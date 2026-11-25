//! Shared low-latency worker pool for parallel SLH-DSA operations.
//!
//! One global pool serves both SHA-2 and SHAKE parameter sets, key generation,
//! signing, and parallel batch verification. Workers spin briefly between jobs
//! so back-to-back calls wake in ~1–2 µs, then park on a shared condition
//! variable so idle threads consume zero CPU.
//!
//! Re-entrant or concurrent callers that find the pool busy execute their work
//! directly on the calling thread, preventing deadlocks and CPU oversubscription.

#![allow(unsafe_code)]

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, OnceLock};
use std::thread;

/// Worker is idle and spinning briefly waiting for the next job.
const IDLE_SPIN: u32 = 0;
/// Worker is parked on the shared condition variable.
const IDLE_PARKED: u32 = 1;
/// Dispatcher assigned a job; worker must execute it and return to IDLE_SPIN.
const WORK_PENDING: u32 = 2;

/// Number of `spin_loop()` iterations a worker executes before parking (~15–25 µs on M4).
const WORKER_SPIN_ITERS: u32 = 1024;

/// Brief spin before parking on `done_cv` while joining workers (~3–5 µs on M4).
const JOIN_SPIN_ITERS: u32 = 256;

#[derive(Clone, Copy)]
struct Job {
    data: *const (),
    call: unsafe fn(*const ()),
    scrub: bool,
}

// SAFETY: `Job` is only read by workers while `Pool::busy` is held by the
// dispatcher, and `PoolGuard::drop` guarantees every woken worker has finished
// executing `call` before the dispatcher returns or unwinds past the caller's
// stack frame. `data` points to an `F: Fn() + Sync`, so concurrent invocation
// through `&F` is sound.
unsafe impl Send for Job {}
unsafe impl Sync for Job {}

// Apple ARM cores use 128-byte cache lines for independently polled slots.
#[cfg_attr(all(target_arch = "aarch64", target_vendor = "apple"), repr(align(128)))]
#[cfg_attr(not(all(target_arch = "aarch64", target_vendor = "apple")), repr(align(64)))]
struct WorkerSlot {
    state: AtomicU32,
}

impl WorkerSlot {
    fn new() -> Self {
        Self {
            state: AtomicU32::new(IDLE_SPIN),
        }
    }
}

struct Pool {
    busy: AtomicBool,
    job: UnsafeCell<Option<Job>>,
    workers: Vec<Arc<WorkerSlot>>,
    park_lock: Mutex<()>,
    park_cv: Condvar,
    // Twice the outstanding worker count, plus one if any worker panicked.
    // A single acquire reads both the join condition and the outcome.
    remaining: AtomicUsize,
    caller_parked: AtomicBool,
    done_lock: Mutex<()>,
    done_cv: Condvar,
}

// SAFETY: `job` is exclusively mutated by the thread that successfully transitions
// `busy` from `false` to `true`, only when all prior workers have completed
// (established via Release/Acquire on `remaining`), and read by workers only
// while their `WorkerSlot::state == WORK_PENDING`.
unsafe impl Sync for Pool {}

struct PoolGuard<'a> {
    pool: &'a Pool,
}

impl Drop for PoolGuard<'_> {
    fn drop(&mut self) {
        let mut spins = 0u32;
        let failed = loop {
            let state = self.pool.remaining.load(Ordering::Acquire);
            if state < 2 {
                break state == 1;
            }
            if spins < JOIN_SPIN_ITERS {
                core::hint::spin_loop();
                spins += 1;
            } else {
                // Publish `caller_parked` before re-checking `remaining` (SeqCst
                // pairs with worker's SeqCst fetch_sub + caller_parked load).
                self.pool.caller_parked.store(true, Ordering::SeqCst);
                if self.pool.remaining.load(Ordering::SeqCst) >= 2 {
                    let mut g = self
                        .pool
                        .done_lock
                        .lock()
                        .unwrap_or_else(|e| e.into_inner());
                    while self.pool.remaining.load(Ordering::Acquire) >= 2 {
                        g = self
                            .pool
                            .done_cv
                            .wait(g)
                            .unwrap_or_else(|e| e.into_inner());
                    }
                }
                self.pool.caller_parked.store(false, Ordering::Relaxed);
            }
        };
        // SAFETY: a zero outstanding worker count with Acquire synchronization guarantees every
        // dispatched worker has already finished reading `pool.job` and stored
        // `IDLE_SPIN`.
        unsafe {
            *self.pool.job.get() = None;
        }
        self.pool.busy.store(false, Ordering::Release);
        if failed && !thread::panicking() {
            panic!("SLH-DSA worker panicked");
        }
    }
}

/// Keep secret computation below a frame that [`scrub_worker_stack`] can overwrite.
#[inline(never)]
fn run_worker_job(call: unsafe fn(*const ()), data: *const ()) {
    // SAFETY: Guaranteed valid for the duration of `WORK_PENDING` by `PoolGuard`.
    unsafe { call(data) };
}

/// Overwrite 64 KiB of worker stack below the caller's frame with volatile zeros.
/// Uses `u64` words (8,192 × 8 bytes = 64 KiB) so volatile zeroing runs ~8× faster
/// than byte-by-byte volatile stores while covering the exact same 64 KiB region.
#[inline(never)]
pub(crate) fn scrub_worker_stack() {
    use zeroize::Zeroize;
    let mut scratch = [0u64; 8 * 1024];
    scratch.zeroize();
}

fn worker_once(pool: &Pool, slot: &WorkerSlot) {
    let mut spins = 0u32;
    loop {
        let s = slot.state.load(Ordering::Acquire);
        if s == WORK_PENDING {
            break;
        }
        if spins < WORKER_SPIN_ITERS {
            core::hint::spin_loop();
            spins += 1;
        } else {
            match slot.state.compare_exchange(
                IDLE_SPIN,
                IDLE_PARKED,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    let mut guard = pool.park_lock.lock().unwrap_or_else(|e| e.into_inner());
                    while slot.state.load(Ordering::Acquire) == IDLE_PARKED {
                        guard = pool.park_cv.wait(guard).unwrap_or_else(|e| e.into_inner());
                    }
                    break;
                }
                Err(WORK_PENDING) => break,
                Err(_) => {}
            }
        }
    }

    // SAFETY: Our Acquire load observed `WORK_PENDING`, which synchronizes-with
    // the dispatcher's AcqRel swap after initializing `pool.job`.
    let job = unsafe { (*pool.job.get()).expect("pool job present") };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        run_worker_job(job.call, job.data);
    }));
    if let Err(payload) = result {
        pool.remaining.fetch_or(1, Ordering::Relaxed);
        // User-defined panic payloads can panic again in Drop. Retiring the
        // first payload here keeps such a panic from terminating this worker.
        if let Err(second) =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(payload)))
        {
            core::mem::forget(second);
        }
    }
    if job.scrub {
        scrub_worker_stack();
    }
    // Transition back to IDLE_SPIN BEFORE decrementing `remaining` so that
    // once the outstanding count hits 0, all slots are ready for the next dispatch.
    slot.state.store(IDLE_SPIN, Ordering::Release);
    if pool.remaining.fetch_sub(2, Ordering::SeqCst) < 4
        && pool.caller_parked.load(Ordering::SeqCst)
    {
        let _g = pool.done_lock.lock().unwrap_or_else(|e| e.into_inner());
        pool.done_cv.notify_one();
    }
}

fn worker_loop(pool: &'static Pool, slot: Arc<WorkerSlot>) {
    loop {
        worker_once(pool, &slot);
    }
}

static PARALLELISM: OnceLock<usize> = OnceLock::new();
static POOL: OnceLock<Pool> = OnceLock::new();

/// Cached number of logical hardware threads available to this process.
pub(crate) fn available_threads() -> usize {
    *PARALLELISM.get_or_init(|| {
        thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    })
}

fn global_pool() -> &'static Pool {
    POOL.get_or_init(|| new_pool(available_threads().saturating_sub(1)))
}

fn new_pool(wanted: usize) -> Pool {
    let mut slots = Vec::with_capacity(wanted);
    for _ in 0..wanted {
        slots.push(Arc::new(WorkerSlot::new()));
    }
    Pool {
        busy: AtomicBool::new(false),
        job: UnsafeCell::new(None),
        workers: slots,
        park_lock: Mutex::new(()),
        park_cv: Condvar::new(),
        remaining: AtomicUsize::new(0),
        caller_parked: AtomicBool::new(false),
        done_lock: Mutex::new(()),
        done_cv: Condvar::new(),
    }
}

static WORKERS_SPAWNED: OnceLock<usize> = OnceLock::new();

fn ensure_workers() -> (&'static Pool, usize) {
    let pool = global_pool();
    let count = *WORKERS_SPAWNED.get_or_init(|| {
        let mut spawned = 0usize;
        for slot in &pool.workers {
            let slot_clone = Arc::clone(slot);
            if thread::Builder::new()
                .name(alloc::format!("slhdsa-worker-{spawned}"))
                .spawn(move || worker_loop(pool, slot_clone))
                .is_ok()
            {
                spawned += 1;
            } else {
                break;
            }
        }
        spawned
    });
    (pool, count)
}

/// Execute `f` concurrently across up to `max_threads` threads (including the
/// calling thread).
///
/// When `scrub` is `true`, each worker scrubs 64 KiB of its stack after `f`
/// completes before returning to the idle pool.
///
/// If the pool is currently busy (concurrent or nested call), `f` executes
/// directly on the calling thread.
pub(crate) fn execute<F: Fn() + Sync>(max_threads: usize, scrub: bool, f: &F) {
    if max_threads <= 1 {
        f();
        return;
    }
    let (pool, spawned) = ensure_workers();
    let n_workers = (max_threads - 1).min(spawned);
    dispatch(pool, n_workers, scrub, f);
}

fn dispatch<F: Fn() + Sync>(pool: &Pool, n_workers: usize, scrub: bool, f: &F) {
    if n_workers == 0 {
        f();
        return;
    }
    if pool
        .busy
        .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        // Another caller owns the pool (or this is a re-entrant call).
        f();
        return;
    }

    unsafe fn trampoline<F: Fn() + Sync>(ptr: *const ()) {
        let f = &*(ptr as *const F);
        f();
    }

    // SAFETY: We hold `busy == true` and all previous workers have joined.
    unsafe {
        *pool.job.get() = Some(Job {
            data: (f as *const F).cast::<()>(),
            call: trampoline::<F>,
            scrub,
        });
    }
    // n_workers is bounded by the length of a Vec<Arc<WorkerSlot>>, so doubling fits.
    pool.remaining.store(n_workers * 2, Ordering::Relaxed);
    pool.caller_parked.store(false, Ordering::Relaxed);

    let _guard = PoolGuard { pool };

    let mut need_notify = false;
    for slot in &pool.workers[..n_workers] {
        let prev = slot.state.swap(WORK_PENDING, Ordering::AcqRel);
        if prev == IDLE_PARKED {
            need_notify = true;
        }
    }
    if need_notify {
        let _lock = pool.park_lock.lock().unwrap_or_else(|e| e.into_inner());
        pool.park_cv.notify_all();
    }

    f();
    // `_guard` drops here, joining all `n_workers` workers and releasing `busy`.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_failure_propagates_after_join_and_pool_is_reusable() {
        let (_, workers) = ensure_workers();
        if workers == 0 {
            return;
        }
        let caller = thread::current().id();
        // Another concurrent dispatch can trigger the serial fallback. Retry
        // until this test owns a dispatch and actually runs on a worker.
        loop {
            let worker_ran = AtomicBool::new(false);
            let failed = std::panic::catch_unwind(|| {
                execute(2, false, &|| {
                    if thread::current().id() != caller {
                        worker_ran.store(true, Ordering::Relaxed);
                        panic!("worker failure");
                    }
                });
            });
            if worker_ran.load(Ordering::Relaxed) {
                assert!(failed.is_err());
                break;
            }
            thread::yield_now();
        }
        execute(2, false, &|| {});
    }

    #[test]
    fn panicking_payload_destructor_preserves_worker() {
        struct Payload;
        impl Drop for Payload {
            fn drop(&mut self) {
                panic!("payload destructor");
            }
        }

        let pool = new_pool(1);
        let caller = thread::current().id();
        let (ready, retired) = std::sync::mpsc::channel();
        thread::scope(|scope| {
            let pool = &pool;
            scope.spawn(move || {
                worker_once(pool, &pool.workers[0]);
                ready.send(()).unwrap();
                worker_once(pool, &pool.workers[0]);
            });
            let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                dispatch(pool, 1, false, &|| {
                    if thread::current().id() != caller {
                        std::panic::panic_any(Payload);
                    }
                });
            }));
            assert!(failed.is_err());
            retired.recv().expect("worker survived payload destructor");
            let calls = AtomicUsize::new(0);
            dispatch(pool, 1, false, &|| {
                calls.fetch_add(1, Ordering::Relaxed);
            });
            assert_eq!(calls.load(Ordering::Relaxed), 2);
        });
    }

    #[test]
    fn parallel_work_queue_and_scrub_preserve_results() {
        const ITEMS: usize = 32;
        let next = AtomicUsize::new(0);
        let slots: Vec<OnceLock<usize>> = (0..ITEMS).map(|_| OnceLock::new()).collect();
        execute(4, true, &|| loop {
            let i = next.fetch_add(1, Ordering::Relaxed);
            let Some(slot) = slots.get(i) else { break };
            slot.set(i * 3 + 7).expect("unique work item");
        });
        for (i, slot) in slots.iter().enumerate() {
            assert_eq!(*slot.get().expect("all items completed"), i * 3 + 7);
        }
    }

    #[test]
    fn nested_reentrant_execute_falls_back_cleanly() {
        let pool = new_pool(1);
        let caller = thread::current().id();
        let nested = AtomicUsize::new(0);
        thread::scope(|scope| {
            scope.spawn(|| worker_once(&pool, &pool.workers[0]));
            dispatch(&pool, 1, false, &|| {
                let outer = thread::current().id();
                dispatch(&pool, 1, false, &|| {
                    assert_eq!(outer, thread::current().id());
                    nested.fetch_add(1, Ordering::Relaxed);
                });
                if outer != caller {
                    assert!(pool.busy.load(Ordering::Relaxed));
                }
            });
        });
        assert_eq!(nested.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn caller_panic_joins_workers_before_unwinding_without_double_panic() {
        let (_, workers) = ensure_workers();
        if workers == 0 {
            return;
        }
        let caller = thread::current().id();
        loop {
            let worker_read_stack = AtomicBool::new(false);
            let stack_payload = [0x5Au8; 64];
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                execute(3, false, &|| {
                    if thread::current().id() == caller {
                        panic!("caller failure");
                    } else {
                        // Borrow caller stack payload while caller is unwinding.
                        // PoolGuard::drop must join this worker before stack_payload drops.
                        let sum: usize = stack_payload.iter().map(|&b| b as usize).sum();
                        assert_eq!(sum, 64 * 0x5A);
                        worker_read_stack.store(true, Ordering::Relaxed);
                        panic!("simultaneous worker failure");
                    }
                });
            }));
            assert!(res.is_err());
            if worker_read_stack.load(Ordering::Relaxed) {
                break;
            }
            thread::yield_now();
        }
        // Pool must remain usable after simultaneous caller + worker panics.
        let check = AtomicUsize::new(0);
        execute(4, false, &|| {
            check.fetch_add(1, Ordering::Relaxed);
        });
        assert!(check.load(Ordering::Relaxed) >= 1);
    }

    #[test]
    fn parked_worker_and_waiting_dispatcher_exchange_a_borrowed_job() {
        let pool = new_pool(1);
        let slot = &pool.workers[0];
        let caller = thread::current().id();
        let value = AtomicUsize::new(0);
        thread::scope(|scope| {
            scope.spawn(|| worker_once(&pool, slot));
            // Dispatch after this worker has taken the parking branch.
            while slot.state.load(Ordering::Acquire) != IDLE_PARKED {
                thread::yield_now();
            }
            dispatch(&pool, 1, false, &|| {
                if thread::current().id() != caller {
                    // Complete after the caller has advertised its wait.
                    while !pool.caller_parked.load(Ordering::Acquire) {
                        thread::yield_now();
                    }
                    value.store(17, Ordering::Relaxed);
                }
            });
            // Check publication through the pool join, before the scope joins.
            assert_eq!(value.load(Ordering::Relaxed), 17);
            assert_eq!(slot.state.load(Ordering::Relaxed), IDLE_SPIN);
            assert!(!pool.busy.load(Ordering::Relaxed));
        });
    }

    #[test]
    fn concurrent_dispatchers_and_parked_worker_wakeup() {
        // Ensure workers have a chance to enter IDLE_PARKED on park_cv, then wake.
        for _ in 0..8 {
            thread::yield_now();
        }
        let handles: Vec<_> = (0..3)
            .map(|t| {
                thread::spawn(move || {
                    for round in 0..4 {
                        let next = AtomicUsize::new(0);
                        let done = AtomicUsize::new(0);
                        execute(4, false, &|| {
                            while next.fetch_add(1, Ordering::Relaxed) < 6 {
                                done.fetch_add(1 + t + round, Ordering::Relaxed);
                            }
                        });
                        assert_eq!(done.load(Ordering::Relaxed), 6 * (1 + t + round));
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().expect("dispatcher thread succeeded");
        }
    }
}
