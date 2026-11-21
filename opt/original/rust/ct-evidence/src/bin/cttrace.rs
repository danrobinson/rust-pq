//! Deterministic trace comparison under the Unicorn CPU emulator.
//!
//! This process maps *its own* Mach-O image (the release-optimised arm64
//! machine code of `slhdsa` linked into this binary) into a Unicorn AArch64
//! guest at the same virtual addresses, gives the guest a private stack, heap
//! and I/O area at fixed guest addresses, and executes the harness entry
//! points instruction by instruction. Hooks record
//!
//!   * every executed basic block (address, size),
//!   * every memory read and write (address, size) -- never the value,
//!   * every call that leaves the image (malloc/realloc/free/memcpy/...),
//!     which is serviced by a deterministic host-side stub and recorded with
//!     its pointer/size arguments.
//!
//! Two runs have "the same trace" iff these event sequences are identical.
//! Sequences are compared through a 128-bit running hash plus per-chunk
//! checkpoints; on a mismatch the diverging chunk is re-run in capture mode
//! and the first differing event is printed with its symbol.

use ct_evidence::*;
use std::collections::HashMap;
use std::ffi::{c_char, c_int, c_void, CStr};
use std::sync::{Arc, Mutex};

// ------------------------------------------------------------ unicorn FFI
#[allow(non_camel_case_types)]
type uc_engine = c_void;
extern "C" {
    fn uc_open(arch: c_int, mode: c_int, uc: *mut *mut uc_engine) -> c_int;
    fn uc_ctl(uc: *mut uc_engine, control: c_int, ...) -> c_int;
    fn uc_mem_map(uc: *mut uc_engine, addr: u64, size: u64, perms: u32) -> c_int;
    fn uc_mem_write(uc: *mut uc_engine, addr: u64, bytes: *const u8, size: u64) -> c_int;
    fn uc_mem_read(uc: *mut uc_engine, addr: u64, bytes: *mut u8, size: u64) -> c_int;
    fn uc_reg_write(uc: *mut uc_engine, regid: c_int, value: *const c_void) -> c_int;
    fn uc_reg_read(uc: *mut uc_engine, regid: c_int, value: *mut c_void) -> c_int;
    fn uc_hook_add(uc: *mut uc_engine, hh: *mut usize, typ: c_int, cb: *const c_void, user: *mut c_void, begin: u64, end: u64, ...) -> c_int;
    fn uc_emu_start(uc: *mut uc_engine, begin: u64, until: u64, timeout: u64, count: usize) -> c_int;
    fn uc_emu_stop(uc: *mut uc_engine) -> c_int;
    fn uc_strerror(code: c_int) -> *const c_char;
    fn uc_version(major: *mut u32, minor: *mut u32) -> u32;
}
const UC_ARCH_ARM64: c_int = 2;
const UC_MODE_ARM: c_int = 0;
const UC_HOOK_BLOCK: c_int = 1 << 3;
const UC_HOOK_MEM_UNMAPPED: c_int = (1 << 4) | (1 << 5) | (1 << 6);
const UC_HOOK_MEM_READ: c_int = 1 << 10;
const UC_HOOK_MEM_WRITE: c_int = 1 << 11;
const UC_MEM_WRITE: c_int = 17;
const REG_X0: c_int = 199;
const REG_X29: c_int = 1;
const REG_X30: c_int = 2;
const REG_SP: c_int = 4;
const REG_PC: c_int = 260;
const UC_CTL_CPU_MODEL_WRITE: c_int = 7 | (1 << 26) | (1 << 30);
const UC_CPU_ARM64_MAX: c_int = 3;

// ------------------------------------------------------------ host symbols
#[repr(C)]
struct DlInfo {
    fname: *const c_char,
    fbase: *mut c_void,
    sname: *const c_char,
    saddr: *mut c_void,
}
extern "C" {
    fn dladdr(addr: *const c_void, info: *mut DlInfo) -> c_int;
    fn _dyld_get_image_header(idx: u32) -> *const u8;
    fn _dyld_get_image_vmaddr_slide(idx: u32) -> isize;
    fn malloc(n: usize) -> *mut c_void;
    fn calloc(a: usize, b: usize) -> *mut c_void;
    fn realloc(p: *mut c_void, n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn posix_memalign(out: *mut *mut c_void, a: usize, n: usize) -> c_int;
    fn memcpy(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
    fn memmove(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
    fn memset(d: *mut c_void, c: c_int, n: usize) -> *mut c_void;
    fn bzero(d: *mut c_void, n: usize);
    fn memcmp(a: *const c_void, b: *const c_void, n: usize) -> c_int;
    fn bcmp(a: *const c_void, b: *const c_void, n: usize) -> c_int;
}

fn symbol(addr: u64) -> String {
    unsafe {
        let mut info: DlInfo = std::mem::zeroed();
        if dladdr(addr as *const c_void, &mut info) != 0 && !info.sname.is_null() {
            let s = CStr::from_ptr(info.sname).to_string_lossy().into_owned();
            let d = format!("{:#}", rustc_demangle::demangle(&s));
            format!("{}+0x{:x}", d, addr - info.saddr as u64)
        } else {
            format!("0x{addr:x}")
        }
    }
}
fn symbol_start(addr: u64) -> Option<(String, u64)> {
    unsafe {
        let mut info: DlInfo = std::mem::zeroed();
        if dladdr(addr as *const c_void, &mut info) != 0 && !info.sname.is_null() {
            let s = CStr::from_ptr(info.sname).to_string_lossy().into_owned();
            Some((format!("{:#}", rustc_demangle::demangle(&s)), info.saddr as u64))
        } else {
            None
        }
    }
}

// ------------------------------------------------------------ guest layout
const HEAP_BASE: u64 = 0x40_0000_0000;
const HEAP_SIZE: u64 = 64 << 20;
const STACK_BASE: u64 = 0x50_0000_0000;
const STACK_SIZE: u64 = 8 << 20;
const IO_BASE: u64 = 0x60_0000_0000;
const IO_IN: u64 = IO_BASE;
const IO_OUT: u64 = IO_BASE + 0x10000;
const IO_SIZE: u64 = 0x20000;
const EXIT_ADDR: u64 = 0x70_0000_0000;

const CHUNK: u64 = 1 << 16;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Stub {
    Malloc,
    Calloc,
    Realloc,
    Free,
    PosixMemalign,
    Memcpy,
    Memmove,
    Memset,
    Bzero,
    Memcmp,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Ev {
    kind: u8, // 1 block, 2 read, 3 write, 4.. stub
    a: u64,
    b: u64,
    pc: u64,
}

/// Declassification patch: when the block at `at` (a return site) is reached
/// for the n-th time, overwrite guest memory / registers with recorded values.
#[derive(Clone, Default)]
struct Declass {
    /// entry address of `thash`
    thash: u64,
    /// entry address of `prf_msg`
    prf_msg: u64,
    /// record (true) or replay (false)
    record: bool,
    /// recorded / to-be-replayed 16-byte values, in order of occurrence
    values: Vec<[u8; 16]>,
    next: usize,
    /// pending returns: (return address, sp at entry, result pointer x8)
    pending: Vec<(u64, u64, u64)>,
    applied: usize,
    enabled: bool,
}

struct State {
    uc: *mut uc_engine,
    h1: u64,
    h2: u64,
    n_ev: u64,
    n_blocks: u64,
    n_insn: u64,
    n_rd: u64,
    n_wr: u64,
    n_stub: u64,
    chunks: Vec<u64>,
    cap: Option<(u64, u64)>,
    captured: Vec<Ev>,
    cur_block: u64,
    stubs: HashMap<u64, Stub>,
    img_lo: u64,
    img_hi: u64,
    // deterministic guest allocator
    bump: u64,
    free_lists: HashMap<u64, Vec<u64>>,
    sizes: HashMap<u64, u64>,
    heap_peak: u64,
    err: Option<String>,
    dc: Declass,
    /// per-function entry counters (only when profiling)
    profile: Option<HashMap<u64, u64>>,
}

impl State {
    #[inline(always)]
    fn event(&mut self, kind: u8, a: u64, b: u64) {
        let x = a ^ ((kind as u64) << 56) ^ (b << 48);
        self.h1 = (self.h1.rotate_left(5) ^ x).wrapping_mul(0x9E3779B97F4A7C15);
        self.h2 = (self.h2 ^ x).wrapping_mul(0xC2B2AE3D27D4EB4F).rotate_left(31) ^ b;
        if let Some((lo, hi)) = self.cap {
            if self.n_ev >= lo && self.n_ev < hi {
                // (the guest PC is only synchronised at block boundaries, so we
                // attribute memory events to the enclosing basic block)
                let pc = self.cur_block;
                self.captured.push(Ev { kind, a, b, pc });
            }
        }
        self.n_ev += 1;
        if self.n_ev % CHUNK == 0 {
            self.chunks.push(self.h1 ^ self.h2);
        }
    }
    fn reg(&self, r: c_int) -> u64 {
        let mut v = 0u64;
        unsafe { uc_reg_read(self.uc, r, &mut v as *mut u64 as *mut c_void) };
        v
    }
    fn set_reg(&self, r: c_int, v: u64) {
        unsafe { uc_reg_write(self.uc, r, &v as *const u64 as *const c_void) };
    }
    fn rd(&mut self, addr: u64, n: u64) -> Vec<u8> {
        let mut b = vec![0u8; n as usize];
        if n > 0 && unsafe { uc_mem_read(self.uc, addr, b.as_mut_ptr(), n) } != 0 {
            self.fail(format!("stub read of unmapped guest memory 0x{addr:x}+{n}"));
        }
        b
    }
    fn wr(&mut self, addr: u64, b: &[u8]) {
        if !b.is_empty() && unsafe { uc_mem_write(self.uc, addr, b.as_ptr(), b.len() as u64) } != 0 {
            self.fail(format!("stub write to unmapped guest memory 0x{addr:x}+{}", b.len()));
        }
    }
    fn fail(&mut self, msg: String) {
        if self.err.is_none() {
            self.err = Some(msg);
        }
        unsafe { uc_emu_stop(self.uc) };
    }
    fn g_malloc(&mut self, size: u64) -> u64 {
        let r = (size.max(1) + 15) & !15;
        let p = match self.free_lists.get_mut(&r).and_then(|l| l.pop()) {
            Some(p) => p,
            None => {
                let p = self.bump;
                self.bump += r;
                if self.bump > HEAP_BASE + HEAP_SIZE {
                    self.fail("guest heap exhausted".into());
                }
                self.heap_peak = self.heap_peak.max(self.bump - HEAP_BASE);
                p
            }
        };
        self.sizes.insert(p, r);
        p
    }
    fn g_free(&mut self, p: u64) {
        if p == 0 {
            return;
        }
        match self.sizes.remove(&p) {
            Some(r) => self.free_lists.entry(r).or_default().push(p),
            None => self.fail(format!("guest free of unknown pointer 0x{p:x}")),
        }
    }
    fn stub(&mut self, s: Stub) {
        let x0 = self.reg(REG_X0);
        let x1 = self.reg(REG_X0 + 1);
        let x2 = self.reg(REG_X0 + 2);
        self.n_stub += 1;
        let k = 16 + s as u8;
        match s {
            Stub::Malloc => {
                let p = self.g_malloc(x0);
                self.event(k, x0, 0);
                self.event(k, p, 1);
                self.set_reg(REG_X0, p);
            }
            Stub::Calloc => {
                let n = x0 * x1;
                let p = self.g_malloc(n);
                self.wr(p, &vec![0u8; n as usize]);
                self.event(k, n, 0);
                self.event(k, p, 1);
                self.set_reg(REG_X0, p);
            }
            Stub::Realloc => {
                let old = if x0 == 0 { 0 } else { *self.sizes.get(&x0).unwrap_or(&0) };
                if x0 != 0 && old == 0 {
                    self.fail(format!("guest realloc of unknown pointer 0x{x0:x}"));
                }
                let p = self.g_malloc(x1);
                if x0 != 0 {
                    let d = self.rd(x0, old.min(x1));
                    self.wr(p, &d);
                    self.g_free(x0);
                }
                self.event(k, x0, 0);
                self.event(k, x1, 1);
                self.event(k, p, 2);
                self.set_reg(REG_X0, p);
            }
            Stub::Free => {
                self.g_free(x0);
                self.event(k, x0, 0);
            }
            Stub::PosixMemalign => {
                if x1 > 16 {
                    self.fail(format!("posix_memalign with alignment {x1} not supported by stub"));
                }
                let p = self.g_malloc(x2);
                self.wr(x0, &p.to_le_bytes());
                self.event(k, x0, 0);
                self.event(k, x2, 1);
                self.event(k, p, 2);
                self.set_reg(REG_X0, 0);
            }
            Stub::Memcpy | Stub::Memmove => {
                let d = self.rd(x1, x2);
                self.wr(x0, &d);
                self.event(k, x0, 0);
                self.event(k, x1, 1);
                self.event(k, x2, 2);
            }
            Stub::Memset => {
                self.wr(x0, &vec![x1 as u8; x2 as usize]);
                self.event(k, x0, 0);
                self.event(k, x2, 2);
            }
            Stub::Bzero => {
                self.wr(x0, &vec![0u8; x1 as usize]);
                self.event(k, x0, 0);
                self.event(k, x1, 2);
            }
            Stub::Memcmp => {
                // Data-dependent in libSystem (early exit). Treated as a leak
                // source unless the code under test never reaches it; we record
                // the call and FAIL the run so that it cannot go unnoticed.
                self.event(k, x0, 0);
                self.event(k, x1, 1);
                self.event(k, x2, 2);
                self.fail("memcmp/bcmp reached from code under test (libSystem memcmp is not constant-time)".into());
            }
        }
    }
}

extern "C" fn hook_block(_uc: *mut uc_engine, addr: u64, size: u32, user: *mut c_void) {
    let st = unsafe { &mut *(user as *mut State) };
    st.cur_block = addr;
    if addr < st.img_lo || addr >= st.img_hi {
        if let Some(&s) = st.stubs.get(&addr) {
            st.stub(s);
            return;
        }
        if addr == EXIT_ADDR {
            return;
        }
        st.fail(format!("execution left the image at 0x{addr:x} ({})", symbol(addr)));
        return;
    }
    st.n_blocks += 1;
    st.n_insn += (size / 4) as u64;
    st.event(1, addr, size as u64);
    if let Some(p) = st.profile.as_mut() {
        *p.entry(addr).or_insert(0) += 1;
    }
    if st.dc.enabled {
        declass_hook(st, addr);
    }
}

/// Declassification hook, see `sign_declass`.
///
/// On entry to `thash`/`prf_msg` we remember the return address (x30) and the
/// stack pointer and the indirect-result pointer x8 (in this build rustc
/// returns `[u8; 16]` through an sret pointer; this assumption is checked in
/// every experiment: the first recorded value must equal the signature's R,
/// exactly nine values must be recorded, and replaying a run's own values
/// must leave its trace and output unchanged). When execution reaches the
/// return address with the same stack pointer, the function has returned and
/// its 16-byte result is at that pointer; it is recorded or overwritten there
/// through the emulator API (no guest-visible memory event).
fn declass_hook(st: &mut State, addr: u64) {
    if let Some(&(ret, sp, outptr)) = st.dc.pending.last() {
        if addr == ret && st.reg(REG_SP) == sp {
            st.dc.pending.pop();
            if st.dc.record {
                let v: [u8; 16] = st.rd(outptr, 16).try_into().unwrap();
                st.dc.values.push(v);
            } else {
                match st.dc.values.get(st.dc.next).cloned() {
                    Some(r) => {
                        st.wr(outptr, &r);
                        st.dc.applied += 1;
                    }
                    None => st.fail("declass replay: more declassification points than recorded".into()),
                }
                st.dc.next += 1;
            }
        }
    }
    let interesting = if addr == st.dc.prf_msg {
        true
    } else if addr == st.dc.thash {
        // thash(pk_seed: x0, adrs: x1, m: x2, len: x3). Adrs is a repr(Rust)
        // struct; we locate `typ` and `word2` by reading all six fields and
        // matching on the field layout discovered at start-up.
        let a = st.reg(REG_X0 + 1);
        let raw = st.rd(a, 32);
        let (typ, word2) = adrs_typ_word2(&raw);
        // FORS_ROOTS (4): the FORS public key. TREE (2) at height 9: an XMSS
        // root recomputed from the signature (xmss_node inside xmss_sign only
        // goes up to height 8, so height 9 identifies xmss_pk_from_sig).
        typ == 4 || (typ == 2 && word2 == 9)
    } else {
        false
    };
    if interesting {
        st.dc.pending.push((st.reg(REG_X30), st.reg(REG_SP), st.reg(REG_X0 + 8)));
    }
}

/// Offsets of `typ` and `word2` inside the in-memory `Adrs`, discovered by
/// probing a value with distinct field contents (repr(Rust) layout is not
/// guaranteed, so we do not hard-code it).
static ADRS_LAYOUT: std::sync::OnceLock<(usize, usize)> = std::sync::OnceLock::new();
fn adrs_layout() -> (usize, usize) {
    *ADRS_LAYOUT.get_or_init(|| {
        let a = slhdsa::address::Adrs { layer: 0x11111111, tree: 0x2222222222222222, typ: 0x33333333, keypair: 0x44444444, word2: 0x55555555, word3: 0x66666666 };
        assert_eq!(std::mem::size_of_val(&a), 32);
        let raw: [u8; 32] = unsafe { std::mem::transmute(a) };
        let find = |b: u8| (0..32).step_by(4).find(|&o| raw[o..o + 4] == [b; 4]).unwrap();
        (find(0x33), find(0x55))
    })
}
fn adrs_typ_word2(raw: &[u8]) -> (u32, u32) {
    let (t, w) = adrs_layout();
    (u32::from_le_bytes(raw[t..t + 4].try_into().unwrap()), u32::from_le_bytes(raw[w..w + 4].try_into().unwrap()))
}

extern "C" fn hook_mem(_uc: *mut uc_engine, typ: c_int, addr: u64, size: c_int, _value: i64, user: *mut c_void) {
    let st = unsafe { &mut *(user as *mut State) };
    if typ == UC_MEM_WRITE {
        st.n_wr += 1;
        st.event(3, addr, size as u64);
    } else {
        st.n_rd += 1;
        st.event(2, addr, size as u64);
    }
}

extern "C" fn hook_unmapped(_uc: *mut uc_engine, typ: c_int, addr: u64, size: c_int, _value: i64, user: *mut c_void) -> bool {
    let st = unsafe { &mut *(user as *mut State) };
    let pc = st.reg(REG_PC);
    st.fail(format!("unmapped access type {typ} at 0x{addr:x} size {size} (target {}), pc {} ", symbol(addr), symbol(pc)));
    false
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Summary {
    h: (u64, u64),
    n_ev: u64,
    n_blocks: u64,
    n_insn: u64,
    n_rd: u64,
    n_wr: u64,
    n_stub: u64,
    chunks: Vec<u64>,
}

struct Emu {
    uc: *mut uc_engine,
    st: Box<State>,
}

fn ck(e: c_int, what: &str) {
    if e != 0 {
        let s = unsafe { CStr::from_ptr(uc_strerror(e)) }.to_string_lossy();
        panic!("unicorn: {what}: {s}");
    }
}

impl Emu {
    fn new(mem_hooks: bool) -> Emu {
        unsafe {
            let mut uc: *mut uc_engine = std::ptr::null_mut();
            ck(uc_open(UC_ARCH_ARM64, UC_MODE_ARM, &mut uc), "uc_open");
            ck(uc_ctl(uc, UC_CTL_CPU_MODEL_WRITE, UC_CPU_ARM64_MAX), "cpu model");

            // --- map our own Mach-O image (all segments, after dyld fixups)
            let hdr = _dyld_get_image_header(0);
            let slide = _dyld_get_image_vmaddr_slide(0) as u64;
            let ncmds = *(hdr.add(16) as *const u32);
            let mut p = hdr.add(32);
            let (mut lo, mut hi) = (u64::MAX, 0u64);
            for _ in 0..ncmds {
                let cmd = *(p as *const u32);
                let cmdsize = *(p.add(4) as *const u32);
                if cmd == 0x19 {
                    let name = CStr::from_ptr(p.add(8) as *const c_char).to_string_lossy().into_owned();
                    let vmaddr = *(p.add(24) as *const u64);
                    let vmsize = *(p.add(32) as *const u64);
                    if name != "__PAGEZERO" && name != "__LINKEDIT" && vmsize > 0 {
                        let a = vmaddr.wrapping_add(slide);
                        let sz = (vmsize + 0xfff) & !0xfff;
                        ck(uc_mem_map(uc, a, sz, 7), "map image segment");
                        ck(uc_mem_write(uc, a, a as *const u8, vmsize), "copy image segment");
                        lo = lo.min(a);
                        hi = hi.max(a + sz);
                    }
                }
                p = p.add(cmdsize as usize);
            }
            ck(uc_mem_map(uc, HEAP_BASE, HEAP_SIZE, 3), "map heap");
            ck(uc_mem_map(uc, STACK_BASE, STACK_SIZE, 3), "map stack");
            ck(uc_mem_map(uc, IO_BASE, IO_SIZE, 3), "map io");
            ck(uc_mem_map(uc, EXIT_ADDR, 0x1000, 5), "map exit");

            // --- stubs for everything the image imports and the code under test may call
            let imports: [(usize, Stub); 11] = [
                (malloc as *const () as usize, Stub::Malloc),
                (calloc as *const () as usize, Stub::Calloc),
                (realloc as *const () as usize, Stub::Realloc),
                (free as *const () as usize, Stub::Free),
                (posix_memalign as *const () as usize, Stub::PosixMemalign),
                (memcpy as *const () as usize, Stub::Memcpy),
                (memmove as *const () as usize, Stub::Memmove),
                (memset as *const () as usize, Stub::Memset),
                (bzero as *const () as usize, Stub::Bzero),
                (memcmp as *const () as usize, Stub::Memcmp),
                (bcmp as *const () as usize, Stub::Memcmp),
            ];
            let mut stubs = HashMap::new();
            let mut pages = std::collections::HashSet::new();
            let ret = 0xd65f03c0u32.to_le_bytes();
            let page: Vec<u8> = ret.iter().cycle().take(0x1000).cloned().collect();
            for (a, s) in imports {
                let a = a as u64;
                let pg = a & !0xfff;
                if pages.insert(pg) {
                    ck(uc_mem_map(uc, pg, 0x1000, 5), "map stub page");
                    ck(uc_mem_write(uc, pg, page.as_ptr(), 0x1000), "write stub page");
                }
                // memcpy and memmove may resolve to the same address
                stubs.entry(a).or_insert(s);
            }

            let mut st = Box::new(State {
                uc,
                h1: 0,
                h2: 0,
                n_ev: 0,
                n_blocks: 0,
                n_insn: 0,
                n_rd: 0,
                n_wr: 0,
                n_stub: 0,
                chunks: Vec::new(),
                cap: None,
                captured: Vec::new(),
                cur_block: 0,
                stubs,
                img_lo: lo,
                img_hi: hi,
                bump: HEAP_BASE,
                free_lists: HashMap::new(),
                sizes: HashMap::new(),
                heap_peak: 0,
                err: None,
                dc: Declass::default(),
                profile: None,
            });
            let user = &mut *st as *mut State as *mut c_void;
            let mut hh = 0usize;
            ck(uc_hook_add(uc, &mut hh, UC_HOOK_BLOCK, hook_block as *const c_void, user, 1u64, 0u64), "hook block");
            if mem_hooks {
                ck(uc_hook_add(uc, &mut hh, UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, hook_mem as *const c_void, user, 1u64, 0u64), "hook mem");
            }
            ck(uc_hook_add(uc, &mut hh, UC_HOOK_MEM_UNMAPPED, hook_unmapped as *const c_void, user, 1u64, 0u64), "hook unmapped");
            Emu { uc, st }
        }
    }

    /// Run `f(IO_IN, IO_OUT)` in the guest from a fresh deterministic state.
    fn run(&mut self, f: Entry, input: &[u8], cap: Option<(u64, u64)>) -> Result<(Summary, Vec<u8>), String> {
        let st = &mut *self.st;
        st.h1 = 0x243F6A8885A308D3;
        st.h2 = 0x13198A2E03707344;
        st.n_ev = 0;
        st.n_blocks = 0;
        st.n_insn = 0;
        st.n_rd = 0;
        st.n_wr = 0;
        st.n_stub = 0;
        st.chunks.clear();
        st.cap = cap;
        st.captured.clear();
        st.bump = HEAP_BASE;
        st.free_lists.clear();
        st.sizes.clear();
        st.err = None;
        st.dc.pending.clear();
        st.dc.next = 0;
        st.dc.applied = 0;
        unsafe {
            ck(uc_mem_write(self.uc, IO_IN, input.as_ptr(), input.len() as u64), "write input");
            let zero = vec![0u8; OUT_MAX];
            ck(uc_mem_write(self.uc, IO_OUT, zero.as_ptr(), OUT_MAX as u64), "clear output");
            st.set_reg(REG_X0, IO_IN);
            st.set_reg(REG_X0 + 1, IO_OUT);
            st.set_reg(REG_SP, STACK_BASE + STACK_SIZE - 0x100);
            st.set_reg(REG_X29, 0);
            st.set_reg(REG_X30, EXIT_ADDR);
            let e = uc_emu_start(self.uc, f as usize as u64, EXIT_ADDR, 0, 0);
            if let Some(m) = st.err.take() {
                return Err(m);
            }
            if e != 0 {
                let s = CStr::from_ptr(uc_strerror(e)).to_string_lossy().into_owned();
                return Err(format!("emulation error: {s} at pc {}", symbol(st.reg(REG_PC))));
            }
            let mut out = vec![0u8; OUT_MAX];
            ck(uc_mem_read(self.uc, IO_OUT, out.as_mut_ptr(), OUT_MAX as u64), "read output");
            Ok((
                Summary { h: (st.h1, st.h2), n_ev: st.n_ev, n_blocks: st.n_blocks, n_insn: st.n_insn, n_rd: st.n_rd, n_wr: st.n_wr, n_stub: st.n_stub, chunks: st.chunks.clone() },
                out,
            ))
        }
    }

    /// Locate and describe the first differing event between two inputs.
    fn first_divergence(&mut self, f: Entry, a: &[u8], sa: &Summary, b: &[u8], sb: &Summary) -> String {
        let c = sa.chunks.iter().zip(sb.chunks.iter()).position(|(x, y)| x != y).unwrap_or(sa.chunks.len().min(sb.chunks.len())) as u64;
        let range = Some((c * CHUNK, (c + 1) * CHUNK));
        let saved = self.st.dc.clone();
        let ea = match self.run(f, a, range) {
            Ok(_) => self.st.captured.clone(),
            Err(e) => return format!("(capture run failed: {e})"),
        };
        self.st.dc = saved.clone();
        let eb = match self.run(f, b, range) {
            Ok(_) => self.st.captured.clone(),
            Err(e) => return format!("(capture run failed: {e})"),
        };
        self.st.dc = saved;
        let k = ea.iter().zip(eb.iter()).position(|(x, y)| (x.kind, x.a, x.b) != (y.kind, y.a, y.b)).unwrap_or(ea.len().min(eb.len()));
        let d = |e: Option<&Ev>| match e {
            None => "<end of trace>".to_string(),
            Some(e) => {
                let kind = match e.kind {
                    1 => "exec block".to_string(),
                    2 => "read".to_string(),
                    3 => "write".to_string(),
                    k => format!("call-out stub #{}", k - 16),
                };
                let tgt = if e.kind == 1 { symbol(e.a) } else { format!("0x{:x}", e.a) };
                format!("{kind} {tgt} (size/arg {}) in basic block {}", e.b, symbol(e.pc))
            }
        };
        let prev = if k > 0 { format!("last common event: {}; ", d(ea.get(k - 1))) } else { String::new() };
        format!("first divergence at event #{}: {}A: {} | B: {}", c * CHUNK + k as u64, prev, d(ea.get(k)), d(eb.get(k)))
    }
}

// ------------------------------------------------------------- experiments

fn native(f: Entry, input: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; OUT_MAX];
    f(input.as_ptr(), out.as_mut_ptr());
    out
}

struct Row {
    order: usize,
    name: String,
    what: &'static str,
    expect_equal: bool,
    pairs: usize,
    equal: usize,
    differ: usize,
    errors: Vec<String>,
    insn: u64,
    blocks: u64,
    mem: u64,
    stubs: u64,
    first_div: Option<String>,
    native_ok: bool,
    secs: f64,
}

fn run_components(filter: &str, scale: f64, threads: usize, seed: u64) -> bool {
    let ts = Arc::new(targets());
    // one job per (target, public configuration)
    let mut jobs: Vec<(usize, usize)> = Vec::new();
    for (ti, t) in ts.iter().enumerate() {
        if !t.name.contains(filter) {
            continue;
        }
        for p in 0..t.trials.0 {
            jobs.push((ti, p));
        }
    }
    let jobs = Arc::new(Mutex::new(jobs.into_iter().rev().collect::<Vec<_>>()));
    let rows: Arc<Mutex<Vec<Row>>> = Arc::new(Mutex::new(Vec::new()));
    let mut hs = Vec::new();
    for _ in 0..threads {
        let (ts, jobs, rows) = (ts.clone(), jobs.clone(), rows.clone());
        hs.push(std::thread::spawn(move || {
            let mut emu = Emu::new(true);
            loop {
                let job = jobs.lock().unwrap().pop();
                let Some((ti, p)) = job else { break };
                let t = &ts[ti];
                let t0 = std::time::Instant::now();
                let nsec = ((t.trials.1 as f64 * scale).ceil() as usize).max(2);
                let mut row = Row { order: ti, name: t.name.clone(), what: t.what, expect_equal: t.expect_equal, pairs: 0, equal: 0, differ: 0, errors: vec![], insn: 0, blocks: 0, mem: 0, stubs: 0, first_div: None, native_ok: true, secs: 0.0 };
                let mut rng = Rng::new(seed ^ ((ti as u64) << 32) ^ (p as u64 + 1).wrapping_mul(0xD1B54A32D192ED03));
                let mut base = public_input(t, rng.next());
                vary_input(t, &mut base, &mut rng);
                match emu.run(t.f, &base, None) {
                    Err(e) => row.errors.push(e),
                    Ok((sref, out)) => {
                        row.native_ok &= out == native(t.f, &base);
                        row.insn = sref.n_insn;
                        row.blocks = sref.n_blocks;
                        row.mem = sref.n_rd + sref.n_wr;
                        row.stubs = sref.n_stub;
                        // pair 0: the varied bytes all zero (the special value also used
                        // as a fixed class by the timing harness); then fresh random values
                        for k in 0..nsec + 1 {
                            let mut other = base.clone();
                            if k == 0 {
                                for &(o, l) in &t.vary {
                                    for x in &mut other[o..o + l] {
                                        *x = 0;
                                    }
                                }
                            } else {
                                vary_input(t, &mut other, &mut rng);
                            }
                            if other == base {
                                continue;
                            }
                            match emu.run(t.f, &other, None) {
                                Err(e) => row.errors.push(e),
                                Ok((s, out)) => {
                                    row.native_ok &= out == native(t.f, &other);
                                    row.pairs += 1;
                                    if s == sref {
                                        row.equal += 1;
                                    } else {
                                        row.differ += 1;
                                        if row.first_div.is_none() {
                                            row.first_div = Some(emu.first_divergence(t.f, &base, &sref, &other, &s));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                row.secs = t0.elapsed().as_secs_f64();
                eprintln!("  done {} [public config {}]: {} pairs, {} equal, {} differ ({:.1}s)", row.name, p, row.pairs, row.equal, row.differ, row.secs);
                rows.lock().unwrap().push(row);
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    // merge per target
    let mut rows = Arc::try_unwrap(rows).ok().unwrap().into_inner().unwrap();
    rows.sort_by_key(|r| r.order);
    let mut merged: Vec<Row> = Vec::new();
    let mut cfgs: Vec<usize> = Vec::new();
    for r in rows {
        match merged.last_mut() {
            Some(m) if m.order == r.order => {
                m.pairs += r.pairs;
                m.equal += r.equal;
                m.differ += r.differ;
                m.errors.extend(r.errors);
                m.native_ok &= r.native_ok;
                m.insn = m.insn.max(r.insn);
                m.blocks = m.blocks.max(r.blocks);
                m.mem = m.mem.max(r.mem);
                m.stubs = m.stubs.max(r.stubs);
                m.secs += r.secs;
                if m.first_div.is_none() {
                    m.first_div = r.first_div;
                }
                *cfgs.last_mut().unwrap() += 1;
            }
            _ => {
                merged.push(r);
                cfgs.push(1);
            }
        }
    }
    println!("| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|");
    let mut all_ok = true;
    let mut notes = Vec::new();
    for (m, c) in merged.iter().zip(cfgs.iter()) {
        let ok = m.errors.is_empty() && m.native_ok && m.pairs > 0 && if m.expect_equal { m.differ == 0 } else { m.differ > 0 };
        all_ok &= ok;
        let verdict = match (m.expect_equal, ok) {
            (true, true) => "PASS (all identical)",
            (true, false) => "**FAIL: DIVERGENCE**",
            (false, true) => "PASS (control: difference detected)",
            (false, false) => "**FAIL: control not detected**",
        };
        println!("| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |", m.name, m.what, c, m.pairs, m.equal, m.differ, m.insn, m.blocks, m.mem, m.stubs, if m.native_ok { "yes" } else { "NO" }, verdict);
        if let Some(d) = &m.first_div {
            notes.push(format!("- `{}`: {}", m.name, d));
        }
        for e in &m.errors {
            notes.push(format!("- `{}`: ERROR {}", m.name, e));
        }
    }
    if !notes.is_empty() {
        println!("\nDivergence details (first differing pair of each row):\n");
        for n in notes {
            println!("{n}");
        }
    }
    println!("\noverall: {}", if all_ok { "ALL ROWS AS EXPECTED" } else { "UNEXPECTED RESULT IN AT LEAST ONE ROW" });
    all_ok
}

// --- whole-signature experiments ------------------------------------------

fn sign_input(rng: &mut Rng, mlen: usize) -> Vec<u8> {
    let mut b = vec![0u8; IN_MAX];
    rng.fill(&mut b);
    b[OFF_A..OFF_A + 4].copy_from_slice(&(mlen as u32).to_le_bytes());
    b[OFF_B..OFF_B + 2].copy_from_slice(&0u16.to_le_bytes());
    b
}
/// Replace (SK.seed, SK.prf, addrnd) by fresh values. If `honest`, also
/// recompute PK.root for the new SK.seed (so sk is a real key pair); PK.seed
/// stays fixed.
fn new_secret(b: &mut [u8], rng: &mut Rng, honest: bool) {
    rng.fill(&mut b[OFF_SK..OFF_SK + 32]);
    rng.fill(&mut b[OFF_ADDRND..OFF_ADDRND + 16]);
    if honest {
        set_honest_root(b);
    }
}
fn set_honest_root(b: &mut [u8]) {
    let g = |o: usize| -> [u8; 16] { b[o..o + 16].try_into().unwrap() };
    let (sk, _pk) = slhdsa::slh_keygen_internal(&g(OFF_SK), &g(OFF_SK + 16), &g(OFF_SK + 32));
    b[OFF_SK..OFF_SK + 64].copy_from_slice(&sk);
}

fn find_fn(entry_hint: &str) -> Option<u64> {
    // Resolve a function of the slhdsa crate inside this image by scanning the
    // image's symbols through dladdr (works for local symbols as long as the
    // binary is not stripped).
    unsafe {
        let hdr = _dyld_get_image_header(0);
        let slide = _dyld_get_image_vmaddr_slide(0) as u64;
        let ncmds = *(hdr.add(16) as *const u32);
        let mut p = hdr.add(32);
        for _ in 0..ncmds {
            let cmd = *(p as *const u32);
            let cmdsize = *(p.add(4) as *const u32);
            if cmd == 0x19 && CStr::from_ptr(p.add(8) as *const c_char).to_string_lossy() == "__TEXT" {
                let lo = (*(p.add(24) as *const u64)).wrapping_add(slide);
                let hi = lo + *(p.add(32) as *const u64);
                let mut a = lo;
                let mut seen = 0u64;
                while a < hi {
                    if let Some((name, start)) = symbol_start(a) {
                        if start != seen {
                            seen = start;
                            if name == entry_hint {
                                return Some(start);
                            }
                        }
                    }
                    a += 4;
                }
            }
            p = p.add(cmdsize as usize);
        }
    }
    None
}

/// Experiment S1/S2: full signing with declassified values pinned.
///
/// Run A: honest signing with secret set A, *recording* the declassified
/// 16-byte values at the points where they are produced:
///   R            = return value of prf_msg,
///   PK_FORS      = return value of thash(.., ADRS{type=FORS_ROOTS}, ..),
///   root_j (x7)  = return value of thash(.., ADRS{type=TREE, height=9}, ..)
///                  (the XMSS root recomputed from the layer-j signature).
/// Run B: same public inputs (m, PK.seed, PK.root), *different* SK.seed,
/// SK.prf and addrnd, with those nine return values overwritten by the
/// recorded ones. Everything else the code computes in run B (every FORS
/// secret, every WOTS secret and chain value, every tree node) is different.
/// The audit's claim "the trace depends on the secrets only through R,
/// PK_FORS and the XMSS roots (which are public, since the verifier
/// recomputes them)" predicts identical traces. Without pinning the traces
/// must differ (control).
fn run_sign(entry: Entry, name: &str, ctxlen: u16, pubs: usize, secrets: usize, mem_hooks: bool, threads: usize, seed: u64) -> bool {
    let thash = find_fn("slhdsa::hash::thash");
    let prf = find_fn("slhdsa::hash::prf_msg");
    println!("### {name}: declassification-pinned trace comparison ({})\n", if mem_hooks { "control flow + memory addresses" } else { "control flow only" });
    let (Some(thash), Some(prf)) = (thash, prf) else {
        println!("INCONCLUSIVE: could not locate out-of-line `thash` ({thash:?}) / `prf_msg` ({prf:?}) symbols in this build (inlined or stripped); experiment not run.");
        return false;
    };
    let results = Arc::new(Mutex::new(Vec::new()));
    let jobs = Arc::new(Mutex::new((0..pubs).rev().collect::<Vec<_>>()));
    let mut hs = Vec::new();
    for _ in 0..threads.min(pubs) {
        let (results, jobs) = (results.clone(), jobs.clone());
        hs.push(std::thread::spawn(move || {
            let mut emu = Emu::new(mem_hooks);
            emu.st.dc.thash = thash;
            emu.st.dc.prf_msg = prf;
            loop {
                let Some(p) = jobs.lock().unwrap().pop() else { break };
                let mut log = Vec::new();
                let mut ok = true;
                let mut rng = Rng::new(seed ^ (p as u64 + 1).wrapping_mul(0x9E6C63D0876A9A47));
                let mlen = [32usize, 0, 100, 1][p % 4];
                let mut a = sign_input(&mut rng, mlen);
                a[OFF_B..OFF_B + 2].copy_from_slice(&ctxlen.to_le_bytes());
                set_honest_root(&mut a);
                // run A: record
                emu.st.dc.enabled = true;
                emu.st.dc.record = true;
                emu.st.dc.values.clear();
                let (sa, outa) = match emu.run(entry, &a, None) {
                    Ok(x) => x,
                    Err(e) => {
                        results.lock().unwrap().push((p, false, vec![format!("run A failed: {e}")], 0, 0, 0, 0u64, 0u64));
                        continue;
                    }
                };
                let nrec = emu.st.dc.values.len();
                let native_ok = outa == native(entry, &a);
                let recorded = emu.st.dc.values.clone();
                // sanity: the recorded values are exactly R (sig[0..16]) and nothing unexpected
                let r_ok = nrec == 9 && recorded[0][..] == outa[0..16];
                if !native_ok || !r_ok {
                    ok = false;
                    log.push(format!("sanity failure: emu==native {native_ok}, recorded {nrec} declassified values (expected 9), R matches signature prefix: {}", nrec > 0 && recorded[0][..] == outa[0..16]));
                }
                // sanity: replaying A's values into A is a no-op
                emu.st.dc.record = false;
                match emu.run(entry, &a, None) {
                    Ok((s, o)) => {
                        if s != sa || o != outa {
                            ok = false;
                            log.push("sanity failure: replaying A into A changed the trace/output".into());
                        }
                    }
                    Err(e) => {
                        ok = false;
                        log.push(format!("replay A failed: {e}"))
                    }
                }
                let (mut eq, mut ne, mut ctl_ne, mut ctl_eq) = (0, 0, 0, 0);
                for k in 0..secrets {
                    let mut b = a.clone();
                    new_secret(&mut b, &mut rng, false);
                    // (PK.seed, PK.root, m unchanged; SK.seed, SK.prf, addrnd fresh)
                    emu.st.dc.enabled = true;
                    emu.st.dc.record = false;
                    emu.st.dc.values = recorded.clone();
                    match emu.run(entry, &b, None) {
                        Ok((sb, outb)) => {
                            let applied = emu.st.dc.applied;
                            if applied != 9 {
                                ok = false;
                                log.push(format!("secret {k}: {applied} values pinned (expected 9)"));
                            }
                            if sb == sa {
                                eq += 1;
                            } else {
                                ne += 1;
                                ok = false;
                                let d = emu.first_divergence(entry, &a, &sa, &b, &sb);
                                log.push(format!("secret {k}: PINNED TRACES DIFFER: {d}"));
                            }
                            // the secret-derived signature bytes must really differ
                            if outb[16..7856] == outa[16..7856] {
                                ok = false;
                                log.push(format!("secret {k}: signature bodies identical?!"));
                            }
                        }
                        Err(e) => {
                            ok = false;
                            log.push(format!("secret {k}: run failed: {e}"))
                        }
                    }
                    // control: same B without pinning -> trace must differ
                    if k < 2 {
                        emu.st.dc.enabled = false;
                        match emu.run(entry, &b, None) {
                            Ok((sb, _)) => {
                                if sb == sa {
                                    ctl_eq += 1;
                                    ok = false;
                                    log.push(format!("secret {k}: unpinned control did NOT differ"));
                                } else {
                                    ctl_ne += 1;
                                }
                            }
                            Err(e) => log.push(format!("control run failed: {e}")),
                        }
                    }
                }
                let _ = ctl_eq;
                eprintln!("  {} public config {p}: pinned equal {eq}, differ {ne}; unpinned controls differing {ctl_ne}", "sign");
                results.lock().unwrap().push((p, ok, log, eq, ne, ctl_ne, sa.n_insn, sa.n_ev));
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let mut res = Arc::try_unwrap(results).ok().unwrap().into_inner().unwrap();
    res.sort_by_key(|r| r.0);
    println!("| public config (m, PK.seed, key A) | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |");
    println!("|---|---|---|---|---|---|---|---|");
    let mut all = true;
    for (p, ok, _log, eq, ne, ctl, insn, ev) in &res {
        all &= *ok;
        println!("| {p} | {} | {eq} | {ne} | {ctl}/{} | {insn} | {ev} | {} |", eq + ne, (eq + ne).min(2), if *ok { "PASS" } else { "**FAIL**" });
    }
    for (p, _, log, ..) in &res {
        for l in log {
            println!("- config {p}: {l}");
        }
    }
    println!();
    all
}

/// Experiment S3: unconditioned whole-signature profile. Fixed public
/// (m, PK.seed), random honest keys and addrnd. The traces differ (public
/// transcript differs); we report what is nevertheless invariant.
fn run_sign_profile(n: usize, threads: usize, seed: u64) {
    println!("### slh_sign_internal: unconditioned profile over random honest keys (m and PK.seed fixed)\n");
    let rows = Arc::new(Mutex::new(Vec::new()));
    let jobs = Arc::new(Mutex::new((0..n).rev().collect::<Vec<_>>()));
    let thash = find_fn("slhdsa::hash::thash");
    let sha = find_fn("slhdsa::sha256::sha256");
    let mut base = sign_input(&mut Rng::new(seed), 32);
    set_honest_root(&mut base);
    let base = Arc::new(base);
    let mut hs = Vec::new();
    for _ in 0..threads.min(n) {
        let (rows, jobs, base) = (rows.clone(), jobs.clone(), base.clone());
        hs.push(std::thread::spawn(move || {
            let mut emu = Emu::new(false);
            emu.st.profile = Some(HashMap::new());
            loop {
                let Some(k) = jobs.lock().unwrap().pop() else { break };
                let mut b = (*base).clone();
                if k > 0 {
                    let mut rng = Rng::new(seed ^ (k as u64).wrapping_mul(0xA24BAED4963EE407));
                    new_secret(&mut b, &mut rng, true);
                }
                emu.st.profile.as_mut().unwrap().clear();
                match emu.run(w_sign_internal, &b, None) {
                    Ok((s, _)) => {
                        let prof = emu.st.profile.as_ref().unwrap();
                        let c = |a: Option<u64>| a.and_then(|a| prof.get(&a).cloned()).unwrap_or(0);
                        // multiset of executed blocks, order-insensitive
                        let mut v: Vec<(u64, u64)> = prof.iter().map(|(a, n)| (*a, *n)).collect();
                        v.sort();
                        let mut h = 0u64;
                        for (a, n) in v {
                            h = (h.rotate_left(7) ^ a ^ n.wrapping_mul(0x9E3779B97F4A7C15)).wrapping_mul(0xC2B2AE3D27D4EB4F);
                        }
                        rows.lock().unwrap().push((k, s.n_insn, s.n_blocks, s.n_stub, c(thash), c(sha), h, s.h.0));
                    }
                    Err(e) => eprintln!("profile run {k} failed: {e}"),
                }
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let mut rows = Arc::try_unwrap(rows).ok().unwrap().into_inner().unwrap();
    rows.sort();
    let distinct = |f: &dyn Fn(&(usize, u64, u64, u64, u64, u64, u64, u64)) -> u64| {
        let mut v: Vec<u64> = rows.iter().map(|r| f(r)).collect();
        v.sort();
        v.dedup();
        v
    };
    let insn = distinct(&|r| r.1);
    println!("- runs: {} (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and m fixed)", rows.len());
    println!("- distinct full control-flow traces: {} (expected: all distinct, the public transcript differs)", distinct(&|r| r.7).len());
    println!("- distinct executed-instruction counts: {} (min {}, max {}, spread {})", insn.len(), insn.first().unwrap(), insn.last().unwrap(), insn.last().unwrap() - insn.first().unwrap());
    println!("- distinct basic-block counts: {}", distinct(&|r| r.2).len());
    println!("- distinct call-out (malloc/realloc/free/memcpy) counts: {:?}", distinct(&|r| r.3));
    println!("- distinct `thash` call counts: {:?}", distinct(&|r| r.4));
    println!("- distinct `sha256` call counts: {:?}", distinct(&|r| r.5));
    println!("- distinct block-execution histograms (multiset of executed blocks, order ignored): {}", distinct(&|r| r.6).len());
    println!();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut mode = "components".to_string();
    let mut filter = String::new();
    let mut scale = 1.0f64;
    let mut threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(12);
    let mut seed = 0x51_4844_5341u64;
    let mut pubs = 3usize;
    let mut secrets = 3usize;
    let mut nomem = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--filter" => {
                i += 1;
                filter = args[i].clone()
            }
            "--scale" => {
                i += 1;
                scale = args[i].parse().unwrap()
            }
            "--threads" => {
                i += 1;
                threads = args[i].parse().unwrap()
            }
            "--seed" => {
                i += 1;
                seed = args[i].parse().unwrap()
            }
            "--pubs" => {
                i += 1;
                pubs = args[i].parse().unwrap()
            }
            "--secrets" => {
                i += 1;
                secrets = args[i].parse().unwrap()
            }
            "--no-mem" => nomem = true,
            m => mode = m.to_string(),
        }
        i += 1;
    }
    let (mut maj, mut min) = (0u32, 0u32);
    let v = unsafe { uc_version(&mut maj, &mut min) };
    eprintln!("unicorn {}.{} (0x{:x}), {} threads, seed {}", maj, min, v, threads, seed);
    let ok = match mode.as_str() {
        "list" => {
            for t in targets() {
                println!("{}", t.name);
            }
            true
        }
        "components" => run_components(&filter, scale, threads, seed),
        "sign" => run_sign(w_sign_internal, "slh_sign_internal", 0, pubs, secrets, !nomem, threads, seed),
        "sign-ctx" => run_sign(w_sign, "slh_sign (ctx of 17 bytes)", 17, pubs, secrets, !nomem, threads, seed),
        "sign-profile" => {
            run_sign_profile(pubs, threads, seed);
            true
        }
        m => {
            eprintln!("unknown mode {m}");
            false
        }
    };
    std::process::exit(if ok { 0 } else { 1 });
}
