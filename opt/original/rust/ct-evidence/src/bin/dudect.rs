//! dudect-style timing leakage test (Reparaz, Balasch, Verbauwhede 2017).
//!
//! Two input classes that share ALL public inputs and differ only in the
//! secret bytes: class 0 uses one fixed secret, class 1 a fresh pseudo-random
//! secret for every measurement. The class of each measurement is chosen at
//! random, inputs are prepared before the clock starts, and execution times
//! are compared with Welch's t-test, on the raw data and on 100 cropped
//! versions (measurements above a percentile threshold are discarded, with
//! the dudect thresholds 1 - 0.5^(10(i+1)/100)). |t| > 4.5 is the conventional
//! "leak detected" threshold.
//!
//! Noise floor: the same statistic is computed on two *null* splits (class-1
//! samples split by parity of their arrival order, and likewise for class 0),
//! which by construction contain no input-dependent signal.

use ct_evidence::*;
use std::time::Instant;

extern "C" {
    fn mach_absolute_time() -> u64;
    fn mach_timebase_info(info: *mut [u32; 2]) -> i32;
    fn pthread_set_qos_class_self_np(qos: u32, rel: i32) -> i32;
}

fn now() -> u64 {
    unsafe { mach_absolute_time() }
}

#[derive(Clone, Copy, Default)]
struct Acc {
    n: f64,
    mean: f64,
    m2: f64,
}
impl Acc {
    fn push(&mut self, x: f64) {
        self.n += 1.0;
        let d = x - self.mean;
        self.mean += d / self.n;
        self.m2 += d * (x - self.mean);
    }
    fn var(&self) -> f64 {
        self.m2 / (self.n - 1.0)
    }
}
fn welch(a: &Acc, b: &Acc) -> f64 {
    if a.n < 2.0 || b.n < 2.0 {
        return 0.0;
    }
    let den = (a.var() / a.n + b.var() / b.n).sqrt();
    if den == 0.0 {
        return 0.0;
    }
    (a.mean - b.mean) / den
}

/// max |t| over the uncropped test and the 100 dudect croppings.
/// Returns (t_uncropped, max |t|, index of the cropping attaining it (-1 = uncropped)).
fn dudect_stat(samples: &[(u8, f64)]) -> (f64, f64, i32) {
    let mut sorted: Vec<f64> = samples.iter().map(|s| s.1).collect();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let t_of = |thr: f64| {
        let mut acc = [Acc::default(); 2];
        for &(c, x) in samples {
            if x <= thr {
                acc[c as usize].push(x);
            }
        }
        welch(&acc[0], &acc[1])
    };
    let t0 = t_of(f64::INFINITY);
    let (mut best, mut arg) = (t0.abs(), -1);
    for i in 0..100 {
        let q = 1.0 - 0.5f64.powf(10.0 * (i as f64 + 1.0) / 100.0);
        let idx = ((sorted.len() as f64 * q) as usize).min(sorted.len() - 1);
        let t = t_of(sorted[idx]).abs();
        if t > best {
            best = t;
            arg = i;
        }
    }
    (t0, best, arg)
}

fn null_stat(samples: &[(u8, f64)], class: u8) -> f64 {
    let mut k = 0u8;
    let relabelled: Vec<(u8, f64)> = samples
        .iter()
        .filter(|s| s.0 == class)
        .map(|s| {
            k ^= 1;
            (k, s.1)
        })
        .collect();
    if relabelled.len() < 8 {
        return 0.0;
    }
    dudect_stat(&relabelled).1
}

fn median(v: &mut Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

struct Report {
    name: String,
    what: String,
    reps: usize,
    n0: usize,
    n1: usize,
    med0: f64,
    med1: f64,
    t_raw: f64,
    t_max: f64,
    crop: i32,
    null_rand: f64,
    null_fixed: f64,
    /// difference of class means (class 0 - class 1) over the samples below the
    /// pooled 90th percentile, in ns per call, and relative to the mean
    delta_ns: f64,
    delta_rel: f64,
    /// standard error of the (uncropped) difference of class means, ns per call
    se_ns: f64,
    secs: f64,
}

fn trimmed_delta(samples: &[(u8, f64)]) -> (f64, f64) {
    let mut sorted: Vec<f64> = samples.iter().map(|s| s.1).collect();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let thr = sorted[(sorted.len() * 9 / 10).min(sorted.len() - 1)];
    let mut acc = [Acc::default(); 2];
    for &(c, x) in samples {
        if x <= thr {
            acc[c as usize].push(x);
        }
    }
    let d = acc[0].mean - acc[1].mean;
    (d, d / (0.5 * (acc[0].mean + acc[1].mean)))
}

fn print_header() {
    println!("| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
}
fn print_row(r: &Report, expect_leak: bool) {
    let leak = r.t_max > 4.5;
    let verdict = match (leak, expect_leak) {
        (false, false) => "no leak detected",
        (true, false) => "**t > 4.5**",
        (true, true) => "leak detected (expected: control)",
        (false, true) => "**control NOT detected**",
    };
    println!(
        "| {} | {} | {} | {} | {} | {:.1} | {:.1} | {:+.3} | {:+.4}% | {:+.2} | {:.2}{} | {:.2} | {:.2} | {} | {:.3} |",
        r.name,
        r.what,
        r.reps,
        r.n0,
        r.n1,
        r.med0,
        r.med1,
        r.delta_ns,
        r.delta_rel * 100.0,
        r.t_raw,
        r.t_max,
        if r.crop >= 0 { format!(" (crop {})", r.crop) } else { String::new() },
        r.null_rand,
        r.null_fixed,
        verdict,
        r.se_ns
    );
    use std::io::Write;
    std::io::stdout().flush().ok();
    eprintln!("  [{}] done in {:.1}s", r.name, r.secs);
}

/// Generic measurement loop. `prep(class, rng, buf)` writes the input for one
/// measurement into `buf` (outside the timed region).
fn measure(
    name: &str,
    what: &str,
    f: Entry,
    n_total: usize,
    ns_per_tick: f64,
    seed: u64,
    prep: &mut dyn FnMut(u8, &mut Rng, &mut [u8]),
) -> Report {
    let started = Instant::now();
    let mut rng = Rng::new(seed);
    let mut out = vec![0u8; OUT_MAX];
    let mut buf = vec![0u8; IN_MAX];
    // calibrate: at least ~20 us per measurement (the clock ticks at ~42 ns)
    prep(1, &mut rng, &mut buf);
    let mut reps = 1usize;
    let per_meas_ns;
    loop {
        let t0 = now();
        for _ in 0..reps {
            f(std::hint::black_box(buf.as_ptr()), out.as_mut_ptr());
        }
        let dt = (now() - t0) as f64 * ns_per_tick;
        if dt >= 20_000.0 || reps >= 1 << 14 {
            per_meas_ns = dt;
            break;
        }
        reps *= 2;
    }
    // warm-up: ~50 ms worth of measurements (at least 4), measured and discarded
    let warm = ((50e6 / per_meas_ns) as usize).clamp(4, 512);
    const BATCH: usize = 512;
    let mut samples: Vec<(u8, f64)> = Vec::with_capacity(n_total);
    let mut inputs = vec![0u8; BATCH * IN_MAX];
    let mut classes = vec![0u8; BATCH];
    // warm-up batch is measured and discarded
    let mut first = true;
    while samples.len() < n_total {
        let b = if first { warm } else { BATCH.min(n_total - samples.len()) };
        for k in 0..b {
            let c = (rng.next() >> 63) as u8;
            classes[k] = c;
            prep(c, &mut rng, &mut inputs[k * IN_MAX..(k + 1) * IN_MAX]);
        }
        for k in 0..b {
            let p = inputs[k * IN_MAX..].as_ptr();
            let t0 = now();
            for _ in 0..reps {
                f(std::hint::black_box(p), out.as_mut_ptr());
            }
            let dt = now() - t0;
            if !first {
                samples.push((classes[k], dt as f64 * ns_per_tick / reps as f64));
            }
        }
        std::hint::black_box(&out);
        first = false;
    }
    let (t_raw, t_max, crop) = dudect_stat(&samples);
    let mut v0: Vec<f64> = samples.iter().filter(|s| s.0 == 0).map(|s| s.1).collect();
    let mut v1: Vec<f64> = samples.iter().filter(|s| s.0 == 1).map(|s| s.1).collect();
    Report {
        name: name.to_string(),
        what: what.to_string(),
        reps,
        n0: v0.len(),
        n1: v1.len(),
        med0: median(&mut v0),
        med1: median(&mut v1),
        t_raw,
        t_max,
        crop,
        null_rand: null_stat(&samples, 1),
        null_fixed: null_stat(&samples, 0),
        delta_ns: trimmed_delta(&samples).0,
        delta_rel: trimmed_delta(&samples).1,
        se_ns: {
            let mut acc = [Acc::default(); 2];
            for &(c, x) in &samples {
                acc[c as usize].push(x);
            }
            (acc[0].var() / acc[0].n + acc[1].var() / acc[1].n).sqrt()
        },
        secs: started.elapsed().as_secs_f64(),
    }
}

fn set_honest_root(b: &mut [u8]) {
    let g = |o: usize| -> [u8; 16] { b[o..o + 16].try_into().unwrap() };
    let (sk, _pk) = slhdsa::slh_keygen_internal(&g(OFF_SK), &g(OFF_SK + 16), &g(OFF_SK + 32));
    b[OFF_SK..OFF_SK + 64].copy_from_slice(&sk);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut mode = "components".to_string();
    let mut filter = String::new();
    let mut scale = 1.0f64;
    let mut seed = 0xD0DEC7u64;
    let mut fixed_zero = false;
    let mut n_sign = 150usize;
    // class design for `components`: fixed-random (dudect default), or the
    // diagnostics fixed-fixed (two different fixed secrets) and random-random
    // (both classes fresh random: a true null experiment)
    let mut classes = "fixed-random".to_string();
    // set PSTATE.DIT (Arm data-independent-timing mode) for the measuring thread
    let mut dit = false;
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
            "--seed" => {
                i += 1;
                seed = args[i].parse().unwrap()
            }
            "--n" => {
                i += 1;
                n_sign = args[i].parse().unwrap()
            }
            "--fixed-zero" => fixed_zero = true,
            "--dit" => dit = true,
            "--classes" => {
                i += 1;
                classes = args[i].clone()
            }
            m => mode = m.to_string(),
        }
        i += 1;
    }
    let mut tb = [0u32; 2];
    unsafe {
        mach_timebase_info(&mut tb);
        pthread_set_qos_class_self_np(0x21, 0); // QOS_CLASS_USER_INTERACTIVE: prefer performance cores
    }
    let ns_per_tick = tb[0] as f64 / tb[1] as f64;
    let dit_state = unsafe {
        let mut v: u64;
        if dit {
            // msr DIT, #1
            core::arch::asm!(".inst 0xd503415f");
        }
        // mrs x0, DIT
        core::arch::asm!(".inst 0xd53b42a0", out("x0") v);
        (v >> 24) & 1
    };
    // observed clock granularity
    let mut gran = f64::INFINITY;
    for _ in 0..10000 {
        let a = now();
        let mut b = now();
        while b == a {
            b = now();
        }
        gran = gran.min((b - a) as f64 * ns_per_tick);
    }
    println!("clock: mach_absolute_time, {:.3} ns/tick, observed granularity {:.1} ns; PSTATE.DIT = {}; classes = {}; fixed class = {}; seed {}\n", ns_per_tick, gran, dit_state, classes, if fixed_zero { "all-zero secret" } else { "one fixed pseudo-random secret" }, seed);

    match mode.as_str() {
        "components" => {
            print_header();
            for (ti, t) in targets().iter().enumerate() {
                if t.dudect_n == 0 || !t.name.contains(&filter) {
                    continue;
                }
                let n_total = ((2 * t.dudect_n) as f64 * scale).ceil() as usize;
                let base = public_input(t, seed ^ (ti as u64) << 20);
                let mut fixed = base.clone();
                if fixed_zero {
                    for &(o, l) in &t.vary {
                        for x in &mut fixed[o..o + l] {
                            *x = 0;
                        }
                    }
                } else {
                    vary_input(t, &mut fixed, &mut Rng::new(seed ^ 0xF1ED ^ (ti as u64) << 20));
                }
                let mut fixed_b = base.clone();
                vary_input(t, &mut fixed_b, &mut Rng::new(seed ^ 0xF1EDB ^ (ti as u64) << 20));
                // class 0 / class 1 are fixed (true) or fresh random (false)
                let (c0_fixed, c1_fixed) = match classes.as_str() {
                    "fixed-random" => (true, false),
                    "fixed-fixed" => (true, true),
                    "random-random" => (false, false),
                    c => panic!("unknown --classes {c}"),
                };
                let mut prep = |c: u8, rng: &mut Rng, buf: &mut [u8]| {
                    let is_fixed = if c == 0 { c0_fixed } else { c1_fixed };
                    if is_fixed {
                        buf.copy_from_slice(if c == 0 { &fixed } else { &fixed_b });
                        // consume the same amount of PRNG output in both classes
                        let mut scratch = base.clone();
                        vary_input(t, &mut scratch, rng);
                    } else {
                        buf.copy_from_slice(&base);
                        vary_input(t, buf, rng);
                    }
                };
                let r = measure(&t.name, t.what, t.f, n_total, ns_per_tick, seed ^ (ti as u64 + 1) << 8, &mut prep);
                print_row(&r, !t.expect_equal);
            }
        }
        // Whole signature. Public inputs shared by both classes: m, PK.seed.
        "sign-key" | "sign-addrnd" => {
            let vary_key = mode == "sign-key";
            let mut rng = Rng::new(seed ^ 0x5167);
            let mut base = vec![0u8; IN_MAX];
            rng.fill(&mut base);
            base[OFF_A..OFF_A + 4].copy_from_slice(&32u32.to_le_bytes());
            set_honest_root(&mut base);
            let fixed = base.clone();
            let mut prep = |c: u8, rng: &mut Rng, buf: &mut [u8]| {
                buf.copy_from_slice(&fixed);
                if c == 1 {
                    rng.fill(&mut buf[OFF_ADDRND..OFF_ADDRND + 16]);
                    if vary_key {
                        rng.fill(&mut buf[OFF_SK..OFF_SK + 32]);
                        set_honest_root(buf); // real key pair for the new SK.seed (PK.seed unchanged)
                    }
                }
            };
            print_header();
            let (name, what) = if vary_key {
                ("slh_sign_internal (m, PK.seed fixed; honest keys)", "SK.seed, SK.prf, addrnd (PK.root changes with SK.seed)")
            } else {
                ("slh_sign_internal (m, whole key fixed)", "addrnd only")
            };
            let r = measure(name, what, w_sign_internal, 2 * n_sign, ns_per_tick, seed ^ 0xABCD, &mut prep);
            print_row(&r, false);
        }
        m => {
            eprintln!("unknown mode {m}");
            std::process::exit(2);
        }
    }
}
