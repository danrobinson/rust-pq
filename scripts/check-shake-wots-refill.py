#!/usr/bin/env python3
"""Re-extract sort_descending across 3 targets, symbolically replay rust/src/shake/batch.rs WOTS+, and audit all Shakeopt Lean proofs."""
from pathlib import Path
import os
import runpy
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SRC = ROOT / "rust/src"
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
from build import function

facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
LEAN, run = facade["LEAN"], facade["run"]

WOTS_FUNCTIONS = (
    "word",
    "seed_words",
    "adrs_words",
    "extract_lane",
    "refill_short_inplace",
    "fill_prf",
    "keygen",
    "sort_descending",
    "sign",
    "recover",
)

WOTS_THEOREMS = [
    "Shakeopt.WotsRefill.sort_descending_spec",
    "Shakeopt.WotsRefill.sort_descending_perm",
    "Shakeopt.WotsRefill.wots_keygen_batch_eq",
    "Shakeopt.WotsRefill.refill_engine_spec",
    "Shakeopt.WotsRefill.wots_sign_refill_eq",
    "Shakeopt.WotsRefill.wots_recover_refill_eq",
]

ALL_AUDIT = {
    "Shakeopt.Segmented": [
        "Shakeopt.Segmented.keccak_feed_append",
        "Shakeopt.Segmented.sponge_absorb_append",
        "Shakeopt.Segmented.prf_msg_ctx_spec",
        "Shakeopt.Segmented.prf_msg_ctx_params",
        "Shakeopt.Segmented.prf_msg_ctx_eq_contiguous",
        "Shakeopt.Segmented.h_msg_ctx_spec",
        "Shakeopt.Segmented.h_msg_ctx_params",
        "Shakeopt.Segmented.h_msg_ctx_eq_contiguous",
        "Shakeopt.Segmented.shake_sign_ctx_spec",
        "Shakeopt.Segmented.shake_verify_ctx_spec",
        "Shakeopt.Segmented.slh_sign_spec",
        "Shakeopt.Segmented.slh_verify_spec",
    ],
    "Shakeopt.ForsHoriz": [
        "Shakeopt.ForsHoriz.fors_sibling_index",
        "Shakeopt.ForsHoriz.fors_climb_parity",
        "Shakeopt.ForsHoriz.fors_subtree_horiz_eq",
        "Shakeopt.ForsHoriz.fors_sign_horiz_eq",
        "Shakeopt.ForsHoriz.fors_sign_fallback_eq",
        "Shakeopt.ForsHoriz.fors_recover_batch_eq",
    ],
    "Shakeopt.WotsRefill": WOTS_THEOREMS,
}

HARNESS_TEMPLATE = r"""
#![allow(dead_code, unused_imports, unused_variables)]
extern crate alloc;

#[path = "ADDRESS_PATH"]
mod address;
#[path = "PARAMS_PATH"]
mod params;
#[path = "UTIL_PATH"]
mod util;

use std::cell::RefCell;
use std::collections::HashMap;
use address::{Adrs, WOTS_HASH, WOTS_PK, WOTS_PRF};
use params::{LEN2, LEN_MAX, W};

const WIDTH: usize = PROOF_WIDTH;

/// Hash-consed injective symbolic SHAKE256 oracle.
struct Oracle {
    ids: HashMap<Vec<u8>, u64>,
    next_id: u64,
    perm_calls: usize,
    perm_lanes: usize,
    sponge_calls: usize,
}

impl Oracle {
    fn new() -> Self {
        Self {
            ids: HashMap::new(),
            next_id: 1,
            perm_calls: 0,
            perm_lanes: 0,
            sponge_calls: 0,
        }
    }

    fn mix(mut x: u64) -> u64 {
        x = x.wrapping_add(0x9e3779b97f4a7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        x ^ (x >> 31)
    }

    fn shake_words(&mut self, msg: &[u8]) -> [u64; 25] {
        let next = &mut self.next_id;
        let id = *self.ids.entry(msg.to_vec()).or_insert_with(|| {
            let id = *next;
            *next += 1;
            id
        });
        let mut out = [0u64; 25];
        for w in 0..25 {
            let v = Self::mix(id.wrapping_mul(0x100000001b3) ^ ((w as u64 + 1) << 56));
            out[w] = if w == 0 {
                (id << 16) ^ (v & 0xffff) ^ 0xA55A
            } else {
                v | 1
            };
        }
        out
    }

    fn shake_bytes<const N: usize>(&mut self, msg: &[u8]) -> [u8; N] {
        let words = self.shake_words(msg);
        let mut out = [0u8; N];
        for j in 0..N / 8 {
            out[8 * j..8 * j + 8].copy_from_slice(&words[j].to_le_bytes());
        }
        out
    }
}

thread_local! {
    static ORACLE: RefCell<Oracle> = RefCell::new(Oracle::new());
}

mod shake256 {
    use super::*;
    pub mod parallel {
        use super::*;
        pub const WIDTH: usize = PROOF_WIDTH;
        pub type States = [[u64; WIDTH]; 25];

        pub fn permute_active(s: &mut States, active: usize) {
            assert!((1..=WIDTH).contains(&active), "invalid active count {active}");
            ORACLE.with(|o| {
                let mut o = o.borrow_mut();
                o.perm_calls += 1;
                o.perm_lanes += active;
                for lane in 0..active {
                    let mut raw = [0u8; 200];
                    for w in 0..25 {
                        raw[8 * w..8 * w + 8].copy_from_slice(&s[w][lane].to_le_bytes());
                    }
                    assert_eq!(
                        &raw[136..200],
                        &[0u8; 64],
                        "non-zero capacity bytes in permute_active lane {lane}"
                    );
                    assert_eq!(
                        raw[135] & 0x80,
                        0x80,
                        "missing 0x80 end-of-rate padding bit in lane {lane}"
                    );
                    raw[135] &= !0x80;
                    let pad_pos = raw[..136]
                        .iter()
                        .rposition(|&b| b != 0)
                        .expect("missing 0x1f SHAKE domain byte");
                    assert_eq!(
                        raw[pad_pos], 0x1f,
                        "expected 0x1f domain byte at offset {pad_pos}, got {:#x}",
                        raw[pad_pos]
                    );
                    assert!(
                        pad_pos == 64 || pad_pos == 80 || pad_pos == 96,
                        "unexpected FIPS 205 WOTS short-hash input length {pad_pos}"
                    );
                    let words = o.shake_words(&raw[..pad_pos]);
                    for w in 0..25 {
                        s[w][lane] = words[w];
                    }
                }
            });
        }
    }

    pub struct Sponge {
        buf: Vec<u8>,
    }

    impl Sponge {
        pub fn new() -> Self {
            Self { buf: Vec::new() }
        }
        pub fn absorb(&mut self, data: &[u8]) {
            self.buf.extend_from_slice(data);
        }
        pub fn finish(self, out: &mut [u8]) {
            ORACLE.with(|o| {
                let mut o = o.borrow_mut();
                o.sponge_calls += 1;
                let words = o.shake_words(&self.buf);
                let mut raw = [0u8; 200];
                for w in 0..25 {
                    raw[8 * w..8 * w + 8].copy_from_slice(&words[w].to_le_bytes());
                }
                out.copy_from_slice(&raw[..out.len()]);
            });
        }
    }
}

mod shake {
    pub mod hash {
        use crate::address::Adrs;
        use crate::shake256::Sponge;

        pub fn start<const N: usize>(seed: &[u8; N], adrs: &Adrs) -> Sponge {
            let mut s = Sponge::new();
            s.absorb(seed);
            s.absorb(&adrs.full());
            s
        }

        pub fn digest<const N: usize>(sponge: Sponge) -> [u8; N] {
            let mut out = [0u8; N];
            sponge.finish(&mut out);
            out
        }
    }

    pub mod batch {
        use super::hash::{digest, start};
        use crate::address::{Adrs, WOTS_HASH, WOTS_PK, WOTS_PRF};
        use crate::params::{LEN2, LEN_MAX, W};
        use crate::shake256::parallel::{self, States, WIDTH};
        use crate::util::block;
        use alloc::vec::Vec;

        // PRODUCTION_WOTS_FUNCTIONS

        pub fn run_sort(steps: &[u32]) -> ([usize; LEN_MAX], usize) {
            sort_descending(steps)
        }
    }

    pub fn wots_keygen<const N: usize>(sk: &[u8; N], seed: &[u8; N], addr: crate::address::Adrs) -> [u8; N] {
        batch::keygen(sk, seed, addr)
    }
    pub fn wots_sign<const N: usize>(sk: &[u8; N], seed: &[u8; N], addr: crate::address::Adrs, digits: &[u32]) -> Vec<u8> {
        batch::sign(sk, seed, addr, digits)
    }
    pub fn wots_recover<const N: usize>(sig: &[u8], seed: &[u8; N], addr: crate::address::Adrs, digits: &[u32]) -> [u8; N] {
        batch::recover(sig, seed, addr, digits)
    }
}

// --- Textbook FIPS 205 Algorithms 5, 6, 7, 8 over the exact same symbolic oracle ---

fn ref_shake<const N: usize>(parts: &[&[u8]]) -> [u8; N] {
    let mut msg = Vec::new();
    for p in parts {
        msg.extend_from_slice(p);
    }
    ORACLE.with(|o| o.borrow_mut().shake_bytes::<N>(&msg))
}

fn ref_chain<const N: usize>(
    mut x: [u8; N],
    start_step: u32,
    steps: u32,
    seed: &[u8; N],
    adrs: Adrs,
) -> [u8; N] {
    for j in 0..steps {
        let a = adrs.with_word3(start_step + j);
        x = ref_shake(&[seed, &a.full(), &x]);
    }
    x
}

fn ref_wots_pk_gen<const N: usize>(sk: &[u8; N], seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    let len = 2 * N + LEN2;
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let hash_adrs = adrs.with_type(WOTS_HASH).with_keypair(adrs.keypair);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    let mut tmp = Vec::with_capacity(len * N);
    for i in 0..len {
        let secret = ref_shake::<N>(&[seed, &sk_adrs.with_word2(i as u32).full(), sk]);
        let end = ref_chain(secret, 0, W - 1, seed, hash_adrs.with_word2(i as u32));
        tmp.extend_from_slice(&end);
    }
    ref_shake(&[seed, &pk_adrs.full(), &tmp])
}

fn ref_wots_sign<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    adrs: Adrs,
    digits: &[u32],
) -> Vec<u8> {
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let hash_adrs = adrs.with_type(WOTS_HASH).with_keypair(adrs.keypair);
    let mut sig = Vec::with_capacity(digits.len() * N);
    for (i, &d) in digits.iter().enumerate() {
        let secret = ref_shake::<N>(&[seed, &sk_adrs.with_word2(i as u32).full(), sk]);
        let end = ref_chain(secret, 0, d, seed, hash_adrs.with_word2(i as u32));
        sig.extend_from_slice(&end);
    }
    sig
}

fn ref_wots_pk_from_sig<const N: usize>(
    sig: &[u8],
    seed: &[u8; N],
    adrs: Adrs,
    digits: &[u32],
) -> [u8; N] {
    let hash_adrs = adrs.with_type(WOTS_HASH).with_keypair(adrs.keypair);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    let mut tmp = Vec::with_capacity(digits.len() * N);
    for (i, &d) in digits.iter().enumerate() {
        let blk = util::block::<N>(sig, i);
        let end = ref_chain(blk, d, (W - 1) - d, seed, hash_adrs.with_word2(i as u32));
        tmp.extend_from_slice(&end);
    }
    ref_shake(&[seed, &pk_adrs.full(), &tmp])
}

fn check_sort(steps: &[u32]) {
    let (order, total) = shake::batch::run_sort(steps);
    let expected_total = steps.iter().filter(|&&s| s > 0).count();
    assert_eq!(total, expected_total);
    let mut seen = vec![false; steps.len()];
    for j in 0..total {
        let idx = order[j];
        assert!(idx < steps.len());
        assert!(steps[idx] > 0);
        assert!(!seen[idx], "duplicate index {idx} in sort_descending");
        seen[idx] = true;
        if j > 0 {
            assert!(steps[order[j - 1]] >= steps[idx], "not descending at {j}");
        }
    }
    for (i, &s) in steps.iter().enumerate() {
        assert_eq!(seen[i], s > 0);
    }
}

fn test_width<const N: usize>() {
    let len = 2 * N + LEN2;
    let sk: [u8; N] = core::array::from_fn(|i| (0x41u8).wrapping_add(i as u8 * 13));
    let seed: [u8; N] = core::array::from_fn(|i| (0x87u8).wrapping_add(i as u8 * 17));
    let adrs = Adrs {
        layer: 3,
        tree: 0x1122_3344_5566_7788,
        typ: WOTS_HASH,
        keypair: 29,
        word2: 7,
        word3: 11,
    };

    // 1. Keygen
    let got_pk = shake::wots_keygen::<N>(&sk, &seed, adrs);
    let exp_pk = ref_wots_pk_gen::<N>(&sk, &seed, adrs);
    assert_eq!(got_pk, exp_pk, "WOTS keygen mismatch N={N} WIDTH={WIDTH}");

    // 2. Edge-case + mixed digit vectors
    let mut vectors: Vec<(&str, Vec<u32>)> = vec![
        ("all_zero", vec![0u32; len]),
        ("all_max", vec![15u32; len]),
        ("all_one", vec![1u32; len]),
        ("alt_0_15", (0..len).map(|i| if i % 2 == 0 { 0 } else { 15 }).collect()),
        ("alt_15_0", (0..len).map(|i| if i % 2 == 0 { 15 } else { 0 }).collect()),
        ("ascending", (0..len).map(|i| (i % 16) as u32).collect()),
        ("descending", (0..len).map(|i| (15 - (i % 16)) as u32).collect()),
        ("mixed_a", (0..len).map(|i| ((i * 7 + 3) % 16) as u32).collect()),
        ("mixed_b", (0..len).map(|i| ((i * 11 + 5) % 16) as u32).collect()),
        ("sparse_w_minus_1", (0..len).map(|i| if i < WIDTH - 1 { (i as u32 % 15) + 1 } else { 0 }).collect()),
        ("sparse_w", (0..len).map(|i| if i < WIDTH { (i as u32 % 15) + 1 } else { 0 }).collect()),
        ("sparse_w_plus_1", (0..len).map(|i| if i <= WIDTH { (i as u32 % 15) + 1 } else { 0 }).collect()),
    ];
    for pos in [0, len / 2, len - 1] {
        for val in [1u32, 15u32] {
            let mut v = vec![0u32; len];
            v[pos] = val;
            vectors.push(("single_nonzero", v));
        }
    }

    for (label, digits) in vectors {
        check_sort(&digits);
        let rem: Vec<u32> = digits.iter().map(|&d| (W - 1) - d).collect();
        check_sort(&rem);

        let got_sig = shake::wots_sign::<N>(&sk, &seed, adrs, &digits);
        let exp_sig = ref_wots_sign::<N>(&sk, &seed, adrs, &digits);
        assert_eq!(got_sig, exp_sig, "WOTS sign mismatch N={N} WIDTH={WIDTH} case={label}");

        let got_rec = shake::wots_recover::<N>(&got_sig, &seed, adrs, &digits);
        let exp_rec = ref_wots_pk_from_sig::<N>(&got_sig, &seed, adrs, &digits);
        assert_eq!(got_rec, exp_rec, "WOTS recover mismatch N={N} WIDTH={WIDTH} case={label}");
        assert_eq!(got_rec, exp_pk, "WOTS sign->recover roundtrip mismatch N={N} WIDTH={WIDTH} case={label}");

        // Synthetic arbitrary signature bytes (non-genuine) for recover
        let synth: Vec<u8> = (0..len * N).map(|i| ((i * 29 + 7) ^ (i >> 4)) as u8).collect();
        let got_rec2 = shake::wots_recover::<N>(&synth, &seed, adrs, &digits);
        let exp_rec2 = ref_wots_pk_from_sig::<N>(&synth, &seed, adrs, &digits);
        assert_eq!(got_rec2, exp_rec2, "WOTS recover synthetic mismatch N={N} WIDTH={WIDTH} case={label}");
    }
    println!("WIDTH={WIDTH} N={N} (len={len}): verified keygen, sort_descending, sign, and recover across all 18 digit vectors");
}

fn main() {
    test_width::<16>();
    test_width::<24>();
    test_width::<32>();
    ORACLE.with(|o| {
        let o = o.borrow();
        println!(
            "WIDTH={WIDTH}: checked {} permute_active calls ({} active lanes) and {} sponge calls",
            o.perm_calls, o.perm_lanes, o.sponge_calls
        );
    });
}
"""


def check_sort_extraction(scratch: Path, target: str) -> None:
    package = scratch / "Sort"
    llbc = scratch / "sort.llbc"
    run(
        [
            ROOT / ".tools/aeneas/charon/bin/charon",
            "cargo",
            "--preset=aeneas",
            "--start-from",
            "crate::shake::batch::sort_descending",
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "platform-sha2",
            "--target",
            target,
        ],
        ROOT / "rust",
    )
    run(
        [
            ROOT / ".tools/aeneas/bin/aeneas",
            "-backend",
            "lean",
            "-abort-on-error",
            "-no-progress-bar",
            "-namespace",
            "ShakeoptSort",
            "-split-files",
            "-dest",
            package,
            llbc,
        ],
        ROOT,
    )
    if {p.name for p in package.iterdir()} != {"Types.lean", "Funs.lean"}:
        raise ValueError(f"unexpected sort_descending external dependencies on {target}: {list(package.iterdir())}")
    funs = (package / "Funs.lean").read_text().replace("public import Sort.Types", "public import Shakeopt.Sort.Types")
    if funs != (LEAN / "Shakeopt/Sort/Funs.lean").read_text():
        raise ValueError(f"sort_descending Funs.lean differs on {target}")
    if (package / "Types.lean").read_bytes() != (LEAN / "Shakeopt/Sort/Types.lean").read_bytes():
        raise ValueError(f"sort_descending Types.lean differs on {target}")
    print(f"{target}: matched Shakeopt.Sort extraction (sort_descending, zero external dependencies)", flush=True)


def run_symbolic_replay(width: int) -> None:
    batch_src = (SRC / "shake/batch.rs").read_text()
    wots_funs = "\n\n".join(function(batch_src, name) for name in WOTS_FUNCTIONS)

    code = HARNESS_TEMPLATE
    code = code.replace("ADDRESS_PATH", str(SRC / "address.rs"))
    code = code.replace("PARAMS_PATH", str(SRC / "params.rs"))
    code = code.replace("UTIL_PATH", str(SRC / "util.rs"))
    code = code.replace("PROOF_WIDTH", str(width))
    code = code.replace("// PRODUCTION_WOTS_FUNCTIONS", wots_funs)

    with tempfile.TemporaryDirectory(prefix=f"shake-wots-w{width}-") as tmp:
        src = Path(tmp) / "probe.rs"
        exe = Path(tmp) / "probe"
        src.write_text(code)
        subprocess.run(["rustc", "--edition=2021", "-O", src, "-o", exe], check=True)
        subprocess.run([exe], check=True)


def main() -> None:
    os.environ["PATH"] = os.pathsep.join(
        [str(Path.home() / ".elan/bin"), str(Path.home() / ".cargo/bin"), os.environ["PATH"]]
    )
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            check_sort_extraction(Path(tmp), target)
    for width in (8, 3):
        run_symbolic_replay(width)
    run(["lake", "build", "Shakeopt.Segmented", "Shakeopt.ForsHoriz", "Shakeopt.WotsRefill"], LEAN)
    for module, theorems in ALL_AUDIT.items():
        facade["audit_theorems"](module, theorems)
        print(
            f"{module}: audited {len(theorems)} theorems strictly within [propext, Classical.choice, Quot.sound]",
            flush=True,
        )


if __name__ == "__main__":
    main()
