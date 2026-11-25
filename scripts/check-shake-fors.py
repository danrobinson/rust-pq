#!/usr/bin/env python3
"""Lift production rust/src/shake/fors_batch.rs over a symbolic SHAKE256 oracle and audit Lean proofs."""

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

THEOREMS = [
    "Shakeopt.ForsHoriz.fors_sibling_index",
    "Shakeopt.ForsHoriz.fors_climb_parity",
    "Shakeopt.ForsHoriz.fors_subtree_horiz_eq",
    "Shakeopt.ForsHoriz.fors_sign_horiz_eq",
    "Shakeopt.ForsHoriz.fors_sign_fallback_eq",
    "Shakeopt.ForsHoriz.fors_recover_batch_eq",
]

BATCH_HELPERS = (
    "word",
    "seed_words",
    "adrs_words",
    "header_active",
    "put_active",
    "read_active",
    "short_active",
    "pair_active",
)

FORS_FUNCTIONS = (
    "word",
    "fors_leaves_fused",
    "fors_subtree_horiz",
    "batch_leaves_slice",
    "batch_pairs_slice",
    "nodes_fallback",
    "sign",
    "recover",
)

HARNESS_TEMPLATE = r"""
#![allow(dead_code, unused_imports, unused_variables)]
extern crate alloc;

#[path = "ADDRESS_PATH"]
mod address;
#[path = "PARAMS_PATH"]
mod params;

use std::cell::RefCell;
use std::collections::HashMap;
use address::{Adrs, FORS_PRF, FORS_ROOTS, FORS_TREE};
use params::{Params, K_MAX};

const WIDTH: usize = PROOF_WIDTH;

/// Hash-consed injective symbolic SHAKE256 oracle:
/// Every distinct absorbed input byte string gets a unique 64-bit symbol ID,
/// expanded deterministically into 200 non-zero distinct bytes across all 25 lanes.
/// Equality of two N-byte outputs implies exact equality of their entire symbolic
/// derivation trees (every input byte, address byte, domain separator, and child order).
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
            // Word 0 carries the unique symbol id directly in its low 48 bits mixed with a tag;
            // all 25 words are distinct and non-zero.
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
                    // Capacity bytes 136..200 MUST be strictly zero on every single-block call.
                    assert_eq!(
                        &raw[136..200],
                        &[0u8; 64],
                        "non-zero capacity bytes in permute_active lane {lane}"
                    );
                    // Final SHAKE256 pad bit 0x80 at byte 135.
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
                        pad_pos % 8 == 0 && (64..=128).contains(&pad_pos),
                        "unexpected FIPS 205 FORS input length {pad_pos}"
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

        pub fn thash_pair<const N: usize>(
            seed: &[u8; N],
            adrs: &Adrs,
            a: &[u8; N],
            b: &[u8; N],
        ) -> [u8; N] {
            let mut s = start(seed, adrs);
            s.absorb(a);
            s.absorb(b);
            digest(s)
        }
    }

    pub mod batch {
        use crate::address::Adrs;
        use crate::shake256::parallel::{self, States, WIDTH};

        // PRODUCTION_BATCH_HELPERS
    }

    pub mod fors_batch {
        use super::batch::{adrs_words, pair_active, seed_words, short_active};
        use super::hash::{digest, start, thash_pair};
        use crate::address::{Adrs, FORS_PRF, FORS_ROOTS, FORS_TREE};
        use crate::params::{Params, K_MAX};
        use crate::shake256::parallel::{self, States, WIDTH};
        use alloc::vec::Vec;

        // PRODUCTION_FORS_FUNCTIONS
    }

    pub fn fors_sign<const N: usize>(p: &crate::params::Params, sel: &[u32], sk: &[u8; N], seed: &[u8; N], a: crate::address::Adrs) -> Vec<u8> {
        fors_batch::sign(p, sel, sk, seed, a)
    }
    pub fn fors_recover<const N: usize>(p: &crate::params::Params, sel: &[u32], sig: &[u8], seed: &[u8; N], a: crate::address::Adrs) -> [u8; N] {
        fors_batch::recover(p, sel, sig, seed, a)
    }
    pub fn fors_subtree<const N: usize>(sk: &[u8; N], seed: &[u8; N], a: crate::address::Adrs, idx: u32, h: u32) -> [u8; N] {
        fors_batch::fors_subtree_horiz(sk, seed, a, idx, h)
    }
}

// --- Textbook FIPS 205 Algorithms 14, 15, 16, 17 over the exact same symbolic oracle ---

fn ref_shake<const N: usize>(parts: &[&[u8]]) -> [u8; N] {
    let mut msg = Vec::new();
    for p in parts {
        msg.extend_from_slice(p);
    }
    ORACLE.with(|o| o.borrow_mut().shake_bytes::<N>(&msg))
}

fn ref_fors_sk_gen<const N: usize>(sk: &[u8; N], seed: &[u8; N], adrs: Adrs, idx: u32) -> [u8; N] {
    let a = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(idx);
    ref_shake(&[seed, &a.full(), sk])
}

fn ref_fors_node<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    adrs: Adrs,
    i: u32,
    z: u32,
) -> [u8; N] {
    let tree_adrs = adrs.with_type(FORS_TREE).with_keypair(adrs.keypair);
    if z == 0 {
        let sk_val = ref_fors_sk_gen(sk, seed, adrs, i);
        let a = tree_adrs.with_word2(0).with_word3(i);
        ref_shake(&[seed, &a.full(), &sk_val])
    } else {
        let l = ref_fors_node(sk, seed, adrs, 2 * i, z - 1);
        let r = ref_fors_node(sk, seed, adrs, 2 * i + 1, z - 1);
        let a = tree_adrs.with_word2(z).with_word3(i);
        ref_shake(&[seed, &a.full(), &l, &r])
    }
}

fn ref_fors_sign<const N: usize>(
    p: &Params,
    selections: &[u32],
    sk: &[u8; N],
    seed: &[u8; N],
    adrs: Adrs,
) -> Vec<u8> {
    let mut sig = Vec::new();
    for (tree, &sel) in selections.iter().enumerate() {
        let leaf = ((tree as u32) << p.a) + sel;
        sig.extend_from_slice(&ref_fors_sk_gen(sk, seed, adrs, leaf));
        for j in 0..p.a {
            let s = (sel >> j) ^ 1;
            let node = ref_fors_node(sk, seed, adrs, ((tree as u32) << (p.a - j)) + s, j);
            sig.extend_from_slice(&node);
        }
    }
    sig
}

fn ref_fors_pk_from_sig<const N: usize>(
    p: &Params,
    selections: &[u32],
    sig: &[u8],
    seed: &[u8; N],
    adrs: Adrs,
) -> [u8; N] {
    let tree_adrs = adrs.with_type(FORS_TREE).with_keypair(adrs.keypair);
    let stride = (p.a as usize + 1) * N;
    let mut roots = Vec::new();
    for (tree, &sel) in selections.iter().enumerate() {
        let base = tree * stride;
        let sk_val = &sig[base..base + N];
        let mut ti = ((tree as u32) << p.a) + sel;
        let mut node = ref_shake::<N>(&[seed, &tree_adrs.with_word2(0).with_word3(ti).full(), sk_val]);
        for j in 0..p.a {
            let auth = &sig[base + (j as usize + 1) * N..base + (j as usize + 2) * N];
            if ((sel >> j) & 1) == 0 {
                ti /= 2;
                let a = tree_adrs.with_word2(j + 1).with_word3(ti);
                node = ref_shake::<N>(&[seed, &a.full(), &node, auth]);
            } else {
                ti = (ti - 1) / 2;
                let a = tree_adrs.with_word2(j + 1).with_word3(ti);
                node = ref_shake::<N>(&[seed, &a.full(), auth, &node]);
            }
        }
        roots.extend_from_slice(&node);
    }
    let root_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    ref_shake(&[seed, &root_adrs.full(), &roots])
}

fn test_param_set<const N: usize>(name: &str, p: &Params) {
    let sk: [u8; N] = core::array::from_fn(|i| (0x31u8).wrapping_add(i as u8 * 7));
    let seed: [u8; N] = core::array::from_fn(|i| (0x93u8).wrapping_add(i as u8 * 11));
    let adrs = Adrs {
        layer: 0,
        tree: 0x0123_4567_89ab_cdef,
        typ: FORS_TREE,
        keypair: 42,
        word2: 99,
        word3: 77,
    };

    let k = p.k as usize;
    let max_sel = (1u32 << p.a) - 1;
    let cases: Vec<(&str, Vec<u32>)> = vec![
        ("all_zero", vec![0u32; k]),
        ("all_max", vec![max_sel; k]),
        ("alternating", (0..k).map(|i| if i % 2 == 0 { 0 } else { max_sel }).collect()),
        ("mixed", (0..k).map(|i| ((i as u32 * 2654435761) >> (32 - p.a)) & max_sel).collect()),
    ];

    for (label, selections) in cases {
        let got_sig = shake::fors_sign::<N>(p, &selections, &sk, &seed, adrs);
        let exp_sig = ref_fors_sign::<N>(p, &selections, &sk, &seed, adrs);
        assert_eq!(got_sig, exp_sig, "FORS sign mismatch for {name}/{label} WIDTH={WIDTH}");

        let got_pk = shake::fors_recover::<N>(p, &selections, &got_sig, &seed, adrs);
        let exp_pk = ref_fors_pk_from_sig::<N>(p, &selections, &got_sig, &seed, adrs);
        assert_eq!(got_pk, exp_pk, "FORS recover mismatch (genuine) for {name}/{label} WIDTH={WIDTH}");

        // Also check recover on an arbitrary synthetic signature with unique per-byte patterns.
        let mut synth = vec![0u8; got_sig.len()];
        for (idx, b) in synth.iter_mut().enumerate() {
            *b = ((idx * 37 + 13) ^ (idx >> 5)) as u8;
        }
        let got_pk2 = shake::fors_recover::<N>(p, &selections, &synth, &seed, adrs);
        let exp_pk2 = ref_fors_pk_from_sig::<N>(p, &selections, &synth, &seed, adrs);
        assert_eq!(got_pk2, exp_pk2, "FORS recover mismatch (synthetic) for {name}/{label} WIDTH={WIDTH}");
    }
    println!("WIDTH={WIDTH} {name}: verified sign + recover across all selection patterns");
}

fn test_horiz_heights<const N: usize>() {
    let sk: [u8; N] = core::array::from_fn(|i| (0x55u8).wrapping_add(i as u8 * 3));
    let seed: [u8; N] = core::array::from_fn(|i| (0xA7u8).wrapping_add(i as u8 * 5));
    let adrs = Adrs {
        layer: 0,
        tree: 0x0fed_cba9_8765_4321,
        typ: FORS_TREE,
        keypair: 17,
        word2: 5,
        word3: 9,
    };
    for height in 3u32..=14 {
        let indices: &[u32] = if height <= 9 { &[0, 1, 5, 13] } else { &[0, 3] };
        for &node_idx in indices {
            let got = shake::fors_subtree::<N>(&sk, &seed, adrs, node_idx, height);
            let exp = ref_fors_node::<N>(&sk, &seed, adrs, node_idx, height);
            assert_eq!(got, exp, "fors_subtree_horiz mismatch N={N} h={height} idx={node_idx}");
        }
    }
    println!("WIDTH={WIDTH} N={N}: verified fors_subtree_horiz for heights 3..=14");
}

fn main() {
    let p_128s = Params { n: 16, h: 63, d: 7, hp: 9, a: 12, k: 14, m: 30 };
    let p_128f = Params { n: 16, h: 66, d: 22, hp: 3, a: 6, k: 33, m: 34 };
    let p_192s = Params { n: 24, h: 63, d: 7, hp: 9, a: 14, k: 17, m: 39 };
    let p_192f = Params { n: 24, h: 66, d: 22, hp: 3, a: 8, k: 33, m: 42 };
    let p_256s = Params { n: 32, h: 64, d: 8, hp: 8, a: 14, k: 22, m: 47 };
    let p_256f = Params { n: 32, h: 68, d: 17, hp: 4, a: 9, k: 35, m: 49 };

    if WIDTH == 8 {
        test_horiz_heights::<16>();
        test_horiz_heights::<24>();
        test_horiz_heights::<32>();
    }

    test_param_set::<16>("shake_128s", &p_128s);
    test_param_set::<16>("shake_128f", &p_128f);
    test_param_set::<24>("shake_192s", &p_192s);
    test_param_set::<24>("shake_192f", &p_192f);
    test_param_set::<32>("shake_256s", &p_256s);
    test_param_set::<32>("shake_256f", &p_256f);

    ORACLE.with(|o| {
        let o = o.borrow();
        println!(
            "WIDTH={WIDTH}: checked {} permute_active calls ({} active lanes) and {} sponge calls",
            o.perm_calls, o.perm_lanes, o.sponge_calls
        );
    });
}
"""


def run_symbolic_replay(width: int) -> None:
    batch_src = (SRC / "shake/batch.rs").read_text()
    fors_src = (SRC / "shake/fors_batch.rs").read_text()
    batch_helpers = "\n\n".join(function(batch_src, name) for name in BATCH_HELPERS)
    fors_funs = "\n\n".join(function(fors_src, name) for name in FORS_FUNCTIONS)

    code = HARNESS_TEMPLATE
    code = code.replace("ADDRESS_PATH", str(SRC / "address.rs"))
    code = code.replace("PARAMS_PATH", str(SRC / "params.rs"))
    code = code.replace("PROOF_WIDTH", str(width))
    code = code.replace("// PRODUCTION_BATCH_HELPERS", batch_helpers)
    code = code.replace("// PRODUCTION_FORS_FUNCTIONS", fors_funs)

    with tempfile.TemporaryDirectory(prefix=f"shake-fors-w{width}-") as tmp:
        src = Path(tmp) / "probe.rs"
        exe = Path(tmp) / "probe"
        src.write_text(code)
        subprocess.run(["rustc", "--edition=2021", "-O", src, "-o", exe], check=True)
        subprocess.run([exe], check=True)


def main() -> None:
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )
    for gate in (
        "check-shake-fors-plan.py",
        "check-shake-fors-scatter.py",
        "check-shake-active-hashes.py",
        "check-shake-fors-fused.py",
        "check-shake-fors-tree.py",
    ):
        subprocess.run([sys.executable, HERE / gate], check=True)
    for width in (8, 3):
        run_symbolic_replay(width)
    facade["run"](["lake", "build", "Shakeopt.ForsHoriz"], facade["LEAN"])
    facade["audit_theorems"]("Shakeopt.ForsHoriz", THEOREMS)
    print(
        f"Shakeopt.ForsHoriz: audited {len(THEOREMS)} theorems strictly within [propext, Classical.choice, Quot.sound]",
        flush=True,
    )


if __name__ == "__main__":
    main()
