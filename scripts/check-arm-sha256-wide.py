#!/usr/bin/env python3
"""Verify ARM64 SHA-256 arm_wide.rs kernel, pure-Rust stack encoders, and safe callers.

Checks:
1. Fresh Charon + Aeneas extraction of `Armwide` (`wots_digits_stack`, `base_2b_stack`,
   `prepare_tlen`, `sort_descending`, `parent_block_512`) on `aarch64-apple-darwin` and
   `aarch64-unknown-linux-gnu` matches `lean-hw/Armwide/{Types,Funs}.lean` after namespacing the extraction
   with zero external axioms.
2. `rust/src/sha256.rs` `const K: [u32; 64]` matches `Spec.SHA256.K` in Lean.
3. Symbolic AST verification of lifted production `make_head` (rounds 0..3),
   `finish_from_r4` (rounds 4..63 deferred schedule), and `compress_block_lanes` (rounds 0..63)
   against the Lean `Armwide.Kernel` model for all `L in {1,2,3,4}` and `NEED_EFGH in {false,true}`.
4. Lifted production caller replay of `wots_endpoints_{1,2,4}`, `wots_sign_fused`,
   `wots_recover`, `compress_multi_{1,2,4}`, `parents_16`, `fors_leaves`,
   `fors_verify_leaves`, `fors_path_level_16`, `xmss::arm::batch_root`,
   `wots::arm::{pk_gen, sign, recover}`, and `fors::arm::{subtree, pk_from_sig}`,
   recording and verifying EVERY compressed hash block (address bytes, payload, padding,
   bit-length) and output position against FIPS 205 for all 6 SHA-2 parameter sets.
5. Builds and axiom-audits `Armwide.Encoders`, `Armwide.WotsRefill`, and `Armwide.Kernel`.
"""

import os
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
common = facade["common"]
ROOT, LEAN = facade["ROOT"], facade["LEAN"]

ARMWIDE_ROOTS = (
    "crate::wots::arm::wots_digits_stack",
    "crate::fors::arm::base_2b_stack",
    "crate::xmss::arm::prepare_tlen",
    "crate::sha256::arm_wide::sort_descending",
    "crate::sha512::paired::parent_block_512",
)


def check_extraction(scratch: Path) -> None:
    """Re-extract Armwide on both Apple and Linux AArch64 and assert exact match."""
    for target in facade["TARGETS"][:2]:
        folder = scratch / f"extract_{target}"
        folder.mkdir()
        dest = facade["extract"]("rust", target, "Armwide", folder, ARMWIDE_ROOTS, ())
        if (dest / "FunsExternal_Template.lean").exists():
            raise ValueError(f"unexpected external axioms in Armwide extraction on {target}")
        for fname in ("Types.lean", "Funs.lean"):
            got = (dest / fname).read_bytes()
            # The standalone extraction otherwise collides with the core slhdsa package
            # when its signing scheduler and the SHA-256 kernel are imported together.
            got = got.replace(b"namespace slhdsa\n", b"namespace ArmwideRust\n").replace(
                b"end slhdsa\n", b"end ArmwideRust\n")
            ref = (LEAN / "Armwide" / fname).read_bytes()
            if got != ref:
                raise ValueError(f"Armwide/{fname} differs from fresh extraction on {target}")
        print(f"{target}: Armwide namespace-adjusted extraction matched byte-for-byte (0 external axioms)", flush=True)


def check_sha256_k() -> None:
    """Verify `rust/src/sha256.rs` `const K: [u32; 64]` matches `Spec.SHA256.K` in Lean."""
    src = (ROOT / "rust/src/sha256.rs").read_text()
    m = re.search(r"const K: \[u32; 64\] = \[([^\]]+)\];", src)
    if not m:
        raise ValueError("could not find SHA-256 K in rust/src/sha256.rs")
    words = [
        re.fullmatch(r"0x[0-9a-f]+", k.strip())[0]
        for k in m.group(1).strip().rstrip(",").split(",")
    ]
    if len(words) != 64:
        raise ValueError(f"expected 64 SHA-256 K constants, got {len(words)}")
    common["run"](
        ["lake", "env", "lean", "--stdin"],
        LEAN,
        input=f"import Spec.Sha256\nexample : Spec.SHA256.K = [{','.join(words)}] := by decide\n",
        text=True,
    )
    print("SHA-256 K constants match Spec.SHA256.K: OK", flush=True)


def extract_kernel_block(src: str) -> str:
    """Extract `struct Head` and the `kernel! { ... }` block from `arm_wide.rs`."""
    start = src.index("#[derive(Clone, Copy)]\nstruct Head {")
    end = src.index("\n}\n\n/// Out-of-line 4-lane", start) + 3
    block = src[start:end]
    # Unwrap `kernel! { ... }` macro so the functions compile directly in our symbolic harness.
    block = block.replace("kernel! {", "", 1)
    # Remove the matching closing `}` of `kernel! {` at the end
    idx = block.rfind("}")
    block = block[:idx] + block[idx + 1 :]
    block = block.replace("super::K", "SHA256_K")
    return block


def check_symbolic_kernel_ast(scratch: Path) -> None:
    """Symbolically execute lifted production `make_head`, `step_lanes`, `finish_from_r4`,
    and `compress_block_lanes` as exact Arm.lean ASTs and verify exact identity with
    the Lean `Armwide.Kernel` definitions for all `L in {1,2,3,4}` and `NEED_EFGH in {false,true}`."""
    wide_src = (ROOT / "rust/src/sha256/arm_wide.rs").read_text()
    kblock = extract_kernel_block(wide_src)
    # Remove load_n/store_n/make_hdr/pack_short from the AST-only check (checked separately
    # in `arm-pack.py` and in our full caller replay below); keep `Head`, `make_head`,
    # `step_lanes`, `finish_from_r4`, `compress_block_lanes`, `load_heads`, `load_shared_head`.
    m_head = re.search(r"#\[derive\(Clone, Copy\)\]\s*struct Head \{[^}]+\}", kblock)
    if not m_head:
        raise ValueError("could not extract Head struct")

    def get_fn(name: str) -> str:
        s = kblock.index(f"unsafe fn {name}")
        # Find closing brace at 4-space indent
        e = kblock.index("\n    }", s) + 6
        return kblock[s:e]

    make_head_fn = get_fn("make_head")
    step_lanes_fn = get_fn("step_lanes")
    finish_fn = get_fn("finish_from_r4")
    compress_fn = get_fn("compress_block_lanes")
    load_heads_fn = get_fn("load_heads")
    load_shared_fn = get_fn("load_shared_head")

    # Verify every production instantiation of `finish_from_r4` and `compress_block_lanes`
    if re.search(r"finish_from_r4::<(?!L,|1,|2,|3,|4,)", wide_src):
        raise ValueError("unexpected finish_from_r4 instantiation in arm_wide.rs")
    if re.search(r"compress_block_lanes::<(?!L,|K_LANES,|1,|2,|4,)", wide_src):
        raise ValueError("unexpected compress_block_lanes instantiation in arm_wide.rs")

    # In the AST harness, a `V` is a symbolic expression ID stored in a global arena,
    # and `[u32; 4]` in `Head` / `&[u32; 8]` state / `k_ptr: *const u32` store tagged handles
    # so `vld1q_u32` / `vst1q_u32` / `arm::load_words` / `arm::load_be` preserve exact AST IDs!
    harness = f"""
#![allow(unused_unsafe, dead_code, unused_variables)]
use std::cell::RefCell;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Expr {{
    Zero,
    State(usize),          // 0 = abcd0, 4 = efgh0
    Block(usize, usize),   // (lane_tag, word_group 0..4)
    ConstK(usize),         // offset 4*I
    Add(usize, usize),
    Sha256H(usize, usize, usize),
    Sha256H2(usize, usize, usize),
    Sha256Su0(usize, usize),
    Sha256Su1(usize, usize, usize),
}}

thread_local! {{
    static ARENA: RefCell<Vec<Expr>> = RefCell::new(Vec::new());
}}

fn intern(e: Expr) -> V {{
    ARENA.with(|a| {{
        let mut v = a.borrow_mut();
        if let Some(pos) = v.iter().position(|x| *x == e) {{
            V(pos as u32)
        }} else {{
            let id = v.len();
            v.push(e);
            V(id as u32)
        }}
    }})
}}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct V(u32);

#[derive(Clone, Copy)]
struct Adrs(usize); // lane tag
impl Adrs {{
    fn compress(&self) -> [u8; 22] {{
        let mut b = [0u8; 22];
        b[0] = self.0 as u8;
        b
    }}
}}

// K table encodes offset tag at each index so `k_ptr.add(4 * I)` yields `ConstK(4 * I)`.
const SHA256_K: [u32; 64] = [
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
    16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,
    32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,
    48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,
];

mod arm {{
    use super::*;
    pub fn load_words(s: &[u32], off: usize) -> V {{
        if s.len() == 64 {{
            intern(Expr::ConstK(off))
        }} else {{
            assert!(off == 0 || off == 4);
            intern(Expr::State(off))
        }}
    }}
    pub fn load_be(b: &[u8], off: usize) -> V {{
        assert_eq!(off, 0);
        intern(Expr::Block(b[0] as usize, 0))
    }}
}}

unsafe fn vdupq_n_u32(x: u32) -> V {{ assert_eq!(x, 0); intern(Expr::Zero) }}
unsafe fn vld1q_u32(ptr: *const u32) -> V {{
    let tag = *ptr;
    let is_k = *ptr.add(1) == tag.wrapping_add(1) && *ptr.add(2) == tag.wrapping_add(2) && *ptr.add(3) == tag.wrapping_add(3);
    if is_k && tag < 64 && tag % 4 == 0 {{
        intern(Expr::ConstK(tag as usize))
    }} else {{
        V(tag)
    }}
}}
unsafe fn vst1q_u32(ptr: *mut u32, v: V) {{
    *ptr = v.0;
    *ptr.add(1) = 0xdead_beef;
    *ptr.add(2) = 0xcafe_babe;
    *ptr.add(3) = 0x1234_5678;
}}
unsafe fn vaddq_u32(a: V, b: V) -> V {{ intern(Expr::Add(a.0 as usize, b.0 as usize)) }}
unsafe fn vsha256hq_u32(d: V, n: V, m: V) -> V {{ intern(Expr::Sha256H(d.0 as usize, n.0 as usize, m.0 as usize)) }}
unsafe fn vsha256h2q_u32(d: V, n: V, m: V) -> V {{ intern(Expr::Sha256H2(d.0 as usize, n.0 as usize, m.0 as usize)) }}
unsafe fn vsha256su0q_u32(d: V, n: V) -> V {{ intern(Expr::Sha256Su0(d.0 as usize, n.0 as usize)) }}
unsafe fn vsha256su1q_u32(d: V, n: V, m: V) -> V {{ intern(Expr::Sha256Su1(d.0 as usize, n.0 as usize, m.0 as usize)) }}

{m_head.group(0)}
{make_head_fn}
{step_lanes_fn}
{finish_fn}
{compress_fn}
{load_heads_fn}
{load_shared_fn}

// Exact Lean `Armwide.Kernel` reference AST builder
fn lean_step_lane(need_efgh: bool, abcd: V, efgh: V, m: &mut [V; 4], i: usize) -> (V, V) {{
    let w = intern(Expr::Add(m[i % 4].0 as usize, intern(Expr::ConstK(4 * i)).0 as usize));
    let a_next = intern(Expr::Sha256H(abcd.0 as usize, efgh.0 as usize, w.0 as usize));
    let e_next = if i < 15 || need_efgh {{
        intern(Expr::Sha256H2(efgh.0 as usize, abcd.0 as usize, w.0 as usize))
    }} else {{
        efgh
    }};
    if i < 12 {{
        let s0 = intern(Expr::Sha256Su0(m[i % 4].0 as usize, m[(i + 1) % 4].0 as usize));
        m[i % 4] = intern(Expr::Sha256Su1(s0.0 as usize, m[(i + 2) % 4].0 as usize, m[(i + 3) % 4].0 as usize));
    }}
    (a_next, e_next)
}}

fn lean_finish_from_r4(need_efgh: bool, lane: usize) -> (V, V) {{
    let abcd0 = intern(Expr::State(0));
    let efgh0 = intern(Expr::State(4));
    let m0 = intern(Expr::Block(lane, 0));
    let m1 = intern(Expr::Block(lane, 1));
    let m2 = intern(Expr::Block(lane, 2));
    let m3 = intern(Expr::Block(lane, 3));
    // makeHead (step 0)
    let w0 = intern(Expr::Add(m0.0 as usize, intern(Expr::ConstK(0)).0 as usize));
    let a1 = intern(Expr::Sha256H(abcd0.0 as usize, efgh0.0 as usize, w0.0 as usize));
    let e1 = intern(Expr::Sha256H2(efgh0.0 as usize, abcd0.0 as usize, w0.0 as usize));
    // deferred step 1
    let w1 = intern(Expr::Add(m1.0 as usize, intern(Expr::ConstK(4)).0 as usize));
    let mut abcd = intern(Expr::Sha256H(a1.0 as usize, e1.0 as usize, w1.0 as usize));
    let mut efgh = intern(Expr::Sha256H2(e1.0 as usize, a1.0 as usize, w1.0 as usize));
    let s0_16 = intern(Expr::Sha256Su0(m0.0 as usize, m1.0 as usize));
    let w16 = intern(Expr::Sha256Su1(s0_16.0 as usize, m2.0 as usize, m3.0 as usize));
    let s0_20 = intern(Expr::Sha256Su0(m1.0 as usize, m2.0 as usize));
    let w20 = intern(Expr::Sha256Su1(s0_20.0 as usize, m3.0 as usize, w16.0 as usize));
    let mut m = [w16, w20, m2, m3];
    for i in 2..16 {{
        let (a, e) = lean_step_lane(need_efgh, abcd, efgh, &mut m, i);
        abcd = a;
        efgh = e;
    }}
    let abcd_out = intern(Expr::Add(abcd.0 as usize, abcd0.0 as usize));
    let efgh_out = if need_efgh {{ intern(Expr::Add(efgh.0 as usize, efgh0.0 as usize)) }} else {{ efgh }};
    (abcd_out, efgh_out)
}}

fn lean_compress_block(need_efgh: bool, lane: usize) -> (V, V) {{
    let mut abcd = intern(Expr::State(0));
    let mut efgh = intern(Expr::State(4));
    let mut m = [
        intern(Expr::Block(lane, 0)),
        intern(Expr::Block(lane, 1)),
        intern(Expr::Block(lane, 2)),
        intern(Expr::Block(lane, 3)),
    ];
    for i in 0..16 {{
        let (a, e) = lean_step_lane(need_efgh, abcd, efgh, &mut m, i);
        abcd = a;
        efgh = e;
    }}
    (abcd, efgh)
}}

fn check_finish<const L: usize, const NEED_EFGH: bool>() {{
    let st = [0u32; 8];
    let heads: [Head; L] = core::array::from_fn(|l| unsafe {{ make_head(&st, Adrs(l)) }});
    let (m0, a1, e1) = unsafe {{ load_heads::<L>(&heads) }};
    let m1: [V; L] = core::array::from_fn(|l| intern(Expr::Block(l, 1)));
    let m2: [V; L] = core::array::from_fn(|l| intern(Expr::Block(l, 2)));
    let m3: [V; L] = core::array::from_fn(|l| intern(Expr::Block(l, 3)));
    let (out_a, out_e) = unsafe {{ finish_from_r4::<L, NEED_EFGH>(&st, a1, e1, m0, m1, m2, m3, SHA256_K.as_ptr()) }};
    for l in 0..L {{
        let (exp_a, exp_e) = lean_finish_from_r4(NEED_EFGH, l);
        assert_eq!(out_a[l], exp_a, "finish_from_r4<{{L}},{{NEED_EFGH}}> abcd AST mismatch on lane {{l}}");
        if NEED_EFGH {{
            assert_eq!(out_e[l], exp_e, "finish_from_r4<{{L}},{{NEED_EFGH}}> efgh AST mismatch on lane {{l}}");
        }}
    }}
}}

fn check_compress<const L: usize, const NEED_EFGH: bool>() {{
    let mut abcd: [V; L] = core::array::from_fn(|_| intern(Expr::State(0)));
    let mut efgh: [V; L] = core::array::from_fn(|_| intern(Expr::State(4)));
    let mut m: [[V; 4]; L] = core::array::from_fn(|l| [
        intern(Expr::Block(l, 0)),
        intern(Expr::Block(l, 1)),
        intern(Expr::Block(l, 2)),
        intern(Expr::Block(l, 3)),
    ]);
    unsafe {{ compress_block_lanes::<L, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, SHA256_K.as_ptr()) }};
    for l in 0..L {{
        let (exp_a, exp_e) = lean_compress_block(NEED_EFGH, l);
        assert_eq!(abcd[l], exp_a, "compress_block_lanes<{{L}},{{NEED_EFGH}}> abcd AST mismatch on lane {{l}}");
        if NEED_EFGH {{
            assert_eq!(efgh[l], exp_e, "compress_block_lanes<{{L}},{{NEED_EFGH}}> efgh AST mismatch on lane {{l}}");
        }}
    }}
}}

fn main() {{
    check_finish::<1, false>(); check_finish::<1, true>();
    check_finish::<2, false>(); check_finish::<2, true>();
    check_finish::<3, false>(); check_finish::<3, true>();
    check_finish::<4, false>(); check_finish::<4, true>();
    check_compress::<1, false>(); check_compress::<1, true>();
    check_compress::<2, false>(); check_compress::<2, true>();
    check_compress::<4, false>(); check_compress::<4, true>();
    // Also check load_shared_head replicates (m0, a1, e1) identically across L lanes
    let st = [0u32; 8];
    let sh = unsafe {{ make_head(&st, Adrs(42)) }};
    let (sm0, sa1, se1) = unsafe {{ load_shared_head::<4>(&sh) }};
    let (hm0, ha1, he1) = unsafe {{ load_heads::<4>(&[sh, sh, sh, sh]) }};
    assert_eq!(sm0, hm0); assert_eq!(sa1, ha1); assert_eq!(se1, he1);
    println!("Symbolic AST check of make_head + finish_from_r4 + compress_block_lanes (L=1..4, NEED_EFGH=false/true): OK");
}}
"""
    rs = scratch / "sym_kernel256.rs"
    bin_path = scratch / "sym_kernel256"
    rs.write_text(harness)
    subprocess.run(["rustc", "--edition=2021", "-O", rs, "-o", bin_path], check=True)
    subprocess.run([bin_path], check=True)


def strip_for_replay(path: Path, extra_replacements: list[tuple[str, str]]) -> str:
    src = path.read_text()
    if "#[cfg(test)]" in src:
        src = src[: src.index("#[cfg(test)]")]
    lines = []
    for line in src.splitlines():
        s = line.strip()
        if s.startswith("//!") or s.startswith("use core::arch::aarch64::*;"):
            continue
        if s.startswith("#[target_feature(") or s.startswith("#[cfg_attr(target_feature") or s.startswith("#[cfg_attr(not(target_feature"):
            continue
        lines.append(line)
    out = "\n".join(lines)
    for old, new in extra_replacements:
        out = out.replace(old, new)
    return out


def check_full_caller_replay(scratch: Path) -> None:
    """Lift ACTUAL production `arm_wide.rs`, `paired.rs`, `xmss/arm.rs`, `wots/arm.rs`,
    and `fors/arm.rs` and replay every single function against FIPS 205 for all 6 SHA-2
    parameter sets, recording and auditing EVERY compressed SHA-256 and SHA-512 block."""
    addr_src = (ROOT / "rust/src/address.rs").read_text()
    params_src = (ROOT / "rust/src/params.rs").read_text()

    sha256_src = (ROOT / "rust/src/sha256.rs").read_text()
    k256 = re.search(r"const K: \[u32; 64\] = \[[^\]]+\];", sha256_src).group(0)
    h0_256 = re.search(r"const H0: \[u32; 8\] = \[[^\]]+\];", sha256_src).group(0)

    sha512_src = (ROOT / "rust/src/sha512.rs").read_text()
    k512 = re.search(r"const K: \[u64; 80\] = \[[^\]]+\];", sha512_src).group(0)
    h0_512 = re.search(r"const H0: \[u64; 8\] = \[[^\]]+\];", sha512_src).group(0)

    arm_wide_src = strip_for_replay(
        ROOT / "rust/src/sha256/arm_wide.rs",
        [
            ("use super::hw::arm::{self, V};", "use crate::sha256::hw::arm::{self, V};"),
            ("super::K", "crate::sha256::K"),
            ("pub(crate) fn", "pub fn"),
        ],
    )
    # Remove target_feature inside macro_rules! kernel!
    arm_wide_src = re.sub(
        r"macro_rules! kernel \{.*?\n\}",
        "macro_rules! kernel {\n    ($($item:item)*) => { $($item)* };\n}",
        arm_wide_src,
        count=1,
        flags=re.S,
    )
    # Instrument `finish_from_r4` and `compress_block_lanes` to log every compressed 64-byte block
    # right at entry, before executing the unmodified production body.
    if "let mut abcd = a1;" not in arm_wide_src:
        raise ValueError("unexpected finish_from_r4 body in arm_wide.rs")
    arm_wide_src = arm_wide_src.replace(
        "let mut abcd = a1;",
        "for lane in 0..L { record_block_words(state, m0[lane], m1[lane], m2[lane], m3[lane]); }\n        let mut abcd = a1;",
        1,
    )
    if "step_lanes::<L, 0, NEED_EFGH>(abcd, efgh, m, k_ptr);" not in arm_wide_src:
        raise ValueError("unexpected compress_block_lanes body in arm_wide.rs")
    arm_wide_src = arm_wide_src.replace(
        "step_lanes::<L, 0, NEED_EFGH>(abcd, efgh, m, k_ptr);",
        "for lane in 0..L { let st = [abcd[lane].0[0], abcd[lane].0[1], abcd[lane].0[2], abcd[lane].0[3], efgh[lane].0[0], efgh[lane].0[1], efgh[lane].0[2], efgh[lane].0[3]]; record_block_words(&st, m[lane][0], m[lane][1], m[lane][2], m[lane][3]); }\n        step_lanes::<L, 0, NEED_EFGH>(abcd, efgh, m, k_ptr);",
        1,
    )

    paired_src = strip_for_replay(
        ROOT / "rust/src/sha512/paired.rs",
        [
            ("use super::hw::arm;", "use crate::sha512::hw::arm;"),
            ("super::K", "crate::sha512::K"),
            ("pub(super) fn", "pub fn"),
            ("pub(crate) fn", "pub fn"),
        ],
    )
    # Instrument `rounds_lanes` and `compress_multi_1_active` to log every compressed 128-byte block.
    if "group!(0);" not in paired_src:
        raise ValueError("unexpected rounds_lanes / compress_multi_1_active body in paired.rs")
    paired_src = paired_src.replace(
        "macro_rules! step {\n        ($i:expr) => {{",
        "for lane in 0..K_LANES { record_block512_words(&lanes[lane].state, &lanes[lane].schedule); }\n    macro_rules! step {\n        ($i:expr) => {{",
        1,
    )
    paired_src = paired_src.replace(
        "let mut w = load_block(msg, off);",
        "let mut w = load_block(msg, off);\n        record_block512_words(&v, &w);",
        1,
    )

    xmss_arm_src = strip_for_replay(
        ROOT / "rust/src/xmss/arm.rs",
        [
            ("use super::*;", "use crate::xmss_ctx::*;"),
            ("pub(super) fn", "pub fn"),
        ],
    )
    wots_arm_src = strip_for_replay(
        ROOT / "rust/src/wots/arm.rs",
        [
            ("use super::*;", "use crate::wots_ctx::*;"),
            ("alloc::vec!", "std::vec!"),
            ("pub(super) fn", "pub fn"),
        ],
    )
    fors_arm_src = strip_for_replay(
        ROOT / "rust/src/fors/arm.rs",
        [
            ("use super::*;", "use crate::fors_ctx::*;"),
            ("pub(super) fn", "pub fn"),
        ],
    )

    # Assemble a self-contained single-file Rust crate implementing exact Armv8 NEON/SHA2
    # instructions AND recording every single SHA-256 and SHA-512 compression call!
    harness = f"""
#![allow(unused_unsafe, dead_code, unused_variables, unused_imports, non_camel_case_types)]
extern crate alloc;
use std::cell::RefCell;

// Recording log of every SHA-256 and SHA-512 compression executed by the lifted production code.
thread_local! {{
    static LOG256: RefCell<Vec<([u32; 8], [u8; 64])>> = RefCell::new(Vec::new());
    static LOG512: RefCell<Vec<([u64; 8], [u8; 128])>> = RefCell::new(Vec::new());
}}

fn clear_logs() {{
    LOG256.with(|l| l.borrow_mut().clear());
    LOG512.with(|l| l.borrow_mut().clear());
}}

fn take_logs() -> (Vec<([u32; 8], [u8; 64])>, Vec<([u64; 8], [u8; 128])>) {{
    let a = LOG256.with(|l| core::mem::take(&mut *l.borrow_mut()));
    let b = LOG512.with(|l| core::mem::take(&mut *l.borrow_mut()));
    (a, b)
}}

// Exact Armv8 NEON vector types
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint32x4_t(pub [u32; 4]);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint16x8_t(pub [u16; 8]);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint8x16_t(pub [u8; 16]);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint8x8_t(pub [u8; 8]);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint64x2_t(pub [u64; 2]);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint64x1_t(pub u64);

pub mod neon_ops {{
    use super::*;

    pub fn vdupq_n_u32(x: u32) -> uint32x4_t {{ uint32x4_t([x; 4]) }}
    pub fn vdup_n_u8(x: u8) -> uint8x8_t {{ uint8x8_t([x; 8]) }}
    pub fn vdup_n_u64(x: u64) -> uint64x1_t {{ uint64x1_t(x) }}
    pub fn vdupq_n_u64(x: u64) -> uint64x2_t {{ uint64x2_t([x; 2]) }}

    pub fn vcombine_u8(lo: uint8x8_t, hi: uint8x8_t) -> uint8x16_t {{
        let mut out = [0u8; 16];
        out[0..8].copy_from_slice(&lo.0);
        out[8..16].copy_from_slice(&hi.0);
        uint8x16_t(out)
    }}

    pub fn vcombine_u64(lo: uint64x1_t, hi: uint64x1_t) -> uint64x2_t {{
        uint64x2_t([lo.0, hi.0])
    }}

    pub fn vget_low_u8(v: uint8x16_t) -> uint8x8_t {{
        let mut out = [0u8; 8];
        out.copy_from_slice(&v.0[0..8]);
        uint8x8_t(out)
    }}

    pub fn vld1_u8(ptr: *const u8) -> uint8x8_t {{
        let mut out = [0u8; 8];
        unsafe {{ core::ptr::copy_nonoverlapping(ptr, out.as_mut_ptr(), 8); }}
        uint8x8_t(out)
    }}

    pub fn vst1_u8(ptr: *mut u8, v: uint8x8_t) {{
        unsafe {{ core::ptr::copy_nonoverlapping(v.0.as_ptr(), ptr, 8); }}
    }}

    pub fn vst1q_u8(ptr: *mut u8, v: uint8x16_t) {{
        unsafe {{ core::ptr::copy_nonoverlapping(v.0.as_ptr(), ptr, 16); }}
    }}

    pub fn vld1q_u32(ptr: *const u32) -> uint32x4_t {{
        unsafe {{ uint32x4_t([*ptr, *ptr.add(1), *ptr.add(2), *ptr.add(3)]) }}
    }}

    pub fn vst1q_u32(ptr: *mut u32, v: uint32x4_t) {{
        unsafe {{ for i in 0..4 {{ *ptr.add(i) = v.0[i]; }} }}
    }}

    pub fn vld1q_u64(ptr: *const u64) -> uint64x2_t {{
        unsafe {{ uint64x2_t([*ptr, *ptr.add(1)]) }}
    }}

    pub fn vst1q_u64(ptr: *mut u64, v: uint64x2_t) {{
        unsafe {{
            *ptr = v.0[0];
            *ptr.add(1) = v.0[1];
        }}
    }}

    pub fn vreinterpretq_u8_u32(v: uint32x4_t) -> uint8x16_t {{
        let mut out = [0u8; 16];
        for i in 0..4 {{ out[4 * i..4 * i + 4].copy_from_slice(&v.0[i].to_le_bytes()); }}
        uint8x16_t(out)
    }}

    pub fn vreinterpretq_u32_u8(v: uint8x16_t) -> uint32x4_t {{
        let mut out = [0u32; 4];
        for i in 0..4 {{ out[i] = u32::from_le_bytes(v.0[4 * i..4 * i + 4].try_into().unwrap()); }}
        uint32x4_t(out)
    }}

    pub fn vreinterpretq_u16_u32(v: uint32x4_t) -> uint16x8_t {{
        let b = vreinterpretq_u8_u32(v).0;
        let mut out = [0u16; 8];
        for i in 0..8 {{ out[i] = u16::from_le_bytes([b[2 * i], b[2 * i + 1]]); }}
        uint16x8_t(out)
    }}

    pub fn vreinterpretq_u32_u16(v: uint16x8_t) -> uint32x4_t {{
        let mut b = [0u8; 16];
        for i in 0..8 {{ b[2 * i..2 * i + 2].copy_from_slice(&v.0[i].to_le_bytes()); }}
        vreinterpretq_u32_u8(uint8x16_t(b))
    }}

    pub fn vreinterpretq_u16_u64(v: uint64x2_t) -> uint16x8_t {{
        let mut b = [0u8; 16];
        b[0..8].copy_from_slice(&v.0[0].to_le_bytes());
        b[8..16].copy_from_slice(&v.0[1].to_le_bytes());
        let mut out = [0u16; 8];
        for i in 0..8 {{ out[i] = u16::from_le_bytes([b[2 * i], b[2 * i + 1]]); }}
        uint16x8_t(out)
    }}

    pub fn vreinterpretq_u8_u64(v: uint64x2_t) -> uint8x16_t {{
        let mut out = [0u8; 16];
        out[0..8].copy_from_slice(&v.0[0].to_le_bytes());
        out[8..16].copy_from_slice(&v.0[1].to_le_bytes());
        uint8x16_t(out)
    }}

    pub fn vrev32q_u8(v: uint8x16_t) -> uint8x16_t {{
        let mut out = [0u8; 16];
        for g in 0..4 {{
            for i in 0..4 {{ out[4 * g + i] = v.0[4 * g + 3 - i]; }}
        }}
        uint8x16_t(out)
    }}

    pub fn vrev32q_u16(v: uint16x8_t) -> uint16x8_t {{
        let mut out = [0u16; 8];
        for g in 0..4 {{
            out[2 * g] = v.0[2 * g + 1];
            out[2 * g + 1] = v.0[2 * g];
        }}
        uint16x8_t(out)
    }}

    pub fn vrev64q_u8(v: uint8x16_t) -> uint8x16_t {{
        let mut out = [0u8; 16];
        for i in 0..8 {{ out[i] = v.0[7 - i]; out[8 + i] = v.0[15 - i]; }}
        uint8x16_t(out)
    }}

    pub fn vextq_u16<const N: i32>(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {{
        let mut cat = [0u16; 16];
        cat[0..8].copy_from_slice(&a.0);
        cat[8..16].copy_from_slice(&b.0);
        let n = N as usize;
        let mut out = [0u16; 8];
        out.copy_from_slice(&cat[n..n + 8]);
        uint16x8_t(out)
    }}

    pub fn vsetq_lane_u32<const LANE: i32>(val: u32, mut v: uint32x4_t) -> uint32x4_t {{
        v.0[LANE as usize] = val;
        v
    }}

    pub fn vsetq_lane_u16<const LANE: i32>(val: u16, mut v: uint16x8_t) -> uint16x8_t {{
        v.0[LANE as usize] = val;
        v
    }}

    pub fn vaddq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {{
        uint32x4_t([
            a.0[0].wrapping_add(b.0[0]),
            a.0[1].wrapping_add(b.0[1]),
            a.0[2].wrapping_add(b.0[2]),
            a.0[3].wrapping_add(b.0[3]),
        ])
    }}

    // Exact Arm.lean SHA256H / SHA256H2 / SHA256SU0 / SHA256SU1
    fn sha256_hash(mut x: [u32; 4], mut y: [u32; 4], w: [u32; 4], part1: bool) -> uint32x4_t {{
        for e in 0..4 {{
            let ch = ((y[1] ^ y[2]) & y[0]) ^ y[2];
            let maj = (x[0] & x[1]) | ((x[0] | x[1]) & x[2]);
            let s1 = y[0].rotate_right(6) ^ y[0].rotate_right(11) ^ y[0].rotate_right(25);
            let s0 = x[0].rotate_right(2) ^ x[0].rotate_right(13) ^ x[0].rotate_right(22);
            let t = y[3].wrapping_add(s1).wrapping_add(ch).wrapping_add(w[e]);
            let x3 = t.wrapping_add(x[3]);
            let y3 = t.wrapping_add(s0).wrapping_add(maj);
            x = [y3, x[0], x[1], x[2]];
            y = [x3, y[0], y[1], y[2]];
        }}
        uint32x4_t(if part1 {{ x }} else {{ y }})
    }}

    pub fn vsha256hq_u32(d: uint32x4_t, n: uint32x4_t, m: uint32x4_t) -> uint32x4_t {{
        sha256_hash(d.0, n.0, m.0, true)
    }}

    pub fn vsha256h2q_u32(d: uint32x4_t, n: uint32x4_t, m: uint32x4_t) -> uint32x4_t {{
        sha256_hash(n.0, d.0, m.0, false)
    }}

    pub fn vsha256su0q_u32(d: uint32x4_t, n: uint32x4_t) -> uint32x4_t {{
        let f = |elt: u32| elt.rotate_right(7) ^ elt.rotate_right(18) ^ (elt >> 3);
        uint32x4_t([
            f(d.0[1]).wrapping_add(d.0[0]),
            f(d.0[2]).wrapping_add(d.0[1]),
            f(d.0[3]).wrapping_add(d.0[2]),
            f(n.0[0]).wrapping_add(d.0[3]),
        ])
    }}

    pub fn vsha256su1q_u32(d: uint32x4_t, n: uint32x4_t, m: uint32x4_t) -> uint32x4_t {{
        let g = |elt: u32| elt.rotate_right(17) ^ elt.rotate_right(19) ^ (elt >> 10);
        let r0 = g(m.0[2]).wrapping_add(d.0[0]).wrapping_add(n.0[1]);
        let r1 = g(m.0[3]).wrapping_add(d.0[1]).wrapping_add(n.0[2]);
        let r2 = g(r0).wrapping_add(d.0[2]).wrapping_add(n.0[3]);
        let r3 = g(r1).wrapping_add(d.0[3]).wrapping_add(m.0[0]);
        uint32x4_t([r0, r1, r2, r3])
    }}
}}

pub mod address {{
{addr_src}
}}

pub mod params {{
{params_src}
}}

pub mod sha256 {{
    use super::*;
    pub {k256}
    pub {h0_256}

    pub mod hw {{
        pub mod arm {{
            use crate::uint32x4_t;
            pub type V = uint32x4_t;
            pub fn available() -> bool {{ true }}
            pub fn load_words(w: &[u32], at: usize) -> V {{
                uint32x4_t([w[at], w[at + 1], w[at + 2], w[at + 3]])
            }}
            pub fn load_be(b: &[u8], off: usize) -> V {{
                uint32x4_t([
                    u32::from_be_bytes(b[off..off + 4].try_into().unwrap()),
                    u32::from_be_bytes(b[off + 4..off + 8].try_into().unwrap()),
                    u32::from_be_bytes(b[off + 8..off + 12].try_into().unwrap()),
                    u32::from_be_bytes(b[off + 12..off + 16].try_into().unwrap()),
                ])
            }}
        }}
    }}

    pub fn compress_portable(st: &[u32; 8], msg: &[u8], off: usize) -> [u32; 8] {{
        let mut blk = [0u8; 64];
        blk.copy_from_slice(&msg[off..off + 64]);
        crate::LOG256.with(|l| l.borrow_mut().push((*st, blk)));
        ref_compress256(st, &blk)
    }}

    pub fn ref_compress256(st: &[u32; 8], block: &[u8]) -> [u32; 8] {{
        let mut w = [0u32; 64];
        for i in 0..16 {{
            w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
        }}
        for i in 16..64 {{
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }}
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *st;
        for i in 0..64 {{
            let bsig1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = h.wrapping_add(bsig1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let bsig0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = bsig0.wrapping_add(maj);
            h = g; g = f; f = e; e = d.wrapping_add(t1);
            d = c; c = b; b = a; a = t1.wrapping_add(t2);
        }}
        [
            st[0].wrapping_add(a), st[1].wrapping_add(b), st[2].wrapping_add(c), st[3].wrapping_add(d),
            st[4].wrapping_add(e), st[5].wrapping_add(f), st[6].wrapping_add(g), st[7].wrapping_add(h),
        ]
    }}

    pub mod arm_wide {{
        use crate::neon_ops::*;
        use crate::{{uint16x8_t, uint32x4_t, uint64x1_t, uint64x2_t, uint8x16_t, uint8x8_t}};
        // Instrument `finish_from_r4` and `compress_block_lanes` by intercepting block words
        // right before running the exact lifted production body!
        fn record_block_words(st: &[u32; 8], m0: uint32x4_t, m1: uint32x4_t, m2: uint32x4_t, m3: uint32x4_t) {{
            let mut blk = [0u8; 64];
            let ms = [m0, m1, m2, m3];
            for g in 0..4 {{
                for j in 0..4 {{
                    blk[16 * g + 4 * j..16 * g + 4 * j + 4].copy_from_slice(&ms[g].0[j].to_be_bytes());
                }}
            }}
            crate::LOG256.with(|l| l.borrow_mut().push((*st, blk)));
        }}
{arm_wide_src}
    }}
}}

pub mod sha512 {{
    use super::*;
    pub {k512}
    pub {h0_512}

    pub mod hw {{
        pub mod arm {{
            use crate::uint64x2_t;
            pub type V = uint64x2_t;
            pub fn available() -> bool {{ true }}
            pub fn load_words(w: &[u64], at: usize) -> V {{ uint64x2_t([w[at], w[at + 1]]) }}
            pub fn load_be(b: &[u8], off: usize) -> V {{
                uint64x2_t([
                    u64::from_be_bytes(b[off..off + 8].try_into().unwrap()),
                    u64::from_be_bytes(b[off + 8..off + 16].try_into().unwrap()),
                ])
            }}
            pub fn add(a: V, b: V) -> V {{
                uint64x2_t([a.0[0].wrapping_add(b.0[0]), a.0[1].wrapping_add(b.0[1])])
            }}
            pub fn ext1(a: V, b: V) -> V {{ uint64x2_t([a.0[1], b.0[0]]) }}
            fn sig1_h(x: u64) -> u64 {{ x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41) }}
            fn sig0_h(x: u64) -> u64 {{ x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39) }}
            fn s0(x: u64) -> u64 {{ x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7) }}
            fn s1(x: u64) -> u64 {{ x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6) }}
            pub fn sha512h(d: V, n: V, m: V) -> V {{
                let (x, y, w) = (n, m, d);
                let hi = ((y.0[1] & x.0[0]) ^ ((!y.0[1]) & x.0[1]))
                    .wrapping_add(sig1_h(y.0[1])).wrapping_add(w.0[1]);
                let tmp = hi.wrapping_add(y.0[0]);
                let lo = ((tmp & y.0[1]) ^ ((!tmp) & x.0[0]))
                    .wrapping_add(sig1_h(tmp)).wrapping_add(w.0[0]);
                uint64x2_t([lo, hi])
            }}
            pub fn sha512h2(d: V, n: V, m: V) -> V {{
                let (x, y, w) = (n, m, d);
                let hi = ((x.0[0] & y.0[1]) ^ (x.0[0] & y.0[0]) ^ (y.0[1] & y.0[0]))
                    .wrapping_add(sig0_h(y.0[0])).wrapping_add(w.0[1]);
                let lo = ((hi & y.0[0]) ^ (hi & y.0[1]) ^ (y.0[1] & y.0[0]))
                    .wrapping_add(sig0_h(hi)).wrapping_add(w.0[0]);
                uint64x2_t([lo, hi])
            }}
            pub fn sha512su0(d: V, n: V) -> V {{
                uint64x2_t([d.0[0].wrapping_add(s0(d.0[1])), d.0[1].wrapping_add(s0(n.0[0]))])
            }}
            pub fn sha512su1(d: V, n: V, m: V) -> V {{
                uint64x2_t([
                    d.0[0].wrapping_add(s1(n.0[0])).wrapping_add(m.0[0]),
                    d.0[1].wrapping_add(s1(n.0[1])).wrapping_add(m.0[1]),
                ])
            }}
        }}
    }}

    pub fn compress(st: &[u64; 8], msg: &[u8], off: usize) -> [u64; 8] {{
        let mut blk = [0u8; 128];
        blk.copy_from_slice(&msg[off..off + 128]);
        crate::LOG512.with(|l| l.borrow_mut().push((*st, blk)));
        ref_compress512(st, &blk)
    }}

    pub fn ref_compress512(st: &[u64; 8], block: &[u8]) -> [u64; 8] {{
        let mut w = [0u64; 80];
        for i in 0..16 {{
            w[i] = u64::from_be_bytes(block[8 * i..8 * i + 8].try_into().unwrap());
        }}
        for i in 16..80 {{
            let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
            let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }}
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *st;
        for i in 0..80 {{
            let bsig1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = h.wrapping_add(bsig1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let bsig0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = bsig0.wrapping_add(maj);
            h = g; g = f; f = e; e = d.wrapping_add(t1);
            d = c; c = b; b = a; a = t1.wrapping_add(t2);
        }}
        [
            st[0].wrapping_add(a), st[1].wrapping_add(b), st[2].wrapping_add(c), st[3].wrapping_add(d),
            st[4].wrapping_add(e), st[5].wrapping_add(f), st[6].wrapping_add(g), st[7].wrapping_add(h),
        ]
    }}

    pub mod paired {{
        use crate::neon_ops::*;
        use crate::{{uint64x2_t, uint8x16_t, uint8x8_t}};
        fn record_block512_words(v: &[uint64x2_t; 4], w: &[uint64x2_t; 8]) {{
            let st = [v[0].0[0], v[0].0[1], v[1].0[0], v[1].0[1], v[2].0[0], v[2].0[1], v[3].0[0], v[3].0[1]];
            let mut blk = [0u8; 128];
            for g in 0..8 {{
                blk[16 * g..16 * g + 8].copy_from_slice(&w[g].0[0].to_be_bytes());
                blk[16 * g + 8..16 * g + 16].copy_from_slice(&w[g].0[1].to_be_bytes());
            }}
            crate::LOG512.with(|l| l.borrow_mut().push((st, blk)));
        }}
{paired_src}
    }}
}}

pub mod hash {{
    use crate::address::Adrs;
    use crate::{{sha256, sha512}};

    pub struct Seed<const N: usize> {{
        pub state: [u32; 8],
        pub state512: [u64; 8],
    }}

    pub fn seed_ctx<const N: usize>(pk_seed: &[u8; N]) -> Seed<N> {{
        let mut b256 = [0u8; 64];
        b256[..N].copy_from_slice(pk_seed);
        let state = sha256::ref_compress256(&sha256::H0, &b256);
        let mut b512 = [0u8; 128];
        b512[..N].copy_from_slice(pk_seed);
        let state512 = sha512::ref_compress512(&sha512::H0, &b512);
        Seed {{ state, state512 }}
    }}

    pub fn trunc512<const N: usize>(st: &[u64; 8]) -> [u8; N] {{
        let mut full = [0u8; 64];
        for i in 0..8 {{ full[8 * i..8 * i + 8].copy_from_slice(&st[i].to_be_bytes()); }}
        let mut out = [0u8; N];
        out.copy_from_slice(&full[..N]);
        out
    }}

    pub fn hash2<const N: usize>(seed: &Seed<N>, adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; N] {{
        if N == 16 {{
            let mut blk = [0u8; 64];
            blk[..22].copy_from_slice(&adrs.compress());
            blk[22..38].copy_from_slice(left);
            blk[38..54].copy_from_slice(right);
            blk[54] = 0x80;
            blk[56..64].copy_from_slice(&(((64 + 22 + 32) as u64) * 8).to_be_bytes());
            let st = sha256::compress_portable(&seed.state, &blk, 0);
            let mut out = [0u8; N];
            for i in 0..4 {{ out[4 * i..4 * i + 4].copy_from_slice(&st[i].to_be_bytes()); }}
            out
        }} else {{
            let mut blk = [0u8; 128];
            blk[..22].copy_from_slice(&adrs.compress());
            blk[22..22 + N].copy_from_slice(left);
            blk[22 + N..22 + 2 * N].copy_from_slice(right);
            blk[22 + 2 * N] = 0x80;
            blk[120..128].copy_from_slice(&(((128 + 22 + 2 * N) as u64) * 8).to_be_bytes());
            let st = sha512::compress(&seed.state512, &blk, 0);
            trunc512::<N>(&st)
        }}
    }}

    pub fn thash_pair<const N: usize>(seed: &Seed<N>, adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; N] {{
        hash2(seed, adrs, left, right)
    }}
}}

pub mod xmss_ctx {{
    pub use crate::address::{{Adrs, TREE, WOTS_HASH}};
    pub use crate::hash::{{hash2, Seed}};
    pub use crate::params::LEN2;
}}

pub mod xmss_arm {{
{xmss_arm_src}
}}

pub mod wots_ctx {{
    pub use crate::address::{{Adrs, WOTS_PK}};
    pub use crate::hash::Seed;
    pub use crate::params::{{LEN2, LEN_MAX}};
}}

pub mod wots_arm {{
{wots_arm_src}
}}

pub mod fors_ctx {{
    pub use crate::address::{{Adrs, FORS_ROOTS}};
    pub use crate::hash::{{thash_pair, Seed}};
    pub use crate::params::{{K_MAX, Params}};
    pub const BATCH: usize = 16;
    pub fn block<const N: usize>(s: &[u8], i: usize) -> [u8; N] {{
        let mut out = [0u8; N];
        out.copy_from_slice(&s[i * N..(i + 1) * N]);
        out
    }}
}}

pub mod fors_arm {{
{fors_arm_src}
}}

// === Independent FIPS 205 reference implementation (also records expected blocks) ===
thread_local! {{
    static REF_LOG256: RefCell<Vec<([u32; 8], [u8; 64])>> = RefCell::new(Vec::new());
    static REF_LOG512: RefCell<Vec<([u64; 8], [u8; 128])>> = RefCell::new(Vec::new());
}}

fn clear_all_logs() {{
    clear_logs();
    REF_LOG256.with(|l| l.borrow_mut().clear());
    REF_LOG512.with(|l| l.borrow_mut().clear());
}}

fn assert_logs_match(label: &str) {{
    let (mut got256, mut got512) = take_logs();
    let mut exp256 = REF_LOG256.with(|l| core::mem::take(&mut *l.borrow_mut()));
    let mut exp512 = REF_LOG512.with(|l| core::mem::take(&mut *l.borrow_mut()));
    got256.sort_unstable();
    exp256.sort_unstable();
    got512.sort_unstable();
    exp512.sort_unstable();
    assert_eq!(got256.len(), exp256.len(), "{{label}}: SHA-256 block count mismatch ({{}} vs {{}})", got256.len(), exp256.len());
    assert_eq!(got256, exp256, "{{label}}: SHA-256 block content/address/padding mismatch");
    assert_eq!(got512.len(), exp512.len(), "{{label}}: SHA-512 block count mismatch ({{}} vs {{}})", got512.len(), exp512.len());
    assert_eq!(got512, exp512, "{{label}}: SHA-512 block content/address/padding mismatch");
}}

mod fips205 {{
    use crate::address::*;
    use crate::params::*;
    use crate::{{sha256, sha512, REF_LOG256, REF_LOG512}};

    pub fn sha256_full(msg: &[u8]) -> [u8; 32] {{
        let mut p = msg.to_vec();
        p.push(0x80);
        while p.len() % 64 != 56 {{ p.push(0); }}
        p.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
        let mut st = sha256::H0;
        for (idx, c) in p.chunks_exact(64).enumerate() {{
            if idx > 0 {{
                let blk: [u8; 64] = c.try_into().unwrap();
                REF_LOG256.with(|l| l.borrow_mut().push((st, blk)));
            }}
            st = sha256::ref_compress256(&st, c);
        }}
        let mut out = [0u8; 32];
        for i in 0..8 {{ out[4 * i..4 * i + 4].copy_from_slice(&st[i].to_be_bytes()); }}
        out
    }}

    pub fn sha512_full(msg: &[u8]) -> [u8; 64] {{
        let mut p = msg.to_vec();
        p.push(0x80);
        while p.len() % 128 != 112 {{ p.push(0); }}
        p.extend_from_slice(&((msg.len() as u128) * 8).to_be_bytes());
        let mut st = sha512::H0;
        for (idx, c) in p.chunks_exact(128).enumerate() {{
            if idx > 0 {{
                let blk: [u8; 128] = c.try_into().unwrap();
                REF_LOG512.with(|l| l.borrow_mut().push((st, blk)));
            }}
            st = sha512::ref_compress512(&st, c);
        }}
        let mut out = [0u8; 64];
        for i in 0..8 {{ out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_be_bytes()); }}
        out
    }}

    pub fn f_hash<const N: usize>(pk_seed: &[u8; N], adrs: Adrs, msg: &[u8; N]) -> [u8; N] {{
        let mut buf = Vec::with_capacity(64 + 22 + N);
        buf.extend_from_slice(pk_seed);
        buf.resize(64, 0);
        buf.extend_from_slice(&adrs.compress());
        buf.extend_from_slice(msg);
        let d = sha256_full(&buf);
        let mut out = [0u8; N];
        out.copy_from_slice(&d[..N]);
        out
    }}

    pub fn prf<const N: usize>(pk_seed: &[u8; N], sk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {{
        f_hash(pk_seed, adrs, sk_seed)
    }}

    pub fn t_hash<const N: usize>(pk_seed: &[u8; N], adrs: Adrs, msg: &[u8]) -> [u8; N] {{
        let mut out = [0u8; N];
        if N == 16 {{
            let mut buf = Vec::with_capacity(64 + 22 + msg.len());
            buf.extend_from_slice(pk_seed);
            buf.resize(64, 0);
            buf.extend_from_slice(&adrs.compress());
            buf.extend_from_slice(msg);
            out.copy_from_slice(&sha256_full(&buf)[..N]);
        }} else {{
            let mut buf = Vec::with_capacity(128 + 22 + msg.len());
            buf.extend_from_slice(pk_seed);
            buf.resize(128, 0);
            buf.extend_from_slice(&adrs.compress());
            buf.extend_from_slice(msg);
            out.copy_from_slice(&sha512_full(&buf)[..N]);
        }}
        out
    }}

    pub fn h_hash<const N: usize>(pk_seed: &[u8; N], adrs: Adrs, l: &[u8; N], r: &[u8; N]) -> [u8; N] {{
        let mut msg = Vec::with_capacity(2 * N);
        msg.extend_from_slice(l);
        msg.extend_from_slice(r);
        t_hash(pk_seed, adrs, &msg)
    }}

    pub fn chain<const N: usize>(x: [u8; N], start: u32, steps: u32, pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {{
        let mut cur = x;
        for j in 0..steps {{
            cur = f_hash(pk_seed, adrs.with_word3(start + j), &cur);
        }}
        cur
    }}

    pub fn base_2b(x: &[u8], b: u32, out_len: usize) -> Vec<u32> {{
        let mut inp = 0usize;
        let mut bits = 0u32;
        let mut total = 0u32;
        let mask = (1u32 << b) - 1;
        let mut out = Vec::with_capacity(out_len);
        for _ in 0..out_len {{
            while bits < b {{
                total = (total << 8) + x[inp] as u32;
                inp += 1;
                bits += 8;
            }}
            bits -= b;
            out.push((total >> bits) & mask);
        }}
        out
    }}

    pub fn wots_digits<const N: usize>(m: &[u8; N]) -> Vec<u32> {{
        let mut d = base_2b(m, 4, 2 * N);
        let mut csum: u32 = 0;
        for &v in &d {{ csum += 15 - v; }}
        csum <<= 4;
        let csum_bytes = [(csum >> 8) as u8, csum as u8];
        d.extend(base_2b(&csum_bytes, 4, 3));
        d
    }}

    pub fn wots_pk_gen<const N: usize>(sk: &[u8; N], pk: &[u8; N], adrs: Adrs) -> [u8; N] {{
        let len = 2 * N + LEN2;
        let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
        let mut tmp = Vec::with_capacity(len * N);
        for i in 0..len {{
            let s = prf(pk, sk, sk_adrs.with_word2(i as u32));
            let ep = chain(s, 0, 15, pk, adrs.with_word2(i as u32));
            tmp.extend_from_slice(&ep);
        }}
        t_hash(pk, adrs.with_type(WOTS_PK).with_keypair(adrs.keypair), &tmp)
    }}

    pub fn wots_sign<const N: usize>(m: &[u8; N], sk: &[u8; N], pk: &[u8; N], adrs: Adrs) -> Vec<u8> {{
        let digits = wots_digits(m);
        let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
        let mut sig = Vec::with_capacity(digits.len() * N);
        for (i, &d) in digits.iter().enumerate() {{
            let s = prf(pk, sk, sk_adrs.with_word2(i as u32));
            let ep = chain(s, 0, d, pk, adrs.with_word2(i as u32));
            sig.extend_from_slice(&ep);
        }}
        sig
    }}

    pub fn wots_pk_from_sig<const N: usize>(sig: &[u8], m: &[u8; N], pk: &[u8; N], adrs: Adrs) -> [u8; N] {{
        let digits = wots_digits(m);
        let mut tmp = Vec::with_capacity(digits.len() * N);
        for (i, &d) in digits.iter().enumerate() {{
            let mut s = [0u8; N];
            s.copy_from_slice(&sig[i * N..(i + 1) * N]);
            let ep = chain(s, d, 15 - d, pk, adrs.with_word2(i as u32));
            tmp.extend_from_slice(&ep);
        }}
        t_hash(pk, adrs.with_type(WOTS_PK).with_keypair(adrs.keypair), &tmp)
    }}

    pub fn xmss_node<const N: usize>(sk: &[u8; N], i: u32, z: u32, pk: &[u8; N], adrs: Adrs) -> [u8; N] {{
        if z == 0 {{
            wots_pk_gen(sk, pk, adrs.with_type(WOTS_HASH).with_keypair(i))
        }} else {{
            let l = xmss_node(sk, 2 * i, z - 1, pk, adrs);
            let r = xmss_node(sk, 2 * i + 1, z - 1, pk, adrs);
            h_hash(pk, adrs.with_type(TREE).with_word2(z).with_word3(i), &l, &r)
        }}
    }}

    pub fn fors_node<const N: usize>(sk: &[u8; N], i: u32, z: u32, pk: &[u8; N], adrs: Adrs) -> [u8; N] {{
        if z == 0 {{
            let s = prf(pk, sk, adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(i));
            f_hash(pk, adrs.with_word2(0).with_word3(i), &s)
        }} else {{
            let l = fors_node(sk, 2 * i, z - 1, pk, adrs);
            let r = fors_node(sk, 2 * i + 1, z - 1, pk, adrs);
            h_hash(pk, adrs.with_word2(z).with_word3(i), &l, &r)
        }}
    }}

    pub fn fors_pk_from_sig<const N: usize>(p: &Params, sig: &[u8], md: &[u8], pk: &[u8; N], adrs: Adrs) -> [u8; N] {{
        let indices = base_2b(md, p.a, p.k as usize);
        let mut roots = Vec::with_capacity(p.k as usize * N);
        for (i, &idx) in indices.iter().enumerate() {{
            let mut node = [0u8; N];
            let sk_off = (i * (p.a as usize + 1)) * N;
            node.copy_from_slice(&sig[sk_off..sk_off + N]);
            let mut ti = ((i as u32) << p.a) + idx;
            node = f_hash(pk, adrs.with_word2(0).with_word3(ti), &node);
            for h in 0..p.a as usize {{
                let mut sib = [0u8; N];
                let sib_off = (i * (p.a as usize + 1) + 1 + h) * N;
                sib.copy_from_slice(&sig[sib_off..sib_off + N]);
                let parent = ti >> 1;
                let a_node = adrs.with_word2((h + 1) as u32).with_word3(parent);
                node = if ti & 1 == 0 {{
                    h_hash(pk, a_node, &node, &sib)
                }} else {{
                    h_hash(pk, a_node, &sib, &node)
                }};
                ti = parent;
            }}
            roots.extend_from_slice(&node);
        }}
        t_hash(pk, adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair), &roots)
    }}
}}

fn check_wots_suite<const N: usize, const L: usize>() {{
    let sk: [u8; N] = core::array::from_fn(|i| (i * 19 + 3) as u8);
    let pk: [u8; N] = core::array::from_fn(|i| (i * 7 + 11) as u8);
    let seed = hash::seed_ctx(&pk);
    let adrs = address::Adrs::new()
        .with_layer(2)
        .with_tree(0x0123_4567_89ab_cdef)
        .with_type(address::WOTS_HASH)
        .with_keypair(13);
    let len = 2 * N + params::LEN2;

    // 1. wots_endpoints_1, wots_endpoints_2, wots_endpoints_4
    let mut buf1 = [0u8; L];
    sha256::arm_wide::wots_endpoints_1::<N>(&seed.state, &sk, adrs, &mut buf1);
    let sk_adrs = adrs.with_type(address::WOTS_PRF).with_keypair(adrs.keypair);
    for c in 0..len {{
        let s = fips205::prf(&pk, &sk, sk_adrs.with_word2(c as u32));
        let ep = fips205::chain(s, 0, 15, &pk, adrs.with_word2(c as u32));
        assert_eq!(&buf1[22 + c * N..22 + (c + 1) * N], &ep);
    }}

    let mut bufs2 = [[0u8; L]; 2];
    sha256::arm_wide::wots_endpoints_2::<N, L>(&seed.state, &sk, adrs, 10, &mut bufs2);
    for lane in 0..2 {{
        let la = adrs.with_type(address::WOTS_HASH).with_keypair(10 + lane as u32);
        let lsk = la.with_type(address::WOTS_PRF).with_keypair(la.keypair);
        for c in 0..len {{
            let s = fips205::prf(&pk, &sk, lsk.with_word2(c as u32));
            let ep = fips205::chain(s, 0, 15, &pk, la.with_word2(c as u32));
            assert_eq!(&bufs2[lane][22 + c * N..22 + (c + 1) * N], &ep);
        }}
    }}

    let mut bufs4 = [[0u8; L]; 4];
    sha256::arm_wide::wots_endpoints_4::<N, L>(&seed.state, &sk, adrs, 20, &mut bufs4);
    for lane in 0..4 {{
        let la = adrs.with_type(address::WOTS_HASH).with_keypair(20 + lane as u32);
        let lsk = la.with_type(address::WOTS_PRF).with_keypair(la.keypair);
        for c in 0..len {{
            let s = fips205::prf(&pk, &sk, lsk.with_word2(c as u32));
            let ep = fips205::chain(s, 0, 15, &pk, la.with_word2(c as u32));
            assert_eq!(&bufs4[lane][22 + c * N..22 + (c + 1) * N], &ep);
        }}
    }}

    // 2. wots_sign_fused & wots_recover edge cases (all-0, all-15, mixed 0/15, random)
    let sig_src: Vec<u8> = (0..len * N).map(|i| ((i * 29 + 5) & 0xff) as u8).collect();
    for variant in 0..6usize {{
        let digits: Vec<u32> = (0..len).map(|i| match variant {{
            0 => 0,
            1 => 15,
            2 => if i % 2 == 0 {{ 0 }} else {{ 15 }},
            3 => if i < 3 {{ 15 }} else {{ 0 }},
            4 => if i < 2 {{ 0 }} else {{ (i % 15 + 1) as u32 }},
            _ => ((i * 17 + variant * 5) % 16) as u32,
        }}).collect();

        // wots_sign_fused
        let mut out_sig = vec![0u8; len * N];
        sha256::arm_wide::wots_sign_fused::<N>(&seed.state, &sk, adrs, &digits, &mut out_sig);
        for (c, &d) in digits.iter().enumerate() {{
            let s = fips205::prf(&pk, &sk, sk_adrs.with_word2(c as u32));
            let ep = fips205::chain(s, 0, d, &pk, adrs.with_word2(c as u32));
            assert_eq!(&out_sig[c * N..(c + 1) * N], &ep, "wots_sign_fused<{{N}}> variant={{variant}} c={{c}}");
        }}

        // wots_recover
        let mut rec_buf = [0u8; L];
        sha256::arm_wide::wots_recover::<N>(&seed.state, adrs, &sig_src, &digits, &mut rec_buf);
        for (c, &d) in digits.iter().enumerate() {{
            let mut s = [0u8; N];
            s.copy_from_slice(&sig_src[c * N..(c + 1) * N]);
            let ep = fips205::chain(s, d, 15 - d, &pk, adrs.with_word2(c as u32));
            assert_eq!(&rec_buf[22 + c * N..22 + (c + 1) * N], &ep, "wots_recover<{{N}}> variant={{variant}} c={{c}}");
        }}
    }}

    // 3. wots::arm::{{pk_gen, sign, recover}} + round-trip (with EXACT block-log audit!)
    clear_all_logs();
    let pk_gen_actual = wots_arm::pk_gen::<N>(&sk, &seed, adrs);
    let pk_gen_exp = fips205::wots_pk_gen(&sk, &pk, adrs);
    assert_eq!(pk_gen_actual, pk_gen_exp, "wots::arm::pk_gen<{{N}}> mismatch");
    assert_logs_match(&format!("wots::arm::pk_gen<{{N}}>"));
    for mv in [0x00u8, 0xffu8, 0x5au8, 0xa5u8, 0x37u8] {{
        let m: [u8; N] = core::array::from_fn(|i| mv.wrapping_add((i * 13) as u8));
        clear_all_logs();
        let sig_act = wots_arm::sign::<N>(&m, &sk, &seed, adrs);
        let sig_exp = fips205::wots_sign(&m, &sk, &pk, adrs);
        assert_eq!(sig_act, sig_exp, "wots::arm::sign<{{N}}> mismatch");
        assert_logs_match(&format!("wots::arm::sign<{{N}}> mv={{mv}}"));
        clear_all_logs();
        let rec_act = wots_arm::recover::<N>(&sig_act, &m, &seed, adrs);
        let rec_ref = fips205::wots_pk_from_sig(&sig_act, &m, &pk, adrs);
        assert_eq!(rec_act, pk_gen_exp, "wots::arm::recover<{{N}}> round-trip mismatch");
        assert_eq!(rec_act, rec_ref);
        assert_logs_match(&format!("wots::arm::recover<{{N}}> mv={{mv}}"));
    }}

    // 4. xmss::arm::batch_root for heights 1..=4 (both even and odd index, with block-log audit!)
    let xmss_adrs = address::Adrs::new().with_layer(4).with_tree(0x1122_3344_5566_7788);
    for h in 1..=4u32 {{
        for idx in [0u32, 3u32] {{
            clear_all_logs();
            let act = xmss_arm::batch_root::<N>(&sk, idx, h, &seed, xmss_adrs);
            let exp = fips205::xmss_node(&sk, idx, h, &pk, xmss_adrs);
            assert_eq!(act, exp, "xmss::arm::batch_root<{{N}}> h={{h}} idx={{idx}} mismatch");
            assert_logs_match(&format!("xmss::arm::batch_root<{{N}}> h={{h}} idx={{idx}}"));
        }}
    }}
}}

fn check_sha256_multi_and_parents_16() {{
    let pk = [0x42u8; 16];
    let seed = hash::seed_ctx(&pk);
    // compress_multi_{1,2,4} on L = 64, 128, 640
    fn check_cm<const L: usize>(st: &[u32; 8]) {{
        let msgs: [[u8; L]; 4] = core::array::from_fn(|l| core::array::from_fn(|i| ((l * 37 + i * 19 + 5) & 0xff) as u8));
        let mut exp = [[0u8; 16]; 4];
        for l in 0..4 {{
            let mut s = *st;
            for c in msgs[l].chunks_exact(64) {{ s = sha256::ref_compress256(&s, c); }}
            for w in 0..4 {{ exp[l][4 * w..4 * w + 4].copy_from_slice(&s[w].to_be_bytes()); }}
        }}
        let mut o4 = [[0u8; 16]; 4];
        sha256::arm_wide::compress_multi_4::<L>(st, &msgs, &mut o4);
        assert_eq!(o4, exp);
        let mut o2 = [[0u8; 16]; 2];
        let p2: &[[u8; L]; 2] = (&msgs[0..2]).try_into().unwrap();
        sha256::arm_wide::compress_multi_2::<L>(st, p2, &mut o2);
        assert_eq!(o2, exp[0..2]);
        for l in 0..4 {{
            assert_eq!(sha256::arm_wide::compress_multi_1(st, &msgs[l]), exp[l]);
        }}
    }}
    check_cm::<64>(&seed.state);
    check_cm::<128>(&seed.state);
    check_cm::<640>(&seed.state);

    // parents_16 for counts 1..=8
    let adrs = address::Adrs::new().with_layer(1).with_tree(0x9988_7766_5544_3322).with_type(address::TREE).with_word2(2);
    for count in 1..=8usize {{
        let orig: Vec<[u8; 16]> = (0..2 * count).map(|i| core::array::from_fn(|b| ((i * 31 + b * 7 + count) & 0xff) as u8)).collect();
        let mut vals = orig.clone();
        sha256::arm_wide::parents_16(&seed.state, adrs, 50, &mut vals, count);
        for i in 0..count {{
            let exp = fips205::h_hash(&pk, adrs.with_word3(50 + i as u32), &orig[2 * i], &orig[2 * i + 1]);
            assert_eq!(vals[i], exp, "parents_16 count={{count}} i={{i}} mismatch");
        }}
    }}
}}

fn check_fors_param_set<const N: usize>(p: &params::Params, name: &str) {{
    let sk: [u8; N] = core::array::from_fn(|i| (i * 23 + 5) as u8);
    let pk: [u8; N] = core::array::from_fn(|i| (i * 11 + 7) as u8);
    let seed = hash::seed_ctx(&pk);
    let adrs = address::Adrs::new()
        .with_layer(0)
        .with_tree(0xabcd_ef01_2345_6789)
        .with_type(address::FORS_TREE)
        .with_keypair(42);

    // 1. fors_leaves for counts 1..=16
    for count in [1usize, 2, 3, 4, 5, 7, 8, 16] {{
        let mut out = vec![[0u8; N]; count];
        sha256::arm_wide::fors_leaves::<N>(&seed.state, &sk, adrs, 100, &mut out);
        for i in 0..count {{
            let exp = fips205::fors_node(&sk, 100 + i as u32, 0, &pk, adrs);
            assert_eq!(out[i], exp, "fors_leaves {{name}} count={{count}} i={{i}} mismatch");
        }}
    }}

    // 2. fors::arm::subtree for heights 0..=4 (with exact block-log audit!)
    for h in 0..=4u32 {{
        clear_all_logs();
        let act = fors_arm::subtree::<N>(&sk, 5, h, &seed, adrs);
        let exp = fips205::fors_node(&sk, 5, h, &pk, adrs);
        assert_eq!(act, exp, "fors::arm::subtree {{name}} h={{h}} mismatch");
        assert_logs_match(&format!("fors::arm::subtree {{name}} h={{h}}"));
    }}

    // 3. fors_verify_leaves, fors_path_level_16 (N=16), and fors::arm::pk_from_sig (with exact block-log audit!)
    let k = p.k as usize;
    let a = p.a as usize;
    let sig_len = k * (a + 1) * N;
    let sig: Vec<u8> = (0..sig_len).map(|i| ((i * 43 + (i >> 4) * 17 + 9) & 0xff) as u8).collect();
    for md_seed in [0x00u8, 0xffu8, 0x5au8, 0xc3u8] {{
        let md: Vec<u8> = (0..p.md_bytes()).map(|i| md_seed.wrapping_add((i * 29) as u8)).collect();
        clear_all_logs();
        let act = fors_arm::pk_from_sig::<N>(p, &sig, &md, &seed, adrs);
        let exp = fips205::fors_pk_from_sig::<N>(p, &sig, &md, &pk, adrs);
        assert_eq!(act, exp, "fors::arm::pk_from_sig {{name}} md_seed={{md_seed}} mismatch");
        assert_logs_match(&format!("fors::arm::pk_from_sig {{name}} md_seed={{md_seed}}"));
    }}

    // 4. Direct fors_verify_leaves & fors_path_level_16 check
    let raw = fips205::base_2b(&vec![0x55u8; p.md_bytes()], p.a, k);
    let mut idxs: Vec<u32> = (0..k).map(|i| ((i as u32) << p.a) + raw[i]).collect();
    let mut vals = vec![[0u8; N]; k];
    sha256::arm_wide::fors_verify_leaves::<N>(&seed.state, adrs, &sig, &idxs, &mut vals, a);
    for i in 0..k {{
        let mut sk_leaf = [0u8; N];
        let off = i * (a + 1) * N;
        sk_leaf.copy_from_slice(&sig[off..off + N]);
        let exp = fips205::f_hash(&pk, adrs.with_word2(0).with_word3(idxs[i]), &sk_leaf);
        assert_eq!(vals[i], exp, "fors_verify_leaves {{name}} i={{i}} mismatch");
    }}
    if N == 16 {{
        let mut vals16: Vec<[u8; 16]> = vals.iter().map(|v| {{
            let mut b = [0u8; 16]; b.copy_from_slice(&v[..16]); b
        }}).collect();
        let orig_vals16 = vals16.clone();
        let orig_idxs = idxs.clone();
        sha256::arm_wide::fors_path_level_16(&seed.state, adrs, &sig, &mut idxs, &mut vals16, a, 0);
        let pk16: [u8; 16] = pk[..16].try_into().unwrap();
        for i in 0..k {{
            let pos = orig_idxs[i];
            let parent = pos >> 1;
            assert_eq!(idxs[i], parent);
            let sib_off = (i * (a + 1) + 1) * 16;
            let sib: [u8; 16] = sig[sib_off..sib_off + 16].try_into().unwrap();
            let adr = adrs.with_word2(1).with_word3(parent);
            let exp = if pos & 1 == 0 {{
                fips205::h_hash(&pk16, adr, &orig_vals16[i], &sib)
            }} else {{
                fips205::h_hash(&pk16, adr, &sib, &orig_vals16[i])
            }};
            assert_eq!(vals16[i], exp, "fors_path_level_16 {{name}} i={{i}} mismatch");
        }}
    }}
}}

fn main() {{
    check_wots_suite::<16, 640>();
    check_wots_suite::<24, 1280>();
    check_wots_suite::<32, 2304>();
    check_sha256_multi_and_parents_16();

    // All 6 FIPS 205 SHA-2 parameter sets
    check_fors_param_set::<16>(&params::SHA2_128S, "SHA2-128s");
    check_fors_param_set::<16>(&params::SHA2_128F, "SHA2-128f");
    check_fors_param_set::<24>(&params::SHA2_192S, "SHA2-192s");
    check_fors_param_set::<24>(&params::SHA2_192F, "SHA2-192f");
    check_fors_param_set::<32>(&params::SHA2_256S, "SHA2-256s");
    check_fors_param_set::<32>(&params::SHA2_256F, "SHA2-256f");

    println!("Lifted production caller replay across all 6 SHA-2 parameter sets: OK");
}}
"""
    rs = scratch / "replay_arm_wide.rs"
    bin_path = scratch / "replay_arm_wide"
    rs.write_text(harness)
    subprocess.run(["rustc", "--edition=2021", "-O", rs, "-o", bin_path], check=True)
    subprocess.run([bin_path], check=True)


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo/bin"),
            str(Path.home() / ".elan/bin"),
            os.environ["PATH"],
        ]
    )
    check_sha256_k()
    runpy.run_path(str(HERE / "check-arm-sign-order.py"))["check"]()
    subprocess.run([os.sys.executable, HERE / "check-arm-wots-transitions.py"], check=True)
    subprocess.run([os.sys.executable, HERE / "check-arm-keygen.py"], check=True)
    subprocess.run([os.sys.executable, HERE / "check-arm-wots-recovery.py"], check=True)
    subprocess.run([os.sys.executable, HERE / "check-arm-xmss-leaves.py"], check=True)
    subprocess.run([os.sys.executable, HERE / "check-arm-xmss-callers.py"], check=True)
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        check_extraction(scratch)
        check_symbolic_kernel_ast(scratch)
        check_full_caller_replay(scratch)

    common["run"](
        ["lake", "build", "Armwide.Encoders", "Armwide.WotsRefill", "Armwide.Kernel"],
        LEAN,
    )
    facade["audit_theorems"](
        "Armwide.Encoders",
        [
            "slhdsa.Armwide.wots_digits_stack_spec",
            "slhdsa.Armwide.base_2b_stack_spec",
            "slhdsa.Armwide.base_2b_stack_valid_params",
            "slhdsa.Armwide.prepare_tlen_spec",
            "slhdsa.Armwide.prepare_tlen_sha256_pad",
            "slhdsa.Armwide.prepare_tlen_sha512_pad",
            "slhdsa.Armwide.parent_block_512_spec",
        ],
    )
    facade["audit_theorems"](
        "Armwide.WotsRefill",
        [
            "slhdsa.Armwide.WotsRefill.sort_descending_spec",
            "slhdsa.Armwide.WotsRefill.recover_scheduler_eq_fips",
            "slhdsa.Armwide.WotsRefill.recover_with_extracted_sort",
            "slhdsa.Armwide.WotsRefill.recover_all_fifteen",
            "slhdsa.Armwide.WotsRefill.recover_all_zero",
            "slhdsa.Armwide.WotsRefill.sign_fused_scheduler_eq_fips",
            "slhdsa.Armwide.WotsRefill.sign_fused_digit_zero",
            "slhdsa.Armwide.WotsRefill.sign_fused_digit_fifteen",
        ],
    )
    facade["audit_theorems"](
        "Armwide.Kernel",
        [
            "slhdsa.Armwide.Kernel.deferred_step01_eq_kstep01",
            "slhdsa.Armwide.Kernel.finishFromR4_true_eq_compress",
            "slhdsa.Armwide.Kernel.finishFromR4_false_eq_compress_take4",
            "slhdsa.Armwide.Kernel.compressBlockLane_true_eq_compress",
            "slhdsa.Armwide.Kernel.compressBlockLane_false_eq_compress_take4",
            "slhdsa.Armwide.Kernel.finishFromR4_storeN_eq_fips",
        ],
    )
    print("All ARM64 SHA-256 arm_wide.rs + safe caller checks & Lean axiom audits PASSED!")


if __name__ == "__main__":
    main()
