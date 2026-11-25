#!/usr/bin/env python3
"""Check cached SIMD WOTS signing and public-key recovery.

Lean verifies the emitted sort, both emitted scatter loops, chain iteration and equality
of the lane model to the portable WOTS computation. Kani checks the intervening Rust
gather calls, packed-state initialization, one inductive loop step and output extraction.
Permutation outputs and table lookups are arbitrary. The extracted util.block theorem
supplies the valid-slice contract for recovery reads. Replay with Kani 0.68.0.
"""
import argparse
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile
import textwrap

HERE = Path(__file__).resolve().parent
shared = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
ROOT, LEAN = shared["ROOT"], shared["LEAN"]
extract_fn = runpy.run_path(str(HERE / "parallel-proof/build.py"))["function"]
KANI = Path(os.environ.get("KANI", Path.home() / ".kani/kani-0.68.0/bin/kani-driver"))
CORE = ROOT / "rust/src"


def batch_body(source, name, begin, end):
    batch_header = "for batch in order[..digits.len()].chunks(WIDTH) {"
    head, loop = extract_fn(source, name).split(batch_header)
    body, tail = loop.split("\n    }", 1)
    if head.split("{", 1)[1].strip() != begin or tail.strip() != end.strip():
        raise ValueError(f"{name} changed its batch partition, result initialization or assembly")
    return body


def batch_parts(source):
    sign = batch_body(source, "wots_sign",
                      "let order = chain_order(digits);\n    let mut sig = vec![0u8; N * digits.len()];",
                      "sig\n}")
    recover = batch_body(source, "wots_pk_from_sig",
                         "let order = chain_order(digits);\n    let mut endpoints = [[0u8; N]; 67];",
                         """let mut pk = super::start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
    for key in &endpoints[..digits.len()] {
        pk.absorb(key);
    }
    super::digest(pk)
}""")
    split = "for (lane, &id) in batch.iter().enumerate() {"
    return [tuple(batch.split(split)) for batch in (sign, recover)]


def harness(source, n, width):
    (sign, _), (recover, _) = batch_parts(source)
    params = (CORE / "params.rs").read_text()
    layout = (CORE / "shake256/parallel.rs").read_text()
    if set(re.findall(r"const WIDTH: usize = (\d+);", layout)) != {"3", "8"}:
        raise ValueError("production SIMD widths changed")
    if "pub(crate) type States = [[u64; WIDTH]; 25];" not in layout:
        raise ValueError("production SIMD state layout changed")
    code = (HERE / "cache-proof/wots-simd.rs").read_text()
    chains = extract_fn(source, "chains")
    prefix, body = chains.split("while index != end {")
    body, finish = body.split("\n    }\n    let mut result")
    init = prefix.split("-> [[u8; N]; WIDTH] {", 1)[1]
    if not finish.rstrip().endswith("result\n}"):
        raise ValueError("unexpected packed chain result")
    for key, value in {
        "ADDRESS_FILE": CORE / "address.rs", "NODE_BYTES": n,
        "LANE_COUNT": width, "SIGN_BATCH": sign, "RECOVER_BATCH": recover,
        "SECRET_FUNCTION": extract_fn(source, "secrets"),
        "W_PARAMETER": re.search(r"pub const W: u32 = (\d+);", params).group(1),
        "CHECKSUM_DIGITS": re.search(r"pub const LEN2: usize = (\d+);", params).group(1),
        "PACKED_INIT": init, "PACKED_BODY": body, "PACKED_FINISH": "let mut result"+finish.rstrip()[:-1],
        "PACKED_OFFSET": re.search(r"let offset = (.*?);", init).group(1),
        "PACKED_FUNCTIONS": "\n".join(extract_fn(source, f) for f in ("word","header","put")),
    }.items():
        code = code.replace(key, str(value))
    return code


def same_program(generated, module, target):
    def tokens(text):
        text = re.sub(r"/--.*?-/", "", text, flags=re.S)
        return text.split("namespace CacheopsRust\n", 1)[1].split()
    actual = tokens((generated / "Funs.lean").read_text())
    expected = tokens((LEAN / f"Cachepath/{module}.lean").read_text())
    if actual != expected:
        raise ValueError(f"{module} differs from the Rust extracted on {target}")


def check_lean(source):
    (_, sign), (_, recover) = batch_parts(source)
    sig = "sig:&mut alloc::vec::Vec<u8>"
    key = "endpoints:&mut [[u8;N];67]"
    loops = []
    for name, tail, destination in (("sig", sign, sig), ("key", recover, key)):
        loops.append(
            f"pub fn cell_{name}<const N:usize,const WIDTH:usize>"
            f"(batch:&[usize], values:&[[u8;N];WIDTH], {destination}) {{"
            f"for (lane, &id) in batch.iter().enumerate() {{{tail}\n}}"
        )
    for target in shared["facade"]["TARGETS"]:
        with tempfile.TemporaryDirectory() as temp:
            tmp = Path(temp)
            order = shared["extract_target"](target, tmp / "order", ("crate::cache::shake_ops::simd::chain_order",), ())
            same_program(order, "WotsOrderProgram", target)
            raw = shared["extract_target"](target, tmp / "inputs", ("crate::wots::wots_digits", "crate::util::block"), ())
            parse = shared["generated_declarations"]
            produced = parse(raw / "Funs.lean", "CacheopsRust", strict=True)
            portable = parse(ROOT / "lean/Slhdsa/Funs.lean", "slhdsa")
            if not {"util.block", "wots.wots_digits"} <= produced.keys():
                raise ValueError("missing production WOTS input operations")
            for name, body in produced.items():
                if portable.get(name) != body:
                    raise ValueError(f"{target}: {name} differs from the proved WOTS input operation")
            crate = shared["copy_rust_crate"](tmp)
            with (crate / "src/lib.rs").open("a") as out:
                out.write("\n" + "\n".join(loops))
            scatter = shared["extract_target"](target, tmp / "scatter", ("crate::cell_sig", "crate::cell_key"), (), crate=crate)
            same_program(scatter, "WotsScatterProgram", target)
    shared["facade"]["audit_theorems"]("Slhdsa.Proofs.Util", ["slhdsa.block_spec"])
    for module, names in {
        "WotsLanes": ("sign_spec", "recover_spec", "sign_eq_scalar", "recover_eq_scalar", "tracked_lane", "loop_termination"),
        "WotsOrder": ("chain_order_spec",),
        "WotsScatter": ("sig_spec", "sig_rows", "key_spec", "writes_at"),
    }.items():
        shared["facade"]["run"](["lake", "build", f"Cachepath.{module}"], LEAN)
        shared["facade"]["audit_theorems"](f"Cachepath.{module}", [f"CacheopsRust.{module}.{name}" for name in names])


def run_kani(source, n, width, operation, *, mutation=False):
    with tempfile.TemporaryDirectory(prefix="rust-pq-cache-wots-") as folder:
        p = Path(folder) / "wots.rs"
        p.write_text(harness(source, n, width))
        env = os.environ.copy()
        env["PATH"] = os.pathsep.join([str(KANI.parent), str(Path.home() / ".cargo/bin"), env["PATH"]])
        result = subprocess.run(
            [KANI, "--output-format", "terse", "--harness", operation, p],
            cwd=folder, env=env, check=not mutation, text=True, capture_output=mutation,
        )
        if mutation:
            if result.returncode != 1 or not re.search(r"Failed Checks:.*assert", result.stdout):
                raise ValueError("mutation did not reach a failing Kani assertion\n" + result.stdout + result.stderr)
            print(f"Kani rejected the mutated {operation} at N={n}, WIDTH={width}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--operation", choices=("order", "packed_chains", "packed_boundary", "gather_batch"))
    parser.add_argument("--n", type=int, choices=(16,24,32))
    parser.add_argument("--width", type=int, choices=(3,8))
    parser.add_argument("--mutation-tests", action="store_true", help="check the sensitivity of the packed and gather contracts")
    args = parser.parse_args()
    src = (CORE / "cache.rs").read_text().split("    mod simd {", 1)[1].split("\n    }\n", 1)[0]
    source = textwrap.dedent(src)
    if args.mutation_tests:
        for before, after, op in (
            ("if index[lane] < end[lane] {", "if index[lane] <= end[lane] {", "packed_chains"),
            ("let values = ids.map(|i| block(sig, i));", "let values = ids.map(|_| block(sig, 0));", "gather_batch"),
        ):
            if source.count(before) != 1:
                raise ValueError("Could not locate WOTS mutation site")
            run_kani(source.replace(before, after), 16, 3, op, mutation=True)
        return
    if args.operation in (None, "order"):
        check_lean(source)
    if args.operation == "order":
        return
    for n in (args.n,) if args.n else (16,24,32):
        for width in (args.width,) if args.width else (3,8):
            for op in (args.operation,) if args.operation else ("packed_chains","packed_boundary","gather_batch"):
                run_kani(source, n, width, op)
                print(f"Kani proved {op} at N={n}, WIDTH={width}",flush=True)


if __name__ == "__main__":
    main()
