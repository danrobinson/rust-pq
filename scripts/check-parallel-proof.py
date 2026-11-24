# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Replay the parallel sign, subtree and single-state permutation proofs."""

import re
import runpy
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
common = facade["common"]
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
sys.path.insert(0, str(HERE / "parallel-proof"))
import build
import signer
import subtree


def check_dispatch(scratch):
    llbc = scratch / "fast.llbc"
    generated = scratch / "fast"
    cuts = (
        "crate::shake256::round",
        "crate::sha256::x86::avx512_available",
        "crate::shake256::stream_x86::blocks",
    )
    run(
        [
            ROOT / ".tools/aeneas/charon/bin/charon",
            "cargo",
            "--preset=aeneas",
            "--start-from",
            "crate::shake256::permute",
            *(arg for name in cuts for arg in ("--opaque", name)),
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "parallel",
            "--target",
            "x86_64-unknown-linux-gnu",
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
            "-split-files",
            "-dest",
            generated,
            llbc,
        ],
        ROOT,
    )

    def decls(file, namespace):
        return set(common["declarations"](common["body"](file, namespace)))

    scalar = decls(LEAN / "Keccakscalar/Funs.lean", "KeccakScalarRust")
    entry = (
        (LEAN / "Parallel/Dispatch.lean")
        .read_text()
        .split("def shake256.permute\n", 1)[1]
        .split("\ntheorem ", 1)[0]
    )
    expected = {
        d
        for d in scalar
        if d.startswith(
            (
                "@[global_simps, irreducible]\ndef shake256.RC",
                "@[rust_loop_body]\ndef shake256.permute_loop.body",
                "@[rust_loop]\ndef shake256.permute_loop",
            )
        )
    }
    if len(expected) != 3 or decls(generated / "Types.lean", "slhdsa"):
        raise ValueError("unexpected scalar declarations or nominal input types")
    if decls(generated / "Funs.lean", "slhdsa") != expected | {
        "def shake256.permute\n" + entry.strip("\n")
    }:
        raise ValueError(
            "feature-selected permutation no longer matches the proved caller"
        )
    bindings = {
        "sha256.x86.avx512_available": "GatherRust.sha256.x86.avx512_available",
        "shake256.stream_x86.blocks": "KgridbulkRust.shake256.stream_x86.blocks",
        "shake256.round": "KeccakScalarRust.shake256.round",
    }
    checks = ["import Parallel.Dispatch", "open Aeneas Aeneas.Std Result"]
    external = (
        (generated / "FunsExternal_Template.lean")
        .read_text()
        .split("open slhdsa", 1)[1]
    )
    for declaration in common["declarations"](external):
        name, signature = re.fullmatch(
            r"axiom\s+(\S+)\s*:\s*(.*)", declaration, re.DOTALL
        ).groups()
        checks.append(f"example : {signature} := {bindings.pop(name)}")
    if bindings:
        raise ValueError("missing permutation dependencies")
    for family in ("sha2", "shake"):
        for level in (128, 192, 256):
            for variant in ("s", "f"):
                p = f"Spec.{family}_{level}{variant}"
                checks.append(f"example : {p}.a ≤ 14 ∧ {p}.hp ≤ 9 := by decide")
                if family == "shake":
                    checks.append(
                        f"example : {p}.len = 2*{p}.n+3 ∧ {p}.w=16 := by decide"
                    )
    run(["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(checks), text=True)


def check_entry_calls():
    def single(file, fragment, count=1):
        source = re.sub(r"//[^\n]*|\s+", "", (build.SRC / file).read_text())
        if source.count(re.sub(r"\s+", "", fragment)) != count:
            raise ValueError(f"review the feature-selected call in {file}")

    single(
        "xmss.rs",
        """shake_only! {
        #[cfg(all(feature = "platform-sha2", any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        )))]
        if z >= 1 && super::batch::available::<N>() {
            return super::batch::xmss_subtree(sk_seed, seed, i, z, adrs);
        }
    }""",
    )
    single("shake/batch.rs", "matches!(N, 16 | 24 | 32) && parallel::available()")
    single(
        "slh.rs",
        """#[cfg(all(feature = "parallel", not(target_os = "none")))]
        if let Some(sig) = parallel::sign($p, md, &$sk_seed, &seed, adrs, &$r, idx_tree, idx_leaf) {
            return sig;
        }""",
    )
    for file in ("slh.rs", "slh/message.rs"):
        single(file, "sign_digest!(N, p, sk_seed, pk_seed, r, digest)", 2 if file == "slh.rs" else 1)


def main():
    check_entry_calls()
    modules = {
        "Parallel.Fused": "ParallelFused.context_sign_fips",
        "Parallel.SplitTree": "ParallelSplitTree.keygenRoot",
        "Parallel.Batch": "ParallelBatch.verify_all",
        "Parallel.Subtree": "ParallelSubtree.subtree_eq",
        "Parallel.Dispatch": "slhdsa.ParallelDispatch.permute_fips",
    }
    run(["lake", "build", *modules], LEAN)
    for module, theorem in modules.items():
        facade["audit_theorems"](module, [theorem])
    with tempfile.TemporaryDirectory() as tmp:
        check_dispatch(Path(tmp))
        signer.main()
        build.check_tree_layout(Path(tmp))
        image = build.build(Path(tmp))
        for n in (16, 24, 32):
            for height in (1, 2, 3):
                subtree.check(image, n, height)
    run(["sh", HERE / "check-keccak-assembly.sh", "parallel"], ROOT)


if __name__ == "__main__":
    main()
