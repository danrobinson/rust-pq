#!/usr/bin/env python3
"""Verify hardware and software dispatch, including RustCrypto's forced soft builds."""
import json
import os
from pathlib import Path
import re
import runpy
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
TARGET = "x86_64-unknown-linux-gnu"


def extract(scratch, package, namespace, root_names, boundary_names, flags="", manifest=None):
    out = scratch / package
    filename = scratch / (package.lower() + ".llbc")
    environment = dict(os.environ, CARGO_TARGET_DIR=str(scratch / "target"), RUSTFLAGS=flags)
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         *(arg for name in root_names for arg in ("--start-from", name)),
         *(arg for name in boundary_names for arg in ("--opaque", name)),
         "--dest-file", filename, "--", "--locked", "--target", TARGET,
         *(["--manifest-path", manifest] if manifest else ["--features", "platform-sha2"])],
        ROOT / "rust", env=environment)
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
         "-no-progress-bar", "-namespace", namespace, "-split-files", "-dest", out, filename], ROOT)
    return out


def equal(text, expected, description):
    if text != expected:
        raise ValueError(description)


def detector(source, module, features):
    expression = r'cpufeatures::new!\(' + module + r',\s*([^;]+)\);'
    match, = re.findall(expression, source)
    equal(re.findall(r'"([^"]+)"', match), features, f"unexpected feature guard {module}")


def main():
    meta = json.loads(run(["cargo", "metadata", "--locked", "--format-version", "1",
                           "--features", "platform-sha2", "--filter-platform", TARGET],
                          ROOT / "rust", capture_output=True).stdout)
    root, = (node for node in meta["resolve"]["nodes"] if node["id"] == meta["resolve"]["root"])
    dep, = (dep for dep in root["deps"] if dep["name"] == "sha2_platform")
    pkg, = (pkg for pkg in meta["packages"] if pkg["id"] == dep["pkg"])
    manifest = Path(pkg["manifest_path"])
    detector((manifest.parent / "src/sha256.rs").read_text(), "shani_cpuid", ["sha", "sse4.1"])
    detector((manifest.parent / "src/sha512.rs").read_text(), "avx2_cpuid", ["avx2"])
    for bits, required in ((256, ["sha", "ssse3", "sse4.1"]), (512, ["avx2"])):
        src = (ROOT / f"rust/src/sha{bits}/stream.rs").read_text()
        detector(src, "hardware_backend", required)
        detector(src, "has_bmi2", ["bmi2"])
        detector(src, "dedicated", ["sha"])

    with tempfile.TemporaryDirectory(prefix="slh-sha-dispatch-") as tmp:
        scratch = Path(tmp)
        bits = (256, 512)
        roots = [f"crate::sha{n}::compress{n}" for n in bits]
        opaque = [f"crate::sha{n}::{path}" for n, path in (
            (256, "x86_sha::compress"), (512, "x86_avx2::compress"), (256, "shani_cpuid::get"),
            (512, "avx2_cpuid::get"), (256, "soft::unroll::compress"), (512, "soft::unroll::compress"))]
        result = extract(scratch, "Rcdispatch", "RcDispatchRust", roots, opaque, manifest=manifest)
        for file in ("Types.lean", "Funs.lean"):
            equal((result / file).read_text(), (LEAN / "Rcdispatch" / file).read_text(), file)

        roots = [f"crate::sha{n}::compress" for n in bits]
        opaque = [f"crate::sha{n}::stream::{f}" for n in bits for f in
                  ("scalar", "has_bmi2::get", "dedicated::get", "hardware_backend::get")]
        opaque += [f"sha2::sha{n}::compress{n}" for n in bits] + ["core::core_arch"]
        run(["lake", "build", "X86remainder.Proof"], LEAN)
        stream_roots = [f"crate::sha{n}::sha{n}_from" for n in bits]
        stream_cuts = [f"crate::sha{n}::stream::{f}" for n in bits for f in
                       ("remainder", "prescheduled", "available::get")]
        stream_cuts += ["crate::sha256::stream::dedicated::get", "core::core_arch"]
        for flag, forced in (("", ()), ("sha2_backend", bits), ("sha2_256_backend", (256,)),
                             ("sha2_512_backend", (512,))):
            for package, ns, rs, cuts in (
                ("X86remainder", "X86RemainderRust", roots, opaque),
                ("X86stream", "X86StreamRust", stream_roots, stream_cuts),
            ):
                result = extract(scratch, package, ns, rs, cuts, f'--cfg {flag}="soft"' if flag else "")
                actual = (result / "Funs.lean").read_text()
                expected = (LEAN / package / "Funs.lean").read_text()
                for n in forced:
                    prefix = f"def sha{n}.stream.FORCE_SOFT : Bool := "
                    expected = expected.replace(prefix + "false", prefix + "true")
                spans = r"(?m)^(\s*Source: .*?)lines \d+:\d+-\d+:\d+"
                equal(re.sub(spans, r"\1lines <span>", actual), re.sub(spans, r"\1lines <span>", expected),
                      f"{package} extraction for {flag}")
                if forced:
                    body = actual.split(f"namespace {ns}\n", 1)[1].rsplit("end " + ns, 1)[0]
                    verification = f"import {package}.Funs\nopen Aeneas Aeneas.Std Result ControlFlow {ns}\nnamespace Fresh\n" + body
                    for n in forced:
                        if package == "X86remainder":
                            claim = f"sha{n}.stream.remainder = StreamScalarRust.sha{n}.stream.scalar"
                            proof = f"funext st blocks\n  simp [sha{n}.stream.remainder, sha{n}.stream.FORCE_SOFT]"
                        else:
                            claim = f"∀ st blocks, sha{n}.stream.prefix st blocks = ok (blocks, st)"
                            proof = f"intro st blocks\n  simp [sha{n}.stream.prefix, sha{n}.stream.FORCE_SOFT]"
                        verification += f"example : {claim} := by\n  {proof}\n"
                    check = scratch / "Forced.lean"
                    check.write_text(verification + "end Fresh\n")
                    run(["lake", "env", "lean", check], LEAN)


if __name__ == "__main__":
    main()
