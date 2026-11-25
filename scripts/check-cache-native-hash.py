#!/usr/bin/env python3
"""Replay hosted cache sponges, the Apple sequential permutation and the combined round trips."""
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
common = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
LEAN = common["LEAN"]
parse = common["generated_declarations"]
extract = common["extract_target"]


def same(package, reference, namespace, file):
    actual = parse(package / file, "CacheopsRust")
    expected = parse(LEAN / reference / file, namespace)
    differences = sorted(n for n in actual.keys() | expected.keys() if actual.get(n) != expected.get(n))
    if differences:
        raise ValueError(f"{reference}/{file} differs in {differences}")


def check_apple_single(package):
    """Match both entry points, each loop, all closure definitions, the detector and round constants."""
    text = (LEAN / "Cachepath/NativeAppleSingle.lean").read_text()
    wrappers = {}
    for found in re.finditer(r"^def (sha3Single|single)\b[\s\S]+?(?=\n\n)", text, re.M):
        wrappers[found[1]] = " ".join(found[0].split())
    for file in ("Types.lean", "Funs.lean"):
        emitted = parse(package / file, "CacheopsRust", strict=True)
        bulk = parse(LEAN / "Kapplebulk" / file, "KapplebulkRust")
        for n, body in emitted.items():
            changed = body.replace("shake256.parallel.sha3.single_loop0", "shake256.parallel.sha3.blocks_loop0_loop0")
            changed = changed.replace("shake256.parallel.sha3.single_loop1", "shake256.parallel.sha3.blocks_loop1")
            changed = changed.replace("shake256.parallel.sha3.single.closure", "shake256.parallel.sha3.blocks.closure")
            if n in ("shake256.parallel.single", "shake256.parallel.sha3.single"):
                short = "single" if n == "shake256.parallel.single" else "sha3Single"
                changed = changed.replace("shake256.parallel.sha3.single", "sha3Single")
                changed = changed.replace("shake256.parallel.single", "single").replace("Std.U64", "U64")
                if changed != wrappers[short]:
                    raise ValueError(f"Apple singleton entry {n} changed")
            else:
                new = re.search(r"\bdef ([\w.]+)", changed)[1]
                if bulk.get(new) != changed:
                    raise ValueError(f"Apple singleton dependency {n} diverged from the checked {new}")
    print("Apple sequential single, detector, broadcast, 24 SHA3 rounds and lane-zero stores matched", flush=True)


def source():
    arm = "aarch64-unknown-linux-gnu"
    apple = "aarch64-apple-darwin"
    x86 = "x86_64-unknown-linux-gnu"
    shake = "crate::shake256::"
    parallel = shake + "parallel::"
    with tempfile.TemporaryDirectory(prefix="hosted-cache-sponge-") as directory:
        work = Path(directory)
        single = extract(apple, work / "single", (parallel + "single",), (parallel + "sha3::round",))
        check_apple_single(single)
        for target, pkg, ns, root, cuts in (
            (apple, "Kappleouter", "KappleouterRust", "shake256", (parallel+"single",parallel+"blocks")),
            (apple, "Kapplebulk", "KapplebulkRust", "parallel::blocks", (parallel+"sha3::round",)),
            (apple, "Ksha3", "Ksha3Rust", "parallel::sha3::round", ()),
            (arm, "Kspongel", "KspongeLRust", "shake256", (shake+"oriented::blocks",shake+"oriented::permute")),
            (arm, "Koriented", "KorientedRust", "oriented::permute", ()),
            (arm, "Kbulk", "KbulkRust", "oriented::blocks", (shake+"oriented::round",)),
            (x86, "Kxouter", "KxouterRust", "shake256", (shake+"round",shake+"stream_x86::blocks","crate::sha256::x86::avx512_available")),
        ):
            fresh = extract(target, work / pkg, (shake + root,), cuts)
            for file in ("Types.lean", "Funs.lean"):
                same(fresh, pkg, ns, file)
            print(f"{target}: matched {pkg}", flush=True)


def main():
    source()
    common["facade"]["run"](["lake", "build", "Cachepath.NativeHashReplay"], LEAN)
    roots = [f"Hosted{host}Session.CacheopsRust.NativeSession.{name}" for host, names in (
        ("Apple", ("appleFull", "apple_reuse")), ("Linux", ("linuxArmFull", "linuxArm_reuse")),
        ("X86", ("linuxX86Full", "linuxX86_reuse")),
    ) for name in names]
    common["facade"]["audit_theorems"]("Cachepath.NativeHashReplay",
                                      ["CacheopsRust.NativeAppleSingle.single_fips", *roots])


if __name__ == "__main__":
    main()
