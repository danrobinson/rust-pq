#!/usr/bin/env python3
"""Bind the production cache's packed WOTS call graph to the verified ShakeBatch program."""
import argparse
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
shared = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
LEAN = shared["LEAN"]
base = "crate::cache::shake_ops::"


def normalize(text):
    return " ".join(text.split())


def renamed(text):
    for source, model in (
        ("cache.shake_ops.simd.wots_pk_from_sig", "shake.batch.recover"),
        ("cache.shake_ops.simd.wots_pk_gen_single", "shake.batch.keygen"),
        ("cache.shake_ops.simd.wots_sign", "shake.batch.sign"),
        ("cache.shake_ops.simd.", "shake.batch."),
        ("cache.shake_ops.start", "shake.hash.start"),
        ("cache.shake_ops.digest", "shake.hash.digest"),
    ):
        text = text.replace(source, model)
    return text


def model_declarations(width):
    models = {}
    for module in ("Program", "WotsChainProgram", "WotsKeyProgram", "WotsSignProgram", "WotsOrderProgram"):
        text = (LEAN / f"Shakebatch/{module}.lean").read_text()
        for old, new in (
            ("machine.width", f"{width}#usize"), ("machine.permute", "shake256.parallel.permute"),
            ("stream.State", "shake256.Sponge"), ("stream.start", "shake.hash.start"),
            ("stream.absorb", "shake256.Sponge.absorb"), ("stream.digest", "shake.hash.digest"),
        ):
            text = text.replace(old, new)
        for match in re.finditer(r"^def\s+(shake\.batch\.[\w.]+)\b[\s\S]*?(?=\n\s*\n|\nend\b|\Z)", text, re.M):
            models[match[1]] = normalize(match[0])
    text = (LEAN / "Cachepath/WotsRowsProgram.lean").read_text()
    text = text.replace("machine.width", f"{width}#usize").replace("Leaves.gen", "shake.batch.wots_pk_gen_batch")
    text = text.replace("ShakeBatch.shake.batch.pair", "shake.batch.pair")
    text = re.sub(r"(?<![.\w])((?:fill_xmss_leaves|hash_pairs)[.\w]*)", r"shake.batch.\1", text)
    for match in re.finditer(r"^def\s+(shake\.batch\.[\w.]+)\b[\s\S]*?(?=\n\s*\n|\nend\b|\Z)", text, re.M):
        models[match[1]] = normalize(match[0])
    text = (LEAN / "Cachepath/WotsFusedProgram.lean").read_text()
    text = text.replace("machine.width", f"{width}#usize").replace("machine.permute", "shake256.parallel.permute")
    text = text.replace("ShakeBatch.shake.batch.", "shake.batch.").replace("ArrayAdrsW", f"ArrayAdrs{width}")
    # The source closure carries a phantom N. Its specialized Lean call needs this explicit argument.
    text = text.replace(f"ArrayAdrs{width}.call (N:=N)", f"ArrayAdrs{width}.call")
    text = re.sub(r"(?<![.\w])generate(?=[._\s])", "shake.batch.wots_pk_gen_batch", text)
    for match in re.finditer(r"^def\s+(shake\.batch\.[\w.]+)\b[\s\S]*?(?=\n\s*\n|\nend\b|\Z)", text, re.M):
        models[match[1]] = normalize(match[0])
    return models


def check(package, target, width):
    models = model_declarations(width)
    checked = {}
    for name in ("Types.lean", "Funs.lean"):
        for raw in shared["facade"]["common"]["declarations"](
                shared["facade"]["common"]["body"](package / name, "CacheopsRust")):
            header = re.search(r"\bdef\s+(cache\.shake_ops\.simd\.[\w.]+)", raw)
            if not header:
                continue
            key = renamed(header[1])
            body = normalize(renamed(raw[header.start():]).replace("shake256.parallel.WIDTH", f"{width}#usize"))
            if models.get(key) != body:
                raise ValueError(f"{target}: {key} differs from its verified body")
            checked[key] = body
    # Follow definitions from the actual entry points, including closure trait instances.
    names = re.compile(r"[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+")
    seen = set()
    todo = ["shake.batch.sign", "shake.batch.recover", "shake.batch.keygen",
            "shake.batch.fill_xmss_leaves", "shake.batch.hash_pairs"]
    while todo:
        key = todo.pop()
        if key in seen:
            continue
        seen.add(key)
        todo.extend(ref for ref in names.findall(models[key]) if ref.startswith("shake.batch.") and ref not in seen)
    if seen != checked.keys():
        raise ValueError(f"{target}: unexpected WOTS dependency set {seen ^ checked.keys()}")
    # The sorted callers also use the ordinary address setters, serialization and FIPS constants.
    parse = shared["generated_declarations"]
    for file in ("Types.lean", "Funs.lean"):
        produced = parse(package / file, "CacheopsRust")
        verified = parse(LEAN.parent / "lean/Slhdsa" / file, "slhdsa")
        for name, declaration in produced.items():
            if name.startswith(("address.", "params.")) and verified.get(name) != declaration:
                raise ValueError(f"{target}: shared input definition {name} changed")
    constants = shared["generated_declarations"](package / "Funs.lean", "CacheopsRust")
    expected_width = f"def shake256.parallel.WIDTH : Std.Usize := {width}#usize"
    if not constants.get("shake256.parallel.WIDTH", "").endswith(expected_width):
        raise ValueError(f"{target}: missing production SIMD width")
    print(f"{target}: matched {len(seen)} reachable WOTS definitions through the packed permutation call", flush=True)


def extract_and_check(target, width, scratch, crate=None):
    roots = tuple(base + "simd::" + name for name in ("wots_sign", "wots_pk_from_sig", "wots_pk_gen_single",
                                                      "fill_xmss_leaves", "hash_pairs"))
    cuts = tuple(base + name for name in ("start", "digest")) + (
        "crate::util::block", "crate::shake256::{Sponge}::absorb", "crate::shake256::parallel::permute",
    )
    package = shared["extract_target"](target, scratch, roots, cuts, crate=crate)
    check(package, target, width)


def check_permutation(target, scratch):
    """Re-extract the actual enabled Linux kernel, including its native round."""
    x86 = target.startswith("x86")
    unit = "avx512" if x86 else "mixed"
    prefix = "crate::shake256::parallel::"
    kernel = prefix + unit + "::"
    cuts = (kernel + "permute",) + (("crate::sha256::x86::avx512_available",) if x86 else ())
    dispatch = shared["extract_target"](target, scratch / "dispatch", (prefix + "permute",), cuts)
    wrapper = shared["generated_declarations"](dispatch / "Funs.lean", "CacheopsRust", strict=True)
    if x86:
        expected = shared["generated_declarations"](LEAN / "Kxdispatch/Funs.lean", "KxdispatchRust", strict=True)
    else:
        text = (LEAN / "Shakebatch/LinuxDispatch.lean").read_text().split("end KldispRust")[0]
        expected = {m[1]: normalize(m[0]) for m in re.finditer(
            r"^def (shake256\.parallel\.[\w.]+)\b[\s\S]*?(?=\n\s*\n|\Z)", text, re.M)}
    if wrapper != expected:
        raise ValueError(f"{target}: native Keccak dispatcher changed: {wrapper.keys() ^ expected.keys()}")
    for op, package, cuts in (
        ("permute", "Kavxperm" if x86 else "Kmixedperm", (kernel + "round",)),
        ("round", "Kavx" if x86 else "Kmixed", ()),
    ):
        fresh = shared["extract_target"](target, scratch / op, (kernel + op,), cuts)
        for file in ("Types.lean", "Funs.lean"):
            parse = shared["generated_declarations"]
            actual = parse(fresh / file, "CacheopsRust")
            model = parse(LEAN / package / file, package + "Rust")
            if actual != model:
                delta = sorted(k for k in actual.keys() | model.keys() if actual.get(k) != model.get(k))
                raise ValueError(f"{target}: {op} implementation differs in {delta}")
    print(f"{target}: matched the native Keccak dispatcher, 24-round loop and round", flush=True)


def check_stream(target, scratch):
    x86 = target.startswith("x86")
    package, namespace = ("Kxouter", "KxouterRust") if x86 else ("Kspongel", "KspongeLRust")
    cuts = ("crate::shake256::round", "crate::shake256::stream_x86::blocks",
            "crate::sha256::x86::avx512_available") if x86 else (
                "crate::shake256::oriented::blocks", "crate::shake256::oriented::permute")
    fresh = shared["extract_target"](target, scratch, ("crate::shake256::shake256",), cuts)
    for file in ("Types.lean", "Funs.lean"):
        parse = shared["generated_declarations"]
        if parse(fresh / file, "CacheopsRust") != parse(LEAN / package / file, namespace):
            raise ValueError(f"{target}: native incremental sponge changed in {file}")


def check_inputs(target, scratch):
    roots = (base + "start", base + "digest", "crate::util::block", "crate::wots::wots_digits")
    fresh = shared["extract_target"](target, scratch, roots, ("crate::shake256",))
    parse = shared["generated_declarations"]
    for file in ("Types.lean", "Funs.lean"):
        actual = parse(fresh / file, "CacheopsRust", strict=True)
        reference = parse(LEAN.parent / "lean/Slhdsa" / file, "slhdsa")
        for name, declaration in actual.items():
            if reference.get(renamed(name)) != renamed(declaration):
                raise ValueError(f"{target}: unmatched digit decoder, block read or sponge input in {name}")


def mutation_test():
    with tempfile.TemporaryDirectory(prefix="wots-callback-mutant-") as folder:
        scratch = Path(folder)
        crate = shared["copy_rust_crate"](scratch)
        path = crate / "src/cache.rs"
        source = path.read_text()
        for name, original, changed in (
            ("signing digit gather", "chains(seed, addr, ids, &values, [0; WIDTH], ids.map(|i| digits[i]))",
             "chains(seed, addr, ids, &values, [0; WIDTH], ids.map(|_| digits[0]))"),
            ("fused sponge boundary", "if pos == 17 {", "if pos == 16 {"),
        ):
            if source.count(original) != 1:
                raise ValueError(f"missing unique {name} mutation site")
            path.write_text(source.replace(original, changed))
            try:
                extract_and_check("aarch64-apple-darwin", 8, scratch / name.replace(" ", "-"), crate)
            except ValueError as error:
                if "differs from its verified body" not in str(error):
                    raise
            else:
                raise ValueError(f"accepted the incorrect {name}")
            print(f"rejected the mutated production {name}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutation-test", action="store_true")
    args = parser.parse_args()
    if args.mutation_test:
        mutation_test()
        return
    for target, width in (("aarch64-apple-darwin", 8), ("aarch64-unknown-linux-gnu", 3),
                          ("x86_64-unknown-linux-gnu", 8)):
        with tempfile.TemporaryDirectory(prefix="wots-callbacks-") as folder:
            scratch = Path(folder)
            extract_and_check(target, width, scratch / "callbacks")
            check_inputs(target, scratch / "inputs")
            if "linux" in target:
                check_permutation(target, scratch / "kernel")
                check_stream(target, scratch / "stream")
    shared["facade"]["run"](["lake", "build", "Cachepath.WotsPlatforms", "Cachepath.WotsRows", "Cachepath.WotsFused"], LEAN)
    shared["facade"]["audit_theorems"]("Cachepath.WotsFused", [
        "slhdsa.cache.builder.nativeShake.Vector.Fused." + name for name in
        ("absorb_row", "absorb_tip_rows", "finish_rows", "init_pk", "all_chains", "correct")
    ])
    shared["facade"]["audit_theorems"]("Cachepath.WotsFusedPrf", [
        "slhdsa.cache.builder.nativeShake.Vector.Fused." + name for name in
        ("round_spec", "rounds", "packed_layout", "chain_spec", "init_input", "init_prf", "addresses_spec", "inner_spec")
    ])
    shared["facade"]["audit_theorems"]("Cachepath.WotsRows", [
        "slhdsa.cache.builder.nativeShake.Vector." + name for name in ("row_loop", "fill_spec", "parents_spec", "ops")
    ])
    shared["facade"]["audit_theorems"]("Cachepath.WotsPlatforms", [
        "CacheopsRust.WotsCallbacks." + name for name in
        ("linux_native_fields", "x86_native_fields", "single_eq", "map_blocks_panic", "packed_reject", "sign_eq", "recover_eq", "fields", "linux_fields", "x86_fields")
    ])


if __name__ == "__main__":
    main()
