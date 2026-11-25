#!/usr/bin/env python3
"""Check the native Arm XMSS sign, seeded keygen and cache-builder callers."""

import os
from pathlib import Path
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
LEAN = facade["LEAN"]
common = facade["common"]
sets = ["sha2_" + p + s for p in ["128", "192", "256"] for s in ["s", "f"]]
APIS = ["slh_keygen_internal", "keygen"]


def inspect(target, temp):
    cache_check = runpy.run_path(str(HERE / "check-cache-construction.py"))
    roots = [
        "crate::xmss::xmss_sign",
        "crate::slh::slh_keygen_internal",
        cache_check["builders"][0],
    ]
    roots.extend("crate::sets::" + s + "::" + api for s in sets for api in APIS)
    cuts = [
        "crate::xmss::xmss_node",
        "crate::wots::wots_sign",
        "crate::util::block",
        *cache_check["builder_cuts"],
    ]
    package = facade["extract"]("rust", target, "UpperArm", temp, roots, cuts)

    def declarations(path):
        return list(common["declarations"](common["body"](path)))

    port = declarations(LEAN / "Slhdsa/Funs.lean") + declarations(
        LEAN / "Cachepath/BuilderProgram.lean"
    )
    program = [
        (LEAN / "Armwide" / (name + ".lean")).read_text()
        for name in ["XmssSigner", "XmssKeygen", "XmssCacheBuilder"]
    ]
    selected = {0: set(), 1: set(), 2: set()}
    typed = set()
    for decl in declarations(package / "Funs.lean"):
        name = decl.split("def ", 1)[1].split()[0] if "def " in decl else ""
        owner = None
        if name.startswith("xmss.xmss_sign"):
            owner = 0
        elif name == "slh.slh_keygen_internal":
            owner = 1
        elif name in {
            "cache.sha2_ops.build_xmss_tree",
            "cache.sha2_ops.build_xmss_tree_loop0.body",
            "cache.sha2_ops.build_xmss_tree_loop0",
        }:
            owner = 2
        if owner is not None:
            if decl not in program[owner]:
                raise ValueError(
                    f"{target}: {name} differs from its verified native caller"
                )
            selected[owner].add(name)
        elif decl not in port:
            raise ValueError(
                f"{target}: unrecognized extracted dependency {name}: {decl[:160]}"
            )
        if any(name == f"sets.{s}.{api}" for s in sets for api in APIS):
            typed.add(name)
    if list(map(len, selected.values())) != [3, 1, 3] or len(typed) != len(sets) * len(
        APIS
    ):
        raise ValueError(f"{target}: missing Arm caller specialization")
    if set(declarations(package / "Types.lean")) - set(
        declarations(LEAN / "Slhdsa/Types.lean")
    ):
        raise ValueError(f"{target}: native Arm caller types changed")
    print(
        f"{target}: XMSS signing, keygen, serial cache builder and twelve typed keygen entries match",
        flush=True,
    )


def inspect_parallel(target, directory):
    directory.mkdir()
    construction = runpy.run_path(str(HERE / "check-cache-construction.py"))
    tickets = runpy.run_path(str(HERE / "check-parallel-leaf-fill.py"))
    construction["check_parallel"](target, directory)
    tickets["check"](target, directory)
    # The second instantiation reuses the four same extracted declarations in a
    # namespace where the WOTS call is bound to the native public dispatcher.
    native = (LEAN / "Armwide/XmssParallelBuilder.lean").read_text()
    program = (LEAN / "Cachepath/ParallelFillProgram.lean").read_text()
    worker = program[
        program.index("@[rust_loop_body]") : program.index("def shakeBatch")
    ].strip()
    program = (LEAN / "Cachepath/BuilderParallelProgram.lean").read_text()
    tree = program[
        program.index("def sha2Tree\n") : program.index(
            "/-- Parallel-feature root of the shake builder"
        )
    ].strip()
    if worker not in native or tree not in native:
        raise ValueError(
            f"{target}: native parallel SHA-2 leaf builder or per-ticket program differs"
        )


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo/bin"),
            str(Path.home() / ".elan/bin"),
            os.environ["PATH"],
        ]
    )
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"][:2]:
            inspect(target, Path(tmp))
            inspect_parallel(target, Path(tmp) / target)
    facade["run"](
        [
            "lake",
            "build",
            "Armwide.XmssSigner",
            "Armwide.XmssKeygenSets",
            "Armwide.XmssParallelBuilder",
        ],
        LEAN,
    )
    for module, namespace, names in [
        ("XmssSigner", "Signer", ["xmss_sign_spec", "sign_eq_scalar"]),
        ("XmssKeygen", "Generate", ["keygen_eq_scalar", "keygen_fips"]),
        (
            "XmssParallelBuilder",
            "Generate",
            ["parallel_builder_eq", "parallel_tree_kernel", "parallel_cached_keys"],
        ),
        (
            "XmssCacheBuilder",
            "Generate",
            ["cache_builder_eq", "tree_kernel", "cached_keys"],
        ),
    ]:
        facade["audit_theorems"](
            "Armwide." + module,
            ["slhdsa.Armwide.XmssLeaves." + namespace + "." + n for n in names],
        )
    facade["audit_theorems"](
        "Armwide.XmssKeygenSets",
        [
            f"ArmWideKeygen{cpu}.slhdsa.{s}.{api}_spec"
            for cpu in [256, 512]
            for s in sets
            for api in APIS
        ],
    )


if __name__ == "__main__":
    main()
