#!/usr/bin/env python3
"""Compare the full SDK outputs of the portable and three accelerated builds."""
from itertools import combinations
from pathlib import Path
import runpy
import subprocess

api = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))


def x86_entry(s, op):
    if op in ("public_key", "keygen"):
        return f"X86KeyRust.sets.{s}.{op}", f"slhdsa.X86.Key.{s}.{op}_fips"
    owner = "X86Public" if op in api["CONTEXT"] else "X86Internal"
    return f"{owner}.slhdsa.sets.{s}.{op}", f"{owner}.slhdsa.{s}.{op}_spec"


def entry(s, op, target):
    if s.startswith("shake_"):
        owner = {"x86": "NativeShakeX86", "apple": "NativeShakeApple",
                 "linux": "NativeShakeLinux", "portable": "PortableShakeSDK"}[target]
        prefix = "" if op == "public_key" else owner + "."
        return f"{prefix}slhdsa.sets.{s}.{op}", f"{owner}.slhdsa.{s}.{op}_spec"
    if target == "x86":
        return x86_entry(s, op)
    if target == "portable":
        owner = "" if op == "public_key" else "PortableAPI."
        return f"{owner}slhdsa.sets.{s}.{op}", f"PortableAPI.slhdsa.{s}.{op}_spec"
    return api["arm_entry"](s, op, target)


def main():
    modules = ["PeerEquality.Outputs", "X86key.Sets", "X86platform.Public",
               "Armplatform.Keygen", "Armplatform.LinuxInternal", "Armplatform.LinuxContext", "Portableplatform.Public",
               *(f"Shakebatch.{platform}Api" for platform in ("Apple", "Linux", "X86", "Portable"))]
    api["run"](["lake", "build", *modules], api["LEAN"])
    source = [*(f"import {module}" for module in modules), "open Aeneas Aeneas.Std Result slhdsa",
              "set_option maxRecDepth 65536", "set_option maxHeartbeats 0"]
    names = []
    sets = list(api["SETS"]) + [s.replace("sha2_", "shake_") for s in api["SETS"]]
    for s in sets:
        for op in api["OPERATIONS"]:
            for lhs, rhs in combinations(("x86", "apple", "linux", "portable"), 2):
                name = f"CrossTarget.{s}.{op}_{lhs}_{rhs}"
                names.append(name)
                source.append(api["agreement"](s, op, name, *entry(s, op, lhs), *entry(s, op, rhs)))
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=api["LEAN"],
                            input="\n".join(source), text=True, stdout=subprocess.PIPE)
    if result.returncode:
        raise SystemExit(result.stdout)
    lines = set(result.stdout.splitlines())
    for name in names:
        if f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in lines:
            raise SystemExit(f"Missing or unexpected axiom audit for {name}")
    print(f"Kernel checked {len(names)} cross-target output equalities")


if __name__ == "__main__":
    main()
