#!/usr/bin/env python3
"""Extract the pinned RustCrypto SHAKE recipes and check their FIPS 205 refinements."""
from collections import Counter
from pathlib import Path
import os
import re
import runpy
import shutil
import subprocess
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-peer-digest.py")))
ROOT = common["ROOT"]
source = ROOT / "scripts/peer-shake"
lower = runpy.run_path(str(source / "lower.py"))
SHAPES = {"128s":(16,14,30), "128f":(16,33,34), "192s":(24,17,39),
          "192f":(24,33,42), "256s":(32,22,47), "256f":(32,35,49)}
PARAMS = {"new_from_pk_seed": "(pk_seed : Bytes)",
          "prf_sk": "(cached : S) (adrs sk_seed : Bytes)",
          "f": "(cached : S) (adrs m : Bytes)",
          "h": "(cached : S) (adrs m1 m2 : Bytes)",
          "t": "(cached : S) (adrs : Bytes) (m : List Bytes)",
          "prf_msg": "(sk_prf opt_rand : Bytes) (msg : List (List Bytes))",
          "h_msg": "(rand pk_seed pk_root : Bytes) (msg : List (List Bytes))"}


def program(cases):
    result = """import Spec.SlhDsa
open Spec (Bytes)
namespace PeerShake

/-- SHAKE256 streaming operations cut at the RustCrypto digest provider. -/
structure Xof (S : Type) where
  empty : S
  update : S → Bytes → S
  finish : S → Nat → Bytes

variable {S : Type} (x : Xof S)
"""
    for op, binders in PARAMS.items():
        state, role = cases[op]
        if role is None:
            result += f"\ndef {op} {binders} : S :=\n  {state}\n"
        else:
            result += f"\ndef {op} ({role} : Nat) {binders} : Bytes :=\n  x.finish {state} {role}\n"
    return result + "\nend PeerShake\n"


def extract(p, peer, deps):
    import json
    common["unpack_peer"](peer, p, deps[peer["name"], peer["version"], peer["source"]])
    manifest = p / "Cargo.toml"
    manifest.write_text(re.sub(r"(?ms)^\[dev-dependencies\.[^\]]+\]\n.*?(?=^\[|\Z)", "", manifest.read_text()))
    shutil.copy2(ROOT / "bench/Cargo.lock", p / "Cargo.lock")
    subprocess.run(["cargo", "metadata", "--offline", "--format-version", "1"],
                   cwd=p, stdout=subprocess.DEVNULL, check=True)
    normal = common["metadata"](manifest)
    ids = {n["id"]: n for n in normal["resolve"]["nodes"]}
    packages = {v["id"]: v for v in normal["packages"]}
    current = common["registry_checksums"](p / "Cargo.lock")
    seen = set()
    pending = [normal["resolve"]["root"]]
    while pending:
        i = pending.pop()
        if i in seen:
            continue
        seen.add(i)
        v = packages[i]
        if v["source"]:
            k = v["name"], v["version"], v["source"]
            if deps.get(k) != current[k]:
                raise ValueError(f"dependency outside benchmark lock: {k}")
        pending.extend(d["pkg"] for d in ids[i]["deps"] if any(m["kind"]!="dev" for m in d["dep_kinds"]))
    recipe = {}
    for shape,(n,k,m) in SHAPES.items():
        entry = "peer_shake_"+shape
        root = (source / "roots.rs").read_text().replace("ROOT",entry).replace("PEER_TYPE","Shake"+shape)
        root = root.replace("PARAM_N",str(n)).replace("PARAM_LEN",str(2*n+3)).replace("PARAM_K",str(k))
        common["append"](p / "src/lib.rs", root)
        file = p / (shape+".llbc")
        subprocess.run([ROOT/".tools/aeneas/charon/bin/charon","cargo","--monomorphize","--hide-marker-traits",
                        "--hide-allocator","--reconstruct-asserts","--reconstruct-matches","--start-from","crate::"+entry,
                        *[v for name in ("sha3","digest","hybrid_array","typenum","zerocopy","core") for v in ("--opaque",name)],
                        "--dest-file",file,"--","--locked","--manifest-path",manifest,"--target-dir",p/"target"],
                       cwd=p, check=True)
        ir = lower["Lower"](json.loads(file.read_text()))
        counts = Counter()
        for f in ir.fns:
            if not f:
                continue
            name = lower["path"](f)
            op = name.rsplit(".",1)[-1]
            if name != "slh_dsa.hashes.shake."+op or op not in PARAMS:
                continue
            expr, size = lower["extracted"](ir,f)
            expected = None if op == "new_from_pk_seed" else (m if op == "h_msg" else n)
            if size != expected:
                raise ValueError(f"{shape} {op} produced {size} bytes rather than {expected}")
            role = None if size is None else ("mbytes" if op == "h_msg" else "n")
            code = expr, role
            if op in recipe and recipe[op] != code:
                raise ValueError(f"disagreeing monomorphizations for {op}")
            recipe[op] = code
            counts[op] += 1
        if counts != {"new_from_pk_seed": 1, "prf_msg": 1, "h_msg": 1, "prf_sk":2,"t":2,"h":2,"f":2}:
            raise ValueError(f"unexpected {shape} peer call graph: {counts}")
        print(f"{shape}: verified eleven concrete RustCrypto SHAKE method bodies", flush=True)
    return program(recipe)


def main():
    os.environ["PATH"] = os.pathsep.join(str(Path.home()/tool/"bin") for tool in (".elan",".cargo"))+os.pathsep+os.environ["PATH"]
    graph = common["metadata"](ROOT/"bench/Cargo.toml")
    peer, = [p for p in graph["packages"] if p["name"]=="slh-dsa" and p["version"]=="0.2.0-rc.5"]
    with tempfile.TemporaryDirectory(prefix="peer-hash-shake-") as d:
        content = extract(Path(d),peer,common["registry_checksums"](ROOT/"bench/Cargo.lock"))
    lean = ROOT/"lean-hw"
    if (lean/"Shakebatch/PeerHashProgram.lean").read_text() != content:
        raise ValueError("fresh RustCrypto SHAKE MIR differs from the verified Lean program")
    subprocess.run(["lake","build","Shakebatch.PeerHashProof"],cwd=lean,check=True)
    with tempfile.TemporaryDirectory(prefix="peer-shake-axioms-") as d:
        check = Path(d) / "Check.lean"
        names = ("seeded","prf_fips","f_fips","h_fips","t_fips","prf_msg_fips","h_msg_fips")
        check.write_text("import Shakebatch.PeerHashProof\n" + "".join(f"#print axioms PeerShake.{n}\n" for n in names))
        output = subprocess.check_output(["lake","env","lean",check],cwd=lean,text=True)
        for name in names:
            line, = [line for line in output.splitlines() if f"'PeerShake.{name}'" in line]
            if "does not depend on any axioms" in line:
                continue
            match = re.search(r"depends on axioms: \[(.*?)\]", line)
            if not match or set(match[1].split(", ")) - {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError(line)


if __name__=="__main__":
    main()
