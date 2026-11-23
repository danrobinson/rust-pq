#!/usr/bin/env python3
"""Verify pinned SHAKE256's streaming adapters (requires z3-solver 4.15.4.0)."""
import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile

import z3

locked = runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT = locked["ROOT"]
PROOFS = ROOT / "scripts/peer-xof"
TARGETS = ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu")
FEATURES = ["--no-default-features", "--features", "digest/alloc,digest/block-api,digest/mac,digest/oid"]


def compiled(path, name, target, features):
    subprocess.run(["cargo", "rustc", "--lib", "--locked", "--release", "--target", target,
                    *features, "--", "--emit=llvm-ir"], cwd=path, check=True)
    [file] = list((path / "target" / target / "release").rglob(name+"-*.ll"))
    return file.read_text()


def main():
    if z3.get_version()[:3] != (4,15,4):
        raise RuntimeError("use z3-solver 4.15.4.0")
    os.environ["PATH"] = os.pathsep.join(str(Path.home()/t/"bin") for t in (".elan",".cargo")) + os.pathsep + os.environ["PATH"]
    eager = runpy.run_path(str(PROOFS / "eager.py"))
    reader = runpy.run_path(str(PROOFS / "reader.py"))
    wire = runpy.run_path(str(PROOFS / "wiring.py"))
    with tempfile.TemporaryDirectory(prefix="peer-stream-") as d:
        root = Path(d)
        buffer, sha = root / "buffer", root / "sha"
        buffer.mkdir()
        sha.mkdir()
        locked["unpack"](buffer, "block-buffer", "0.12.1")
        manifest = locked["unpack"](sha, "sha3", "0.11.0")
        locked["common"]["append"](buffer / "src/lib.rs", (PROOFS / "buffer.rs").read_text())
        lib = sha / "src/lib.rs"
        # The new no_mangle marker applies solely to the observed iterator specialization.
        before = lib.read_text()
        if before.count("#![forbid(unsafe_code)]")!=1:
            raise ValueError("unexpected sha3 crate attributes")
        lib.write_text(before.replace("#![forbid(unsafe_code)]","#![deny(unsafe_code)]"))
        locked["common"]["append"](lib, (PROOFS / "roots.rs").read_text())
        for target in TARGETS:
            data = compiled(buffer, "block_buffer", target, [])
            eager["inspect"](data)
            reader["inspect"](data)
            provider = compiled(sha, "sha3", target, FEATURES)
            it = reader["canonical"](provider, "proof_iterate_sha3_blocks", ("%blocks.0","%blocks.1","%process"))
            if it != (PROOFS / "iterate.ll").read_text().strip():
                raise ValueError("unexpected block iterator SSA")
            n,k=z3.Ints("blocks iteration")
            domain={"guard":[n>=0,n<67818912035696881,k>=0,k<n]}
            eager["requires"](domain,z3.And((k+1)*136<=n*136,n*136<=2**63-1,
                         ((k+1)*136==n*136)==(k+1==n),n-(k+1)<n-k),"block iterator bounds/termination")
            file = sha / (target+".llbc")
            subprocess.run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--monomorphize",
                    "--hide-marker-traits", "--hide-allocator", "--reconstruct-asserts", "--reconstruct-matches",
                    "--start-from", "crate::proof_stream_api", *[v for pkg in ("block_buffer","keccak","hybrid_array","core","typenum")
                    for v in ("--opaque",pkg)], "--include","core::option::Option","--include","digest",
                    "--opaque","crate::block_api::xor_block","--dest-file",file,"--","--locked","--manifest-path",manifest,
                    "--target",target,*FEATURES,"--target-dir",sha/"charon-target"], cwd=sha, check=True)
            if wire["wiring"](json.loads(file.read_text())) != (PROOFS / "wiring.mir").read_text():
                raise ValueError("unexpected SHAKE256 receiver, field, closure, iterator or result plumbing")
            print(target+": verified unbounded streaming and concrete provider wiring",flush=True)
        audit=runpy.run_path(str(ROOT/"scripts/check-peer-keccak.py"))["audit"]
        audit(root, ["Peerarmkeccak.Xof"], ["PeerShake.Buffer.providerCorrect","PeerShake.Buffer.completeBlock",
               "PeerShake.Buffer.updateView","PeerShake.Buffer.padView","PeerShake.Buffer.readView"])


if __name__=="__main__":
    main()
