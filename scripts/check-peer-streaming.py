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
TARGETS = ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu",
           "powerpc64-unknown-linux-gnu", "i686-unknown-linux-gnu", "wasm32-unknown-unknown",
           "x86_64-unknown-none")
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
    parts = runpy.run_path(str(PROOFS / "parts.py"))
    words = runpy.run_path(str(PROOFS / "words.py"))
    cert = runpy.run_path(str(PROOFS / "certificates.py"))["Certificates"]()
    with tempfile.TemporaryDirectory(prefix="peer-stream-") as d:
        root = Path(d)
        buffer, sha, peer = root / "buffer", root / "sha", root / "peer"
        buffer.mkdir()
        sha.mkdir()
        peer.mkdir()
        word_core=root/"word-core"
        word_core.mkdir()
        words["prepare"](word_core, locked)
        locked["unpack"](peer, "slh-dsa", "0.2.0-rc.5")
        parts["append_roots"](peer / "src/lib.rs", locked["common"]["append"])
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
            wasm = target.startswith("wasm32")
            bits = 32 if wasm or target.startswith("i686") else 64
            max_bytes = 2**(bits-1)-1
            words["inspect"](compiled(word_core, "sha3", target, FEATURES), bits)
            parts["inspect"](compiled(peer, "slh_dsa", target, []), bits, wasm)
            data = compiled(buffer, "block_buffer", target, [])
            eager["inspect"](data, cert.record, bits)
            reader["inspect"](data, cert.record, bits)
            provider = compiled(sha, "sha3", target, FEATURES)
            it = reader["canonical"](provider, "proof_iterate_sha3_blocks", ("%blocks.0","%blocks.1","%process"))
            expected = (PROOFS / ("iterate-wasm.ll" if wasm else "iterate.ll")).read_text().strip()
            if it != expected.replace("i64",f"i{bits}"):
                raise ValueError("unexpected block iterator SSA")
            n,k=z3.Ints("blocks iteration")
            domain={"guard":[n>=0,n<=max_bytes//136,k>=0,k<n]}
            cert.record(domain,z3.And((k+1)*136<=n*136,n*136<=max_bytes,
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
        obligations, names = cert.program()
        if obligations != (ROOT / "lean-hw/Peerarmkeccak/BufferVcs.lean").read_text():
            raise ValueError("fresh LLVM verification obligations differ from checked Lean declarations")
        audit(root, ["Peerarmkeccak.Provider","Peerarmkeccak.BufferVcs","Peerarmkeccak.IteratorProof","Peerarmkeccak.WordBytes"], [*names,"PeerShake.Backend.correct","PeerShake.Backend.provider_eq","PeerShake.Buffer.providerCorrect","PeerShake.Buffer.completeBlock",
               "PeerShake.Buffer.updateView","PeerShake.Buffer.padView","PeerShake.Buffer.readView",
               "PeerShake.Buffer.descriptorStep","PeerShake.Buffer.foldParts","PeerShake.Buffer.descriptorStep32",
               "PeerShake.Buffer.descriptorMask","PeerShake.Buffer.blockMask","PeerShake.Buffer.descriptorFour",
               "PeerShake.Buffer.descriptorTail","PeerShake.Buffer.blockEight","PeerShake.Buffer.blockPrefix","PeerShake.WordBytes.xor_byte","PeerShake.WordBytes.swap_byte"])


if __name__=="__main__":
    main()
