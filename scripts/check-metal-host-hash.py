#!/usr/bin/env python3
"""Re-extract the Metal crate's CPU hashing, framing and coordinates with the Apple target."""
from pathlib import Path
import re
import os
import runpy
import tempfile

here = Path(__file__).resolve().parent
facade = runpy.run_path(str(here / "check-platform-facade.py"))
root, lean, common = facade["ROOT"], facade["LEAN"], facade["common"]
operations = ("shake_prf_msg","shake_h_msg","with_context","digest_tree","digest_leaf")


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".cargo/bin"), str(Path.home()/".elan/bin"), os.environ["PATH"]])
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        llbc, fresh = tmp / "host.llbc", tmp / "fresh"
        facade["run"]([root / ".tools/aeneas/charon/bin/charon","cargo","--preset=aeneas",
                       *(arg for name in operations for arg in ("--start-from","crate::"+name)),
                       "--opaque","slhdsa::shake256::shake256","--dest-file",llbc,"--",
                       "--locked","--lib","--target","aarch64-apple-darwin"],root / "metal")
        facade["run"]([root / ".tools/aeneas/bin/aeneas","-backend","lean","-abort-on-error",
                       "-no-progress-bar","-split-files","-dest",fresh,llbc],root)
        defs = list(common["declarations"](common["body"](fresh / "Funs.lean","slhdsa_metal")))
        source = (lean / "Metal/HostHashProgram.lean").read_text()
        if len(defs) != len(operations) or any(
            d.replace("slhdsa.shake256.shake256","KappleouterRust.shake256.shake256") not in source for d in defs
        ):
            raise ValueError("Metal host helper differs from the checked extraction")
        # The dependency's Params and its imported Rust functions are nominally
        # shared. Verify the complete field layout and all external signatures.
        checked = common["body"](fresh / "Types.lean","slhdsa_metal")
        actual = common["body"](lean / "Slhdsa/Types.lean")
        structs = list(common["declarations"](checked))
        if len(structs)!=1 or structs[0].removeprefix('@[rust_type "slhdsa::params::Params"]\n').replace("slhdsa.params.Params","params.Params") not in actual:
            raise ValueError("Metal dependency Params layout changed")
        external = (fresh / "FunsExternal_Template.lean").read_text()
        externs = re.findall(r"^axiom (\S+)\s*:\s*([^/]+?)(?=\n\s*/--|\Z)",external,re.M|re.S)
        known = {"slhdsa.util.to_int","slhdsa.shake256.shake256", *(
            "slhdsa.params.Params."+n for n in ("md_bytes","tree_bits","tree_bytes","leaf_bytes"))}
        if {n for n,_ in externs} != known:
            raise ValueError("unreviewed Metal host external")
        proof = "import Metal.HostPreprocess\nopen Aeneas Aeneas.Std Result\n"
        for n,t in externs:
            expr = "KappleouterRust.shake256.shake256" if n=="slhdsa.shake256.shake256" else n
            proof += f"example : {t.strip()} := {expr}\n"
        facade["run"](["lake","build","Metal.HostPreprocess"],lean)
        facade["run"](["lake","env","lean","--stdin"],lean,input=proof,text=True)
    facade["audit_theorems"]("Metal.HostPreprocess",["MetalHostHash."+n for n in
        ("tree_fips","leaf_fips","frame_fips","shake_randomizer","shake_digest","hashRequest_fips","prepare_fips")])
    print("Metal host: matched five Apple Rust helpers and audited both request hash branches.",flush=True)


if __name__ == "__main__":
    main()
