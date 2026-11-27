#!/usr/bin/env python3
"""Re-extract the SHA-2 and SHAKE worker dispatch inside Algorithm 19."""
from pathlib import Path
import re
import runpy
import tempfile

here = Path(__file__).resolve().parent
cache = runpy.run_path(str(here / "check-cache-endtoend.py"))
arm = cache["facade"]["common"]
ops = ("slh::parallel::sign","hash::seed_ctx","hash::h_msg","hash::prf_msg","fors::fors_sign",
       "fors::fors_pk_from_sig","ht::ht_sign","slh::digest_tree","slh::digest_leaf")
hosts = ("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu")


def check(target, scratch):
    owners = ("crate::","crate::shake::")
    package = cache["extract_target"](target,scratch,[f+"slh::slh_sign_internal" for f in owners]+["crate::shake::slh::shake_sign_ctx"],
        [f+k for f in owners for k in ops]+["crate::util::block","crate::params::Params::md_bytes","crate::shake::hash::prf_msg_ctx","crate::shake::hash::h_msg_ctx"],features="parallel")
    body = arm["body"](package/"Funs.lean","CacheopsRust")
    shared = set(arm["declarations"](arm["body"](arm["LEAN"]/"Slhdsa/Funs.lean")))
    aliases = []
    program = ["import Parallel.SegmentedCaller","import Armplatform.Replay","open Aeneas Aeneas.Std Result",
               "open slhdsa slhdsa.ParallelCaller","set_option linter.concreteInstances false",
               "set_option maxHeartbeats 0","noncomputable section","namespace FreshUncached",
               "variable [fb : Sh.Fallback] [wf : Worker ShakeSeed] [ws : Worker hash.Seed]",
               "variable [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features]"]
    expected = {f.replace("::",".")[len("crate."):] + k.replace("::",".") for f in owners for k in ops}|{"util.block","shake.hash.prf_msg_ctx","shake.hash.h_msg_ctx"}
    actual = set()
    for path in package.glob("*External_Template.lean"):
        text = path.read_text()
        for decl in arm["declarations"](text[text.index("/-- "):]):
            m = re.fullmatch(r"axiom\s+(\S+)\s*(.*)",decl,re.S)
            if not m or m[1] not in expected:
                raise ValueError(f"unexpected Algorithm 19 cutpoint: {decl[:160]}")
            name,signature=m.groups()
            actual.add(name)
            n = " N" if re.match(r"[{(]N",signature) else ""
            if name in ("slh.parallel.sign","shake.slh.parallel.sign"):
                impl=("@ws.run" if name.startswith("slh.") else "@wf.run")+n
            elif name in ("shake.fors.fors_sign","shake.fors.fors_pk_from_sig","shake.ht.ht_sign"):
                impl="@fb."+{"shake.fors.fors_sign":"forsSign","shake.fors.fors_pk_from_sig":"forsRecover","shake.ht.ht_sign":"htSign"}[name]+n
            elif name in ("ht.ht_sign","fors.fors_sign","fors.fors_pk_from_sig"):
                impl="@slhdsa.NativeArmSignature."+name+" cpu features"+n
            elif name in ("hash.prf_msg","hash.h_msg"):
                impl="@slhdsa.NativeArmSignature."+name+n
            elif name in ("shake.hash.prf_msg_ctx","shake.hash.h_msg_ctx"):
                impl="@ShakeoptSeg."+name+n
            else:
                impl="@slhdsa."+name+n
            aliases.append(f"abbrev {name} {signature} := {impl}")
    if actual!=expected:
        raise ValueError(f"lost worker or primitive boundary: {expected-actual}")
    types = set(arm["declarations"](arm["body"](arm["LEAN"]/"Slhdsa/Types.lean")))
    if set(arm["declarations"](arm["body"](package/"Types.lean","CacheopsRust")))-types:
        raise ValueError(f"unexpected nominal types on {target}")
    program+=aliases
    entries={"shake.slh.slh_sign_internal":"Sh","slh.slh_sign_internal":"S2","shake.slh.shake_sign_ctx":"Sh"}
    found=set()
    for d in arm["declarations"](body):
        name=re.search(r"\bdef\s+([^\s:]+)",d)[1]
        if name in entries:
            program.append(d)
            found.add(name)
        elif d not in shared:
            raise ValueError(f"new dependency in parallel signing: {name}")
    if found!=set(entries): raise ValueError("missing Algorithm 19 entry")
    program.append("end FreshUncached")
    for name,owner in entries.items():
        ref=f"slhdsa.ParallelCaller.{owner}"
        theorem="sign_ctx_spec" if name.endswith("shake_sign_ctx") else "sign_spec"
        program.append(f"run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry "
                       f"`{ref}.{theorem} `{ref}.{name} `FreshUncached.{name} `FreshUncached.{name}_fips")
    source=scratch/"Caller.lean"
    source.write_text("\n".join(program)+"\n")
    arm["run"](["lake","env","lean",source],arm["LEAN"])
    print(f"{target}: attached conditional FIPS proofs to both parallel Algorithm 19 callers and segmented SHAKE signing",flush=True)


def main():
    arm["run"](["lake","build","Parallel.SegmentedCaller"],arm["LEAN"])
    for target in hosts:
        with tempfile.TemporaryDirectory() as temp:
            check(target,Path(temp))


if __name__=="__main__":
    main()
