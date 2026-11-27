"""Derive finite typed write receipts for all generated phase-one dispatch jobs."""

import re

from worker_effects import CELL, FUNCTIONS, PREFIX


def dispatch_receipt_witness(generated: str) -> str:
    definitions = [
        fn for fn in FUNCTIONS.findall(generated) if fn[0].startswith("dispatch")
    ]
    refs = re.compile(
        re.escape(PREFIX)
        + "("
        + "|".join(
            re.escape(n) for n, _, _ in sorted(definitions, key=lambda fn: -len(fn[0]))
        )
        + r")(?![\w.])"
    )
    stores = re.compile(
        r"(?m)^([ ]*)let r ← " + re.escape(CELL) + r"\.set (\w+) (\w+)\n"
        r"\1core\.result\.Result\.expect \((Array\.Insts\.CoreFmtDebug N core\.fmt\.DebugU8)\) r\n"
        r'\s+\(toStr ("[^"]+")\)'
    )
    out = [
        """
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std ControlFlow Result Error
open ParallelDispatchWrites ParallelWorkerCounterSafety ParallelWorkerInterleave
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
"""
    ]
    count = 0
    for name, signature, body in definitions:
        params, result = signature.rsplit(" :\n  Result ", 1)
        params = params.replace(CELL, "Physical N")
        args = " ".join(re.findall(r"\((\w+) :", params))
        deps = list(dict.fromkeys(m[1] for m in refs.finditer(body)))
        body, n = stores.subn(r"\1checkedSet \2 \3 (\4) (toStr \5)", body)
        count += n
        if CELL + ".set" in body or CELL + ".get" in body:
            raise ValueError(f"unexpected shared operation in {name}")
        body = refs.sub(lambda m: "receipted." + m[1], body).replace(CELL, "Physical N")
        body = body.replace("←\n      if ", "← id <|\n      if ")
        body = re.sub(r"(?m)^  loop$", "  ParallelDispatchWrites.loop", body)
        out.append(
            f"def receipted.{name}\n{params} :\n  RecordedJob N {result}\n  := do\n{body}\n"
        )
        lemma = name.replace(".", "_") + "_live"
        simp = ", ".join(
            [
                "live_bind",
                "live_lift",
                "live_checkedSet",
                "raw_bind",
                "raw_lift",
                "raw_record_loop",
                "raw_cert_loop",
                "bind_assoc",
            ]
            + [n.replace(".", "_") + "_live" for n in deps]
        )
        proof = f"  unfold receipted.{name} interpreted.{name}\n"
        if name == "dispatch":
            proof += "  cases h : item.kind <;> simp only [h]\n"
        proof += f"  all_goals simp only [{simp}]\n  all_goals first | rfl | (congr 1; funext p; rcases p with ⟨o, iter⟩; cases o <;> simp only [{simp}] <;> rfl)\n"
        out.append(
            f"theorem {lemma}\n{params} :\n    (receipted.{name} {args}).live.raw =\n"
            f"    (interpreted.{name} (certifiedOps N) {args}).raw := by\n{proof}"
        )
        if name == "dispatch":
            out.append(f"""
theorem dispatch_published
{params} (fuel : Nat) (writes : List (Publication N))
    (receipt : (receipted.dispatch {args}).receipt fuel = ok (writes,()))
    {{h peers dest final}} (safe : All peers)
    (run : Steps h ((interpreted.dispatch (certifiedOps N) {args}).raw :: peers) dest (pure () :: final)) :
    ∀ w ∈ writes, dest.cells w.key = some w.value := by
  apply RecordedJob.completed _ fuel writes receipt safe
  rwa [dispatch_live]
""")
    if len(definitions) != 13 or count != 10:
        raise ValueError(
            f"unexpected dispatch receipt coverage: {len(definitions)} functions, {count} stores"
        )
    return "\n".join(out) + "\nend\nend slhdsa.WorkerEffects\n"
