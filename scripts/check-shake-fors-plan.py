#!/usr/bin/env python3
"""Replay native FORS output stores using arbitrary selection variables and Lean certificates."""

from pathlib import Path
import os
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
function = runpy.run_path(str(HERE / "parallel-proof/build.py"))["function"]
source = ROOT / "rust/src/shake/fors_batch.rs"
lean = ROOT / "lean-hw"


def transcript(folder, width, original):
    sign = "\n".join(
        function(original, op)
        for op in ("batch_leaves_slice", "batch_pairs_slice", "sign")
    ).replace("pub(super) fn", "fn")
    for before, after in (
        ("u8", "usize"),
        ("&[u32]", "&[Expr]"),
        ("[u32; WIDTH]", "[Expr; WIDTH]"),
        ("[0u32;", "[Expr(0);"),
    ):
        sign = sign.replace(before, after)
    harness = (HERE / "shake-fors/sign-plan.rs").read_text()
    harness = harness.replace("PROOF_WIDTH", str(width)).replace(
        "PARAMS_PATH", str(ROOT / "rust/src/params.rs")
    )
    path = folder / "plan.rs"
    path.write_text(harness.replace("// PRODUCTION_SIGN", sign))
    exe = folder / "plan"
    subprocess.run(
        ["rustc", "--edition=2021", "-O", "-C", "overflow-checks=yes", path, "-o", exe],
        check=True,
    )
    return subprocess.check_output([exe], text=True)


def certificate(data, width):
    src = [
        "import Shakeopt.ForsPlan",
        "open Spec Shakeopt.ForsPlan",
        "open Shakeopt.ForsPlan.Op",
        "set_option maxRecDepth 64000",
        "set_option maxHeartbeats 0",
    ]
    fields = {}
    checks = set()
    intermediates = {}
    for line in data.splitlines():
        kind, value = line.split(" ", 1)
        if kind == "set":
            name = value
            fields[name] = []
            intermediates[name] = set()
        elif kind == "block":
            op, index = value.split(") ", 1)
            fields[name].append(f"{op}),{index}")
        elif kind == "child":
            # The production small-tree passes use the same symbolic sibling for
            # a parent and its children. Generalize just that identical subterm.
            sibling = r"\(\.xor \(\.shr \(\.add \(\.lit \d+\) \(\.sel \d+\)\) \d+\) 1\)"
            matches = re.findall(sibling, value)
            if len(matches) != 2 or matches[0] != matches[1]:
                raise ValueError(f"mismatched parent/child variables: {line}")
            abstract = value.replace(matches[0], "base")
            m = re.fullmatch(
                r"(.+) (base|\(\.add \(\.mul \d+ base\) \(\.lit \d+\)\)|\(\.mul \d+ base\)) ([01])",
                abstract,
            )
            if not m:
                raise ValueError(f"unknown child geometry: {line}")
            x, y, side = m.groups()
            intermediates[name].update(
                expr.replace("base", matches[0]) for expr in (x, y)
            )
            checks.add(
                f"example (base : Index) (pick : Nat → Nat) : Index.eval pick {x} = 2*Index.eval pick {y}+{side} := by simp [Index.eval] <;> omega"
            )
        else:
            raise ValueError(line)
    if set(fields) != {f"{b}{s}" for b in [128, 192, 256] for s in "sf"}:
        raise ValueError("incomplete parameter family")
    src.extend(sorted(checks))
    for name, rows in fields.items():
        plan = ",\n".join(f"({row})" for row in rows)
        children = ",\n".join(sorted(intermediates[name]))
        src.extend(
            [
                f"def plan_{name} : List Field := [{plan}]",
                f"example : (plan_{name}.map Prod.snd ++ ([{children}] : List Index)).all (fun x => (x.bound (2^shake_{name}.a-1)).isSome) = true := by decide",
                f"theorem result_{name} (md sk pk : Bytes) (a : Adrs) : render shake_{name} md sk pk a plan_{name} = forsSign shake_{name} md sk pk a := by",
                f"  have same : plan_{name} = canonical shake_{name} {str(width == 3).lower()} := by decide",
                f"  rw [same]; exact render_fips {str(width == 3).lower()} shake_{name} md sk pk a",
                f"#print axioms result_{name}",
            ]
        )
    return "\n".join(src)


def reject_mutations(folder):
    original = source.read_text()
    mutants = (
        (3, "copy_from_slice(&sec[lane])", "copy_from_slice(&sec[0])"),
        (
            8,
            "left[lane] = children[2 * (i + lane)];",
            "left[lane] = children[2 * (i + lane) + 1];",
        ),
        (8, "4 * sib + c as u32", "4 * sib + (3 - c) as u32"),
        (8, "let sib = (leaf >> j) ^ 1;", "let sib = (leaf >> j) ^ 0;"),
    )
    for width, old, new in mutants:
        if original.count(old) != 1:
            raise ValueError(f"unexpected mutation site {old}")
        code = certificate(transcript(folder, width, original.replace(old, new)), width)
        # One shape suffices to expose each mutation. Keep its entire first theorem.
        code = code.split("def plan_128f :", 1)[0]
        out = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            input=code,
            text=True,
            cwd=lean,
            stdout=subprocess.PIPE,
        )
        if out.returncode == 0 or not any(
            s in out.stdout for s in ("decide", "omega could not prove")
        ):
            raise ValueError(
                f"missing expected failed proof for {new}: {out.stdout[:600]}"
            )
    print(
        "Lean rejected all four changes to lane selection, packed child reads, and sibling indices.",
        flush=True,
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    subprocess.run(["lake", "build", "Shakeopt.ForsPlan"], cwd=lean, check=True)
    with tempfile.TemporaryDirectory() as temp:
        folder = Path(temp)
        for width in (3, 8):
            data = transcript(folder, width, source.read_text())
            code = certificate(data, width)
            out = subprocess.run(
                ["lake", "env", "lean", "--stdin"],
                input=code,
                text=True,
                cwd=lean,
                stdout=subprocess.PIPE,
            )
            if out.returncode:
                raise RuntimeError(out.stdout[:6000])
            roots = re.findall(
                r"^'result_(\w+)' depends on axioms: \[([^\]]*)\]$", out.stdout, re.M
            )
            if len(roots) != 6 or any(
                set(a.split(", ")) - {"propext", "Classical.choice", "Quot.sound"}
                for _, a in roots
            ):
                raise RuntimeError("incomplete or unexpected Lean proof dependencies")
            print(
                f"WIDTH={width}: checked {data.count('block ')} ordered FORS output blocks and {data.count('child ')} child positions with six Lean certificates.",
                flush=True,
            )

        reject_mutations(folder)


if __name__ == "__main__":
    main()
