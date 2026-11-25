#!/usr/bin/env python3
"""Check the optimized ARC bridge's normal-return CFG against MetalCompletion."""
from pathlib import Path
import os
import json
import hashlib
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def observations(ir, function):
    body = re.search(rf"^define [^\n]*?@slh_metal_cmd_{function}\([^\n]+\{{\n(.*?)^\}}",
                     ir, re.M | re.S)
    if body is None:
        raise ValueError("missing optimized bridge")
    blocks = {"entry": []}
    block = "entry"
    for raw in body.group(1).splitlines():
        line = raw.split(";", 1)[0].strip()
        if line.endswith(":"):
            block = line[:-1]
            blocks[block] = []
        elif line:
            blocks[block].append(line)
    receiver = {"endEncoding": "encoder", "commit": "cmdBuf",
                "waitUntilCompleted": "cmdBuf", "status": "cmdBuf"}
    paths = []

    def walk(label, previous, visited, registers, facts, events):
        if label in visited:
            raise ValueError("unexpected loop in command completion")
        visited = visited | {label}
        registers = registers.copy()
        events = list(events)
        for line in blocks[label]:
            assigned = re.match(r"(%\d+) = ", line)
            dest = assigned[1] if assigned else None
            send = re.search(r'@"objc_msgSend\$([\w:]+)"\(ptr (?:noundef )?(?:nonnull )?(%\d+|@\S+?),', line)
            if send:
                sel, obj = send.groups()
                if sel in ("encoder", "cmdBuf", "concurrent"):
                    if obj != "%0":
                        raise ValueError("invalid command handle receiver")
                elif sel == "memoryBarrierWithScope:":
                    scope = re.search(r"i64 noundef (\d+)\)", line)
                    if registers.get(obj) != "encoder" or not scope:
                        raise ValueError("invalid buffer barrier receiver or scope")
                    events.append(f"(BarrierEvent.bufferBarrier {scope[1]})")
                elif sel in receiver:
                    if registers.get(obj) != receiver[sel]:
                        raise ValueError(f"invalid receiver for {sel}")
                    events.append(sel)
                elif sel not in ("error", "localizedDescription", "UTF8String"):
                    raise ValueError(f"unknown Objective-C selector {sel}")
                if dest:
                    registers[dest] = sel
            elif " call " in line or line.startswith("call "):
                fn = re.search(r"@([.\w]+)\(", line)
                if not fn or fn[1] not in {"strncpy", "llvm.objc.autoreleasePoolPush",
                        "llvm.objc.autoreleasePoolPop", "llvm.objc.release", "llvm.objc.retain",
                        "llvm.objc.retainAutorelease", "llvm.objc.clang.arc.noop.use"}:
                    raise ValueError(f"unclassified call: {line}")
                if re.search(r"ptr (?:nonnull )?%0\)", line):
                    if fn[1] == "llvm.objc.release":
                        events.append("releaseHandle")
                    elif fn[1] == "llvm.objc.retain":
                        events.append("retainHandle")
            elif dest and " = icmp eq ptr %0, null" in line:
                registers[dest] = "missing"
            elif dest and (cmp := re.search(r"icmp eq i64 (%\d+), (\d+)$", line)):
                if registers.get(cmp[1]) == "status":
                    if cmp[2] != "4":
                        raise ValueError("completed enumerator differs from the SDK")
                    registers[dest] = "completed"
            elif dest and " = phi i32 " in line:
                incoming = dict((pred, val) for val, pred in re.findall(r"\[ (-?\d+|%\d+), %(\d+) \]", line))
                val = incoming[previous]
                registers[dest] = registers[val] if val.startswith("%") else int(val)
            elif line.startswith("br i1 "):
                cond, yes, no = re.fullmatch(r"br i1 (%\d+), label %(\d+), label %(\d+)", line).groups()
                key = registers.get(cond, cond)
                for value, target in ((True, yes), (False, no)):
                    if key not in facts or facts[key] == value:
                        walk(target, label, visited, registers, {**facts, key:value}, events)
                return
            elif line.startswith("br label %"):
                return walk(line.split("%")[1], label, visited, registers, facts, events)
            elif line == "ret void":
                paths.append((not facts["missing"], facts.get("concurrent"), tuple(events), None))
                return
            elif line.startswith("ret i32 "):
                val = line.split()[-1]
                code = registers[val] if val.startswith("%") else int(val)
                paths.append((not facts["missing"], facts.get("completed"), tuple(events), code))
                return
            elif not re.search(r" = (?:icmp |or i1 |select |add |getelementptr |phi ptr )|^store i8 ", line):
                raise ValueError(f"unclassified IR: {line}")
        raise ValueError("unterminated basic block")

    walk("entry", None, set(), {}, {}, [])
    return paths


def certificate(paths, barriers):
    bools = {True:"true", False:"false"}
    rows = []
    for present, status, events, ret in paths:
        flag = "none" if status is None else f"(some {bools[status]})"
        steps = ",".join("." + s for s in events)
        rows.append(f"⟨{bools[present]}, {flag}, [{steps}], ({ret})⟩")
    barrier_rows = []
    for present, concurrent, events, _ in barriers:
        flag = "none" if concurrent is None else f"(some {bools[concurrent]})"
        steps = ",".join(s if s.startswith("(") else "." + s for s in events)
        barrier_rows.append(f"⟨{bools[present]}, {flag}, [{steps}]⟩")
    return """import Metal.BridgeWait
open MetalCompletion.BridgeWait
private def paths : List Path := [ROWS]
example : ∀ p ∈ paths, valid p := by decide
example : ∃ p ∈ paths, p.code = 0 := by decide
private def barriers : List BarrierPath := [BARRIERS]
example : ∀ p ∈ barriers, validBarrier p := by decide
example : ∃ p ∈ barriers, p.concurrent = some true := by decide
""".replace("ROWS", ",\n".join(rows)).replace("BARRIERS", ",\n".join(barrier_rows))


def archive_binding(ir, folder, env):
    """Check the exact optimized IR used for the proofs against Cargo's object."""
    build = subprocess.check_output(["cargo", "build", "--locked", "--release", "--example", "bench_metal",
                                     "--message-format=json"], cwd=ROOT/"metal", env=env, text=True)
    reports = [json.loads(line) for line in build.splitlines()]
    dirs = [Path(report["out_dir"]) for report in reports if report.get("reason") == "build-script-executed"
            and "slhdsa-metal" in report["package_id"]]
    if len(dirs) != 1:
        raise ValueError("ambiguous Cargo Metal bridge archive")
    actual = subprocess.check_output(["ar","-p",dirs[0]/"libmetal_bridge.a","bridge.o"])
    obj = folder / "recompiled.o"
    subprocess.run(["clang","-O2","-c",ir,"-o",obj], check=True)
    if obj.read_bytes() != actual or (dirs[0]/"bridge.o").read_bytes() != actual:
        raise ValueError("checked optimized IR did not reproduce the release bridge object")
    print(f"Cargo release bridge.o matches checked IR output: SHA-256 {hashlib.sha256(actual).hexdigest()}", flush=True)


def main():
    env = os.environ.copy()
    env["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"),str(Path.home()/".cargo/bin"),env["PATH"]])
    lean = ROOT / "lean-hw"
    subprocess.run(["lake","build","Metal.BridgeWait"], cwd=lean, env=env, check=True)
    original = (ROOT / "metal/src/bridge.m").read_text()
    dispatch = runpy.run_path(str(HERE / "metal-proof/bridge_dispatch.py"))["check"]
    caller = (ROOT / "metal/src/gpu.rs").read_text()
    if "assert!(buffers.len() <= 16 && inline_bytes.len() <= 8);" not in caller:
        raise ValueError("review Rust dispatch argument capacities")

    with tempfile.TemporaryDirectory() as tmp:
        ir = Path(tmp, "bridge.ll")
        src = Path(tmp, "checked.m")
        cases = [
            ("production", None, None),
            ("inverted concurrency", "if (obj.concurrent)", "if (!obj.concurrent)"),
            ("wrong barrier scope", "memoryBarrierWithScope:MTLBarrierScopeBuffers", "memoryBarrierWithScope:MTLBarrierScopeTextures"),
            ("wrong inline index", "length:bytes_lens[i] atIndex:bytes_indices[i]", "length:bytes_indices[i] atIndex:bytes_lens[i]"),
            ("swapped grid dimensions", "MTLSizeMake(tg_x, 1, 1)", "MTLSizeMake(grid_x, 1, 1)"),
            ("omitted wait", "[obj.cmdBuf waitUntilCompleted];", ""),
            ("inverted status", "!= MTLCommandBufferStatusCompleted", "== MTLCommandBufferStatusCompleted"),
            ("swapped commit and wait", "[obj.cmdBuf commit];\n        [obj.cmdBuf waitUntilCompleted];",
             "[obj.cmdBuf waitUntilCompleted];\n        [obj.cmdBuf commit];"),
        ]
        for name, before, after in cases:
            source = original
            if before is not None:
                if original.count(before) != 1:
                    raise ValueError(f"ambiguous mutation: {name}")
                source = source.replace(before, after)
            src.write_text(source + '\n_Static_assert(MTLCommandBufferStatusCompleted == 4 && MTLBarrierScopeBuffers == 1, "status and barrier ABI");\n')
            subprocess.run(["clang","-fobjc-arc","-O2","-Wall","-Wextra","-Werror","-S","-emit-llvm",src,"-o",ir], check=True)
            if name == "production":
                archive_binding(ir, Path(tmp), env)
            compiled = ir.read_text()
            if name == "production":
                print(f"Checked {dispatch(compiled)} optimized dispatch layouts and four early exits.", flush=True)
            if name in ("wrong inline index", "swapped grid dimensions"):
                try:
                    dispatch(compiled)
                except ValueError as error:
                    if "compiled dispatch message operands differ" not in str(error):
                        raise
                    print(f"Symbolic dispatch rejected {name}.", flush=True)
                    continue
                raise ValueError(f"mutation passed: {name}")
            paths = observations(compiled, "commit_and_wait")
            barriers = observations(compiled, "barrier")
            result = subprocess.run(["lake","env","lean","--stdin"], input=certificate(paths, barriers), text=True,
                                    cwd=lean, env=env, capture_output=True)
            if before is None:
                if result.returncode:
                    raise ValueError(result.stdout + result.stderr)
                print(f"Lean checked {len(paths)} wait paths and {len(barriers)} barrier paths in optimized bridge IR.", flush=True)
            elif not result.returncode or "decide" not in result.stdout + result.stderr:
                raise ValueError(f"expected the kernel to reject {name}: {result.stdout}{result.stderr}")
            else:
                print(f"Lean rejected {name}.", flush=True)


if __name__ == "__main__":
    main()
