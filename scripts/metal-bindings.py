"""Extract slot layouts from each Rust dispatch and both MSL entry-point macros."""

import json
import re
from collections import Counter

# Shader argument names denote these logical scratch resources. FORS roots
# use the pass-1 output directly when the second pass has zero levels.
SHADER_ROLES = {
    "keys": "keys",
    "trees": "xmss_trees",
    "layers": "wots_layers",
    "jobs": "fors_jobs",
    "out_chain_tips": "chain_tips",
    "chain_tips": "chain_tips",
    "out_leaves": "xmss_leaves",
    "leaves": "xmss_leaves",
    "out_roots": "xmss_roots",
    "xmss_roots": "xmss_roots",
    "out_sub_roots": "fors_sub_roots",
    "in_sub_roots": "fors_sub_roots",
    "out_fors_roots": "fors_roots",
    "fors_roots": "fors_roots",
    "out_pk_fors": "pk_fors",
    "pk_fors": "pk_fors",
    "out_sigs": "out_sigs",
}
PARAM_TYPES = {
    "xmss_params": "XmssParams",
    "fors_params": "ForsParams",
    "wots_sign_params": "WotsSignParams",
}
SITE_COUNTS = {
    "keygen_internal_batch_family": Counter(
        wots_chains=1, wots_tlen=1, xmss_leaves_streaming=1, xmss_reduce=1
    ),
    "sign_internal_batch_family": Counter(
        wots_chains=1,
        wots_tlen=1,
        xmss_leaves_streaming=1,
        xmss_reduce=2,
        fors_pass1=1,
        fors_pass2=1,
        fors_pk=2,
        wots_sign=1,
    ),
}


def code(text):
    return re.sub(r"/\*.*?\*/|//[^\n]*", "", text, flags=re.S)


def shader_layouts(source, prefix):
    layouts = {}
    for kernel, args, body in re.findall(
        r"kernel void (\w+)_##SUFFIX\s*\((.*?)\)\s*\\?\s*\{(.*?)\}", code(source), re.S
    ):
        args = args.replace("\\", "")
        slots = re.findall(r"(\w+)\s*\[\[buffer\((\d+)\)\]\]", args)
        params = re.findall(r"constant\s+(\w+)\s*&p\s*\[\[buffer", args)
        if (
            len(params) != 1
            or slots[-1][0] != "p"
            or [int(i) for _, i in slots] != list(range(len(slots)))
        ):
            raise ValueError(f"unrecognized Metal interface for {kernel}")
        kind = "threadgroups" if "[[threadgroup(0)]]" in args else "threads"
        arguments = re.findall(r"(\w+)\s*\[\[", args)
        if kernel.startswith("shake_") != (prefix == "shake_"):
            raise ValueError(f"unexpected kernel family for {kernel}")
        width = "NL" if prefix else "NW"
        forwarded = f"{kernel}_impl<{width}>({','.join(arguments)});"
        if re.sub(r"\s+|\\", "", body) != forwarded:
            raise ValueError(f"{kernel}: wrapper changes kernel arguments")
        name = kernel.removeprefix("shake_")
        if name in layouts:
            raise ValueError(f"duplicate Metal kernel {kernel}")
        layouts[name] = (tuple(SHADER_ROLES[x] for x, _ in slots[:-1]), params[0], kind)
    return layouts


def verify(lib, sha2, shake):
    lib = code(lib)
    interfaces = shader_layouts(sha2, ""), shader_layouts(shake, "shake_")
    claims = ["import Metal.Bindings"]
    compact_lib = re.sub(r"\s+", "", lib)
    for family, prefix, msl, macro, word in (
        ("sha2", "", sha2, "DEFINE_KERNELS", 4),
        ("shake", "shake_", shake, "DEFINE_SHAKE_KERNELS", 8),
    ):
        for n in (16, 24, 32):
            field = f"{family}_p{n}"
            load = f'let{field}=PipelinesForN::load(&ctx,"{prefix}","N{n}")?;'
            arm = f"(HashFamily::{family.capitalize()},{n})=>Ok(&self.{field}),"
            if (
                load not in compact_lib
                or arm not in compact_lib
                or not re.search(rf"^{macro}\(N{n},\s*{n // word}\)$", msl, re.M)
            ):
                raise ValueError(f"incorrect pipeline selection for {family}/{n}")
    expected_kernels = set(SITE_COUNTS["sign_internal_batch_family"])
    if any(set(interface) != expected_kernels for interface in interfaces):
        raise ValueError("kernel declarations differ from the reviewed dispatch set")
    for kernel in interfaces[0]:
        load = f'{kernel}:ctx.pipeline(&format!("{{prefix}}{kernel}_{{suffix}}"))?,'
        if load not in compact_lib:
            raise ValueError(f"incorrect pipeline name for {kernel}")
    sites = re.compile(r"\bcmd\.dispatch_(\w+)\s*\((.*?)\);", re.S)
    for fn, expected in SITE_COUNTS.items():
        start = lib.index("fn " + fn + "<")
        body = lib[start : lib.index("\n    }", start)]
        if (
            re.sub(r"\s+", "", body).count("letpipes=self.pipelines::<N>(family)?;")
            != 1
        ):
            raise ValueError(f"{fn}: incorrect pipeline selection")
        keygen = fn == "keygen_internal_batch_family"
        leaves = "total_leavesasu32" if keygen else "total_xmss_leavesasu32"
        grids = {
            "wots_chains": ("total_chains", "tg_chains", "0"),
            "wots_tlen": (leaves, "tg_tlen", "0"),
            "xmss_leaves_streaming": (leaves, "tg_leaves", "0"),
            "xmss_reduce": (
                "countasu32" if keygen else "total_treesasu32",
                "reduce_tg",
                "reduce_tg_mem",
            ),
            "fors_pass1": ("fors1_tgs", "fors1_tg_x", "fors1_tg_mem"),
            "fors_pass2": ("fors2_tgs", "fors2_tg_x", "fors2_tg_mem"),
            "fors_pk": ("num_sigsasu32", "tg_fpk", "0"),
            "wots_sign": ("total_wots_chains", "tg_wsig", "0"),
        }
        aliases = {}
        found = Counter()
        for call in sites.finditer(body):
            kind, args = call.groups()
            args = re.sub(r"\s+", "", args)
            m = re.fullmatch(
                r"&pipes\.(\w+),&\[([\w,]+)\],&\[InlineBytes::of\((\d+),&(\w+)\)\],"
                r"([^,]+),([^,]+),([^,]+),",
                args,
            )
            if not m:
                raise ValueError(f"unrecognized dispatch in {fn}: {args}")
            kernel, buffers, slot, params, grid, group, scratch = m.groups()
            if (grid, group, scratch) != grids[kernel]:
                raise ValueError(
                    f"{fn}/{kernel}: incorrect grid or threadgroup allocation"
                )
            names = buffers.split(",")
            for name in names:
                # Resolve the actual scratch field, including block-local bindings.
                definitions = re.findall(
                    r"\blet\s+" + re.escape(name) + r"\s*=\s*(.*?);",
                    body[: call.start()],
                    re.S,
                )
                rhs = re.sub(r"\s+", "", definitions[-1])
                direct = re.fullmatch(r"pool\.(\w+)\.as_ref\(\)\.unwrap\(\)", rhs)
                if direct:
                    aliases[name] = direct[1]
                elif (
                    name == "froots_buf"
                    and rhs == "ifs2>0{pool.fors_roots.as_ref().unwrap()}else{fsub_buf}"
                    and aliases.get("fsub_buf") == "fors_sub_roots"
                ):
                    aliases[name] = "fors_roots"
                else:
                    raise ValueError(
                        f"{fn}: unknown scratch allocation for {name}: {rhs}"
                    )
            actual = (tuple(aliases[x] for x in names), PARAM_TYPES[params], kind)
            if int(slot) != len(names) or (scratch == "0") != (kind == "threads"):
                raise ValueError(
                    f"{fn}: incorrect inline or threadgroup slot for {kernel}"
                )
            if not re.search(
                r"let\s+" + params + r"\s*=\s*" + PARAM_TYPES[params] + r"\s*\{", body
            ):
                raise ValueError(f"{fn}: incorrect type for {params}")
            for interface in interfaces:
                if actual != interface[kernel]:
                    raise ValueError(
                        f"{fn}/{kernel}: host {actual}, shader {interface[kernel]}"
                    )
                host = json.dumps(actual[0])
                shader = json.dumps(interface[kernel][0])
                claims.append(
                    f"example {{α : Type}} := @MetalBindings.dispatch α {host} {shader} {slot} rfl rfl"
                )
            found[kernel] += 1
        if found != expected:
            raise ValueError(f"{fn}: unexpected dispatch sites: {found}")
    if len(sites.findall(lib)) != sum(sum(c.values()) for c in SITE_COUNTS.values()):
        raise ValueError("unreviewed dispatch outside keygen/signing")
    return "\n".join(claims)


def check_slot_swaps(lib, sha2, shake):
    """Require the checker to reject every transposition at every host call site."""
    pairs = 0
    pattern = r"cmd\.dispatch_\w+\(\s*&pipes\.\w+,\s*&\[([\w,\s]+)\]"
    for call in re.finditer(pattern, lib):
        names = [name.strip() for name in call[1].split(",")]
        for i in range(len(names)):
            for j in range(i):
                swapped = names.copy()
                swapped[i], swapped[j] = swapped[j], swapped[i]
                mutant = lib[: call.start(1)] + ", ".join(swapped) + lib[call.end(1) :]
                try:
                    verify(mutant, sha2, shake)
                except ValueError as err:
                    if ": host " not in str(err):
                        raise
                else:
                    raise AssertionError(
                        f"accepted swapped host arguments {names[i]}, {names[j]}"
                    )
                pairs += 1
    if not pairs:
        raise ValueError("no Metal dispatches for slot-swap negative controls")
    print(f"Rejected all {pairs} host-buffer transpositions.")


def check_stages(lib, *, require_dependencies=True):
    """Execute the encoder's branch and barrier logic for every launch mode."""
    import os
    import subprocess
    import tempfile
    from pathlib import Path

    lib = code(lib)
    src = ""
    for fn, label in zip(SITE_COUNTS, ["keygen", "sign"]):
        start = lib.index("fn " + fn + "<")
        body = lib[start : lib.index("\n    }", start)]
        mode, program = re.findall(
            r"let mut cmd = self.ctx.begin_cmd\((true|false)\)\?;(.*?)cmd.commit_and_wait\(\)\?;",
            body,
            re.S,
        )[0]
        # Preserve all control flow. Erase pure geometry/borrow bindings and
        # replace each validated dispatch call with its kernel publication.
        program = re.sub(
            r"cmd\.dispatch_(?:threads|threadgroups)\(\s*&pipes\.(\w+),.*?\);",
            r'log.push(("\1", stage)); if !concurrent { stage += 1; }',
            program,
            flags=re.S,
        )
        program = program.replace("cmd.barrier();", "stage += 1;").replace(
            "unsafe {", "{"
        )
        program = re.sub(r"let (?!mut )\w+\s*=\s*([^;{}]+);", "", program)
        src += f"fn {label}(use_two_phase:bool,s2:u32) -> Vec<(&'static str,u32)> {{\n"
        src += (
            f"let concurrent = {mode};let mut stage=0;let mut log=Vec::new();\n"
            + program
            + "\nlog\n}\n"
        )

    src += """
fn main() {
    for phase in [false,true] { for split in [0,1] {
        for (signing, log) in [(false,keygen(phase,split)),(true,sign(phase,split))] {
            let stage = |name| {
                let mut found = log.iter().filter(|(k,_)| *k == name);
                let result = found.next().expect(name).1;
                assert!(found.next().is_none(), "duplicate {name}");
                result
            };
            let leaves = if phase {
                assert!(stage("wots_chains") < stage("wots_tlen")); stage("wots_tlen")
            } else { stage("xmss_leaves_streaming") };
            assert!(leaves < stage("xmss_reduce"));
            let mut count = if phase {3} else {2};
            if signing {
                let f1 = stage("fors_pass1");
                if split > 0 {
                    assert!(f1 < stage("fors_pass2") && stage("fors_pass2") < stage("fors_pk"));
                    count += 1;
                } else {assert!(f1 < stage("fors_pk"));}
                assert!(stage("fors_pk") < stage("wots_sign"));
                assert!(stage("xmss_reduce") < stage("wots_sign"));
                count += 3;
            }
            assert_eq!(log.len(), count);
            print!("{} {} {}", signing, phase, split);
            for (kernel, epoch) in log { print!(" {kernel}:{epoch}"); }
            println!();
        }
    } }
}
"""
    if not require_dependencies:
        # Negative controls replay the mutated graph and ask the Lean resource
        # checker to refute it, allowing the invalid trace to reach the kernel.
        start = src.index("            let stage = |name|")
        src = src[:start] + src[src.index('            print!("{} {} {}"', start):]
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "stages.rs"
        exe = Path(tmp) / "stages"
        source.write_text(src)
        env = dict(
            os.environ,
            PATH=str(Path.home() / ".cargo/bin") + os.pathsep + os.environ["PATH"],
        )
        subprocess.run(
            ["rustc", "--edition=2021", "-Aunused", "-O", source, "-o", exe],
            env=env,
            check=True,
        )
        output = subprocess.run([exe], check=True, text=True, stdout=subprocess.PIPE).stdout
    traces = {}
    for line in output.splitlines():
        signing, phase, split, *events = line.split()
        traces[(signing == "true", phase == "true", int(split))] = [
            (name, int(epoch)) for name, epoch in (event.split(":") for event in events)
        ]
    if len(traces) != 8:
        raise ValueError("incomplete encoder control-flow coverage")
    return traces
