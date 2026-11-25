# /// script
# requires-python = ">=3.10"
# dependencies = ["pycparser==3.0"]
# ///
"""Verify MSL per-lane memory effects and barrier participation at all FIPS geometries."""

import concurrent.futures
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SUPPORT = HERE / "metal-proof"
ROOT = HERE.parent
sys.path.insert(0, str(SUPPORT))
from effects import extract, helper_contract

NAMES = dict(
    wots_chains="chains",
    wots_tlen="tlen",
    xmss_leaves_streaming="streaming",
    xmss_reduce="xmss",
    fors_pass1="pass1",
    fors_pass2="pass2",
    fors_pk="fors_pk",
    wots_sign="wots_sign",
)
ROWS = runpy.run_path(str(HERE / "check-metal-kernels.py"))["PARAM_SETS"]
MODEL = (SUPPORT / "workgroup.c").read_text()


def check_geometry(lib):
    # Bind the values passed through the Rust/Objective-C dispatch audit,
    # including repeated xmss_reduce call sites in the two planning branches.
    definitions = {
        "reduce_tg": ["1u32<<(p.hp-1)", "1u32<<(hp-1)", "1u32<<(hp-1)"],
        "reduce_tg_mem": ["reduce_tg*(Nasu32)"] * 3,
        "fors1_tg_x": ["1u32<<(s1-1)"],
        "fors2_tg_x": ["1u32<<(s2-1)"],
        "fors1_tg_mem": ["fors1_tg_x*(Nasu32)"],
        "fors2_tg_mem": ["fors2_tg_x*(Nasu32)"],
        "fors1_tgs": ["(num_sigsasu32)*p.k*subtrees_per_tree"],
        "fors2_tgs": ["(num_sigsasu32)*p.k"],
        "total_chains": [
            "(total_leaves*wots_len)asu32",
            "(total_xmss_leaves*wots_len)asu32",
        ],
        "total_wots_chains": ["(total_trees*wots_len)asu32"],
    }
    lib = re.sub(r"//[^\n]*|/\*.*?\*/", "", lib, flags=re.S)
    for variable, expected in definitions.items():
        actual = re.findall(r"\blet\s+(?:mut\s+)?" + variable + r"\s*=([^;]+);", lib)
        if [re.sub(r"\s+", "", value) for value in actual] != expected:
            raise ValueError("unexpected host dispatch dimension: " + variable)


def projection(source, prefix, name):
    source_ir, barriers = extract(source, prefix + name + "_impl")
    if barriers != (3 if NAMES[name] in ("xmss", "pass1", "pass2") else 0):
        raise ValueError("unexpected barrier count in " + name)
    source_ir = re.sub(r"\btrees\[([^\]]+)\]", r"get_tree(\1)", source_ir)
    source_ir = re.sub(r"\blayers\[([^\]]+)\]", r"get_layer(\1)", source_ir)
    # The original source loads one read-only descriptor. Keep the dependency of
    # both fields on its index, while abstracting all admissible digest values.
    source_ir = re.sub(
        r"ForsJobDesc job = jobs\[([^\]]+)\];",
        r"uint job_base = get_fors_base(\1);",
        source_ir,
    )
    source_ir = source_ir.replace("job.sig_byte_off", "job_base")
    return re.sub(r"job\.indices\[([^\]]+)\]", r"get_fors_index(\1)", source_ir)


def harness(row, name, ir):
    _, family, n, _, d, hp, a, k, _ = row
    s1 = a if a <= 8 else 7
    s2 = a - s1
    words = n // (8 if family == "shake" else 4)
    wots = 2 * n + 3
    sig_bytes = n * (1 + (1 + a) * k + d * (wots + hp))
    kind = NAMES[name]
    # XMSS and WOTS descriptors point inside a signature. Even the final
    # field in a batch filling the u32 address space is a legal base.
    field_bytes = {"xmss": hp * n, "wots_sign": wots * n}.get(kind, sig_bytes)
    height = {"xmss": hp, "pass1": s1, "pass2": s2}.get(kind, 0)
    stride = {
        "chains": d * (1 << hp) * wots,
        "tlen": d * (1 << hp),
        "streaming": d * (1 << hp),
        "xmss": d,
        "pass1": k * (1 << s2),
        "pass2": k,
        "fors_pk": 1,
        "wots_sign": d * wots,
    }[kind]
    # Any batch whose command fits the host guards. Keygen issues one XMSS
    # tree per key with the sentinel and may admit more items than signing.
    limit = (2**32 - 1) // (stride * words)
    if kind in ("pass1", "pass2", "fors_pk", "wots_sign"):
        limit = min(limit, (2**32 - 1) // sig_bytes)
    definitions = dict(
        N=n, WORDS=words, WOTS=wots, HP=hp, A=a, S1=s1, S2=s2, KERNEL=kind
    )
    prefix = "".join(f"#define {key} {val}\n" for key, val in definitions.items())
    return (
        prefix
        + MODEL
        + "\nvoid run(void)"
        + ir
        + f"""
int main(void) {{
    uint count = arbitrary();
    assume(count <= {limit}u);
    p = (Params){{.hp=HP,.a=A,.s1=S1,.s2=S2,.num_trees=count*{d},.leaves_per_tree=1u<<HP,
        .wots_len=WOTS,.num_sigs=count,.subtrees_per_tree=1u<<S2,.k={k},.num_layers=count*{d}}};
    uint total = count * {stride}u;
    if (KERNEL == xmss || KERNEL == chains || KERNEL == tlen || KERNEL == streaming) {{
        uniform_keygen = arbitrary() & 1u;
        if (uniform_keygen) {{
            p.num_trees = arbitrary();
            uint items_per_tree = {stride // d if kind in ("xmss", "chains", "tlen", "streaming") else 1}u;
            assume(p.num_trees <= UINT_MAX / (items_per_tree * WORDS));
            total = p.num_trees * items_per_tree;
        }}
    }}
    owner_group = arbitrary();
    admitted = owner_group < total;
    gid = tg_id = sig_idx = owner_group;
    descriptor = KERNEL == pass1 ? (owner_group >> S2)/{k} : owner_group/{k};
    tree_number = KERNEL == pass1 ? (owner_group >> S2)%{k} : owner_group%{k};
    subtree = owner_group % (1u << S2);
    target = arbitrary();
    assume(target < (1u << (KERNEL == xmss ? HP : A)));
    if (KERNEL == xmss && uniform_keygen) target = UINT_MAX;
    signature_base = arbitrary();
    /* All legal descriptors have space for this signature's fields. */
    assume(signature_base <= UINT_MAX - {field_bytes});
    watch = arbitrary();
    assume(watch < (KERNEL == wots_sign ? WOTS : KERNEL == xmss ? HP : A+1));
    lanes = {1 << (max(height, 1) - 1)}u;
    tid = arbitrary(); assume(tid < lanes);
    run();
    CHECK(phase == (admitted ? {max(0, 2 * height - 1)}u : 0u), "uniform barrier sequence completed");
    CHECK(signature_count == (uint)owns(watch), "every owned signature node written exactly once");
    uint mask = (admitted && tid == 0 && KERNEL != wots_sign) ? (1u << WORDS)-1u : 0u;
    CHECK(global_mask == mask, "complete device node");
}}
"""
    )


def run_cbmc(cbmc, folder, label, content, expect=None):
    file = folder / (label + ".c")
    file.write_text(content)
    cmd = [
        cbmc,
        str(file),
        "--unwind",
        "18",
        "--unwinding-assertions",
        "--slice-formula",
        "--verbosity",
        "5",
        "--object-bits",
        "12",
    ]
    p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if expect is None:
        if p.returncode != 0 or "VERIFICATION SUCCESSFUL" not in p.stdout:
            raise ValueError(label + "\n" + p.stdout[-6000:])
    elif p.returncode != 10 or not any(
        expect in line and "FAILURE" in line for line in p.stdout.splitlines()
    ):
        raise ValueError(
            label + ": unexpected negative control outcome\n" + p.stdout[-6000:]
        )


def negatives(cbmc, folder, source, row):
    # Mutate the production MSL before lifting it. Every test checks for a
    # specific violated contract so translation failures cannot count as success.
    name = "xmss_reduce"
    start = source.index("inline void xmss_reduce_impl(")
    end = source.index("\n}", start) + 2
    original = source[start:end]
    cases = (
        (
            "overlapping-writes",
            "tg_nodes[tid * NW + i] = parent[i];",
            "tg_nodes[(tid >> 1) * NW + i] = parent[i];",
            "unique writer",
        ),
        (
            "stale-read",
            "right[i] = tg_nodes[(2u * tid + 1u) * NW + i];",
            "right[i] = tg_nodes[half_leaves * NW + i];",
            "read initialized",
        ),
        (
            "divergent-barrier",
            "threadgroup_barrier(mem_flags::mem_threadgroup);",
            "if (tid == 0u) threadgroup_barrier(mem_flags::mem_threadgroup);",
            "barrier",
        ),
        (
            "missing-word",
            "tg_nodes[tid * NW + i] = parent[i];",
            "if (i != 1) tg_nodes[tid * NW + i] = parent[i];",
            "prefix initialized",
        ),
        ("wrong-signer-lane", "if (tid == sib)", "if (tid == 0u)", "unique writer"),
        ("wrong-root", "out_roots[out_off + i]", "out_roots[i]", "unique writer"),
    )
    for label, old, new, failure in cases:
        if old not in original:
            raise ValueError("negative control no longer matches: " + label)
        changed = original.replace(old, new, 1)
        ir = projection(source[:start] + changed + source[end:], "", name)
        run_cbmc(cbmc, folder, label, harness(row, name, ir), failure)
        print("Rejected " + label, flush=True)


def main():
    cbmc = (
        os.environ.get("CBMC")
        or shutil.which("cbmc")
        or str(Path.home() / ".kani/kani-0.68.0/bin/cbmc")
    )
    check_geometry((ROOT / "metal/src/lib.rs").read_text())
    sources = {}
    for family in ("sha2", "shake"):
        prefix = "shake_" if family == "shake" else ""
        shader = (
            ROOT
            / "metal/shaders"
            / ("slhdsa_shake.metal" if prefix else "slhdsa.metal")
        )
        source = shader.read_text()
        helper_contract(source, prefix)
        code = re.sub(r"//[^\n]*|/\*.*?\*/", "", source, flags=re.S)
        if len(re.findall(r"\bthreadgroup_barrier\s*\(", code)) != 9:
            raise ValueError("barrier outside modeled reduction kernels")
        if not prefix:
            sha2_source = source
        if set(re.findall(r"inline void (\w+_impl)\(", source)) != {
            prefix + k + "_impl" for k in NAMES
        }:
            raise ValueError("unexpected production kernel set")
        for name in NAMES:
            sources[family, name] = projection(source, prefix, name)

    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        jobs = [
            (row[0] + "-" + name, harness(row, name, sources[row[1], name]))
            for row in ROWS
            for name in NAMES
            if not (name == "fors_pass2" and row[6] <= 8)
        ]
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as executor:
            futures = [
                executor.submit(run_cbmc, cbmc, folder, label, src)
                for label, src in jobs
            ]
            for (label, _), future in zip(jobs, futures):
                future.result()
                print(label, flush=True)
        negatives(cbmc, folder, sha2_source, ROWS[0])
        print(f"Checked {len(jobs)} shader/geometry combinations.")
    facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
    facade["run"](["lake", "build", "Metal.Workgroup"], ROOT / "lean-hw")
    facade["audit_theorems"](
        "Metal.Workgroup",
        [
            "Metal.Workgroup." + theorem
            for theorem in (
                "no_conflict",
                "preceding_write",
                "uniform_barriers",
                "separate_slots",
            )
        ],
    )


if __name__ == "__main__":
    main()
