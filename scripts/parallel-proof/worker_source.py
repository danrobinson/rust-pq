"""Closure-convert the signing worker in a scratch crate for Aeneas extraction."""

import re

ARGS = {
    "usize": "d hp leaf_pk_count fors_stride total_phase1",
    "u32": "a",
    "Adrs": "fors_addr",
    "&Params": "p",
    "&[u8]": "md",
    "&[u8;N]": "sk",
    "&Seed<N>": "seed",
    "&Vec<WorkItem>": "jobs",
    "&Vec<(Adrs,u32)>": "layers",
    "&Vec<u32>": "fors_indices",
    "&Vec<XmssAuthMeta>": "xmss_meta",
    "&Vec<ForsSplitMeta>": "fors_split_meta",
    "&Vec<OnceLock<[u8;N]>>": "xmss_slots leaf_pks fors_direct fors_split",
    "&AtomicUsize": "phase1_next phase1_done phase2_next",
    "&AtomicU8": "phase2_state",
    "&Mutex<()>": "phase2_lock",
    "&Condvar": "phase2_cv",
    "&OnceLock<Vec<u8>>": "sig_fors_cell",
    "&OnceLock<Vec<[u8;N]>>": "xmss_auth_cell roots_cell",
    "&Vec<OnceLock<Vec<u8>>>": "wots_sigs",
}


def between(text, start, end):
    if text.count(start) != 1:
        raise ValueError(f"ambiguous worker boundary {start!r}")
    lo = text.index(start)
    hi = text.index(end, lo)
    return text[lo:hi]


def stage(rust):
    args = {name: ty for ty, names in ARGS.items() for name in names.split()}
    guard = between(rust, "    const PHASE1_RUNNING", "    let total_phase1")
    old = (
        between(rust, "    let run = || {", "    };\n\n    crate::pool::execute")
        + "    };"
    )
    worker = old[len("    let run = || {") : -len("    };")]
    worker = re.sub(
        r"&(phase2_state|phase2_lock|phase2_cv|fors_split_meta|fors_direct)\b(?!\[)",
        r"\1",
        worker,
    )
    helpers = []

    def function(name, body, inputs, output=""):
        generic = (
            "<const N:usize>"
            if any(re.search(r"\bN\b", ty) for ty in inputs.values())
            else ""
        )
        params = ", ".join(f"{key}: {ty}" for key, ty in inputs.items())
        helpers.append(f"\nfn {name}{generic}({params}) {output} {{\n{body}\n}}\n")
        return f"{name}({', '.join(inputs)})"

    def outline(name, start, end, extra=None):
        nonlocal worker
        body = between(worker, start, end)
        inputs = {n: t for n, t in args.items() if re.search(r"\b" + n + r"\b", body)}
        inputs.update(extra or {})
        worker = worker.replace(body, function(name, body, inputs) + ";\n", 1)

    outline(
        "dispatch",
        "            match item.kind",
        "            // The thread",
        {"item": "WorkItem"},
    )
    outline(
        "reduce",
        "                for meta in fors_split_meta",
        "                let _g = phase2_lock",
    )
    outline(
        "publish", "                let _g = phase2_lock", "            }\n        }"
    )
    wait = between(worker, "        let mut spins", "        let roots =")
    wait_body, count = re.subn(
        r"abort_guard\.armed = false;\s*return;", "return false;", wait
    )
    if count != 2:
        raise ValueError("expected two aborted wait exits")
    wait_call = function(
        "wait",
        wait_body + "true",
        {n: args[n] for n in ("phase2_state", "phase2_lock", "phase2_cv")},
        "-> bool",
    )
    worker = worker.replace(
        wait, f"if !{wait_call} {{abort_guard.armed=false; return;}}\n"
    )
    outline("phase_two", "        let roots =", "        abort_guard.armed = false;")
    abort = between(guard, "                let _g = self.lock", "\n            }")
    guard = guard.replace(
        abort,
        function(
            "abort",
            abort.replace("self.", ""),
            {"state": "&AtomicU8", "lock": "&Mutex<()>", "cv": "&Condvar"},
        ).replace("(state, lock, cv)", "(self.state, self.lock, self.cv)")
        + ";",
    )
    function("flat_worker", worker, args)
    actual = [
        ("&" if ty.startswith("&") and n not in ("sk", "seed", "md", "p") else "") + n
        for n, ty in args.items()
    ]
    return (
        rust.replace(
            between(rust, "    const PHASE1_RUNNING", "    let total_phase1"), "", 1
        ).replace(old, "    let run = || flat_worker(" + ", ".join(actual) + ");", 1)
        + "\n"
        + guard
        + "".join(helpers)
    )
