"""Give shared allocations distinct call sites before Aeneas pure-call simplification."""

import re

COUNTERS = ("phase1_next", "phase1_done", "phase2_next")
OUTPUTS = ("sig_fors_cell", "xmss_auth_cell", "roots_cell")
TABLES = ("xmss_slots", "leaf_pks", "fors_direct", "fors_split", "wots_sigs")


def allocation_sites(rust):
    helpers = []

    def replace(name, pattern, expression, helper):
        nonlocal rust
        rust, hits = re.subn(
            r"(let " + name + r"\b[^;=]*=\s*" + pattern + r")",
            lambda m: m[0][: m.start(2) - m.start()] + expression,
            rust,
        )
        if hits != 1:
            raise ValueError(f"expected one allocation for {name}, found {hits}")
        helpers.append(helper)

    for name in COUNTERS:
        replace(
            name,
            r"(AtomicUsize::new\(0\))",
            f"alloc_{name}()",
            f"fn alloc_{name}() -> AtomicUsize {{ AtomicUsize::new(0) }}",
        )
    for name in OUTPUTS:
        # These type annotations include a semicolon inside [u8; N].
        pat = r"(let " + name + r":[^=]+?= )OnceLock::new\(\)"
        rust, count = re.subn(pat, r"\g<1>alloc_" + name + "()", rust)
        if count != 1:
            raise ValueError("missing global cell allocation " + name)
        helpers.append(f"fn alloc_{name}<T>() -> OnceLock<T> {{ OnceLock::new() }}")
    for name in TABLES:
        pat = (
            r"(let "
            + name
            + r":[^=]+?=\s*\(0\.\.[^)]+\)\.map\()\|_\| OnceLock::new\(\)(\)\.collect\(\);)"
        )
        rust, count = re.subn(pat, r"\g<1>|i| alloc_" + name + r"(i)\2", rust)
        if count != 1:
            raise ValueError("missing table allocation " + name)
        helpers.append(
            f"fn alloc_{name}<T>(_index: usize) -> OnceLock<T> {{ OnceLock::new() }}"
        )
    return rust + "\n" + "\n".join(helpers) + "\n"


def check_captures(generated):
    caller = generated.split("def shake.slh.parallel.sign\n")[1]
    sites = re.findall(
        r"pool\.execute\s+.*?\btrue\s+\((.*?)\)\s*let o ←", caller, re.DOTALL
    )
    if not sites:
        raise ValueError("missing extracted pool capture")
    for site in sites:
        captures = [x.strip() for x in site.split(",")]
        if captures[-10:] != [
            *COUNTERS,
            "phase2_state",
            "phase2_lock",
            "phase2_cv",
            *OUTPUTS,
            "wots_sigs",
        ]:
            raise ValueError(f"incorrect captured shared identities {captures[-10:]}")
        if captures[-14:-10] != list(TABLES[:-1]):
            raise ValueError("incorrect captured shared tables")
    for name in COUNTERS + OUTPUTS:
        if len(
            re.findall(
                r"let " + name + r" ←\s*shake\.slh\.parallel\.alloc_" + name + r"\b",
                caller,
            )
        ) != len(sites):
            raise ValueError("missing extracted shared constructor " + name)


def allocation_witness(generated):
    """Erasure of each labelled constructor recovers the original std call."""
    equations = ["namespace slhdsa\nopen Aeneas Aeneas.Std"]
    for name in COUNTERS:
        equations.append(
            f"example : shake.slh.parallel.alloc_{name} = "
            "core.sync.atomic.AtomicUsizeAlign8Usize.new 0#usize := rfl"
        )
    for name in OUTPUTS:
        equations.append(
            f"example (T : Type) : shake.slh.parallel.alloc_{name} T = "
            "std.sync.once_lock.OnceLock.new T := rfl"
        )
    for n, name in enumerate(TABLES, 1):
        equations.append(
            f"example (T : Type) (i : Std.Usize) : shake.slh.parallel.alloc_{name} T i = "
            "std.sync.once_lock.OnceLock.new T := rfl"
        )
        match = re.search(
            rf"^def\s+shake\.slh\.parallel\.sign\.closure_{n}\.Insts\.[^.]+\.call_mut\n(.*?)(?=\n\n)",
            generated,
            re.MULTILINE | re.DOTALL,
        )
        if not match or not re.search(
            rf"let ol ←\s*shake\.slh\.parallel\.alloc_{name}\s+\(.*?\) tupled_args\s+ok \(ol, c\)$",
            match[1],
            re.DOTALL,
        ):
            raise ValueError("incorrect table allocation index in " + name)
        # Check the use of that callback at the captured vector, too.
        caller = generated.split("def shake.slh.parallel.sign\n")[1]
        sites = re.findall(
            rf"let (\w+) ←\s*core\.iter\.traits\.iterator\.Iterator\.map\.default\s+[^←]+?closure_{n}\.Insts\.[^←]+?\(\)\s+let {name} ←\s*([^←]+?)\n\s*let ",
            caller,
        )
        if not sites or any(
            not collect.rstrip().endswith(" " + var) for var, collect in sites
        ):
            raise ValueError("wrong iterator collected into " + name)
    equations.append("end slhdsa")
    return "\n".join(equations) + "\n"


def allocation_graphs(staged, tagged):
    """Inline only the eleven checked normal-return constructor bodies."""
    import worker_mir as mir

    prefix = "shake::slh::parallel::"
    for name in COUNTERS + OUTPUTS + TABLES:
        primitive = (
            "Atomic::<usize>::new(const 0_usize)"
            if name in COUNTERS
            else "OnceLock::<T>::new()"
        )
        blocks = mir.block_map(mir.function(tagged, prefix + "alloc_" + name))
        if {k: [x.strip() for x in v] for k, v in blocks.items()} != {
            0: [f"_0 = {primitive} -> [return: bb1, unwind continue];"],
            1: ["return;"],
        }:
            raise ValueError("unexpected allocation helper body " + name)
    orig = mir.function(staged, prefix + "sign")
    caller = mir.function(tagged, prefix + "sign")
    for name in COUNTERS + OUTPUTS:
        dest = mir.only(re.findall(r"debug " + name + r" => (_\d+);", caller))
        pat = r"(" + dest + r" = )" + prefix + "alloc_" + name
        if name in COUNTERS:
            pat += r"\(\)"
            call = r"\g<1>Atomic::<usize>::new(const 0_usize)"
        else:
            pat += r"::<(.+?)>\(\)"
            call = r"\g<1>OnceLock::<\2>::new()"
        caller, n = re.subn(pat, call, caller)
        if n != 1:
            raise ValueError("incorrect allocated destination " + name)
    before, cb1 = mir.normal_graph(orig, True, "caller")
    after, cb2 = mir.normal_graph(caller, True, "caller")
    # The pool callback takes no tuple argument and has a distinct MIR ABI.
    pool = prefix + "sign::{closure#6}"
    worker1, worker2 = mir.function(staged, pool), mir.function(tagged, pool)
    env1, env2 = mir.CLOSURE.search(worker1)[0], mir.CLOSURE.search(worker2)[0]
    if cb1.index(env1) != cb2.index(env2) or worker1.replace(
        env1, "Self"
    ) != worker2.replace(env2, "Self"):
        raise ValueError("allocation labels changed worker environment")
    cb1.remove(env1)
    cb2.remove(env2)
    left, right = mir.callbacks(staged, cb1), mir.callbacks(tagged, cb2)
    for name in TABLES:
        c = mir.only(
            i for i, body in enumerate(right) if prefix + "alloc_" + name + "::" in body
        )
        pat = re.escape(prefix + "alloc_" + name) + r"::<(.+?)>\(copy _2\)"
        right[c], n = re.subn(pat, r"OnceLock::<\1>::new()", right[c])
        if n != 1:
            raise ValueError("incorrect allocation index " + name)
        right[c] = right[c].replace("    debug i => _2;\n", "")
    if before != after or left != right:
        raise ValueError("labelled allocation changes caller or callback MIR")
    return before, after
