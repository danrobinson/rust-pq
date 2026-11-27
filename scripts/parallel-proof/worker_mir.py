"""Compare normal control flow and operands in the production and staged Rust signer."""

import re
from collections import Counter

LOCAL = re.compile(r"(?<!\w)_\d+\b")
BLOCK = re.compile(r"\bbb(\d+)\b")
CLOSURE = re.compile(r"\{closure@[^}]+\}")
CAPTURE = re.compile(r"\(\(\*_1\)\.(\d+): &[^\n]+\)")
BY_VALUE = {
    "item",
    "a",
    "fors_addr",
    "fors_stride",
    "d",
    "hp",
    "leaf_pk_count",
    "total_phase1",
}


def only(values):
    (value,) = values
    return value


def function(mir, name):
    return mir.split("\nfn " + name + "(", 1)[1].split("\n}\n", 1)[0]


def block_map(body):
    return {
        int(i): lines.strip().splitlines()
        for i, lines in re.findall(
            r"^    bb(\d+): \{\n(.*?)^    \}", body, re.MULTILINE | re.DOTALL
        )
    }


def normal_graph(body, helper, region="dispatch"):
    blocks = block_map(body)

    def select(test):
        return only(k for k, lines in blocks.items() if test("\n".join(lines)))

    def returned(k):
        return int(re.search(r"return: bb(\d+)", blocks[k][-1])[1])

    def acquire_lock():
        capture = only(re.findall(r"debug roots_cell => \(\*\(\(\*_1\)\.(\d+):", body))
        set_roots = select(
            lambda text: f"((*_1).{capture}:" in text and ">::set(" in text
        )
        drop = returned(set_roots)
        if not re.match(r"drop\(_\d+\)", blocks[drop][0].strip()):
            raise ValueError("missing result drop after publishing roots")
        lock = returned(drop)
        if "Mutex::<()>::lock(" not in blocks[lock][-1]:
            raise ValueError("unexpected reducer continuation")
        return lock

    def after_publish():
        notify = select(lambda text: "Condvar::notify_all(" in text)
        drop = returned(notify)
        if not re.match(r"drop\(_\d+\)", blocks[drop][0].strip()):
            raise ValueError("missing mutex guard drop after publication")
        return returned(drop)

    if region == "caller":
        entry = 0
        boundary = select(lambda text: text.rstrip().endswith("return;"))
        # Reordering the capture environment changes its physical layout. Resolve
        # temporary shared references to their places, then sort by field name.
        capture = select(
            lambda text: (
                "phase1_next:" in text and "wots_sigs:" in text and "{closure@" in text
            )
        )
        lines = [s.strip() for s in blocks[capture]]
        idx = only(i for i, line in enumerate(lines) if "{closure@" in line)
        aliases = {}
        for line in lines[:idx]:
            bind = re.fullmatch(r"(_\d+) = &(_\d+);", line)
            if (
                not bind
                or len(
                    re.findall(
                        r"(?<!\w)" + bind[1] + r"\b",
                        "\n".join(s for v in blocks.values() for s in v),
                    )
                )
                != 2
            ):
                raise ValueError(
                    "capture construction contains a nonlocal or effectful operation"
                )
            aliases[bind[1]] = bind[2]
        define = re.fullmatch(r"(_\d+ = \{closure@[^}]+\}) \{ (.*) \};", lines[idx])
        fields = []
        for binding in define[2].split(", "):
            field, how, local = re.fullmatch(
                r"(\w+): (copy|move) (_\d+)", binding
            ).groups()
            bound = (
                "shared " + aliases[local]
                if local in aliases and how == "move"
                else how + " " + local
            )
            fields.append(field + ": " + bound)
        if len(fields) != 30 or len({f.split(":")[0] for f in fields}) != 30:
            raise ValueError("unexpected signing closure captures")
        blocks[capture] = [
            define[1] + " { " + ", ".join(sorted(fields)) + " };",
            *lines[idx + 1 :],
        ]
    elif region == "dispatch":
        entry = select(lambda text: "WorkKind));" in text and "switchInt" in text)
        boundary = (
            select(lambda text: text == "return;")
            if helper
            else select(
                lambda text: "Ordering::AcqRel;" in text and "fetch_add(" in text
            )
        )
        index = next(i for i, x in enumerate(blocks[entry]) if " = discriminant(" in x)
        blocks[entry] = blocks[entry][index:]
    elif region == "reduce":
        entry = (
            0
            if helper
            else select(
                lambda text: "ForsSplitMeta> as IntoIterator>::into_iter" in text
            )
        )
        if helper:
            boundary = select(lambda text: text.rstrip().endswith("return;"))
        else:
            boundary = acquire_lock()
    elif region == "publish":
        entry = 0 if helper else acquire_lock()
        boundary = select(lambda text: text == "return;") if helper else after_publish()
    elif region == "controller":
        # Replace each matched payload region with a single normally returning
        # call. Its continuation is the boundary checked by that region's proof.
        entry = only(
            int(re.search(r"goto -> bb(\d+)", x)[1])
            for x in blocks[0]
            if "goto ->" in x
        )
        lookup = select(lambda text: "WorkItem]>::get::<usize>" in text)
        decide = returned(lookup)
        select_item = blocks[decide][-1]
        boundary = int(re.search(r"0: bb(\d+)", select_item)[1])
        dispatch = int(re.search(r"1: bb(\d+)", select_item)[1])
        increment = select(
            lambda text: "Ordering::AcqRel;" in text and "fetch_add(" in text
        )
        reducer = select(
            lambda text: (
                (
                    "::reduce::<N>("
                    if helper
                    else "ForsSplitMeta> as IntoIterator>::into_iter"
                )
                in text
            )
        )
        publish = (
            select(lambda text: "::publish(" in text) if helper else acquire_lock()
        )
        after = returned(publish) if helper else after_publish()
        if helper and (returned(dispatch) != increment or returned(reducer) != publish):
            raise ValueError("unexpected outlined call continuation")
        item = only(re.findall(r"debug item => (_\d+);", body))
        d = blocks[dispatch]
        if not helper and ("discriminant((" + item + ".1:" not in " ".join(d)):
            raise ValueError("wrong WorkItem scrutinee")
        index = next(
            j
            for j, line in enumerate(d)
            if line.strip().startswith(item + " = copy (*")
        )
        blocks[dispatch] = d[: index + 1] + [f"dispatch({item}) -> bb{increment};"]
        blocks[reducer] = [f"reduce -> bb{publish};"]
        blocks[publish] = [f"publish -> bb{after};"]
        if not helper:
            if any(
                not re.fullmatch(r"_\d+ = const false;|goto -> bb\d+;", s.strip())
                for s in blocks[after]
            ):
                raise ValueError("unexpected post-publication code")
            blocks[after] = [blocks[after][-1]]
        blocks[boundary] = ["await readiness;"]
    elif region == "wait":
        entry = (
            0
            if helper
            else select(
                lambda text: (
                    re.search(r"_\d+ = const 0_u32;\s+goto ->", text) is not None
                )
            )
        )
        boundary = (
            select(lambda text: "_0 = const true;" in text)
            if helper
            else select(
                lambda text: "OnceLock::<alloc::vec::Vec<[u8; N]>>::get(" in text
            )
        )
        if helper and (
            len(blocks[boundary]) != 2
            or blocks[int(BLOCK.search(blocks[boundary][-1])[1])][0].strip()
            != "return;"
        ):
            raise ValueError("unexpected READY return")
        blocks[boundary] = ["ready;"]
        abort = max(blocks) + 1
        blocks[abort] = ["aborted;"]
        # The source disarms its private AbortGuard before leaving. The helper
        # returns false to the caller, which disarms the same guard. Preserve
        # the MutexGuard drop on the parked path on both sides.
        aborts = []
        for k, lines in list(blocks.items()):
            first = lines[0].strip()
            pred = (
                first == "_0 = const false;"
                if helper
                else bool(re.fullmatch(r"\(_\d+\.3: bool\) = const false;", first))
            )
            if pred and not (
                not helper
                and len(lines) > 1
                and "drop(" in lines[1]
                and re.search(r"drop\((_\d+)\)", lines[1])[1] == LOCAL.search(first)[0]
            ):
                aborts.append(k)
        if len(aborts) != 2:
            raise ValueError("expected two aborted wait exits")
        for k in aborts:
            lines = blocks[k]
            if len(lines) != 2:
                raise ValueError("unexpected abort path")
            target = int(BLOCK.search(lines[-1])[1])
            if lines[-1].strip().startswith("drop("):
                blocks[k] = [
                    f"{lines[-1].strip().split(' -> ')[0]} -> [return: bb{abort}];"
                ]
            elif lines[-1].strip().startswith("goto ->"):
                blocks[k] = ["aborted;"]
            else:
                raise ValueError("unexpected abort terminator")
            # No further payload work after the abort exit, through return.
            seen = set()
            while target not in seen:
                seen.add(target)
                rest = [l.strip() for l in blocks[target]]
                if rest == ["return;"]:
                    break
                if not all(re.fullmatch(r"_\d+ = const false;", l) for l in rest[:-1]):
                    raise ValueError("work after aborted wait")
                if not (
                    rest[-1].startswith("goto ->")
                    or (
                        not helper
                        and rest[-1].startswith(
                            "drop(" + LOCAL.search(lines[0])[0] + ") ->"
                        )
                    )
                ):
                    raise ValueError("wrong abort continuation")
                target = int(BLOCK.search(rest[-1])[1])
            else:
                raise ValueError("cycle after abort")
    elif region == "wots":
        entry = (
            0
            if helper
            else select(
                lambda text: "OnceLock::<alloc::vec::Vec<[u8; N]>>::get(" in text
            )
        )
        if helper:
            boundary = select(lambda text: text == "return;")
        else:
            claim = select(
                lambda text: "OnceLock<alloc::vec::Vec<u8>>]>::get::<usize>" in text
            )
            switch = int(re.search(r"return: bb(\d+)", blocks[claim][-1])[1])
            boundary = int(re.search(r"0: bb(\d+)", blocks[switch][-1])[1])
            if not re.fullmatch(
                r"\(_\d+\.\d+: bool\) = const false;", blocks[boundary][0].strip()
            ):
                raise ValueError("exhausted WOTS path must disarm its guard")
    else:
        raise ValueError(region)
    if helper or region == "caller":
        args = {
            v: "$" + n
            for n, v in re.findall(r"^    debug (\w+) => (_\d+);", body, re.MULTILINE)
        }
    else:
        args = {}
        if region == "dispatch":
            item = only(
                re.findall(r"discriminant\(\((_\d+)\.1:", "\n".join(blocks[entry]))
            )
            args[item] = "$item"
    captures = {
        i: n for n, i in re.findall(r"debug (\w+) => \(\*\(\(\*_1\)\.(\d+):", body)
    }
    if not helper and region not in ("controller", "wait", "caller"):
        blocks[boundary] = ["return;"]

    def skip(k):
        seen = set()
        while (goto := re.fullmatch(r"goto -> bb(\d+);", blocks[k][0].strip())) and len(
            blocks[k]
        ) == 1:
            if k in seen:
                raise ValueError("silent control-flow cycle")
            seen.add(k)
            k = int(goto[1])
        return k

    reachable = [entry]
    ops = []
    nexts = []
    for k in reachable:
        lines = [v.strip() for v in blocks[k]]
        lines[-1] = re.sub(
            r", unwind(?:: bb\d+| continue| unreachable)\]", "]", lines[-1]
        )
        dests = [skip(int(b)) for b in BLOCK.findall(lines[-1])]
        for d in dests:
            if d not in reachable:
                reachable.append(d)
        ops.append(lines)
        nexts.append([reachable.index(d) for d in dests])
    count = Counter(
        m[1] for lines in ops for line in lines if (m := re.match(r"(_\d+) =", line))
    )
    # Drop flags that are never read on a normal path have no normal-path effect.
    read = {
        v
        for lines in ops
        for line in lines
        for v in LOCAL.findall(re.sub(r"^_\d+ = ", "", line))
    }
    locals_ = {}
    closures = {}
    graph = []
    for lines, edges in zip(ops, nexts):
        out = []
        for line in lines:
            flag = re.fullmatch(r"(_\d+) = const (?:true|false);", line)
            if flag and flag[1] not in read:
                continue
            m = re.fullmatch(r"(_\d+) = no_retag copy (.+);", line)
            if m and (cap := CAPTURE.fullmatch(m[2])):
                if count[m[1]] != 1:
                    raise ValueError("nonunique capture temporary")
                name = captures[cap[1]]
                args[m[1]] = ("&" if name in BY_VALUE else "") + "$" + name
                continue
            line = line.replace(
                "shake::slh::parallel::sign::PHASE", "shake::slh::parallel::PHASE"
            )
            line = LOCAL.sub(lambda m: args.get(m[0], m[0]), line)
            line = re.sub(r"\(\*&([$]\w+)\)", r"\1", line)
            # Copying a read-only input to a fresh temporary preserves its value.
            m = re.fullmatch(r"(_\d+) = (?:copy |&)([&$][$\w]+);", line)
            if m and count[m[1]] == 1:
                args[m[1]] = ("&" if " = &" in line else "") + m[2]
                continue
            line = re.sub(r"(?:copy|move) (&?\$\w+)", r"arg \1", line)
            line = LOCAL.sub(
                lambda m: "v" + str(locals_.setdefault(m[0], len(locals_))), line
            )
            line = CLOSURE.sub(
                lambda m: "callback" + str(closures.setdefault(m[0], len(closures))),
                line,
            )
            line = BLOCK.sub("target", line)
            out.append(line)
        graph.append((out, edges))
    return graph, list(closures)


def callbacks(mir, names):
    """Use the closure type at each call site to resolve and compare its body."""
    result = []
    for capture in names:
        matches = re.findall(
            r"\nfn [^\n]+\(_1: (?:&mut |&)?"
            + re.escape(capture)
            + r"(, [^\n]+\{\n.*?\n)\}",
            mir,
            re.DOTALL,
        )
        result.append(only(matches).replace(capture, "Self"))
    return result


def graph_witness(left, right, name):
    # Use one literal dictionary for both sides. Distinct MIR operations never
    # get the same label, even if they occur in corresponding blocks.
    alphabet = {}

    def encode(graph):
        return (
            "["
            + ",".join(
                f"⟨{alphabet.setdefault(tuple(ops), len(alphabet))},{edges}⟩"
                for ops, edges in graph
            )
            + "]"
        )

    return f"""private def {name}Prod : Graph := {encode(left)}
private def {name}Lift : Graph := {encode(right)}
theorem {name}_runs {{S E : Type}} (eval : Nat → S → Nat → List E → S → Prop)
    (pc : Nat) (s : S) (log : List E) (finish : Nat) (final : S) :
    Run eval {name}Prod pc s log finish final ↔ Run eval {name}Lift pc s log finish final :=
  same_runs (by rfl) eval pc s log finish final
#print axioms {name}_runs
"""


def call_arguments(text, wrapper):
    """Trace copies and shared captures into the outlined call, in ABI order."""
    name = "shake::slh::parallel::"
    driver = function(text, name + "flat_worker")
    params = lambda body: dict(
        re.findall(r"^    debug (\w+) => (_\d+);", body, re.MULTILINE)
    )
    captures = {
        i: n for n, i in re.findall(r"debug (\w+) => \(\*\(\(\*_1\)\.(\d+):", wrapper)
    }
    origins = {}
    for line in block_map(wrapper)[0]:
        if m := re.fullmatch(r"(_\d+) = no_retag copy (.+);", line.strip()):
            origins[m[1]] = captures[CAPTURE.fullmatch(m[2])[1]]
        elif m := re.fullmatch(r"(_\d+) = copy \(\*(_\d+)\);", line.strip()):
            origins[m[1]] = origins[m[2]]

    def arguments(body, callee):
        actual = only(
            re.findall(re.escape(name + callee) + r"(?:::<N>)?\(([^()]*)\) ->", body)
        )
        return [re.fullmatch(r"(?:move|copy) (_\d+)", a)[1] for a in actual.split(", ")]

    def expected(body):
        header = body.split(") ->", 1)[0]
        argument_names = {v: k for k, v in params(body).items()}
        return [argument_names[v] for v in re.findall(r"(_\d+): ", header)]

    if [origins[v] for v in arguments(wrapper, "flat_worker")] != expected(driver):
        raise ValueError("worker capture argument order differs")
    local = {v: k for k, v in params(driver).items()}
    item = only(re.findall(r"debug item => (_\d+);", driver))
    local[item] = "item"
    for fn in ("dispatch", "reduce", "wait", "publish", "phase_two"):
        if [local[v] for v in arguments(driver, fn)] != expected(
            function(text, name + fn)
        ):
            raise ValueError(f"incorrect arguments to {fn}")


def check_wait_exit(driver):
    """Check the boolean returned by the wait helper controls WOTS and cleanup."""
    blocks = block_map(driver)

    def ret(lines):
        return int(re.search(r"return: bb(\d+)", lines[-1])[1])

    wait = only(v for v in blocks.values() if "::wait(" in v[-1])
    flag = re.match(r"(_\d+) =", wait[-1].strip())[1]
    branch = only(blocks[ret(wait)]).strip()
    paths = re.fullmatch(
        r"switchInt\(move " + flag + r"\) -> \[0: bb(\d+), otherwise: bb(\d+)\];",
        branch,
    )
    if not paths:
        raise ValueError("wait result does not control worker exit")
    wots = blocks[int(paths[2])]
    if "::phase_two::<N>(" not in wots[-1]:
        raise ValueError("ready worker did not enter WOTS")
    for exit_block in [int(paths[1]), ret(wots)]:
        disarm, drop = [s.strip() for s in blocks[exit_block]]
        guard = re.fullmatch(r"\((_\d+)\.3: bool\) = const false;", disarm)[1]
        if not drop.startswith(f"drop({guard}) ->") or blocks[ret([drop])] != [
            "return;"
        ]:
            raise ValueError("worker failed to disarm and release its guard")
    if "armed: const true" not in " ".join(blocks[0]):
        raise ValueError("worker guard must start armed")
