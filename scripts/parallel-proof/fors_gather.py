"""Verify the two gather fragments with arbitrary prior scratch and an arbitrary physical row."""

from pathlib import Path
import re
from build import SRC, compile_probe, function
import subtree

bv = subtree.bv
HERE = Path(__file__).resolve().parent


def build(directory, source):
    tree = function(source, "fors_subtree_horiz")
    template = (
        (HERE / "fors-gather.rs")
        .read_text()
        .replace("ADDRESS_PATH", str(SRC / "address.rs"))
    )
    shared, macro = template.split("macro_rules! capture")
    code = shared
    for name, bound in [("carry", "8"), ("flush", "count")]:
        regex = rf"(?:let row = buf\[h\];\s*)?for k in 0\.\.{bound} \{{[^{{}}]*?\}}"
        matches = re.findall(regex, tree)
        if len(matches) != 1:
            raise ValueError(f"unexpected FORS {name} gather")
        code += "macro_rules! " + name + macro.replace("GATHER_BODY", matches[0])
        for n in (16, 24, 32):
            code += f"\n{name}!({name}{n}, {n});\n"
    return compile_probe(directory, code)


def check_output_frame(st, out, n):
    stack = st.solver.eval_one(st.regs.rsp)

    def frame(state):
        address, length = (
            state.inspect.mem_write_address,
            state.inspect.mem_write_length,
        )
        if not isinstance(address, int):
            if address.symbolic:
                raise ValueError("data-dependent write address")
            address = address.concrete_value
        if length is None:
            length = state.inspect.mem_write_expr.size() // 8
        if not isinstance(length, int):
            if length.symbolic:
                raise ValueError("data-dependent write size")
            length = length.concrete_value
        if not (
            out <= address <= out + n - length
            or stack - 0x40000 <= address <= stack - length
        ):
            raise ValueError("write outside the output and local stack frame")

    st.inspect.b("mem_write", when=subtree.angr.BP_BEFORE, action=frame)


def check(args):
    binary, n, h, label = args
    p = subtree.project_for(binary)
    out, src, tmp, tags, stop = 0x710000, 0x720000, 0x730000, 0x740000, 0x750000
    row = [bv.BVS("child", 8 * n) for _ in range(16)]
    left, right = ([bv.BVS("old", 8 * n) for _ in range(8)] for _ in range(2))
    fields = [[bv.BVS("word", 32) for _ in range(7)] for _ in range(9)]
    base, lvl = bv.BVS("base", 32), bv.BVS("level", 32)

    def address(a, suffix):
        return bv.Concat(a[0], bv.BVV(0, 32), *a[1:5], *suffix)

    for name, count in [("carry", 8), ("flush", 2), ("flush", 4)]:
        st = p.factory.call_state(
            p.loader.find_symbol(name + str(n)).rebased_addr,
            out,
            src,
            tmp,
            tags,
            h,
            count,
            base,
            lvl,
            ret_addr=stop,
            prototype="void f(void*,void*,void*,void*,size_t,size_t,unsigned,unsigned)",
            add_options={
                subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
                subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            },
        )
        for j, x in enumerate(row):
            st.memory.store(src + (16 * h + j) * n, x)
        for j, x in enumerate(left + right):
            st.memory.store(tmp + j * n, x)
        for j, words in enumerate(fields):
            st.memory.store(tags + 28 * j, bv.Concat(*(x.reversed for x in words)))
        check_output_frame(st, out, 8 * (32 + 2 * n))
        expected = []
        for k in range(8):
            if k < count:
                expected.extend(
                    [address(fields[8], (lvl, base + k)), row[2 * k], row[2 * k + 1]]
                )
            else:
                expected.extend([address(fields[k], fields[k][5:]), left[k], right[k]])
        stream = iter([("return", (), bv.Concat(*expected))])
        subtree.execute(
            p,
            st,
            out,
            stop,
            stream,
            8,
            f"FORS {label} {name} n={n} row={h} lanes={count}",
            report=False,
        )
