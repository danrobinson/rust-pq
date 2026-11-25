# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check all permutation inputs and outputs of SIMD cached WOTS leaves and FORS nodes."""

import argparse
import concurrent.futures
import runpy
import sys
import tempfile
import textwrap
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))

import angr
import claripy as bv
from active import check as check_short_or_pair
from build import SRC, compile_probe, function
from subtree import execute, project_for, word_row, zeros


def compile_cache(folder, width, mutation=None):
    source = (SRC / "cache.rs").read_text().split("    mod simd {", 1)[1]
    source = textwrap.dedent(source.split("\n    }\n", 1)[0])
    if mutation is not None:
        old, new = mutation
        if source.count(old) != 1:
            raise ValueError("could not locate the Rust mutation")
        source = source.replace(old, new)
    functions = [
        function(source, name)
        for name in (
            "word",
            "header",
            "put",
            "read",
            "short",
            "pair",
            "wots_pk_gen_batch",
        )
    ]
    # Cut only the two recursive edges. Each arbitrary child result represents
    # the induction hypothesis at level - 1, with all call arguments checked.
    nodes = function(source, "fors_nodes")
    if nodes.count("= fors_nodes(") != 2:
        raise ValueError("unexpected recursive FORS edges")
    functions.extend(
        [
            function(source, "fors_secrets"),
            nodes.replace("= fors_nodes(", "= child(").replace(
                "fn fors_nodes<", "pub(super) fn fors_nodes<", 1
            ),
        ]
    )
    functions.append("""
    extern "C" {
        fn proof_child(result:*mut u8,sk:*const u8,seed:*const u8,addr:*const u8,
                       indices:*const u32,level:u32);
    }
    fn child<const N:usize>(sk:&[u8;N], seed:&[u8;N], addr:Adrs,
                            indices:[u32;WIDTH], level:u32) -> [[u8;N];WIDTH] {
        let mut out=[[0u8;N];WIDTH];
        unsafe { proof_child(out.as_mut_ptr().cast(), sk.as_ptr(),seed.as_ptr(),
                             addr.full().as_ptr(),indices.as_ptr(),level); }
        out
    }
    """)
    # Expose the allocated output slice at the verification boundary. Preserve
    # its Rust-computed length, zero initialization and every indexed write.
    sign = function(source, "fors_sign")
    replacements = [
        ("addr: Adrs,\n) -> Vec<u8> {", "addr: Adrs, buffer: &mut [u8],\n) {"),
        (
            "let mut sig = vec![0u8; selections.len() * stride];",
            "let sig = &mut buffer[..selections.len() * stride]; sig.fill(0);",
        ),
        ("let siblings = fors_nodes(", "let siblings = child("),
        ("\n    sig\n}", "\n}"),
    ]
    for old, new in replacements:
        if sign.count(old) != 1:
            raise ValueError("unrecognized cached FORS signing boundary: " + old)
        sign = sign.replace(old, new)
    functions.append(sign)
    # Expose the exact stream handed to digest, substituting a byte collector
    # for the already checked incremental sponge. Lower each lane's selection
    # to its proved equivalent mask to keep symbolic parities out of pointers.
    recovery = function(source, "fors_pk_from_sig")
    for even, odd in (("values", "siblings"), ("siblings", "values")):
        original = (
            "if indices[lane] & 1 == 0 {\n                    "
            + even
            + "[lane]\n                } else {\n                    "
            + odd
            + "[lane]\n                }"
        )
        if recovery.count(original) != 1:
            raise ValueError("unexpected FORS parity expression")
        recovery = recovery.replace(
            original, f"select(indices[lane], {even}[lane], {odd}[lane])"
        )
    for old, new in (
        (") -> [u8; N] {", ") -> super::Sponge {"),
        ("super::digest(pk)", "pk"),
    ):
        if recovery.count(old) != 1:
            raise ValueError("unexpected FORS recovery output")
        recovery = recovery.replace(old, new)
    functions.extend(
        [
            recovery,
            """
    fn select<const N:usize>(index:u32, even:[u8;N], odd:[u8;N]) -> [u8;N] {
        let mask=0u8.wrapping_sub((index & 1) as u8);
        core::array::from_fn(|i| (even[i] & !mask) | (odd[i] & mask))
    }""",
        ]
    )
    probe = (HERE / "parallel-proof/probe.rs").read_text()
    layout = (SRC / "shake256/parallel.rs").read_text()
    layout = layout[
        layout.index('#[cfg(target_arch = "x86_64")]') : layout.index("/// One copy")
    ]
    if width == 3:
        layout = layout.replace('target_arch = "x86_64"', "any()").replace(
            'all(target_arch = "aarch64", not(target_vendor = "apple"))', "all()"
        )
    probe = probe.replace(
        "use crate::params::{LEN2, W}", "use crate::params::{LEN2, W, Params}"
    )
    probe = probe.replace("Adrs, WOTS_HASH", "Adrs, FORS_PRF, WOTS_HASH").replace(
        "// PRODUCTION_LAYOUT", layout
    )
    probe = probe.replace(
        "// PRODUCTION_HELPERS",
        "\n".join(functions)
        + """
    pub(super) fn hash<const N:usize>(seed:&[u8;N], a:&[Adrs;WIDTH], l:&[[u8;N];WIDTH],
                                      r:&[[u8;N];WIDTH], op:u32) -> [[u8;N];WIDTH] {
        if op == 0 { short(seed,a,l) } else { pair(seed,a,l,r) }
    }""",
    )
    cache_source = (SRC / "cache.rs").read_text().split("mod shake_ops {", 1)[1]

    read_body = runpy.run_path(str(HERE / "check-cache-build.py"))["body"]
    probe += (
        "\n"
        + read_body(cache_source, "start")
        + """
struct Sponge { bytes:[u8;1200], len:usize }
impl Sponge {
    fn new()->Self { Self { bytes:[0;1200],len:0 } }
    fn absorb(&mut self, data:&[u8]){
        self.bytes[self.len..self.len+data.len()].copy_from_slice(data);
        self.len+=data.len();
    }
}
use address::Adrs;
"""
    )
    probe = probe.replace(
        "use crate::params::{LEN2, W, Params};",
        "use crate::{address::FORS_ROOTS,block}; use crate::params::{LEN2, W, Params};",
    )
    probe += "\n" + read_body((SRC / "util.rs").read_text(), "block")
    for name in ("address", "params"):
        probe = probe.replace(name.upper() + "_PATH", str(SRC / (name + ".rs")))
    for n in (16, 24, 32):
        probe += f"""
#[no_mangle] pub extern "C" fn keygen{n}(out:&mut [[u8;{n}];{width}], sk:&[u8;{n}],
    seed:&[u8;{n}], fields:&[u8;32], keys:&[u32;{width}]) {{
    *out=batch::wots_pk_gen_batch(sk,seed,decode(fields),*keys)
}}
#[no_mangle] pub extern "C" fn node{n}(out:&mut [[u8;{n}];{width}], sk:&[u8;{n}],
    seed:&[u8;{n}], fields:&[u8;32], keys:&[u32;{width}], height:u32) {{
    *out=batch::fors_nodes(sk,seed,decode(fields),*keys,height)
}}
#[no_mangle] pub extern "C" fn active{n}(out:&mut [[u8;{n}];{width}], seed:&[u8;{n}],
    fields:&[[u8;32];{width}], l:&[[u8;{n}];{width}], r:&[[u8;{n}];{width}], _active:usize, op:u32) {{
    *out=batch::hash(seed,&fields.map(|f|decode(&f)),l,r,op)
}}"""
        for speed in ("S", "F"):
            probe += f"""
#[no_mangle] pub extern "C" fn recover{n}{speed}(out:*mut u8, sig:*const u8,seed:&[u8;{n}],
    fields:&[u8;32],keys:*const u32) {{
    let p=&params::SHA2_{8 * n}{speed};
    let k=p.k as usize;
    let sel=unsafe {{core::slice::from_raw_parts(keys,k)}};
    let sig=unsafe {{core::slice::from_raw_parts(sig,k*(1+p.a as usize)*{n})}};
    let sponge=batch::fors_pk_from_sig(p,sel,sig,seed,decode(fields));
    let result=unsafe {{core::slice::from_raw_parts_mut(out, {n}+32+k*{n})}};
    result.copy_from_slice(&sponge.bytes[..sponge.len]);
}}
#[no_mangle] pub extern "C" fn sign{n}{speed}(out:*mut u8, sk:&[u8;{n}],seed:&[u8;{n}],
    fields:&[u8;32],keys:*const u32) {{
    let p=&params::SHA2_{8 * n}{speed};
    let k=p.k as usize;
    let sel=unsafe {{ core::slice::from_raw_parts(keys,k) }};
    let data=unsafe {{core::slice::from_raw_parts_mut(out,k*(1+p.a as usize)*{n})}};
    batch::fors_sign(p,sel,sk,seed,decode(fields),data)
}}"""
    probe += """
fn decode(f:&[u8;32]) -> address::Adrs {
    let word=|i:usize|u32::from_be_bytes(f[i..i+4].try_into().unwrap());
    address::Adrs {layer:word(0),tree:u64::from_be_bytes(f[8..16].try_into().unwrap()),
        typ:word(16),keypair:word(20),word2:word(24),word3:word(28)}
}"""
    return compile_probe(folder, probe)


def pad(message):
    size = message.size() // 8
    if size == 135:
        return bv.Concat(message, bv.BVV(0x9F, 8), zeros(64))
    return bv.Concat(
        message, bv.BVV(0x1F, 8), zeros(134 - size), bv.BVV(128, 8), zeros(64)
    )


def rows(messages):
    return [word_row(messages, j) for j in range(25)]


def result(width):
    return [bv.BVS("permutation", 64 * width) for _ in range(25)]


def prefixes(n, width, permuted):
    return [
        bv.Concat(*(row.get_bytes(lane * 8, 8) for row in permuted[: n // 8]))
        for lane in range(width)
    ]


def vector_hash(n, width, seed, addresses, payloads):
    blocks = [
        pad(bv.Concat(seed, addr, data))
        for addr, data in zip(addresses, payloads, strict=True)
    ]
    output = result(width)
    yield "permute", rows(blocks), output
    return prefixes(n, width, output)


def wots_transcript(n, width, sk, seed, fields, keys):
    """FIPS WOTS_PK absorbs every endpoint in order with SHAKE256's 136-byte rate."""

    def address(lane, domain, chain=0, step=0):
        return bv.Concat(
            fields.get_bytes(0, 4),
            zeros(4),
            fields.get_bytes(8, 8),
            bv.BVV(domain, 32),
            keys[lane],
            bv.BVV(chain, 32),
            bv.BVV(step, 32),
        )

    sponge = [zeros(8 * width)] * 25
    pending = [bv.Concat(seed, address(lane, 1)) for lane in range(width)]
    for chain in range(2 * n + 3):
        blocks = [
            pad(bv.Concat(seed, address(lane, 5, chain), sk)) for lane in range(width)
        ]
        output = result(width)
        yield "permute", rows(blocks), output
        for step in range(15):
            blocks = [
                pad(bv.Concat(seed, address(lane, 0, chain, step), value))
                for lane, value in enumerate(prefixes(n, width, output))
            ]
            output = result(width)
            yield "permute", rows(blocks), output
        pending = [
            bv.Concat(old, value) if old is not None else value
            for old, value in zip(pending, prefixes(n, width, output))
        ]
        size = pending[0].size() // 8
        if size >= 136:
            blocks = [bv.Concat(buf.get_bytes(0, 136), zeros(64)) for buf in pending]
            inputs = [old ^ new for old, new in zip(sponge, rows(blocks))]
            sponge = result(width)
            yield "permute", inputs, sponge
            pending = [
                buf.get_bytes(136, size - 136) if size > 136 else None
                for buf in pending
            ]
    # Zero residual bytes require a fresh padded block as well.
    blocks = [
        pad(buf)
        if buf is not None
        else bv.Concat(bv.BVV(31, 8), zeros(134), bv.BVV(128, 8), zeros(64))
        for buf in pending
    ]
    output = result(width)
    yield "permute", [old ^ new for old, new in zip(sponge, rows(blocks))], output
    yield "return", (), bv.Concat(*prefixes(n, width, output))


def node_transcript(n, width, sk, seed, fields, keys, height):
    address = bv.Concat(fields.get_bytes(0, 4), zeros(4), fields.get_bytes(8, 24))

    def addresses(domain, z):
        return [
            bv.Concat(
                address.get_bytes(0, 16),
                domain,
                address.get_bytes(20, 4),
                bv.BVV(z, 32),
                key,
            )
            for key in keys
        ]

    if height == 0:
        payload = yield from vector_hash(
            n, width, seed, addresses(bv.BVV(6, 32), 0), [sk] * width
        )
    else:
        children = []
        for side in (0, 1):
            packed = bv.Concat(*((2 * key + side).reversed for key in keys))
            child = bv.BVS("child", width * n * 8)
            yield "child", (sk, seed, address, packed, height - 1), child
            children.append(child)
        payload = [
            bv.Concat(*(child.get_bytes(lane * n, n) for child in children))
            for lane in range(width)
        ]
    values = yield from vector_hash(
        n, width, seed, addresses(address.get_bytes(16, 4), height), payload
    )
    yield "return", (), bv.Concat(*values)


def check_generator(project, n, width, height=None):
    out, secret, public, field_ptr, key_ptr, stop = (
        0x710000 + i * 0x10000 for i in range(6)
    )
    sk, seed = (bv.BVS(label, 8 * n) for label in ("secret", "seed"))
    fields = bv.BVS("address", 256)
    index_bits = 32 - (height or 0)
    keys = [
        bv.ZeroExt(32 - index_bits, bv.BVS("key_index", index_bits))
        for _ in range(width)
    ]
    name = "keygen" if height is None else "node"
    extra = () if height is None else (height,)
    signature = (
        "void f(void*,void*,void*,void*,void*"
        + ("" if height is None else ",unsigned")
        + ")"
    )
    state = project.factory.call_state(
        project.loader.find_symbol(f"{name}{n}").rebased_addr,
        out,
        secret,
        public,
        field_ptr,
        key_ptr,
        *extra,
        ret_addr=stop,
        prototype=signature,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    for ptr, value in (
        (secret, sk),
        (public, seed),
        (field_ptr, fields),
        (key_ptr, bv.Concat(*(key.reversed for key in keys))),
    ):
        state.memory.store(ptr, value)
    expected = (
        wots_transcript(n, width, sk, seed, fields, keys)
        if height is None
        else node_transcript(n, width, sk, seed, fields, keys, height)
    )
    execute(
        project,
        state,
        out,
        stop,
        expected,
        width,
        f"cached {name} n={n} width={width} height={height}",
    )


def sign_transcript(n, width, sk, seed, fields, selections, height):
    stride = height + 1
    signature = [None] * (stride * len(selections))
    address = bv.Concat(fields.get_bytes(0, 4), zeros(4), fields.get_bytes(8, 24))
    for first in range(0, len(selections), width):
        active = min(width, len(selections) - first)
        trees = [first + min(lane, active - 1) for lane in range(width)]
        indices = [selections[tree] + tree * (1 << height) for tree in trees]
        prfs = [
            bv.Concat(
                address.get_bytes(0, 16),
                bv.BVV(6, 32),
                address.get_bytes(20, 4),
                zeros(4),
                index,
            )
            for index in indices
        ]
        secrets = yield from vector_hash(n, width, seed, prfs, [sk] * width)
        for lane in range(active):
            signature[trees[lane] * stride] = secrets[lane]
        for level in range(height):
            # FIPS Algorithm 16 indexes the tree and local sibling separately.
            siblings = [
                tree * (1 << (height - level)) + (bv.LShR(selections[tree], level) ^ 1)
                for tree in trees
            ]
            packed = bv.Concat(*(idx.reversed for idx in siblings))
            nodes = bv.BVS("siblings", width * n * 8)
            yield "child", (sk, seed, address, packed, level), nodes
            for lane in range(active):
                signature[trees[lane] * stride + level + 1] = nodes.get_bytes(
                    lane * n, n
                )
    yield "return", (), bv.Concat(*signature)


def recover_transcript(n, width, signature, seed, fields, selections, height):
    addr = bv.Concat(fields.get_bytes(0, 4), zeros(4), fields.get_bytes(8, 24))
    roots = []

    for first in range(0, len(selections), width):
        active = min(width, len(selections) - first)
        trees = [first + min(lane, active - 1) for lane in range(width)]
        leaves = [tree * (1 << height) + selections[tree] for tree in trees]

        def addresses(level):
            return [
                bv.Concat(
                    addr.get_bytes(0, 24), bv.BVV(level, 32), bv.LShR(leaf, level)
                )
                for leaf in leaves
            ]

        def field(level):
            return [
                signature.get_bytes((tree * (height + 1) + level) * n, n)
                for tree in trees
            ]

        vals = yield from vector_hash(n, width, seed, addresses(0), field(0))
        for level in range(height):
            payloads = []
            for tree, value, sibling in zip(trees, vals, field(level + 1), strict=True):
                mask = bv.SignExt(n * 8 - 1, selections[tree][level:level])
                left = (value & ~mask) | (sibling & mask)
                right = (sibling & ~mask) | (value & mask)
                payloads.append(bv.Concat(left, right))
            vals = yield from vector_hash(
                n, width, seed, addresses(level + 1), payloads
            )
        roots.extend(vals[:active])
    root_address = bv.Concat(
        addr.get_bytes(0, 16), bv.BVV(4, 32), addr.get_bytes(20, 4), zeros(8)
    )
    yield "return", (), bv.Concat(seed, root_address, *roots)


def check_mask():
    index, a, b = bv.BVS("idx", 32), bv.BVS("even", 8), bv.BVS("odd", 8)
    mask = -(index[7:0] & 1)
    if bv.Solver().satisfiable(
        extra_constraints=[((a & ~mask) | (b & mask)) != bv.If((index & 1) == 0, a, b)]
    ):
        raise ValueError("parity lowering differs from the production conditional")


def check_fors_sign(project, n, width, speed, k, height, recover=False):
    out, secret, public, field_ptr, indices, stop = (
        0x710000 + i * 0x10000 for i in range(6)
    )
    sk, seed = (bv.BVS(label, 8 * n) for label in ("secret", "seed"))
    fields = bv.BVS("address", 256)
    selections = [
        bv.ZeroExt(32 - height, bv.BVS("selected_leaf", height)) for _ in range(k)
    ]
    operation = "recover" if recover else "sign"
    entry = project.loader.find_symbol(f"{operation}{n}{speed}").rebased_addr
    state = project.factory.call_state(
        entry,
        out,
        secret,
        public,
        field_ptr,
        indices,
        ret_addr=stop,
        prototype="void f(void*,void*,void*,void*,void*)",
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    signature = None
    if recover:
        fields_in_signature = [
            bv.BVS("signature_field", n * 8) for _ in range(k * (height + 1))
        ]
        signature = bv.Concat(*fields_in_signature)
        # angr 9.2.213 can restart a large symbolic concatenation at the next
        # page boundary during a bulk store. Keep the oracle separate from the
        # memory image, and verify that the image contains every original field.
        for j, field in enumerate(fields_in_signature):
            start = secret + j * n
            for i in range(n):
                state.memory.store(start + i, field.get_byte(i))
        for j, field in enumerate(fields_in_signature):
            actual = state.memory.load(secret + j * n, n)
            if actual is not field and state.solver.satisfiable(
                extra_constraints=[actual != field]
            ):
                raise ValueError(f"symbolic signature input corruption at field {j}")
    else:
        state.memory.store(secret, sk)
    for ptr, value in (
        (public, seed),
        (field_ptr, fields),
        (indices, bv.Concat(*(v.reversed for v in selections))),
    ):
        state.memory.store(ptr, value)
    execute(
        project,
        state,
        out,
        stop,
        (
            recover_transcript(n, width, signature, seed, fields, selections, height)
            if recover
            else sign_transcript(n, width, sk, seed, fields, selections, height)
        ),
        width,
        f"cached FORS {operation} n={n}{speed} width={width}",
    )


def check_set(args):
    image, width, n = args
    project = project_for(image)
    for op in (0, 1):
        check_short_or_pair(width, project, n, width, op)
    check_generator(project, n, width)
    for height in range(15):
        check_generator(project, n, width, height)
    geometries = {
        16: ((14, 12), (33, 6)),
        24: ((17, 14), (33, 8)),
        32: ((22, 14), (35, 9)),
    }
    for speed, (k, height) in zip(("S", "F"), geometries[n], strict=True):
        check_fors_sign(project, n, width, speed, k, height)
        check_fors_sign(project, n, width, speed, k, height, recover=True)


def main(workers):
    check_mask()
    with tempfile.TemporaryDirectory() as tmp:
        jobs = []
        for width in (3, 8):
            folder = Path(tmp) / str(width)
            folder.mkdir()
            image = compile_cache(folder, width)
            jobs.extend((image, width, n) for n in (16, 24, 32))
        if workers == 1:
            for job in jobs:
                check_set(job)
        else:
            with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
                list(pool.map(check_set, jobs))

    for old, new, height in (
        (
            "let id = u64::from((chain as u32).swap_bytes());",
            "let id = u64::from((chain as u32 + 1).swap_bytes());",
            None,
        ),
        (
            "pair(seed, &addresses, &left, &right)\n",
            "pair(seed, &addresses, &right, &left)\n",
            1,
        ),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            project = project_for(compile_cache(Path(tmp), 3, (old, new)))
            try:
                check_generator(project, 16, 3, height)
            except ValueError as exc:
                if "mismatch at call" not in str(exc):
                    raise
                print(f"Rejected production mutation: {new}", flush=True)
            else:
                raise ValueError(f"mutation survived: {new}")

    with tempfile.TemporaryDirectory() as tmp:
        mutation = (
            "block(sig, tree * stride + j as usize + 1)",
            "block(sig, tree * stride + j as usize)",
        )
        project = project_for(compile_cache(Path(tmp), 3, mutation))
        try:
            check_fors_sign(project, 24, 3, "S", 17, 14, recover=True)
        except ValueError as exc:
            if "mismatch at call" not in str(exc):
                raise
            print("Rejected shifted FORS signature authentication path", flush=True)
        else:
            raise ValueError("shifted FORS authentication path survived")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--jobs",
        type=int,
        choices=range(1, 7),
        default=1,
        help="number of independent layout/size proofs to run concurrently",
    )
    main(parser.parse_args().jobs)
