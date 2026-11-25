#!/usr/bin/env python3
"""Check production Metal value operations using symbolic messages and compression results."""

import concurrent.futures
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CBMC = (
    os.environ.get("CBMC")
    or shutil.which("cbmc")
    or str(Path.home() / ".kani/kani-0.68.0/bin/cbmc")
)
MODEL = (HERE / "metal-proof/values.cpp").read_text()


def definition(source, name):
    pattern = r"(?:template\s*<[^>]+>\s*)?inline\s+\w+\s+" + name + r"\s*\("
    (match,) = re.finditer(pattern, source)
    end = source.index("\n}", match.end()) + 2
    return source[match.start() : end]


def address_only(body, variables):
    """A rebased offset may only be added once to a device index, or to
    another rebased offset. Its absolute value cannot influence a hash or branch."""
    body = re.sub(r"//[^\n]*|/\*.*?\*/", "", body, flags=re.S)
    names = r"\b(?:" + "|".join(variables) + r")\b"

    def linear(expr):
        used = re.findall(names, expr)
        if used and (
            len(used) != 1
            or not re.fullmatch(r"\s*" + used[0] + r"\s*(?:\+\s*[\w\s+*().]+)?", expr)
        ):
            raise ValueError("non-additive rebased offset: " + expr)

    def declaration(m):
        if m[1] not in variables:
            return m[0]
        linear(m[2])
        return ""

    def access(m):
        linear(m[1])
        return "0"

    body = re.sub(r"uint32_t\s+(\w+)\s*=\s*([^;]+);", declaration, body)
    body = re.sub(
        r"\b(?:pk_fors|xmss_roots|chain_tips|fors_roots|out_chain_tips|out_leaves|out_pk_fors)\[([^\]]+)\]",
        access,
        body,
    )
    if re.search(names, body):
        raise ValueError("rebased offset escapes device address")


def program(family, n, change=None, op=None, nodes=0, geom=None):
    files = ROOT / "metal/shaders"
    sha = (files / "slhdsa.metal").read_text()
    shake = (files / "slhdsa_shake.metal").read_text()
    src = shake if family == "shake" else sha
    if change:
        before, after = change
        if src.count(before) != 1:
            raise ValueError("ambiguous negative control: " + before)
        src = src.replace(before, after)
    structs = sha[
        sha.index("constant uint32_t ADRS_WOTS_HASH") : sha.index(
            "// SHA-256", sha.index("struct WotsSignParams")
        )
    ]
    # Only source declarations (no compression arithmetic) before this marker.
    structs = structs[: structs.index("};", structs.index("struct WotsSignParams")) + 2]
    structs += "\n" + re.search(r"struct ShakeKeyMaterial\s*\{[^}]+\};", shake)[0]
    prefix = "shake_" if family == "shake" else ""
    names = (
        "bswap32 bswap64 store_le64 write_shake_node_bytes write_shake_node_bytes_tg "
        "adrs_full_lanes shake_thash_short shake_thash_pair shake_run_wots_chain "
        "shake_wots_digit_at shake_wots_sign_impl"
        if family == "shake"
        else "store_be32 write_node_bytes write_node_bytes_tg adrs_to_w256 thash_short_words "
        "thash_pair_words run_wots_chain wots_digit_at wots_sign_impl"
    )
    functions = [definition(src, name) for name in names.split()]
    if op in ("sign", "fused", "tips"):
        # The real chain is independently checked for arbitrary inputs at this
        # width. At the call site assert the full argument contract and return
        # arbitrary final words. This avoids duplicating 16 compression rounds.
        index = names.split().index(
            ("shake_" if family == "shake" else "") + "wots_digit_at"
        )
        functions[index] = (
            functions[index].split("{", 1)[0]
            + """{
            __CPROVER_assert(chain == ::chain, "digit belongs to this chain");
            for (uint i=0; i<words; ++i)
                __CPROVER_assert(msg[i] == signingMessage[i], "signs the specified layer message");
            return expectedDigit;
        }"""
        )
        idx = names.split().index(
            ("shake_" if family == "shake" else "") + "run_wots_chain"
        )
        header = functions[idx].split("{", 1)[0]
        seed = (
            "pk_seed[i] == key.pk_seed[i]"
            if family == "shake"
            else "seed_st[i] == key.state256[i]"
        )
        seed_len = "words" if family == "shake" else "8"
        if op != "sign":
            functions[idx] = (
                header
                + """{
              __CPROVER_assert(layer == ::layer && tree == ::tree && keypair == ::keypair &&
                   chain == (TIP_ONLY ? ::chain : tipCount) && steps == 15, "chain-tip address and step count");
              for (uint i=0;i<words;++i) {
                __CPROVER_assert(sk_seed[i]==input[i],"chain-tip secret seed");
                val[i] = streamData[chain*words+i];
              }
              for (uint i=0;i<"""
                + seed_len
                + """;++i)
                __CPROVER_assert("""
                + seed
                + """, "chain-tip public seed");
              ++tipCount;
            }"""
            )
        else:
            functions[idx] = (
                header
                + """{
          __CPROVER_assert(layer == ::layer && tree == ::tree && keypair == ::keypair &&
                           chain == ::chain, "WOTS chain address");
          for (uint i = 0; i < words; ++i) {
            __CPROVER_assert(sk_seed[i] == input[i], "WOTS chain secret seed");
            val[i] = previous[i] = arbitrary64();
          }
          for (uint i = 0; i < """
                + seed_len
                + """; ++i)
            __CPROVER_assert("""
                + seed
                + """, "WOTS chain public seed");
          calls += 1 + steps;
        }"""
            )
    if nodes:
        # The stream structs have only int/word operations and the compression
        # cutpoints below. Keep the complete bodies and the real stream caller.
        def struct(name):
            return re.search(r"struct " + name + r"\s*\{.*?\n\};", src, re.S)[0]

        stream = (
            struct("ShakeSponge")
            if family == "shake"
            else struct("TlenStream256") + "\n" + struct("TlenStream512")
        )
        functions += [
            stream,
            definition(
                src,
                ("shake_" if family == "shake" else "")
                + (
                    {
                        "tlen": "wots_tlen_impl",
                        "fused": "xmss_leaves_streaming_impl",
                        "tips": "wots_chains_impl",
                    }.get(op, "fors_pk_impl")
                ),
            ),
        ]
    options, driver = "", ""
    if geom:
        helper = runpy.run_path(str(HERE / "metal-proof/reducer_values.py"))
        options, driver = helper["reducer"](
            src, family, op, geom, definition, functions, names
        )
    # Peel off the base of a source-checked allocation so CBMC can reason
    # about its local words at arbitrary dispatch positions.
    bases = dict(
        keys="keyIndex",
        trees="treeIndex",
        layers="layerIndex",
        jobs="sigNumber",
        chain_tips="globalLeaf*chains*words",
        out_chain_tips="globalLeaf*chains*words",
        out_leaves="globalLeaf*words",
        fors_roots="sigNumber*STREAM_NODES*words",
        out_pk_fors="sigNumber*words",
        pk_fors="sigNumber*words",
        xmss_roots="sigNumber*layerCount*words",
    )
    selected_kernel = {
        "tips": "wots_chains",
        "tlen": "wots_tlen",
        "fused": "xmss_leaves_streaming",
        "sign": "wots_sign",
        "fors": "fors_pk",
    }.get(op, op)
    for i, func in enumerate(functions):
        if not re.search(r"\binline void \w+_impl\(", func):
            continue
        header, body = func.split("{", 1)
        # Instantiate the quotient/remainder projections of row-major gids
        # at arbitrary legal coordinates. MetalCommandValues.decode proves
        # each projection. Require its literal source expression before
        # substituting, so swapped radices cannot inherit this justification.
        coords = {
            "chain": ("gid % p.wots_len", "::chain"),
            "leaf_global": ("gid / p.wots_len", "globalLeaf"),
            "leaf_idx": (
                ("leaf_global" if op == "tips" else "gid") + " % p.leaves_per_tree",
                "::keypair",
            ),
            "tree_idx": (
                ("leaf_global" if op == "tips" else "gid") + " / p.leaves_per_tree",
                "treeIndex",
            ),
            "layer_global": ("gid / p.wots_len", "layerIndex"),
            "st_local": ("tg_id % p.subtrees_per_tree", "sub"),
            "tmp": ("tg_id / p.subtrees_per_tree", "sigNumber*K+treeNo"),
            "tree_i": (("tmp" if op == "fors_pass1" else "tg_id") + " % p.k", "treeNo"),
            "sig_idx": (
                ("tmp" if op == "fors_pass1" else "tg_id") + " / p.k",
                "sigNumber",
            ),
        }
        # Unused helper definitions need no coordinate specialization.
        fn = re.search(r"inline void (\w+)_impl", header)[1].removeprefix("shake_")
        if fn == selected_kernel:
            for var, (expr, coord) in coords.items():
                decl = re.search(r"uint32_t " + var + r"\s*=\s*([^;]+);", body)
                if decl:
                    if re.sub(r"\s+", "", decl[1]) != re.sub(r"\s+", "", expr):
                        raise ValueError("unverified dispatch coordinate: " + var)
                    body = body[: decl.start(1)] + coord + body[decl.end(1) :]
        recordBases = bases.copy()
        if fn == selected_kernel:
            active = {
                "wots_sign": "uint32_t total_chains = p.num_layers * p.wots_len; if (gid >= total_chains) return;",
                "wots_chains": "uint32_t total_chains = p.num_trees * p.leaves_per_tree * p.wots_len; if (gid >= total_chains) return;",
                "wots_tlen": "uint32_t total_leaves = p.num_trees * p.leaves_per_tree; if (gid >= total_leaves) return;",
                "xmss_leaves_streaming": "uint32_t total_leaves = p.num_trees * p.leaves_per_tree; if (gid >= total_leaves) return;",
                "fors_pk": "if (sig_idx >= p.num_sigs) return;",
                "xmss_reduce": "if (tg_id >= p.num_trees) return;",
                "fors_pass1": "uint32_t total_tgs = p.num_sigs * p.k * p.subtrees_per_tree; if (tg_id >= total_tgs) return;",
                "fors_pass2": "uint32_t total_trees = p.num_sigs * p.k; if (tg_id >= total_trees) return;",
            }[fn]

            def exact(text, replacement):
                nonlocal body
                tokens = re.findall(r"\w+|>=|[^\w\s]", text)
                pattern = r"\s*".join(re.escape(t) for t in tokens)
                body, count = re.subn(pattern, lambda _: replacement, body)
                if count != 1:
                    raise ValueError(
                        "unrecognized active-lane or base expression: " + text
                    )

            exact(active, "")
            # Normalize the base of each suballocation on both sides of its
            # pointer expression. Earlier source checks discharge all wrap and
            # allocation bounds. No cryptographic argument is rewritten.
            width = "NL" if prefix else "NW"
            if fn == "wots_sign":
                address_only(body, ("off",))
                exact("uint32_t off = desc.sig_idx * " + width + ";", "uint32_t off=0;")
                exact(
                    "uint32_t off=(desc.sig_idx*p.d+(desc.layer-1u))*" + width + ";",
                    "uint32_t off=(desc.layer-1u)*" + width + ";",
                )
                recordBases.update(pk_fors="0", xmss_roots="0")
            if fn in ("wots_tlen", "xmss_leaves_streaming", "wots_chains", "fors_pk"):
                offsets = (
                    ("out_off", "off", "tip_base")
                    if fn == "wots_tlen"
                    else (
                        ("out_off", "off", "root_base")
                        if fn == "fors_pk"
                        else ("out_off",)
                    )
                )
                address_only(body, offsets)
                if fn == "wots_tlen":
                    exact(
                        "uint32_t tip_base=gid*p.wots_len*" + width + ";",
                        "uint32_t tip_base=0;",
                    )
                    recordBases["chain_tips"] = "0"
                if fn == "fors_pk":
                    exact(
                        "uint32_t root_base=sig_idx*p.k*" + width + ";",
                        "uint32_t root_base=0;",
                    )
                    recordBases["fors_roots"] = "0"
                out = (
                    "out_chain_tips"
                    if fn == "wots_chains"
                    else "out_pk_fors"
                    if fn == "fors_pk"
                    else "out_leaves"
                )
                exact(
                    "uint32_t out_off="
                    + ("sig_idx" if fn == "fors_pk" else "gid")
                    + "*"
                    + width
                    + ";",
                    "uint32_t out_off="
                    + ("::chain*" + width if fn == "wots_chains" else "0")
                    + ";",
                )
                recordBases[out] = "0"
        for arr, base in recordBases.items():
            body = re.sub(r"\b" + arr + r"\[([^\]]+)\]", rf"{arr}[(\1)-({base})]", body)
        body = body.replace(
            "out_sigs + desc.wots_byte_off", "out_sigs + (desc.wots_byte_off - sigBase)"
        )
        functions[i] = header + "{" + body
    defs = "\n".join(functions)
    size = n // (8 if family == "shake" else 4)
    defs = re.sub(r"template\s*<uint (?:NW|NL)>", "", defs)
    defs = re.sub(r"<(?:NW|NL)>", "", defs)
    defs = re.sub(r"\b(?:NW|NL)\b", str(size), defs)
    return (
        options
        + f"#define TIP_ONLY {int(op == 'tips')}\n#define FUSED {int(op == 'fused')}\n#define STREAM_NODES {nodes}\n#define WOTS_STREAM {int(op in ('tlen', 'fused', 'tips'))}\n#define BYTES {n}\n#define words {size}\n#define chains {2 * n + 3}\n#define SHAKE {int(family == 'shake')}\n"
        + MODEL.replace("<words>", "")
        .replace("/* descriptor declarations */", structs)
        .replace("/* MSL definitions */", defs)
        + driver
    )


def check(folder, label, code, failure=None):
    path = folder / (label + ".cpp")
    path.write_text(code)
    proc = subprocess.run(
        [
            CBMC,
            str(path),
            "--object-bits",
            "16",
            "--unwind",
            ("550" if re.search(r"#define STREAM_NODES [1-9]", code) else "70"),
            "--unwinding-assertions",
            "--verbosity",
            "4",
        ],
        capture_output=True,
        text=True,
    )
    if failure:
        if proc.returncode == 10 and re.search(
            re.escape(failure) + r": FAILURE", proc.stdout
        ):
            return
    elif proc.returncode == 0 and "VERIFICATION SUCCESSFUL" in proc.stdout:
        return
    failed = [line for line in proc.stdout.splitlines() if ": FAILURE" in line]
    raise RuntimeError(
        label
        + "\n"
        + proc.stderr
        + "\n"
        + ("\n".join(failed) if failed else proc.stdout[-4000:])
    )


def controls(folder):
    try:
        program(
            "shake",
            16,
            (
                "sp.absorb_lane(chain_tips[tip_base + i]);",
                "sp.absorb_lane(chain_tips[2u * tip_base + i]);",
            ),
            "tlen",
            35,
        )
    except ValueError as exc:
        if "non-additive rebased offset" not in str(exc):
            raise
    else:
        raise ValueError("incorrectly scaled record base accepted")
    print("Rejected scaled stream record base", flush=True)

    cases = [
        (
            "bad-checksum",
            "shake",
            "digit",
            0,
            None,
            ("8u - 4u * c_idx", "4u * c_idx"),
            "FIPS message or checksum digit",
        ),
        (
            "bad-chain-domain",
            "sha2",
            "chain",
            0,
            None,
            ("w2 &= 0xFF00FFFFu", "w2 &= 0xFFFFFFFFu"),
            "FIPS SHA-256 block",
        ),
        (
            "bad-parent",
            "shake",
            "pair",
            0,
            None,
            ("st[2 * NL + 4 + i] = right[i]", "st[2 * NL + 4 + i] = left[i]"),
            "FIPS sponge input",
        ),
        (
            "bad-sibling",
            "sha2",
            "fors_pass1",
            0,
            (3, 6, 33),
            (
                "fors_tree_sig_off + n_bytes, leaf1",
                "fors_tree_sig_off + n_bytes, leaf0",
            ),
            "FIPS authentication or secret node value",
        ),
        (
            "bad-fors-subroot",
            "sha2",
            "fors_pass2",
            0,
            (3, 9, 35),
            (
                "lvl1, node1_word3, left, right, parent1",
                "lvl1, node1_word3, right, left, parent1",
            ),
            "ordered Merkle children",
        ),
        (
            "bad-xmss-parent",
            "shake",
            "xmss_reduce",
            0,
            (3, 6, 33),
            (
                "ADRS_TREE, 0u, lvl, tid, left, right, parent",
                "ADRS_TREE, 0u, lvl, tid+1, left, right, parent",
            ),
            "FIPS parent height and index",
        ),
        (
            "bad-fors-stream",
            "sha2",
            "fors",
            33,
            None,
            (
                "s.init(seed_st, 0u, job.idx_tree, ADRS_FORS_ROOTS",
                "s.init(seed_st, 0u, job.idx_tree, ADRS_WOTS_PK",
            ),
            "FIPS streaming SHA-256 block",
        ),
        (
            "bad-wots-tip",
            "shake",
            "fused",
            35,
            None,
            ("leaf_idx, c, 15u, tip", "leaf_idx, c, 14u, tip"),
            "chain-tip address and step count",
        ),
        (
            "bad-output-word",
            "sha2",
            "serialization",
            0,
            None,
            ("dst[2] = uint8_t(v >> 8);", "dst[2] = uint8_t(v >> 16);"),
            "FIPS node serialization",
        ),
        (
            "bad-final-public-key",
            "shake",
            "sign",
            0,
            None,
            ("msg[i] = pk_fors[off + i]", "msg[i] = ~pk_fors[off + i]"),
            "signs the specified layer message",
        ),
    ]
    for label, family, op, count, geom, change, failure in cases:
        code = program(family, 16, change, op, count, geom)
        entry = "reduction" if geom else "stream" if count else op
        check(folder, label, code + f"\nint main(){{check_{entry}();}}\n", failure)
        print("Rejected", label, flush=True)


def main():
    with (
        tempfile.TemporaryDirectory() as tmp,
        concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool,
    ):
        folder = Path(tmp)
        tasks = []
        for family in ("sha2", "shake"):
            for n in (16, 24, 32):
                for op in ("digit", "chain", "pair", "short", "sign", "serialization"):
                    label = f"{family}-{n}-{op}"
                    code = (
                        program(family, n, op=op)
                        + f"\nint main() {{ check_{op}(); }}\n"
                    )
                    tasks.append((label, pool.submit(check, folder, label, code)))
        rows = runpy.run_path(str(HERE / "check-metal-kernels.py"))["PARAM_SETS"]
        for family, n, op, count in sorted(
            {
                (row[1], row[2], op, row[7] if op == "fors" else 2 * row[2] + 3)
                for row in rows
                for op in ("fors", "tlen", "tips", "fused")
            }
        ):
            label = f"{family}-{n}-{op}-{count}"
            code = (
                program(family, n, op=op, nodes=count)
                + "\nint main(){ check_stream(); }\n"
            )
            tasks.append((label, pool.submit(check, folder, label, code)))
        for row in rows:
            _, family, n, _, _, hp, a, k, _ = row
            for op in ("xmss_reduce", "fors_pass1", "fors_pass2"):
                if op == "fors_pass2" and a <= 8:
                    continue
                label = row[0] + "-" + op
                code = (
                    program(family, n, op=op, geom=(hp, a, k))
                    + "\nint main(){check_reduction();}\n"
                )
                tasks.append((label, pool.submit(check, folder, label, code)))
        for label, task in tasks:
            task.result()
            print("Verified", label, flush=True)
        controls(folder)
        print(f"Verified {len(tasks)} source value cases.", flush=True)


if __name__ == "__main__":
    main()
