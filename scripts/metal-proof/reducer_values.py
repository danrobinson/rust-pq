"""Lift reducer word accesses into a universally quantified FIPS node table."""

import re
from pathlib import Path

SUPPORT = Path(__file__).resolve().parent


def reducer(src, family, name, geom, definition, functions, names):
    hp, a, k = geom
    prefix = "shake_" if family == "shake" else ""
    kernel = prefix + name + "_impl"
    source = definition(src, kernel)
    header, body = source.split("{", 1)
    body = re.sub(r"//[^\n]*|/\*.*?\*/", "", body, flags=re.S)
    # Only resource operations get virtualized; keep the entire shader control
    # flow and all local word arithmetic, copies, arguments and loop updates.
    for arr, op in (
        ("out_sub_roots", "publishRoot"),
        ("out_fors_roots", "publishRoot"),
        ("out_roots", "publishRoot"),
        ("tg_nodes", "storeShared"),
    ):
        body = re.sub(
            r"\b" + arr + r"\[([^\]]+)\]\s*=\s*([^;]+);", rf"{op}(\1,\2);", body
        )
    for arr, op in (
        ("leaves", "initialWord"),
        ("in_sub_roots", "initialWord"),
        ("tg_nodes", "sharedWord"),
    ):
        body = re.sub(r"\b" + arr + r"\[([^\]]+)\]", rf"{op}(\1)", body)
    body = re.sub(
        r"write_"
        + prefix
        + r"node_bytes_tg<\w+>\(out_sigs \+ (.*?),\s*tg_nodes \+ ([^;]+?)\);",
        r"signatureShared(\1,\2);",
        body,
        flags=re.S,
    )
    body = re.sub(
        r"write_" + prefix + r"node_bytes<\w+>\(out_sigs \+ ([^;]+?),\s*(\w+)\);",
        r"expectedOutput(\1,\2);",
        body,
    )
    if re.search(
        r"\b(tg_nodes|leaves|in_sub_roots|out_roots|out_sigs|out_fors_roots|out_sub_roots)\b",
        body,
    ):
        raise ValueError("unlifted reducer buffer access in " + kernel)
    body = body.replace(
        "threadgroup_barrier(mem_flags::mem_threadgroup)", "memoryBarrier()"
    )
    pair = "shake_thash_pair" if prefix else "thash_pair_words"
    body = re.sub(r"\b" + pair + r"<\w+>", "localPair", body)
    short = "shake_thash_short" if prefix else "thash_short_words"
    formals = "ad0,ad1,ad2,ad3" if prefix else "w0,w1,w2,w3,w4,w5_hi"
    seed = "pk_seed" if prefix else "seed_st"
    # Reuse the separately verified serializer/compression contract.
    proto = definition(src, short).split("{", 1)[0].replace(short, "reducerShort")
    functions += [
        (SUPPORT / "reducer-values.cpp").read_text(),
        proto
        + "{Word packed[]={"
        + formals
        + "}; leafShort("
        + seed
        + ",packed,in_val,out_val);}",
        header + "{" + body.replace(short + "<", "reducerShort<"),
    ]
    xmss, pass1 = name == "xmss_reduce", name == "fors_pass1"
    args = (
        "&key,&desc,0,0,0,xp,0,group,worker"
        if xmss
        else "&key,&job,0,0,fp,0,group,worker"
        if pass1
        else "&key,&job,0,0,0,fp,0,group,worker"
    )
    driver = (
        (SUPPORT / "reducer-driver.cpp")
        .read_text()
        .replace("RUN_REDUCER", kernel + "(" + args + ");")
    )
    constants = dict(
        XMSS=int(xmss),
        PASS1=int(pass1),
        PASS2=int(not xmss and not pass1),
        A=a,
        HP=hp,
        K=k,
        S1=(a if a <= 8 else 7),
    )
    return "".join(f"#define {k} {v}\n" for k, v in constants.items()), driver
