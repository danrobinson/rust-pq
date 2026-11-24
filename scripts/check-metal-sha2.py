#!/usr/bin/env python3
"""Check the Metal SHA-2 compression macros and their unrolled register schedules."""

import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def compact(s):
    return re.sub(r"\s+|\\\n", "", s)


def function(source, name):
    start = source.rindex("\ninline ", 0, source.index(name + "(")) + 1
    return source[start : source.index("\n}", start) + 2]


def require(actual, expected):
    if compact(actual) != compact(expected):
        raise ValueError(f"review compression binding: {actual}")


def check(source, sha):
    bits = 32 if sha == 256 else 64
    rounds = 64 if sha == 256 else 80
    word = f"uint{bits}_t"
    stem = f"SHA{sha}"
    tail = "u" if sha == 256 else "ul"
    rotations = (
        (2, 13, 22, 6, 11, 25, 7, 18, 3, 17, 19, 10)
        if sha == 256
        else (28, 34, 39, 14, 18, 41, 1, 8, 7, 19, 61, 6)
    )

    def rot(v, i):
        return f"rotr{bits}({v},{i}{tail})"

    rotation = "rotate(x,32u-n)" if bits == 32 else "(x>>n)|(x<<(64ul-n))"
    require(
        function(source, f"rotr{bits}"),
        f"inline {word} rotr{bits}({word} x,{word} n){{return {rotation};}}",
    )
    begin = source.index(f"#define {stem}_R(")
    end = source.index(f"inline void sha{sha}_compress", begin)
    macros = source[begin:end].replace("\\\n", "").strip().split("#define ")[1:]

    def big(v, r):
        return "^".join(rot(v, i) for i in r)

    require(
        macros[0],
        f"""{stem}_R(a,b,c,d,e,f,g,h,k,wi) do {{
        {word} s1={big("e", rotations[3:6])}; {word} ch=g^(e&(f^g));
        {word} t1=h+s1+ch+(k)+(wi); {word} s0={big("a", rotations[:3])};
        {word} maj=(a&b)|(c&(a|b)); d+=t1; h=t1+s0+maj; }} while(0)""",
    )
    require(
        macros[1],
        f"""{stem}_WEXT(w,j) do {{
        {word} x=w[((j)+1)&15];{word} y=w[((j)+14)&15];
        {word} ss0={big("x", rotations[6:8])}^(x>>{rotations[8]});
        {word} ss1={big("y", rotations[9:11])}^(y>>{rotations[11]});
        w[(j)]=w[(j)]+ss0+w[((j)+9)&15]+ss1; }} while(0)""",
    )
    if len(macros) != 4:
        raise ValueError("unexpected compression macros")
    for extend in (False, True):
        code = f"{stem}_16_EXT(w,base)" if extend else f"{stem}_16_INIT(w)"
        regs = list("abcdefgh")
        for i in range(16):
            if extend:
                code += f"{stem}_WEXT(w,{i});"
            idx = f"(base)+{i}" if extend else str(i)
            code += f"{stem}_R({','.join(regs)},K{sha}[{idx}],w[{i}]);"
            regs = regs[-1:] + regs[:-1]
        require(macros[2 + extend], code)

    for separate in [False, True] if sha == 256 else [False]:
        name = f"sha{sha}_compress" + ("_from" if separate else "")
        src, dst = ("base_st", "out") if separate else ("st", "st")
        signature = (
            f"const thread {word} base_st[8],thread {word} w[16],thread {word} out[8]"
            if separate
            else f"thread {word} st[8],thread {word} w[16]"
        )
        code = f"inline void {name}({signature}){{"
        for i in (0, 4):
            code += (
                word
                + ",".join(
                    f"{reg}={src}[{j}]"
                    for j, reg in enumerate("abcdefgh"[i : i + 4], i)
                )
                + ";"
            )
        code += f"{stem}_16_INIT(w);for(uint base=16u;base<{rounds}u;base+=16u){{{stem}_16_EXT(w,base);}}"
        for i, reg in enumerate("abcdefgh"):
            code += (
                f"{dst}[{i}]={src}[{i}]+{reg};" if separate else f"{dst}[{i}]+={reg};"
            )
        require(function(source, name), code + "}")

    values = re.search(
        rf"constant {word} K{sha}\[{rounds}\] = \{{([^}}]+)\}};", source
    )[1]
    ks = [
        re.fullmatch(r"(0x[0-9a-f]+)" + tail, x.strip())[1] for x in values.split(",")
    ]
    rotr = (
        (lambda x, i: f"({x}.rotateLeft ({bits}-{i}))")
        if bits == 32
        else (lambda x, i: f"(({x} >>> ({i} : Nat)) ||| ({x} <<< ({bits}-{i} : Nat)))")
    )
    laws = [
        f"namespace Metal{sha}",
        f"open Spec.SHA{sha}",
        f"example : K = [{','.join(ks)}] := by decide",
    ]
    for f, r in zip(
        ("bsig0", "bsig1", "ssig0", "ssig1"),
        (rotations[:3], rotations[3:6], rotations[6:9], rotations[9:]),
    ):
        args = [rotr("x", i) for i in r]
        if f.startswith("ssig"):
            args[-1] = f"(x >>> ({r[-1]} : Nat))"
        laws.append(
            f"example (x : Word) : {' ^^^ '.join(args)} = {f} x := by unfold {f}; bv_decide"
        )
    laws += [
        "example (e f g : Word) : g ^^^ (e &&& (f ^^^ g)) = ch e f g := by unfold ch; bv_decide",
        "example (a b c : Word) : (a &&& b) ||| (c &&& (a ||| b)) = maj a b c := by unfold maj; bv_decide",
        "example (x y z t : Word) : x+y+z+t = t+z+y+x := by ac_rfl",
        "example (x y z : Word) : x+y+z = x+(y+z) := by ac_rfl",
        f"end Metal{sha}",
    ]
    return laws


def main():
    shader = (ROOT / "metal/shaders/slhdsa.metal").read_text()
    proof = ["import Spec.Sha512", "import Std.Tactic.BVDecide"]
    for sha in (256, 512):
        proof.extend(check(shader, sha))
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Compression.lean"
        path.write_text("\n".join(proof))
        subprocess.run(["lake", "env", "lean", path], cwd=ROOT / "lean", check=True)


if __name__ == "__main__":
    main()
