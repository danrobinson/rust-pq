#!/usr/bin/env python3
"""Textual check for MIdeal/Sha2_128s.lean (run by scripts/check.sh, step 0b).

Each MIdeal statement must be the single-set tree's statement (git commit 26aa3d8, read with
`git show`; SLHDSA_REPO overrides the repository) under the renamings
`RENAMES` below, character for character (whitespace runs normalised):

* `Ideal.rust_ideal_security_closed_tight8`, `Ideal.rust_ideal_security_closed_pure_tight8`,
  `Ideal.api_ideal_security_closed_pure_tight8` (security/Ideal/RustFinalClosedTight8.lean of 26aa3d8);
* the structure `E2E.PureBytesEndToEnd` (security/E2E/Bytes.lean of 26aa3d8);
* `Ideal.pureBytesAlg_realCF` (security/Ideal/RustFinalClosedPure.lean of 26aa3d8);
* and, with their own renamings (`rename_gen`), the six statements of ME2E/Gen128s.lean against
  `E2E.rust_securityG` … (security/E2E/HeadlineGen.lean of 26aa3d8) and `E2E.api_pure_securityG`.

The renamings touch only the Rust-function names, the real-scheme side (`vp prims codec128s`,
`Link.vp Link.prims Reduction.codec128s` -> the same objects spelled at `Sha2Set.s128s`, which
`MIdeal/Sha2_128s.lean` shows are `rfl`-equal), `node`, `Link.decodePk`, and the names of the
`E2E` end-to-end structures.  In particular the ideal-model game and the bound (conjunct 3) are
left untouched, so they must appear verbatim.
"""
import os, re, sys

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, "..", ".."))
MINE = os.path.join(root, "security", "MIdeal", "Sha2_128s.lean")
import subprocess
def old_file(rel):
    repo = os.environ.get("SLHDSA_REPO") or root
    return subprocess.run(["git", "-C", repo, "show", "26aa3d8:" + rel],
                          check=True, capture_output=True, text=True).stdout

S = "Sha2Set.s128s"
RENAMES = [
    ("slhdsa.slh.slh_", "slhdsa.sets.sha2_128s.slh_"),
    ("slhdsa.api.", "slhdsa.sets.sha2_128s."),
    ("Link.vp Link.prims Reduction.codec128s", f"{S}.vp {S}.prims (codec {S})"),
    ("vp prims codec128s", f"{S}.vp {S}.prims (codec {S})"),
    ("PublicKeyCore prims.core", f"PublicKeyCore {S}.prims.core"),
    ("prims.Y", f"{S}.prims.Y"),
    ("prims.PkSeed", f"{S}.prims.PkSeed"),
    ("prims.SkSeed", f"{S}.prims.SkSeed"),
    ("prims.SkPrf", f"{S}.prims.SkPrf"),
    ("Link.decodePk pk", f"MLink.decodePk {S} pk"),
    ("E2E.PureBytesEndToEnd", "PureBytesEndToEnd"),
    ("E2E.ApiPureBytesEndToEnd", "ME2E.sha2_128s.ApiPureBytesEndToEnd"),
]
NODE = re.compile(r"\(node (\w+)\)")


def rename(t):
    for a, b in RENAMES:
        t = t.replace(a, b)
    # `S128s.prims.Y` etc. must not be renamed twice
    t = t.replace(f"{S}.{S}.", f"{S}.")
    return NODE.sub(lambda m: f"(node {S} {m.group(1)})", t)


def norm(t):
    return re.sub(r"\s+", " ", t).strip()


def decl(text, kind, name):
    """The statement of `theorem name` (up to the `:=` that ends a line), or the whole
    `structure name` (up to the next blank line)."""
    m = re.search(rf"^{kind} {re.escape(name)}\b", text, re.M)
    if not m:
        sys.exit(f"FAIL: {kind} {name} not found")
    rest = text[m.start():]
    if kind == "structure":
        return rest[: rest.index("\n\n")]
    end = re.search(r":=[ \t]*\n", rest)
    return rest[: end.start()]


def rename_gen(t):
    """The renamings of ME2E/Gen128s.lean: Rust names; part (a)'s cores and `node` at Sha2Set.s128s."""
    t = t.replace("slhdsa.slh.slh_", "slhdsa.sets.sha2_128s.slh_").replace("slhdsa.api.", "slhdsa.sets.sha2_128s.")
    for f in ("byteKeygen", "byteSignPure", "byteSign", "byteVerifyPure", "byteVerify"):
        t = re.sub(r"\b%s vp prims codec128s" % f, f"{f} {S}.vp {S}.prims (codec {S})", t)
    return re.sub(r"\(node (\w+)\)", rf"(node {S} \1)", t)


def main():
    tight8 = old_file("security/Ideal/RustFinalClosedTight8.lean")
    pure = old_file("security/Ideal/RustFinalClosedPure.lean")
    bytes_ = old_file("security/E2E/Bytes.lean")
    mine = open(MINE).read()
    pairs = [
        (decl(bytes_, "structure", "PureBytesEndToEnd"), decl(mine, "structure", "PureBytesEndToEnd")),
        (decl(pure, "theorem", "pureBytesAlg_realCF"), decl(mine, "theorem", "pureBytesAlg_realCF")),
    ] + [
        (decl(tight8, "theorem", n), decl(mine, "theorem", n))
        for n in ("rust_ideal_security_closed_tight8", "rust_ideal_security_closed_pure_tight8",
                  "api_ideal_security_closed_pure_tight8")
    ]
    bad = 0
    for orig, ours in pairs:
        if norm(rename(orig)) != norm(ours):
            bad = 1
            a, b = norm(rename(orig)), norm(ours)
            i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
            print("FAIL: statement differs:", ours.split("\n")[0])
            print("  expected …", a[max(0, i - 80): i + 80])
            print("  found    …", b[max(0, i - 80): i + 80])
    # ME2E/Gen128s.lean: the general-sampling-spec headlines (E2E/HeadlineGen.lean of 26aa3d8, and
    # api_pure_securityG of its E2E/Api.lean); only part (a) is respelled at Sha2Set.s128s there.
    gen_old = old_file("security/E2E/HeadlineGen.lean") + old_file("security/E2E/Api.lean")
    gen_mine = open(os.path.join(root, "security", "ME2E", "Gen128s.lean")).read()
    for n in ("rust_securityG", "rust_security_linearG", "rust_pure_securityG", "rust_pure_security_linearG",
              "rust_security_resourcesG", "api_pure_securityG"):
        a, b = norm(rename_gen(decl(gen_old, "theorem", n))), norm(decl(gen_mine, "theorem", n))
        if a != b:
            bad = 1
            i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
            print("FAIL: statement differs:", n)
            print("  expected …", a[max(0, i - 80): i + 80])
            print("  found    …", b[max(0, i - 80): i + 80])
        pairs.append((a, b))
    if bad:
        sys.exit(1)
    print(f"{len(pairs)} statements = single-set statements under the renamings")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--print":
        tight8 = old_file("security/Ideal/RustFinalClosedTight8.lean")
        pure = old_file("security/Ideal/RustFinalClosedPure.lean")
        bytes_ = old_file("security/E2E/Bytes.lean")
        print(rename(decl(bytes_, "structure", "PureBytesEndToEnd")))
        print(rename(decl(pure, "theorem", "pureBytesAlg_realCF")))
        for n in ("rust_ideal_security_closed_tight8", "rust_ideal_security_closed_pure_tight8",
                  "api_ideal_security_closed_pure_tight8"):
            print(rename(decl(tight8, "theorem", n)))
    else:
        main()
