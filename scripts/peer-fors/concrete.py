"""Install observation points *inside* the actual, concrete peer methods in a scratch crate."""

from pathlib import Path
import re


def cut_methods(source, method, expected, replacement, copy=None):
    """Keep Rust signatures and replace only the bodies at named induction boundaries."""
    methods = list(re.finditer(r"^    fn " + method + r"(?=[(<])", source, re.M))
    if len(methods) != expected:
        raise ValueError(
            f"expected {expected} definitions of {method}, found {len(methods)}"
        )
    for entry in reversed(methods):
        opening = source.index("{", entry.end())
        # Each pinned method finishes at its four-space closing brace;
        # interior blocks have greater indentation.
        closing = source.index("\n    }", opening) + len("\n    }")
        declaration = source[entry.start() : opening]
        original = source[entry.start() : closing]
        if copy:
            saved = (
                original.replace("fn " + method + "(", "fn " + copy + "(", 1) + "\n\n"
            )
        else:
            saved = ""
        source = (
            source[: entry.start()]
            + saved
            + declaration
            + "{\n"
            + replacement
            + "\n    }"
            + source[closing:]
        )
    return source


def instrument(peer, template):
    source = (peer / "src/fors.rs").read_text()
    # Each concrete implementation has its own symbols, so crossing from one
    # SHA-2 security category or from SHAKE into another provider is detected.
    params = {
        "prf": "seed: *const u8, addr: *const u8",
        "f": "addr: *const u8, msg: *const u8",
        "h": "addr: *const u8, left: *const u8, right: *const u8",
        "t": "addr: *const u8, rows: *const u8, count: usize",
    }
    calls = {
        f"{family}_{op}": decl
        for family in ("shake", "sha2l1", "sha2l35")
        for op, decl in params.items()
    }
    calls["node"] = "seed: *const u8, addr: *const u8, index: u32, level: u32"
    declarations = [
        f"pub(crate) fn {name}_observe(out: *mut u8, state: *const u8, {args});"
        for name, args in calls.items()
    ]
    observations = 'unsafe extern "C" {\n' + "\n".join(declarations) + "\n}\n"
    state = "core::ptr::from_ref(self).cast::<u8>()"

    def body(call, args):
        return f"let mut out = Array::default(); unsafe {{ crate::fors::{call}_observe(out.as_mut_ptr(), {state}, {args}) }}; out"

    source = cut_methods(
        source,
        "fors_node",
        1,
        body("node", "sk_seed.0.as_ptr(), adrs.as_ref().as_ptr(), i, z"),
        "proof_observed_node",
    )
    (peer / "src/fors.rs").write_text(source + "\n" + observations)
    for family, types in (("sha2", ("Sha2L1", "Sha2L35")), ("shake", ("Shake",))):
        path = peer / f"src/hashes/{family}.rs"
        implementation = path.read_text()
        for typ in types:
            marker = f"HashSuite for {typ}<N, M>"
            if implementation.count(marker) != 1:
                raise ValueError(f"expected unique {marker}")
            begin = implementation.rindex("\nimpl", 0, implementation.index(marker))
            end = implementation.index("\n}", implementation.index(marker)) + 2
            methods = implementation[begin:end]
            for method, args in (
                ("prf_sk", "sk_seed.0.as_ptr(), adrs.as_ref().as_ptr()"),
                ("f", "adrs.as_ref().as_ptr(), m.as_ptr()"),
                ("h", "adrs.as_ref().as_ptr(), m1.as_ptr(), m2.as_ptr()"),
                ("t", "adrs.as_ref().as_ptr(), m.as_ptr().cast(), m.len()"),
            ):
                op = "prf" if method == "prf_sk" else method
                methods = cut_methods(
                    methods, method, 1, body(typ.lower() + "_" + op, args)
                )
            implementation = implementation[:begin] + methods + implementation[end:]
        path.write_text(implementation)
    entry = template[template.index("#[unsafe(no_mangle)]") :]
    return (
        """use crate::address::ForsTree;
use crate::fors::ForsParams;
use crate::hashes::HashSuite;
use crate::SkSeed;
use hybrid_array::Array;
type P=crate::PEER_TYPE;
const A:u32=PARAM_A;
const K:usize=PARAM_K;
const N:usize=PARAM_N;
const MD:usize=(K*A as usize+7)/8;
"""
        + entry
        + """
#[unsafe(no_mangle)]
pub fn SUITE_node(state:&P, seed:&SkSeed<<P as HashSuite>::N>, addr:&ForsTree,
                  index:u32, z:u32, out:&mut [u8;N]) {
    *out=state.proof_observed_node(seed,index,z,addr).0;
}
"""
    )
