"""Prepare the locked SHA-512 fallback for extraction without duplicating its round body.

Charon's structured-control-flow pass has a depth limit. Re-express the eighty
consecutive, identical macro bodies as a counted loop after checking every
call's index, macro hygiene, and absence of a control transfer from that body.
"""

import argparse
import json
import re
import subprocess
from pathlib import Path


def compact(source):
    return re.sub(r"\s+", "", re.sub(r"//[^\n]*", "", source))


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    metadata = subprocess.check_output(
        [
            "cargo",
            "metadata",
            "--format-version",
            "1",
            "--locked",
            "--features",
            "platform-sha2",
            "--manifest-path",
            "rust/Cargo.toml",
        ],
        text=True,
    )
    (dep,) = [
        p
        for p in json.loads(metadata)["packages"]
        if p["name"] == "sha2" and p["version"] == "0.11.1"
    ]
    source = Path(dep["manifest_path"]).parent / "src"
    original = (source / "sha512/soft/unroll.rs").read_text()
    marker = "    ($i:ident, $b:block) => {"
    start = original.index(marker)
    end = original.index("\n    };\n}", start)
    expansion = compact(original[start + len(marker) : end])
    require(
        expansion == "".join(f"let$i={i};$b;" for i in range(80)),
        "unrolled macro order",
    )
    require(original.count("repeat80!(i, {") == 1, "unique loop site")
    body = original.split("repeat80!(i, {")[1].split("\n    });")[0]
    require(
        not re.search(
            r"\b(break|continue|return|unsafe|drop|loop|while|for)\b|\?|\w!\s*[({\[]", body
        ),
        "round must complete normally with no escaping side effects",
    )
    require(
        not re.search(r"\b(let\s+(mut\s+)?i|i\s*=)\b", body), "round index is read-only"
    )

    # The only external helper in the extraction reads an immutable K64 word.
    expected = """
    fn rk(i: usize) -> u64 {
        unsafe {
            let p = K64.as_ptr().add(i);
            core::ptr::read_volatile(p)
        }
    }
    """
    helper = original[original.index("fn rk(") : original.index("/// Process a block")]
    require(compact(helper) == compact(expected), "volatile constant read")

    dst = args.output
    (dst / "src/sha512/soft").mkdir(parents=True, exist_ok=True)
    (dst / "Cargo.toml").write_text(
        '[package]\nname="rcsoftware"\nversion="0.1.0"\nedition="2024"\n[lib]\npath="src/lib.rs"\n'
    )
    (dst / "src/lib.rs").write_text(
        "#![no_std]\nmod consts; pub mod sha512 { pub mod soft; }\n"
    )
    (dst / "src/consts.rs").write_text((source / "consts.rs").read_text())
    (dst / "src/sha512/soft/unroll.rs").write_text(
        original[:start] + marker + " for $i in 0..80 $b" + original[end:]
    )
    # Keep the original byte-load helper verbatim. Select the non-compact
    # module used by the production release on Graviton2.
    selection, load = (
        (source / "sha512/soft.rs").read_text().split("#[inline(always)]", 1)
    )
    require(
        compact(selection)
        == compact(
            """cfg_if::cfg_if! {
        if #[cfg(sha2_backend_soft = "compact")] {mod compact; pub(super) use compact::compress;}
        else {mod unroll; pub(super) use unroll::compress;} }"""
        ),
        "software backend selection",
    )
    (dst / "src/sha512/soft.rs").write_text("pub mod unroll;\n#[inline(always)]" + load)


if __name__ == "__main__":
    main()
