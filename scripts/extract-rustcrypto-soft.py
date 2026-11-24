"""Prepare the locked software SHA fallback for extraction without duplicating its round body.

Charon's structured-control-flow pass has a depth limit. Re-express the
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
    parser.add_argument("--bits", choices=(256, 512), type=int, default=512)
    args = parser.parse_args()
    bits = args.bits
    rounds = 64 if bits == 256 else 80
    module = f"sha{bits}"
    call = f"repeat{rounds}!(i, " + "{"

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
    original = (source / module / "soft/unroll.rs").read_text()
    marker = "    ($i:ident, $b:block) => {"
    start = original.index(marker)
    end = original.index("\n    };\n}", start)
    expansion = compact(original[start + len(marker) : end])
    require(
        expansion == "".join(f"let$i={i};$b;" for i in range(rounds)),
        "unrolled macro order",
    )
    require(original.count(call) == 1, "unique loop site")
    body = original.split(call)[1].split("\n    });")[0]
    require(
        not re.search(
            r"\b(break|continue|return|unsafe|drop|loop|while|for)\b|\?|\w!\s*[({\[]",
            body,
        ),
        "round must complete normally with no escaping side effects",
    )
    require(
        not re.search(r"\b(let\s+(mut\s+)?i|i\s*=)\b", body), "round index is read-only"
    )

    # The only external helper reads a word from immutable static storage.
    expected = """
    fn rk(i: usize) -> u64 {
        unsafe {
            let p = K64.as_ptr().add(i);
            core::ptr::read_volatile(p)
        }
    }
    """
    if bits == 256:
        expected = """
        fn rk(i:usize)->u32 {
            cfg_if::cfg_if! {
                if #[cfg(any(target_arch="x86",target_arch="x86_64"))] {
                    use core::ptr::read as r;
                } else {use core::ptr::read_volatile as r;}
            }
            unsafe {let p=K32.as_ptr().add(i); r(p)}
        }
        """
    helper = original[original.index("fn rk(") : original.index("/// Process a block")]
    require(compact(helper) == compact(expected), "volatile constant read")

    dst = args.output
    (dst / "src" / module / "soft").mkdir(parents=True, exist_ok=True)
    (dst / "Cargo.toml").write_text(
        '[package]\nname="rcsoftware"\nversion="0.1.0"\nedition="2024"\n[lib]\npath="src/lib.rs"\n'
    )
    if bits == 256:
        (cfg_package,) = (
            p for p in json.loads(metadata)["packages"] if p["name"] == "cfg-if"
        )
        manifest = dst / "Cargo.toml"
        manifest.write_text(
            manifest.read_text()
            + "\n[dependencies]\ncfg-if={path="
            + json.dumps(str(Path(cfg_package["manifest_path"]).parent))
            + "}\n"
        )
    (dst / "src/lib.rs").write_text(
        f"#![no_std]\nmod consts; pub mod {module} {{ pub mod soft; }}\n"
    )
    (dst / "src/consts.rs").write_text((source / "consts.rs").read_text())
    (dst / "src" / module / "soft/unroll.rs").write_text(
        original[:start] + marker + f" for $i in 0..{rounds} $b" + original[end:]
    )
    # Keep the original byte-load helper verbatim. Select the non-compact
    # module used by the production release on Graviton2.
    marker = "#[inline(always)]" if bits == 512 else "fn to_u32s"
    selection, load = (source / module / "soft.rs").read_text().split(marker, 1)
    require(
        compact(selection)
        == compact(
            """cfg_if::cfg_if! {
        if #[cfg(sha2_backend_soft = "compact")] {mod compact; pub(super) use compact::compress;}
        else {mod unroll; pub(super) use unroll::compress;} }"""
        ),
        "software backend selection",
    )
    (dst / "src" / module / "soft.rs").write_text("pub mod unroll;\n" + marker + load)


if __name__ == "__main__":
    main()
