"""Build the production subtree and byte-layout helpers with two modeled callees."""

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "rust/src"


def function(source, name):
    match = re.search(
        r"^(?:pub\(super\) )?fn " + name + r"(?:<|\()", source, re.MULTILINE
    )
    if not match:
        raise ValueError(name)
    end = source.index("\n}", match.start()) + 2
    return source[match.start() : end]


def check_tree_layout(folder):
    batch = (SRC / "shake/batch.rs").read_text()
    body = "\n".join(
        function(batch, name) for name in ("xmss_subtree", "xmss_subtree_fallback")
    )
    probe = Path(__file__).with_name("tree-layout.rs").read_text()
    probe = probe.replace("// PRODUCTION_TREE", body).replace(
        "pub(super) fn xmss_subtree", "fn xmss_subtree"
    )
    probe = probe.replace("ADDRESS_PATH", str(SRC / "address.rs"))
    for width in (3, 8):
        source = folder / "tree-layout.rs"
        source.write_text(probe.replace("PROOF_WIDTH", str(width)))
        binary = folder / "tree-layout"
        subprocess.run(
            [
                "rustc",
                "--edition=2021",
                "-O",
                "-C",
                "overflow-checks=yes",
                "-Awarnings",
                source,
                "-o",
                binary,
            ],
            check=True,
        )
        subprocess.run([binary], check=True)


def build(folder):
    batch = (SRC / "shake/batch.rs").read_text()
    probe = (Path(__file__).with_name("probe.rs")).read_text()
    probe = probe.replace(
        "// PRODUCTION_HELPERS",
        "\n".join(
            function(batch, name)
            for name in (
                "word",
                "seed_words",
                "adrs_words",
                "header_active",
                "put_active",
                "read_active",
                "extract_lane",
                "pair_active",
                "refill_short_inplace",
                "fill_prf",
                "wots_leaves_batch",
                "wots_leaves_small",
                "xmss_subtree",
                "xmss_subtree_fallback",
            )
        ),
    )
    layout = (SRC / "shake256/parallel.rs").read_text()
    start = layout.index('#[cfg(target_arch = "x86_64")]')
    end = layout.index("\n", layout.index("pub(crate) type States"))
    probe = probe.replace("// PRODUCTION_LAYOUT", layout[start:end])
    for name in ("address", "params"):
        probe = probe.replace(name.upper() + "_PATH", str(SRC / (name + ".rs")))
    probe += "\n".join(
        f'#[no_mangle] pub extern "C" fn proof{n}_{height}(out: &mut [u8;{n}], '
        f"sk: &[u8;{n}], seed: &[u8;{n}], idx: u32, layer: u32, tree: u64, rest: &[u32;4]) {{"
        f"*out = batch::xmss_subtree(sk, seed, idx, {height}, address::Adrs {{ layer, tree, "
        "typ: rest[0], keypair: rest[1], word2: rest[2], word3: rest[3] }); }"
        for n in (16, 24, 32)
        for height in (1, 2, 3)
    )
    source = folder / "probe.rs"
    source.write_text(probe)
    obj = folder / "probe.o"
    subprocess.run(
        [
            "rustc",
            "--edition=2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--crate-type=lib",
            "-Copt-level=3",
            "-Cpanic=abort",
            "--emit=obj",
            "-Awarnings",
            source,
            "-o",
            obj,
        ],
        check=True,
    )
    sysroot = subprocess.check_output(
        ["rustc", "--print", "sysroot"], text=True
    ).strip()
    (linker,) = Path(sysroot, "lib/rustlib").glob("*/bin/rust-lld")
    image = folder / "probe.so"
    subprocess.run(
        [linker, "-flavor", "gnu", "-shared", "--gc-sections", obj, "-o", image],
        check=True,
    )
    return image
