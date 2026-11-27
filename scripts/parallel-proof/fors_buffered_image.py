"""Compile the exact FORS routine with observable cryptographic primitive calls."""

from pathlib import Path
from build import SRC, compile_probe, function

HERE = Path(__file__).resolve().parent


def image(folder, source):
    # Keep the common parent and serialization ABI identical to the XMSS checker.
    common = (
        (HERE / "buffered-tree.rs").read_text().split("fn xmss_subtree_fallback")[0]
    )
    common = common.replace("ADDRESS_PATH", str(SRC / "address.rs")).replace(
        "Adrs,TREE", "Adrs,FORS_TREE"
    )
    tree = function(source, "fors_subtree_horiz").replace("pub(super) fn", "fn", 1)
    return compile_probe(
        folder, common + tree + "\n" + (HERE / "fors-buffered.rs").read_text()
    )
