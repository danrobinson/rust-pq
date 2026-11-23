"""Build the replay against the shipping kernels and an isolated full-round control."""
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def replace(path, old, new):
    text = path.read_text()
    if text.count(old) != 1:
        raise ValueError(f"control patch no longer matches {path}")
    path.write_text(text.replace(old, new))


with tempfile.TemporaryDirectory() as tmp:
    work = Path(tmp)
    for name in ("native", "full"):
        dest = work / name
        shutil.copytree(ROOT / "rust/src", dest / "src")
        shutil.copy(ROOT / "rust/Cargo.toml", dest)
    full = work / "full"
    replace(full / "Cargo.toml", 'name = "slhdsa"\nversion', 'name = "replay-full"\nversion')
    # An opaque register operand prevents loop-invariant code motion from silently
    # reinstating prefix reuse. The assembly template emits no instructions.
    arm = full / "src/sha256.rs"
    replace(arm, "s.abcd[LANE] = slots[LANE].a1;\n                s.efgh[LANE] = slots[LANE].e1;",
            """let mut fresh_head = slots[LANE].m0;
                unsafe { core::arch::asm!("/* {h:v} */", h=inout(vreg) fresh_head, options(nomem, nostack, preserves_flags)); }
                let w = arm::add(fresh_head, arm::load_words(&super::K, 0));
                s.abcd[LANE] = arm::sha256h(abcd0, efgh0, w);
                s.efgh[LANE] = arm::sha256h2(efgh0, abcd0, w);""")
    path = full / "src/sha256/x86/avx512.rs"
    old = """let mut prefix = initial;
        for i in 0..4 {
            prefix = round(prefix, words[i], super::super::K[i]);
        }
        loop {
            words = chain_address(words, fixed4, counter, half);"""
    new = """loop {
            words = chain_address(words, fixed4, counter, half);
            let mut prefix = initial;
            let mut head = words[0];
            unsafe { core::arch::asm!("/* {h} */", h=inout(zmm_reg) head, options(nomem, nostack, preserves_flags)); }
            prefix = round(prefix, head, super::super::K[0]);
            for i in 1..4 {
                prefix = round(prefix, words[i], super::super::K[i]);
            }"""
    replace(path, old, new)
    src = work / "src"
    src.mkdir()
    for module in HERE.glob("*.rs"):
        shutil.copy(module, src)
    for name in ("slh", "fors", "xmss", "wots", "ht"):
        shutil.copy(ROOT / f"rust/src/{name}.rs", src)
    (work / "Cargo.toml").write_text("""[package]
name="hash-replay"
version="0.1.0"
edition="2021"
[dependencies]
native={package="slhdsa",path="native",features=["platform-sha2"]}
full={package="replay-full",path="full",features=["platform-sha2"]}
""")
    shutil.copy(ROOT / "rust/Cargo.lock", work)
    subprocess.run(["cargo", "build", "--release", "--manifest-path", str(work / "Cargo.toml")], check=True)
    binary = Path(os.environ.get("CARGO_TARGET_DIR",work / "target")).resolve() / "release/hash-replay"
    subprocess.run([str(binary), *sys.argv[1:]], check=True)
