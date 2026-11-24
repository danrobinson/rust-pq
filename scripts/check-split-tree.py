#!/usr/bin/env python3
"""Replay the split-tree lemma and check the production reducer's primitive calls."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "parallel-proof"))
from build import ROOT, SRC, function


def check_keygen_queue(source):
    """Bind the successful keygen branch to the Joined trace and split-tree model."""
    keygen = function(source, "keygen")
    # All supported geometries satisfy sub_h <= hp in both target branches.
    # Check the computation up to the split as well as the queue effects.
    expected = """pub(super) fn keygen<const N: usize>(
        p: &Params, sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs,
    ) -> Option<[u8; N]> {
        let threads = crate::pool::available_threads();
        if threads < 2 || p.hp < 3 { return None; }
        #[cfg(target_arch = "x86_64")]
        let sub_h = if p.hp >= 8 { 3 } else if p.hp >= 6 { 2 } else { 0 };
        #[cfg(not(target_arch = "x86_64"))]
        let sub_h = if p.hp >= 9 { 3 } else if p.hp >= 6 { 2 } else { 0 };
        let split = p.hp - sub_h;
        let count = 1usize << split;
        let nodes: Vec<OnceLock<[u8; N]>> = (0..count).map(|_| OnceLock::new()).collect();
        let next = AtomicUsize::new(0);
        let fill = || loop {
            let job = next.fetch_add(1, Ordering::Relaxed);
            let Some(slot) = nodes.get(job) else { break };
            let value = xmss_node::<N>(sk_seed, job as u32, sub_h, seed, adrs);
            slot.set(value).expect("unique keygen subtree job");
        };
        crate::pool::execute(threads.min(count), true, &fill);
        Some(reduce_tree(&nodes, seed, adrs.with_type(TREE), 0, sub_h, p.hp,))
    }"""
    def compact(text):
        return re.sub(r"//[^\n]*|\s+", "", text)
    if compact(keygen) != compact(expected):
        raise ValueError("review keygen ticket effects and split policy against keygenRoot")


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    parallel = (SRC/"slh/parallel.rs").read_text()
    check_keygen_queue(parallel)
    source = function(parallel, "reduce_tree")
    # Keep all slot reads, in-place updates, shifts, loop bounds and truncation.
    # Node is opaque. Index denotes root*scale+offset without u32 wrapping;
    # FIPS subtree indices must fit in u32 at the lowest split height.
    lifted = source.replace("[u8; N]", "Node").replace("root_idx: u32", "root_idx: Index")
    probe = (HERE/"parallel-proof/split-tree.rs").read_text().replace("// PRODUCTION", lifted)
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        (tmp/"split.rs").write_text(probe)
        subprocess.run(["rustc", tmp/"split.rs", "-o", tmp/"split"], check=True)
        subprocess.run([tmp/"split"], check=True)
    subprocess.run(["lake", "build", "Parallel.SplitTree"], cwd=ROOT/"lean-hw", check=True)
    audit = "import Parallel.SplitTree\n#print axioms ParallelSplitTree.xmss\n#print axioms ParallelSplitTree.fors\n#print axioms ParallelSplitTree.keygenRoot\n"
    output = subprocess.check_output(["lake", "env", "lean", "--stdin"], input=audit, text=True, cwd=ROOT/"lean-hw")
    for theorem in ("xmss", "fors", "keygenRoot"):
        match = re.search(rf"'ParallelSplitTree\.{theorem}' depends on axioms: \[([^\]]*)\]", output)
        if not match or set(match[1].split(", ")) - {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError(output)


if __name__ == "__main__":
    main()
