"""Lift the production scheduler to symbolic bytes and symbolic input-index bits."""

import re
import subprocess
import tempfile
from pathlib import Path

from build import SRC, function


def once(s, before, after):
    if s.count(before) != 1:
        raise ValueError(f"review the proof binding for {before!r}")
    return s.replace(before, after)


def symbolic_source(source):
    sign = function(source, "sign")
    # Byte copies become term copies, including complete Vec slices. The two
    # public scalar indices become bit origins. All job arithmetic stays Rust.
    sign = re.sub(r"\bu8\b", "Token", sign)
    sign = once(sign, "mut tree: u64", "mut tree: Word")
    sign = once(sign, "mut leaf: u32", "mut leaf: Word")
    sign = once(
        sign,
        "(tree & ((1u64 << p.hp) - 1)) as u32",
        "(tree & ((1u64 << p.hp) - 1)).low32()",
    )

    # This is the shared-state boundary of the Joined theorem. Refuse new
    # reads, writes, synchronization or control dependencies without review.
    def compact(text):
        return re.sub(r"//[^\n]*|\s+", "", text)

    def section(start, end):
        return compact(sign).split(compact(start), 1)[1].split(compact(end), 1)[0]

    queue = section("let nodes:", "let fill")
    if queue != compact("""
        Vec<OnceLock<[Token; N]>> = (0..layers.len() * p.hp as usize)
            .map(|_| OnceLock::new()).collect();
        let next = AtomicUsize::new(0);
    """):
        raise ValueError("ticket counter or slot initialization changed")
    worker = section("let fill = || loop {", "}; let (fors, mut root)")
    if worker != compact("""
        let job = next.fetch_add(1, Ordering::Relaxed);
        let Some(slot) = nodes.get(job) else { break };
        let height = p.hp - 1 - (job / layers.len()) as u32;
        let (addr, index) = layers[job % layers.len()];
        let value = xmss_node(sk, (index >> height) ^ 1, height, seed, addr);
        slot.set(value).expect("unique XMSS job");
    """):
        raise ValueError("worker effects differ from the Joined model")
    scope = section("thread::scope(|scope| {", "}); let mut signature")
    if scope != compact("""
        for _ in 1..workers {
            if thread::Builder::new().spawn_scoped(scope, || {
                run_worker(&fill); scrub_worker_stack();
            }).is_err() { break; }
        }
        let fors = fors_sign(p, md, sk, seed, fors_addr);
        let root = fors_pk_from_sig(p, &fors, md, seed, fors_addr);
        fill();
        (fors, root)
    """):
        raise ValueError("scope, drain or join differs from the Joined model")
    conditions = re.findall(r"\bif\s+([^{]+)\{", re.sub(r"//[^\n]*", "", sign))
    if list(map(compact, conditions)) != [
        "workers<2||p.hp==0",
        "thread::Builder::new().spawn_scoped(scope,||",
        "j+1<layers.len()",
    ]:
        raise ValueError("review new control flow for symbolic input dependencies")
    return function(source, "run_worker") + "\nfn scrub_worker_stack() {}\n" + sign


def main():
    source = (SRC / "slh/parallel.rs").read_text()
    probe = Path(__file__).with_name("signer.rs").read_text()
    probe = probe.replace("// PRODUCTION_SIGNER", symbolic_source(source))
    probe = probe.replace("PARAMS_PATH", str(SRC / "params.rs"))
    probe = probe.replace("ADDRESS_PATH", str(SRC / "address.rs"))
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp, "signer.rs")
        binary = Path(tmp, "signer")
        src.write_text(probe)
        subprocess.run(
            [
                "rustc",
                "--edition=2021",
                "-O",
                "-C",
                "overflow-checks=yes",
                "-Awarnings",
                src,
                "-o",
                binary,
            ],
            check=True,
        )
        subprocess.run([binary], check=True)


if __name__ == "__main__":
    main()
