"""Lift the production scheduler to symbolic bytes and symbolic input-index bits."""

import re
import subprocess
import tempfile
from pathlib import Path

from build import SRC, function
import cached


def once(s, before, after):
    if s.count(before) != 1:
        raise ValueError(f"review the proof binding for {before!r}")
    return s.replace(before, after)


def check_phase_order(sign):
    """Bind the queue events in the Lean trace to their Rust publication points."""
    text = re.sub(r"//[^\n]*|\s+", "", sign)
    markers = [
        "let total_phase1=jobs.len();",
        "let phase1_next=AtomicUsize::new(0);",
        "let phase1_done=AtomicUsize::new(0);",
        "let phase2_state=AtomicU8::new(PHASE1_RUNNING);",
        "let phase2_next=AtomicUsize::new(0);",
        "let run=||{",
        "loop{let job_idx=phase1_next.fetch_add(1,Ordering::Relaxed);"
        "let Some(&item)=jobs.get(job_idx)else{break;};match item.kind{",
        "if phase1_done.fetch_add(1,Ordering::AcqRel)+1==total_phase1{",
        "let _=sig_fors_cell.set(sig_fors);let _=xmss_auth_cell.set(xmss_auth);let _=roots_cell.set(roots);",
        "phase2_state.store(PHASE2_READY,Ordering::Release);phase2_cv.notify_all();",
        "let st=phase2_state.load(Ordering::Acquire);if st==PHASE2_READY{break;}",
        "while phase2_state.load(Ordering::Acquire)==PHASE1_RUNNING{",
        "if phase2_state.load(Ordering::Acquire)!=PHASE2_READY{abort_guard.armed=false;return;}break;",
        'let roots=roots_cell.get().expect("roots ready");',
        "loop{let j=phase2_next.fetch_add(1,Ordering::Relaxed);let Some(slot)=wots_sigs.get(j)else{break;};",
        'slot.set(sig).expect("unique WOTS sign job");',
        "crate::pool::execute(threads.min(total_phase1),true,&run);",
    ]
    markers = [re.sub(r"\s+", "", m) for m in markers]
    if any(text.count(m) != 1 for m in markers):
        raise ValueError(
            "review ticket claims, publications and barrier against ParallelFused"
        )
    indices = [text.index(m) for m in markers]
    if indices != sorted(indices):
        raise ValueError("parallel publication order changed")
    # A result assembled by the last finisher must be independent of its ticket.
    if re.search(r"item|job_idx", text[indices[7] + len(markers[7]) : indices[9]]):
        raise ValueError("last-finisher identity used in the reduction")
    if text.count(".fetch_add(") != 3:
        raise ValueError("unexpected scheduler counter update")


def symbolic_source(source):
    # Keep the job allocation, sorting, slot writes and two-phase assembly.
    # Digest/address bits are symbolic only where the production type carries
    # a cryptographic index. Job sizes, counters and array offsets stay concrete.
    sign = once(function(source, "sign"), "pub(super) fn sign", "pub(crate) fn sign")
    check_phase_order(sign)
    # Each dispatched worker makes at most one terminating fetch per phase.
    # Production caps the number of workers at total_phase1, caller included.
    sign = once(
        sign,
        "let total_phase1 = jobs.len();",
        """let total_phase1 = jobs.len();
        assert!(total_phase1 > 0);
        assert!(total_phase1 * 2 <= u32::MAX as usize);
        assert!(total_phase1 + p.d as usize <= u32::MAX as usize);""",
    )
    sign = sign.replace("[u8; N]", "[Token; N]").replace("Vec<u8>", "Vec<Token>")
    sign = once(sign, "md: &[u8]", "md: &[Token]")
    sign = once(sign, "mut tree: u64", "mut tree: Word")
    sign = once(sign, "mut leaf: u32", "mut leaf: Word")
    sign = once(
        sign,
        "(tree & ((1u64 << p.hp) - 1)) as u32",
        "(tree & ((1u64 << p.hp) - 1)).low32()",
    )
    sign = once(
        sign,
        """if index & 1 == 0 {
                            hash2::<N>(seed, &a_node, &node, sibling)
                        } else {
                            hash2::<N>(seed, &a_node, sibling, &node)
                        }""",
        "climb_step(index, seed, &a_node, &node, sibling)",
    )
    # Every other control decision in the lifted signer must operate on
    # public geometry, scheduling metadata or a concrete worker ticket.
    meta = source[
        source.index("struct XmssAuthMeta") : source.index("pub(super) fn sign<")
    ]
    meta = re.sub(r"\b(root_idx|idx): u32", r"\1: Word", meta)
    reduce = (
        function(source, "reduce_tree")
        .replace("[u8; N]", "[Token; N]")
        .replace("root_idx: u32", "root_idx: Word")
    )
    return meta + reduce + "\n" + sign


def probe_source(cache_source):
    source = (SRC / "slh/parallel.rs").read_text()
    probe = Path(__file__).with_name("signer.rs").read_text()
    cached_probe = Path(__file__).with_name("cached.rs").read_text()
    probe = probe.replace("// CACHED_HARNESS", cached.harness(cached_probe, cache_source))
    probe = probe.replace("// PRODUCTION_SIGNER", symbolic_source(source))
    probe = probe.replace("PARAMS_PATH", str(SRC / "params.rs"))
    probe = probe.replace("ADDRESS_PATH", str(SRC / "address.rs"))
    return probe


def main():
    width_source = (SRC / "shake256/parallel.rs").read_text()
    widths = re.findall(r"const WIDTH: usize = ([^;]+);", width_source)
    if set(widths) != {"3", "8"}:
        raise ValueError("replay all production Keccak lane widths")
    probe = probe_source((SRC / "cache.rs").read_text())
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp, "signer.rs")
        binary = Path(tmp, "signer")
        for width, simd in ((3, False), (3, True), (8, True)):
            print(f"Checking cached and uncached signing at width {width}, cached SIMD {simd}", flush=True)
            src.write_text(probe.replace("PROOF_WIDTH", str(width)))
            subprocess.run(
                [
                    "rustc",
                    "--edition=2021",
                    *(["--cfg", "proof_simd"] if simd else []),
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
