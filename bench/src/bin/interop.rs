//! Interoperability sanity check, run before any timing.
//!
//! For each implementation and message length (32 B, 1 KiB):
//!  1. keygen from the same seeds gives byte-identical SK and PK to the verified crate;
//!  2. the verified crate's (deterministic) signature verifies under it;
//!  3. its own signature with the same SK verifies under the verified crate;
//!  4. where it signs deterministically, its signature is byte-identical to the verified crate's;
//!  5. a signature with one flipped bit is rejected.
//! Exits non-zero if any FIPS 205 implementation disagrees with the verified crate.
use slhdsa_bench::*;

fn main() {
    let v = verified();
    let (sk, pk) = (v.keygen)(&SK_SEED, &SK_PRF, &PK_SEED);
    let mut failures = 0;
    println!("| implementation | scheme | same SK/PK from seeds | verifies verified-crate sig | its sig verifies under verified crate | sig bytes identical | rejects tampered |");
    println!("|---|---|---|---|---|---|---|");
    for imp in all() {
        let (isk, ipk) = (imp.keygen)(&SK_SEED, &SK_PRF, &PK_SEED);
        let same_keys = isk == sk && ipk == pk;
        let mut ok_verify_ours = true;
        let mut ok_ours_verify_theirs = true;
        let mut identical = true;
        let mut rejects = true;
        for mlen in [32usize, 1024] {
            let m = message(mlen);
            let ours = (v.make_signer)(&sk)(&m);
            let theirs = (imp.make_signer)(&sk)(&m);
            let iv = (imp.make_verifier)(&pk);
            ok_verify_ours &= iv(&m, &ours);
            ok_ours_verify_theirs &= (v.make_verifier)(&pk)(&m, &theirs);
            identical &= ours == theirs;
            let mut bad = theirs.clone();
            bad[SIG_BYTES / 2] ^= 1;
            rejects &= !iv(&m, &bad) && iv(&m, &theirs);
        }
        let yn = |b: bool| if b { "yes" } else { "NO" };
        let det = if imp.deterministic { yn(identical) } else if identical { "yes (?)" } else { "n/a (randomised)" };
        println!(
            "| {} | {} | {} | {} | {} | {} | {} |",
            imp.name,
            if imp.fips205 { "FIPS 205" } else { "SPHINCS+ r3" },
            yn(same_keys),
            yn(ok_verify_ours),
            yn(ok_ours_verify_theirs),
            det,
            yn(rejects)
        );
        if imp.fips205 && !(same_keys && ok_verify_ours && ok_ours_verify_theirs && identical && rejects) {
            failures += 1;
        }
        if !imp.fips205 && !rejects {
            failures += 1;
        }
    }
    if failures > 0 {
        eprintln!("INTEROP FAILURES: {failures}");
        std::process::exit(1);
    }
}
