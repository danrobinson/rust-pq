#!/usr/bin/env python3
"""Prove the two crates split every digest into identical FORS digits and XMSS indices."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SIZES = {"128s": 30, "128f": 34, "192s": 39, "192f": 42, "256s": 47, "256f": 49}


def append(file, code):
    with file.open("a") as out:
        out.write("\n" + code + "\n")


def metadata(manifest):
    data = subprocess.check_output(["cargo", "metadata", "--locked", "--format-version", "1",
                                    "--manifest-path", str(manifest)])
    return json.loads(data)


def registry_checksums(lock):
    # These fields are all single-line strings in Cargo's generated lockfile.
    result = {}
    for section in lock.read_text().split("[[package]]")[1:]:
        fields = dict(re.findall(r'^(name|version|source|checksum) = "([^"]+)"$', section, re.M))
        if "checksum" in fields:
            result[fields["name"], fields["version"], fields["source"]] = fields["checksum"]
    return result


def unpack_peer(peer, dest, checksum):
    source = Path(peer["manifest_path"]).parent
    prefix = source.name
    archive = source.parents[2]/"cache"/source.parent.name/(prefix+".crate")
    if hashlib.sha256(archive.read_bytes()).hexdigest() != checksum:
        raise ValueError("RustCrypto archive differs from benchmark lock")
    with tarfile.open(archive) as packed:
        for item in packed:
            path = Path(item.name).relative_to(prefix)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError("invalid path in crate")
            if not item.isfile():
                if item.isdir():
                    continue
                raise ValueError("unexpected entry in crate")
            (dest/path).parent.mkdir(parents=True, exist_ok=True)
            (dest/path).write_bytes(packed.extractfile(item).read())


def setup(p):
    locked = metadata(ROOT / "bench/Cargo.toml")
    peer, = [x for x in locked["packages"] if x["name"] == "slh-dsa"]
    if peer["version"] != "0.2.0-rc.5":
        raise ValueError("unexpected RustCrypto version")
    # Only append observation functions in the scratch copies; private methods stay intact.
    pins = registry_checksums(ROOT/"bench/Cargo.lock")
    unpack_peer(peer,p/"peer",pins[peer["name"],peer["version"],peer["source"]])
    ours = p/"ours"
    ours.mkdir()
    shutil.copytree(ROOT/"rust/src", ours/"src")
    shutil.copy2(ROOT/"rust/Cargo.toml", ours)
    append(ours/"src/slh.rs", '''
pub fn observed_indices(p: &Params, digest: &[u8]) -> (u64, u32) {
    (digest_tree(p, digest), digest_leaf(p, digest))
}
''')
    (p/"Cargo.toml").write_text('''[package]
name="peer-digest-proof"
version="0.1.0"
edition="2021"
[dependencies]
slh-dsa={path="peer"}
slhdsa={path="ours"}
''')
    shutil.copy2(ROOT/"bench/Cargo.lock", p/"Cargo.lock")
    (p/"src").mkdir()
    harnesses = []
    for suffix, length in SIZES.items():
        for family in ("sha2","shake"):
            name = f"{family}_{suffix}"
            ty = ("Sha2_" if family == "sha2" else "Shake") + suffix
            append(p/"peer/src/lib.rs", f'''
/// Observe the native digest decomposition for the proof harness.
pub fn observed_{name}(bytes: &[u8; {length}]) -> (&[u8], u64, u32, alloc::vec::Vec<u16>) {{
    let digest = bytes.into();
    let (md, tree, leaf) = util::split_digest::<{ty}>(digest);
    let digits = util::base_2b::<<{ty} as fors::ForsParams>::K, <{ty} as fors::ForsParams>::A>(md);
    (md.as_slice(), tree, leaf, digits.to_vec())
}}''')
            slh = "slhdsa::shake::slh" if family == "shake" else "slhdsa::slh"
            harnesses.append(f'''
#[kani::proof]
#[kani::unwind(80)]
fn check_{name}() {{
    let bytes: [u8; {length}] = kani::any();
    let p = &slhdsa::params::SHA2_{suffix.upper()};
    let (md, tree, leaf, digits) = slh_dsa::observed_{name}(&bytes);
    assert_eq!(md, &bytes[..p.md_bytes()]);
    let indices = {slh}::observed_indices(p, &bytes);
    assert_eq!((tree, leaf), indices);
    let ours = slhdsa::util::base_2b(&bytes[..p.md_bytes()], p.a, p.k as usize);
    assert_eq!(ours.len(), digits.len());
    for i in 0..ours.len() {{
        assert_eq!(ours[i], u32::from(digits[i]));
    }}
}}''')
    (p/"src/lib.rs").write_text("#![cfg(kani)]\n" + "\n".join(harnesses))
    # Cargo prunes benchmark-only packages. Enforce identical registry versions and sources.
    subprocess.run(["cargo","metadata","--offline","--format-version","1"],cwd=p,
                   stdout=subprocess.DEVNULL,check=True)
    for key, checksum in registry_checksums(p/"Cargo.lock").items():
        if pins.get(key) != checksum:
            raise ValueError(f"unpinned dependency: {key}")



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--harness", help="check a single named harness")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="slh-digest-proof-") as directory:
        p = Path(directory)
        setup(p)
        subprocess.run(["cargo","kani"] + (["--harness",args.harness] if args.harness else []),
                       cwd=p,check=True)


if __name__ == "__main__":
    main()
