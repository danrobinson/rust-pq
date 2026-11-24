#!/usr/bin/env python3
"""Make a checksummed source distribution from the committed HEAD."""
import argparse
import gzip
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile
import tomllib


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("dist"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]

    def git(*args):
        return subprocess.check_output(["git", *args], cwd=root).decode().strip()

    commit = git("rev-parse", "HEAD")
    versions = {
        tomllib.loads(git("show", f"{commit}:{crate}/Cargo.toml"))["package"]["version"]
        for crate in ("rust", "compat")
    }
    if len(versions) != 1:
        parser.error("the Rust crates have different versions")
    name = f"rust-pq-{versions.pop()}"
    dest = args.output.resolve()
    dest.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dest) as stage:
        archive = Path(stage) / f"{name}.tar.gz"
        with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
            with subprocess.Popen(
                ["git", "archive", "--format=tar", f"--prefix={name}/", commit],
                cwd=root, stdout=subprocess.PIPE,
            ) as proc:
                shutil.copyfileobj(proc.stdout, gz)
                if proc.wait():
                    raise SystemExit("git archive failed")
        with archive.open("rb") as source:
            digest = hashlib.file_digest(source, "sha256").hexdigest()
        checksum = archive.with_suffix(".gz.sha256")
        checksum.write_text(f"{digest}  {archive.name}\n")
        for artifact in (archive, checksum):
            artifact.replace(dest / artifact.name)
    print(f"{commit}  {dest / archive.name}")


if __name__ == "__main__":
    main()
