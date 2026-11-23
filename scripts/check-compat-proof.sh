#!/bin/sh
# Re-extract the adapter from its production crate, then verify the trait methods
# against each feature build of the core.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
(cd compat && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas \
  --dest-file "$scratch/facade.llbc" --opaque 'slhdsa::params::Params' \
  --start-from '{impl crate::params::Core for _}' \
  --start-from '{impl signature::Signer for crate::signing_key::SigningKey}::try_sign' \
  --start-from '{impl signature::Verifier for crate::verifying_key::VerifyingKey}::verify' \
  --start-from 'crate::signing_key::SigningKey::try_sign_with_context' \
  --start-from 'crate::verifying_key::VerifyingKey::try_verify_with_context' \
  -- --locked)
"$root/.tools/aeneas/bin/aeneas" -backend lean -abort-on-error -no-progress-bar \
  -dest "$scratch" -split-files "$scratch/facade.llbc"
for f in Types Funs; do cmp "$scratch/$f.lean" "lean/Facade/$f.lean"; done
for project in lean lean-hw; do
  (cd "$project" && lake build Facade)
  for file in Multipart Sign Verify; do
    (cd "$project" && lake env lean "Facade/$file.lean") > "$scratch/axioms"
    expected=$(grep -c '^#print axioms ' "$project/Facade/$file.lean")
    checked=$(grep -Fc 'depends on axioms: [propext, Classical.choice, Quot.sound]' "$scratch/axioms" || true)
    [ "$expected" -gt 0 ] && [ "$checked" -eq "$expected" ] || {
      cat "$scratch/axioms" >&2
      exit 1
    }
  done
done
