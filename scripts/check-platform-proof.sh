#!/bin/sh
# Re-extract the production architecture-specific functions and kernel-check their lane specifications.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
extract() {
  package=$1
  namespace=$2
  llbc=$3
  shift 3
  arch=x86_64-unknown-linux-gnu
  opaque=core::core_arch
  proofdir=lean
  if [ "$package" = Paired ]; then
    arch=aarch64-unknown-linux-gnu
    opaque=slhdsa::sha512::hw::arm
    proofdir=lean-hw
  fi
  if [ "$package" = Parent512 ]; then
    proofdir=lean-hw
  fi
  mkdir "$scratch/$package"
  (cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas "$@" \
    --opaque "$opaque" --dest-file "$scratch/$llbc.llbc" -- \
    --locked --features platform-sha2 --target "$arch")
  .tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -namespace "$namespace" \
    -split-files -dest "$scratch/$package" "$scratch/$llbc.llbc"
  for name in Types Funs; do
    cmp "$scratch/$package/$name.lean" "$proofdir/$package/$name.lean"
  done
  sed -n 's/^axiom \([^ :]*\).*/\1/p' "$scratch/$package/"*External_Template.lean | LC_ALL=C sort > "$scratch/actual"
}
extract Platform PlatformRust platform --start-from 'crate::sha256::x86::avx512::compress' \
  --start-from 'crate::sha512::x86::compress'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m512i
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_add_epi64
core.core_arch.x86.avx512f._mm512_ror_epi32
core.core_arch.x86.avx512f._mm512_ror_epi64
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set1_epi64
core.core_arch.x86.avx512f._mm512_srli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi64
core.core_arch.x86.avx512f._mm512_ternarylogic_epi32
core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
NAMES
cmp "$scratch/actual" "$scratch/expected"
extract Avx2 Avx2Rust avx2 --start-from 'crate::sha256::x86::avx2::compress8'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m256i
core.core_arch.x86.__m256i.Insts.CoreCloneClone.clone
core.core_arch.x86.avx._mm256_set1_epi32
core.core_arch.x86.avx._mm256_set_epi32
core.core_arch.x86.avx._mm256_setzero_si256
core.core_arch.x86.avx2._mm256_add_epi32
core.core_arch.x86.avx2._mm256_and_si256
core.core_arch.x86.avx2._mm256_andnot_si256
core.core_arch.x86.avx2._mm256_or_si256
core.core_arch.x86.avx2._mm256_slli_epi32
core.core_arch.x86.avx2._mm256_srli_epi32
core.core_arch.x86.avx2._mm256_xor_si256
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean && lake build Platform && lake env lean --stdin > "$scratch/axioms" <<'LEAN'
import Platform
#print axioms slhdsa.X86.round_spec
#print axioms slhdsa.X86.compress_spec
#print axioms slhdsa.X86.S512.compress_spec
LEAN
)
for name in round_spec compress_spec S512.compress_spec; do
  grep -Fx "'slhdsa.X86.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
done
(cd lean-hw && lake build Slhdsa.Proofs.Platform && lake env lean Slhdsa/Proofs/Platform.lean > "$scratch/blocks")
for name in X86 X86.S512 Avx2; do
  grep -Fx "'slhdsa.$name.compress_block_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/blocks"
done
extract Paired PairedRust paired --start-from 'crate::sha512::paired::compress_parents'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.arm_shared.neon.uint64x2_t
sha512.hw.arm.add
sha512.hw.arm.ext1
sha512.hw.arm.load_be
sha512.hw.arm.load_words
sha512.hw.arm.sha512h
sha512.hw.arm.sha512h2
sha512.hw.arm.sha512su0
sha512.hw.arm.sha512su1
sha512.hw.arm.store_words
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Paired.Proof && lake env lean --stdin > "$scratch/paired-axioms.log" <<'LEAN'
import Paired.Proof
#print axioms slhdsa.H512.Paired.parents_spec
LEAN
)
grep -Fx "'slhdsa.H512.Paired.parents_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/paired-axioms.log"
extract Shani ShaNiRust shani --start-from 'crate::sha256::x86::compress_pair'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m128i
core.core_arch.x86.sha._mm_sha256msg1_epu32
core.core_arch.x86.sha._mm_sha256msg2_epu32
core.core_arch.x86.sha._mm_sha256rnds2_epu32
core.core_arch.x86.sse2._mm_add_epi32
core.core_arch.x86.sse2._mm_set_epi32
core.core_arch.x86.sse2._mm_shuffle_epi32
core.core_arch.x86.sse41._mm_extract_epi32
core.core_arch.x86.ssse3._mm_alignr_epi8
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Slhdsa.Proofs.ShaNi && lake env lean --stdin > "$scratch/shani-axioms.log" <<'LEAN'
import Slhdsa.Proofs.ShaNi
#print axioms slhdsa.Intel.compress_pair_spec
LEAN
)
grep -Fx "'slhdsa.Intel.compress_pair_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/shani-axioms.log"

extract Parent512 ParentsRust parent512 --start-from 'crate::sha512::x86::compress_parents'
cat > "$scratch/expected" <<'NAMES'
Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
core.array.Array.map
core.array.iter.IntoIter
core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
core.core_arch.x86.__m512i
core.core_arch.x86.avx512f._mm512_add_epi64
core.core_arch.x86.avx512f._mm512_ror_epi64
core.core_arch.x86.avx512f._mm512_set1_epi64
core.core_arch.x86.avx512f._mm512_srli_epi64
core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
core.intrinsics.transmute
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Parent512.Proof && lake env lean --stdin > "$scratch/parent512-axioms.log" <<'LEAN'
import Parent512.Proof
#print axioms slhdsa.X86.S512.Parents.parents_spec
LEAN
)
grep -Fx "'slhdsa.X86.S512.Parents.parents_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/parent512-axioms.log"
