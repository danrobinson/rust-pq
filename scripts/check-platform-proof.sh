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
  arch=${platform_arch:-x86_64-unknown-linux-gnu}
  opaque=core::core_arch
  proofdir=lean
  if [ "$package" = Paired ]; then
    arch=aarch64-unknown-linux-gnu
    opaque=slhdsa::sha512::hw::arm
    proofdir=lean-hw
  fi
  case "$package" in
    Parent512|Gather512|Keypadding|Store256|Digest256|Parentblock|Parentx86|Parentarm|Leaf256) proofdir=lean-hw ;;
  esac
  mkdir "$scratch/$package"
  (cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas "$@" \
    --opaque "$opaque" --dest-file "$scratch/$llbc.llbc" -- \
    --locked --features platform-sha2 --target "$arch")
  .tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -namespace "$namespace" \
    -split-files -dest "$scratch/$package" "$scratch/$llbc.llbc"
  for name in Types Funs; do
    cmp "$scratch/$package/$name.lean" "$proofdir/$package/$name.lean"
  done
  if [ "$package" = Keypadding ] || [ "$package" = Parentblock ]; then
    # All operations in this extraction are implemented by Aeneas.
    for template in "$scratch/$package/"*External_Template.lean; do
      test ! -e "$template"
    done
    return
  fi
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

extract Gather512 GatherRust gather512 --start-from 'crate::sha512::x86::key_digests' \
  --opaque 'crate::sha256::x86::avx512_available'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m128i
core.core_arch.x86.__m256i
core.core_arch.x86.__m512i
core.core_arch.x86.avx._mm256_set1_epi32
core.core_arch.x86.avx._mm256_set_epi32
core.core_arch.x86.avx2._mm256_mullo_epi32
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_add_epi64
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_mask_i32gather_epi64
core.core_arch.x86.avx512f._mm512_ror_epi64
core.core_arch.x86.avx512f._mm512_set1_epi64
core.core_arch.x86.avx512f._mm512_setzero_si512
core.core_arch.x86.avx512f._mm512_srli_epi64
core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
core.core_arch.x86.sse2._mm_set_epi32
core.intrinsics.transmute
core.ptr.const_ptr.RawPtrConstT.add
core.ptr.const_ptr.RawPtrConstT.cast
core.slice.Slice.as_ptr
sha256.x86.avx512_available
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Gather512.Fips && lake env lean --stdin > "$scratch/gather512-axioms.log" <<'LEAN'
import Gather512.Fips
#print axioms slhdsa.X86.S512.Gather.key_digests_spec
#print axioms slhdsa.X86.S512.Gather.tweakable_digest_spec
LEAN
)
for name in key_digests_spec tweakable_digest_spec; do
  grep -Fx "'slhdsa.X86.S512.Gather.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/gather512-axioms.log"
done

extract Keypadding PadRust keypadding --start-from 'crate::xmss::wide::prepare_message'
(cd lean-hw && lake build Keypadding.Proof && lake env lean --stdin > "$scratch/keypadding-axioms.log" <<'LEAN'
import Keypadding.Proof
#print axioms slhdsa.X86.Keypadding.prepare_message_spec
#print axioms slhdsa.X86.Keypadding.padded_endpoints
LEAN
)
for name in prepare_message_spec padded_endpoints; do
  grep -Fx "'slhdsa.X86.Keypadding.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/keypadding-axioms.log"
done

extract Store256 StoreRust store256 --start-from 'crate::sha256::x86::avx512::write_words'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_unpackhi_epi32
core.core_arch.x86.avx512f._mm512_unpackhi_epi64
core.core_arch.x86.avx512f._mm512_unpacklo_epi32
core.core_arch.x86.avx512f._mm512_unpacklo_epi64
core.core_arch.x86.sse2._mm_set_epi32
core.intrinsics.transmute
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Store256.Proof && lake env lean --stdin > "$scratch/store256-axioms.log" <<'LEAN'
import Store256.Proof
#print axioms slhdsa.X86.Store.write_words_spec
LEAN
)
grep -Fx "'slhdsa.X86.Store.write_words_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/store256-axioms.log"

extract Digest256 DigestRust digest256 --start-from 'crate::sha256::x86::key_digests' \
  --opaque 'crate::sha256::x86::avx512_available' --opaque 'crate::sha256::x86::avx512::compress' \
  --opaque 'crate::sha256::x86::avx512::round' --opaque 'crate::sha256::x86::avx512::write_words'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
core.core_arch.x86.avx512f._mm512_mullo_epi32
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_setzero_si512
core.core_arch.x86.sse2._mm_set_epi32
core.ptr.const_ptr.RawPtrConstT.add
core.ptr.const_ptr.RawPtrConstT.cast
core.slice.Slice.as_ptr
sha256.x86.avx512.compress
sha256.x86.avx512.round
sha256.x86.avx512.write_words
sha256.x86.avx512_available
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Digest256.Fips && lake env lean --stdin > "$scratch/digest256-axioms.log" <<'LEAN'
import Digest256.Fips
#print axioms slhdsa.X86.Digest.key_digests_spec
#print axioms slhdsa.X86.Digest.tweakable_digest_spec
LEAN
)
for name in key_digests_spec tweakable_digest_spec; do
  grep -Fx "'slhdsa.X86.Digest.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/digest256-axioms.log"
done

# The same parent message constructor is compiled on both architectures.
for platform_arch in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu; do
  extract Parentblock ParentBlockRust parentblock --start-from 'crate::sha512::parents::parent_block'
  rm -r "$scratch/Parentblock"
done
unset platform_arch
(cd lean-hw && lake build Parentblock.Fips && lake env lean --stdin > "$scratch/parentblock-axioms.log" <<'LEAN'
import Parentblock.Fips
#print axioms slhdsa.PlatformParent.parent_block_spec
#print axioms slhdsa.PlatformParent.x86_parents
#print axioms slhdsa.PlatformParent.arm_parents
LEAN
)
for name in parent_block_spec x86_parents arm_parents; do
  grep -Fx "'slhdsa.PlatformParent.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/parentblock-axioms.log"
done

for package in Parentx86 Parentarm; do
  case "$package" in
    Parentx86) driver_llbc=parentx86; platform_arch=x86_64-unknown-linux-gnu
      available=sha256.x86.avx512_available
      compress=sha512.x86.compress_parents ;;
    Parentarm) driver_llbc=parentarm; platform_arch=aarch64-unknown-linux-gnu
      available=sha512.hw.arm.available
      compress=sha512.paired.compress_parents ;;
  esac
  extract "$package" "${package}Rust" "$driver_llbc" \
    --start-from 'crate::sha512::parents::parents' --start-from 'crate::sha512::parents::path_parents' \
    --opaque 'crate::address' --opaque 'crate::sha512::parents::parent_block' \
    --opaque 'crate::sha256::x86::avx512_available' --opaque 'crate::sha512::x86::compress_parents' \
    --opaque 'crate::sha512::paired::compress_parents' --opaque 'crate::sha512::hw::arm::available'
  printf '%s\n' address.Adrs address.Adrs.with_word3 sha512.parents.parent_block \
    "$available" "$compress" | LC_ALL=C sort > "$scratch/expected"
  cmp "$scratch/actual" "$scratch/expected"
done
unset platform_arch
(cd lean-hw && lake build Parentdriver.Proof && lake env lean Parentdriver/Proof.lean > "$scratch/driver-axioms.log")
for name in unsupported_width x86_tree_spec arm_tree_spec x86_path_spec arm_path_spec; do
  grep -Fx "'slhdsa.PlatformParent.Driver.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/driver-axioms.log"
done

extract Leaf256 LeafRust leaf256 --start-from 'crate::sha256::x86::fors_leaves' \
  --opaque 'crate::sha256::x86::avx512_available' --opaque 'crate::sha256::x86::avx512::compress' \
  --opaque 'crate::sha256::x86::avx512::round' --opaque 'crate::sha256::x86::avx512::write_words'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m512i
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_and_si512
core.core_arch.x86.avx512f._mm512_or_si512
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_slli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi32
core.core_arch.x86.avx512f._mm512_xor_si512
sha256.x86.avx512.compress
sha256.x86.avx512.round
sha256.x86.avx512.write_words
sha256.x86.avx512_available
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Leaf256.Prefix Leaf256.Pack && lake env lean --stdin > "$scratch/leaf-axioms.log" <<'LEAN'
import Leaf256.Pack
import Leaf256.Prefix
#print axioms slhdsa.X86.Leaf.short_block
#print axioms slhdsa.X86.Leaf.words_spec
#print axioms slhdsa.X86.Leaf.initial_spec
#print axioms slhdsa.X86.Leaf.first_two
#print axioms slhdsa.X86.Leaf.pack_words
LEAN
)
for name in short_block words_spec initial_spec first_two pack_words; do
  grep -Fx "'slhdsa.X86.Leaf.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/leaf-axioms.log"
done
