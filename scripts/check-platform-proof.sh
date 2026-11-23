#!/bin/sh
# Re-extract the production architecture-specific functions and kernel-check their lane specifications.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
same_translation() {
  # Source positions move when an unrelated function changes size. Compare
  # every declaration, type, term, source path and macro origin.
  for side in 1 2; do
    case $side in 1) input=$1 ;; 2) input=$2 ;; esac
    sed -E "/^[[:space:]]+Source: '/s/lines [0-9]+:[0-9]+-[0-9]+:[0-9]+/lines <span>/g" "$input" > "$scratch/translation-$side"
  done
  cmp "$scratch/translation-1" "$scratch/translation-2" || {
    echo "Translation changed: $1 versus $2" >&2
    return 1
  }
}
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
    Parent512|Gather512|Keypadding|Store256|Digest256|Parentblock|Parentx86|Parentarm|Leaf256|Parent256|Chainni|Chainvectors|Chainwrite|Chainwide|Chainavx2|Chainx86|Wots|Wotsx86|Wotswide|Wotsapi|Treehash|Keccakscalar|Koriented|Shakeabs|Xmssroot|Xmsskeys|Streamround|Armstream|Streamstep|Streamscalar|Streamvector|X86remainder|X86stream) proofdir=lean-hw ;;
  esac
  mkdir "$scratch/$package"
  (cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas "$@" \
    --opaque "$opaque" --dest-file "$scratch/$llbc.llbc" -- \
    --locked --features platform-sha2 --target "$arch")
  .tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -namespace "$namespace" \
    -split-files -dest "$scratch/$package" "$scratch/$llbc.llbc"
  if [ "$package" = Armstream ] && [ "$arch" = aarch64-apple-darwin ]; then
    # Apple uses a separate SHA-512 single-block implementation. All definitions
    # reachable from both streaming entry points must match the Linux proof.
    same_translation "$scratch/$package/Types.lean" "$proofdir/$package/Types.lean"
    sed '/^\/-- \[slhdsa::sha512::compress\]:$/,/^$/d' "$proofdir/$package/Funs.lean" > "$scratch/shared-arm-stream"
    same_translation "$scratch/$package/Funs.lean" "$scratch/shared-arm-stream"
  else
    for name in Types Funs; do
      same_translation "$scratch/$package/$name.lean" "$proofdir/$package/$name.lean"
    done
  fi
  if [ "$package" = Keypadding ] || [ "$package" = Parentblock ] || [ "$package" = Streamround ] || [ "$package" = Keccakscalar ] || [ "$package" = Koriented ]; then
    # All operations in this extraction are implemented by Aeneas.
    for template in "$scratch/$package/"*External_Template.lean; do
      test ! -e "$template"
    done
    return
  fi
  if [ "$package" = Xmsskeys ]; then
    # Charon wraps the long mutable-chunk iterator declaration after the keyword.
    awk '/^axiom$/ { getline; print $1; next } /^axiom / { print $2 }' "$scratch/$package/"*External_Template.lean | LC_ALL=C sort > "$scratch/actual"
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
(cd lean-hw && lake build Leaf256.Fips && lake env lean --stdin > "$scratch/leaf-axioms.log" <<'LEAN'
import Leaf256.Fips
#print axioms slhdsa.X86.Leaf.fors_node_spec
#print axioms slhdsa.X86.Leaf.fors_leaves_spec
#print axioms slhdsa.X86.Leaf.short_block
#print axioms slhdsa.X86.Leaf.words_spec
#print axioms slhdsa.X86.Leaf.initial_spec
#print axioms slhdsa.X86.Leaf.first_two
#print axioms slhdsa.X86.Leaf.pack_words
LEAN
)
for name in fors_node_spec fors_leaves_spec short_block words_spec initial_spec first_two pack_words; do
  grep -Fx "'slhdsa.X86.Leaf.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/leaf-axioms.log"
done
extract Parent256 TreeRust parent256 --start-from 'crate::sha256::x86::fors_parents' \
  --opaque 'crate::sha256::x86::avx512_available' --opaque 'crate::sha256::x86::avx512::compress' \
  --opaque 'crate::sha256::x86::avx512::round' --opaque 'crate::sha256::x86::avx512::write_words'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
core.core_arch.x86.avx512f._mm512_or_si512
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_setzero_si512
core.core_arch.x86.avx512f._mm512_slli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi32
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
(cd lean-hw && lake build Parent256.Top && lake env lean --stdin > "$scratch/tree-axioms.log" <<'LEAN'
import Parent256.Top
#print axioms slhdsa.X86.Parent.pair_block
#print axioms slhdsa.X86.Parent.words_spec
#print axioms slhdsa.X86.Parent.initial_spec
#print axioms slhdsa.X86.Parent.first_four
#print axioms slhdsa.X86.Parent.gather_pairs
#print axioms slhdsa.X86.Parent.shuffled_pairs
#print axioms slhdsa.X86.Parent.read_child
#print axioms slhdsa.X86.Parent.pack_children
#print axioms slhdsa.X86.Parent.child_word
#print axioms slhdsa.X86.Parent.serialize_children
#print axioms slhdsa.X86.Parent.message_layout
#print axioms slhdsa.X86.Parent.prepare_spec
#print axioms slhdsa.X86.Parent.hash_batch_spec
#print axioms slhdsa.X86.Parent.children_intact
#print axioms slhdsa.X86.Parent.advance
#print axioms slhdsa.X86.Parent.batches_spec
#print axioms slhdsa.X86.Parent.fors_parents_spec
#print axioms slhdsa.X86.Parent.short_count
#print axioms slhdsa.X86.Parent.unsupported_width
LEAN
)
for name in pair_block words_spec initial_spec first_four gather_pairs shuffled_pairs read_child pack_children child_word serialize_children message_layout prepare_spec hash_batch_spec children_intact advance batches_spec fors_parents_spec short_count unsupported_width; do
  grep -Fx "'slhdsa.X86.Parent.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/tree-axioms.log"
done
extract Chainni ChainNiRust chainni --start-from 'crate::sha256::x86::chains' \
  --opaque 'crate::hash::chain_blocks_portable' --opaque 'crate::sha256::x86::compress_pair'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m128i
core.core_arch.x86.sse2._mm_set_epi32
core.core_arch.x86.sse2._mm_shuffle_epi32
core.core_arch.x86.sse41._mm_blend_epi16
core.core_arch.x86.ssse3._mm_alignr_epi8
hash.chain_blocks_portable
sha256.x86.compress_pair
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainni.Top && lake env lean --stdin > "$scratch/chainni-axioms.log" <<'LEAN'
import Chainni.Top
#print axioms slhdsa.Intel.Chain.chains_spec
#print axioms slhdsa.Intel.Chain.pack_spec
#print axioms slhdsa.Intel.Chain.shared_spec
#print axioms slhdsa.Intel.Chain.group_spec
LEAN
)
for name in chains_spec pack_spec shared_spec group_spec; do
  grep -Fx "'slhdsa.Intel.Chain.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/chainni-axioms.log"
done
extract Chainvectors ChainVectorRust chainvectors --start-from 'crate::sha256::x86::avx512::chain_address' \
  --start-from 'crate::sha256::x86::avx512::chain_value' --start-from 'crate::sha256::x86::avx512::chain_done'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m512i
core.core_arch.x86.avx512f._mm512_and_si512
core.core_arch.x86.avx512f._mm512_mask_mov_epi32
core.core_arch.x86.avx512f._mm512_or_si512
core.core_arch.x86.avx512f._mm512_slli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi32
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainvectors.Words && lake env lean --stdin > "$scratch/chainvectors-axioms.log" <<'LEAN'
import Chainvectors.Words
#print axioms slhdsa.X86.Chain.address_spec
#print axioms slhdsa.X86.Chain.value_spec
#print axioms slhdsa.X86.Chain.saved_spec
LEAN
)
for name in address_spec value_spec saved_spec; do
  grep -Fx "'slhdsa.X86.Chain.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/chainvectors-axioms.log"
done

extract Chainwrite ChainWriteRust chainwrite --start-from 'crate::sha256::x86::avx512::write_finished' \
  --opaque 'crate::sha256::x86::avx512::transpose_rows'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.sse2._mm_set_epi32
core.num.U16.trailing_zeros
sha256.x86.avx512.transpose_rows
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainwrite.Top && lake env lean --stdin > "$scratch/chainwrite-axioms.log" <<'LEAN'
import Chainwrite.Top
#print axioms slhdsa.X86.Chain.write_finished_spec
#print axioms slhdsa.X86.Chain.write_index_spec
#print axioms slhdsa.X86.Chain.write_chunk_spec
LEAN
)
for name in write_finished_spec write_index_spec write_chunk_spec; do
  grep -Fx "'slhdsa.X86.Chain.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/chainwrite-axioms.log"
done

extract Chainwide ChainWideRust chainwide --start-from 'crate::sha256::x86::avx512::chains' \
  --opaque 'crate::sha256::x86::chains' \
  --opaque 'crate::sha256::x86::avx512::compression_step' \
  --opaque 'crate::sha256::x86::avx512::round' \
  --opaque 'crate::sha256::x86::avx512::write_finished' \
  --opaque 'crate::sha256::x86::avx512::chain_address' \
  --opaque 'crate::sha256::x86::avx512::chain_value' \
  --opaque 'crate::sha256::x86::avx512::chain_done' \
  --opaque 'crate::sha256::x86::sha_ni::get'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.__m512i.Insts.CoreCloneClone.clone
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_and_si512
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_cmpeq_epi32_mask
core.core_arch.x86.avx512f._mm512_cmplt_epu32_mask
core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
core.core_arch.x86.avx512f._mm512_maskz_loadu_epi32
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_setzero_si512
core.core_arch.x86.sse2._mm_set_epi32
core.ptr.const_ptr.RawPtrConstT.add
core.ptr.const_ptr.RawPtrConstT.cast
core.slice.Slice.as_ptr
sha256.x86.avx512.chain_address
sha256.x86.avx512.chain_done
sha256.x86.avx512.chain_value
sha256.x86.avx512.compression_step
sha256.x86.avx512.round
sha256.x86.avx512.write_finished
sha256.x86.chains
sha256.x86.sha_ni.get
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainwide.Top && lake env lean --stdin > "$scratch/chainwide-axioms.log" <<'LEAN'
import Chainwide.Top
#print axioms slhdsa.X86.Chain.chains_spec
#print axioms slhdsa.X86.Chain.load_ranges_spec
#print axioms slhdsa.X86.Chain.iteration_spec
#print axioms slhdsa.X86.Chain.active_has_budget
#print axioms slhdsa.X86.Chain.compression_step_spec
#print axioms slhdsa.X86.Chain.start_mask
#print axioms slhdsa.X86.Chain.end_mask
#print axioms slhdsa.X86.Chain.input_words
#print axioms slhdsa.X86.Chain.broadcast_spec
#print axioms slhdsa.X86.Chain.prefix_spec
LEAN
)
for name in chains_spec input_words broadcast_spec prefix_spec compression_step_spec start_mask end_mask load_ranges_spec iteration_spec active_has_budget; do
  grep -Fx "'slhdsa.X86.Chain.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/chainwide-axioms.log"
done


extract Chainavx2 ChainAvx2Rust chainavx2 --start-from 'crate::sha256::x86::avx2::chains' \
  --opaque 'crate::sha256::x86::avx2::compress8' --opaque 'crate::hash::chain_blocks_portable'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m256i
core.core_arch.x86.avx._mm256_set1_epi32
core.intrinsics.transmute
core.slice.Slice.as_chunks_mut
hash.chain_blocks_portable
sha256.x86.avx2.compress8
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainavx2.Top && lake env lean --stdin > "$scratch/avx2-chain-axioms" <<'LEAN'
import Chainavx2.Top
#print axioms slhdsa.Avx2.Chain.chains_spec
#print axioms slhdsa.Avx2.Chain.groups_spec
#print axioms slhdsa.Avx2.Chain.batch_steps_spec
#print axioms slhdsa.Avx2.Chain.step_spec
#print axioms slhdsa.Avx2.Chain.store_bytes_spec
#print axioms slhdsa.Avx2.Chain.longest_spec
#print axioms slhdsa.Avx2.Chain.range_lengths_spec
#print axioms slhdsa.Avx2.Chain.addresses_spec
#print axioms slhdsa.Avx2.Chain.broadcast_spec
#print axioms slhdsa.Avx2.Chain.digest_lanes_spec
#print axioms slhdsa.Avx2.Chain.word_store_spec
#print axioms ChainAvx2Rust.chunks_roundtrip
LEAN
)
for name in slhdsa.Avx2.Chain.chains_spec slhdsa.Avx2.Chain.groups_spec slhdsa.Avx2.Chain.batch_steps_spec slhdsa.Avx2.Chain.step_spec slhdsa.Avx2.Chain.store_bytes_spec slhdsa.Avx2.Chain.longest_spec slhdsa.Avx2.Chain.range_lengths_spec slhdsa.Avx2.Chain.addresses_spec slhdsa.Avx2.Chain.broadcast_spec slhdsa.Avx2.Chain.digest_lanes_spec slhdsa.Avx2.Chain.word_store_spec ChainAvx2Rust.chunks_roundtrip; do
  grep -Fx "'$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/avx2-chain-axioms"
done


extract Chainx86 ChainX86Rust chainx86 --start-from 'crate::sha256::x86::chain_blocks' \
  --opaque 'crate::hash::chain_blocks_portable' --opaque 'crate::sha256::x86::avx2::chains' \
  --opaque 'crate::sha256::x86::avx512::chains' --opaque 'crate::sha256::x86::chains' \
  --opaque 'crate::sha256::x86::has_avx512::get' --opaque 'crate::sha256::x86::has_avx2::get' \
  --opaque 'crate::sha256::x86::sha_ni::get'
cat > "$scratch/expected" <<'NAMES'
hash.chain_blocks_portable
sha256.x86.avx2.chains
sha256.x86.avx512.chains
sha256.x86.chains
sha256.x86.has_avx2.get
sha256.x86.has_avx512.get
sha256.x86.sha_ni.get
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Chainx86.Top && lake env lean --stdin > "$scratch/x86-chain-axioms" <<'LEAN'
import Chainx86.Top
#print axioms slhdsa.X86.Dispatch.chains_spec
#print axioms slhdsa.X86.Dispatch.fallback_eq
LEAN
)
for name in chains_spec fallback_eq; do
  grep -Fx "'slhdsa.X86.Dispatch.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/x86-chain-axioms"
done


extract Wots WotsRust wots --start-from 'crate::sha256::x86::avx512::wots_endpoints' \
  --start-from 'crate::sha256::x86::avx512::recover' --opaque 'crate::sha256::x86::avx512::write_words' \
  --opaque 'crate::sha256::x86::avx512::round' --opaque 'crate::sha256::x86::avx512::compression_step' \
  --opaque 'crate::hash::short_block'
cat > "$scratch/expected" <<'NAMES'
core.array.Array.map
core.core_arch.x86.__m128i
core.core_arch.x86.__m512i
core.core_arch.x86.__m512i.Insts.CoreCloneClone.clone
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_and_si512
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_cmpeq_epi32_mask
core.core_arch.x86.avx512f._mm512_cmpge_epi32_mask
core.core_arch.x86.avx512f._mm512_loadu_si512
core.core_arch.x86.avx512f._mm512_mask_add_epi32
core.core_arch.x86.avx512f._mm512_mask_i32gather_epi32
core.core_arch.x86.avx512f._mm512_mask_mov_epi32
core.core_arch.x86.avx512f._mm512_mask_sub_epi32
core.core_arch.x86.avx512f._mm512_mullo_epi32
core.core_arch.x86.avx512f._mm512_or_si512
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_setzero_si512
core.core_arch.x86.avx512f._mm512_slli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi32
core.core_arch.x86.avx512f._mm512_xor_si512
core.core_arch.x86.sse2._mm_set_epi32
core.num.U16.trailing_zeros
core.ptr.const_ptr.RawPtrConstT.add
core.ptr.const_ptr.RawPtrConstT.cast
core.slice.Slice.as_ptr
core.slice.SliceArray.as_flattened
hash.short_block
sha256.x86.avx512.compression_step
sha256.x86.avx512.round
sha256.x86.avx512.write_words
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Wots.Slots Wots.Input Wots.Fips Wots.Serialize Wots.Address Wots.Driver Wots.Recovery && lake env lean --stdin > "$scratch/wots-axioms" <<'LEAN'
import Wots.Slots
import Wots.Input
import Wots.Fips
import Wots.Serialize
import Wots.Address
import Wots.Driver
import Wots.Recovery
#print axioms slhdsa.X86.Wots.account_retirement
#print axioms slhdsa.X86.Wots.loop_endpoints
#print axioms slhdsa.X86.Wots.recover_fips
#print axioms slhdsa.X86.Wots.change_chain_word
#print axioms slhdsa.X86.Wots.load_chains
#print axioms slhdsa.X86.Wots.cycle_chains
#print axioms slhdsa.X86.Wots.loaded_chain
#print axioms slhdsa.X86.Wots.advance_chain
#print axioms slhdsa.X86.Wots.recovery_descent
#print axioms slhdsa.X86.Wots.recovery_terminates
#print axioms slhdsa.X86.Wots.run_recovery_entry
#print axioms slhdsa.X86.Wots.recover_total
#print axioms slhdsa.X86.Wots.refill_owns
#print axioms slhdsa.X86.Wots.finish_owned
#print axioms slhdsa.X86.Wots.cycle_body_eq
#print axioms slhdsa.X86.Wots.recovery_f_spec
#print axioms slhdsa.X86.Wots.compress_round_spec
#print axioms slhdsa.X86.Wots.refill_load_spec
#print axioms slhdsa.X86.Wots.retire_spec
#print axioms slhdsa.X86.Wots.finish_spec
#print axioms slhdsa.X86.Wots.pack_high_spec
#print axioms slhdsa.X86.Wots.refill_spec
#print axioms slhdsa.X86.Wots.load_lanes_spec
#print axioms slhdsa.X86.Wots.signature_words
#print axioms slhdsa.X86.Wots.order_spec
#print axioms slhdsa.X86.Wots.order_partition
#print axioms slhdsa.X86.Wots.bypass_spec
#print axioms slhdsa.X86.Wots.preparation_spec
#print axioms slhdsa.X86.Wots.recover_eq
#print axioms slhdsa.X86.Wots.histogram_spec
#print axioms slhdsa.X86.Wots.offsets_spec
#print axioms slhdsa.X86.Wots.endpoints_fips
#print axioms slhdsa.X86.Wots.placed_lane
#print axioms slhdsa.X86.Wots.batch_frame
#print axioms slhdsa.X86.Wots.write_batch_spec
#print axioms slhdsa.X86.Wots.store_batch_eq
#print axioms slhdsa.X86.Wots.entry_spec
#print axioms slhdsa.X86.Wots.batch_body_eq
#print axioms slhdsa.X86.Wots.batch_fips
#print axioms slhdsa.X86.Wots.destination_spec
#print axioms slhdsa.X86.Wots.key_prf_fips
#print axioms slhdsa.X86.Wots.stage_spec
#print axioms slhdsa.X86.Wots.flatten_spec
#print axioms slhdsa.X86.Wots.copy_rows_spec
#print axioms slhdsa.X86.Wots.endpoint_chain_fips
#print axioms slhdsa.X86.Wots.chain_spec
#print axioms slhdsa.X86.Wots.step_spec
#print axioms slhdsa.X86.Wots.pack_spec
#print axioms slhdsa.X86.Wots.slot_regs_spec
#print axioms slhdsa.X86.Wots.words_spec
#print axioms slhdsa.X86.Wots.first_two
#print axioms slhdsa.X86.Wots.recovery_words
LEAN
)
for name in endpoint_chain_fips chain_spec step_spec pack_spec slot_regs_spec words_spec first_two recovery_words stage_spec flatten_spec copy_rows_spec destination_spec key_prf_fips batch_body_eq batch_fips entry_spec endpoints_fips placed_lane batch_frame write_batch_spec store_batch_eq histogram_spec offsets_spec order_spec order_partition bypass_spec preparation_spec recover_eq refill_spec load_lanes_spec signature_words refill_load_spec retire_spec finish_spec pack_high_spec recovery_f_spec compress_round_spec cycle_body_eq refill_owns finish_owned recovery_descent recovery_terminates run_recovery_entry recover_total loaded_chain advance_chain change_chain_word load_chains cycle_chains account_retirement loop_endpoints recover_fips; do
  grep -Fx "'slhdsa.X86.Wots.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/wots-axioms"
done

extract Wotsx86 WotsX86Rust wotsx86 --start-from 'crate::sha256::x86::wots_endpoints' \
  --start-from 'crate::sha256::x86::recover' --opaque 'crate::sha256::x86::avx512::wots_endpoints' \
  --opaque 'crate::sha256::x86::avx512::recover' --opaque 'crate::sha256::x86::has_avx512::get'
cat > "$scratch/expected" <<'NAMES'
sha256.x86.avx512.recover
sha256.x86.avx512.wots_endpoints
sha256.x86.has_avx512.get
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Wotsx86.Proof && lake env lean --stdin > "$scratch/wots-wrapper-axioms" <<'LEAN'
import Wotsx86.Proof
#print axioms slhdsa.X86.Wots.Checked.endpoints_fips
#print axioms slhdsa.X86.Wots.Checked.recover_fips
#print axioms slhdsa.X86.Wots.Checked.no_cpu
LEAN
)
for name in endpoints_fips recover_fips no_cpu; do
  grep -Fx "'slhdsa.X86.Wots.Checked.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/wots-wrapper-axioms"
done

extract Streamround StreamRoundRust streamround --start-from 'crate::sha256::stream::round' \
  --start-from 'crate::sha512::stream::round'
(cd lean-hw && lake build Streamround.Read && lake env lean --stdin > "$scratch/stream-round-axioms" <<'LEAN'
import Streamround.Read
#print axioms slhdsa.X86.Stream.read32
#print axioms slhdsa.X86.Stream.read64
#print axioms slhdsa.X86.Stream.load256
#print axioms slhdsa.X86.Stream.load512
#print axioms slhdsa.X86.Stream.expansion256
#print axioms slhdsa.X86.Stream.expansion512
#print axioms slhdsa.X86.Stream.round256_spec
#print axioms slhdsa.X86.Stream.round512_spec
LEAN
)
for name in round256_spec round512_spec read32 read64 load256 load512 expansion256 expansion512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/stream-round-axioms"
done

platform_arch=aarch64-unknown-linux-gnu
extract Armstream ArmStreamRust armstream --start-from 'crate::sha256::sha256_from' \
  --start-from 'crate::sha512::sha512_from' --start-from 'crate::sha512::compress' \
  --opaque 'sha2::sha256::compress256' --opaque 'sha2::sha512::compress512'
unset platform_arch
cat > "$scratch/expected" <<'NAMES'
core.slice.Slice.as_chunks
core.slice.raw.from_ref
sha2.sha256.compress256
sha2.sha512.compress512
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Armstream.Proof && lake env lean --stdin > "$scratch/arm-stream-axioms" <<'LEAN'
import Armstream.Proof
#print axioms slhdsa.PlatformStream.arm256_from
#print axioms slhdsa.PlatformStream.arm512_from
#print axioms slhdsa.PlatformStream.arm512_block
LEAN
)
for name in arm256_from arm512_from arm512_block; do
  grep -Fx "'slhdsa.PlatformStream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/arm-stream-axioms"
done

mv "$scratch/Armstream" "$scratch/Armstream-linux"
platform_arch=aarch64-apple-darwin
extract Armstream ArmStreamRust armstream --start-from 'crate::sha256::sha256_from' \
  --start-from 'crate::sha512::sha512_from' --opaque 'sha2::sha256::compress256' \
  --opaque 'sha2::sha512::compress512'
unset platform_arch
sed '/^core.slice.raw.from_ref$/d' "$scratch/expected" > "$scratch/expected-apple-stream"
cmp "$scratch/actual" "$scratch/expected-apple-stream"

extract Streamstep StreamStepRust streamstep --start-from 'crate::sha256::stream::read_word' \
  --start-from 'crate::sha512::stream::read_word' --start-from 'crate::sha256::stream::scalar_step' \
  --start-from 'crate::sha512::stream::scalar_step' --opaque 'crate::sha256::stream::round' \
  --opaque 'crate::sha512::stream::round'
cat > "$scratch/expected" <<'NAMES'
sha256.stream.round
sha512.stream.round
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Streamstep.Transition && lake env lean --stdin > "$scratch/stream-word-axioms" <<'LEAN'
import Streamstep.Transition
#print axioms slhdsa.X86.Stream.read_word256
#print axioms slhdsa.X86.Stream.read_word512
#print axioms slhdsa.X86.Stream.step256
#print axioms slhdsa.X86.Stream.step512
LEAN
)
for name in read_word256 read_word512 step256 step512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/stream-word-axioms"
done

extract Streamscalar StreamScalarRust streamscalar --start-from 'crate::sha256::stream::scalar' \
  --start-from 'crate::sha512::stream::scalar' --opaque 'crate::sha256::stream::read_word' \
  --opaque 'crate::sha512::stream::read_word' --opaque 'crate::sha256::stream::scalar_step' \
  --opaque 'crate::sha512::stream::scalar_step'
cat > "$scratch/expected" <<'NAMES'
sha256.stream.read_word
sha256.stream.scalar_step
sha512.stream.read_word
sha512.stream.scalar_step
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Streamscalar.Top && lake env lean --stdin > "$scratch/stream-scalar-axioms" <<'LEAN'
import Streamscalar.Top
#print axioms slhdsa.X86.Stream.scalar256
#print axioms slhdsa.X86.Stream.scalar512
LEAN
)
for name in scalar256 scalar512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/stream-scalar-axioms"
done

extract X86remainder X86RemainderRust x86remainder --start-from 'crate::sha256::compress' \
  --start-from 'crate::sha512::compress' --opaque 'crate::sha256::stream::scalar' \
  --opaque 'crate::sha512::stream::scalar' --opaque 'crate::sha256::stream::has_bmi2::get' \
  --opaque 'crate::sha512::stream::has_bmi2::get' --opaque 'crate::sha256::stream::dedicated::get' \
  --opaque 'crate::sha512::stream::dedicated::get' --opaque 'sha2::sha256::compress256' \
  --opaque 'sha2::sha512::compress512'
cat > "$scratch/expected" <<'NAMES'
core.slice.raw.from_ref
sha2.sha256.compress256
sha2.sha512.compress512
sha256.stream.dedicated.get
sha256.stream.has_bmi2.get
sha256.stream.scalar
sha512.stream.dedicated.get
sha512.stream.has_bmi2.get
sha512.stream.scalar
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build X86remainder.Proof && lake env lean --stdin > "$scratch/x86-rem-axioms" <<'LEAN'
import X86remainder.Proof
#print axioms slhdsa.X86.Stream.remainder256
#print axioms slhdsa.X86.Stream.remainder512
#print axioms slhdsa.X86.Stream.single256
#print axioms slhdsa.X86.Stream.single512
LEAN
)
for name in remainder256 remainder512 single256 single512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/x86-rem-axioms"
done

(cd lean-hw && lake build Streamvector.Controls Streamvector.Groups Streamscalar.Ordered && lake env lean --stdin > "$scratch/stream-gather-axioms" <<'LEAN'
import Streamvector.Controls
import Streamvector.Groups
import Streamscalar.Ordered
#print axioms slhdsa.X86.Stream.offsets256
#print axioms slhdsa.X86.Stream.offsets512
#print axioms slhdsa.X86.Stream.swap256
#print axioms slhdsa.X86.Stream.swap512
#print axioms slhdsa.X86.Stream.gathered256
#print axioms slhdsa.X86.Stream.gathered512
#print axioms slhdsa.X86.Stream.ordered_round256
#print axioms slhdsa.X86.Stream.ordered_round512
#print axioms slhdsa.X86.Stream.write_ordered256
#print axioms slhdsa.X86.Stream.write_ordered512
#print axioms slhdsa.X86.Stream.prefix_groups256
#print axioms slhdsa.X86.Stream.prefix_groups512
LEAN
)
for name in offsets256 offsets512 swap256 swap512 gathered256 gathered512 ordered_round256 ordered_round512 write_ordered256 write_ordered512 prefix_groups256 prefix_groups512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/stream-gather-axioms"
done

extract X86stream X86StreamRust x86stream --start-from 'crate::sha256::sha256_from' \
  --start-from 'crate::sha512::sha512_from' --opaque 'crate::sha256::stream::remainder' \
  --opaque 'crate::sha512::stream::remainder' --opaque 'crate::sha256::stream::prescheduled' \
  --opaque 'crate::sha512::stream::prescheduled' --opaque 'crate::sha256::stream::available::get' \
  --opaque 'crate::sha512::stream::available::get' --opaque 'crate::sha256::stream::dedicated::get'
cat > "$scratch/expected" <<'NAMES'
core.slice.Slice.as_chunks
sha256.stream.available.get
sha256.stream.dedicated.get
sha256.stream.prescheduled
sha256.stream.remainder
sha512.stream.available.get
sha512.stream.prescheduled
sha512.stream.remainder
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build X86stream.Top && lake env lean --stdin > "$scratch/x86-stream-top-axioms" <<'LEAN'
import X86stream.Top
#print axioms slhdsa.X86.Stream.stream256
#print axioms slhdsa.X86.Stream.stream512
#print axioms slhdsa.X86.Stream.continued256
#print axioms slhdsa.X86.Stream.continued512
#print axioms slhdsa.X86.Stream.short256
#print axioms slhdsa.X86.Stream.short512
#print axioms slhdsa.X86.Stream.fallback256
#print axioms slhdsa.X86.Stream.fallback512
LEAN
)
for name in stream256 stream512 continued256 continued512 short256 short512 fallback256 fallback512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/x86-stream-top-axioms"
done


extract Wotswide WotsWideRust wotswide --start-from 'crate::wots::wide::recover' \
  --opaque 'crate::sha256::x86::recover' --opaque 'crate::sha256::compress' --opaque 'crate::sha512::compress'
cat > "$scratch/expected" <<'NAMES'
sha256.compress
sha256.x86.recover
sha512.compress
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Wotswide.Recovery && lake env lean --stdin > "$scratch/wide-axioms" <<'LEAN'
import Wotswide.Recovery
#print axioms slhdsa.X86.Wots.Wide.thash_eq
#print axioms slhdsa.X86.Wots.Wide.recover_fips
LEAN
)
for name in thash_eq recover_fips; do
  grep -Fx "'slhdsa.X86.Wots.Wide.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/wide-axioms"
done

extract Wotsapi WotsApiRust wotsapi --start-from 'crate::wots::wots_pk_from_sig' \
  --opaque 'crate::wots::wide::recover' --opaque 'crate::sha256::x86::avx512_available' \
  --opaque 'crate::sha256::x86::chain_blocks' --opaque 'crate::hash::thash_values'
cat > "$scratch/expected" <<'NAMES'
hash.thash_values
sha256.x86.avx512_available
sha256.x86.chain_blocks
wots.wide.recover
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Wotsapi.Fallback && lake env lean --stdin > "$scratch/wotsapi-axioms" <<'LEAN'
import Wotsapi.Fallback
#print axioms slhdsa.X86.Wots.Api.recover_fips
LEAN
)
grep -Fx "'slhdsa.X86.Wots.Api.recover_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/wotsapi-axioms"

extract Streamvector StreamVectorRust streamvector --start-from 'crate::sha256::stream::prescheduled' \
  --start-from 'crate::sha512::stream::prescheduled' --opaque 'crate::sha256::stream::round' \
  --opaque 'crate::sha512::stream::round'
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m128i
core.core_arch.x86.__m256i
core.core_arch.x86.__m512i
core.core_arch.x86.avx._mm256_set_epi32
core.core_arch.x86.avx512bw._mm512_shuffle_epi8
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_add_epi64
core.core_arch.x86.avx512f._mm512_broadcast_i32x4
core.core_arch.x86.avx512f._mm512_i32gather_epi32
core.core_arch.x86.avx512f._mm512_i32gather_epi64
core.core_arch.x86.avx512f._mm512_ror_epi32
core.core_arch.x86.avx512f._mm512_ror_epi64
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_set1_epi64
core.core_arch.x86.avx512f._mm512_set_epi32
core.core_arch.x86.avx512f._mm512_srli_epi32
core.core_arch.x86.avx512f._mm512_srli_epi64
core.core_arch.x86.avx512f._mm512_ternarylogic_epi32
core.core_arch.x86.avx512f._mm512_ternarylogic_epi64
core.core_arch.x86.sse2._mm_set_epi32
core.intrinsics.transmute
core.ptr.const_ptr.RawPtrConstT.add
core.ptr.const_ptr.RawPtrConstT.cast
core.slice.Slice.as_ptr
sha256.stream.round
sha512.stream.round
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Streamvector.Top && lake env lean --stdin > "$scratch/vector-axioms" <<'LEAN'
import Streamvector.Top
#print axioms slhdsa.X86.Stream.prescheduled256
#print axioms slhdsa.X86.Stream.prescheduled512
LEAN
)
for name in prescheduled256 prescheduled512; do
  grep -Fx "'slhdsa.X86.Stream.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/vector-axioms"
done

extract Xmsskeys XmssKeysRust xmsskeys --start-from 'crate::xmss::wide::keys' \
  --opaque 'crate::xmss::wide::prepare_message' --opaque 'crate::sha256::x86::wots_endpoints' \
  --opaque 'crate::sha256::x86::key_digests' --opaque 'crate::sha512::x86::key_digests'
cat > "$scratch/expected" <<'NAMES'
core.slice.Slice.chunks_mut
core.slice.iter.ChunksMut
core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next
sha256.x86.key_digests
sha256.x86.wots_endpoints
sha512.x86.key_digests
xmss.wide.prepare_message
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Xmsskeys.Top && lake env lean --stdin > "$scratch/xmsskeys-axioms" <<'LEAN'
import Xmsskeys.Top
#print axioms slhdsa.X86.Wots.keyBatch_fips
#print axioms slhdsa.X86.Wots.endpoint_payload
#print axioms slhdsa.X86.XmssKeys.keys_fips
#print axioms slhdsa.X86.XmssKeys.tree_leaves
LEAN
)
for name in Wots.keyBatch_fips Wots.endpoint_payload XmssKeys.keys_fips XmssKeys.tree_leaves; do
  grep -Fx "'slhdsa.X86.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/xmsskeys-axioms"
done

extract Treehash TreeHashRust treehash --start-from 'crate::xmss::hash2' \
  --opaque 'crate::sha256::compress' --opaque 'crate::sha512::compress'
cat > "$scratch/expected" <<'NAMES'
sha256.compress
sha512.compress
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Treehash.Proof && lake env lean --stdin > "$scratch/treehash-axioms" <<'LEAN'
import Treehash.Proof
#print axioms slhdsa.X86.TreeHash.hash2_fips
LEAN
)
grep -Fx "'slhdsa.X86.TreeHash.hash2_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/treehash-axioms"

extract Xmssroot XmssRootRust xmssroot --start-from 'crate::xmss::wide::batch_root' \
  --opaque 'crate::xmss::wide::keys' --opaque 'crate::xmss::hash2'
cat > "$scratch/expected" <<'NAMES'
xmss.hash2
xmss.wide.keys
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Xmssroot.Top && lake env lean --stdin > "$scratch/xmssroot-axioms" <<'LEAN'
import Xmssroot.Top
#print axioms slhdsa.X86.XmssRoot.batch_root_fips
LEAN
)
grep -Fx "'slhdsa.X86.XmssRoot.batch_root_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/xmssroot-axioms"

platform_arch=i686-unknown-linux-gnu
extract Keccakscalar KeccakScalarRust keccakscalar --start-from 'crate::shake256::permute'
extract Shakeabs ShakeAbsRust shakeabs --start-from 'crate::shake256::shake256' --opaque 'crate::shake256::permute'
echo 'shake256.permute' > "$scratch/expected"
cmp "$scratch/actual" "$scratch/expected"
(cd lean-hw && lake build Shakeabs.Top && lake env lean --stdin > "$scratch/shakeabs-axioms" <<'LEAN'
import Shakeabs.Top
#print axioms slhdsa.PlatformShake.shake256_fips
LEAN
)
grep -Fx "'slhdsa.PlatformShake.shake256_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/shakeabs-axioms"

unset platform_arch
python3 "$root/scripts/check-arm-api-proof.py"
python3 "$root/scripts/check-platform-encoding.py"
python3 "$root/scripts/check-portable-shake.py"
sh "$root/scripts/check-keccak-assembly.sh"
platform_arch=aarch64-unknown-linux-gnu
extract Koriented KorientedRust koriented --start-from 'crate::shake256::oriented::permute'
(cd lean-hw && lake build Koriented.Permutation && lake env lean --stdin > "$scratch/oriented-axioms" <<'LEAN'
import Koriented.Permutation
#print axioms slhdsa.Oriented.permute_fips
LEAN
)
grep -Fx "'slhdsa.Oriented.permute_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/oriented-axioms"
