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
    Parent512|Gather512|Keypadding|Store256|Digest256|Parentblock|Parentx86|Parentarm|Leaf256|Parent256|Chainni|Chainvectors|Chainwrite|Chainwide|Chainavx2|Chainx86|Wots) proofdir=lean-hw ;;
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
(cd lean-hw && lake build Wots.Slots Wots.Input Wots.Fips Wots.Serialize Wots.Address Wots.Driver && lake env lean --stdin > "$scratch/wots-axioms" <<'LEAN'
import Wots.Slots
import Wots.Input
import Wots.Fips
import Wots.Serialize
import Wots.Address
import Wots.Driver
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
for name in endpoint_chain_fips chain_spec step_spec pack_spec slot_regs_spec words_spec first_two recovery_words stage_spec flatten_spec copy_rows_spec destination_spec key_prf_fips batch_body_eq batch_fips entry_spec endpoints_fips placed_lane batch_frame write_batch_spec store_batch_eq; do
  grep -Fx "'slhdsa.X86.Wots.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/wots-axioms"
done
