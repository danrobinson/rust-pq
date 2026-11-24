import Xmsskeys.Group
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys

def prepareAll (G L : Usize) (a : XmssKeysRust.address.Adrs) (first : U32) (size block : Usize) := do
  let messages := Array.repeat G (Array.repeat L 0#u8)
  let (s,back) ← lift (Array.to_slice_mut messages)
  let (it,iterBack) ← core.slice.Slice.iter_mut s
  let (e,enumBack) ← XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default
    (XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT (Array U8 L)) it
  let (endIt,write) ← XmssKeysRust.xmss.wide.keys_loop0_loop0 e id a first size block
  ok (back (iterBack (enumBack (write endIt))))

theorem prepareAll_spec (G L : Usize) (a : XmssKeysRust.address.Adrs) (first : U32) (size block : Usize)
    (keys : first.val+G.val≤2^32) (minSize : 22≤size.val) (maxSize : size.val+3≤L.val)
    (bits : (block.val+size.val)*8<65536) :
    prepareAll G L a first size block ⦃ rows => ∀ j<G.val,
      initialized (Array.repeat L 0#u8) rows.val[j]! a first size block j ⦄ := by
  let all := Array.repeat G (Array.repeat L 0#u8)
  unfold prepareAll
  simp only [Array.to_slice_mut,lift,core.slice.Slice.iter_mut,
    XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_eq,bind_ok]
  apply WP.spec_bind (preparedRows all.to_slice a first size block (by simpa [all] using keys) minSize maxSize bits)
  rintro ⟨endIt,write⟩ ⟨count,correct⟩
  simp only [step_simps]
  have len : (write endIt).iter.slice.val.length=G.val := by simpa [all,Slice.length] using count
  rw [Array.from_slice_val _ _ len]
  intro j hj
  simpa [all,Array.val_to_slice,Array.repeat_val,hj] using correct j (by simpa [all] using hj)

def oneGroup {N} (G L : Usize) (seed : XmssKeysRust.hash.Seed N) (sk : Array U8 N)
    (a : XmssKeysRust.address.Adrs) (first : U32) (len group : Usize) (out : Wots.Rows N) := do
  let offset ← group * G
  let key ← first + (UScalar.cast .U32 offset)
  let bytes ← len * N
  let size ← 22#usize + bytes
  let block := if N=16#usize then 64#usize else 128#usize
  let rows ← prepareAll G L a key size block
  digestPrefix seed sk a key rows out

theorem group_spec {N} (G L : Usize) (p : params.Params) (hp : PN p N) (seed : XmssKeysRust.hash.Seed N)
    (hs : SeedOk (seedOf seed)) (sk : Array U8 N) (a : XmssKeysRust.address.Adrs) (first : U32)
    (len group : Usize) (out : Wots.Rows N) (cpu : GatherRust.avx512Available=true) (format : shape N G L)
    (count : len.val=2*N.val+3) (keys : first.val+group.val*G.val+G.val≤2^32)
    (nonempty : 0<out.length) (used : out.length≤G.val) :
    oneGroup G L seed sk a first len group out ⦃ final => final.length=out.length ∧ ∀ j<out.length,
      bytes final.val[j]!.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
        (Wots.leafAddress (XmssKeysRust.asChecked a) (first.val+group.val*G.val+j)) ⦄ := by
  have positive : 0<G.val := by rcases format with h|h|h <;> omega
  unfold oneGroup
  step as ⟨offset,hOff⟩
  all_goals try (have h : group.val*G.val≤4294967295 := by omega; scalar_tac)
  have cast : (UScalar.cast .U32 offset).val=offset.val := by scalar_tac
  step as ⟨key,hKey⟩
  all_goals try scalar_tac
  have lengths : 22+len.val*N.val+3≤L.val ∧ (128+(22+len.val*N.val))*8<65536 := by
    rw [count]; rcases format with ⟨n,g,l⟩|⟨n,g,l⟩|⟨n,g,l⟩ <;> rw [n,l] <;> decide
  step as ⟨byteCount,hBytes⟩
  all_goals try scalar_tac
  step as ⟨size,hSize⟩
  all_goals try scalar_tac
  let block : Usize := if N=16#usize then 64#usize else 128#usize
  have bits : (block.val+size.val)*8<65536 := by unfold block; split <;> scalar_tac
  step with prepareAll_spec G L a key size block (by omega) (by scalar_tac) (by omega) bits as ⟨rows,prepared⟩
  have proof := digestPrefix_spec p hp seed hs sk a key rows out size block cpu format rfl
    (by rw [hSize,hBytes,count]) (by omega) used nonempty prepared
  simpa only [hKey,cast,hOff] using proof
end slhdsa.X86.XmssKeys
