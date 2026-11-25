import Cachepath.NativeVerify.WordsProgram
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify
open ShakeBatch

theorem seed_spec {N : Usize} (seed : Array U8 N) (bound : N.val≤32) :
    seed_words seed ⦃ out => ∀ k < 4, out.val[k]!.bv =
      if k<N.val/8 then inputWord seed.val k else 0 ⦄ := by
  unfold seed_words
  step as ⟨count,div⟩
  unfold seed_words_loop
  apply WP.spec_mono (range_fold (seed_words_loop.body seed) count _ (fun i out =>
    ∀ k < 4, out.val[k]!.bv = if k < i then inputWord seed.val k else 0) ?_ ?_ ?_)
  · intro out h; simpa only [div] using h
  · intro k hk; interval_cases k <;> rfl
  · intro it s stop live prev
    unfold seed_words_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag,lift,bind_ok]
    step with word_spec seed.to_slice it.start (by simp;omega) as ⟨w,h⟩
    step as ⟨out,upd⟩
    refine ⟨next,out,rfl,ends.trans stop,idx,?_⟩
    intro k hk
    rw [upd,Array.set_val_eq]
    by_cases eq : it.start.val=k
    · subst k
      rw [setSame _ _ _ (by simpa),h,ite_eq_left_iff.mpr (by omega)]
      simp only [Array.val_to_slice,inputWord]
    · rw [setOther _ _ _ _ eq,prev k hk]
      by_cases small : k < it.start.val <;> simp only [small,ite_true,ite_false,show (k < next.start.val) ↔ k < it.start.val by omega]
  · intro it s done stop
    unfold seed_words_loop.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,done]))
    simp [no,tag]

private theorem treeBytes (v : U64) : Spec.toByte v.val 12 = [0,0,0,0] ++ Spec.toByte v.val 8 := by
  have high (k : Nat) (bound : 64 ≤ k) : v.val >>> k = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (v.hBounds.trans_le (Nat.pow_le_pow_right (by decide) bound))
  change [BitVec.ofNat 8 (v.val >>> 88),BitVec.ofNat 8 (v.val >>> 80),
    BitVec.ofNat 8 (v.val >>> 72),BitVec.ofNat 8 (v.val >>> 64)] ++ Spec.toByte v.val 8 = _
  rw [high 88 (by decide),high 80 (by decide),high 72 (by decide),high 64 (by decide)]
  rfl

private theorem swapTree (v : U64) : swap64 v ⦃ out =>
    out.bv = Spec.Keccak.laneBytes 0 (Spec.toByte v.val 8) ⦄ := by
  simp only [swap64,WP.spec_ok]
  change _ = Spec.Keccak.laneBytes 0 (Spec.toByte v.bv.toNat 8)
  rw [toByte8]
  simp only [Spec.Keccak.laneBytes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (v.bv.extractLsb' 0 8 ++ v.bv.extractLsb' 8 8 ++ v.bv.extractLsb' 16 8 ++ v.bv.extractLsb' 24 8 ++ v.bv.extractLsb' 32 8 ++ v.bv.extractLsb' 40 8 ++ v.bv.extractLsb' 48 8 ++ v.bv.extractLsb' 56 8).getLsbD i = _
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_setWidth,BitVec.getLsbD_setWidth',BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp (config := {decide := true}) [BitVec.getLsbD_of_ge]

open cache.builder.nativeShake.Vector.Fused in
private theorem pair32 (x y : U32) :
    Spec.Keccak.laneBytes 0 (Spec.toByte x.val 4 ++ Spec.toByte y.val 4) = addressLow x ||| wordTag y := by
  let zero : address.Adrs := ⟨0#u32,0#u64,0#u32,0#u32,0#u32,0#u32⟩
  exact packed_address zero x y 3 (by decide)

open cache.builder.nativeShake.Vector.Fused in
theorem address_spec (a : address.Adrs) : adrs_words a ⦃ out =>
    ∀ i < 4, out.val[i]!.bv = addressWord a i ⦄ := by
  unfold adrs_words
  simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
  step with swapTree a.tree as ⟨tree,tw⟩
  step as ⟨hi,_,hb⟩
  step as ⟨last,_,lb⟩
  have addr := treeBytes a.tree
  intro i bound
  interval_cases i
  · change addressLow a.layer = _
    unfold addressWord
    simp only [adrsS,Spec.Adrs.bytes,addr]
    change _ = Spec.Keccak.laneBytes 0 (Spec.toByte a.layer.val 4 ++ Spec.toByte 0 4)
    simpa [wordTag] using (pair32 a.layer 0#u32).symm
  · change tree.bv = _
    rw [tw]
    unfold addressWord
    simp only [adrsS,Spec.Adrs.bytes,addr]
    rfl
  · change (addressLow a.typ ||| hi.bv) = _
    refine (congrArg (fun v : BitVec 64 => addressLow a.typ ||| v) hb).trans ?_
    change _ = Spec.Keccak.laneBytes 0 (Spec.toByte a.typ.val 4 ++ Spec.toByte a.keypair.val 4)
    exact (pair32 _ _).symm
  · change (addressLow a.word2 ||| last.bv) = _
    refine (congrArg (fun v : BitVec 64 => addressLow a.word2 ||| v) lb).trans ?_
    change _ = Spec.Keccak.laneBytes 0 (Spec.toByte a.word2.val 4 ++ Spec.toByte a.word3.val 4)
    exact (pair32 _ _).symm

end slhdsa.NativeVerify
