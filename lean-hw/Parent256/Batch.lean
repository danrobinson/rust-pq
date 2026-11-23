import Parent256.Message
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open Spec.SHA256

def hashBatch (base : Array Reg 16#usize) (iv pre : Array Reg 8#usize) (idx : Reg)
    (rows : Slice (Array U8 16#usize)) (stride : Reg) (start : Usize) (mask : U16)
    (dst : Slice (Array U8 16#usize)) := do
  let w ← prepare base idx rows stride start mask
  let h ← TreeRust.sha256.x86.avx512.compress iv pre w
  TreeRust.sha256.x86.avx512.write_words h dst

theorem hash_batch_spec (p : Spec.Params) (pk : Spec.Bytes) (A : Spec.Adrs)
    (base : Array Reg 16#usize) (iv pre : Array Reg 8#usize) (idx stride : Reg)
    (rows dst : Slice (Array U8 16#usize)) (start : Usize) (mask : U16)
    (family : p.family = .sha2) (width : p.n = 16) (hpk : pk.length = 16)
    (hw : ∀ k, k < 16 → ∀ j, base.val[k]! j = word (template A) (4*k))
    (seed : ∀ j, stateWords (laneState iv j) = seedState 16 pk)
    (hp : Trace pre (fun _ => schedule (template A)) (laneState iv) 4)
    (hm : Digest.Mask mask dst.length) (hs : Digest.Stride stride 32)
    (hn : 0 < dst.length) (hl : dst.length ≤ 16) (bound : 2*(start.val+dst.length) ≤ rows.length)
    (size : 32*(start.val+dst.length) ≤ Usize.max) :
    hashBatch base iv pre idx rows stride start mask dst ⦃ r => r.length = dst.length ∧
      ∀ j : Fin 16, j.val < dst.length → bytes r.val[j.val]!.val =
        Spec.H p pk {A with word3 := (idx j).toNat} (children rows (start.val+j.val)) ⦄ := by
  letI : Fact (p.family = .sha2) := ⟨family⟩
  unfold hashBatch
  step with prepare_spec base idx rows stride start mask dst.length hm hs hn bound size as ⟨w,hw'⟩
  let B := fun j => Leaf.blockOf (parentWords (fun k => base.val[k]! j)
      (fun k => sourceWord rows start.val dst.length k j) (idx j))
  have words (k : Nat) (hk : k < 16) (j) : w.val[k]! j = word (B j) (4*k) := by
    rw [Leaf.word_blockOf _ _ hk]; exact hw' k hk j
  have prefix_ok : Trace pre (fun j => schedule (B j)) (laneState iv) 4 := by
    apply Leaf.transfer_prefix (by decide) _ hp
    intro j k hk
    rw [Leaf.word_blockOf _ _ (by omega)]
    simp (disch := omega) only [parentWords,if_neg,hw]
  step with compress_block_spec iv pre w B prefix_ok words as ⟨d,hd⟩
  apply WP.spec_mono (Store.write_words_spec d dst (Or.inl rfl) hl)
  rintro r ⟨hlen,hr⟩
  refine ⟨hlen,fun j hj => ?_⟩
  have beq : B j = padFrom 64 ({A with word3 := (idx j).toNat}.compress ++ children rows (start.val+j.val)) := by
    rw [← message_layout _ _ _ _ (idx j).isLt,BitVec.ofNat_toNat]
    apply Leaf.block_congr
    intro k hk
    simp (disch := omega) only [B,parentWords,hw,sourceWord,if_pos hj,BitVec.setWidth_eq]
  have ws := hd j
  change stateWords (laneState d j) = Spec.SHA256.compress (stateWords (laneState iv j)) (B j) at ws
  rw [beq,seed] at ws
  let digest := stateWords (laneState d j)
  have nw : digest.length = 8 := rfl
  have len : (children rows (start.val+j.val)).length = 32 := by simp [children]
  have fips : (ser digest).take 16 = Spec.H p pk {A with word3 := (idx j).toNat} (children rows (start.val+j.val)) := by
    rw [H_eq,width,if_pos rfl]
    unfold digest
    rw [ws]
    exact th256_one 16 pk hpk (by decide) _ _ (by omega)
  rw [← fips]
  apply List.ext_getElem
  · simp [ser_length,nw]
  · intro k hk _
    have h : k < 16 := by simpa using hk
    have byte := hr j hj k h
    unfold Store.digestByte at byte
    rw [show d.val[k/4]! j = digest[k/4]! from Leaf.lane_lookup d j _ (by omega),
        getElem!_pos _ _ (by simpa using h)] at byte
    have enc := Digest.ser_byte digest k (by omega)
    rw [getElem!_pos _ _ (by rw [ser_length,nw]; omega)] at enc
    simp only [bytes,List.getElem_map,List.getElem_take]
    exact byte.trans enc.symm

end slhdsa.X86.Parent
