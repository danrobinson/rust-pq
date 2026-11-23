import Parent256.Driver
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Parent
open TreeRust.sha256.x86.avx512
open Spec.SHA256

theorem kernel_spec (p : Spec.Params) (pk : Spec.Bytes) (s : Array U32 8#usize)
    (a : TreeRust.address.Adrs) (first : U32) (rows : Rows) (count : Usize)
    (family : p.family = .sha2) (width : p.n = 16) (hpk : pk.length = 16)
    (seed : s.val.map (·.bv) = seedState 16 pk)
    (bound : 2*count.val ≤ rows.length) (indices : first.val+count.val ≤ 2^32)
    (size : 32*count.val ≤ Usize.max) :
    fors_parents s a first rows count ⦃ r =>
      Processed (expected p pk (adrsS (addressOf a)) first rows) rows r count.val ⦄ := by
  let A := adrsS (addressOf a)
  unfold fors_parents
  simp only [TreeRust.address.Adrs.with_word3,bind_ok]
  step with pair_block _ _ _ as ⟨b,hb⟩
  have eq : bytes b.val = template A := by
    rw [hb]
    rfl
  step with words_spec 16#usize b as ⟨base,hbase⟩
  rw [eq] at hbase
  step with initial_spec 16#usize s as ⟨iv,hiv⟩
  step with first_four iv base (fun _ => template A) hbase as ⟨pre,hpre⟩
  simp only [TreeRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    TreeRust.core.core_arch.x86.avx512f._mm512_slli_epi32,LeafRust.core.core_arch.x86.avx512f._mm512_slli_epi32,
    _root_.core.core_arch.x86.sse2._mm_set_epi32,TreeRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    DigestRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,bind_ok]
  step as ⟨it,hit,hstep⟩
  have eit : it = ⟨⟨0#usize,count⟩,16#usize⟩ := by cases it; simp_all
  rw [eit]
  have lanes : (fun j : Fin 16 => [(0#i32).bv,(1#i32).bv,(2#i32).bv,(3#i32).bv,(4#i32).bv,(5#i32).bv,(6#i32).bv,(7#i32).bv,(8#i32).bv,(9#i32).bv,(10#i32).bv,(11#i32).bv,(12#i32).bv,(13#i32).bv,(14#i32).bv,(15#i32).bv][j.val]!) =
      fun j => BitVec.ofNat 32 j.val := by funext j; fin_cases j <;> decide
  rw [lanes]
  apply batches_spec p pk A base iv pre _ first rows count family width hpk hbase
    (fun j => (Leaf.initial_words iv s hiv j).trans seed) hpre _ bound indices size
  intro j; fin_cases j <;> decide

theorem fors_parents_spec (p : Spec.Params) (pk : Spec.Bytes) (s : Array U32 8#usize)
    (a : TreeRust.address.Adrs) (first : U32) (rows : Rows) (count : Usize)
    (family : p.family = .sha2) (width : p.n = 16) (hpk : pk.length = 16)
    (seed : s.val.map (·.bv) = seedState 16 pk) (cpu : GatherRust.avx512Available = true)
    (bound : 2*count.val ≤ rows.length) (indices : first.val+count.val ≤ 2^32)
    (size : 32*count.val ≤ Usize.max) :
    TreeRust.sha256.x86.fors_parents s a first rows count ⦃ n r =>
      if count.val < 2 then n = 0#usize ∧ r = rows
      else n = count ∧ Processed (expected p pk (adrsS (addressOf a)) first rows) rows r count.val ⦄ := by
  unfold TreeRust.sha256.x86.fors_parents
  simp only [bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  by_cases small : count < 2#usize
  · simp [small,show count.val < 2 from small,step_simps]
  · simp only [if_neg small,if_neg (show ¬count.val < 2 from small)]
    simp only [TreeRust.sha256.x86.avx512_available,DigestRust.sha256.x86.avx512_available,
      GatherRust.sha256.x86.avx512_available,cpu,bind_ok,massert,↓reduceIte]
    step as ⟨half,hh⟩
    have le : count ≤ half := by scalar_tac
    simp only [le,decide_true,↓reduceIte,bind_ok]
    step with kernel_spec p pk s a first rows count family width hpk seed bound indices size as ⟨r,hr⟩
    exact hr

theorem short_count (s : Array U32 8#usize) (a : TreeRust.address.Adrs)
    (first : U32) (rows : Rows) (count : Usize) (short : count < 2#usize) :
    TreeRust.sha256.x86.fors_parents s a first rows count = ok (0#usize,rows) := by
  simp [TreeRust.sha256.x86.fors_parents,short]

theorem unsupported_width (N : Usize) (s : Array U32 8#usize) (a : TreeRust.address.Adrs)
    (first : U32) (rows : Slice (Array U8 N)) (count : Usize) (width : N ≠ 16#usize) :
    TreeRust.sha256.x86.fors_parents s a first rows count = ok (0#usize,rows) := by
  simp [TreeRust.sha256.x86.fors_parents,width]

end slhdsa.X86.Parent
