import Kdiag.Chi
open Aeneas Aeneas.Std Result
namespace slhdsa.Kdiag
open KdiagRust.core.core_arch.x86.avx512f
def addConstant (rc : U64) (s : Grid) : Result Grid := do
  let old ← s.index_usize 0#usize
  let i ← lift (UScalar.hcast .I64 rc)
  let k ← _mm512_set1_epi64 i
  let v ← _mm512_mask_xor_epi64 old 1#u8 old k
  s.update 0#usize v

theorem iota_spec (rc : U64) (s : Grid) : addConstant rc s ⦃ out =>
    ∀ (i : Nat), i<5 → ∀ j : Fin 8, out.val[i]! j =
      if i=0 ∧ j.val=0 then s.val[i]! j ^^^ rc.bv else s.val[i]! j ⦄ := by
  unfold addConstant
  step as ⟨old,hr⟩
  simp only [lift,_mm512_set1_epi64,KavxRust.core.core_arch.x86.avx512f._mm512_set1_epi64,
    _mm512_mask_xor_epi64,bind_ok]
  step as ⟨out,ho⟩
  rename_i i hi j
  rw [ho,Array.set_val_eq,getElem!_pos _ i (by simp; omega),List.getElem_set]
  by_cases iz : i=0
  · subst i
    fin_cases j <;> simp [hr,getElem!_pos]
  · simp [iz,Ne.symm iz,getElem!_pos s.val i (by simpa using hi)]
end slhdsa.Kdiag
