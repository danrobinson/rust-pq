import Chainwide.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open ChainWideRust.core.core_arch.x86.avx512f

/-- Logical range membership after t compressions. Arithmetic here is unbounded. -/
abbrev Live (start stop : Reg) (t : Nat) (j : Fin 16) := (start j).toNat+t < (stop j).toNat

def Schedule (start stop current : Reg) (active : U16) (t : Nat) :=
  (∀ j : Fin 16, active.bv.getLsbD j.val = decide (Live start stop t j)) ∧
  ∀ j : Fin 16, Live start stop t j → (current j).toNat = (start j).toNat+t

def advance (current stop : Reg) (active : U16) : Result (Reg × U16) := do
  let one ← core.core_arch.x86.avx512f._mm512_set1_epi32 1#i32
  let next ← core.core_arch.x86.avx512f._mm512_add_epi32 current one
  let eq ← _mm512_cmpeq_epi32_mask next stop
  ok (next,active &&& eq)

theorem advance_spec (start stop current : Reg) (active : U16) (t : Nat)
    (sched : Schedule start stop current active t) :
    advance current stop active ⦃ next finished =>
      (∀ j : Fin 16, finished.bv.getLsbD j.val =
        decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat)) ∧
      Schedule start stop next (active &&& ~~~finished) (t+1) ⦄ := by
  simp only [advance,core.core_arch.x86.avx512f._mm512_set1_epi32,
    core.core_arch.x86.avx512f._mm512_add_epi32,_mm512_cmpeq_epi32_mask,bind_ok,step_simps]
  obtain ⟨mask,atStep⟩ := sched
  let next : Reg := fun j => current j + 1
  let equal := laneMask fun j => next j == stop j
  change (∀ j : Fin 16, (active.bv &&& equal.bv).getLsbD j.val = _) ∧
    Schedule start stop next (active &&& ~~~(active &&& equal)) (t+1)
  have succVal (j) (h : Live start stop t j) : (next j).toNat = (start j).toNat+t+1 := by
    have curr := atStep j h
    have lim := (stop j).isLt
    unfold Live at h
    change (current j + 1#32).toNat = _
    rw [BitVec.toNat_add_of_lt (by change (current j).toNat+1 < 2^32; omega),curr]
    rfl
  have doneBit (j : Fin 16) : (active.bv &&& equal.bv).getLsbD j.val =
      decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat) := by
    rw [BitVec.getLsbD_and,mask j,lane_mask]
    by_cases h : Live start stop t j
    · simp only [h,decide_true,Bool.true_and,true_and,beq_iff_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,decide_eq_true_eq]
      rw [← succVal j h]
      exact ⟨fun e => congrArg BitVec.toNat e,BitVec.eq_of_toNat_eq⟩
    · simp [h]
  refine ⟨doneBit,fun j => ?_,fun j h => ?_⟩
  · change (active.bv &&& ~~~(active.bv &&& equal.bv)).getLsbD j.val = _
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,doneBit,mask]
    simp only [j.isLt,decide_true,Bool.true_and,Live]
    by_cases live : (start j).toNat+t < (stop j).toNat <;>
      by_cases last : (start j).toNat+t+1 = (stop j).toNat <;> simp [live,last] <;> omega
  · exact succVal j (by unfold Live at *; omega)

def loadRanges (starts ends : Slice U32) (offset : Usize) (mask : U16) := do
  let start ← loadCounters starts offset mask
  let stop ← loadCounters ends offset mask
  let less ← _mm512_cmplt_epu32_mask start stop
  ok (start,stop,less &&& mask)

theorem load_ranges_spec (starts ends : Slice U32) (offset : Usize) (mask : U16)
    (hs : offset.val ≤ starts.length) (he : offset.val ≤ ends.length)
    (valid : ∀ j : Fin 16, mask.bv.getLsbD j.val → offset.val+j.val < min starts.length ends.length) :
    loadRanges starts ends offset mask ⦃ start stop active =>
      Schedule start stop start active 0 ∧
      (∀ j : Fin 16, start j = if mask.bv.getLsbD j.val then starts.val[offset.val+j.val]!.bv else 0) ∧
      (∀ j : Fin 16, stop j = if mask.bv.getLsbD j.val then ends.val[offset.val+j.val]!.bv else 0) ⦄ := by
  unfold loadRanges
  step with load_counters_spec starts offset mask hs (fun j h => lt_of_lt_of_le (valid j h) (Nat.min_le_left _ _)) as ⟨start,hstart⟩
  step with load_counters_spec ends offset mask he (fun j h => lt_of_lt_of_le (valid j h) (Nat.min_le_right _ _)) as ⟨stop,hstop⟩
  step with start_mask start stop as ⟨less,hless⟩
  refine ⟨⟨fun j => ?_,fun _ _ => rfl⟩,hstart,hstop⟩
  change (less.bv &&& mask.bv).getLsbD j.val = _
  rw [BitVec.getLsbD_and,hless]
  cases h : mask.bv.getLsbD j.val <;> simp only [Live,Nat.add_zero,hstart j,hstop j,h,Bool.false_eq_true,ite_false,ite_true,Bool.and_true,Bool.and_false,lt_self_iff_false,decide_false]

theorem all_finished (start stop : Reg) (t : Nat) (orig finished : U16)
    (initial : ∀ j : Fin 16, orig.bv.getLsbD j.val = decide (Live start stop 0 j))
    (last : ∀ j : Fin 16, finished.bv.getLsbD j.val =
      decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat))
    (all : finished = orig) : ∀ j, ¬ Live start stop (t+1) j := by
  intro j live
  have init : Live start stop 0 j := by unfold Live at *; omega
  have isLast := last j
  rw [all,initial j,decide_eq_true init] at isLast
  have heq := (of_decide_eq_true isLast.symm).2
  unfold Live at live
  omega

theorem active_has_budget (start stop current : Reg) (active : U16) (t : Nat)
    (s : Schedule start stop current active t) (work : active ≠ 0#u16) : t < 2^32-1 := by
  have nz : active.bv ≠ 0 := by intro eq; apply work; apply U16.bv_eq_imp_eq; exact eq
  let j : Fin 16 := ⟨active.bv.ctz.toNat,by
    have h := BitVec.ctz_lt_iff_ne_zero.mpr nz
    exact h⟩
  have set : active.bv.getLsbD j.val = true := BitVec.getLsbD_true_ctz_of_ne_zero nz
  rw [s.1 j] at set
  have live := of_decide_eq_true set
  unfold Live at live
  have bound := (stop j).isLt
  omega

end slhdsa.X86.Chain
