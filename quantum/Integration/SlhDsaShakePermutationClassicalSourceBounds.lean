import Integration.SlhDsaShakePermutationClassicalSource
import Integration.SlhDsaShakePermutationClassicalByteBudget

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA PQ.Interactive
noncomputable section
variable (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T)
    (g : Completion.Private T) (caps : Fix.Domain T → Capacity) (side : Port → Words)

def playerCost (X Y : Type) (pc sc : ℕ) : (Compression.ClassicalPort.Reads X Y SignSpec).Domain → ℕ
  | .inl _ => pc
  | .inr (.inl _) => 0
  | .inr (.inr _) => sc

local notation "CW" => playerCost (ShakeApi.Input N) (Bytes S.vp.params.m)

theorem row_cost {Z : Type} (pc sc q : ℕ) (j : Row T) (cont : Words → OracleComp (Source S N) Z)
    (hk : ∀ y, WCount (CW pc sc) (cont y) q) : WCount (CW pc sc) (rowCall S N T cap g caps side j cont) (q+pc) := by
  cases j with
  | inr u => exact (hk _).mono (Nat.le_add_right ..)
  | inl a =>
    cases h : ShakeXof.locate (Completion.address cap) a with
    | none => simpa only [rowCall,h] using (hk _).mono (Nat.le_add_right q pc)
    | some x =>
      simp only [rowCall,h]
      rw [wCount_query_bind]
      exact ⟨Nat.le_add_left ..,fun y => (hk _).mono (by change q ≤ q+pc-pc; omega)⟩

theorem source_cost {Z : Type} (pc sc : ℕ) (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Z)
    (q : ℕ) (budget : WCount (playerCost Port Words pc sc) P q) (t : EdgeTrace Words) :
    WCount (CW pc sc) (sourceProgram S N T cap g caps side P t) q := by
  induction P using OracleComp.inductionOn generalizing q t with
  | pure => trivial
  | query_bind i k ih =>
    rcases i with ⟨d,x⟩|n|msg
    · have price : pc ≤ q := budget.1
      have next (u : Words) (t') := ih u _ (budget.2 u) t'
      change WCount _ (if h : old t d x then sourceProgram _ _ _ _ _ _ _ (k h.choose) t else rowCall _ _ _ _ _ _ _ _ _) _
      split
      · exact (next _ t).mono (Nat.sub_le ..)
      · exact (row_cost S N T cap g caps side pc sc (q-pc) _ _ (fun u => next u (edge d x u::t))).mono (by omega)
    · change 0 ≤ q ∧ _
      exact ⟨Nat.zero_le _,fun u => ih _ _ (budget.2 u) _⟩
    · change sc ≤ q ∧ _
      exact ⟨budget.1,fun u => ih _ _ (budget.2 u) _⟩

theorem row_cap {Z : Type} (c : Caps) (out : Z → Prop) (j : Row T) (cont : Words → OracleComp (Source S N) Z)
    (hk : ∀ y, AllQueries (readCap (X := ShakeApi.Input N) (Y := Bytes S.vp.params.m) c) out (cont y)) :
    AllQueries (readCap (X := ShakeApi.Input N) (Y := Bytes S.vp.params.m) c) out (rowCall S N T cap g caps side j cont) := by
  cases j with
  | inr => exact hk _
  | inl a =>
    cases h : ShakeXof.locate (Completion.address cap) a with
    | none => simpa only [rowCall,h] using hk _
    | some x =>
      simp only [rowCall,h]
      rw [QMsg.allQ_query_bind]
      exact ⟨trivial,fun _ => hk _⟩

theorem source_cap {Z : Type} (c : Caps) (out : Z → Prop) (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Z)
    (ok : AllQueries (readCap (X := Port) (Y := Words) c) out P) (t : EdgeTrace Words) :
    AllQueries (readCap (X := ShakeApi.Input N) (Y := Bytes S.vp.params.m) c) out (sourceProgram S N T cap g caps side P t) := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure => exact ok
  | query_bind i k ih =>
    rw [QMsg.allQ_query_bind] at ok
    rcases i with ⟨d,x⟩|n|msg
    · change AllQueries _ _ (if h : old t d x then sourceProgram _ _ _ _ _ _ _ (k h.choose) t else rowCall _ _ _ _ _ _ _ _ _)
      split
      · exact ih _ (ok.2 _) _
      · exact row_cap _ _ _ _ _ _ _ _ _ _ _ (fun u => ih _ (ok.2 _) _)
    · exact ⟨trivial,fun _ => ih _ (ok.2 _) _⟩
    · exact ⟨ok.1,fun _ => ih _ (ok.2 _) _⟩

theorem source_bounds (F : CForger Port Words) (pk : List SLHDSA.Byte) (q s : ℕ) (c : Caps)
    (hp : CountBound (fun i => publicRead (X := Port) (Y := Words) i = true) (F pk) q)
    (hs : CountBound (fun i => signRead (X := Port) (Y := Words) i = true) (F pk) s)
    (hc : AllQueries (readCap (X := Port) (Y := Words) c) (capOut c) (F pk)) :
    let Q := liftClassical (BList.ofList [] (by simp)) (sourceForger S N T cap g caps side F)
    CountBound isPort (Q.main pk) q ∧ CountBound isSign (Q.main pk) s ∧ AllQueries (capIdx c) (capOut c) (Q.main pk) := by
  apply lift_bounds
  · apply (countBound_iff_wCount _ _ _).2
    apply WCount.wmono _ (source_cost S N T cap g caps side 1 0 (F pk) q
      (WCount.wmono _ ((countBound_iff_wCount _ _ _).1 hp)) [])
    all_goals rintro (x|n|m) <;> simp [publicRead,signRead,playerCost]
  · apply (countBound_iff_wCount _ _ _).2
    apply WCount.wmono _ (source_cost S N T cap g caps side 0 1 (F pk) s
      (WCount.wmono _ ((countBound_iff_wCount _ _ _).1 hs)) [])
    all_goals rintro (x|n|m) <;> simp [publicRead,signRead,playerCost]
  · exact source_cap S N T cap g caps side c _ (F pk) hc []

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.source_bounds
