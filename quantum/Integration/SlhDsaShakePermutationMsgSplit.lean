import Integration.SlhDsaShakePermutationSkFirstHybrid

/-! A single classical challenge in an arbitrary quantum computation. The
prefix ends immediately before the challenge, with the pending message and
resumption as classical data. The same quantum workspace flows through the
bind, including all off-diagonal entries of every surviving branch. -/
namespace Reduction.ShakePermutation.MsgSplit
open Classical OracleComp OracleSpec PQ.Interactive Quantum
variable {W D R A : Type} [Fintype W] [Inhabited R]
abbrev Source (W D R A : Type) [Fintype W] := QOC W (PRFScheme.PRFOracleSpec D R) A
abbrev Stage (W D R A : Type) [Fintype W] := A ⊕ (D × (R → Closed W A))
def isChallenge : InstrIdx W ⊕ (ℕ ⊕ D) → Bool
  | .inr (.inr _) => true
  | _ => false

noncomputable def before (p : Source W D R A) : Closed W (Stage W D R A) :=
  OracleComp.construct (C:=fun _ => Closed W (Stage W D R A)) (fun a => pure (.inl a))
    (fun t next later => match t, next, later with
      | .inl j, _, later => liftM ((instrSpec W + unifSpec).query (.inl j)) >>= later
      | .inr (.inl n), _, later => liftM ((instrSpec W + unifSpec).query (.inr n)) >>= later
      | .inr (.inr d), next, _ => pure (.inr (d,fun r => ansRun (fun _ => default) (next r)))) p

noncomputable def resume (f : D → R) : Stage W D R A → Closed W A
  | .inl a => pure a
  | .inr (d,k) => k (f d)

omit [Inhabited R] in
theorem no_query (f g : D → R) (p : Source W D R A) (bound : CountBound (fun i => isChallenge i = true) p 0) :
    ansRun f p = ansRun g p := by
  induction p using OracleComp.inductionOn with
  | pure a => rw [ansRun_pure,ansRun_pure]
  | query_bind t k ih =>
    rw [countBound_query_bind] at bound
    rcases t with j | (n|d)
    · rw [ansRun_instr,ansRun_instr]
      exact bind_congr fun r => ih r (bound r)
    · rw [ansRun_unif,ansRun_unif]
      exact bind_congr fun r => ih r (bound r)
    · simp [isChallenge] at bound

theorem answered (f : D → R) (p : Source W D R A) (bound : CountBound (fun i => isChallenge i = true) p 1) :
    ansRun f p = before p >>= resume f := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [before,resume,ansRun_pure]
  | query_bind t k ih =>
    rw [countBound_query_bind] at bound
    rcases t with j | (n|d)
    · rw [ansRun_instr]
      change _ = (liftM ((instrSpec W + unifSpec).query (.inl j)) >>= fun r => before (k r)) >>= _
      rw [bind_assoc]
      exact bind_congr fun r => ih r (bound r)
    · rw [ansRun_unif]
      change _ = (liftM ((instrSpec W + unifSpec).query (.inr n)) >>= fun r => before (k r)) >>= _
      rw [bind_assoc]
      exact bind_congr fun r => ih r (bound r)
    · have rest : ∀ r, CountBound (fun i => isChallenge i = true) (k r) 0 := bound.2
      rw [ansRun_oracle]
      change _ = pure (.inr (d,fun r => ansRun (fun _ => default) (k r)) : Stage W D R A) >>= _
      rw [pure_bind]
      exact no_query _ _ _ (rest (f d))

end Reduction.ShakePermutation.MsgSplit
#print axioms Reduction.ShakePermutation.MsgSplit.answered
