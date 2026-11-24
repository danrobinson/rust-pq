import Integration.SlhDsaShakePermutationClassicalComparison
import Integration.SlhDsaShakePermutationClassicalOverlay

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
structure Monitor (I A : Type) where
  values : Bank I A
  graph : EdgeTrace A

def start (I A : Type) : Monitor I A := ⟨fun _ => none,[]⟩

def advance {I A : Type} [DecidableEq I] [DecidableEq A] (H : I → A) (j : I) (d : Bool) (x : A)
    (m : Monitor I A) : Option (Monitor I A) :=
  match m.values j with
  | some v => if h : old m.graph d x then if v = h.choose then some m else none else none
  | none => if old m.graph d x ∨ ¬freshOut m.graph d (H j) then none else
      some ⟨Function.update m.values j (some (H j)),edge d x (H j)::m.graph⟩

def inspect {I A Z : Type} [DecidableEq I] [DecidableEq A] [Fintype A] (H : I → A)
    (ev : Z → Option (Monitor I A) → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) :
    Option (Monitor I A) → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => Option (Monitor I A) → ℝ≥0∞) ev (fun i _ k m => match i with
    | .inl _ => uniformMean fun u => k u m
    | .inr (j,d,x) => k (H j) (m.bind (advance H j d x))) P

theorem inspect_bind {I A Z V : Type} [DecidableEq I] [DecidableEq A] [Fintype A] (H : I → A)
    (ev : V → Option (Monitor I A) → ℝ≥0∞) (P : OracleComp (Tagged I A) Z)
    (k : Z → OracleComp (Tagged I A) V) (m) :
    inspect H ev (P >>= k) m = inspect H (fun z s => inspect H ev (k z) s) P m := by
  induction P using OracleComp.inductionOn generalizing m with
  | pure => simp only [pure_bind]; rfl
  | query_bind i f ih =>
    rw [bind_assoc]; rcases i with n|⟨j,d,x⟩
    · exact congrArg uniformMean (funext fun u => ih u m)
    · exact ih _ _

theorem inspect_failed {I A Z : Type} [DecidableEq I] [DecidableEq A] [Fintype A] (H : I → A)
    (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) :
    inspect H (fun z m => if m.isSome then ev z else 0) P none = 0 := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact (congrArg uniformMean (funext ih)).trans (avg_const (U := Fin (n+1)) _)
    · exact ih _

theorem inspect_guarded {I A Z : Type} [Fintype I] [Nonempty A] [DecidableEq I] [DecidableEq A] [Fintype A] (H : I → A)
    (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) (m : Monitor I A) (hm : coherent H m.values) :
    inspect H (fun z m => if m.isSome then ev z else 0) P (some m) = guarded H ev P m.values m.graph := by
  induction P using OracleComp.inductionOn generalizing m with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨j,d,x⟩
    · exact congrArg uniformMean (funext fun u => ih u m hm)
    · change inspect _ _ (k (H j)) (advance H j d x m) = _
      cases h : m.values j with
      | some v =>
        by_cases known : old m.graph d x
        · by_cases same : v = known.choose
          · simp only [advance,guarded,OracleComp.construct_query_bind,h,dite_eq_left known,ite_eq_left same]
            rw [hm j v h]
            exact ih v m hm
          · simp only [advance,guarded,OracleComp.construct_query_bind,h,dite_eq_left known,ite_eq_right same]
            apply inspect_failed
        · simp only [advance,guarded,OracleComp.construct_query_bind,h,dite_eq_right known]
          apply inspect_failed
      | none =>
        by_cases bad : old m.graph d x ∨ ¬freshOut m.graph d (H j)
        · simp only [advance,guarded,OracleComp.construct_query_bind,h,ite_eq_left bad]
          apply inspect_failed
        · simp only [advance,guarded,OracleComp.construct_query_bind,h,ite_eq_right bad]
          exact ih _ _ (coherent_write hm j)

def checks (T : ℕ) (H : Row T → Words) (p : List Rate) : List Rate → Option (Monitor (Row T) Words) →
    Option (Monitor (Row T) Words)
  | [],m => m
  | b::bs,m => checks T H (p++[b]) bs (m.bind (advance H (rowId T (p++[b])) false
      (join (rateXor b (rateOf (bankState T H p))) (capOf (bankState T H p)))))

theorem inspect_absorb (T : ℕ) (H : Row T → Words) (ev : Words → Option (Monitor (Row T) Words) → ℝ≥0∞)
    (p xs : List Rate) (m) : inspect H ev (absorb T p (bankState T H p) xs) m =
      ev (bankState T H (p++xs)) (checks T H p xs m) := by
  induction xs generalizing p m with
  | nil => simp only [absorb,List.append_nil]; rfl
  | cons r rs ih =>
    rw [absorb,inspect_bind]
    change inspect H ev (absorb T (p++[r]) (H (rowId T (p++[r]))) rs) _ = _
    have e : bankState T H (p++[r]) = H (rowId T (p++[r])) := by simp [bankState]
    rw [← e,ih]; simp [checks]

def fullStep (S : Sha2Set) (N T : ℕ) (H : Row T → Words) (raw : ShakeApi.RawTable S N) :
    (i : (Native S N).Domain) → Report T × Option (Monitor (Row T) Words) →
      (Native S N).Range i × (Report T × Option (Monitor (Row T) Words))
  | .inl (d,x),(r,m) =>
    let z := recordPub T H r d x
    (z.1,z.2,if old r.edges d x then m else m.bind (advance H (publicRow T r.edges d x) d x))
  | .inr x,(r,m) => (raw x,(reportStep S N T H raw (.inr x) r).2,checks T H [] (blocksOf x) m)

theorem raw_state (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) (H : Row T → Words)
    (x : ShakeApi.Input N) :
    ShakeXof.head (output_sizes S).2 (Completion.bytes (rateOf (bankState T H (blocksOf x)))) = rawOf S cap H x := by
  have len := blocksOf_length N T cap x
  have pos : 0 < (blocksOf x).length := by simp [blocksOf,messageBlocks_length]
  have h : (blocksOf x) ≠ [] := by intro e; simp [e] at pos
  rw [hidden_state H h]
  simp only [rowId,dite_eq_left len,rawOf]; rfl

theorem inspect_driver (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T) {Z : Type}
    (H : Row T → Words) (ev : Z → Option (Monitor (Row T) Words) → ℝ≥0∞) (P : OracleComp (Outer S N) Z)
    (r : Report T) (m) :
    inspect H ev (driver S N T P r.edges) m =
      mixedRun (fullStep S N T H (rawOf S cap H)) (fun z s => ev z s.2) P (r,m) := by
  induction P using OracleComp.inductionOn generalizing r m with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · change inspect _ _ (_ >>= _) _ = _
      rw [inspect_bind]; exact congrArg uniformMean (funext fun u => ih u r m)
    · change inspect _ _ (publicStep T r.edges d x >>= _) _ = _
      rw [inspect_bind,publicStep]
      change _ = mixedRun _ _ (k (recordPub T H r d x).1) ((recordPub T H r d x).2,
        if old r.edges d x then m else m.bind (advance H (publicRow T r.edges d x) d x))
      simp only [recordPub]
      split
      · exact ih _ r m
      · rw [inspect_bind]
        let j := publicRow T r.edges d x
        let y := H j
        exact ih y ⟨edge d x y::r.edges,insert j r.seen,r.privateRows,r.clean && decide (isolated r.edges x y)⟩ (m.bind (advance H j d x))
    · change inspect _ _ (absorb T [] (bankState T H []) _ >>= _) _ = _
      rw [inspect_bind,inspect_absorb,List.nil_append]
      change inspect H ev (driver S N T (k (ShakeXof.head (output_sizes S).2 (Completion.bytes (rateOf (bankState T H (blocksOf x)))))) r.edges) _ = _
      rw [raw_state S N T cap]
      exact ih _ (reportStep S N T H (rawOf S cap H) (.inr x) r).2 _

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.inspect_driver
