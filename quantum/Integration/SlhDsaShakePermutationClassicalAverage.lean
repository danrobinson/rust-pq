import Integration.SlhDsaShakePermutationClassicalPublicRisk
import Integration.SlhDsaShakePermutationClassicalReport

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section

theorem report_eval (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (ev : Z → Report T → ℝ≥0∞) (P : OracleComp (Native S N) Z) (r : Report T) :
    detRun (reportStep S N T H raw) ev P r = ev (report S N T H raw P r).1 (report S N T H raw P r).2 := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => rfl
  | query_bind i k ih => exact ih (reportStep _ _ _ H raw i r).1 (reportStep _ _ _ H raw i r).2

private theorem dirty_absorbs (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Outer S N) Z) (r : Report T) (h : r.clean=false) :
    mixedRun (reportStep S N T H raw) (fun _ s => hit (s.clean = false)) P r = 1 := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => change hit (r.clean=false) = _; simp [hit,h]
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · exact (congrArg uniformMean (funext fun u => ih u r h)).trans (avg_const (U := Fin (n+1)) _)
    · exact ih _ (recordPub T H r d x).2 (by simp only [recordPub]; split <;> simp [h])
    · exact ih _ (reportStep S N T H raw (.inr x) r).2 h

theorem report_publicBad (S : Sha2Set) (N T : ℕ) {Z : Type} (rates : Row T → Rate) (caps : Row T → Capacity)
    (raw : ShakeApi.RawTable S N) (P : OracleComp (Outer S N) Z) (r : Report T) (h : r.clean=true) :
    let H := fun j => join (rates j) (caps j)
    mixedRun (reportStep S N T H raw) (fun _ s => hit (s.clean=false)) P r = publicBad S N T rates caps raw P r.edges := by
  let H := fun j => join (rates j) (caps j)
  induction P using OracleComp.inductionOn generalizing r with
  | pure => change hit (r.clean=false) = 0; simp [hit,h]
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · exact congrArg uniformMean (funext fun u => ih u r h)
    · let z := recordPub T H r d x
      change mixedRun _ _ (k z.1) z.2 = if known : old r.edges d x then publicBad _ _ _ _ _ _ (k known.choose) r.edges else
        if isolated r.edges x (H (publicRow T r.edges d x)) then publicBad S N T rates caps raw
          (k (H (publicRow T r.edges d x))) (edge d x (H (publicRow T r.edges d x))::r.edges) else 1
      split
      · rename_i oldx
        simpa only [z,recordPub,dite_eq_left oldx] using ih z.1 z.2 (by simp [z,recordPub,oldx,h])
      · rename_i fresh
        let j := publicRow T r.edges d x
        by_cases safe : isolated r.edges x (H j)
        · have hz : z.2.clean = true := by simp [z,recordPub,fresh,j,h,safe]
          have out := ih z.1 z.2 hz
          simpa only [z,recordPub,dite_eq_right fresh,H,j,ite_eq_left safe] using out
        · have hz : z.2.clean = false := by simp [z,recordPub,fresh,j,h,safe]
          have out := dirty_absorbs S N T H raw (k z.1) z.2 hz
          simpa only [z,recordPub,dite_eq_right fresh,H,j,ite_eq_right safe] using out
    · exact ih _ (reportStep S N T H raw (.inr x) r).2 h

theorem mean_coverage {G C : Type} [Fintype G] [Fintype C] [Nonempty G] [Nonempty C]
    (keep pub hid : G → C → ℝ≥0∞) (actual visible : G → ℝ≥0∞) (bound : ℝ≥0∞)
    (point : ∀ g c, 1 ≤ keep g c + pub g c + hid g c)
    (ak : ∀ g, uniformMean (keep g) = actual g) (ap : ∀ g, uniformMean (pub g) = visible g)
    (ah : ∀ c, uniformMean (fun g => hid g c) ≤ bound) :
    1 ≤ uniformMean actual + uniformMean visible + bound := by
  calc
    1 = uniformMean (fun _ : G => uniformMean (fun _ : C => 1)) := by simp only [avg_const]
    _ ≤ uniformMean (fun g => uniformMean (fun c => keep g c + pub g c + hid g c)) :=
      mean_mono fun g => mean_mono (point g)
    _ = (uniformMean actual + uniformMean visible) + uniformMean (fun g => uniformMean (hid g)) := by
      simp_rw [mean_add,ak,ap]
    _ ≤ _ := by
      rw [mean_comm]
      exact add_le_add le_rfl ((mean_mono ah).trans_eq (avg_const _))

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.report_publicBad
