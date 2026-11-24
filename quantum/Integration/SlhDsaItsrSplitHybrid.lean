import PQ.QROM.ItsrPullback

/-! Adaptive ITSR with honest evaluations compiled into the simulator for
the reprogramming hop and charged in the independent-digest search hop. -/
namespace PQ.QROM.Pull
open Quantum ENNReal
open scoped ComplexOrder
universe u v w
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

variable {K Xm D X Y Req : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [Nonempty D] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u,v}} {Out : QReg → Type w} {A : QReg} {s : ℕ}

abbrev LabelTable (K Xm D : Type) (s : ℕ) := ((K × Xm) × Option (Fin s)) → D

/-- A run in one of the two salt-row hybrids. When finalTable is false, the
table at a query uses precisely the salts already issued at that transcript. -/
noncomputable def phaseWin (φ : (K × Xm → D) → X → Y) (tg : Req → Xm) (oc : ∀ u, Out u → K × Xm)
    (Cov : Finset D → D → Prop) (I : L.Interp) (ρ : SubState A)
    (x : IAdv L (qromSpec X Y) Req K Out s A) (Rs : Fin s → K) (Ψ : LabelTable K Xm D s)
    (finalTable : Bool) :=
  leafProb (nRuntime fun t : List Req => φ (nFn Rs Ψ (if finalTable then s else t.length)))
    I (pComp x Rs) (joint ρ) (fun p => itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc p))

/-- The frozen simulator may depend on the external table of independent labels.
Its program cannot depend on the independent salt tape. Simulation need only
hold on the good tapes, in both the all-final and currently-issued runtimes. -/
theorem split_adaptive_le (ι : K × Xm → X) (φ : (K × Xm → D) → X → Y)
    (tg : Req → Xm) (oc : ∀ u, Out u → K × Xm) (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (I : L.Interp) (ρ : SubState A) (x : IAdv L (qromSpec X Y) Req K Out s A)
    (freeze : LabelTable K Xm D s → IAdv L (qromSpec X Y) Req K Out s A)
    (q Q : ℕ) (allCost : IAdv.IsQueryBound s x (fun _ => Q)) (publicCost : ∀ Ψ, IAdv.IsQueryBound s (freeze Ψ) (fun _ => q))
    (hι : Function.Injective ι) (locality : ∀ H G z, φ H z ≠ φ G z → ∃ w, ι w = z ∧ H w ≠ G w)
    (mono : ∀ (U V : Finset D) d, U ⊆ V → Cov U d → Cov V d)
    (Good : (Fin s → K) → Prop) [DecidablePred Good] (ε : ℝ≥0∞)
    (bad : (avg fun Rs => if Good Rs then (0:ℝ≥0∞) else 1) ≤ ε)
    (sim : ∀ Rs, Good Rs → ∀ Ψ b,
      phaseWin φ tg oc Cov I ρ x Rs Ψ b = phaseWin φ tg oc Cov I ρ (freeze Ψ) Rs Ψ b) :
    itsrPExp φ tg oc I ρ s x Cov ≤
      (((2*(Q:ℝ≥0∞)+1)^2*coverProb (Fin s) Cov)^(2⁻¹:ℝ) +
        2*q*((s:ℝ≥0∞)*(Fintype.card K : ℝ≥0∞)⁻¹)^(2⁻¹:ℝ))^2 + ε := by
  classical
  let value := phaseWin (s := s) φ tg oc Cov I ρ
  let masked := fun (Rs : Fin s → K) (Ψ : LabelTable K Xm D s) (b : Bool) =>
    if Good Rs then value (freeze Ψ) Rs Ψ b else 0
  let δ := 4*(q:ℝ≥0∞)*((Fintype.card K:ℝ≥0∞)⁻¹*(s*q:ℕ))
  have hop (Ψ : LabelTable K Xm D s) :
      (avg fun Rs => masked Rs Ψ true)^(2⁻¹:ℝ) ≤ (avg fun Rs => masked Rs Ψ false)^(2⁻¹:ℝ) + δ^(2⁻¹:ℝ) := by
    let fam := fun (Rs : Fin s → K) (_ : Unit) (m : ℕ) => φ (nFn Rs Ψ m)
    have upd (Rs : Fin s → K) (_ : Unit) (j : Fin s) (r : K) (m : ℕ) (before : m ≤ j.val) :
        fam (Function.update Rs j r) () m = fam Rs () m := by
      apply congrArg φ
      funext z
      simp only [nFn,lastIdx_update Rs j _ r before]
    have diff (Rs : Fin s → K) (_ : Unit) (m : ℕ) (z : X) (hne : fam Rs () s z ≠ fam Rs () m z) :
        ∃ j : Fin s, m ≤ j.val ∧ rowOf ι z = some (Rs j) := by
      obtain ⟨w,rfl,unequal⟩ := locality _ _ _ hne
      obtain ⟨j,hj,eq⟩ := lastIdx_ne (Rs := Rs) (m := m) (r := w.1) (fun hl => unequal (by simp only [nFn,hl]))
      exact ⟨j,hj,by rw [rowOf_apply hι,eq]⟩
    have budget (Rs : Fin s → K) := isWeightedBound_of_isTotalBound (fun t : List Req => Nat.sub_le s t.length)
      (pComp_isTotalBound (publicCost Ψ) Rs)
    let ev := fun (Rs : Fin s → K) (_ : Unit) p => Good Rs ∧ itsrAWin Cov Rs (nFn Rs Ψ s) (lv tg oc p)
    have h := mpg_sqrt_le (I := I) (ρ := ρ) (fam := fam) (rowOf := rowOf ι) upd diff (publicCost Ψ) budget ev
    have eq (Rs : Fin s → K) (b : Bool) :
        leafProb (nRuntime fun t : List Req => fam Rs () (if b then s else t.length)) I
          (pComp (freeze Ψ) Rs) (joint ρ) (ev Rs ()) = masked Rs Ψ b := by
      by_cases g : Good Rs
      · simp only [masked,ev,g,true_and,ite_true]
        rfl
      · simp [masked,ev,g,leafProb,ind]
    have one (f : Unit → ℝ≥0∞) : avg f = f () := (avg_congr (fun u => by cases u; rfl) : avg f = avg (fun _ : Unit => f ())).trans (avg_const _)
    simp_rw [one] at h
    have final (Rs : Fin s → K) : leafProb (nRuntime fun _ : List Req => fam Rs () s) I
        (pComp (freeze Ψ) Rs) (joint ρ) (ev Rs ()) = masked Rs Ψ true := eq Rs true
    have current (Rs : Fin s → K) : leafProb (nRuntime fun t : List Req => fam Rs () t.length) I
        (pComp (freeze Ψ) Rs) (joint ρ) (ev Rs ()) = masked Rs Ψ false := eq Rs false
    simp only [final,current] at h
    exact h
  have combined := sqrt_avg_le (fun Ψ => avg fun Rs => masked Rs Ψ true)
    (fun Ψ => avg fun Rs => masked Rs Ψ false) (fun _ => δ) hop
  rw [avg_const,avg_comm (fun Ψ Rs => masked Rs Ψ true),avg_comm (fun Ψ Rs => masked Rs Ψ false)] at combined
  have sub (Rs Ψ) : masked Rs Ψ false ≤ value x Rs Ψ false := by
    by_cases g : Good Rs
    · simp only [masked,g,ite_true]; exact (sim Rs g Ψ false).symm.le
    · simp [masked,g]
  have search := (avg_mono fun Rs => avg_mono (sub Rs)).trans (itsrP_hyb_le (tg := tg) (oc := oc) (I := I) (ρ := ρ) hι locality mono allCost)
  have normal : δ^(2⁻¹:ℝ) = 2*q*((s:ℝ≥0∞)*(Fintype.card K : ℝ≥0∞)⁻¹)^(2⁻¹:ℝ) := by
    have e : δ = 4*(q:ℝ≥0∞)*((s:ℝ≥0∞)*(Fintype.card K:ℝ≥0∞)⁻¹*q) := by unfold δ; push_cast; ring
    rw [e,sqrt_four_mul]
  rw [normal] at combined
  have main := pow_le_pow_left' (combined.trans (add_le_add (sqrt_le_sqrt search) le_rfl)) 2
  rw [sq_sqrt] at main
  have point (Rs Ψ) : value x Rs Ψ true ≤ masked Rs Ψ true + (if Good Rs then 0 else 1) := by
    by_cases g : Good Rs
    · simp only [masked,g,ite_true,add_zero]; exact (sim Rs g Ψ true).le
    · simp only [masked,g,ite_false,zero_add]
      exact (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  have endgame := avg_mono fun Rs => avg_mono (point Rs)
  simp only [avg_add,avg_const] at endgame
  calc
    _ = avg (fun Rs => avg fun Ψ => value x Rs Ψ true) :=
      itsrPExp_eq_N (φ := φ) (I := I) (ρ := ρ) (x := x) (fun Rs H p => itsrAWin Cov Rs H (lv tg oc p))
    _ ≤ _ := endgame.trans (add_le_add main bad)

end PQ.QROM.Pull
#print axioms PQ.QROM.Pull.split_adaptive_le
