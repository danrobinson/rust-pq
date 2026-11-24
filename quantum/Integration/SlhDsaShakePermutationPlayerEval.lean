import Integration.SlhDsaShakePermutationPlayer

/-! Continuation semantics for the expanded control tree. Both the adaptive
classical challenger and the terminal measurement are parameters. -/
namespace Reduction.ShakePermutation.RoundPort.Player
open Classical Quantum OracleComp OracleSpec PQ.Interactive Fix Matrix ENNReal
open scoped Kronecker

def wp {J α V : Type} {s : OracleSpec J} (step : ∀ t, (s.Range t → V) → V)
    (p : OracleComp s α) (k : α → V) : V :=
  OracleComp.construct (C := fun _ => V) k (fun t _ ih => step t ih) p

@[simp] theorem wp_pure {J α V : Type} {s : OracleSpec J} (step : ∀ t, (s.Range t → V) → V)
    (a : α) (k : α → V) : wp step (pure a) k = k a := rfl
theorem wp_query {J α V : Type} {s : OracleSpec J} (step : ∀ t, (s.Range t → V) → V)
    (t : J) (g : s.Range t → OracleComp s α) (k : α → V) :
    wp step (liftM (s.query t) >>= g) k = step t (fun u => wp step (g u) k) := rfl

@[simp] theorem wp_atom {J V : Type} {s : OracleSpec J} (step : ∀ t, (s.Range t → V) → V)
    (t : J) (k : s.Range t → V) : wp step (liftM (s.query t)) k = step t k := by
  simpa only [bind_pure,wp_pure] using wp_query step t (fun u => pure u) k

theorem wp_bind {J α β V : Type} {s : OracleSpec J} (step : ∀ t, (s.Range t → V) → V)
    (p : OracleComp s α) (g : α → OracleComp s β) (k : β → V) :
    wp step (p >>= g) k = wp step p (fun u => wp step (g u) k) := by
  induction p using OracleComp.inductionOn with
  | pure => simp
  | query_bind t c ih => simp only [bind_assoc,wp_query,ih]

abbrev Density (A : Type) := Matrix A A ℂ
def turn {A : Type} (e : Equiv.Perm A) (ρ : Density A) := ρ.submatrix e.symm e.symm

variable {ι E σ : Type} [Fintype E] [DecidableEq E] {sp : OracleSpec ι}
abbrev Env (sp : OracleSpec ι) (σ : Type) := ∀ t, (sp.Range t → σ → ℝ≥0∞) → σ → ℝ≥0∞
abbrev Value (σ A : Type) := σ → Density A → ℝ≥0∞

noncomputable def bigStep (k : MaskAddr → Capacity) (h : RateMask) (env : Env sp σ) :
    ∀ t : (instrSpec (Big E) + Banks sp).Domain,
      ((instrSpec (Big E) + Banks sp).Range t → Value σ (Big E)) → Value σ (Big E)
  | .inl j, f, s, ρ => ∑ i : Fin (j.1+1), f i s (j.2.1.branch i ρ)
  | .inr (.inl ()), f, s, ρ => f () s (turn (wireGate E (onMask ((oracleEquiv k).prodCongr (Equiv.refl Work)))) ρ)
  | .inr (.inr (.inl ())), f, s, ρ => f () s (turn (wireGate E (onHead ((oracleEquiv h).prodCongr (Equiv.refl Work)))) ρ)
  | .inr (.inr (.inr t)), f, s, ρ => env t (fun u s' => f u s' ρ) s

noncomputable def oldStep (H : Port → Words) (env : Env sp σ) :
    ∀ t : (instrSpec (Old E) + (portSpec + sp)).Domain,
      ((instrSpec (Old E) + (portSpec + sp)).Range t → Value σ (Old E)) → Value σ (Old E)
  | .inl j, f, s, ρ => ∑ i : Fin (j.1+1), f i s (j.2.1.branch i ρ)
  | .inr (.inl ()), f, s, ρ => f () s (turn ((oracleEquiv H).prodCongr (Equiv.refl E)) ρ)
  | .inr (.inr t), f, s, ρ => env t (fun u s' => f u s' ρ) s

private theorem eval_gate (k : MaskAddr → Capacity) (h : RateMask) (env : Env sp σ) (e : Equiv.Perm (Reg Work))
    (out : Unit → Value σ (Big E)) :
    wp (bigStep k h env) (gate e) out = fun s ρ => out () s (turn (wireGate E e) ρ) := by
  funext s ρ
  change (∑ i : Fin 1, out () s ((SubInstrument.relabel (wireGate E e)).branch () ρ)) = _
  rw [Fin.sum_univ_one,SubInstrument.relabel_branch_apply]
  rfl

private theorem lower_wp {X Y : Type} [AddCommGroup Y] (k : MaskAddr → Capacity) (h : RateMask)
    (env : Env sp σ) (tab : X → Y) (p : Driver E sp Unit)
    (lens : Equiv.Perm (Register X Y Work) → Equiv.Perm (Reg Work))
    (comp : ∀ a b, lens (a.trans b) = (lens a).trans (lens b))
    (port : ∀ out, wp (bigStep k h env) p out =
      fun s ρ => out () s (turn (wireGate E (lens ((oracleEquiv tab).prodCongr (Equiv.refl Work)))) ρ))
    (c : Circuit X Y Work) (out : Unit → Value σ (Big E)) :
    wp (bigStep k h env) (lower p lens c) out =
      fun s ρ => out () s (turn (wireGate E (lens (c.run tab))) ρ) := by
  induction c generalizing out with
  | localOp e => exact eval_gate k h env _ out
  | port => exact port out
  | seq a b ia ib =>
    rw [lower,wp_bind,ia,ib,Circuit.run,comp]
    rfl

theorem expand_wp (k : MaskAddr → Capacity) (h : RateMask) (env : Env sp σ)
    (p : Program Work) (out : Unit → Value σ (Big E)) :
    wp (bigStep k h env) (expand p) out = fun s ρ => out () s (turn (wireGate E (p.run k h)) ρ) := by
  induction p generalizing out with
  | mask c =>
    apply lower_wp k h env k _ onMask _ _ c out
    · intro a b; rfl
    · intro f; rw [askMask,wp_atom]; rfl
  | head c =>
    apply lower_wp k h env h _ onHead _ _ c out
    · intro a b; rfl
    · intro f; rw [askHead,wp_atom]; rfl
  | localOp e => exact eval_gate k h env _ out
  | seq a b ia ib => rw [expand,wp_bind,ia,ib]; rfl

def aux : Aux := ((baseMask,0),(0,0),0)
noncomputable def prepared {A : Type} (ρ : Density A) : Density (A × Aux) :=
  ρ ⊗ₖ Matrix.single aux aux (1 : ℂ)

private theorem prepared_turn {A B : Type} [DecidableEq B] (b : B) (e : Equiv.Perm (A × B)) (f : Equiv.Perm A)
    (he : ∀ a, e (a,b) = (f a,b)) (ρ : Density A) :
    turn e (ρ ⊗ₖ Matrix.single b b (1 : ℂ)) =
      turn f ρ ⊗ₖ Matrix.single b b (1 : ℂ) := by
  have inv (a : A) : e.symm (a,b) = (f.symm a,b) := e.symm_apply_eq.mpr (by rw [he,f.apply_symm_apply])
  have other (a : A) (v : B) (hv : v ≠ b) : (e.symm (a,v)).2 ≠ b := by
    intro h
    obtain ⟨a',v',eq⟩ : ∃ a' v', e.symm (a,v) = (a',v') := ⟨_,_,rfl⟩
    rw [eq] at h
    change v' = b at h
    subst v'
    have ht := e.symm_apply_eq.mp eq
    rw [he] at ht
    exact hv (congrArg Prod.snd ht)
  ext ⟨a,v⟩ ⟨a',v'⟩
  by_cases hv : v = b <;> by_cases hw : v' = b
  · subst v; subst v'; simp [turn,kroneckerMap_apply,inv]
  · subst v; simp [turn,kroneckerMap_apply,inv,Matrix.single_apply,Ne.symm (other _ _ hw),Ne.symm hw]
  · subst v'; simp [turn,kroneckerMap_apply,inv,Matrix.single_apply,Ne.symm (other _ _ hv),Ne.symm hv]
  · simp [turn,kroneckerMap_apply,Matrix.single_apply,Ne.symm (other _ _ hv),Ne.symm (other _ _ hw),Ne.symm hv,Ne.symm hw]

private theorem framed (j : InstrIdx (Old E)) (i : Fin (j.1+1)) (ρ : Density (Old E)) :
    (frameIdx j).2.1.branch i (prepared ρ) = prepared (j.2.1.branch i ρ) := by
  change (j.2.1.branch i).amplify Aux (ρ ⊗ₖ _) = _
  rw [MatrixMap.amplify_kronecker]
  rfl

theorem expanded_wp (π : Permutation) (ki ko : Mask) (h : RateMask) (env : Env sp σ)
    {α : Type} (P : QOC (Old E) (portSpec + sp) α) (out : α → Value σ (Big E)) (s : σ) (ρ : Density (Old E)) :
    wp (bigStep (bank ki ko) h env) (expanded π P) out s (prepared ρ) =
      wp (oldStep (oracle (salted ki ko h π)) env) P (fun a s' ρ' => out a s' (prepared ρ')) s ρ := by
  induction P using OracleComp.inductionOn generalizing s ρ with
  | pure a => simp [expanded]
  | query_bind t c ih =>
    simp only [expanded,simulateQ_bind,simulateQ_spec_query,wp_bind,wp_atom]
    rcases t with j | (⟨⟩|i)
    · simp only [impl,wp_atom,oldStep]
      change (∑ n : Fin (j.1+1), wp (bigStep (bank ki ko) h env) (expanded π (c n)) out s
        ((frameIdx j).2.1.branch n (prepared ρ))) = _
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [framed]
      exact ih n _ _
    · simp only [impl,oldStep]
      rw [expand_wp (bank ki ko) h env (publicPort π)]
      have he (x : Old E) : wireGate E ((publicPort π).run (bank ki ko) h) (x,aux) =
          (actual π ki ko h E x,aux) := by
        rcases x with ⟨⟨a,y⟩,env'⟩
        change (wires E).symm (((publicPort π).run (bank ki ko) h) (clean a y 0),env') = _
        rw [publicPort_clean]; rfl
      dsimp only
      rw [prepared,prepared_turn aux _ _ he]
      exact ih () _ _
    · simp only [impl,wp_atom,bigStep,oldStep]
      change env i (fun u s' => wp _ (expanded π (c u)) out s' (prepared ρ)) s = _
      exact congrFun (congrArg (env i) (funext fun u => funext fun s' => ih u s' ρ)) s

end Reduction.ShakePermutation.RoundPort.Player
#print axioms Reduction.ShakePermutation.RoundPort.Player.expanded_wp
