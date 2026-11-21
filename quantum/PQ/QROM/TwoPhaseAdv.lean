import PQ.QROM.TwoPhase

/-!
# Interactive first-phase adversaries

A first-phase adversary of a two-phase game is a quantum query algorithm that, besides its
quantum access to the hash, sends up to `n` *classical* requests to the challenger of the game
and continues according to the classical responses.

* `IAdv L spec Req Resp Out n A`: such an adversary, by recursion on `n`.  With `n = 0` it is a
  program with leaves in `Out`.  With `n + 1` it is a program (the segment before the next
  request) each of whose leaves on a register `u` is either a final output in `Out u` or a
  request `req : Req` together with, for every response `resp : Resp`, an adversary with `n`
  requests continuing on `u`.  The quantum state on `u` is kept across the request; the request
  and the response are classical.
* `IAdv.flat ch K n s x`: the adversary `x` run against the deterministic challenger
  `ch : Req → St → Resp × St` from the challenger state `s`, followed by the continuation
  `K u o s'` on the final output `o` and the final challenger state `s'`; one `QuantumComp`.
  The challenger state is threaded by `flat`, not by the adversary: it is the game's record.
* `IAdv.IsQueryBound`: every path makes at most `b i` calls of port `i`, whatever the responses.
* `flat_branch_eq_zero`, `flat_branch_congr`: a leaf whose recorded challenger state `t` does not
  extend the current state is not reached, and two challengers that agree on every request
  except those after which `t` is no longer reachable give the same post-state at `t`.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v u₁ v₁ w w₂

namespace PQ.QROM

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {Req Resp : Type}
  {Out : QReg → Type w} {W₂ : QReg → Type w₂} {St : Type}

/-- Interactive adversaries with at most `n` classical requests. -/
def IAdv (L : LocalSig.{u, v}) (spec : QuantumOracleSpec.{u₁, v₁}) (Req Resp : Type)
    (Out : QReg → Type w) : ℕ → QReg → Type (max 1 u v u₁ v₁ w)
  | 0, A => QuantumComp L spec Out A
  | n + 1, A =>
    QuantumComp L spec (fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) A

namespace IAdv

/-- Run the interactive adversary against the challenger `ch` from the state `s`, then continue
with `K` on the final output and the final challenger state. -/
def flat (ch : Req → St → Resp × St) (K : ∀ u, Out u → St → QuantumComp L spec W₂ u) :
    (n : ℕ) → {A : QReg} → St → IAdv L spec Req Resp Out n A → QuantumComp L spec W₂ A
  | 0, _, s, x => QuantumComp.bind (X := Out) x fun u o ↦ K u o s
  | n + 1, _, s, x =>
    QuantumComp.bind (X := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x
      fun u r ↦ match r with
        | .inl o => K u o s
        | .inr rc => flat ch K n (ch rc.1 s).2 (rc.2 (ch rc.1 s).1)

/-- The continuation that stops with the final output and the challenger state. -/
def stop (u : QReg) (o : Out u) (s : St) : QuantumComp L spec (fun u ↦ Out u × St) u :=
  QuantumComp.pure (o, s)

/-- Running against the challenger and continuing with `K` is running against the challenger,
stopping, and then running `K`. -/
theorem flat_eq_bind (ch : Req → St → Resp × St) (K : ∀ u, Out u → St → QuantumComp L spec W₂ u)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) :
    flat ch K n s x = (flat ch (stop (L := L) (spec := spec)) n s x).bind
      fun u os ↦ K u os.1 os.2 := by
  induction n generalizing A s with
  | zero =>
    have key : ∀ x : QuantumComp L spec Out A,
        QuantumComp.bind x (fun u o ↦ K u o s) =
          (QuantumComp.bind x fun u o ↦ stop (L := L) (spec := spec) u o s).bind
            fun u os ↦ K u os.1 os.2 := fun x ↦ by
      rw [QuantumComp.bind_assoc]
      rfl
    exact key x
  | succ n ih =>
    have key : ∀ x : QuantumComp L spec
        (fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) A,
        QuantumComp.bind x (fun u r ↦ match r with
          | .inl o => K u o s
          | .inr rc => flat ch K n (ch rc.1 s).2 (rc.2 (ch rc.1 s).1)) =
        (QuantumComp.bind x fun u r ↦ match r with
          | .inl o => stop (L := L) (spec := spec) u o s
          | .inr rc => flat ch (stop (L := L) (spec := spec)) n (ch rc.1 s).2
              (rc.2 (ch rc.1 s).1)).bind fun u os ↦ K u os.1 os.2 := fun x ↦ by
      rw [QuantumComp.bind_assoc]
      congr 1
      funext u r
      cases r with
      | inl o => rfl
      | inr rc => exact ih _ _
    exact key x

/-- Every path of the adversary makes at most `b i` calls of port `i`, whatever the responses:
against every deterministic challenger the flattened program is within the budget `b`. -/
def IsQueryBound (n : ℕ) {A : QReg} (x : IAdv L spec Req Resp Out n A) (b : spec.Port → ℕ) :
    Prop :=
  ∀ (St : Type) (ch : Req → St → Resp × St) (s : St),
    (flat ch (stop (L := L) (spec := spec)) n s x).IsQueryBound b

theorem flat_isQueryBound (ch : Req → St → Resp × St)
    {K : ∀ u, Out u → St → QuantumComp L spec W₂ u} {n : ℕ} {A : QReg} (s : St)
    {x : IAdv L spec Req Resp Out n A} {b₁ b₂ : spec.Port → ℕ} (hx : IsQueryBound n x b₁)
    (hK : ∀ u o s, (K u o s).IsQueryBound b₂) : (flat ch K n s x).IsQueryBound (b₁ + b₂) := by
  rw [flat_eq_bind]
  exact (hx St ch s).bind fun u os ↦ hK u os.1 os.2

end IAdv

/-! ## Branches of sequenced runs -/

section Branch

variable (R : QuantumRuntime spec) (I : L.Interp) {W : QReg → Type w} {A : QReg}

theorem run_bind_branch_eq_zero (x : QuantumComp L spec W A)
    (k : ∀ u, W u → QuantumComp L spec W₂ u) (c : Σ u, W₂ u)
    (h : ∀ p : Σ u, W u, (R.run I (k p.1 p.2)).branch c = 0) :
    (R.run I (x.bind k)).branch c = 0 := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply]
  simp [h]

theorem run_bind_branch_congr (x : QuantumComp L spec W A)
    (k k' : ∀ u, W u → QuantumComp L spec W₂ u) (c : Σ u, W₂ u)
    (h : ∀ p : Σ u, W u, (R.run I (k p.1 p.2)).branch c = (R.run I (k' p.1 p.2)).branch c) :
    (R.run I (x.bind k)).branch c = (R.run I (x.bind k')).branch c := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.run_bind, QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply,
    DSubInstrument.branch_bind_apply]
  simp [h]

end Branch

/-! ## Reachability and locality -/

section Locality

variable (R : QuantumRuntime spec) (I : L.Interp)

/-- A leaf whose recorded challenger state `t` does not extend the current state `s` is not
reached.  `ext s t` reads "`t` extends `s`"; every step of the challenger extends the state. -/
theorem flat_branch_eq_zero (ch : Req → St → Resp × St) (ext : St → St → Prop)
    (hrefl : ∀ s, ext s s) (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) (u : QReg) (o : Out u)
    (t : St) (h : ¬ ext s t) :
    (R.run I (IAdv.flat ch (IAdv.stop (L := L) (spec := spec)) n s x)).branch ⟨u, (o, t)⟩ = 0 := by
  induction n generalizing A s with
  | zero =>
    refine run_bind_branch_eq_zero R I (W := Out) x _ _ fun p ↦ ?_
    unfold IAdv.stop
    rw [QuantumRuntime.run_pure]
    refine DSubInstrument.branch_ret_of_ne _ fun heq ↦ h ?_
    cases heq
    exact hrefl _
  | succ n ih =>
    refine run_bind_branch_eq_zero R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' =>
      unfold IAdv.stop
      rw [QuantumRuntime.run_pure]
      refine DSubInstrument.branch_ret_of_ne _ fun heq ↦ h ?_
      cases heq
      exact hrefl _
    | inr rc => exact ih _ _ fun h' ↦ h (hstep _ _ _ h')

/-- **Locality.** Two challengers that answer every request in the same way, except requests
after which the recorded state `t` can no longer be reached under either, leave the same
post-state at every leaf with recorded state `t`. -/
theorem flat_branch_congr (ch ch' : Req → St → Resp × St) (ext : St → St → Prop)
    (hrefl : ∀ s, ext s s) (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (hstep' : ∀ req s t, ext (ch' req s).2 t → ext s t) (t : St)
    (hloc : ∀ req s, ch req s = ch' req s ∨ (¬ ext (ch req s).2 t ∧ ¬ ext (ch' req s).2 t))
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L spec Req Resp Out n A) (u : QReg) (o : Out u) :
    (R.run I (IAdv.flat ch (IAdv.stop (L := L) (spec := spec)) n s x)).branch ⟨u, (o, t)⟩ =
      (R.run I (IAdv.flat ch' (IAdv.stop (L := L) (spec := spec)) n s x)).branch
        ⟨u, (o, t)⟩ := by
  induction n generalizing A s with
  | zero => rfl
  | succ n ih =>
    refine run_bind_branch_congr R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L spec Req Resp Out n u))) x _ _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' => rfl
    | inr rc =>
      rcases hloc rc.1 s with heq | ⟨h1, h2⟩
      · simp only [heq]
        exact ih _ _
      · simp only
        rw [flat_branch_eq_zero R I ch ext hrefl hstep n _ _ u o t h1,
          flat_branch_eq_zero R I ch' ext hrefl hstep' n _ _ u o t h2]

end Locality

end PQ.QROM
