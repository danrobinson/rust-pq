import PQ.Interactive.QromBridge
import PQ.QROM.TwoPhaseAdv

/-!
# QROM programs with classical requests, and Part-2 interactive adversaries

Extension of `PQ/Interactive/QromBridge.lean` by classical requests to a challenger.

* `QProgC X Y E Req Resp α`: Part-1 syntax — instruments on the workspace `(X × Y) × E`, calls of
  the oracle port, and classical requests `req : Req` with responses in `Resp`.
* `toIAdv n P : IAdv … Req Resp (fun _ ↦ Option α) n (progReg X Y E)`: the Part-2 interactive
  adversary of `P` with request budget `n` (`PQ/QROM/TwoPhaseAdv.lean`); a request beyond the
  budget ends the run with output `none`.
* `fuelRun n ch s P : QProg X Y E (Option α × St)`: the Part-1 one-port program obtained by
  answering the requests of `P` with the deterministic challenger `ch : Req → St → Resp × St`
  from the state `s` (same budget convention), returning the output and the final challenger
  state.
* `flat_toIAdv`: `IAdv.flat ch IAdv.stop n s (toIAdv n P) = toQC (fuelRun n ch s P)` — an equality
  of VCVio programs.
* `qprob_flat_toIAdv`: hence the Part-2 probability of any event on (output, final challenger
  state) of `toIAdv n P` against `ch` equals the Part-1 Born weight of
  `compile H (fuelRun n ch s P)`.

Restrictions: deterministic challengers (a probabilistic challenger is a deterministic one with
pre-sampled randomness in its state: average the equation over the randomness); one request type
with one response type; no uniform-sampling nodes; the budget convention above (for a program
making at most `n` requests on every path the output is never `none`; this is not proved here).
-/

open OracleComp OracleSpec ENNReal Quantum Matrix PQ.QROM
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α Req Resp St : Type}

/-- Classical requests: one request type, one response type. -/
@[reducible] def reqSpec (Req Resp : Type) : OracleSpec Req := fun _ ↦ Resp

/-- QROM programs with classical requests. -/
abbrev QProgC (X Y E : Type) [Fintype X] [Fintype Y] [Fintype E] (Req Resp α : Type) : Type :=
  QOC ((X × Y) × E) (portSpec + reqSpec Req Resp) α

/-- The interactive adversaries targeted by the translation. -/
abbrev IAdvOf (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype E] [DecidableEq E] (Req Resp α : Type) (n : ℕ) : Type 1 :=
  IAdv LocalSig.instruments.{0} (qromSpec X Y) Req Resp (fun _ ↦ Option α) n (progReg X Y E)

/-- The Part-2 interactive adversary of a program, with request budget `n`. -/
noncomputable def toIAdv : (n : ℕ) → QProgC X Y E Req Resp α → IAdvOf X Y E Req Resp α n
  | 0, P =>
    OracleComp.construct
      (C := fun _ ↦ QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ Option α)
        (progReg X Y E))
      (fun a ↦ QuantumComp.pure (some a))
      (fun t _ ih ↦
        match t, ih with
        | .inl j, ih => QuantumComp.primBind (instrOp j) fun b ↦ ih b
        | .inr (.inl ()), ih => QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E)
            (idSplit X Y E) fun _ ↦ ih ()
        | .inr (.inr _), _ => QuantumComp.pure none) P
  | n + 1, P =>
    OracleComp.construct
      (C := fun _ ↦ QuantumComp LocalSig.instruments.{0} (qromSpec X Y)
        (fun u ↦ Option α ⊕ (Req × (Resp →
          IAdv LocalSig.instruments.{0} (qromSpec X Y) Req Resp (fun _ ↦ Option α) n u)))
        (progReg X Y E))
      (fun a ↦ QuantumComp.pure (Sum.inl (some a)))
      (fun t k ih ↦
        match t, k, ih with
        | .inl j, _, ih => QuantumComp.primBind (instrOp j) fun b ↦ ih b
        | .inr (.inl ()), _, ih => QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E)
            (idSplit X Y E) fun _ ↦ ih ()
        | .inr (.inr req), k, _ => QuantumComp.pure (Sum.inr (req, fun r ↦ toIAdv n (k r)))) P

/-- The Part-1 one-port program: requests answered by the deterministic challenger `ch`. -/
noncomputable def fuelRun (ch : Req → St → Resp × St) :
    (n : ℕ) → St → QProgC X Y E Req Resp α → QProg X Y E (Option α × St)
  | 0, s, P =>
    OracleComp.construct (C := fun _ ↦ QProg X Y E (Option α × St))
      (fun a ↦ pure (some a, s))
      (fun t _ ih ↦
        match t, ih with
        | .inl j, ih =>
          liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inl j)) >>= fun b ↦ ih b
        | .inr (.inl ()), ih =>
          liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inr ())) >>= fun _ ↦ ih ()
        | .inr (.inr _), _ => pure (none, s)) P
  | n + 1, s, P =>
    OracleComp.construct (C := fun _ ↦ St → QProg X Y E (Option α × St))
      (fun a s ↦ pure (some a, s))
      (fun t k ih ↦
        match t, k, ih with
        | .inl j, _, ih => fun s ↦
          liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inl j)) >>= fun b ↦ ih b s
        | .inr (.inl ()), _, ih => fun s ↦
          liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inr ())) >>= fun _ ↦ ih () s
        | .inr (.inr req), k, _ => fun s ↦ fuelRun ch n (ch req s).2 (k (ch req s).1)) P s

/-- **Syntactic bridge**: running the interactive adversary of `P` against the challenger `ch`
(`IAdv.flat`, stopping with the output and the final challenger state) is the VCVio program of
the one-port program `fuelRun ch n s P`. -/
theorem flat_toIAdv (ch : Req → St → Resp × St) (n : ℕ) (s : St) (P : QProgC X Y E Req Resp α) :
    IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0}) (spec := qromSpec X Y)) n s
        (toIAdv n P) = toQC (fuelRun ch n s P) := by
  induction n generalizing s P with
  | zero =>
    induction P using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t k ih =>
      rcases t with j | ⟨⟨⟩⟩ | req
      · change QuantumComp.primBind (instrOp j) (fun b ↦
          IAdv.flat ch IAdv.stop 0 s (toIAdv 0 (k b))) = QuantumComp.primBind (instrOp j) fun b ↦
            toQC (fuelRun ch 0 s (k b))
        exact congrArg _ (funext fun b ↦ ih b)
      · change QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            (fun _ ↦ IAdv.flat ch IAdv.stop 0 s (toIAdv 0 (k ()))) =
          QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            fun _ ↦ toQC (fuelRun ch 0 s (k ()))
        exact congrArg _ (funext fun _ ↦ ih ())
      · rfl
  | succ n ihn =>
    induction P using OracleComp.inductionOn generalizing s with
    | pure a => rfl
    | query_bind t k ih =>
      rcases t with j | ⟨⟨⟩⟩ | req
      · change QuantumComp.primBind (instrOp j) (fun b ↦
          IAdv.flat ch IAdv.stop (n + 1) s (toIAdv (n + 1) (k b))) =
            QuantumComp.primBind (instrOp j) fun b ↦ toQC (fuelRun ch (n + 1) s (k b))
        exact congrArg _ (funext fun b ↦ ih b s)
      · change QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            (fun _ ↦ IAdv.flat ch IAdv.stop (n + 1) s (toIAdv (n + 1) (k ()))) =
          QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            fun _ ↦ toQC (fuelRun ch (n + 1) s (k ()))
        exact congrArg _ (funext fun _ ↦ ih () s)
      · exact ihn (ch req s).2 (k (ch req s).1)

/-- **Bridge with classical requests.**  The Part-2 probability of an event on (output, final
challenger state) for the interactive adversary `toIAdv n P` run against the deterministic
challenger `ch` and the oracle unitary of `H`, equals the Part-1 Born weight of the compiled
machine of `fuelRun ch n s P`. -/
theorem qprob_flat_toIAdv (H : X → Y) (ch : Req → St → Resp × St) (n : ℕ) (s : St)
    (Ev : Option α × St → Prop) [DecidablePred Ev] (P : QProgC X Y E Req Resp α)
    (ρ : SubState ((X × Y) × E)) :
    PQ.QROM.qprob LocalSig.Interp.instruments H
        (IAdv.flat ch (IAdv.stop (L := LocalSig.instruments.{0}) (spec := qromSpec X Y)) n s
          (toIAdv n P)) ρ (fun p ↦ Ev p.2) =
      qWeight Ev (compile H (fuelRun ch n s P)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  rw [flat_toIAdv]
  exact qprob_toQC_eq_qWeight_compile H Ev _ ρ

/-! ## Port-call bounds -/

/-- Every path of the program calls the oracle port at most `q` times, whatever the outcomes of
the instruments and the responses to the requests. -/
def PortBound (P : QProgC X Y E Req Resp α) : ℕ → Prop :=
  OracleComp.construct (C := fun _ ↦ ℕ → Prop)
    (fun _ _ ↦ True)
    (fun t _ ih ↦
      match t, ih with
      | .inl _, ih => fun q ↦ ∀ b, ih b q
      | .inr (.inl ()), ih => fun q ↦ 0 < q ∧ ih () (q - 1)
      | .inr (.inr _), ih => fun q ↦ ∀ r, ih r q) P

/-- A port bound of the program bounds the oracle calls of the flattened run, for every
challenger and every request budget. -/
theorem queryBounded_toQC_fuelRun (ch : Req → St → Resp × St) (n : ℕ) (s : St)
    (P : QProgC X Y E Req Resp α) (q : ℕ) (h : PortBound P q) :
    (toQC (fuelRun ch n s P)).IsQueryBound fun _ ↦ q := by
  induction n generalizing s P q with
  | zero =>
    induction P using OracleComp.inductionOn generalizing q with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rcases t with j | ⟨⟨⟩⟩ | req
      · change (QuantumComp.primBind (instrOp j) fun b ↦
          toQC (fuelRun ch 0 s (k b))).IsQueryBound _
        rw [QuantumComp.isQueryBound_primBind_iff]
        exact fun b ↦ ih b q (h b)
      · change (QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            fun _ ↦ toQC (fuelRun ch 0 s (k ()))).IsQueryBound _
        intro i
        rw [QuantumComp.isQueryBoundAt_queryBind_iff]
        exact ⟨fun _ ↦ ⟨h.1, fun _ ↦ ih () (q - 1) h.2 i⟩, fun hne ↦ absurd rfl hne⟩
      · exact QuantumComp.isQueryBound_pure _ _
  | succ n ihn =>
    induction P using OracleComp.inductionOn generalizing s q with
    | pure a => exact QuantumComp.isQueryBound_pure _ _
    | query_bind t k ih =>
      rcases t with j | ⟨⟨⟩⟩ | req
      · change (QuantumComp.primBind (instrOp j) fun b ↦
          toQC (fuelRun ch (n + 1) s (k b))).IsQueryBound _
        rw [QuantumComp.isQueryBound_primBind_iff]
        exact fun b ↦ ih b s q (h b)
      · change (QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
            fun _ ↦ toQC (fuelRun ch (n + 1) s (k ()))).IsQueryBound _
        intro i
        rw [QuantumComp.isQueryBoundAt_queryBind_iff]
        exact ⟨fun _ ↦ ⟨h.1, fun _ ↦ ih () s (q - 1) h.2 i⟩, fun hne ↦ absurd rfl hne⟩
      · exact ihn (ch req s).2 (k (ch req s).1) q (h (ch req s).1)

/-- A port bound of the program is a query bound of its interactive adversary. -/
theorem isQueryBound_toIAdv (n : ℕ) (P : QProgC X Y E Req Resp α) (q : ℕ) (h : PortBound P q) :
    IAdv.IsQueryBound n (toIAdv n P) fun _ ↦ q := fun St ch s ↦ by
  rw [flat_toIAdv]
  exact queryBounded_toQC_fuelRun ch n s P q h

end PQ.Interactive

open PQ.Interactive in
#print axioms flat_toIAdv
open PQ.Interactive in
#print axioms qprob_flat_toIAdv
open PQ.Interactive in
#print axioms isQueryBound_toIAdv
