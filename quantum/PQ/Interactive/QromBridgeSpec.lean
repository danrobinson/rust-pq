import PQ.Interactive.QromBridge

/-!
# Oracle-port programs with further classical oracles: compilation and syntactic bounds

* `compileQ H P : QOC (WS X Y E) spec α`: the Part-1 machine of a program
  `P : QOC ((X × Y) × E) (portSpec + spec) α` for the function `H`: every call of the oracle
  port is replaced by the instrument `U_H` (`portIdx H`), instruments are framed, queries to
  `spec` (uniform sampling, signing oracle, …) are kept.  For `spec` empty this is `compile`
  up to the target type.
* `CountBound counted P q`: every path of an oracle computation makes at most `q` queries with
  index in `counted`, whatever the answers.
* `AllQueries good goodOut P`: every query index on every path satisfies `good`, and every output
  satisfies `goodOut`.

No semantic theorem is proved here for `compileQ` with a non-empty `spec` (for requests answered
by a deterministic challenger see `QromBridgeReq.lean`).
-/

open OracleComp OracleSpec ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α : Type} {ι : Type} {spec : OracleSpec ι}

/-- The handler compiling an oracle-port program with further oracles `spec`. -/
noncomputable def compileImplQ (H : X → Y) :
    QueryImpl (instrSpec ((X × Y) × E) + (portSpec + spec)) (QOC (WS X Y E) spec)
  | .inl j => liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (framedIdx j)))
  | .inr (.inl ()) => (fun _ ↦ ()) <$>
      (liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (portIdx H))) : QOC (WS X Y E) spec _)
  | .inr (.inr t) => liftM ((instrSpec (WS X Y E) + spec).query (Sum.inr t))

/-- **The Part-1 machine of an oracle-port program with further oracles, for the function `H`.** -/
noncomputable def compileQ (H : X → Y) (P : QOC ((X × Y) × E) (portSpec + spec) α) :
    QOC (WS X Y E) spec α :=
  simulateQ (compileImplQ H) P

/-- Every path makes at most `q` queries with index in `counted`. -/
def CountBound {κ : Type} {sp : OracleSpec κ} (counted : κ → Prop) [DecidablePred counted]
    (P : OracleComp sp α) : ℕ → Prop :=
  OracleComp.construct (C := fun _ ↦ ℕ → Prop)
    (fun _ _ ↦ True)
    (fun t _ ih q ↦ if counted t then 0 < q ∧ ∀ r, ih r (q - 1) else ∀ r, ih r q) P

/-- Every query index on every path satisfies `good`; every output satisfies `goodOut`. -/
def AllQueries {κ : Type} {sp : OracleSpec κ} (good : κ → Prop) (goodOut : α → Prop)
    (P : OracleComp sp α) : Prop :=
  OracleComp.construct (C := fun _ ↦ Prop)
    (fun a ↦ goodOut a)
    (fun t _ ih ↦ good t ∧ ∀ r, ih r) P

/-- Index predicate: the oracle port of a port program. -/
def isPort : InstrIdx ((X × Y) × E) ⊕ (Unit ⊕ ι) → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred (isPort (X := X) (Y := Y) (E := E) (ι := ι)) := fun t ↦ by
  rcases t with _ | _ | _ <;> unfold isPort <;> infer_instance

end PQ.Interactive
