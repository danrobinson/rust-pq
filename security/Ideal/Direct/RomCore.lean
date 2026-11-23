import Ideal.Direct.RomFinal

/-!
# The remaining core as one program under two handlers (`status/DIRECT.md` §12)

`DeferCoreSuf` compares the deferred game of the walk program `walkProg (untag PprfST)` with the
ROM-side game `Yrom = k ← $; (simulateQ (romH k) PprfST).run' ∅`.  Here the deferred side is
put in the same shape: `k ← $; (simulateQ (defH k) PprfST).run s₀` with ONE handler
`defH k = deferredImpl ∘ labI ∘ chainW k ∘ untagT` on the tagged program (`defRun_eq_defH`).
So the core is a statement about one program `PprfST` under the two handlers `defH k` and
`romH k` (`DeferCoreSufH`), the shape of an until-bad / coupling argument; it is equivalent to
`DeferCoreSuf` (`deferCoreSuf_iff_H`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-- The deferred state. -/
abbrev DS : Type := MD.RS St Blk × List (Empty ⊕ MD.Nd Blk)

/-- **The deferred-side handler of the tagged program at the secret seed `k`.** -/
noncomputable def defH (k : Bytes 16) : QueryImpl (QT Dsk) (StateT DS ProbComp) :=
  Gs.deferredImpl ∘ₛ (MD.labI IV128 ∘ₛ (chainW k ∘ₛ untagT))

theorem run_simulateQ_statelessP {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (ψ : QueryImpl spec (StateT σ ProbComp)) (φ : QueryImpl spec ProbComp)
    (h : ∀ t s, (ψ t).run s = (fun a => (a, s)) <$> φ t) (X : OracleComp spec α) (s : σ) :
    (simulateQ ψ X).run s = (fun a => (a, s)) <$> simulateQ φ X := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, bind_map_left, map_bind,
      ih]

theorem liftM_eq_simulateQ_OS {α : Type} (ob : ProbComp α) :
    (liftM ob : OracleComp OS α) =
      simulateQ (fun n => (liftM (OS.query (.inl (.inl n))) : OracleComp OS _)) ob := by
  induction ob using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    rw [liftM_bind, simulateQ_bind, simulateQ_spec_query]
    simp only [← ih]
    rfl

theorem simulateQ_unif_id {α : Type} (ob : ProbComp α) :
    simulateQ (fun n => (liftM (unifSpec.query n) : ProbComp _)) ob = ob := by
  induction ob using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    simp only [ih]

/-- A lifted sample of the walk program, in the deferred game, is the sample. -/
theorem deferred_liftM {α : Type} (ob : ProbComp α) (s : DS) :
    (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128) (liftM ob : OracleComp OS α))).run s =
      (fun a => (a, s)) <$> ob := by
  rw [liftM_eq_simulateQ_OS, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  refine (run_simulateQ_statelessP _ (fun n => (liftM (unifSpec.query n) : ProbComp _))
    (fun n s' => ?_) ob s).trans ?_
  · simp only [QueryImpl.apply_compose, simulateQ_spec_query, MD.labI]
    rw [LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif, Functor.map_map]
  · rw [simulateQ_unif_id]

/-- **The deferred game of the walk program of a tagged program is that program under `defH`.** -/
theorem defRun_eq_defH (P : OracleComp (QT Dsk) Bool) (s : DS) :
    (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128) (walkProg (simulateQ untagT P)))).run s =
      ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) >>= fun k => (simulateQ (defH k) P).run s := by
  unfold walkProg
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, deferred_liftM, bind_map_left]
  refine bind_congr fun k => ?_
  unfold defH
  rw [QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]

theorem defRun_prEvent_H (P : OracleComp (QT Dsk) Bool) (E : Bool → MD.RS St Blk → Prop) :
    Pr{let w ← defRun (walkProg (simulateQ untagT P))}[E w.1 w.2] =
      Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
         let z ← (simulateQ (defH k) P).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[E z.1 st] := by
  rw [← defRun_prEvent, defRun_eq_defH]
  simp only [prEvent_norm]

/-- **The probabilistic core (SUF), one program under two handlers; not proved.** -/
def DeferCoreSufH : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (defH k) (PprfST oR ($ᵗ (Bytes 16)) S)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist
          ((liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
            (simulateQ (romH k) (PprfST oR ($ᵗ (Bytes 16)) S)).run' ∅) {true} +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **The probabilistic core (EUF), one program under two handlers; not proved.** -/
def DeferCoreEufH : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (defH k) (PprfET oR ($ᵗ (Bytes 16)) S)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist
          ((liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
            (simulateQ (romH k) (PprfET oR ($ᵗ (Bytes 16)) S)).run' ∅) {true} +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

theorem deferCoreSuf_iff_H : DeferCoreSuf ↔ DeferCoreSufH := by
  unfold DeferCoreSuf DeferCoreSufH
  simp only [defRun_prEvent_H (E := fun b st => b = true ∧ ¬ Gs.Bad st)]
  rfl

theorem deferCoreEuf_iff_H : DeferCoreEuf ↔ DeferCoreEufH := by
  unfold DeferCoreEuf DeferCoreEufH
  simp only [defRun_prEvent_H (E := fun b st => b = true ∧ ¬ Gs.Bad st)]
  rfl

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.defRun_eq_defH
#print axioms Ideal.Direct.Rom.deferCoreSuf_iff_H
#print axioms Ideal.Direct.Rom.deferCoreEuf_iff_H
