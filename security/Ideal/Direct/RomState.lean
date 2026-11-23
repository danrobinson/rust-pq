import Ideal.Direct.RomCore

/-!
# The ROM-side game as one stateful handler (`status/DIRECT.md` §13)

The ROM-side game of the core (`DeferCoreSufH`, right-hand side) is the tagged program `PprfST`
under `romH k` (the simulator over the ROM base interface `RS`), read through VCVio's ROM runtime
(lazy random oracles for `hashSpec Cr`).  Here the two layers are fused into ONE handler
`romS k : QueryImpl (QT Dsk) (StateT (T × O) ProbComp)` (`T` the simulator's table, `O` the oracle
cache), so that both sides of the core are `StateT _ ProbComp` handlers of the same program:

* `fuseS G φ`: a stateful handler over a stateful base, fused (generic), `run_fuseS`;
* **`yrom_eq`**: the ROM-side success probability is the success probability of the run of
  `romS k` from `(∅, ∅)`, `k` drawn first (exact).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct

section Fuse

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ τ : Type}

/-- **A stateful handler over a stateful base, fused into one stateful handler.** -/
def fuseS (G : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (φ : QueryImpl spec₂ (StateT τ ProbComp)) : QueryImpl spec₁ (StateT (σ × τ) ProbComp) :=
  fun t => StateT.mk fun p =>
    (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ φ ((G t).run p.1)).run p.2

theorem fuseS_run (G : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (φ : QueryImpl spec₂ (StateT τ ProbComp)) (t : spec₁.Domain) (p : σ × τ) :
    (fuseS G φ t).run p =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ φ ((G t).run p.1)).run p.2 := rfl

theorem run_fuseS (G : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (φ : QueryImpl spec₂ (StateT τ ProbComp)) {α : Type} (oa : OracleComp spec₁ α) (s : σ)
    (c : τ) :
    (simulateQ φ ((simulateQ G oa).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (fuseS G φ) oa).run (s, c) := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, fuseS_run, bind_map_left,
      map_bind, ih]

end Fuse

namespace Rom

open Ideal.Realize Ideal.Realize.Prf

/-- The ROM-side state: the simulator's table and the oracle cache. -/
abbrev RomSt : Type := (hS St Blk).QueryCache × (hashSpec Cr).QueryCache

/-- **The ROM-side game as one stateful handler** (the simulator over the lazy oracles). -/
noncomputable def romSt (k : Bytes 16) : QueryImpl (QT Dsk) (StateT RomSt ProbComp) :=
  fuseS (romH k) (hashSpec Cr).romImpl

/-- **The ROM-side success probability is that of the fused handler** (exact). -/
theorem yrom_eq (P : OracleComp (QT Dsk) Bool) :
    (ProbCompRuntime.rom (hashSpec Cr)).evalDist
        ((liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
          (simulateQ (romH k) P).run' ∅) {true} =
      Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
         let z ← (simulateQ (romSt k) P).run (∅, ∅)}[z.1 = true] := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  rw [simulateQ_bind]
  erw [roSim.run'_liftM_bind]
  have h : ∀ k : Bytes 16,
      (simulateQ (hashSpec Cr).romImpl ((simulateQ (romH k) P).run' ∅)).run' ∅ =
        (fun z => z.1) <$> (simulateQ (romSt k) P).run (∅, ∅) := by
    intro k
    rw [StateT.run'_eq]
    have e : (simulateQ (romH k) P).run' ∅ = Prod.fst <$> (simulateQ (romH k) P).run ∅ := rfl
    rw [e, simulateQ_map, StateT.run_map, run_fuseS]
    simp only [Functor.map_map]
    rfl
  simp only [h, prEvent_norm]

end Rom

end Ideal.Direct

#print axioms Ideal.Direct.run_fuseS
#print axioms Ideal.Direct.Rom.yrom_eq
