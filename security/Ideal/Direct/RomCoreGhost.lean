import Ideal.Direct.Couple

/-!
# The remaining core against the eager ghost game (`status/DIRECT.md` §13)

`DeferCoreSufH` (`Direct/RomCore.lean`) compares the deferred game `defH k` with the ROM-side
game `romH k` read through the ROM runtime.  The ROM side is now one stateful handler (`romSt`,
`yrom_eq`, exact) and is dominated by the **eager ghost game** `romGE` (`romGE_le`: the ROM side
with the hidden parts of honest labels drawn at the honest query).  So the core reduces to the
same statement with `romGE` on the right:

* `DeferCoreGhostSufH`, `DeferCoreGhostEufH`: `defH k` (with the end fill and `¬ Bad`) against
  `romGE k`, error `epsHalf + qs/2^128` (unchanged);
* **`deferCoreSufH_of_ghost`**, `deferCoreEufH_of_ghost`, and through `deferCoreSuf_iff_H`,
  **`deferCoreSuf_of_ghost`**, `deferCoreEuf_of_ghost`.

Both sides of `DeferCoreGhostSufH` are `StateT _ ProbComp` handlers of the same program whose
hidden values are drawn at the same moments, which is what a pointwise coupling
(`Couple.coupling_le`) needs.  **`DeferCoreGhostSufH`/`EufH` are NOT proved.**
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-- The eager ghost game of a tagged program, the secret seed drawn first. -/
theorem rom_ge_le (P : OracleComp (QT Dsk) Bool) :
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist
        ((liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16)) >>= fun k =>
          (simulateQ (romH k) P).run' ∅) {true} := by
  rw [yrom_eq, prEvent_run_kernel, prEvent_run_kernel]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun k _ => ?_
  rw [prEvent_map, prEvent_map]
  exact romGE_le k P


/-- **The probabilistic core against the eager ghost game (SUF); not proved.** -/
def DeferCoreGhostSufH : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (defH k) (PprfST oR ($ᵗ (Bytes 16)) S)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
         let z ← (simulateQ (romGE k) (PprfST oR ($ᵗ (Bytes 16)) S)).run
           ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **The probabilistic core against the eager ghost game (EUF); not proved.** -/
def DeferCoreGhostEufH : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
       let z ← (simulateQ (defH k) (PprfET oR ($ᵗ (Bytes 16)) S)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[z.1 = true ∧ ¬ Gs.Bad st] ≤
      Pr{let k ← ($ᵗ (Bytes 16) : ProbComp (Bytes 16))
         let z ← (simulateQ (romGE k) (PprfET oR ($ᵗ (Bytes 16)) S)).run
           ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

theorem deferCoreSufH_of_ghost (h : DeferCoreGhostSufH) : DeferCoreSufH := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (h S oR qf qs ℓ hqf hqs hlong hout).trans ?_
  gcongr
  exact rom_ge_le _

theorem deferCoreEufH_of_ghost (h : DeferCoreGhostEufH) : DeferCoreEufH := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (h S oR qf qs ℓ hqf hqs hlong hout).trans ?_
  gcongr
  exact rom_ge_le _

/-- **`DeferCoreSuf` from the core against the eager ghost game.** -/
theorem deferCoreSuf_of_ghost (h : DeferCoreGhostSufH) : DeferCoreSuf :=
  deferCoreSuf_iff_H.2 (deferCoreSufH_of_ghost h)

/-- **`DeferCoreEuf` from the core against the eager ghost game.** -/
theorem deferCoreEuf_of_ghost (h : DeferCoreGhostEufH) : DeferCoreEuf :=
  deferCoreEuf_iff_H.2 (deferCoreEufH_of_ghost h)

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.rom_ge_le
#print axioms Ideal.Direct.Rom.deferCoreSuf_of_ghost
#print axioms Ideal.Direct.Rom.deferCoreEuf_of_ghost
