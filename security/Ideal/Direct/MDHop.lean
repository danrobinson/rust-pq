import Ideal.Direct.MDSha
import Ideal.Direct.RomNumerics

/-!
# The simulation hop, reduced to two statements about the deferred game (`status/DIRECT.md` §11)

Proved here (unconditional):

* **`suf_le_deferred`**, **`euf_le_deferred`**: `sufI S (optRandU oR) pkSeedDist` is at most the
  probability that the deferred game of the walk program `XS` (H1, `Direct/MDSha.lean`) returns
  `true`, plus twice the probability of `Bad` (`Conflict ∨ PtColl` of the Merkle–Damgård graph)
  at its filled final state (`MD.md_core`, `Direct/MDCore.lean`).  Same for `eufI`, `XE`.

Remaining (named statements, NOT proved; they replace `MDHopSuf`, `MDHopEuf` as hypotheses):

* **`DeferSimSuf`** (G4 + H3): the deferred game of `XS` returns `true` with probability at most
  VCVio's SUF advantage of the simulator `simAdv S oR` plus `(QAll+1)²/2^255 + qs/2^128`.
* **`BadSuf`** (H4, collision part): twice the probability of `Bad` at the filled final state of
  the deferred game of `XS` is at most `(QAll+1)²/2^255`.
* `DeferSimEuf`, `BadEuf`: the EUF twins.

**`mdHopSuf_of`**: `DeferSimSuf → BadSuf → MDHopSuf` (and `mdHopEuf_of`), with the SAME error
`epsHop qf qs ℓ = (QAll+1)²/2^254 + qs/2^128`: the two `(QAll+1)²/2^255` halves add up.  So every
composed theorem of `Direct/RomCompose.lean` and `Direct/RomNumerics.lean` holds under these two
smaller hypotheses (`suf_rom_of_parts`, …).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

set_option linter.unusedSectionVars false

/-- The Merkle–Damgård graph at SHA-256. -/
abbrev Gs : LGraph (MD.Cell St Blk) Empty (MD.Nd Blk) St := MD.mdG (Blk := Blk) IV128

/-- The deferred game of a walk program, with its end fill. -/
noncomputable def defRun (X : OracleComp OS Bool) : ProbComp (Bool × MD.RS St Blk) := do
  let z ← (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128) X)).run ((∅, ∅), [])
  let st ← RelabelState.endFill z.2
  pure (z.1, st)

theorem defRun_prEvent (X : OracleComp OS Bool) (E : Bool → MD.RS St Blk → Prop) :
    Pr{let z ← (simulateQ Gs.deferredImpl (simulateQ (MD.labI IV128) X)).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[E z.1 st] = Pr{let w ← defRun X}[E w.1 w.2] := by
  unfold defRun
  simp only [prEvent_norm]

/-- **Real ≤ deferred + 2·Bad**, for any walk program. -/
theorem real_le_defRun (X : OracleComp OS Bool) :
    HP.prT ((simulateQ (hS St Blk).romImpl (simulateQ (MD.cellsR IV128) X)).run' ∅) ≤
      Pr{let w ← defRun X}[w.1 = true] + 2 * Pr{let w ← defRun X}[Gs.Bad w.2] := by
  have h := MD.md_core IV128 X (· = true)
  rw [defRun_prEvent X (fun b _ ↦ b = true), defRun_prEvent X (fun _ st ↦ Gs.Bad st)] at h
  exact h

/-- **SUF: the ideal-model experiment is at most the deferred game of `XS` plus `2·Bad`.** -/
theorem suf_le_deferred (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    sufI S (optRandU oR) pkSeedDist ≤
      Pr{let w ← defRun (XS S oR pkSeedDist)}[w.1 = true] +
        2 * Pr{let w ← defRun (XS S oR pkSeedDist)}[Gs.Bad w.2] := by
  refine (sufI_le_lazy S oR pkSeedDist).trans ?_
  rw [h1_suf]
  exact real_le_defRun _

/-- **EUF: the ideal-model experiment is at most the deferred game of `XE` plus `2·Bad`.** -/
theorem euf_le_deferred (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) :
    eufI S (optRandU oR) pkSeedDist ≤
      Pr{let w ← defRun (XE S oR pkSeedDist)}[w.1 = true] +
        2 * Pr{let w ← defRun (XE S oR pkSeedDist)}[Gs.Bad w.2] := by
  refine (eufI_le_lazy S oR pkSeedDist).trans ?_
  rw [h1_euf]
  exact real_le_defRun _

/-! ## The remaining statements -/

/-- The 256-bit budget of each half of the hop: `(QAll + 1)² / 2^255`. -/
noncomputable def epsHalf (qf qs ℓ : ℕ) : ℝ≥0∞ := (((QAll qf qs ℓ + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 255

theorem epsHalf_add (qf qs ℓ : ℕ) :
    epsHalf qf qs ℓ + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128 = epsHop qf qs ℓ := by
  unfold epsHalf epsHop
  congr 1
  rw [← ENNReal.add_div]
  have h : (2 : ℝ≥0∞) ^ 255 = 2 * 2 ^ 254 := by rw [← pow_succ']
  rw [h, ← two_mul, ENNReal.mul_div_mul_left _ _ two_ne_zero ofNat_ne_top]

/-- **G4 + H3 (SUF), not proved**: the deferred game of `XS` against VCVio's experiment of the
simulator. -/
def DeferSimSuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[w.1 = true] ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdv S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **H4, collision part (SUF), not proved**: the bad event of the relabelling. -/
def BadSuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    2 * Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ

/-- **G4 + H3 (EUF), not proved.** -/
def DeferSimEuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[w.1 = true] ≤
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdvE S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **H4, collision part (EUF), not proved.** -/
def BadEuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    2 * Pr{let w ← defRun (XE S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ

/-! ## The hop from the two statements -/

theorem mdHopSuf_of (hD : DeferSimSuf) (hB : BadSuf) : MDHopSuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (suf_le_deferred S oR _).trans ?_
  rw [← epsHalf_add]
  calc _ ≤ (strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdv S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128) +
          epsHalf qf qs ℓ :=
        add_le_add (hD S oR qf qs ℓ hqf hqs hlong hout) (hB S oR qf qs ℓ hqf hqs hlong hout)
    _ = _ := by ring

theorem mdHopEuf_of (hD : DeferSimEuf) (hB : BadEuf) : MDHopEuf := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  refine (euf_le_deferred S oR _).trans ?_
  rw [← epsHalf_add]
  calc _ ≤ (unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdvE S oR ($ᵗ (Bytes 16))) + epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128) +
          epsHalf qf qs ℓ :=
        add_le_add (hD S oR qf qs ℓ hqf hqs hlong hout) (hB S oR qf qs ℓ hqf hqs hlong hout)
    _ = _ := by ring

/-! ## The composed bounds under the two statements -/

theorem suf_rom_of_parts (hD : DeferSimSuf) (hB : BadSuf) (S : ForgerI)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  suf_rom_of_hop (mdHopSuf_of hD hB) S oR hqf hqs hlong hout

theorem euf_rom_of_parts (hD : DeferSimEuf) (hB : BadEuf) (S : ForgerI)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  euf_rom_of_hop (mdHopEuf_of hD hB) S oR hqf hqs hlong hout

theorem sufP_rom_of_parts (hD : DeferSimSuf) (hB : BadSuf) (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  sufP_rom_of_hop (mdHopSuf_of hD hB) S oR hqf hqs hlong hout

theorem eufP_rom_of_parts (hD : DeferSimEuf) (hB : BadEuf) (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  eufP_rom_of_hop (mdHopEuf_of hD hB) S oR hqf hqs hlong hout

/-- The pure-interface SUF bound at `(2^64, 2^64)` under the two statements. -/
theorem sufP_rom_2_64_of_parts (hD : DeferSimSuf) (hB : BadSuf) (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ (2 ^ 63)⁻¹ + (2 ^ 64)⁻¹ + (2 ^ 66)⁻¹ :=
  sufP_rom_2_64 S oR hqf hqs hlong hout (mdHopSuf_of hD hB) hf hs hℓ

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.real_le_defRun
#print axioms Ideal.Direct.Rom.suf_le_deferred
#print axioms Ideal.Direct.Rom.euf_le_deferred
#print axioms Ideal.Direct.Rom.epsHalf_add
#print axioms Ideal.Direct.Rom.mdHopSuf_of
#print axioms Ideal.Direct.Rom.mdHopEuf_of
#print axioms Ideal.Direct.Rom.suf_rom_of_parts
#print axioms Ideal.Direct.Rom.sufP_rom_2_64_of_parts
