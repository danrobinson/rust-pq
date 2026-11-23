import Ideal.Direct.RomCoreGhost

/-!
# Headline: the ROM-reduction bounds and what they still assume (`status/DIRECT.md` §13)

**Read this first.  Every bound on `sufI`, `eufI`, `sufP`, `eufP` in this file is CONDITIONAL**:
it takes `DeferCoreGhostSufH` (SUF) or `DeferCoreGhostEufH` (EUF) as a hypothesis
(`Direct/RomCoreGhost.lean`), the probabilistic core of the Merkle–Damgård hop against the eager
ghost game.  These two statements are NOT proved.  The proved, unconditional bounds on these games
remain tight8's (`Ideal/Realize/FinalPureTight8.lean`, `suf_ideal_pure_closed_tight8`:
`2^-63`, `2^-59`, `2^-39` at the three points).

The chain behind each theorem (all other links proved):
```
sufI ≤ deferred game + 2·Pr[Bad]             md_core (MDCore), h1_suf (MDSha)
     ≤ Pr[win ∧ ¬Bad] + 3·Pr[Bad]             MDBadSharp, 3·Pr[Bad] ≤ epsHalf
     ≤ Yrom + epsHalf + qs/2^128 + epsHalf      DeferCoreSuf  ⇐  DeferCoreGhostSufH (this file's hypothesis)
Yrom = VCVio's SUF advantage of simAdv       romGameSuf (RomMatch, H3)
     ≤ securityBound vp 2^128 2 1 qf qs       simAdv_suf_le (RomSim, VCVio's theorem)
```
The games are the same objects as tight8's: `sufP S (optRandU oR) ($ᵗ (Bytes 16))` etc.
The numerics (`epsRom_2_*`, `rom_lt_tight8_2_*`, `RomNumerics.lean`) are unconditional.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

open Ideal.Realize

section Composed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem suf_rom_ghost (hc : DeferCoreGhostSufH) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  suf_rom_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc)

theorem euf_rom_ghost (hc : DeferCoreGhostEufH) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  euf_rom_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc)

theorem suf_rom_2_20_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  suf_rom_2_20_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem suf_rom_2_40_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  suf_rom_2_40_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem suf_rom_2_64_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  suf_rom_2_64_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem euf_rom_2_20_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  euf_rom_2_20_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

theorem euf_rom_2_40_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  euf_rom_2_40_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

theorem euf_rom_2_64_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  euf_rom_2_64_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

end Composed

section ComposedPure

variable (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem sufP_rom_ghost (hc : DeferCoreGhostSufH) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  sufP_rom_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc)

theorem eufP_rom_ghost (hc : DeferCoreGhostEufH) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  eufP_rom_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc)

theorem sufP_rom_2_20_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  sufP_rom_2_20_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem sufP_rom_2_40_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  sufP_rom_2_40_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem sufP_rom_2_64_ghost (hc : DeferCoreGhostSufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  sufP_rom_2_64_core S oR hqf hqs hlong hout (deferCoreSuf_of_ghost hc) hf hs hℓ

theorem eufP_rom_2_20_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  eufP_rom_2_20_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

theorem eufP_rom_2_40_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  eufP_rom_2_40_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

theorem eufP_rom_2_64_ghost (hc : DeferCoreGhostEufH) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  eufP_rom_2_64_core S oR hqf hqs hlong hout (deferCoreEuf_of_ghost hc) hf hs hℓ

end ComposedPure

/-! ## Comparison with tight8 (unconditional numerics) -/

/-- The three point values of the route, each below the proved tight8 value (restated). -/
theorem rom_points_lt_tight8 :
    ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ <
        ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ <
        ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ <
        ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ :=
  ⟨rom_lt_tight8_2_20, rom_lt_tight8_2_40, rom_lt_tight8_2_64⟩

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.suf_rom_ghost
#print axioms Ideal.Direct.Rom.euf_rom_ghost
#print axioms Ideal.Direct.Rom.suf_rom_2_20_ghost
#print axioms Ideal.Direct.Rom.suf_rom_2_40_ghost
#print axioms Ideal.Direct.Rom.suf_rom_2_64_ghost
#print axioms Ideal.Direct.Rom.euf_rom_2_20_ghost
#print axioms Ideal.Direct.Rom.euf_rom_2_40_ghost
#print axioms Ideal.Direct.Rom.euf_rom_2_64_ghost
#print axioms Ideal.Direct.Rom.sufP_rom_ghost
#print axioms Ideal.Direct.Rom.eufP_rom_ghost
#print axioms Ideal.Direct.Rom.sufP_rom_2_20_ghost
#print axioms Ideal.Direct.Rom.sufP_rom_2_40_ghost
#print axioms Ideal.Direct.Rom.sufP_rom_2_64_ghost
#print axioms Ideal.Direct.Rom.eufP_rom_2_20_ghost
#print axioms Ideal.Direct.Rom.eufP_rom_2_40_ghost
#print axioms Ideal.Direct.Rom.eufP_rom_2_64_ghost
#print axioms Ideal.Direct.Rom.rom_points_lt_tight8
