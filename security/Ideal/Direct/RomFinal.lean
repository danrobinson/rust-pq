import Ideal.Direct.RomMatch

/-!
# The route's bounds under the probabilistic core alone (`status/DIRECT.md` §12)

With `BadSuf`/`BadEuf` (sharp form, `Direct/MDBadSharp.lean`) and H3 (`romGameSuf`,
`romGameEuf`, `Direct/RomMatch.lean`) proved, the only remaining hypotheses of the route are
**`DeferCoreSuf`** and **`DeferCoreEuf`** (`Direct/RomGame.lean`): the deferred game of the walk
program of the tagged realiser program, winning with `Bad` failing, against the ROM-side game
`Yrom` / `YromE`, with error `epsHalf + qs/2^128`.

* `mdHopSuf_of_core : DeferCoreSuf → MDHopSuf`, `mdHopEuf_of_core : DeferCoreEuf → MDHopEuf`;
* the composed bounds on `sufI`, `eufI`, `sufP`, `eufP` and the point bounds at
  `(2^60, 2^20)`, `(2^64, 2^40)`, `(2^64, 2^64)`, each under the one remaining hypothesis.

**Every bound here takes `DeferCoreSuf` (or `DeferCoreEuf`) as a hypothesis; it is NOT proved.**
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

open Ideal.Realize

theorem deferSimSufNB_of_core (hc : DeferCoreSuf) : DeferSimSufNB :=
  deferSimSufNB_of_parts romGameSuf hc

theorem deferSimEufNB_of_core (hc : DeferCoreEuf) : DeferSimEufNB :=
  deferSimEufNB_of_parts romGameEuf hc

/-- **The hop (SUF) from the probabilistic core.** -/
theorem mdHopSuf_of_core (hc : DeferCoreSuf) : MDHopSuf :=
  mdHopSuf_of_nb (deferSimSufNB_of_core hc)

/-- **The hop (EUF) from the probabilistic core.** -/
theorem mdHopEuf_of_core (hc : DeferCoreEuf) : MDHopEuf :=
  mdHopEuf_of_nb (deferSimEufNB_of_core hc)

section Composed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem suf_rom_core (hc : DeferCoreSuf) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  suf_rom_of_hop (mdHopSuf_of_core hc) S oR hqf hqs hlong hout

theorem euf_rom_core (hc : DeferCoreEuf) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  euf_rom_of_hop (mdHopEuf_of_core hc) S oR hqf hqs hlong hout

theorem suf_rom_2_20_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  suf_rom_2_20 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem suf_rom_2_40_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  suf_rom_2_40 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem suf_rom_2_64_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  suf_rom_2_64 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem euf_rom_2_20_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  euf_rom_2_20 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

theorem euf_rom_2_40_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  euf_rom_2_40 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

theorem euf_rom_2_64_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  euf_rom_2_64 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

end Composed

section ComposedPure

variable (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
include hqf hqs hlong hout

theorem sufP_rom_core (hc : DeferCoreSuf) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  sufP_rom_of_hop (mdHopSuf_of_core hc) S oR hqf hqs hlong hout

theorem eufP_rom_core (hc : DeferCoreEuf) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  eufP_rom_of_hop (mdHopEuf_of_core hc) S oR hqf hqs hlong hout

theorem sufP_rom_2_20_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  sufP_rom_2_20 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem sufP_rom_2_40_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  sufP_rom_2_40 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem sufP_rom_2_64_core (hc : DeferCoreSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  sufP_rom_2_64 S oR hqf hqs hlong hout (mdHopSuf_of_core hc) hf hs hℓ

theorem eufP_rom_2_20_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  eufP_rom_2_20 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

theorem eufP_rom_2_40_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  eufP_rom_2_40 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

theorem eufP_rom_2_64_core (hc : DeferCoreEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  eufP_rom_2_64 S oR hqf hqs hlong hout (mdHopEuf_of_core hc) hf hs hℓ

end ComposedPure

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.mdHopSuf_of_core
#print axioms Ideal.Direct.Rom.mdHopEuf_of_core
#print axioms Ideal.Direct.Rom.suf_rom_core
#print axioms Ideal.Direct.Rom.euf_rom_core
#print axioms Ideal.Direct.Rom.sufP_rom_core
#print axioms Ideal.Direct.Rom.eufP_rom_core
#print axioms Ideal.Direct.Rom.sufP_rom_2_20_core
#print axioms Ideal.Direct.Rom.sufP_rom_2_40_core
#print axioms Ideal.Direct.Rom.sufP_rom_2_64_core
#print axioms Ideal.Direct.Rom.eufP_rom_2_64_core
