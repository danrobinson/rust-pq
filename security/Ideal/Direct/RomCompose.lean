import Ideal.Direct.RomSim
import Ideal.Realize.FinalCore
import Ideal.Realize.PureForger

/-!
# The ROM route, composed (`status/DIRECT.md` §10): conditional on the simulation hop

* `QAll qf qs ℓ = QcAll qf qs ℓ + 2·qOPrf qs`: every compression cell of the real run (the
  forger's, the signer's and the verifier's; the budget of `Direct/Counts.lean`).
* `epsHop qf qs ℓ = (QAll + 1)² / 2^254 + qs / 2^128`: the error of the Merkle–Damgård
  simulation hop of §10.1 (256-bit events; `E_root`).
* **`MDHopSuf`**, **`MDHopEuf`**: the hop, as a named statement.  For every compression-model
  forger `S` with the hypotheses of tight8 (`qf` compression and `qs` signing queries, signed and
  forged messages of at most `ℓ` bytes),
  `sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ Adv^{SUF}_{ROM}(simAdv S oR) + epsHop qf qs ℓ`
  (and the EUF twin).  **Not proved here**: this is the remaining statement of the route.
* `suf_rom_of_hop`, `euf_rom_of_hop`: under the hop, `sufI` (resp. `eufI`) is at most
  `securityBound vp.params (256^16) 2 1 qf qs + epsHop qf qs ℓ`, for the SAME game objects as
  `suf_ideal_closed_tight8`; `sufP_rom_of_hop`, `eufP_rom_of_hop`: the same for the external pure
  interface of `suf_ideal_pure_closed_tight8`, at message length `ℓ + 257`.

Numerics and the comparison with tight8: `Direct/RomNumerics.lean`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

namespace Ideal.Direct.Rom

open Ideal.Realize

/-- Every compression cell of the real run (an over-count): the eleven-realiser cap `QcAll` and
twice the `PRF`-oracle count. -/
def QAll (qf qs ℓ : ℕ) : ℕ := QcAll qf qs ℓ + 2 * Prf.qOPrf qs

/-- **The error of the simulation hop** (§10.1): 256-bit events among all cells, and `E_root`
(a signer's inner `H_msg` digest beginning with `PK.root`). -/
noncomputable def epsHop (qf qs ℓ : ℕ) : ℝ≥0∞ :=
  (((QAll qf qs ℓ + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 254 + (qs : ℝ≥0∞) / 2 ^ 128

/-- **The simulation hop, SUF form (the remaining statement of the route; not proved).** -/
def MDHopSuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdv S oR ($ᵗ (Bytes 16))) + epsHop qf qs ℓ

/-- **The simulation hop, EUF form (not proved).** -/
def MDHopEuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr))
          (simAdvE S oR ($ᵗ (Bytes 16))) + epsHop qf qs ℓ

/-- The bound of the route. -/
noncomputable def epsRom (qf qs ℓ : ℕ) : ℝ≥0∞ :=
  securityBound Link.vp.params (256 ^ 16) 2 1 qf qs + epsHop qf qs ℓ

/-- **SUF-CMA in the ideal-compression model, under the hop.** -/
theorem suf_rom_of_hop (hop : MDHopSuf) (S : ForgerI)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  (hop S oR qf qs ℓ hqf hqs hlong hout).trans
    (add_le_add (simAdv_suf_le S oR _ hqf hqs) le_rfl)

/-- **EUF-CMA in the ideal-compression model, under the hop.** -/
theorem euf_rom_of_hop (hop : MDHopEuf) (S : ForgerI)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ :=
  (hop S oR qf qs ℓ hqf hqs hlong hout).trans
    (add_le_add (simAdv_euf_le S oR _ hqf hqs) le_rfl)

/-- **SUF-CMA of the external pure interface, under the hop** (`sufP_le_sufI`, messages of at
most `ℓ + 257` bytes). -/
theorem sufP_rom_of_hop (hop : MDHopSuf) (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_rom_of_hop hop S.toI oR (fun pk => toI_port S pk (hqf pk))
      (fun pk => toI_sign S pk (hqs pk)) (fun pk => toI_long S pk (hlong pk))
      (fun pk => toI_out S pk (hout pk)))

/-- **EUF-CMA of the external pure interface, under the hop.** -/
theorem eufP_rom_of_hop (hop : MDHopEuf) (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257) :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_rom_of_hop hop S.toI oR (fun pk => toI_port S pk (hqf pk))
      (fun pk => toI_sign S pk (hqs pk)) (fun pk => toI_long S pk (hlong pk))
      (fun pk => toI_out S pk (hout pk)))

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.suf_rom_of_hop
#print axioms Ideal.Direct.Rom.euf_rom_of_hop
#print axioms Ideal.Direct.Rom.sufP_rom_of_hop
#print axioms Ideal.Direct.Rom.eufP_rom_of_hop
