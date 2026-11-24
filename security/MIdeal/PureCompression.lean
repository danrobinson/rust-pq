import MIdeal.MixedTables
import Ideal.Realize.PureForger
import MReduction.Instances

/-! Classical pure-byte forgery with public access to both SHA-2 compression tables. -/
namespace MIdeal.PureCompression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction ENNReal

abbrev Sign := (List Byte × List Byte) →ₒ Option (List Byte)
abbrev Ports := unifSpec + (hS Chain512 Block512 + (hS St Blk + Sign))

structure Forger where
  main : List Byte → OracleComp Ports ((List Byte × List Byte) × Option (List Byte))

/-- Condition on the public SHA-512 table, preserving the SHA-256 and signing oracles. -/
def Forger.at512 (A : Forger) (g : CF Chain512 Block512) : ForgerP where
  main pk := simulateQ (instImpl g) (A.main pk)

variable (S : Sha2Set)
local notation "P" => fun g => tablePrimitives g S.vp.params

local instance (g : CompressionTables) : SampleableType (P g).Y :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : SampleableType (P g).SkSeed :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).Y :=
  inferInstanceAs (DecidableEq (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed :=
  inferInstanceAs (DecidableEq (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Inhabited (P g).Y :=
  inferInstanceAs (Inhabited (Bytes S.vp.params.n))
local instance (g : CompressionTables) : Fintype (P g).Y :=
  inferInstanceAs (Fintype (Bytes S.vp.params.n))

def codec (g : CompressionTables) : CoreWireCodec S.vp.params (P g).core where
  pkSeed := WireCodec.bytes _
  skSeed := WireCodec.bytes _
  skPrf := WireCodec.bytes _
  y := WireCodec.bytes _
  y_toBytes := fun _ => rfl

set_option maxHeartbeats 1600000 in
theorem structural (g : CompressionTables) : Structural S.vp (P g) :=
  by
  refine ⟨⟨fun _ _ h => h⟩, ?_, (MReduction.structural S).bounds⟩
  intro a ha b hb h
  have bound := fipsApprovedAddressBounds S.fips
  obtain ⟨hac,hal,hat⟩ := sha2Domain_of_addressFacts bound ha
  obtain ⟨hbc,hbl,hbt⟩ := sha2Domain_of_addressFacts bound hb
  exact Concrete.sha2AdrsKey_injective_of_domain hac hal hat hbc hbl hbt h

variable (rand : Bytes S.vp.params.n → Bytes S.vp.params.n → ProbComp (Bytes S.vp.params.n))
    (seeds : ProbComp (Bytes S.vp.params.n)) (A : Forger)

def strong (g : CompressionTables) : PureBytesStrongForger S.vp (P g) (codec S g)
    (fun k => rand k.pkSeed k.pkRoot) seeds where
  main pk := simulateQ (instImpl g.1) ((A.at512 g.2).main pk)

noncomputable def average (f : CompressionTables → ℝ≥0∞) : ℝ≥0∞ :=
  cfAvg fun g₅₁₂ => cfAvg fun g₂₅₆ => f (g₂₅₆,g₅₁₂)

theorem average_add (f h : CompressionTables → ℝ≥0∞) :
    average (fun g => f g + h g) = average f + average h := by
  unfold average
  simp only [cfAvg_add]

theorem average_mono {f h : CompressionTables → ℝ≥0∞} (le : ∀ g, f g ≤ h g) :
    average f ≤ average h := cfAvg_mono fun g => cfAvg_mono fun h => le (h,g)

local notation "F" => strong S rand seeds A
set_option quotPrecheck false in
local notation "Q" => fun g => toInternal (pureBytesToTyped (F g).toUnforgeableAdversary)

theorem suf_linear :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g)) +
        average (fun g => linIdealSuf (Q g)) ≤ average (fun g => linRealSuf (Q g)) := by
  rw [← average_add]
  exact average_mono fun g => slhdsa_pure_bytes_suf_cma_linear (structural S g) (F g)

theorem euf_linear :
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (F g).toUnforgeableAdversary) +
        average (fun g => linIdealEuf (Q g)) ≤ average (fun g => linRealEuf (Q g)) := by
  rw [← average_add]
  exact average_mono fun g => slhdsa_pure_bytes_euf_cma_linear (structural S g) (F g).toUnforgeableAdversary

end MIdeal.PureCompression
#print axioms MIdeal.PureCompression.suf_linear
#print axioms MIdeal.PureCompression.euf_linear
