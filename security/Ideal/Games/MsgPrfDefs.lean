import Ideal.Games.PrfDefs

/-!
# The HMAC-shaped PRF in the ideal-compression model: definitions

The keyed function is HMAC over a Merkle–Damgård hash with compression function `g`, for a key
shorter than a block:

`mac_g(k, d) = out (g (g (IV, ok k), ob (mdFold g (g (IV, ik k)) (b₁ :: rest))))`,
`(b₁, rest) = ib d`,

where `ik k`, `ok k` are the inner and outer key blocks, `ib d` the (non-empty) list of blocks of
the padded inner message after the key block, and `ob s` the single padded block holding the
inner digest `s`.  The input type is a product `P × M` (for `PRF_msg`: `opt_rand` and the
message), so that the adversary type `PrfAdvI` and the ideal experiment `prfIdealGameI` of
`Ideal/Games/PrfDefs.lean` are reused.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal

variable {St Blk K P M Y : Type}

/-- The HMAC-shaped keyed function. -/
def macF (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (g : CF St Blk) (k : K) (d : P × M) : Y :=
  out (g (g (IV, ok k), ob (keyedChain IV ik g k (ib d))))

/-- The PRF scheme `⟨$ᵗ K, mac_g⟩` at the compression table `g`. -/
def macSchemeI [SampleableType K] (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (g : CF St Blk) : PRFScheme K (P × M) Y where
  keygen := $ᵗ K
  eval := macF IV ik ok ib ob out g

/-- Every function-oracle query has at most `L` inner blocks after the first one. -/
def ibLenLe (ib : P × M → Blk × List Blk) (L : ℕ) : ℕ ⊕ ((St × Blk) ⊕ (P × M)) → Prop
  | .inr (.inr d) => (ib d).2.length ≤ L
  | _ => True

section Games

variable [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
  [DecidableEq P] [DecidableEq M]

/-- The real PRF experiment in the ideal-compression model. -/
def macRealGameI (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk)
    (out : St → Y) (A : PrfAdvI St Blk P M Y) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  prfRealExperiment (macSchemeI IV ik ok ib ob out g) (A.inst g)

/-- The PRF advantage in the ideal-compression model (the ideal experiment is
`prfIdealGameI`: a lazy random function on `P × M`). -/
noncomputable def macAdvantageI (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y) : ℝ≥0∞ :=
  (𝒟[macRealGameI IV ik ok ib ob out A]).boolDist (𝒟[prfIdealGameI A])

end Games

end Ideal
