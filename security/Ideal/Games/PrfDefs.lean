import Ideal.Core.Defs
import VCVio.CryptoFoundations.PRF

/-!
# PRF security in the ideal-compression model: definitions

The keyed function is two compression calls, the first on a block of the public seed alone and
the second on a block holding the address and the secret key:

`f_g(k, (pk, a)) = out (g (g (IV, sb pk), blk a k))`.

The public seed `pk` is part of the PRF *input* (chosen by the distinguisher); the secret is the
key `k`.  In the ideal model the compression function `g` is a uniformly random table and the
distinguisher may query it.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal

variable {St Blk K PkSeed Ad Y : Type}

/-- The keyed function `f_g(k, (pk, a)) = out (g (g (IV, sb pk), blk a k))`. -/
def prfF (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y) (g : CF St Blk)
    (k : K) (d : PkSeed × Ad) : Y :=
  out (g (g (IV, sb d.1), blk d.2 k))

/-- The PRF scheme `⟨$ᵗ K, f_g⟩` at the compression table `g`. -/
def prfSchemeI [SampleableType K] (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk)
    (out : St → Y) (g : CF St Blk) : PRFScheme K (PkSeed × Ad) Y where
  keygen := $ᵗ K
  eval := prfF IV sb blk out g

/-- An ideal-model PRF distinguisher: uniform sampling, compression queries, and the candidate
function on inputs `(pk, a)`. -/
abbrev PrfAdvI (St Blk PkSeed Ad Y : Type) :=
  OracleComp (unifSpec + (hS St Blk + ((PkSeed × Ad) →ₒ Y))) Bool

/-- The distinguisher at a fixed compression table: compression queries are answered by `g`. -/
def PrfAdvI.inst (A : PrfAdvI St Blk PkSeed Ad Y) (g : CF St Blk) :
    PRFAdversary (PkSeed × Ad) Y :=
  simulateQ (instImpl g) A

/-- A compression query. -/
def isCompQ : ℕ ⊕ ((St × Blk) ⊕ (PkSeed × Ad)) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A query to the candidate function. -/
def isPrfQ : ℕ ⊕ ((St × Blk) ⊕ (PkSeed × Ad)) → Bool
  | .inr (.inr _) => true
  | _ => false

section Games

variable [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
  [DecidableEq PkSeed] [DecidableEq Ad]

/-- The real PRF experiment in the ideal-compression model. -/
def prfRealGameI (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (A : PrfAdvI St Blk PkSeed Ad Y) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  prfRealExperiment (prfSchemeI IV sb blk out g) (A.inst g)

/-- The ideal PRF experiment (lazy random function) in the ideal-compression model. -/
def prfIdealGameI (A : PrfAdvI St Blk PkSeed Ad Y) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  prfIdealExperiment (A.inst g)

/-- Output distribution of the real experiment. -/
noncomputable def prfRealIdeal (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (A : PrfAdvI St Blk PkSeed Ad Y) : MeasureTheory.Measure Bool :=
  𝒟[prfRealGameI IV sb blk out A]

/-- Output distribution of the ideal experiment. -/
noncomputable def prfIdealIdeal (A : PrfAdvI St Blk PkSeed Ad Y) : MeasureTheory.Measure Bool :=
  𝒟[prfIdealGameI A]

/-- The PRF advantage in the ideal-compression model. -/
noncomputable def prfAdvantageI (IV : St) (sb : PkSeed → Blk) (blk : Ad → K → Blk) (out : St → Y)
    (A : PrfAdvI St Blk PkSeed Ad Y) : ℝ≥0∞ :=
  (prfRealIdeal IV sb blk out A).boolDist (prfIdealIdeal A)

end Games

end Ideal
