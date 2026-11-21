import Reduction.Games

/-!
# The multi-instance WOTS-TW game (M-EUF-GCMA) and its undetectability hybrids

This is the Lean counterpart of HK22 Def. 12 / Thm. 2 (M-EUF-GCMA of WOTS-TW) and of the EasyCrypt
game `M_EUF_GCMA_WOTSTWESNPRF` with its hybrids `Game2/3/4_WOTSTWES` (`proofs/WOTS_TW_ES.ec`).
It is an *intermediate* game, not an assumption: `Reduction.WotsUD`/`Reduction.WotsFinal` bound it
by SM-UD + SM-PRE + SM-TCR of `F`, and the final theorem does not mention it.

The adversary works in two phases, split at the reveal of `PK.seed` exactly as in the SM-games:

* `choose` (seed hidden): may ask for a WOTS+ signature at a fresh instance address on a message
  of its choice — the game samples that instance's `len` secret values, and returns the signature
  and the chain ends (the uncompressed WOTS+ public key) — and may evaluate `Thash` at every tweak
  that is not a chain-step tweak of an allowed instance;
* `forge` (seed revealed, no oracle): names an instance `j` of the signing history, a message
  `m' ≠ mⱼ` and a WOTS+ signature that recovers instance `j`'s chain ends.

`hyb k` is the hybrid in which chain `i` of a signature on `m` (digit `b = chainSteps m i`) is
started from a uniform value at position `min k (b - 1)` instead of position `0`:

* `k = 0`: the real game (every chain starts at position `0`);
* `k = w - 2`: every chain with `b ≥ 1` reveals `F(adrs(i, b-1), u)` for a uniform, never
  revealed `u` — an SM-PRE challenge; chains with `b = 0` reveal their uniform start value.

Consecutive hybrids differ only in whether the value at position `k + 1` of the chains with
`b - 1 > k` is `F(adrs(i,k), u)` or uniform, i.e. by one SM-UD game (HK22 proof of Thm. 2).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction
namespace WotsGame

variable {vp : ValidatedParams} (prims : Primitives vp.params)

/-- Signing-oracle interface: `(instance base address, message) ↦ (signature, chain ends)`;
`none` marks a refused query. -/
abbrev signSpec : OracleSpec (Adrs × prims.Y) :=
  (Adrs × prims.Y) →ₒ Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len)

/-- Collection-oracle interface: `(tweak, inputs) ↦ Thash`; `none` marks a refused query. -/
abbrev collSpec : OracleSpec (prims.AdrsKey × List prims.Y) :=
  (prims.AdrsKey × List prims.Y) →ₒ Option prims.Y

/-- One recorded signing query: instance address, message, signature, chain ends. -/
abbrev Entry : Type :=
  Adrs × prims.Y × WotsSig vp.params prims.core × Vector prims.Y vp.params.len

/-- A two-phase adversary against the WOTS game. -/
structure Adversary where
  /-- Private state carried across the seed reveal. -/
  State : Type
  /-- Phase 1: signing and collection access, seed hidden. -/
  choose : OracleComp (unifSpec + (signSpec prims + collSpec prims)) State
  /-- Phase 2: given the seed, output `(history index, message, signature)`. -/
  forge : State → prims.PkSeed → ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core)

variable {prims}

/-- `key` is a chain-step tweak of one of the allowed instances `insts`. -/
def reservedKey [DecidableEq prims.AdrsKey] (insts : List Adrs) (key : prims.AdrsKey) : Bool :=
  insts.any fun a => (List.range vp.params.len).any fun i =>
    (List.range (vp.params.w - 1)).any fun t =>
      decide (key = prims.adrsToKey ((wotsChainAdrs a i).setHashAddress t))

/-- The signature of hybrid `k` on `msg` at instance `a` from the start values `ss`. -/
def hybSig (k : ℕ) (pk : prims.PkSeed) (a : Adrs) (msg : prims.Y)
    (ss : Vector prims.Y vp.params.len) : WotsSig vp.params prims.core :=
  Vector.ofFn fun i : Fin vp.params.len =>
    let b := chainStepsCore prims.core msg i.val
    let c := min k (b - 1)
    chain prims pk (wotsChainAdrs a i.val) ss[i.val] c (b - c)

/-- The signing oracle of hybrid `k`.  A query is refused when its instance is not allowed or was
already used; otherwise fresh start values are drawn and the entry is recorded. -/
noncomputable def signOracle [SampleableType prims.Y] (k : ℕ) (insts : List Adrs)
    (pk : prims.PkSeed) :
    QueryImpl (signSpec prims) (StateT (List (Entry prims)) ProbComp) :=
  fun q => do
    let hist ← get
    if q.1 ∉ insts ∨ q.1 ∈ hist.map (·.1) then
      return none
    else
      let ss ← (monadLift ($ᵗ (Vector prims.Y vp.params.len) :
        ProbComp (Vector prims.Y vp.params.len)) :
          StateT (List (Entry prims)) ProbComp (Vector prims.Y vp.params.len))
      let sig := hybSig k pk q.1 q.2 ss
      let tops := wotsPkFromSigTops prims sig q.2 pk q.1
      set (hist ++ [(q.1, q.2, sig, tops)])
      return some (sig, tops)

/-- The collection oracle: `Thash` at the game's seed, refused at reserved chain-step tweaks. -/
def collOracle [DecidableEq prims.AdrsKey] (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (collSpec prims) (StateT (List (Entry prims)) ProbComp) :=
  fun q => pure (if reservedKey insts q.1 then none else some (prims.Thash pk q.1 q.2))

/-- All phase-1 oracles. -/
noncomputable def oracles [SampleableType prims.Y] [DecidableEq prims.AdrsKey] (k : ℕ)
    (insts : List Adrs) (pk : prims.PkSeed) :
    QueryImpl (unifSpec + (signSpec prims + collSpec prims))
      (StateT (List (Entry prims)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List (Entry prims)) ProbComp) +
    (signOracle k insts pk + collOracle insts pk)

/-- Hybrid `k` of the WOTS game over the allowed instances `insts`. -/
noncomputable def hyb [SampleableType prims.Y] [DecidableEq prims.Y] [DecidableEq prims.AdrsKey]
    (pkSeedDist : ProbComp prims.PkSeed) (insts : List Adrs) (k : ℕ) (W : Adversary prims) :
    ProbComp Bool := do
  let pk ← pkSeedDist
  let (st, hist) ← (simulateQ (oracles k insts pk) W.choose).run []
  let (j, m', sig') ← W.forge st pk
  match hist[j]? with
  | none => return false
  | some (a, m, _, tops) =>
    return decide (m' ≠ m ∧ wotsPkFromSigTops prims sig' m' pk a = tops)

end WotsGame

/-- The allowed instances of the WOTS game in the SLH-DSA reduction: the base addresses of all
WOTS+ instances of the hypertree. -/
def wotsInsts (vp : ValidatedParams) : List Adrs :=
  (allWotsInstances vp).map fun pos => wotsLeafAdrs pos.toAdrs pos.leaf.val

end Reduction
