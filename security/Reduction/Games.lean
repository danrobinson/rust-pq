import Reduction.Basic

/-!
# Game sequence for the standard-model proof

* `G0` — the real EUF-CMA experiment `SignatureAlg.unforgeableExperiment` against
  `internalAlg vp prims optRand pkSeedDist`.
* `G1` (`g1`) — WOTS+/FORS secrets are read from a uniformly sampled table instead of
  `PRF(PK.seed, SK.seed, ·)` (EC: `EUF_CMA_SPHINCSPLUSTWFS_NPRFPRF`).  It is the *same* VCVio
  experiment, run against the signature scheme `tableAlg`.
* `G2` (`g2`) — additionally the randomizer `R` is a lazily sampled random function of
  `(opt_rand, M)` instead of `PRF_msg(SK.prf, ·, ·)` (EC: `…_NPRFNPRF`).
* `g2Class c` — `G2` intersected with the event "the forgery is of class `c`", for the four
  classes `ForgeryClass`.  The classes partition the forgery space (`classify` is total), so
  `Pr[G2] = Σ_c Pr[g2Class c]` is an identity; all cryptographic content sits in the four branch
  reductions.

All honest objects of `G1`/`G2` are computed by VCVio's provider-parametric programs
(`HashSig.SLHDSA.SecretProvider`) at the pure provider `fun a => pure (tbl (secIdx a))`, over the
*same* `prims.core`; no second copy of the scheme is defined.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction

variable (vp : ValidatedParams) (prims : Primitives vp.params)

/-! ## The secret table -/

/-- Index of the secret table: a 256-bit packing of the six address words. -/
abbrev SecIdx : Type := Fin (2 ^ 256)

/-- Pack an address into the table index (injective on FIPS-canonical addresses, see
`secIdx_injOn_canonical` in `Reduction.PRFHop`). -/
def secIdx (a : Adrs) : SecIdx :=
  Fin.ofNat _ (a.layer + 2 ^ 32 * (a.tree + 2 ^ 96 * (a.type + 2 ^ 32 *
    (a.word1 + 2 ^ 32 * (a.word2 + 2 ^ 32 * a.word3)))))

/-- A table of WOTS+/FORS secret values, one per (packed) address. -/
abbrev SecretTable : Type := SecIdx → prims.Y

/-- The secret provider of a table. -/
def secretOf (tbl : SecretTable vp prims) (a : Adrs) : prims.Y := tbl (secIdx a)

/-- A uniformly random table: independent uniform values at every index, drawn one after the
other in increasing index order (`Fin.mOfFn`).  The definition is choice-free: it does not go
through `Fintype.mPi`/`Fintype.equivFin`.  It denotes the uniform measure on tables
(`evalDist_sampleTable` in `Reduction.Tables`).

**Limitation.**  This is an *eager* table with `2^256` cells; a program that runs it is not
feasible, and sampling a type of this size is exactly what an efficient reduction must avoid.  It
is kept as the reference distribution of `G1`/`G2`.  The adversaries `bPrfMsg`, `bItsr`,
`bOpenPre`, `bTcr`, `bWots` of `Reduction/Final.lean` call it and are therefore choice-free but
infeasible definitions; the variants in `Reduction/Lazy/` replace it by lazy sampling (`bPrfMsgL`,
`bItsrL`) or by a table sampled only on the `2^h·k·2^a + #inst·len` secret cells of the key
structure (`sparseOn`), with equal advantage.  No statement about running time (as opposed to
query, sample and hash-evaluation counts) is made anywhere. -/
noncomputable def sampleTable [SampleableType prims.Y] : ProbComp (SecretTable vp prims) :=
  Fin.mOfFn (2 ^ 256) fun _ => ($ᵗ prims.Y : ProbComp prims.Y)

/-! ## Honest algorithms over a table -/

/-- `PK.root` of the key whose secrets are the table. -/
def idealRoot (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
      (fun a => pure (secretOf vp prims tbl a)) pkSeed :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- The public key of a table. -/
def idealPk (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) : PublicKeyCore prims.core :=
  ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩

/-- FIPS 205 Algorithm 19 with secrets from the table and the randomizer `R` supplied. -/
def idealSign (tbl : SecretTable vp prims) (msg : List Byte) (pk : PublicKeyCore prims.core)
    (R : prims.Y) : GeneralScheme.SignatureCore vp prims.core :=
  simulateQ (PublicHash.impl prims)
    (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
      (fun a => pure (secretOf vp prims tbl a)) msg pk.pkSeed pk.pkRoot R :
      OracleComp (publicHashSpec prims.core) (GeneralScheme.SignatureCore vp prims.core))

section Schemes

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The scheme under attack (abbreviation for the statement of the theorems). -/
noncomputable abbrev realAlg :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (GeneralScheme.SignatureCore vp prims.core) :=
  internalAlg vp prims optRand pkSeedDist

/-- A chosen-message forger against the scheme. -/
abbrev Forger : Type :=
  SignatureAlg.UnforgeableAdversary (realAlg vp prims optRand pkSeedDist)

/-- The scheme of game `G1`: secrets from a uniform table, `R` still `PRF_msg(SK.prf, ·, ·)`. -/
noncomputable def tableAlg :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core)
      (SecretTable vp prims × prims.SkPrf) (GeneralScheme.SignatureCore vp prims.core) where
  keygen := do
    let pkSeed ← pkSeedDist
    let tbl ← sampleTable vp prims
    let skPrf ← $ᵗ prims.SkPrf
    pure (idealPk vp prims tbl pkSeed, (tbl, skPrf))
  sign pk sk msg := do
    let addrnd ← optRand pk
    pure (idealSign vp prims sk.1 msg pk (prims.PRFmsg sk.2 addrnd msg))
  verify pk msg sig := pure (GeneralScheme.verifyInternal vp prims msg sig pk)

variable {vp prims optRand pkSeedDist}

/-- Game `G0`: the real EUF-CMA experiment. -/
noncomputable def g0 (A : Forger vp prims optRand pkSeedDist) : ProbComp Bool :=
  SignatureAlg.unforgeableExperiment A

/-- Game `G1`: the same experiment and the same adversary program against `tableAlg`. -/
noncomputable def g1 (A : Forger vp prims optRand pkSeedDist) : ProbComp Bool :=
  SignatureAlg.unforgeableExperiment
    (sigAlg := tableAlg vp prims optRand pkSeedDist) ⟨A.main⟩

end Schemes

/-! ## Forgery classification (deterministic) -/

/-- The four ways a forgery is charged to a hash property. -/
inductive ForgeryClass
  /-- every FORS leaf the forged digest opens was opened by a signing query (ITSR) -/
  | itsr
  /-- some hypertree layer recovers the honest WOTS+ chain ends from a different message -/
  | wots
  /-- some unopened FORS leaf image is hit by the forged secret value (open preimage) -/
  | openpre
  /-- everything else: a collision against an honest hash call (SM-TCR on `Thash`) -/
  | tcr
deriving DecidableEq, Repr

variable {vp prims}

/-- The digest split verification computes for `(R, M)` under `pk`. -/
def digestParts (pk : PublicKeyCore prims.core) (R : prims.Y) (msg : List Byte) :
    DigestParts vp.params :=
  splitDigest vp.params (prims.Hmsg R pk.pkSeed pk.pkRoot msg)

/-- All FORS leaves opened by the signing transcript `signed = [(Mᵢ, Rᵢ)]`. -/
def openedLeaves (pk : PublicKeyCore prims.core) (signed : List (List Byte × prims.Y)) :
    List (Adrs × ℕ) :=
  signed.flatMap fun e => forsIndices vp (digestParts pk e.2 e.1)

/-- The message WOTS+-signed at layer `j` when hypertree verification is run on the XMSS
signature vector `s` from layer-zero message `m0` (so `layerMsg … 0 = m0`, and
`layerMsg … d` is the recovered root). -/
def layerMsg (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) : ℕ → prims.Y
  | 0 => m0
  | j + 1 =>
    if h : j < vp.params.d then
      xmssPkFromSig prims (LayerPosition.atLayer vp parts ⟨j, h⟩).leaf.val s[j]
        (layerMsg pkSeed parts s m0 j) pkSeed (LayerPosition.atLayer vp parts ⟨j, h⟩).toAdrs
    else layerMsg pkSeed parts s m0 j

/-- Base address of the WOTS+ instance used at layer `j` on the path of `parts`. -/
def layerWotsAdrs (parts : DigestParts vp.params) (j : Fin vp.params.d) : Adrs :=
  wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs (LayerPosition.atLayer vp parts j).leaf.val

/-- The WOTS+ chain ends recovered at layer `j`. -/
def layerTops (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (j : Fin vp.params.d) :
    Vector prims.Y vp.params.len :=
  wotsPkFromSigTops prims (s[j.val]).wots (layerMsg pkSeed parts s m0 j.val) pkSeed
    (layerWotsAdrs parts j)

section Classify

variable [DecidableEq prims.Y]

/-- The first layer at which the forged and the reference signature WOTS+-sign *different*
messages but recover the *same* chain ends. -/
def wotsLayer? (pk : PublicKeyCore prims.core) (parts : DigestParts vp.params)
    (forged ref : GeneralScheme.SignatureCore vp prims.core) : Option (Fin vp.params.d) :=
  let fm0 := forsPkFromSig prims forged.fors parts.md.toList pk.pkSeed parts.forsAdrs
  let hm0 := forsPkFromSig prims ref.fors parts.md.toList pk.pkSeed parts.forsAdrs
  (List.finRange vp.params.d).find? fun j =>
    decide (layerMsg pk.pkSeed parts forged.hypertree fm0 j.val ≠
        layerMsg pk.pkSeed parts ref.hypertree hm0 j.val ∧
      layerTops pk.pkSeed parts forged.hypertree fm0 j =
        layerTops pk.pkSeed parts ref.hypertree hm0 j)

/-- Global index of the leaf that `parts` opens in FORS tree `i`. -/
def leafIndex (parts : DigestParts vp.params) (i : Fin vp.params.k) : ℕ :=
  i.val * 2 ^ vp.params.a + forsIdx vp.params parts.md.toList i.val

/-- The first FORS tree whose opened leaf was never opened by a signing query and whose leaf
image is hit by the forged secret value. -/
def openTree? (pk : PublicKeyCore prims.core) (parts : DigestParts vp.params)
    (opened : List (Adrs × ℕ))
    (forged ref : GeneralScheme.SignatureCore vp prims.core) : Option (Fin vp.params.k) :=
  (List.finRange vp.params.k).find? fun i =>
    decide ((parts.forsAdrs, leafIndex parts i) ∉ opened ∧
      prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) (forged.fors[i.val]).sk =
        prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) (ref.fors[i.val]).sk)

/-- Classify a forgery `(msg, forged)` against the public key `pk`, the signing transcript
`signed = [(Mᵢ, Rᵢ)]`, and the *reference signature* `ref`: the honest signature on `msg` under
the forgery's own randomizer.  Total: every forgery has exactly one class. -/
def classify (pk : PublicKeyCore prims.core) (signed : List (List Byte × prims.Y))
    (msg : List Byte) (forged ref : GeneralScheme.SignatureCore vp prims.core) : ForgeryClass :=
  let parts : DigestParts vp.params := digestParts pk forged.randomness msg
  let opened := openedLeaves pk signed
  if ∀ x ∈ forsIndices vp parts, x ∈ opened then .itsr
  else if (wotsLayer? pk parts forged ref).isSome then .wots
  else if (openTree? pk parts opened forged ref).isSome then .openpre
  else .tcr

end Classify

/-! ## Game `G2` -/

section G2

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- Transcript of `G2`: one entry `(M, opt_rand, R)` per signing query, in order. -/
abbrev G2Log (prims : Primitives vp.params) : Type := List (List Byte × prims.Y × prims.Y)

/-- The randomizer for `(addrnd, msg)` given the transcript so far: the recorded one if this pair
was already signed (a random *function*), otherwise a fresh uniform value. -/
noncomputable def lazyRandomizer (log : G2Log prims) (msg : List Byte) (addrnd : prims.Y) :
    ProbComp prims.Y :=
  match log.find? (fun e => decide (e.1 = msg ∧ e.2.1 = addrnd)) with
  | some e => pure e.2.2
  | none => $ᵗ prims.Y

/-- The signing oracle of `G2`, for an arbitrary deterministic signer `signR` taking the message
and the randomizer (in `G2` itself: `idealSign` at the table). -/
noncomputable def g2SignOracle (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (G2Log prims) ProbComp) :=
  fun msg => do
    let addrnd ← (monadLift (optRand pk) : StateT (G2Log prims) ProbComp prims.Y)
    let log ← get
    let R ← (monadLift (lazyRandomizer log msg addrnd) : StateT (G2Log prims) ProbComp prims.Y)
    set (log ++ [(msg, addrnd, R)])
    return signR msg R

/-- Run a forger against `g2SignOracle` at the signer `signR`; returns the forgery and the
transcript.  Reductions that know the seed run the forger through this very function. -/
noncomputable def g2RunWith (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    ProbComp ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g2SignOracle optRand pk signR) (A.main pk)).run []

/-- Run a forger against the `G2` signing oracle of the table `tbl`. -/
noncomputable def g2Run (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) :
    ProbComp ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  g2RunWith A pk fun m R => idealSign vp prims tbl m pk R

/-- The `(Mᵢ, Rᵢ)` projection of a transcript. -/
def G2Log.signed (log : G2Log prims) : List (List Byte × prims.Y) :=
  log.map fun e => (e.1, e.2.2)

/-- "The forgery is fresh and verifies" in `G2`. -/
def g2Valid (pk : PublicKeyCore prims.core) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : Bool :=
  decide (msg ∉ log.map (·.1)) && GeneralScheme.verifyInternal vp prims msg sig pk

/-- The class of the forgery in `G2`. -/
def g2ClassOf (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) : ForgeryClass :=
  classify pk (G2Log.signed log) msg sig (idealSign vp prims tbl msg pk sig.randomness)

/-- Game `G2`. -/
noncomputable def g2 (A : Forger vp prims optRand pkSeedDist) : ProbComp Bool := do
  let pkSeed ← pkSeedDist
  let tbl ← sampleTable vp prims
  let pk := idealPk vp prims tbl pkSeed
  let ((msg, sig), log) ← g2Run A tbl pk
  return g2Valid pk log msg sig

/-- Game `G2` intersected with "the forgery has class `c`". -/
noncomputable def g2Class (A : Forger vp prims optRand pkSeedDist) (c : ForgeryClass) :
    ProbComp Bool := do
  let pkSeed ← pkSeedDist
  let tbl ← sampleTable vp prims
  let pk := idealPk vp prims tbl pkSeed
  let ((msg, sig), log) ← g2Run A tbl pk
  return g2Valid pk log msg sig && decide (g2ClassOf tbl pk log msg sig = c)

end G2

end Reduction
