# A-prf: the PRF game on the secret-key address domain

New files (nothing existing edited; oleans written): `Reduction/PrfDomain.lean`,
`Reduction/PrfDomainNonVacuity.lean`. No `sorry`/`axiom`/`native_decide`; axioms ⊆ `[propext,
Classical.choice, Quot.sound]`. `bPrfC`, `restrictImpl`, `skRestrict` are choice-free (definition bodies checked).

## Key finding: canonical-only does NOT fix the game
`Adrs.isCanonical` is the 32-byte ADRS check (4-byte layer, 12-byte tree). The SHA-2 `PRF` falls
back to `0^n` outside `Sha2Domain` = canonical ∧ 1-byte layer ∧ 8-byte tree (`Concrete/FIPS.lean:86,
140,192,290`). `⟨256,0,0,0,0,0⟩` IS canonical (`canonical_256`), so requested lemma 5(a) is false as
stated; the domain must also bound layer and tree. Chosen domain (decidable, depends on `d`, `h'`):
```lean
def SkDom (vp) (a : Adrs) : Prop := a.isCanonical = true ∧ a.IsSecretKey ∧ a.layer < vp.params.d ∧
    a.tree < 2 ^ ((vp.params.d - 1) * vp.params.hp)   -- AddressFacts ∧ type ∈ {WOTS_PRF, FORS_PRF}; superset of honest addresses
abbrev SkAdrs (vp) : Type := {a : Adrs // SkDom vp a}
def skPrfC vp prims : PRFScheme prims.SkSeed (prims.PkSeed × SkAdrs vp) prims.Y   -- eval k d = prims.PRF d.1 k d.2.val
```

## Proved (`Reduction/PrfDomain.lean`)
```lean
noncomputable def bPrfC A := simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bPrf A)
-- restrictImpl: forwards uniform queries; function query (pk,a) ↦ query (pk,⟨a,h⟩) if SkDom vp a, else `pure default`
theorem queriesIn_bRestC (hb : CanonicalAddressBounds vp.params) A pkSeed :
    Tables.QueriesIn {d | d.1 = pkSeed ∧ SkDom vp d.2} (bRestC A pkSeed)   -- default branch never taken
-- prfRealExperimentC_eq (programs equal), evalDist_prfIdealExperimentC_eq (laws equal) vs the old experiments at bPrf A
theorem prfRealC_bPrfC (hS : Structural vp prims) A : 𝒟[(skPrfC vp prims).prfRealExperiment (bPrfC A)] {true} = prTrue (g0 A)
theorem prfIdealC_bPrfC hS A : 𝒟[PRFScheme.prfIdealExperiment (bPrfC A)] {true} = prTrue (g1 A)
theorem prfAdvantageC_eq (hb : CanonicalAddressBounds vp.params) A :
    (skPrfC vp prims).prfAdvantage (bPrfC A) = (skPrf vp prims).prfAdvantage (bPrf A)
theorem stepPRFC (hS : Structural vp prims) A :
    prTrue (g0 A) ≤ prTrue (g1 A) + (skPrfC vp prims).prfAdvantage (bPrfC A)
theorem bPrfC_queryBound_exact A qs (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfC A) (fun i => i.isRight = true) (2 ^ vp.params.hp * vp.params.len + qs * signReads vp)
```
Wrapper lemmas (`Reduction.Restrict`): `simulateQ_fnImpl_restrict`, `simulateQ_restrict_liftM`,
`queriesIn_restrict`, `queryBound_restrict`. Integration: rewrite the PRF summand of `bound` with
`prfAdvantageC_eq hS.bounds` (an equality).

## Proved (`Reduction/PrfDomainNonVacuity.lean`)
Non-vacuity: `prfC_const_adv_zero` (advantage 0, any bundle), `prfTesterC_adv` (`= 1 − 1/|Y|` if
`PRF(pk,·,a)` is constant at some `a : SkAdrs vp`), `toy_prfC vp : ∃ B, … = 2⁻¹`, `toy_prfC_lost`,
`skAdrs0 vp : SkAdrs vp`. 128s: `stepPRFC_128s` (no hypothesis);
```lean
theorem canonical_256 : (⟨256,0,0,0,0,0⟩ : Adrs).isCanonical = true
theorem not_skDom_256 (vp) : ¬ SkDom vp ⟨256,0,0,0,0,0⟩      -- also not_skDom_badAdrs : ¬ SkDom Link.vp ⟨256,0,5,0,0,0⟩
theorem not_skDom_of_not_sha2Domain (hb : ApprovedAddressBounds vp.params) (h : ¬ Sha2Domain a) : ¬ SkDom vp a
theorem sha2PRFChecked_ok_128s pk k (a : SkAdrs Link.vp) :
    sha2PRFChecked pk k a.val = .ok (Link.prims.PRF pk k a.val) ∧
    byteArrayPrefixChecked (sha256 (sha2Prefix256 pk ⟨a.val, _, _, _⟩ ++ bytesToByteArray k)) 16 = .ok (Link.prims.PRF pk k a.val)
theorem prf_128s_spec pk k a : Link.nd (Link.prims.PRF pk k a.val) = Spec.PRF (Link.nd pk) (Link.nd k) (Link.adr a.val)
theorem prf_128s_thash pk k a : Link.prims.PRF pk k a.val = Link.prims.Thash pk (Link.prims.adrsToKey a.val) [k]
theorem prf_256_eq_zero pk k : Link.prims.PRF pk k ⟨256,0,0,0,0,0⟩ = zeroBytes 16   -- general: sha2PRF_eq_zero_of_not_sha2Domain
theorem skPrf_broken_128s pk : (skPrf Link.vp Link.prims).prfAdvantage (prfTester pk ⟨256,0,0,0,0,0⟩ (zeroBytes 16))
    = 1 - (Fintype.card Link.prims.Y : ℝ≥0∞)⁻¹     -- old game false at 128s; skPrf_broken_128s_half: 2⁻¹ ≤ it
```

## Audit of the other seven games (SHA2-128s, `Concrete/FIPS.lean`): verdict — no other degenerate input
Only `skPrf` takes a structured `Adrs` from the adversary; every other game input is a fixed-width
byte vector or a byte list, and the concrete functions are total without a reachable fallback:
- `msgPrf` (`Y × List Byte`): `sha2PRFmsg` (FIPS.lean:166) = `byteArrayPrefixOrZero (hmacSha256 …) 16`;
  the zero branch needs output < 16 bytes, never (`Link.PRFmsg_eq`, Link/Hash.lean:115, holds for
  ALL inputs, = `Spec.PRFmsg`). No degenerate input.
- `hmsgFamily`/`itsrProblem`: `sha2Hmsg` (FIPS.lean:174) = prefix of MGF1; `Link.Hmsg_eq`
  (Link/Hash.lean:127) for ALL inputs, no fallback. `splitDigest` (Position.lean:62) is total on
  `Bytes m` (indices reduced mod `2^(h−h')`, `2^h'`, as FIPS); `forsIdx` (Fors.lean:45) has a
  `getD i 0` default but `forsIndices` (Basic.lean:96) only asks `i < k`. No artefact.
- `tcrProblem`, `forsOpenPreProblem`, `wotsUdProblem`, `wotsPreProblem`, `wotsTcrProblem`: tweak type
  `prims.AdrsKey = Bytes 22` (FIPS.lean:287), chosen as raw bytes; `sha2Thash` (FIPS.lean:269) is
  total on every key and every arity: at n = 16 it is `Trunc16(SHA-256(pk‖0^48‖key‖concat ms))` for
  all lists (private `thash_key_eq`, Link/Hash.lean:67), zero branch unreachable; cross-arity
  inputs differ in length. The assumptions range over all 22-byte tweaks: stronger than needed, not degenerate.
- `adrsToKey = sha2AdrsKey` (FIPS.lean:213) DOES have a fallback: every out-of-`Sha2Domain` address
  maps to one of two `sha2FallbackKey`s (FIPS.lean:203), so tweaks collide there. It enters no game
  (games quantify over `AdrsKey`); reductions apply it only to ledger addresses, where
  `Structural.keyInj` (injective on `AddressFacts vp`, KeyDiscipline.lean:66,105) applies.
- Modelling notes, not winnable artefacts: (i) `Sha2.pad` (VCVio/Algorithms/Sha2.lean:108-110)
  takes the bit length mod 2^64, so `sha256` is defined past FIPS 180-4's 2^64-bit limit and the
  `List Byte` domains of `msgPrf`/ITSR include such messages; (ii) at n = 24/32 singleton `Thash`
  is SHA-256, other arities SHA-512 (FIPS.lean:264) — irrelevant at 128s.
