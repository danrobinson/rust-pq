import MReduction.Instances
import MLink.Hash
import MLink.Security
import Reduction.PrfDomainNonVacuity
import Reduction.ForsTightNonVacuity

/-!
# Audit: what the twelve terms of the final bound are about at each SHA-2 parameter set

The generic reduction (`security/Reduction`) is stated for an abstract bundle `prims`; its games
are about `prims.Thash` restricted to an arity class, `prims.PRF` on secret-key addresses,
`prims.PRFmsg` and `prims.Hmsg`.  At `S.prims = sha2Primitives S.vp.params` these are *different
concrete functions depending on `S`* (FIPS 205 §11.2.1 vs §11.2.2).  This file proves which.

| term of `boundFinalTight` | game (function) | `n = 16` (128s, 128f) | `n = 24, 32` (192s/f, 256s/f) |
|---|---|---|---|
| `(skPrfC).prfAdvantage` | `PRF` on `SkAdrs` | SHA-256, pad `64 − n` | SHA-256, pad `64 − n` |
| `(msgPrf).prfAdvantage` | `PRF_msg` | HMAC-SHA-256 | HMAC-SHA-512 |
| `ITSRAdvantage` | `H_msg` | MGF1-SHA-256 ∘ SHA-256 | MGF1-SHA-512 ∘ SHA-512 |
| SM-DSPR, 3·SM-TCR at FORS leaves | `F` (`fHash`) | SHA-256 | SHA-256 |
| class `1` (`thashArityProblemT … 1`) | `F` | SHA-256 | SHA-256 |
| class `2` | `H` | SHA-256 | SHA-512, pad `128 − n` |
| class `len` | `T_len` | SHA-256 | SHA-512 |
| class `k` | `T_k` | SHA-256 | SHA-512 |
| `(w−2)`·SM-UD, SM-PRE, chain SM-TCR | `F` (`fHash`) | SHA-256 | SHA-256 |

In every SM game the *collection* oracle (`thashColl`) is the whole `Thash`, i.e. at `n = 24, 32`
both the SHA-256 and the SHA-512 function, at any arity and any 22-byte key.

Proved here: `arities_pairwise`, `arities_injective` (the four classes are four different games
at every set); `fHash_eval`, `thash_class` (which hash each class is), `problem_th` (which
function each game is about), `prf_spec`, `prfMsg_spec`, `hmsg_spec`; the `PRF`-domain facts
(`skAdrs_dom`, `sha2PRFChecked_ok`, `prf_thash`, `prf_spec`, `not_skDom_badAdrs`, `skPrf_broken`);
the address-width facts behind `structural S`; instances of the generic non-vacuity lemmas.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SLHDSA.Concrete ENNReal

namespace MReduction

open MLink Reduction TweakableHash

variable (S : Sha2Set)

/-! ## 1. Parameters that enter the generic statements -/

/-- `len` and `k` at each set. -/
theorem len_k :
    (S.vp.params.len, S.vp.params.k) =
      match S with
      | .s128s => (35, 14) | .s128f => (35, 33) | .s192s => (51, 17)
      | .s192f => (51, 33) | .s256s => (67, 22) | .s256f => (67, 35) := by
  cases S <;> decide

/-- **The four arities `1, 2, len, k` are pairwise distinct at every set**, so the four class
terms of the bound are four different games (in particular at 256f: `k = 35 ≠ 67 = len`; at
128f/192f `k = 33`, `len = 35/51`). -/
theorem arities_pairwise :
    (1 : ℕ) ≠ 2 ∧ 1 ≠ S.vp.params.len ∧ 1 ≠ S.vp.params.k ∧ 2 ≠ S.vp.params.len ∧
      2 ≠ S.vp.params.k ∧ S.vp.params.len ≠ S.vp.params.k := by
  cases S <;> decide

theorem arities_injective : Function.Injective (arities S.vp) := by
  cases S <;> decide

/-- The coefficient of the undetectability term is `w − 2 = 14` at every set (`lg w = 4`). -/
theorem w_sub_two : S.vp.params.w - 2 = 14 := by cases S <;> rfl

/-- `n = 16` exactly at 128s and 128f. -/
theorem n_eq_16_iff : S.vp.params.n = 16 ↔ S = .s128s ∨ S = .s128f := by
  cases S <;> decide

/-- The compressed address has room for every hypertree address: `d ≤ 256` and the layer-0 tree
index has `(d − 1)·h' ≤ 64` bits — with equality at 256f. -/
theorem treeBits :
    S.vp.params.d ≤ 256 ∧ (S.vp.params.d - 1) * S.vp.params.hp ≤ 64 ∧
      (S.vp.params.d - 1) * S.vp.params.hp = S.vp.params.h - S.vp.params.hp ∧
      ((S.vp.params.d - 1) * S.vp.params.hp = 64 ↔ S = .s256f) := by
  cases S <;> decide

/-- The address-width hypothesis used by `structural S` (VCVio's `fipsApprovedAddressBounds`,
which covers all twelve FIPS sets, including the 64-bit tree index of 256f). -/
theorem approvedBounds : ApprovedAddressBounds S.vp.params := fipsApprovedAddressBounds S.fips

/-! ## 2. Which function each game is about -/

/-- `fHash` — the function of the FORS-leaf DSPR/TCR games and of the WOTS UD/PRE/chain-TCR games
— is `Trunc_n(SHA-256(PK.seed ‖ 0^(64−n) ‖ key ‖ x))` at **every** set. -/
theorem fHash_eval (d : ProbComp S.prims.PkSeed) (pk : S.Node) (key : Bytes 22) (x : S.Node) :
    nd ((fHash S.vp S.prims d).eval pk key x) =
      (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.vp.params.n) ++ nd key ++ nd x)).take
        S.vp.params.n := by
  have := thash_singleton_sha256 S pk key [x] rfl
  simp only [nds, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

/-- The function of each of the nine tweakable-hash games. -/
theorem problem_th (d : ProbComp S.prims.PkSeed) (n : ℕ) :
    (wotsUdProblem S.vp S.prims d).th = fHash S.vp S.prims d ∧
    (wotsPreProblem S.vp S.prims d).th = fHash S.vp S.prims d ∧
    (wotsTcrProblemT S.vp S.prims d).th = fHash S.vp S.prims d ∧
    (∀ pk key (m : {xs : List S.prims.Y // xs.length = n}),
      (thashArityProblemT S.vp S.prims d n).th.eval pk key m = S.prims.Thash pk key m.1) :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- **The class-`n` function.**  `S.prims.Thash` on a list of `n` nodes is the SHA-256 form
(pad `64 − n`) if `n = 1` or the set has `n = 16`, and the SHA-512 form (pad `128 − n`)
otherwise.  With `arities_pairwise`: class `1` is SHA-256 at every set; classes `2`, `len`, `k`
are SHA-256 at 128s/128f and SHA-512 at 192s/192f/256s/256f. -/
theorem thash_class (pk : S.Node) (key : Bytes 22) (xs : List S.Node) :
    nd (S.prims.Thash pk key xs) =
      if xs.length = 1 ∨ S.vp.params.n = 16 then
        (Spec.sha256 (nd pk ++ Spec.toByte 0 (64 - S.vp.params.n) ++ nd key ++ nds xs)).take
          S.vp.params.n
      else
        (Spec.sha512 (nd pk ++ Spec.toByte 0 (128 - S.vp.params.n) ++ nd key ++ nds xs)).take
          S.vp.params.n := by
  split_ifs with h
  · by_cases h1 : xs.length = 1
    · exact thash_singleton_sha256 S pk key xs h1
    · exact thash_sha256_of_n16 S pk key xs h1 (h.resolve_left h1)
  · exact thash_sha512_of_n_ne_16 S pk key xs (fun h1 => h (Or.inl h1)) (fun hn => h (Or.inr hn))

/-- Classes `2`, `len`, `k` (`H`, `T_len`, `T_k`) at the sets with `n ≠ 16`: SHA-512. -/
theorem thash_class_sha512 (hn : S.vp.params.n ≠ 16) (pk : S.Node) (key : Bytes 22)
    (xs : List S.Node)
    (hxs : xs.length = 2 ∨ xs.length = S.vp.params.len ∨ xs.length = S.vp.params.k) :
    nd (S.prims.Thash pk key xs) =
      (Spec.sha512 (nd pk ++ Spec.toByte 0 (128 - S.vp.params.n) ++ nd key ++ nds xs)).take
        S.vp.params.n := by
  obtain ⟨-, h1, h2, -⟩ := arities_pairwise S
  exact thash_sha512_of_n_ne_16 S pk key xs (by rcases hxs with h | h | h <;> omega) hn

/-! ## 3. The `PRF` game: domain facts at every set -/

/-- Every address of the `PRF` game's domain `SkAdrs S.vp` is in the checked `ADRSc` domain. -/
theorem skAdrs_dom (a : SkAdrs S.vp) : MLink.Dom a.val :=
  a.2.sha2Domain (fipsApprovedAddressBounds S.fips)

/-- The out-of-domain secret-key address `⟨256,0,5,0,0,0⟩` of `MLink.not_hprf` is not in the
domain of the `PRF` game. -/
theorem not_skDom_badAdrs : ¬ SkDom S.vp MLink.badAdrs :=
  not_skDom_of_not_sha2Domain (fipsApprovedAddressBounds S.fips)
    fun h => absurd h.2.1 (by decide)

private theorem prefixChecked_ok' (b : ByteArray) (n : ℕ) (h : n ≤ b.size) :
    ∃ v : Bytes n, byteArrayPrefixChecked b n = .ok v := by
  have hraw : (b.extract 0 n).toList = b.data.toList.take n := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract]
    simp
  have hl : (b.extract 0 n).toList.length = n := by
    rw [hraw, List.length_take]
    have : b.data.toList.length = b.size := by rw [Array.length_toList]; rfl
    omega
  exact ⟨⟨(b.extract 0 n).toList.toArray, by simpa using hl⟩, by
    simp [byteArrayPrefixChecked, decodeExact, hl]⟩

/-- **No fallback on the domain of the `PRF` game**: for every address of `SkAdrs S.vp` the
checked SHA-2 `PRF` succeeds and `S.prims.PRF` is its value (generic form of
`Reduction.sha2PRFChecked_ok_128s`). -/
theorem sha2PRFChecked_ok (pk k : S.Node) (a : SkAdrs S.vp) :
    sha2PRFChecked pk k a.val = .ok (S.prims.PRF pk k a.val) := by
  have ⟨h1, h2, h3⟩ : a.val.isCanonical = true ∧ Adrs.Fits 1 a.val.layer = true ∧
      Adrs.Fits 8 a.val.tree = true := skAdrs_dom S a
  obtain ⟨v, hv⟩ := prefixChecked_ok' (VCVio.Algorithms.Sha2.sha256
    (sha2Prefix256 pk ⟨a.val, h1, h2, h3⟩ ++ bytesToByteArray k)) S.vp.params.n
    (by have := S.n_le_32; simpa using this)
  have hc : sha2PRFChecked pk k a.val = .ok v := by
    simp only [sha2PRFChecked, Sha2Address.ofAdrs, h1, h2, h3, dite_true]
    exact hv
  have e : S.prims.PRF pk k a.val = v := by
    show checkedNodeOrZero (sha2PRFChecked pk k a.val) = v
    rw [hc]; rfl
  rw [e]
  exact hc

/-- On its domain, `S.prims.PRF` is the bundle's tweakable hash at the compressed address key
applied to `[SK.seed]`. -/
theorem prf_thash (pk k : S.Node) (a : SkAdrs S.vp) :
    S.prims.PRF pk k a.val = S.prims.Thash pk (S.prims.adrsToKey a.val) [k] :=
  (MLink.hprf_dom S pk k a.val (skAdrs_dom S a)).symm

/-- **The `PRF` term.**  The function of the game `skPrfC S.vp S.prims` is FIPS 205's `PRF`,
`Trunc_n(SHA-256(PK.seed ‖ 0^(64−n) ‖ ADRSc ‖ SK.seed))`, at every set (generic form of
`Reduction.prf_128s_spec`). -/
theorem prf_spec (pk k : S.Node) (a : SkAdrs S.vp) :
    nd ((skPrfC S.vp S.prims).eval k (pk, a)) =
      Spec.PRF S.spec (nd pk) (nd k) (adr a.val) :=
  MLink.PRF_eq S pk k a.val (skAdrs_dom S a)

/-- **The `PRF_msg` term**: `Trunc_n(HMAC-SHA-256(SK.prf, opt_rand ‖ M))` for `n = 16`,
HMAC-SHA-512 otherwise (`Spec.PRFmsg`). -/
theorem prfMsg_spec (k r : S.Node) (m : List UInt8) :
    nd ((msgPrf S.vp S.prims).eval k (r, m)) = Spec.PRFmsg S.spec (nd k) (nd r) (sp m) :=
  MLink.PRFmsg_eq S k r m

/-- **The ITSR term**: the keyed family is `H_msg`, MGF1-SHA-256 over an inner SHA-256 for
`n = 16`, MGF1-SHA-512 over an inner SHA-512 otherwise (`Spec.Hmsg`). -/
theorem hmsg_spec (R pk root : S.Node) (m : List UInt8) :
    nd ((hmsgFamily S.vp S.prims).hash R (pk, root, m)) =
      Spec.Hmsg S.spec (nd R) (nd pk) (nd root) (sp m) :=
  MLink.Hmsg_eq S R pk root m

example (k r m : Spec.Bytes) : Spec.PRFmsg S.spec k r m =
    if S.spec.n = 16 then (Spec.hmacSha256 k (r ++ m)).take S.spec.n
    else (Spec.hmacSha512 k (r ++ m)).take S.spec.n := by cases S <;> rfl

/-! ### The unrestricted `PRF` game is broken at every set (why the domain matters) -/

/-- `PRF(pk, k, ⟨256,0,0,0,0,0⟩) = 0^n` for all `pk`, `k`. -/
theorem prf_256_eq_zero (pk k : S.Node) :
    S.prims.PRF pk k ⟨256, 0, 0, 0, 0, 0⟩ = zeroBytes S.vp.params.n :=
  sha2PRF_eq_zero_of_not_sha2Domain S.vp.params pk k not_sha2Domain_256

/-- The one-query distinguisher at the canonical, out-of-`ADRSc`-domain address
`⟨256,0,0,0,0,0⟩` has advantage `1 − 1/|Y|` against the unrestricted game `skPrf S.vp S.prims`
(not used by any final theorem; they use `skPrfC`). -/
theorem skPrf_broken (pk : S.prims.PkSeed) :
    (skPrf S.vp S.prims).prfAdvantage
        (prfTester (prims := S.prims) pk ⟨256, 0, 0, 0, 0, 0⟩ (zeroBytes S.vp.params.n)) =
      1 - (Fintype.card S.prims.Y : ℝ≥0∞)⁻¹ :=
  prfTester_adv (vp := S.vp) (prims := S.prims) pk _ _ fun k => prf_256_eq_zero S pk k

/-! ## 4. Non-vacuity: the generic lemmas at `S` -/

/-- Every game of the final bound can be lost at every set (instances of the generic lemmas). -/
theorem games_can_be_lost (d : ProbComp S.prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_Advantage (prob := thashArityProblemT S.vp S.prims d n)
        ⟨Unit, pure (), fun _ _ => pure (0, arityDefault S.prims n)⟩ = 0 ∧
    SM_DT_TCR_Advantage (prob := wotsTcrProblemT S.vp S.prims d)
        ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 ∧
    SM_DT_TCR_SourceFinalValidity.advantage (prob := forsTcrProblem S.vp S.prims d)
        ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 ∧
    SM_DT_DSPR_SourceFinalValidity.advantage (prob := forsDsprProblem S.vp S.prims d)
        ⟨Unit, pure (), fun _ _ => pure (0, false)⟩ = 0 ∧
    SM_DT_PRE_Advantage (prob := wotsPreProblem S.vp S.prims d)
        ⟨Unit, pure (), fun _ _ => pure (0, default)⟩ = 0 ∧
    SM_DT_UD_Advantage (prob := wotsUdProblem S.vp S.prims d)
        ⟨Unit, pure (), fun _ _ => pure true⟩ = 0 ∧
    (skPrfC S.vp S.prims).prfAdvantage (pure true :
        OracleComp (PRFScheme.PRFOracleSpec (S.prims.PkSeed × SkAdrs S.vp) S.prims.Y) Bool) = 0 ∧
    (msgPrf S.vp S.prims).prfAdvantage (pure true :
        OracleComp (PRFScheme.PRFOracleSpec (S.prims.Y × List Byte) S.prims.Y) Bool) = 0 :=
  ⟨thashArityT_trivial_adv_zero d n, wotsTcrT_trivial_adv_zero d, forsTcr_trivial_adv_zero d,
    forsDspr_trivial_adv_zero d, pre_trivial_adv_zero d, ud_const_adv_zero d true,
    prfC_const_adv_zero, prfMsg_const_adv_zero⟩

/-- The four class games have a positive target cap at every set and are won with advantage `1`
by `thashArityColliderT` given a seed-independent collision in the class (the generic
`thashArityColliderT_adv_one`; no such collision is known for SHA-2, which is the assumption). -/
theorem class_game_winnable (d : ProbComp S.prims.PkSeed) (n : ℕ)
    (h0 : 0 < arityTargets S.vp n) (t : S.prims.AdrsKey)
    (x y : {xs : List S.prims.Y // xs.length = n}) (hne : y ≠ x)
    (hcol : ∀ pk, S.prims.Thash pk t y.1 = S.prims.Thash pk t x.1) :
    SM_DT_TCR_Advantage (thashArityColliderT (vp := S.vp) d n t x y) = 1 :=
  thashArityColliderT_adv_one d n h0 t x y hne hcol

/-- The caps are positive at every set. -/
theorem caps_pos :
    0 < arityTargets S.vp 1 ∧ 0 < wotsStepTargetsT S.vp ∧ 0 < openPreTargets S.vp ∧
      0 < wotsChainTargets S.vp ∧ 0 < tcrTargets S.vp :=
  ⟨arityTargets_one_pos S.vp, wotsStepTargetsT_pos S.vp, openPreTargets_pos S.vp,
    wotsChainTargets_pos S.vp, tcrTargets_pos S.vp⟩

#print axioms arities_pairwise
#print axioms arities_injective
#print axioms fHash_eval
#print axioms thash_class
#print axioms thash_class_sha512
#print axioms skAdrs_dom
#print axioms sha2PRFChecked_ok
#print axioms prf_thash
#print axioms prf_spec
#print axioms prfMsg_spec
#print axioms hmsg_spec
#print axioms skPrf_broken
#print axioms games_can_be_lost
#print axioms caps_pos

end MReduction
