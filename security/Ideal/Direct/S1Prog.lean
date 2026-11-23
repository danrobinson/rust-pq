import Ideal.Direct.RomGhost
import Ideal.Direct.S1Disc

/-!
# S1, part 2: every honest query of the tagged program is relevant for the run's key
(`status/DIRECT.md` §13.1 (S1), §14)

**S1** of §13.1: every `Thash` query of key generation, signing and verification has
`ps = PK.seed` and `|xs| = arityOf (adrsToKey a)`; every `H_msg` query has
`(ps, pr) = (PK.seed, PK.root)`; every PRF query is at `PK.seed`, and its walk is the arity-1
`Thash` walk.  Proved here:

* `rq_arity`: a role-correct query (`S1.RQ`, the conclusion of the address discipline of
  `S1Disc.lean`) has the arity `arityOf` of its key (the ledger addresses lie in the SHA-2
  checked domain, so the key is `ADRSc`, whose type byte and tree-height word give the arity);
* `prf_arity`, `prf_walk`: every PRF input (`Dsk`) is at an address of arity 1, and its walk
  `[sb128 ps, blk128 a k]` is the `Thash` walk of `(ps, a, [k])`;
* `HonOk pk`: the per-query statement of S1 for the tagged interface `QT Dsk` (coins: no
  condition; port queries: tagged with `pk`; PRF queries: at `pk.pkSeed`; `Thash`: at
  `pk.pkSeed` with the arity of its key; `H_msg`: at `(pk.pkSeed, pk.pkRoot)`; `PRF_msg`: no
  condition);
* **`s1_trace`**: for every stateful handler `J` of `QT Dsk` and every state predicate
  `Rec pk` that `J` preserves on `HonOk pk` queries and that holds initially for every `pk`,
  every final state of a run of `PprfST` (resp. `PprfET`) satisfies `Rec pk` for some `pk`.
  The key `pk = (PK.seed, PK.root)` is the one the program samples and computes; it is not known
  before key generation, so S1 is a pathwise statement with the key chosen along the path:
  the `PK.seed` sample, then key generation (whose queries are `HonOk ⟨ps, r⟩` for every `r`),
  then the rest (`HonOk ⟨ps, root⟩`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf Reduction Reduction.Open SLHDSA.Concrete
open Ideal.Realize.Msg (Rd mainC optRand₀ harnP)

/-! ## The arity of a role-correct query -/

theorem key_bytes (a : Adrs) (hd : Sha2Domain a) :
    (sha2AdrsKey a)[9] = UInt8.ofNat a.type ∧
    (sha2AdrsKey a)[14] = UInt8.ofNat (a.word2 / 16777216 % 256) ∧
    (sha2AdrsKey a)[15] = UInt8.ofNat (a.word2 / 65536 % 256) ∧
    (sha2AdrsKey a)[16] = UInt8.ofNat (a.word2 / 256 % 256) ∧
    (sha2AdrsKey a)[17] = UInt8.ofNat (a.word2 % 256) := by
  obtain ⟨hc, hl, ht⟩ := hd
  rw [sha2AdrsKey_eq_compressed a hc hl ht]
  have hty' : a.type < 256 := by
    have := Adrs.fits_one_type_of_isCanonical hc
    rw [Adrs.fits_iff] at this; simpa using this
  simp [Adrs.compressSha2, Adrs.toBytesBE, toByte, VCVio.Algorithms.Encoding.natToBytesBE,
    List.range_succ, Nat.mod_eq_of_lt hty']

theorem key9 (a : Adrs) (hd : Sha2Domain a) : (sha2AdrsKey a)[9].toNat = a.type := by
  have hty' : a.type < 256 := by
    have := Adrs.fits_one_type_of_isCanonical hd.1
    rw [Adrs.fits_iff] at this; simpa using this
  rw [(key_bytes a hd).1]
  simp [Nat.mod_eq_of_lt hty']

theorem arityOf_t0 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 0) :
    arityOf (sha2AdrsKey a) = 1 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_t1 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 1) :
    arityOf (sha2AdrsKey a) = 35 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_t2 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 2) :
    arityOf (sha2AdrsKey a) = 2 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_t4 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 4) :
    arityOf (sha2AdrsKey a) = 14 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_t5 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 5) :
    arityOf (sha2AdrsKey a) = 1 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_t6 (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 6) :
    arityOf (sha2AdrsKey a) = 1 := by
  have h := (key9 a hd).trans ht; unfold arityOf; rw [h]; rfl

theorem arityOf_forsTree (a : Adrs) (hd : Sha2Domain a) (ht : a.type = 3) :
    arityOf (sha2AdrsKey a) = if a.word2 = 0 then 1 else 2 := by
  obtain ⟨-, -, -, -, hw2, -⟩ := Adrs.fits_of_isCanonical a hd.1
  rw [Adrs.fits_iff] at hw2
  obtain ⟨-, h14, h15, h16, h17⟩ := key_bytes a hd
  have h := (key9 a hd).trans ht
  unfold arityOf
  rw [h, h14, h15, h16, h17]
  have e : ∀ n : ℕ, (UInt8.ofNat n = 0) ↔ n % 256 = 0 := by
    intro n
    constructor
    · intro h; have := congrArg UInt8.toNat h; simpa using this
    · intro h; apply UInt8.toNat_inj.1; simpa using h
  simp only [e]
  split_ifs <;> omega

/-- The address bounds of SLH-DSA-SHA2-128s. -/
theorem hb128 : ApprovedAddressBounds Link.vp.params := fipsApprovedAddressBounds Link.S128

theorem dom_of_facts {a : Adrs} (h : AddressFacts Link.vp a) : Sha2Domain a :=
  sha2Domain_of_addressFacts hb128 h

/-- **The arity of a role-correct query** (S1 at the level of one query). -/
theorem rq_arity {ps ps' : Bytes 16} {key : Bytes 22} {xs : List (Bytes 16)}
    (h : S1.RQ Link.vp Cr ps (.thash ps' key xs)) : ps' = ps ∧ xs.length = arityOf key := by
  obtain ⟨rfl, a, rfl, hr⟩ := h
  refine ⟨rfl, ?_⟩
  have hc := hb128.toCanonicalAddressBounds
  show xs.length = arityOf (sha2AdrsKey a)
  rcases hr with ⟨hF | hF, hl⟩ | ⟨hH | hH, hl⟩ | ⟨hT, hl⟩ | ⟨hT, hl⟩
  · rw [arityOf_t0 a (dom_of_facts (addressFacts_wotsStepAddresses Link.vp hc a hF))
      (type_of_mem_wotsStepAddresses Link.vp hF)]
    exact hl
  · rw [arityOf_forsTree a (dom_of_facts (addressFacts_forsLeafAddresses Link.vp hc a hF))
      (type_of_mem_forsLeafAddresses Link.vp hF), word2_of_mem_forsLeafAddresses Link.vp hF]
    exact hl
  · rw [arityOf_t2 a (dom_of_facts (addressFacts_xmssNodeAddresses Link.vp hc a hH))
      (type_of_mem_xmssNodeAddresses Link.vp hH)]
    exact hl
  · rw [arityOf_forsTree a (dom_of_facts (addressFacts_forsTreeAddresses Link.vp hc a hH))
      (type_of_mem_forsTreeAddresses Link.vp hH)]
    have hw := Nat.pos_iff_ne_zero.1 (word2_pos_of_mem_forsTreeAddresses Link.vp hH)
    simp only [hw, ↓reduceIte]
    exact hl
  · rw [arityOf_t1 a (dom_of_facts (addressFacts_wotsPkAddresses Link.vp hc a hT))
      (type_of_mem_wotsPkAddresses Link.vp hT)]
    exact hl
  · rw [arityOf_t4 a (dom_of_facts (addressFacts_forsRootAddresses Link.vp hc a hT))
      (type_of_mem_forsRootAddresses Link.vp hT)]
    exact hl

/-- **Every PRF input is at an address of arity 1** (a secret-key address of the parameter
set: type `WOTS_PRF` or `FORS_PRF`, in the checked domain). -/
theorem prf_arity (d : Dsk) : arityOf (Cr.adrsToKey d.2.val) = 1 := by
  have hd := dom_of_facts (SkDom.addressFacts d.2.property)
  rcases d.2.property.2.1 with h | h
  · exact arityOf_t5 _ hd h
  · exact arityOf_t6 _ hd h

/-- **The PRF walk is the arity-1 `Thash` walk.** -/
theorem prf_walk (d : Dsk) (k : Bytes 16) :
    [sb128 d.1, blk128 d.2 k] =
      sb128 d.1 :: (tblocks (Cr.adrsToKey d.2.val) [k]).1 :: (tblocks (Cr.adrsToKey d.2.val) [k]).2 := by
  show [sb128 d.1, blk128 d.2 k] = sb128 d.1 :: (tblocks (sha2AdrsKey d.2.val) [k]).1 ::
    (tblocks (sha2AdrsKey d.2.val) [k]).2
  rw [tblocks_snd_of_length_one _ _ rfl]
  rfl

/-! ## The per-query statement of S1 -/

/-- A hash query relevant for `pk`, as far as the honest party is concerned. -/
def HashOk (pk : PublicKeyCore Cr) : (publicHashSpec Cr).Domain → Prop
  | .thash ps key xs => ps = pk.pkSeed ∧ xs.length = arityOf key
  | .hmsg _ ps pr _ => ps = pk.pkSeed ∧ pr = pk.pkRoot

/-- **S1, per query, on the tagged interface over the open PRF domain.** -/
def HonOk0 (pk : PublicKeyCore Cr) : (QT (D₀ Rd)).Domain → Prop
  | .inl _ => True
  | .inr (.inl (.inl pq)) => pq.1 = pk
  | .inr (.inl (.inr d)) => d.1 = pk.pkSeed
  | .inr (.inr (.inl q)) => HashOk pk q
  | .inr (.inr (.inr _)) => True

/-- **S1, per query, on the tagged interface `QT Dsk`** (the interface of `PprfST`). -/
def HonOk (pk : PublicKeyCore Cr) : (QT Dsk).Domain → Prop
  | .inl _ => True
  | .inr (.inl (.inl pq)) => pq.1 = pk
  | .inr (.inl (.inr d)) => d.1 = pk.pkSeed
  | .inr (.inr (.inl q)) => HashOk pk q
  | .inr (.inr (.inr _)) => True

/-! ## Generic transport lemmas -/

section Generic

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}

theorem allQ_simulateQ (impl : QueryImpl spec (OracleComp spec')) {P : ι → Prop}
    {P' : ι' → Prop} (h : ∀ t, P t → AllQueriesSatisfy (impl t) P') {α : Type}
    (oa : OracleComp spec α) (hoa : AllQueriesSatisfy oa P) :
    AllQueriesSatisfy (simulateQ impl oa) P' := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    rw [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (h t hoa.1) fun u => ih u (hoa.2 u)

theorem allQ_simulateQ_run {σ : Type} (G : QueryImpl spec (StateT σ (OracleComp spec')))
    {P' : ι' → Prop} (h : ∀ t s, AllQueriesSatisfy ((G t).run s) P') {α : Type}
    (oa : OracleComp spec α) (s : σ) :
    AllQueriesSatisfy ((simulateQ G oa).run s) P' := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (h t s) fun z => ih z.1 z.2

theorem allQ_liftM {P : ℕ ⊕ ι → Prop} (hP : ∀ n, P (.inl n)) {α : Type} (ob : ProbComp α) :
    AllQueriesSatisfy (liftM ob : OracleComp (unifSpec + spec) α) P := by
  induction ob using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    rw [liftM_bind]
    refine allQueriesSatisfy_bind ?_ fun u => ih u
    exact (allQueriesSatisfy_query_iff (spec := unifSpec + spec) (.inl n) P).2 (hP n)

/-- **Support invariance along a run whose queries all satisfy `P`.** -/
theorem supp_inv_of_allQ {σ : Type} (J : QueryImpl spec (StateT σ ProbComp)) {P : ι → Prop}
    {I : σ → Prop} (hstep : ∀ t s, P t → I s → ∀ z ∈ support ((J t).run s), I z.2)
    {α : Type} (oa : OracleComp spec α) (hoa : AllQueriesSatisfy oa P) (s : σ) (hs : I s) :
    ∀ z ∈ support ((simulateQ J oa).run s), I z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hs
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    intro z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact ih w.1 (hoa.2 w.1) w.2 (hstep t s hoa.1 hs w hw) z hz

end Generic

/-! ## The honest programs -/

/-- The open PRF interface of the honest programs. -/
abbrev PS0 := Reduction.Open.PSpec Rd (D₀ Rd)

/-- S1 per query on the open PRF interface `PS0`. -/
def POk (pk : PublicKeyCore Cr) : (PS0).Domain → Prop
  | .inl _ => True
  | .inr (.inl d) => d.1 = pk.pkSeed
  | .inr (.inr (.inl q)) => HashOk pk q
  | .inr (.inr (.inr _)) => True

theorem hashOk_of_rq {pk : PublicKeyCore Cr} {q : (publicHashSpec Cr).Domain}
    (h : S1.RQ Link.vp Cr pk.pkSeed q) : HashOk pk q := by
  rcases q with ⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩
  · exact rq_arity h
  · exact h.elim

section Honest

attribute [local instance] openQ

variable (pk : PublicKeyCore Cr)

theorem pOk_hq (q : (publicHashSpec Rd.core).Domain) (h : S1.RQ Link.vp Rd.core pk.pkSeed q) :
    AllQueriesSatisfy (HasQuery.query (spec := publicHashSpec Rd.core) q :
      OracleComp (PS0) _) (POk pk) :=
  (allQueriesSatisfy_query_iff (spec := PS0) (.inr (.inr (.inl q))) _).2
    (hashOk_of_rq h)

theorem pOk_secret (a : Adrs) :
    AllQueriesSatisfy (gameQ Rd (pk.pkSeed, a) : OracleComp (PS0) _) (POk pk) :=
  (allQueriesSatisfy_query_iff (spec := PS0) (.inr (.inl (pk.pkSeed, a))) _).2 rfl

/-- **Key generation (S1)**: at the public seed `ps`, for every root `r`. -/
theorem keygen_pOk (ps r : Bytes 16) :
    AllQueriesSatisfy (openKeygenP Rd ps) (POk ⟨ps, r⟩) :=
  S1.keygen_ok (fun oa => AllQueriesSatisfy oa (POk ⟨ps, r⟩))
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
    Rd.core ps (pOk_hq ⟨ps, r⟩) (pOk_secret ⟨ps, r⟩)

/-- **Signing (S1).** -/
theorem sign_pOk (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (skPrf : Bytes 16)
    (m : List Byte) :
    AllQueriesSatisfy (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m) (POk pk) := by
  unfold openSignP
  refine allQueriesSatisfy_bind (allQ_liftM (fun _ => trivial) _) fun addrnd => ?_
  refine allQueriesSatisfy_bind ?_ fun R => ?_
  · exact (allQueriesSatisfy_query_iff (spec := PS0) (.inr (.inr (.inr _))) _).2
      trivial
  · unfold openSignCoreP
    exact S1.sign_ok (fun oa => AllQueriesSatisfy oa (POk pk))
      (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
      Rd.core pk.pkSeed (pOk_hq pk) (pOk_secret pk) m pk.pkRoot R
      ((allQueriesSatisfy_query_iff (spec := PS0) (.inr (.inr (.inl _))) _).2
        ⟨rfl, rfl⟩)

end Honest

/-- **Verification (S1)**: every query of verification against `pk`, of any signature, is
relevant for `pk`. -/
theorem verify_hashOk (pk : PublicKeyCore Cr) (m : List Byte)
    (sig : GeneralScheme.SignatureCore Link.vp Rd.core) :
    AllQueriesSatisfy (GeneralScheme.verifyInternalM Link.vp Rd.core m sig pk :
      OracleComp (publicHashSpec Rd.core) Bool) (HashOk pk) :=
  S1.verify_ok (fun oa => AllQueriesSatisfy oa (HashOk pk))
    (fun x => allQueriesSatisfy_pure x _) (fun _ _ h1 h2 => allQueriesSatisfy_bind h1 h2)
    Rd.core pk (fun q h => (allQueriesSatisfy_query_iff (spec := publicHashSpec Rd.core) q _).2
      (hashOk_of_rq h)) m sig
    ((allQueriesSatisfy_query_iff (spec := publicHashSpec Rd.core) _ _).2 ⟨rfl, rfl⟩)

/-! ## Through the embeddings -/

theorem embQT_ok (pk : PublicKeyCore Cr) (t : (PS0).Domain) (h : POk pk t) :
    AllQueriesSatisfy (embQT (D := D₀ Rd) t) (HonOk0 pk) := by
  rcases t with n | d | q
  · exact (allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inl n) _).2 trivial
  · exact (allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inr (.inl (.inr d))) _).2 h
  · exact (allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inr (.inr q)) _).2 (by
      rcases q with q | q
      · exact h
      · trivial)

theorem hashEmb_ok (pk : PublicKeyCore Cr) (q : (publicHashSpec Rd.core).Domain)
    (h : HashOk pk q) : AllQueriesSatisfy (hashEmb Rd (D₀ Rd) q) (POk pk) :=
  (allQueriesSatisfy_query_iff (spec := PS0) (.inr (.inr (.inl q))) _).2 h

theorem restrictPT_ok (pk : PublicKeyCore Cr) (t : (QT (D₀ Rd)).Domain) (h : HonOk0 pk t) :
    AllQueriesSatisfy (restrictPT (D' := Dsk) (skRestrict Link.vp Rd) t) (HonOk pk) := by
  rcases t with n | (pq | d) | q
  · exact (allQueriesSatisfy_query_iff (spec := QT Dsk) (.inl n) _).2 trivial
  · exact (allQueriesSatisfy_query_iff (spec := QT Dsk) (.inr (.inl (.inl pq))) _).2 h
  · cases hr : skRestrict Link.vp Rd d with
    | none => simp only [restrictPT, hr]; exact allQueriesSatisfy_pure _ _
    | some d' =>
      simp only [restrictPT, hr]
      have e : d'.1 = d.1 := by
        unfold skRestrict at hr
        split_ifs at hr
        cases hr
        rfl
      exact (allQueriesSatisfy_query_iff (spec := QT Dsk) (.inr (.inl (.inr d'))) _).2
        (e.trans h)
  · exact (allQueriesSatisfy_query_iff (spec := QT Dsk) (.inr (.inr q)) _).2 (by
      rcases q with q | q
      · exact h
      · trivial)

/-! ## The tagged programs -/

section Programs

variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))

theorem harnS_ok (pk : PublicKeyCore Cr) (skPrf : Bytes 16)
    (t : (FSpecP (GeneralScheme.SignatureCore Link.vp Rd.core)).Domain) (s : SigLog Link.vp Rd) :
    AllQueriesSatisfy ((harnP (portQT (D := D₀ Rd) pk) (sigSignOracle (fun m => simulateQ embQT
      (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))) t).run s) (HonOk0 pk) := by
  rcases t with n | q | m
  · simp only [harnP, StateT.run_monadLift]
    exact allQueriesSatisfy_bind
      ((allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inl n) _).2 trivial)
      fun _ => allQueriesSatisfy_pure _ _
  · simp only [harnP, StateT.run_monadLift]
    exact allQueriesSatisfy_bind
      ((allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inr (.inl (.inl (pk, q)))) _).2 rfl)
      fun _ => allQueriesSatisfy_pure _ _
  · simp only [harnP, sigSignOracle, run_appendLog_apply]
    exact allQueriesSatisfy_bind
      (allQ_simulateQ embQT (embQT_ok pk) _ (sign_pOk pk oR skPrf m))
      fun _ => allQueriesSatisfy_pure _ _

theorem harnE_ok (pk : PublicKeyCore Cr) (skPrf : Bytes 16)
    (t : (FSpecP (GeneralScheme.SignatureCore Link.vp Rd.core)).Domain) (s : List (List Byte)) :
    AllQueriesSatisfy ((harnP (portQT (D := D₀ Rd) pk)
      (harnessSignOracle (vp := Link.vp) (prims := Rd) (fun m => simulateQ embQT
        (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))) t).run s) (HonOk0 pk) := by
  rcases t with n | q | m
  · simp only [harnP, StateT.run_monadLift]
    exact allQueriesSatisfy_bind
      ((allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inl n) _).2 trivial)
      fun _ => allQueriesSatisfy_pure _ _
  · simp only [harnP, StateT.run_monadLift]
    exact allQueriesSatisfy_bind
      ((allQueriesSatisfy_query_iff (spec := QT (D₀ Rd)) (.inr (.inl (.inl (pk, q)))) _).2 rfl)
      fun _ => allQueriesSatisfy_pure _ _
  · simp only [harnP, harnessSignOracle, StateT.run_bind, StateT.run_monadLift, bind_assoc,
      StateT.run_modify, StateT.run_pure, pure_bind]
    exact allQueriesSatisfy_bind
      (allQ_simulateQ embQT (embQT_ok pk) _ (sign_pOk pk oR skPrf m))
      fun _ => allQueriesSatisfy_pure _ _

/-- Everything the tagged SUF program does after key generation, at the key `pk`. -/
theorem restS_ok (mainP : PortForgerProg Link.vp Rd) (pk : PublicKeyCore Cr) (skPrf : Bytes 16) :
    AllQueriesSatisfy ((simulateQ (harnP (portQT pk)
        (sigSignOracle (fun m => simulateQ embQT
          (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))))
          (mainP pk)).run [] >>= fun z =>
        simulateQ embQT (simulateQ (hashEmb Rd (D₀ Rd)) (sufCheckOpen pk z.1 z.2)))
      (HonOk0 pk) := by
  refine allQueriesSatisfy_bind (allQ_simulateQ_run _ (harnS_ok oR pk skPrf) _ _) fun z => ?_
  refine allQ_simulateQ embQT (embQT_ok pk) _ (allQ_simulateQ _ (hashEmb_ok pk) _ ?_)
  exact allQueriesSatisfy_bind (verify_hashOk pk _ _) fun _ => allQueriesSatisfy_pure _ _

/-- Everything the tagged EUF program does after key generation, at the key `pk`. -/
theorem restE_ok (mainP : PortForgerProg Link.vp Rd) (pk : PublicKeyCore Cr) (skPrf : Bytes 16) :
    AllQueriesSatisfy ((simulateQ (harnP (portQT pk)
        (harnessSignOracle (vp := Link.vp) (prims := Rd)
          (fun m => simulateQ embQT (openSignP (prims := Rd) (optRand₀ oR) pk skPrf m))))
          (mainP pk)).run [] >>= fun z =>
        simulateQ embQT (simulateQ (hashEmb Rd (D₀ Rd))
          (GeneralScheme.verifyInternalM Link.vp Rd.core z.1.1 z.1.2 pk :
            OracleComp (publicHashSpec Rd.core) Bool)) >>= fun v =>
          pure (decide (z.1.1 ∉ z.2) && v))
      (HonOk0 pk) := by
  refine allQueriesSatisfy_bind (allQ_simulateQ_run _ (harnE_ok oR pk skPrf) _ _) fun z => ?_
  refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_pure _ _
  exact allQ_simulateQ embQT (embQT_ok pk) _ (allQ_simulateQ _ (hashEmb_ok pk) _
    (verify_hashOk pk _ _))

theorem keygenT_ok (ps r : Bytes 16) :
    AllQueriesSatisfy (simulateQ embQT (openKeygenP Rd ps)) (HonOk0 ⟨ps, r⟩) :=
  allQ_simulateQ embQT (embQT_ok ⟨ps, r⟩) _ (keygen_pOk ps r)

/-- A run of a stateful handler keeps a family of invariants `Rec pk`, `pk ∈ K`, along a program
all of whose queries are `HonOk pk` for every `pk ∈ K`. -/
theorem supp_family {σ : Type} (J : QueryImpl (QT Dsk) (StateT σ ProbComp))
    (Rec : PublicKeyCore Cr → σ → Prop)
    (hstep : ∀ pk t s, HonOk pk t → Rec pk s → ∀ z ∈ support ((J t).run s), Rec pk z.2)
    (K : PublicKeyCore Cr → Prop) {α : Type} (oa : OracleComp (QT (D₀ Rd)) α)
    (hoa : ∀ pk, K pk → AllQueriesSatisfy oa (HonOk0 pk)) (s : σ) (hs : ∀ pk, K pk → Rec pk s) :
    ∀ z ∈ support ((simulateQ J (simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd)) oa)).run s),
      ∀ pk, K pk → Rec pk z.2 :=
  fun z hz pk hk => supp_inv_of_allQ J (fun t s ht hs' => hstep pk t s ht hs')
    _ (allQ_simulateQ _ (restrictPT_ok pk) _ (hoa pk hk)) s (hs pk hk) z hz

theorem supp_bind_run {σ α β : Type} (J : QueryImpl (QT Dsk) (StateT σ ProbComp))
    (oa : OracleComp (QT (D₀ Rd)) α) (ob : α → OracleComp (QT (D₀ Rd)) β) (s : σ) {z : β × σ}
    (hz : z ∈ support ((simulateQ J (simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd))
      (oa >>= ob))).run s)) :
    ∃ w ∈ support ((simulateQ J (simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd)) oa)).run s),
      z ∈ support ((simulateQ J (simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd)) (ob w.1))).run
        w.2) := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  exact hz

/-- **S1 for the tagged SUF program** (pathwise, with the key chosen along the path). -/
theorem s1_trace_S (S : ForgerI) {σ : Type} (J : QueryImpl (QT Dsk) (StateT σ ProbComp))
    (Rec : PublicKeyCore Cr → σ → Prop)
    (hstep : ∀ pk t s, HonOk pk t → Rec pk s → ∀ z ∈ support ((J t).run s), Rec pk z.2)
    (s₀ : σ) (h₀ : ∀ pk, Rec pk s₀) :
    ∀ z ∈ support ((simulateQ J (PprfST oR pkSeedDist S)).run s₀), ∃ pk, Rec pk z.2 := by
  intro z hz
  unfold PprfST at hz
  obtain ⟨w₁, hw₁, hz⟩ := supp_bind_run J _ _ _ hz
  have h₁ := supp_family J Rec hstep (fun _ => True) _ (fun pk _ => allQ_liftM (fun _ => trivial) _)
    s₀ (fun pk _ => h₀ pk) w₁ hw₁
  unfold bRestWOpenPT at hz
  obtain ⟨w₂, hw₂, hz⟩ := supp_bind_run J _ _ _ hz
  have h₂ := supp_family J Rec hstep (fun _ => True) _ (fun pk _ => allQ_liftM (fun _ => trivial) _)
    w₁.2 h₁ w₂ hw₂
  obtain ⟨w₃, hw₃, hz⟩ := supp_bind_run J _ _ _ hz
  have h₃ := supp_family J Rec hstep (fun pk => pk.pkSeed = w₁.1) _
    (fun pk hpk => by rw [← hpk]; exact keygenT_ok pk.pkSeed pk.pkRoot) w₂.2
    (fun pk _ => h₂ pk trivial) w₃ hw₃
  refine ⟨⟨w₁.1, w₃.1⟩, ?_⟩
  exact supp_family J Rec hstep (fun pk => pk = ⟨w₁.1, w₃.1⟩) _
    (fun pk hpk => by rw [hpk]; exact restS_ok oR (mainC S) _ w₂.1) w₃.2
    (fun pk hpk => by rw [hpk]; exact h₃ _ rfl) z hz _ rfl

/-- **S1 for the tagged EUF program.** -/
theorem s1_trace_E (S : ForgerI) {σ : Type} (J : QueryImpl (QT Dsk) (StateT σ ProbComp))
    (Rec : PublicKeyCore Cr → σ → Prop)
    (hstep : ∀ pk t s, HonOk pk t → Rec pk s → ∀ z ∈ support ((J t).run s), Rec pk z.2)
    (s₀ : σ) (h₀ : ∀ pk, Rec pk s₀) :
    ∀ z ∈ support ((simulateQ J (PprfET oR pkSeedDist S)).run s₀), ∃ pk, Rec pk z.2 := by
  intro z hz
  unfold PprfET at hz
  obtain ⟨w₁, hw₁, hz⟩ := supp_bind_run J _ _ _ hz
  have h₁ := supp_family J Rec hstep (fun _ => True) _ (fun pk _ => allQ_liftM (fun _ => trivial) _)
    s₀ (fun pk _ => h₀ pk) w₁ hw₁
  unfold bRestOpenPT at hz
  obtain ⟨w₂, hw₂, hz⟩ := supp_bind_run J _ _ _ hz
  have h₂ := supp_family J Rec hstep (fun _ => True) _ (fun pk _ => allQ_liftM (fun _ => trivial) _)
    w₁.2 h₁ w₂ hw₂
  obtain ⟨w₃, hw₃, hz⟩ := supp_bind_run J _ _ _ hz
  have h₃ := supp_family J Rec hstep (fun pk => pk.pkSeed = w₁.1) _
    (fun pk hpk => by rw [← hpk]; exact keygenT_ok pk.pkSeed pk.pkRoot) w₂.2
    (fun pk _ => h₂ pk trivial) w₃ hw₃
  refine ⟨⟨w₁.1, w₃.1⟩, ?_⟩
  exact supp_family J Rec hstep (fun pk => pk = ⟨w₁.1, w₃.1⟩) _
    (fun pk hpk => by rw [hpk]; exact restE_ok oR (mainC S) _ w₂.1) w₃.2
    (fun pk hpk => by rw [hpk]; exact h₃ _ rfl) z hz _ rfl

end Programs

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.rq_arity
#print axioms Ideal.Direct.Rom.prf_arity
#print axioms Ideal.Direct.Rom.prf_walk
#print axioms Ideal.Direct.Rom.s1_trace_S
#print axioms Ideal.Direct.Rom.s1_trace_E
