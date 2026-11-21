import Ideal.Core.SimLemmas
import Ideal.Sha.HmsgShape
import Ideal.Sha.HmacShape
import Reduction.Lazy.Open

/-!
# Hash queries as Merkle–Damgård chains of compression queries (generic part of the realisers)

**Reference core.**  The reduction adversaries at a table `g` live over `primsG (liftC g)`, whose
core contains `PRF_g`, `PRF_msg,g`.  The realisers work over ONE table-independent core `core₀`:
the carriers, `adrsToKey`, `yToBytes` of the 128s bundle, and trivial `PRF`, `PRF_msg`
(projections).  `R₀ T H` is the bundle with core `core₀` and public hash functions `T`, `H`;
`primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g)` holds by `rfl` (stated in
`Ideal/Realize/Tcr.lean`).  (`Link.prims.core` cannot serve as the reference core: the kernel,
comparing `X (primsG (liftC g)).core` with `X Link.prims.core`, first compares the two bundles
componentwise and runs into `sha256G (liftC g) … =?= sha256 …`, which it can only refute by
evaluating SHA-256 symbolically (deep recursion).  With `core₀` the comparison fails at once.)

The open programs of `Reduction/Open` evaluate `Thash` / `H_msg` only through queries to
`publicHashSpec core`.  Here such a query (at `core₀`) is interpreted by the program that issues
the compression queries of the SHA-256 evaluation:

* `thashC pk a xs` — the keyed chain of `primsG_Thash_shape` (`2 + (30 + 16·|xs|)/64` queries);
* `hmsgC R pk root M` — the two chains of `hmsg_shape` (`(|M| + 56)/64 + 3` queries);
* `prfMsgC k r M` — the HMAC evaluation of `msgPrf_shape` (`(|M| + 24)/64 + 4` queries);
* `hashC` — the handler of `publicHashSpec core₀` built from the first two;
* `chainImpl tbl` — the handler of an open program `Lazy.RSpec (hS St Blk) D V (publicHashSpec …)`
  whose game slot is a pass-through port for compression queries: uniform bits and port queries
  forwarded, secrets read from `tbl`, hash queries interpreted by `hashC`.

Correctness at a table `g`: `hashC_inst`, `chainImpl_inst` (answering the compression queries
with `g` gives `implTH (thG g) (hmG g)`, resp. `Lazy.tblImpl` of it followed by `instImpl₀ g`;
`impl_R₀`: `implTH T H` is `PublicHash.impl (R₀ T H)`).  Costs: `thashC_bound`, `hmsgC_bound`, `prfMsgC_bound`, `hashC_bound`.
Budget transfer: `qb_simulateQ_classes` (three weighted classes of source queries and a class of
forbidden ones).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize

/-! ## The reference core -/

/-- The table-independent reference core: carriers, address key and byte encoding of the 128s
bundle; `PRF`, `PRF_msg` are projections (they are never evaluated). -/
def core₀ : CorePrimitives Link.vp.params where
  PkSeed := Bytes 16
  SkSeed := Bytes 16
  SkPrf := Bytes 16
  Y := Bytes 16
  AdrsKey := Bytes 22
  adrsToKey := SLHDSA.Concrete.sha2AdrsKey
  PRF := fun pk _ _ => pk
  PRFmsg := fun k _ _ => k
  yToBytes := id

/-- The bundle with core `core₀` and public hash functions `T`, `H`. -/
@[reducible] def R₀ (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) : Primitives Link.vp.params :=
  { toCorePrimitives := core₀, Thash := T, Hmsg := H }

instance (priority := high) : SampleableType core₀.SkSeed :=
  inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.SkPrf :=
  inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.PkSeed :=
  inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : SampleableType core₀.Y :=
  inferInstanceAs (SampleableType (Bytes 16))
instance (priority := high) : DecidableEq core₀.Y := inferInstanceAs (DecidableEq (Bytes 16))
instance (priority := high) : DecidableEq core₀.PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
instance (priority := high) : DecidableEq core₀.SkPrf := inferInstanceAs (DecidableEq (Bytes 16))
instance (priority := high) : DecidableEq core₀.AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
instance (priority := high) : Inhabited core₀.Y := ⟨Vector.replicate 16 0⟩

/-- Dummy hash functions: the bundle `R₀ dT dH` is the one over which the table-independent
programs are written (they never evaluate `Thash`, `H_msg`). -/
def dT : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 := fun pk _ _ => pk
/-- See `dT`. -/
def dH : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30 := fun _ _ _ _ => Vector.replicate 30 0

/-- Uniform bits and compression queries. -/
abbrev CSpec := unifSpec + hS St Blk

/-- One compression query. -/
def cq (q : St × Blk) : OracleComp CSpec St := (liftM (CSpec.query (.inr q)) : OracleComp CSpec St)

/-- Merkle–Damgård iteration from a chaining value, as compression queries. -/
def foldQ (c : St) (bs : List Blk) : OracleComp CSpec St := bs.foldlM (fun c b => cq (c, b)) c

@[simp] theorem cq_inst (g : CF St Blk) (q : St × Blk) :
    simulateQ (instImpl₀ g) (cq q) = pure (g q) := by
  simp [cq]

theorem cq_bound (q : St × Blk) : IsQueryBoundP (cq q) (fun i => i.isRight = true) 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

@[simp] theorem foldQ_inst (g : CF St Blk) (c : St) (bs : List Blk) :
    simulateQ (instImpl₀ g) (foldQ c bs) = pure (mdFold g c bs) := by
  induction bs generalizing c with
  | nil => simp [foldQ, mdFold]
  | cons b bs ih =>
    have h : foldQ c (b :: bs) = cq (c, b) >>= fun c' => foldQ c' bs := by
      simp [foldQ, List.foldlM_cons]
    rw [h, simulateQ_bind, cq_inst, pure_bind, ih]
    rfl

theorem foldQ_bound (c : St) (bs : List Blk) :
    IsQueryBoundP (foldQ c bs) (fun i => i.isRight = true) bs.length := by
  induction bs generalizing c with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons b bs ih =>
    have h : foldQ c (b :: bs) = cq (c, b) >>= fun c' => foldQ c' bs := by
      simp [foldQ, List.foldlM_cons]
    rw [h]
    exact (isQueryBoundP_bind (cq_bound _) fun c' _ => ih c').mono (by simp; omega)

/-! ## The four hash functions over a table, at the `Bytes` carriers -/

/-- `Thash` over the table `g` (`(primsG (liftC g)).Thash`, with the carriers written out). -/
def thG (g : CF St Blk) : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16 :=
  sha2ThashG (liftC g) Link.vp.params

/-- `H_msg` over the table `g`. -/
def hmG (g : CF St Blk) : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30 :=
  sha2HmsgG (liftC g) Link.vp.params

/-- `PRF` over the table `g`. -/
def prfG (g : CF St Blk) : Bytes 16 → Bytes 16 → Adrs → Bytes 16 :=
  fun pkSeed skSeed address =>
    SLHDSA.Concrete.checkedNodeOrZero (sha2PRFCheckedG (liftC g) pkSeed skSeed address)

/-- `PRF_msg` over the table `g`. -/
def pmG (g : CF St Blk) : Bytes 16 → Bytes 16 → List Byte → Bytes 16 :=
  sha2PRFmsgG (liftC g)

theorem thG_shape (g : CF St Blk) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    thG g pk a xs = out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) :=
  primsG_Thash_shape g pk a xs

theorem hmG_shape (g : CF St Blk) (R pk root : Bytes 16) (M : List UInt8) :
    hmG g R pk root M =
      dig30 (mdFold g IV128 (oblocksH R pk (mdFold g IV128 (iblocksH R pk root M)))) :=
  hmsg_shape g R pk root M

theorem pmG_shape (g : CF St Blk) (k r : Bytes 16) (M : List UInt8) :
    pmG g k r M =
      out16 (g (g (IV128, okey k), oblock (mdFold g (g (IV128, ikey k)) (iblocks r M)))) :=
  msgPrf_shape g k r M

/-! ## `Thash` -/

/-- `Thash(pk, a, xs)` as compression queries. -/
def thashC (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) : OracleComp CSpec (Bytes 16) := do
  let cv ← cq (IV128, sb128 pk)
  let c ← cq (cv, (tblocks a xs).1)
  let c' ← foldQ c (tblocks a xs).2
  return out16 c'

theorem thashC_inst (g : CF St Blk) (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    simulateQ (instImpl₀ g) (thashC pk a xs) = pure (thG g pk a xs) := by
  rw [thG_shape]
  simp only [thashC, simulateQ_bind, cq_inst, pure_bind, foldQ_inst, simulateQ_pure, keyedChain]

/-- Compression queries of one `Thash` evaluation. -/
def thashCost (n : ℕ) : ℕ := 2 + (30 + 16 * n) / 64

theorem thashCost_mono {n m : ℕ} (h : n ≤ m) : thashCost n ≤ thashCost m := by
  unfold thashCost
  exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) _

theorem thashC_bound (pk : Bytes 16) (a : Bytes 22) (xs : List (Bytes 16)) :
    IsQueryBoundP (thashC pk a xs) (fun i => i.isRight = true) (thashCost xs.length) := by
  unfold thashC
  refine (isQueryBoundP_bind (cq_bound _) fun cv _ =>
    isQueryBoundP_bind (cq_bound _) fun c _ =>
      isQueryBoundP_bind (m := 0) (foldQ_bound c _) fun c' _ => isQueryBoundP_pure _ _ _).mono ?_
  rw [tblocks_snd_length]
  unfold thashCost
  omega

/-! ## `H_msg` -/

/-- `H_msg(R, pk, root, M)` as compression queries. -/
def hmsgC (R pk root : Bytes 16) (M : List UInt8) : OracleComp CSpec (Bytes 30) := do
  let s ← foldQ IV128 (iblocksH R pk root M)
  let s' ← foldQ IV128 (oblocksH R pk s)
  return dig30 s'

theorem hmsgC_inst (g : CF St Blk) (R pk root : Bytes 16) (M : List UInt8) :
    simulateQ (instImpl₀ g) (hmsgC R pk root M) = pure (hmG g R pk root M) := by
  rw [hmG_shape]
  simp only [hmsgC, simulateQ_bind, pure_bind, foldQ_inst, simulateQ_pure]

/-- Compression queries of one `H_msg` evaluation on a message of `n` bytes. -/
def hmsgCost (n : ℕ) : ℕ := (n + 56) / 64 + 3

theorem hmsgCost_mono {n m : ℕ} (h : n ≤ m) : hmsgCost n ≤ hmsgCost m := by
  unfold hmsgCost
  exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _

theorem hmsgC_bound (R pk root : Bytes 16) (M : List UInt8) :
    IsQueryBoundP (hmsgC R pk root M) (fun i => i.isRight = true) (hmsgCost M.length) := by
  unfold hmsgC
  have h2 : ∀ s : St, IsQueryBoundP (foldQ IV128 (oblocksH R pk s)) (fun i => i.isRight = true) 2 :=
    fun s => by simpa only [oblocksH_length] using foldQ_bound IV128 (oblocksH R pk s)
  refine (isQueryBoundP_bind (foldQ_bound IV128 (iblocksH R pk root M)) fun s _ =>
    isQueryBoundP_bind (m := 0) (h2 s) fun s' _ => isQueryBoundP_pure _ _ _).mono ?_
  rw [iblocksH_length]
  unfold hmsgCost
  omega

/-! ## `PRF_msg` (HMAC) -/

/-- `PRF_msg(k, r, M)` as compression queries. -/
def prfMsgC (k r : Bytes 16) (M : List UInt8) : OracleComp CSpec (Bytes 16) := do
  let ci ← cq (IV128, ikey k)
  let s ← foldQ ci (iblocks r M)
  let co ← cq (IV128, okey k)
  let s' ← cq (co, oblock s)
  return out16 s'

theorem prfMsgC_inst (g : CF St Blk) (k r : Bytes 16) (M : List UInt8) :
    simulateQ (instImpl₀ g) (prfMsgC k r M) = pure (pmG g k r M) := by
  rw [pmG_shape]
  simp only [prfMsgC, simulateQ_bind, cq_inst, pure_bind, foldQ_inst, simulateQ_pure]

/-- Compression queries of one `PRF_msg` evaluation on a message of `n` bytes. -/
def prfMsgCost (n : ℕ) : ℕ := (n + 24) / 64 + 4

theorem prfMsgC_bound (k r : Bytes 16) (M : List UInt8) :
    IsQueryBoundP (prfMsgC k r M) (fun i => i.isRight = true) (prfMsgCost M.length) := by
  unfold prfMsgC
  refine (isQueryBoundP_bind (cq_bound _) fun ci _ =>
    isQueryBoundP_bind (foldQ_bound ci _) fun s _ =>
      isQueryBoundP_bind (cq_bound _) fun co _ =>
        isQueryBoundP_bind (m := 0) (cq_bound _) fun s' _ => isQueryBoundP_pure _ _ _).mono ?_
  rw [iblocks_length]
  unfold prfMsgCost
  omega

/-! ## The handler of the public hash interface -/

/-- The public hash interface of the 128s core, interpreted by compression queries. -/
def hashC : QueryImpl (publicHashSpec core₀) (OracleComp CSpec)
  | .thash pk a xs => thashC pk a xs
  | .hmsg R pk root M => hmsgC R pk root M

/-- The public hash interface of the 128s core answered by two functions `T`, `H`. -/
def implTH (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :
    QueryImpl (publicHashSpec core₀) Id
  | .thash pk a xs => T pk a xs
  | .hmsg R pk root M => H R pk root M

/-- The interpreter of `R₀ T H` is `implTH T H`. -/
theorem impl_R₀ (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) :
    PublicHash.impl (R₀ T H) = implTH T H := by
  funext q
  cases q <;> rfl

/-- **Correctness of `hashC` at the table `g`.** -/
theorem hashC_inst (g : CF St Blk) (q : (publicHashSpec core₀).Domain) :
    simulateQ (instImpl₀ g) (hashC q) =
      pure (f := ProbComp) (α := (publicHashSpec core₀).Range q)
        (implTH (thG g) (hmG g) q) := by
  cases q with
  | thash pk a xs => exact thashC_inst g pk a xs
  | hmsg R pk root M => exact hmsgC_inst g R pk root M

/-- Compression queries of one hash query. -/
def hashCost : (publicHashSpec core₀).Domain → ℕ
  | .thash _ _ xs => thashCost xs.length
  | .hmsg _ _ _ M => hmsgCost M.length

theorem hashC_bound (q : (publicHashSpec core₀).Domain) :
    IsQueryBoundP (hashC q) (fun i => i.isRight = true) (hashCost q) := by
  cases q with
  | thash pk a xs => exact thashC_bound pk a xs
  | hmsg R pk root M => exact hmsgC_bound R pk root M

/-! ## Open programs with a compression port -/

section Port

variable {D V : Type}

/-- Interface of an open program whose game slot is a port for compression queries. -/
abbrev PSpecC (D V : Type) :=
  Reduction.Lazy.RSpec (hS St Blk) D V (publicHashSpec core₀)

/-- Interpretation of an open program with a compression port: uniform bits and port queries
are forwarded, secrets are read from `tbl`, hash queries are issued as chains of compression
queries. -/
def chainImpl (tbl : D → V) : QueryImpl (PSpecC D V) (OracleComp CSpec)
  | .inl n => (liftM (CSpec.query (.inl n)) : OracleComp CSpec _)
  | .inr (.inl q) => cq q
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr q)) => hashC q

/-- **Correctness of `chainImpl` at the table `g`**, for any hash answers `hI` that `hashC`
computes at `g` (in particular `implTH (thG g) (hmG g)`, `hashC_inst`): answering the compression
queries with `g` is the table interpretation with hash answers `hI`, followed by answering the
port queries with `g`. -/
theorem chainImpl_inst (g : CF St Blk) (hI : QueryImpl (publicHashSpec core₀) Id)
    (hH : ∀ q, simulateQ (instImpl₀ g) (hashC q) =
      pure (f := ProbComp) (α := (publicHashSpec core₀).Range q) (hI q))
    (tbl : D → V) {α : Type} (oa : OracleComp (PSpecC D V) α) :
    simulateQ (instImpl₀ g) (simulateQ (chainImpl tbl) oa) =
      simulateQ (instImpl₀ g)
        (simulateQ (Reduction.Lazy.tblImpl (gspec := hS St Blk) hI tbl) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    congr 1
    rcases t with n | q | d | q
    · rfl
    · simp [chainImpl, Reduction.Lazy.tblImpl, cq]
    · simp [chainImpl, Reduction.Lazy.tblImpl]
    · simp [chainImpl, Reduction.Lazy.tblImpl, hH]

end Port

/-! ## Budget transfer with weights -/

section Weighted

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α : Type}

private theorem step_arith {P : Prop} [Decidable P] {n c : ℕ} (h : ¬ P ∨ 0 < n) :
    (if P then c else 0) + (if P then n - 1 else n) * c = n * c := by
  by_cases hp : P
  · have hn : 0 < n := h.resolve_left (not_not.mpr hp)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [hp, Nat.succ_mul, Nat.add_comm]
  · simp [hp]

/-- **Weighted budget transfer.**  If `oa` makes no `p₀`-query, at most `nᵢ` `pᵢ`-queries
(`i = 1, 2, 3`), and the handler step at a query `t` outside `p₀` issues at most
`[p₁ t]·c₁ + [p₂ t]·c₂ + [p₃ t]·c₃` `q`-queries, then the simulation issues at most
`n₁·c₁ + n₂·c₂ + n₃·c₃` `q`-queries. -/
theorem qb_simulateQ_classes {p₀ p₁ p₂ p₃ : ι → Prop} [DecidablePred p₀] [DecidablePred p₁]
    [DecidablePred p₂] [DecidablePred p₃] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')} (c₁ c₂ c₃ : ℕ)
    (hstep : ∀ t, ¬ p₀ t → IsQueryBoundP (impl t) q
      ((if p₁ t then c₁ else 0) + (if p₂ t then c₂ else 0) + (if p₃ t then c₃ else 0)))
    {oa : OracleComp spec α} {n₁ n₂ n₃ : ℕ}
    (h0 : IsQueryBoundP oa p₀ 0) (h1 : IsQueryBoundP oa p₁ n₁) (h2 : IsQueryBoundP oa p₂ n₂)
    (h3 : IsQueryBoundP oa p₃ n₃) :
    IsQueryBoundP (simulateQ impl oa) q (n₁ * c₁ + n₂ * c₂ + n₃ * c₃) := by
  induction oa using OracleComp.inductionOn generalizing n₁ n₂ n₃ with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h0 h1 h2 h3
    have ht0 : ¬ p₀ t := h0.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    have hb := isQueryBoundP_bind (hstep t ht0) fun u _ =>
      ih u (by simpa [ht0] using h0.2 u) (h1.2 u) (h2.2 u) (h3.2 u)
    refine hb.mono (le_of_eq ?_)
    have e1 := step_arith (c := c₁) h1.1
    have e2 := step_arith (c := c₂) h2.1
    have e3 := step_arith (c := c₃) h3.1
    omega

/-- A program without `p`-queries, run through a stateful handler whose steps at non-`p`
queries issue no `q`-query, issues no `q`-query. -/
theorem qb_simulateQ_run_zero {σ : Type} {p : ι → Prop} [DecidablePred p] {q : ι' → Prop}
    [DecidablePred q] {impl : QueryImpl spec (StateT σ (OracleComp spec'))}
    (hstep : ∀ t, ¬ p t → ∀ s, IsQueryBoundP ((impl t).run s) q 0)
    {oa : OracleComp spec α} (h : IsQueryBoundP oa p 0) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ p t := h.1.resolve_right (Nat.lt_irrefl 0)
    rw [simulateQ_query_bind, StateT.run_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, monadLift_self, id_eq]
    exact isQueryBoundP_bind_zero _ _ (hstep t ht s) fun u =>
      ih u.1 (by simpa [ht] using h.2 u.1) u.2

/-- Stateless version of `qb_simulateQ_run_zero`. -/
theorem qb_simulateQ_zero {p : ι → Prop} [DecidablePred p] {q : ι' → Prop}
    [DecidablePred q] {impl : QueryImpl spec (OracleComp spec')}
    (hstep : ∀ t, ¬ p t → IsQueryBoundP (impl t) q 0)
    {oa : OracleComp spec α} (h : IsQueryBoundP oa p 0) :
    IsQueryBoundP (simulateQ impl oa) q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ p t := h.1.resolve_right (Nat.lt_irrefl 0)
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    exact isQueryBoundP_bind_zero _ _ (hstep t ht) fun u => ih u (by simpa [ht] using h.2 u)

end Weighted

end Ideal.Realize

#print axioms Ideal.Realize.thashC_inst
#print axioms Ideal.Realize.hmsgC_inst
#print axioms Ideal.Realize.prfMsgC_inst
#print axioms Ideal.Realize.hashC_inst
#print axioms Ideal.Realize.hashC_bound
#print axioms Ideal.Realize.chainImpl_inst
#print axioms Ideal.Realize.qb_simulateQ_classes
#print axioms Ideal.Realize.qb_simulateQ_run_zero
#print axioms Ideal.Realize.qb_simulateQ_zero
#print axioms Ideal.Realize.impl_R₀
