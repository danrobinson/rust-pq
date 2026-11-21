import Ideal.Core.SimLemmas
import Ideal.Sha.HmsgShape
import Ideal.Sha.HmacShape
import Reduction.Open.WithHash

/-!
# Hash queries as Merkle–Damgård chains of compression queries (generic part of the realisers)

The open programs of `Reduction/Open` evaluate `Thash` / `H_msg` only through queries to
`publicHashSpec Link.prims.core`.  Here such a query is interpreted by the program that issues
the compression queries of the SHA-256 evaluation:

* `thashC pk a xs` — the keyed chain of `primsG_Thash_shape` (`2 + (30 + 16·|xs|)/64` queries);
* `hmsgC R pk root M` — the two chains of `hmsg_shape` (`(|M| + 56)/64 + 3` queries);
* `prfMsgC k r M` — the HMAC evaluation of `msgPrf_shape` (`(|M| + 24)/64 + 4` queries);
* `hashC` — the handler of `publicHashSpec Link.prims.core` built from the first two;
* `chainImpl tbl` — the handler of an open program `Lazy.RSpec (hS St Blk) D V (publicHashSpec …)`
  whose game slot is a pass-through port for compression queries: uniform bits and port queries
  forwarded, secrets read from `tbl`, hash queries interpreted by `hashC`.

Correctness at a table `g`: `hashC_inst`, `chainImpl_inst` (answering the compression queries
with `g` gives `PublicHash.impl (withTH Link.prims Thash_g Hmsg_g)`, resp. `Lazy.tblImpl` of it
followed by `instImpl₀ g`).  Costs: `thashC_bound`, `hmsgC_bound`, `prfMsgC_bound`, `hashC_bound`.
Budget transfer: `qb_simulateQ_classes` (three weighted classes of source queries and a class of
forbidden ones).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize

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
def hashC : QueryImpl (publicHashSpec Link.prims.core) (OracleComp CSpec)
  | .thash pk a xs => thashC pk a xs
  | .hmsg R pk root M => hmsgC R pk root M

/-- The bundle with the core of `Link.prims` and the two public hash functions of the table `g`. -/
abbrev primsQ (g : CF St Blk) : Primitives Link.vp.params :=
  Reduction.Open.withTH Link.prims (thG g) (hmG g)


attribute [irreducible] thG hmG prfG pmG

set_option maxHeartbeats 100000 in
set_option diagnostics true in
set_option diagnostics.threshold 200 in
example (g : CF St Blk) : (primsQ g).core = Link.prims.core := rfl

set_option maxHeartbeats 20000 in
example (g : CF St Blk) (q : (publicHashSpec Link.prims.core).Domain) : (publicHashSpec Link.prims.core).Range q :=
  PublicHash.impl (primsQ g) q
end Ideal.Realize
