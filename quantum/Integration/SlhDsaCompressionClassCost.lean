import Integration.SlhDsaCompressionWotsCost
import Integration.SlhDsaCompressionClassOne
namespace Reduction.Compression.ClassOne
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2
attribute [local instance] Lazy.openQ Lazy.closedQ
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f

theorem sign_cost (tbl : SecretTable S.vp P₀) (pk root R : S.Node) (msg : List Byte) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S f H) tbl) (Lazy.openSign P₀ []ₒ msg pk root R))
      (Lazy.signHashes S.vp * signMax S msg.length) := by
  apply openProgram_cost S f tbl _ _ _
  · exact (Lazy.openSign_kindBound (vp := S.vp) (prims := P₀) (gspec := []ₒ) .hash msg pk root R).mono (by simpa [Lazy.ind] using (Lazy.signB_hash (vp := S.vp)))
  · exact Realize.np_openSign (vp := S.vp) (prims := P₀) (gspec := []ₒ) (exceeds S f msg.length) msg pk root R (fun _ => Nat.not_lt_zero _)
      (okLength_cost S f msg.length pk) (show ¬signMax S msg.length < hmsgCalls S msg.length from not_lt_of_ge (le_max_right ..))

theorem tail_hashes (pkSeed : (P₀).PkSeed)
    (L : List ((P₀).AdrsKey × List (P₀).Y)) (root : (P₀).Y)
    (z : (List Byte × GeneralScheme.SignatureCore S.vp (P₀).core) ×
      G2Log P₀) :
    IsQueryBoundP (qmTail pkSeed L root z) (fun t ↦ Lazy.kind t = .hash)
      (1 + Resources2.verifyHashes S.vp * 2) := by
  have hver : ∀ (parts : DigestParts S.vp.params)
      (sig : GeneralScheme.SignatureCore S.vp (P₀).core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := []ₒ) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) (fun t ↦ Lazy.kind t = .hash)
        (Resources2.verifyHashes S.vp * 2) := fun parts sig ↦
    IsQueryBoundP.simulateQ_run_of_step_le (cost := 2) (q := fun t ↦ Lazy.kind t = .hash)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t _ s ↦ Resources2.collO_step_bound pkSeed L .hash t s)
      (fun t ht s ↦ absurd trivial ht) none
  have hmsg : ∀ (R root : (P₀).Y) (m : List Byte),
      IsQueryBoundP (PublicHash.hmsg (P₀).core R pkSeed root m :
        OracleComp (Lazy.OSpec P₀ []ₒ) (Bytes S.vp.params.m))
        (fun t ↦ Lazy.kind t = .hash) 1 :=
    fun R root m ↦ (isQueryBoundP_query_iff _ _ _).2 fun _ ↦ Nat.one_pos
  unfold qmTail
  exact Lazy.qb_bind _ (hmsg _ _ _) fun dg ↦
    Lazy.qb_bind _ (m := 0) (hver _ _) fun c ↦ isQueryBoundP_pure _ _ _

theorem stored_cost (L : ℕ) (pk : S.Node) (key : Bytes 22) (xs : List S.Node)
    (hx : xs.length ≤ S.vp.params.len) : ¬exceeds S f L (Realize.thIdx P₀ PEmpty pk key xs) := by
  change ¬signMax S L < thashCalls S xs.length
  have hlen : S.vp.params.len ≠ 1 := by cases S <;> decide +kernel
  by_cases one : xs.length = 1
  · rw [one]
    unfold signMax keygenMax
    omega
  · have hmul := Nat.mul_le_mul_left S.vp.params.n hx
    have le : thashCalls S xs.length ≤ thashCalls S S.vp.params.len := by
      by_cases hn : S.vp.params.n = 16 <;> simp [thashCalls,one,hlen,hn] at * <;> omega
    unfold signMax keygenMax
    omega

theorem tail_cost (tbl : SecretTable S.vp P₀) (pk root : S.Node) (log : List (Bytes 22 × List S.Node))
    (hl : ∀ x ∈ log, x.2.length ≤ S.vp.params.len)
    (z : (List Byte × GeneralScheme.SignatureCore S.vp (P₀).core) × G2Log P₀) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S f H) tbl) (qmTail pk log root z))
      ((1 + verifyHashes S.vp * 2) * signMax S z.1.1.length) := by
  apply openProgram_cost _ _ tbl _ _ _ (tail_hashes S f pk log root z)
  have hm : IsQueryBoundP (PublicHash.hmsg (P₀).core z.1.2.randomness pk root z.1.1 :
      OracleComp (Lazy.OSpec P₀ []ₒ) (Bytes S.vp.params.m)) (exceeds S f z.1.1.length) 0 :=
    (isQueryBoundP_query_iff _ _ _).2 fun ht => False.elim ((not_lt_of_ge (le_max_right ..)) ht)
  unfold qmTail
  refine isQueryBoundP_bind_zero _ _ hm fun dg =>
    isQueryBoundP_bind_zero _ _ (Realize.np_collO_run (vp := S.vp) (prims := P₀) (gspec := []ₒ) (exceeds S f z.1.1.length) pk log
      (okLength_cost S f _ pk) (fun x hx => stored_cost S f _ pk _ _ (hl x hx)) _ _ _) fun _ => by simp

end Reduction.Compression.ClassOne
#print axioms Reduction.Compression.ClassOne.tail_cost
#print axioms Reduction.Compression.ClassOne.sign_cost
