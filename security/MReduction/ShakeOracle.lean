import MReduction.Shake
import MReduction.ShakeIdeal
import HashSig.SLHDSA.Security.ByteModel
import HashSig.SLHDSA.Security.RomConformance

/-! The single-oracle model's byte layouts use precisely the extracted implementation's
SHAKE256. All shorter outputs are prefixes of the same XOF stream. -/
namespace ShakeSecurity
set_option maxHeartbeats 800000
open SLHDSA SLHDSA.Security OracleComp OracleSpec MLink

private theorem squeeze_prefix (a : Spec.Keccak.State) (pos n m : Nat) (h : n ≤ m) :
    (Spec.Keccak.squeeze a pos m).take n = Spec.Keccak.squeeze a pos n := by
  induction n generalizing a pos m with
  | zero => rfl
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => simp only [Spec.Keccak.squeeze, List.take_succ_cons]; congr 1; exact ih _ _ _ (by omega)

def answer (S : Sha2Set) (x : List Byte) := hash (sp x) S.vp.params.m

private theorem hashPrefix (S : Sha2Set) (x : List Byte) :
    prefixBytes S.vp.params.n (answer S x) = hash (sp x) S.vp.params.n := by
  have h : S.vp.params.n ≤ S.vp.params.m := by cases S <;> decide
  apply Vector.toList_inj.mp
  rw [toList_prefixBytes_of_le h]
  change (cv (Spec.shake256 (sp x) S.vp.params.m)).take _ = cv (Spec.shake256 _ _)
  unfold cv
  rw [← List.map_take]
  exact congrArg _ (squeeze_prefix _ _ _ _ h)

private theorem flatten_nodes {n : Nat} (xs : List (Bytes n)) :
    sp (xs.map Vector.toList).flatten = nds xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sp (x.toList ++ (xs.map Vector.toList).flatten) = nd x ++ nds xs
    rw [sp_append, ih]
    rfl

theorem thash_layout (S : Sha2Set) (pk : S.Node) (key : Bytes 32) (xs : List S.Node) :
    prefixBytes S.vp.params.n (answer S (pk.toList ++ key.toList ++ (xs.map Vector.toList).flatten)) =
      (prims S).Thash pk key xs := by
  rw [hashPrefix]
  apply congrArg (fun b => hash b _)
  rw [sp_append, sp_append, flatten_nodes]
  rfl

theorem hmsg_layout (S : Sha2Set) (r pk root : S.Node) (msg : List Byte) :
    answer S (r.toList ++ pk.toList ++ root.toList ++ msg) = (prims S).Hmsg r pk root msg := by
  apply congrArg (fun b => hash b _)
  simp only [sp_append]
  rfl

theorem prfmsg_layout (S : Sha2Set) (sk rand : S.Node) (msg : List Byte) :
    prefixBytes S.vp.params.n (answer S (sk.toList ++ rand.toList ++ msg)) =
      (prims S).PRFmsg sk rand msg := by
  rw [hashPrefix]
  apply congrArg (fun b => hash b _)
  simp only [sp_append]
  rfl

theorem answer_layout (S : Sha2Set) :
    unifFwdAnswerImpl (answer S) ∘ₛ ShakeIdeal.SLHDSA.Security.encImpl S.vp =
      unifFwdAnswerImpl (romAnswer (prims S)) := by
  funext t
  rcases t with n | (q | q)
  · simp [ShakeIdeal.SLHDSA.Security.encImpl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_left]
    rfl
  · cases q with
    | thash pk key xs =>
      simp only [QueryImpl.apply_compose, ShakeIdeal.SLHDSA.Security.encImpl, ShakeIdeal.SLHDSA.Security.encHashImpl, unifFwdAnswerImpl,
        QueryImpl.add_apply_inr]
      change prefixBytes _ <$> (pure _ : ProbComp _) = (pure _ : ProbComp _)
      rw [map_pure]
      exact congrArg pure (thash_layout S pk key xs)
    | hmsg r pk root msg =>
      simp only [QueryImpl.apply_compose, ShakeIdeal.SLHDSA.Security.encImpl, ShakeIdeal.SLHDSA.Security.encHashImpl, unifFwdAnswerImpl,
        QueryImpl.add_apply_inr]
      change (pure (answer S (r.toList ++ pk.toList ++ root.toList ++ msg)) : ProbComp _) = pure _
      exact congrArg pure (hmsg_layout S r pk root msg)
  · simp only [QueryImpl.apply_compose, ShakeIdeal.SLHDSA.Security.encImpl, ShakeIdeal.SLHDSA.Security.encHashImpl, unifFwdAnswerImpl,
      QueryImpl.add_apply_inr]
    change prefixBytes _ <$> (pure _ : ProbComp _) = (pure _ : ProbComp _)
    rw [map_pure]
    exact congrArg pure (prfmsg_layout S q.skPrf q.optRand q.msg)

theorem oracle_conformance (S : Sha2Set)
    (optRand : PublicKeyCore (prims S).core → ProbComp (prims S).core.Y)
    (pkSeedDist : ProbComp (prims S).core.PkSeed) :
    (ShakeIdeal.SLHDSA.Security.shakeRomScheme S.vp optRand pkSeedDist).map (simulateQ' (unifFwdAnswerImpl (answer S))) =
      internalAlg S.vp (prims S) optRand pkSeedDist := by
  have h := romScheme_map_romAnswer (vp := S.vp) (prims S) (Equiv.refl _)
    (fun pk sk a _ => by
      change hash (_ ++ nds [sk]) _ = hash _ _
      congr 2
      exact List.append_nil _) optRand pkSeedDist
  rw [← h, ← answer_layout]
  apply SignatureAlg.ext
  · exact (QueryImpl.simulateQ_compose _ _ _).symm
  · funext pk sk msg; exact (QueryImpl.simulateQ_compose _ _ _).symm
  · funext pk msg sig; exact (QueryImpl.simulateQ_compose _ _ _).symm

end ShakeSecurity
