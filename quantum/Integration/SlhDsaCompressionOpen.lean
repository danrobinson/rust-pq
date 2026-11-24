import Integration.SlhDsaCompressionMsgCost
import Integration.SlhDsaBridgeMachFors

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum
open Resources2
variable (S : Sha2Set) (f : RandFns S.vp.params)

private def dispatch (value : RandFns S.vp.params) :
    QueryImpl (publicHashSpec (randPrims f).core) Id
  | .thash pk a xs => value.thash pk a xs
  | .hmsg r pk root m => value.hmsg r pk root m

def hashPort (H : Input → Output) := dispatch S f (functions S (tablesOf H))

def hashCalls : (publicHashSpec (randPrims f).core).Domain → ℕ
  | .thash _ _ xs => thashCalls S xs.length
  | .hmsg _ _ _ m => hmsgCalls S m.length

theorem hashPort_cost (t : (publicHashSpec (randPrims f).core).Domain) :
    EvalCost (fun H => (pure (hashPort S f H t) : ProbComp _)) (hashCalls S f t) := by
  cases t with
  | thash pk a xs => exact thash_cost S pk a xs
  | hmsg r pk root m => exact hmsg_cost S r pk root m

private theorem dispatch_self : dispatch S f f = PublicHash.impl (randPrims f) := by
  funext q
  cases q <;> rfl

theorem hashPort_oracle (g : CompressionTables) : hashPort S (functions S g) (oracle g) =
    PublicHash.impl (randPrims (functions S g)) := by
  unfold hashPort
  exact (congrArg (fun g' => dispatch S (functions S g) (functions S g')) (tablesOf_oracle g)).trans
    (dispatch_self S (functions S g))

local notation "P₀" => randPrims f
def forsWeight : (Lazy.OSpec P₀ (forsG P₀)).Domain → ℕ
  | .inr (.inr (.inr t)) => hashCalls S f t
  | _ => 0

theorem forsOpen_cost (tbl : SecretTable S.vp P₀) (targets : List (Bytes 22 × S.Node))
    {α : Type} (P : OracleComp (Lazy.OSpec P₀ (forsG P₀)) α) (q : ℕ)
    (hq : WCount (forsWeight S f) P q) (s : List ℕ) :
    EvalCost (fun H => (simulateQ (fImpl (hashPort S f H) tbl targets) P).run s) q := by
  apply evalCost_simulateQ_run _ (forsWeight S f) _ P q hq s
  intro t st
  rcases t with n | op | addr | hash
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact EvalCost.const _
  · change EvalCost (fun H => (pure (hashPort S f H hash, st) : ProbComp _)) (hashCalls S f hash)
    simpa only [map_pure] using
      (hashPort_cost S f hash).map (fun z => (z,st))

private theorem countVector {κ α : Type} {sp : OracleSpec κ} (w : sp.Domain → ℕ) {k : ℕ}
    (f : Fin k → OracleComp sp α) (c : ℕ) (h : ∀ i, WCount w (f i) c) :
    WCount w (Vector.ofFnM f) (k*c) := by
  induction k with
  | zero => rw [Vector.ofFnM_zero]; exact wCount_pure ..
  | succ k ih =>
    rw [Vector.ofFnM_succ, Nat.succ_mul]
    refine WCount.bind (ih (fun i => f i.castSucc) fun i => h i.castSucc) fun xs => ?_
    simpa only [Nat.add_zero] using WCount.bind (h (Fin.last k)) (m := 0)
      (fun a => wCount_pure w (xs.push a) 0)

attribute [local instance] Lazy.openQ Lazy.closedQ
theorem forsAnswer_cost (tbl : SecretTable S.vp P₀) (targets : List (Bytes 22 × S.Node))
    (pk : PublicKeyCore (P₀).core) (ys : List S.Node) (opened : List (Adrs × ℕ)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore S.vp (P₀).core) (s : List ℕ) :
    EvalCost (fun H => (simulateQ (fImpl (hashPort S f H) tbl targets)
      (fAnswerO pk ys opened msg sig)).run s)
      (hmsgCalls S msg.length + S.vp.params.k * thashCalls S 1) := by
  apply forsOpen_cost
  unfold fAnswerO
  refine WCount.bind (wCount_liftM_query _ _ (le_refl (hmsgCalls S msg.length))) fun d => ?_
  rw [← Nat.add_zero (S.vp.params.k * thashCalls S 1)]
  refine WCount.bind (countVector (forsWeight S f) _ _ ?_) fun imgs => wCount_pure _ _ _
  intro i
  exact wCount_liftM_query (forsWeight S f) _ (le_refl (thashCalls S 1))

end Reduction.Compression
#print axioms Reduction.Compression.forsOpen_cost

#print axioms Reduction.Compression.forsAnswer_cost
