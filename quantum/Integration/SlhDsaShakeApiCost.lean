import Integration.SlhDsaShakeApiRaw
import Integration.SlhDsaBridgeMachItsr

namespace Reduction.ShakeApi
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum
variable (S : Sha2Set) (N : ℕ)

/-- Any evaluation of the finite raw SHAKE table costs at most one public query. -/
theorem read_cost {α : Type} (xs : List SLHDSA.Byte) (decode : Bytes S.vp.params.m → α) :
    EvalCost (fun H : RawTable S N => (pure (decode (extend H xs)) : ProbComp α)) 1 := by
  by_cases h : xs.length ≤ N
  · simpa only [extend,dite_eq_left h] using (EvalCost.eval (BList.ofList xs h) decode)
  · simpa only [extend,dite_eq_right h] using
      (EvalCost.const (X := Input N) (Y := Bytes S.vp.params.m) (pure (decode default))).mono (Nat.zero_le 1)

variable (base : Xof S)
local notation "P₀" => primitives S base

def hashPort (H : RawTable S N) : QueryImpl (publicHashSpec (P₀).core) Id
  | .thash pk a xs => (primitives S (extend H)).Thash pk a xs
  | .hmsg r pk root m => (primitives S (extend H)).Hmsg r pk root m

theorem hashPort_self (H : RawTable S N) :
    hashPort S N (extend H) H = PublicHash.impl (primitives S (extend H)) := by
  funext t
  cases t <;> rfl

theorem hash_cost (t : (publicHashSpec (P₀).core).Domain) :
    EvalCost (fun H => (pure (hashPort S N base H t) : ProbComp _)) 1 := by
  cases t with
  | thash pk a xs => exact read_cost S N _ (prefixBytes S.vp.params.n)
  | hmsg r pk root m => exact read_cost S N _ id

theorem prf_cost (pk sk : S.Node) (a : Adrs) :
    EvalCost (fun H : RawTable S N => (pure ((primitives S (extend H)).PRF pk sk a) : ProbComp _)) 1 :=
  read_cost S N _ (prefixBytes S.vp.params.n)

theorem prfmsg_cost (sk R : S.Node) (m : List SLHDSA.Byte) :
    EvalCost (fun H : RawTable S N => (pure ((primitives S (extend H)).PRFmsg sk R m) : ProbComp _)) 1 :=
  read_cost S N _ (prefixBytes S.vp.params.n)

theorem simulate_cost {α : Type} (tbl : SecretTable S.vp P₀)
    (P : OracleComp (Lazy.OSpec P₀ []ₒ) α) {q : ℕ} (hq : IsQueryBoundP P (fun t => Lazy.kind t = .hash) q) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S N base H) tbl) P) q := by
  let w (t : (Lazy.OSpec P₀ []ₒ).Domain) := if Lazy.kind t = .hash then 1 else 0
  refine EvalCost.simulateQ _ w ?_ P q (wCount_of_isQueryBoundP _ _ _ hq)
  intro t
  rcases t with n | op | addr | hash
  · exact EvalCost.const _
  · exact PEmpty.elim op
  · exact EvalCost.const _
  · exact hash_cost S N base hash

theorem keygen_cost (tbl : SecretTable S.vp P₀) (pk : S.Node) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S N base H) tbl) (Lazy.openKeygen P₀ []ₒ pk))
      (Lazy.keygenHashes S.vp) :=
  simulate_cost S N base tbl _ ((Lazy.openKeygen_kindBound (prims := P₀) (gspec := []ₒ) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp)))

theorem sign_cost (tbl : SecretTable S.vp P₀) (pk root R : S.Node) (m : List SLHDSA.Byte) :
    EvalCost (fun H => simulateQ (qmImpl (hashPort S N base H) tbl) (Lazy.openSign P₀ []ₒ m pk root R))
      (Lazy.signHashes S.vp) := by
  apply simulate_cost S N base tbl
  exact (Lazy.openSign_kindBound (prims := P₀) (gspec := []ₒ) .hash m pk root R).mono (by simpa [Lazy.ind] using Lazy.signB_hash (vp := S.vp))

end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.keygen_cost
#print axioms Reduction.ShakeApi.sign_cost
