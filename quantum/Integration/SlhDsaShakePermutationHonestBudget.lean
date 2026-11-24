import Integration.SlhDsaShakePermutationHonestCost

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "ROM" => unifSpec + hashSpec (Primitives.core (ShakeApi.primitives S base))

abbrev hashWeight {α : Type} : ℕ ⊕ α → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

private theorem read_count (xs : List SLHDSA.Byte) : WCount hashWeight (readRaw S N xs) 1 := by
  unfold readRaw
  split
  · exact wCount_liftM_query _ _ le_rfl
  · trivial

private theorem raw_count {α : Type} {a : OracleComp ROM α} {n : ℕ}
    (h : IsQueryBoundP a (fun t => t.isRight = true) n) :
    WCount hashWeight (simulateQ (rawImpl S N base) a) n := by
  refine WCount.simulateQ (w := fun t => if t.isRight = true then 1 else 0) _ ?_ (wCount_of_isQueryBoundP _ _ _ h)
  intro t
  rcases t with u | (h | m)
  · exact wCount_liftM_query _ _ le_rfl
  · cases h with
    | thash pk a xs => exact WCount.map (read_count S N _) _
    | hmsg r pk root m => exact read_count S N _
  · exact WCount.map (read_count S N _) _

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
local notation "A" => rawScheme S N base rand seeds

private theorem signing_count (pk sk : List SLHDSA.Byte) (t s) :
    WCount hashWeight ((signing S N A pk sk t).run s) (sgnW (signCharge S) t) := by
  cases t with
  | inl u => exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  | inr m => exact WCount.map (raw_count S N base (sign_bound S base rand seeds pk sk m)) _

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] (F : PortForger X Y E)
variable (fresh : QueryLog (ByteMessage →ₒ ByteSig) → ByteMessage → ByteSig → Bool)

def honestCharge (S : Sha2Set) (qs : ℕ) := keyCharge S + qs * signCharge S + verifyCharge S

theorem joint_budget (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE hashWeight (joint S N F A fresh) (q + honestCharge S qs) := by
  unfold joint honestCharge
  rw [show q+(keyCharge S+qs*signCharge S+verifyCharge S) =
    ((q+qs*signCharge S)+ (0+verifyCharge S))+keyCharge S by omega]
  refine PUE.liftQ_bind _ (raw_count S N base (keygen_bound S base rand seeds)) fun ks => ?_
  refine PUE.bind (PUE.wrap (cnt := sgnW (signCharge S)) _
    (signing_count S N base rand seeds ks.1 ks.2)
    (PUE.compileQ _ _ _ (wCount_of_countBound isPort isSign _ (signCharge S) ?_ _ q qs (hq _) (hs _))) []) ?_
  · intro t
    rcases t with j | u | n | m <;> simp [compileW,isPort,isSign]
  · intro z
    exact PUE.liftQ_bind _ (raw_count S N base (verify_bound S base rand seeds _ _ _))
      (fun _ => PUE.pure _ 0)

theorem benchmark_honest_calls (S : Sha2Set) : honestCharge S 1 ≤ 2^32 := by cases S <;> decide
theorem benchmark_honest_blocks (S : Sha2Set) : 483 * honestCharge S 1 ≤ 2^40 := by cases S <;> decide

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.joint_budget
#print axioms Reduction.ShakePermutation.Honest.benchmark_honest_blocks
