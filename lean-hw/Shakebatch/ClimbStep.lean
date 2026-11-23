import Shakebatch.RecoverOrder
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

/-- Inductive relation for a lane's hash value and global FORS node index. -/
def AtLevel (P : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (ind : List Nat)
    (t h idx : Nat) (v : Spec.Bytes) :=
  v = (forsClimbAt P sig pk a ind t h).1 ∧ idx = (forsClimbAt P sig pk a ind t h).2 ∧
    idx = t*2^(P.a-h) + ind[t]!/2^h

theorem climb_step (P : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (ind : List Nat)
    (t h idx : Nat) (v : Spec.Bytes) (level : h < P.a) (old : AtLevel P sig pk a ind t h idx v) :
    AtLevel P sig pk a ind t (h+1) (idx/2) (Spec.H P pk {a with word2:=h+1,word3:=idx/2}
      (pairMsg v (Spec.block P sig (t*(P.a+1)+1+h)) idx)) := by
  obtain ⟨hv,hti,hcl⟩ := old
  have hpw : 2 ^ (P.a-h) = 2 * 2 ^ (P.a-(h+1)) := by rw [← pow_succ']; congr 1; omega
  have hidx : idx=2*(t*2^(P.a-(h+1)))+ind[t]!/2^h := by rw [hcl,hpw]; ring
  have hmod : idx%2=(ind[t]!/2^h)%2 := by rw [hidx]; omega
  have hdiv : idx/2=t*2^(P.a-(h+1))+ind[t]!/2^(h+1) := by
    rw [hidx,pow_succ,← Nat.div_div_eq_div_mul]; omega
  have step : forsClimbAt P sig pk a ind t (h+1) =
      forsClimbStep P ind[t]! (forsAuthPath P sig t) pk a (forsClimbAt P sig pk a ind t h) h := by
    simp only [forsClimbAt,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  unfold AtLevel
  rw [step]
  by_cases even : (ind[t]!/2^h)%2=0
  · simp only [forsClimbStep,even,↓reduceIte]
    exact ⟨by rw [pairMsg_even _ _ _ (by omega),hv,← hti,fors_block_auth _ _ _ _ level],by rw [hti],hdiv⟩
  · simp only [forsClimbStep,even,↓reduceIte]
    have sub : (idx-1)/2=idx/2 := by omega
    exact ⟨by rw [pairMsg_odd _ _ _ (by omega),hv,← hti,sub,fors_block_auth _ _ _ _ level],
      by rw [← hti,sub],hdiv⟩

end slhdsa.ShakeBatch
