import Shakebatch.ClimbStep
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch

theorem leaf_start {N} (p : slhdsa.params.Params) (hp : PN p N) (sig : Slice U8) (seed : Array U8 N)
    (a : address.Adrs) (digits : List Nat) (t : Nat) (idx : U32)
    (selected : idx.val=t*2^p.a.val+digits[t]!) (key v : Array U8 N)
    (secret : bytes key.val=Spec.block (Shake.params p) (bytes sig.val) (t*(p.a.val+1)))
    (leaf : bytes v.val=Spec.shake256 (bytes seed.val ++
      ((adrsS {a with word2:=0#u32,word3:=idx}).bytes ++ bytes key.val)) N.val) :
    AtLevel (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) digits t 0 idx.val (bytes v.val) := by
  have ad : adrsS {a with word2:=0#u32,word3:=idx} = {adrsS a with word2:=0,word3:=t*2^p.a.val+digits[t]!} := by
    simp only [adrsS,selected];rfl
  refine ⟨?_,?_,?_⟩
  · change bytes v.val=Spec.F (Shake.params p) (bytes seed.val) {adrsS a with word2:=0,word3:=t*2^p.a.val+digits[t]!}
      (Spec.block (Shake.params p) (bytes sig.val) (t*(p.a.val+1)))
    rw [leaf,ad,secret]
    simp only [Spec.F,Shake.params,paramsS_n,hp.n_eq,List.append_assoc]
  · exact selected
  · simpa only [Shake.params,paramsS_a,Nat.sub_zero,Nat.pow_zero,Nat.div_one] using selected

end slhdsa.ShakeBatch
