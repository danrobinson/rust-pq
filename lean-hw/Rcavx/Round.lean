import Rcavx.Funs
import Rcavx.Array
import Streamround.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust Stream
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

private theorem choose (x y z : BitVec 64) : z ^^^ (x &&& (y ^^^ z)) = (x &&& y) ^^^ (~~~x &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

private theorem addLeft (x y z : BitVec 64) : x + (y+z) = y+(x+z) := by
  rw [← BitVec.add_assoc,BitVec.add_comm x y,BitVec.add_assoc]

private theorem sumA (h k w s0 s1 maj ch : BitVec 64) :
    k+(w+(h+(s1+(ch+(s0+maj))))) = h+(s1+(ch+(k+(w+(s0+maj))))) := by
  simp only [BitVec.add_assoc,BitVec.add_comm,addLeft]
private theorem sumE (h k w s1 ch : BitVec 64) :
    k+(w+(h+(s1+ch))) = h+(s1+(ch+(k+w))) := by
  simp only [BitVec.add_assoc,BitVec.add_comm,addLeft]

theorem sha_round (v : Array U64 8#usize) (wk : U64) (W : List (BitVec 64)) (t : Nat)
    (word : wk.bv = Spec.SHA512.K[t]! + W[t]!) :
    sha512.x86_avx2.sha_round v wk ⦃ out => state512 out = Spec.SHA512.round W (state512 v) t ⦄ := by
  conv_lhs => rw [materialize v]
  simp only [sha512.x86_avx2.sha_round,lift,bind_ok,step_simps,at0,put0,at1,put1,at2,put2,at3,put3,at4,put4,at5,put5,at6,put6,at7,put7]
  simp [state512,Spec.SHA512.round,Spec.SHA512.bsig0,Spec.SHA512.bsig1,Spec.SHA512.ch,
    Spec.SHA512.maj,choose,word,Array.make,BitVec.add_assoc]
  exact ⟨sumA _ _ _ _ _ _ _,sumE _ _ _ _ _⟩

end slhdsa.X86.RustCrypto512
