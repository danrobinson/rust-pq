import Streamround.Funs
import Slhdsa.Proofs.Sha256Core
import Slhdsa.Proofs.Sha512Core
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

private theorem choose {n} (x y z : BitVec n) :
    z ^^^ (x &&& (y ^^^ z)) = (x &&& y) ^^^ (~~~x &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

private theorem majority {n} (x y z : BitVec n) :
    (x &&& y) ^^^ (z &&& (x ^^^ y)) = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

def state256 (v : Array U32 8#usize) : Spec.SHA256.State :=
  (v.val[0]!.bv,v.val[1]!.bv,v.val[2]!.bv,v.val[3]!.bv,v.val[4]!.bv,v.val[5]!.bv,v.val[6]!.bv,v.val[7]!.bv)

theorem round256_spec (v : Array U32 8#usize) (wk : U32) (W : List (BitVec 32)) (t : Nat)
    (word : wk.bv = Spec.SHA256.K[t]! + W[t]!) :
    StreamRoundRust.sha256.stream.round v wk ⦃ out => state256 out = Spec.SHA256.round W (state256 v) t ⦄ := by
  unfold StreamRoundRust.sha256.stream.round
  step*
  simp [state256,Spec.SHA256.round,Spec.SHA256.bsig0,Spec.SHA256.bsig1,Spec.SHA256.ch,Spec.SHA256.maj,
    choose,majority,word,BitVec.add_assoc, *]

def state512 (v : Array U64 8#usize) : Spec.SHA512.State :=
  (v.val[0]!.bv,v.val[1]!.bv,v.val[2]!.bv,v.val[3]!.bv,v.val[4]!.bv,v.val[5]!.bv,v.val[6]!.bv,v.val[7]!.bv)

theorem round512_spec (v : Array U64 8#usize) (wk : U64) (W : List (BitVec 64)) (t : Nat)
    (word : wk.bv = Spec.SHA512.K[t]! + W[t]!) :
    StreamRoundRust.sha512.stream.round v wk ⦃ out => state512 out = Spec.SHA512.round W (state512 v) t ⦄ := by
  unfold StreamRoundRust.sha512.stream.round
  step*
  simp [state512,Spec.SHA512.round,Spec.SHA512.bsig0,Spec.SHA512.bsig1,Spec.SHA512.ch,Spec.SHA512.maj,
    choose,majority,word,BitVec.add_assoc, *]
end slhdsa.X86.Stream
