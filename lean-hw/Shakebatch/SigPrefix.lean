import Shakebatch.Auth
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def treeBlock {N : Usize} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : Slice U32) (t z : Nat) : Spec.Bytes :=
  let idx := choices.val[t]!.val
  if z=0 then Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) (t*2^p.a.val+idx)
  else forsAuth (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) t idx (z-1)

def SigPrefix {N : Usize} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : Slice U32) (stride count : Nat) (s : Buffer) :=
  s.length=choices.length*stride ∧ ∀ t < count, ∀ z ≤ p.a.val, ∀ b < N.val,
    sigByte s stride N.val t z b = (treeBlock p sk seed a choices t z)[b]!

theorem batch_done {N : Usize} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : Slice U32) (first active stride : Nat) (indices : Array U32 machine.width)
    (secrets : Rows N) (before once after : Buffer) (shape : stride=(p.a.val+1)*N.val)
    (bounds : first+active ≤ choices.length) (width : active ≤ machine.width.val)
    (prior : SigPrefix p sk seed a choices stride first before)
    (addressed : ∀ j < active, indices.val[j]!.val=(first+j)*2^p.a.val+choices.val[first+j]!.val)
    (keys : ∀ j < machine.width.val, bytes secrets.val[j]!.val=
      Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) indices.val[j]!.val)
    (stored : Scattered secrets first stride 0 active before once)
    (path : AuthWritten p sk seed a indices first active stride p.a.val once after) :
    SigPrefix p sk seed a choices stride (first+active) after := by
  refine ⟨path.1.trans (stored.1.trans prior.1),?_⟩
  intro t tbound z level b byte
  have inside : z*N.val+b < stride := by
    have := Nat.mul_le_mul_right N.val level
    rw [shape,Nat.add_mul,Nat.one_mul];omega
  have endOfTree := Nat.mul_le_mul_right stride (show t+1 ≤ choices.length by omega)
  rw [Nat.add_mul,Nat.one_mul] at endOfTree
  have absolute : t*stride+(z*N.val+b) < before.length := by rw [prior.1];omega
  rw [path.2 t z b inside (stored.1.symm ▸ absolute) byte]
  have secret := scattered_block secrets first stride 0 active before once (by simpa using stored) t z b inside absolute byte
  rw [secret]
  by_cases old : t < first
  · simp [show ¬first ≤ t by omega,prior.2 t old z level b byte]
  · have lt : t-first < active := by omega
    have lane : t-first < machine.width.val := by omega
    have idx := addressed (t-first) lt
    rw [show first+(t-first)=t by omega] at idx
    by_cases zero : z=0
    · subst z
      have field := keys (t-first) lane
      have valid : b < secrets.val[t-first]!.val.length := by simpa using byte
      rw [idx] at field
      simp only [show first ≤ t by omega,tbound,treeBlock,ite_true,not_lt_zero,true_and,false_and,
        zero_le,and_true,ite_false]
      rw [getElem!_pos _ b valid,← bytes_getElem! _ _ valid,field]
    · have less : z-1 < p.a.val := by omega
      simp only [show first ≤ t by omega,tbound,level,show 0 < z by omega,zero,treeBlock,
        authNode,true_and,and_true,ite_true,ite_false,idx,forsAuth,sibling_eq _ _ _ _ less]
      rfl

end slhdsa.ShakeBatch
