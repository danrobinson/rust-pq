import Integration.SlhDsaShakePermutation
import PQ.Interactive.QromBridgeEval

/-! Quantum-port evaluation costs of honest SHAKE256 calls. The bytewise
sponge incurs a forward permutation call for every complete 136-byte input
block and one for finalization. All standard signature outputs fit in one block. -/
namespace Reduction.ShakePermutation
open Spec.Keccak MLink SLHDSA OracleComp OracleSpec PQ.Interactive

def absorb (p : State → State) (a : State) (pos : Nat) : Spec.Bytes → State
  | [] => a
  | b :: bs =>
    let t := xorByte a pos b
    if pos+1 = 136 then absorb p (p t) 0 bs else absorb p t (pos+1) bs

theorem foldl_feed (p : State → State) (xs : Spec.Bytes) (a : State) (pos : Nat) (hp : pos < 136) :
    xs.foldl (feed p) (a,pos) = (absorb p a pos xs,(pos + xs.length) % 136) := by
  induction xs generalizing a pos with
  | nil => simp [absorb,Nat.mod_eq_of_lt hp]
  | cons b bs ih =>
    simp only [List.foldl_cons,feed,absorb,List.length_cons]
    by_cases h : pos+1 = 136
    · simp only [h,ite_true,ih _ 0 (by decide),Nat.zero_add]
      congr 1
      omega
    · simp only [h,ite_false,ih _ (pos+1) (by omega)]
      congr 1
      omega

def forward (H : Port → Words) := lanes (fun x => H (false,x))

theorem absorb_cost (xs : Spec.Bytes) (a : State) (pos : Nat) (hp : pos < 136) :
    EvalCost (fun H => pure (absorb (forward H) a pos xs)) ((pos + xs.length)/136) := by
  induction xs generalizing a pos with
  | nil =>
    simpa only [List.length_nil,Nat.add_zero,Nat.div_eq_of_lt hp,absorb] using
      EvalCost.const (X := Port) (Y := Words) (pure a)
  | cons b bs ih =>
    simp only [absorb,List.length_cons]
    by_cases h : pos+1 = 136
    · simp only [h,ite_true]
      have he := EvalCost.eval (false,pack (xorByte a pos b)) unpack
      have hh := EvalCost.bind he (fun x => ih x 0 (by decide))
      convert hh using 1
      · simp only [pure_bind,forward,lanes]
      · omega
    · simp only [h,ite_false]
      convert ih (xorByte a pos b) (pos+1) (by omega) using 1
      omega

theorem squeeze_within (p : State → State) (a : State) (pos n : Nat) (hn : pos+n ≤ 136) :
    squeeze p a pos n = squeeze id a pos n := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih =>
    have hp : pos ≠ 136 := by omega
    simp only [squeeze,hp,ite_false,ih (pos+1) (by omega)]

theorem xof_cost (xs : Spec.Bytes) (n : Nat) (hn : n ≤ 136) :
    EvalCost (fun H => pure (xof (forward H) xs n)) (xs.length/136 + 1) := by
  have ha := absorb_cost xs initial.1 0 (by decide)
  have h := EvalCost.bind ha (fun a => EvalCost.eval
    (false,pack (xorByte (xorByte a (xs.length % 136) 0x1f) 135 0x80))
    (fun y => squeeze id (unpack y) 0 n))
  simpa only [Nat.zero_add,pure_bind,xof,initial,foldl_feed _ _ _ 0 (by decide),
    finish,forward,lanes,squeeze_within _ _ 0 n (by omega)] using h

theorem hash_cost (xs : Spec.Bytes) (n : Nat) (hn : n ≤ 136) :
    EvalCost (fun H => pure (hash (forward H) xs n)) (xs.length/136 + 1) := by
  let toBytes (ys : Spec.Bytes) : Bytes n := (Vector.ofFn fun i : Fin n =>
    (cv ys)[i.val]!)
  have hh := EvalCost.map (xof_cost xs n hn) toBytes
  convert hh using 1
  funext H
  simp only [map_pure]
  congr 1
  apply Vector.ext
  intro i hi
  simp [toBytes,hash,cv,xof]

theorem output_sizes (S : Sha2Set) : S.vp.params.n ≤ 136 ∧ S.vp.params.m ≤ 136 := by
  cases S <;> decide

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.xof_cost
#print axioms Reduction.ShakePermutation.hash_cost
