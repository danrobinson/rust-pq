import Wots.Step
import Leaf256.Batch
import Leaf256.Layout
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open Spec.SHA256

/-- Writing the next digest replaces every byte introduced by the previous step. -/
theorem packed_overwrite (w h g : Nat → Word) (n k : Nat) (t u : Word) :
    packedWord (packedWord w h n t) g n u k = packedWord w g n u k := by
  unfold packedWord Chain.valueWord
  split_ifs <;> simp_all only [ite_false,ite_true]
  generalize h (n/4-1) = a
  generalize g (n/4-1) = b
  generalize w k = c
  leaf_bits

theorem packed_congr (w w' h h' : Nat → Word) (n k : Nat) (t : Word)
    (sameWord : w k = w' k) (sameHash : ∀ i < 8, h i = h' i)
    (shape : n=16 ∨ n=24 ∨ n=32) :
    packedWord w h n t k = packedWord w' h' n t k := by
  unfold packedWord Chain.valueWord
  split_ifs <;> simp (disch := omega) only [sameHash,sameWord]

def chainState (iv : List Word) (w : Nat → Word) (initial : List Word) (n : Nat) : Nat → List Word
  | 0 => initial
  | t+1 => compress iv (Leaf.blockOf (packedWord w (fun i => (chainState iv w initial n t)[i]!) n (BitVec.ofNat 32 t)))

private def counter (k : Nat) : I32 := ⟨BitVec.ofNat 32 k⟩

private theorem counter_val (k : Nat) (hk : k ≤ 15) : (counter k).val = (k : Int) := by
  interval_cases k <;> decide +kernel

private theorem next_small : ∀ k : Fin 15,
    core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨counter k.val,15#i32⟩ =
      ok (some (counter k.val),⟨counter (k.val+1),15#i32⟩)  := by
  intro k
  have cur := counter_val k.val (by omega)
  have suc := counter_val (k.val+1) (by omega)
  have cmp : (core.iter.range.StepI32.partialOrdInst.lt (counter k.val) 15#i32) = ok true := by
    change ok (decide ((counter k.val).val < (15#i32).val)) = _
    rw [cur,show (15#i32).val = 15 by decide]; simp [show (k.val : Int) < 15 by omega]
  unfold core.iter.range.IteratorRange.next
  simp only [cmp,bind_ok,ite_true]
  simp only [show core.iter.range.StepI32.cloneInst.clone (counter k.val) = ok (counter k.val) by rfl,bind_ok]
  simp only [core.iter.range.StepI32,core.iter.range.IScalarStep,core.iter.range.IScalarStep.forward_checked]
  rw [dif_pos (by rw [cur]; scalar_tac)]
  simp only [bind_ok,Result.ok.injEq,Prod.mk.injEq,core.ops.range.Range.mk.injEq,true_and,and_true]
  apply IScalar.eq_of_val_eq
  rw [IScalar.ofInt_val_eq,suc]; scalar_tac

private theorem last : core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨counter 15,15#i32⟩ =
    ok (none,⟨counter 15,15#i32⟩) := by
  unfold core.iter.range.IteratorRange.next
  have cmp : core.iter.range.StepI32.partialOrdInst.lt (counter 15) 15#i32 = ok false := by
    change ok (decide ((counter 15).val < (15#i32).val)) = _
    rw [counter_val 15 (by decide),show (15#i32).val = 15 by decide]; rfl
  simp only [cmp,bind_ok,Bool.false_eq_true,ite_false]

def chainWords (a : Words) (j : Fin 16) := fun k : Nat => a.val[k]! j

def Ready (base w : Words) (n : Nat) := ∀ j : Fin 16, ∀ h t k, k < 16 →
  packedWord (chainWords w j) h n t k = packedWord (chainWords base j) h n t k

theorem ready_next (base w stored : Words) (h : Hash) (n : Nat) (t : Word) (ready : Ready base w n)
    (packed : ∀ k < 16, ∀ j : Fin 16, stored.val[k]! j = packedWord (chainWords w j) (fun i => h.val[i]! j) n t k)
    (shape : n=16 ∨ n=24 ∨ n=32) : Ready base stored n := by
  intro j g u k hk
  rw [packed_congr _ _ g g n k u (packed k hk j) (fun _ _ => rfl) shape,packed_overwrite,ready j g u k hk]


/-- All fifteen F compressions in the production endpoint loop, for every SIMD
lane, from arbitrary starting digest words and a matching four-round prefix. -/
theorem chain_spec (N : Usize) (iv pre initial : Hash) (base : Words)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (prefixOK : Trace pre (fun j => schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4) :
    wots_endpoints_loop1_loop0 N ⟨0#i32,15#i32⟩ iv (fun _ => 0xffff) base initial pre ⦃ out =>
      ∀ j, stateWords (laneState out j) = chainState (stateWords (laneState iv j)) (chainWords base j)
        (stateWords (laneState initial j)) N.val 15 ⦄ := by
  let holds := fun (h : Hash) k => ∀ j, stateWords (laneState h j) =
    chainState (stateWords (laneState iv j)) (chainWords base j) (stateWords (laneState initial j)) N.val k
  unfold wots_endpoints_loop1_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range I32 × Words × Hash => 15-p.1.start.val.toNat)
    (inv := fun p => ∃ k ≤ 15, p.1 = ⟨counter k,15#i32⟩ ∧ Ready base p.2.1 N.val ∧ holds p.2.2 k)
  · rintro ⟨it,w,h⟩ ⟨k,hk,rfl,ready,old⟩
    by_cases small : k < 15
    · have eq (j : Fin 16) : message N w h (counter k) j =
          Leaf.blockOf (packedWord (chainWords base j) (fun i => (stateWords (laneState h j))[i]!) N.val (BitVec.ofNat 32 k)) := by
        apply Leaf.block_congr
        intro i hi
        rw [show (counter k).bv = BitVec.ofNat 32 k from rfl]
        apply Eq.trans (packed_congr _ _ _ _ _ _ _ rfl (fun i hi => Leaf.lane_lookup h j i hi) shape)
        exact ready j _ _ i hi
      have preOK : Trace pre (fun j => schedule (message N w h (counter k) j)) (laneState iv) 4 := by
        apply Leaf.transfer_prefix (by decide) _ prefixOK
        intro j i hi
        rw [eq,Leaf.word_blockOf _ _ (by omega),Leaf.word_blockOf _ _ (by omega)]
        simp (disch := omega) only [packedWord,Chain.valueWord,if_neg]
      apply WP.spec_mono (step_spec N iv pre _ _ w h (counter k) shape (next_small ⟨k,small⟩) preOK)
      rintro _ ⟨words,out,rfl,hw,hh⟩
      simp only
      refine ⟨⟨k+1,by omega,rfl,ready_next base w words h _ _ ready hw shape,fun j => ?_⟩,?_⟩
      · rw [hh j,eq j,old j]
        rfl
      · rw [counter_val k hk,counter_val (k+1) (by omega)]
        omega
    · have doneK : k = 15 := by omega
      subst k
      simp only
      rw [step_eq,last]
      simp only [bind_ok,step_simps]
      exact old
  · exact ⟨0,by decide,by rfl,fun _ _ _ _ _ => rfl,fun _ => rfl⟩
end slhdsa.X86.Wots
