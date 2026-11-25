import Parallel.ForestPack
import Parallel.LowForsHosted
import Parallel.ScalarForsLowHosted
import Parallel.ForsTickets
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors
inductive Policy where
  | scalar | three | eight
  deriving DecidableEq

def width : Policy → Nat | .scalar => 1 | .three => 3 | .eight => 8
def target (mode : Policy) (a : Nat) := if a≥10 then 9 else if mode≠.scalar ∧ a≥9 then 8 else a
def low (mode : Policy) (a : Nat) := if mode=.eight then min a 3 else min a (target mode a)

inductive Owner where
  | low (first lane col : Nat)
  | direct (first lane height : Nat)
  | reduced (tree height : Nat)
  deriving DecidableEq

def groupFirst (width tree : Nat) := tree/width*width
def highWidth (mode : Policy) := if mode=.three then 3 else 1
def owner (mode : Policy) (a t c : Nat) : Owner :=
  if c≤low mode a then .low (groupFirst (width mode) t) (t%width mode) c
  else if c-1≤target mode a then .direct (groupFirst (highWidth mode) t) (t%highWidth mode) (c-1)
  else .reduced t (c-1)

def slot (a : Nat) : Owner → Nat
  | .low first lane col => (first+lane)*(a+1)+col
  | .direct first lane h => (first+lane)*(a+1)+1+h
  | .reduced tree h => tree*(a+1)+1+h

theorem group_lane (w t : Nat) : groupFirst w t+t%w=t := by simp [groupFirst,Nat.div_add_mod,Nat.mul_comm]
theorem ownership (mode : Policy) (a t c : Nat) : slot a (owner mode a t c)=t*(a+1)+c := by
  unfold owner
  split
  · simp [slot,group_lane]
  · rename_i high
    have : 0<c := by omega
    split <;> simp [slot,group_lane] <;> omega

theorem unique (mode : Policy) (a t u c e : Nat) (within : c≤a) (inside : e≤a)
    (same : slot a (owner mode a t c)=slot a (owner mode a u e)) : t=u ∧ c=e := by
  simp only [ownership] at same
  have decode (i j : Nat) (room : j≤a) : (i*(a+1)+j)/(a+1)=i := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt (by omega),Nat.zero_add]
  have tr := congrArg (·/(a+1)) same
  rw [decode t c within,decode u e inside] at tr
  subst u
  exact ⟨rfl,by omega⟩

theorem complete (mode : Policy) (a k n : Nat) (inside : n<k*(a+1)) :
    ∃ t<k, ∃ c≤a, slot a (owner mode a t c)=n := by
  refine ⟨n/(a+1),Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]),n%(a+1),by have := Nat.mod_lt n (by omega : 0<a+1);omega,?_⟩
  rw [ownership,Nat.mul_comm,Nat.div_add_mod]

private theorem rectangle {α : Type} [Inhabited α] (f : Nat → List α) (n w : Nat)
    (lens : ∀ t<n, (f t).length=w) (t c : Nat) (row : t<n) (column : c<w) :
    ((List.range n).flatMap f)[t*w+c]! = (f t)[c]! := by
  induction n with
  | zero => omega
  | succ n ih =>
    have olds : ∀ t<n,(f t).length=w := fun i hi => lens i (by omega)
    have length : ((List.range n).flatMap f).length=n*w := by
      rw [List.length_flatMap]
      have eq : ((List.range n).map (fun i => (f i).length))=(List.replicate n w) := by
        apply List.ext_getElem (by simp)
        intro i hi hj
        simp only [List.getElem_map,List.getElem_range,List.getElem_replicate,Function.comp_apply]
        exact olds i (by simpa using hi)
      rw [eq];simp
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    by_cases endAt : t=n
    · subst t
      rw [←length,List.getElem!_append_right _ _ _ (by omega)]
      simp
    · have live : t<n := by omega
      have bound := Nat.mul_le_mul_right w live
      rw [Nat.succ_mul] at bound
      rw [List.getElem!_append_left _ _ _ (by omega),ih olds live]

theorem field_eq {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : alloc.vec.Vec U32) (decoded : nats choices.val=Spec.base2b (bytes md.val) p.a.val p.k.val)
    (len : choices.length=p.k.val) (t c : Nat) (tree : t<p.k.val) (col : c≤p.a.val) :
    ParallelLowFors.field p sk seed a choices t c =
      (ParallelCached.forsRows (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))[t*(p.a.val+1)+c]! := by
  unfold ParallelCached.forsRows
  have shape : (Shake.params p).a=p.a.val := rfl
  have trees : (Shake.params p).k=p.k.val := rfl
  simp only [shape,trees]
  rw [rectangle _ _ (p.a.val+1) (by intros;simp) _ _ tree (by omega)]
  have within : t<choices.val.length := (show t<choices.length from len.symm ▸ tree)
  have pick : (Spec.base2b (bytes md.val) p.a.val p.k.val)[t]! = (choices.val[t]!).val := by
    rw [←decoded,fors_nats_getElem! _ _ within,getElem!_pos choices.val _ within]
  cases c with
  | zero => simp [ParallelLowFors.field,ParallelLowFors.absolute,pick]
  | succ h =>
    have small : h<p.a.val := by omega
    rw [ParallelLowFors.field,ForsDriver.sibling_local _ _ _ _ small]
    simp [pick,small,forsAuth,shape,alloc.vec.Vec.val]

end slhdsa.RawFors
