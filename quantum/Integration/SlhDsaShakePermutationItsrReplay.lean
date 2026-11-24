import Integration.SlhDsaShakePermutationItsrBanks
import Integration.SlhDsaShakePermutationAbsorb

/-! A replay of ordinary absorption that records the two capacity masks and
the rate shear at each step. The record contains overwrite inputs, so distinct
ordinary paths can be compared by the recorded tail uniqueness invariant. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

abbrev Table := Addr → Words
abbrev Log := List (Addr × Words)
def perm (π : Permutation) (H : Table) := salted (fun r => capOf (H (mask false r)))
  (fun r => capOf (H (mask true r))) (fun z => rateOf (H (tailHead z))) π

structure Report where
  path : List Rate
  pre : Rate
  cap : Capacity
  head : Rate
  log : Log

def result (w : Report) : Words := join (rateXor w.pre w.head) w.cap
def empty : Report := ⟨[],0,0,0,[]⟩

def push (π : Permutation) (prev : Report) (b : Rate) (a v c : Words) : Report :=
  let r := rateXor b (rateOf (result prev))
  let mid := (layout π).middle r prev.cap (capOf a)
  let cap := (layout π).finish mid.2 (capOf v)
  ⟨r::prev.path,mid.1,cap,rateOf c,
    (mask false r,a)::(mask true mid.1,v)::(tailHead cap,c)::prev.log⟩

def step (π : Permutation) (H : Table) (prev : Report) (b : Rate) : Report :=
  let r := rateXor b (rateOf (result prev))
  let a := H (mask false r)
  let mid := (layout π).middle r prev.cap (capOf a)
  let v := H (mask true mid.1)
  let cap := (layout π).finish mid.2 (capOf v)
  push π prev b a v (H (tailHead cap))

def replay (π : Permutation) (H : Table) : List Rate → Report
  | [] => empty
  | b::bs => step π H (replay π H bs) b

def Matches (D : Bank) (w : Log) := ∀ i y, (i,y) ∈ w → D i = some y

theorem replay_length (π H) (bs : List Rate) :
    (replay π H bs).log.length = 3*bs.length ∧ (replay π H bs).path.length = bs.length := by
  induction bs with
  | nil => simp [replay,empty]
  | cons b bs ih =>
    change (replay π H bs).log.length + 3 = _ ∧ (replay π H bs).path.length+1 = _
    rw [ih.1,ih.2,List.length_cons]; omega

theorem replay_injective (π H) : Function.Injective (fun bs => (replay π H bs).path) := by
  intro a
  induction a with
  | nil => intro b eq; cases b <;> simp [replay,empty,step,push] at *
  | cons b bs ih =>
    rintro (_|⟨c,cs⟩) eq
    · contradiction
    obtain ⟨hd,tl⟩ := List.cons.inj eq
    have tail := ih tl
    subst cs
    have same := congrArg (fun x => rateXor x (rateOf (result (replay π H bs)))) hd
    simp only [rateXor_cancel] at same
    exact congrArg (fun x => x::bs) same

theorem consistent (π H) (xs : List Rate) : ∀ i y, (i,y) ∈ (replay π H xs).log → H i = y := by
  induction xs with
  | nil => simp [replay,empty]
  | cons b bs ih =>
    intro i y mem
    simp only [replay,step,push,List.mem_cons,Prod.mk.injEq] at mem
    rcases mem with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|mem
    · rfl
    · rfl
    · rfl
    · exact ih _ _ mem

theorem logged (π H) (D : Bank) (xs : List Rate) (m : Matches D (replay π H xs).log) :
    let v := replay π H xs
    Relabel.run π (masks D false) (masks D true) v.path = some (v.pre,v.cap) ∧
    (xs ≠ [] → held D v.cap = some v.head) := by
  induction xs with
  | nil => exact ⟨rfl,fun e => False.elim (e rfl)⟩
  | cons b bs ih =>
    let p := replay π H bs
    let r := rateXor b (rateOf (result p))
    let a := H (mask false r)
    let mid := (layout π).middle r p.cap (capOf a)
    let v := H (mask true mid.1)
    let z := (layout π).finish mid.2 (capOf v)
    change Matches D ((mask false r,a)::(mask true mid.1,v)::(tailHead z,H (tailHead z))::p.log) at m
    have old := ih (fun i y h => m i y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
    have e₁ : masks D false r = some (capOf a) := by
      change (D (mask false r)).map capOf = _
      rw [m _ a (by simp)]
      rfl
    have e₂ : masks D true mid.1 = some (capOf v) := by
      change (D (mask true mid.1)).map capOf = _
      rw [m _ v (by simp)]
      rfl
    have e₃ : held D z = some (rateOf (H (tailHead z))) := by
      change (D (tailHead z)).map rateOf = _
      rw [m _ (H (tailHead z)) (by simp)]
      rfl
    change Relabel.run π (masks D false) (masks D true) (r::p.path) = some (mid.1,z) ∧ _
    refine ⟨?_,fun _ => e₃⟩
    have hr : Relabel.run π (masks D false) (masks D true) p.path = some (p.pre,p.cap) := old.1
    simp only [Relabel.run,hr,e₁]
    change (masks D true mid.1).bind _ = _
    rw [e₂]
    rfl

end Reduction.ShakePermutation.ItsrLabel
