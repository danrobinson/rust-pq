import Parallel.ForsFieldPack
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

structure SplitProvider {N} (mode : Mode) (d : Data N) where
  action : Nat → Nat → Result (Cell N)
  issued : ∀ (t j : Nat), t<d.p.k.val → j<d.p.a.val → target mode.policy d.p.a.val<j →
    Receipt mode d (.reduced t j) (action t j)

def word (k : UScalarTy) (v : Nat) : UScalar k := ⟨BitVec.ofNat _ v⟩
theorem word_eq {ty : UScalarTy} (v : Nat) (h : v<2^ty.numBits) : (word ty v).val=v := by
  change v%2^ty.numBits=v
  exact Nat.mod_eq_of_lt h

private theorem width_pos (mode : Mode) : 0<width mode.policy := by cases mode <;> simp [width,Mode.policy]
private theorem width_size (mode : Mode) : width mode.policy≤8 := by cases mode <;> simp [width,Mode.policy]

noncomputable def selectAction {N} (mode : Mode) (d : Data N) (split : Nat → Nat → Result (Cell N)) (t c : Nat) : Result (Cell N) :=
  let w := width mode.policy
  let first := groupFirst w t
  let lane := t%w
  let active := min (d.choices.length-first) w
  let D := low mode.policy d.p.a.val
  if c≤D then
    if mode.policy=.scalar then scalarLow mode.host d (word .U32 t) (word .U32 D) default c
    else groupedLow mode d (word .U16 first) (word .U8 active) (word .U8 D) c lane
  else if c-1≤target mode.policy d.p.a.val then
    if mode.policy=.three then groupedDirect d (word .U16 first) (word .U8 active) (word .U8 (c-1)) lane
    else scalarDirect mode.host d (word .U32 t) (word .U32 (c-1))
  else split t (c-1)

theorem select_receipt {N} (mode : Mode) (d : Data N) (v : Valid d)
    (splitPlan : SplitProvider mode d) (t c : Nat) (tree : t<d.p.k.val) (column : c≤d.p.a.val) :
    Receipt mode d (owner mode.policy d.p.a.val t c) (selectAction mode d splitPlan.action t c) := by
  have trees : d.p.k.val≤35 := v.pn.valid.k_le
  have height : d.p.a.val≤14 := v.pn.valid.a_le
  have depth : low mode.policy d.p.a.val≤d.p.a.val := by unfold low;split <;> exact Nat.min_le_left ..
  let w := width mode.policy
  let first := groupFirst w t
  let lane := t%w
  let active := min (d.choices.length-first) w
  let D := low mode.policy d.p.a.val
  have whole : first+lane=t := group_lane w t
  have bits := System.Platform.le_numBits
  have live : lane<active := by
    have positive := width_pos mode
    have right : lane<w := Nat.mod_lt t positive
    exact Nat.lt_min.mpr ⟨by rw [v.count];omega,right⟩
  have num : active≤8 := (Nat.min_le_right ..).trans (width_size mode)
  have f16 : (word .U16 first).val=first := word_eq _ (by change first<65536;omega)
  have a8 : (word .U8 active).val=active := word_eq _ (by change active<256;omega)
  have D8 : (word .U8 D).val=D := word_eq _ (by change D<256;dsimp [D];omega)
  have D32 : (word .U32 D).val=D := word_eq _ (by change D<4294967296;dsimp [D];omega)
  have t32 : (word .U32 t).val=t := word_eq _ (by change t<4294967296;omega)
  unfold owner selectAction
  split
  · rename_i lower
    by_cases scalar : mode.policy=.scalar
    · have group : groupFirst (width mode.policy) t=t := by simp [scalar,width,groupFirst]
      have lane0 : t%width mode.policy=0 := by simp [scalar,width,Nat.mod_one]
      simp only [if_pos scalar,if_pos lower,group,lane0]
      simpa only [t32] using Receipt.scalarLow (mode:=mode) (d:=d) (word .U32 t) (word .U32 D) default c scalar
        (by simpa only [t32] using tree) (by simpa only [D32] using lower) D32
    · simp only [if_pos lower,if_neg scalar]
      simpa only [f16] using Receipt.groupedLow (mode:=mode) (d:=d) (word .U16 first) (word .U8 active)
        (word .U8 D) c lane scalar (by rw [a8,f16]) (by simpa only [a8] using live) D8 (by simpa only [D8] using lower)
  · rename_i upper
    have positive : 0<c := by omega
    have less : c-1<d.p.a.val := by omega
    have j32 : (word .U32 (c-1)).val=c-1 := word_eq _ (by change c-1<4294967296;omega)
    have j8 : (word .U8 (c-1)).val=c-1 := word_eq _ (by change c-1<256;omega)
    split
    · rename_i direct
      by_cases grouped : mode.policy=.three
      · have same : highWidth mode.policy=w := by simp [highWidth,w,grouped,width]
        rw [same]
        simp only [if_neg upper,if_pos direct,if_pos grouped]
        simpa only [f16,j8] using Receipt.groupedDirect (mode:=mode) (d:=d) (word .U16 first) (word .U8 active)
          (word .U8 (c-1)) lane grouped (by rw [a8,f16];simp [active,w,grouped,width]) (by simpa only [a8] using live) (by simpa only [j8] using less)
      · have hw : highWidth mode.policy=1 := by simp [highWidth,grouped]
        simp only [hw,groupFirst,Nat.div_one,Nat.mul_one,Nat.mod_one]
        simp only [if_neg upper,if_pos direct,if_neg grouped]
        simpa only [t32,j32] using Receipt.scalarDirect (mode:=mode) (d:=d) (word .U32 t) (word .U32 (c-1))
          grouped (by simpa only [t32] using tree) (by simpa only [j32] using less)
    · rename_i large
      simp only [if_neg upper,if_neg large]
      exact splitPlan.issued t (c-1) tree less (by omega)

noncomputable def makePacket {N} (mode : Mode) (d : Data N) (valid : Valid d) (split : SplitProvider mode d) : Packet mode d where
  action := selectAction mode d split.action
  issued t ht c hc := select_receipt mode d valid split t c ht hc

end slhdsa.RawFors
