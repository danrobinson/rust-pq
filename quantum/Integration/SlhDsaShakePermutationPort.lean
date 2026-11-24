import Integration.SlhDsaShakePermutationFixQuery
import Integration.SlhDsaShakePermutationShear

/-! A clean reversible implementation of the public forward/inverse
permutation port using two capacity masks and one rate mask. Every gate
other than the two explicitly designated table ports is oracle-independent. -/
namespace Reduction.ShakePermutation.RoundPort
open Fix Fix.Circuit Quantum

abbrev MaskAddr := Bool × Rate
abbrev MaskReg := MaskAddr × Capacity
abbrev HeadReg := Capacity × Rate
abbrev Reg (Z : Type) := MaskReg × HeadReg × Z

def maskOrder (Z : Type) : Reg Z ≃ (MaskReg × Z) × HeadReg :=
  ⟨fun s => ((s.1,s.2.2),s.2.1),fun s => (s.1.1,s.2,s.1.2),fun _ => rfl,fun _ => rfl⟩

inductive Program (Z : Type) where
  | mask (g : Circuit MaskAddr Capacity Z)
  | head (g : Circuit Capacity Rate Z)
  | localOp (g : Equiv.Perm Z)
  | seq (a b : Program Z)

namespace Program

def run {Z : Type} (k : MaskAddr → Capacity) (h : RateMask) :
    Program Z → Equiv.Perm (Reg Z)
  | .mask g => (maskOrder Z).trans (((g.run k).prodCongr (Equiv.refl _)).trans (maskOrder Z).symm)
  | .head g => (Equiv.refl _).prodCongr (g.run h)
  | .localOp e => (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr e)
  | .seq a b => (a.run k h).trans (b.run k h)

def count {Z : Type} (maskBank : Bool) : Program Z → Nat
  | .mask g => if maskBank then g.cost else 0
  | .head g => if maskBank then 0 else g.cost
  | .localOp _ => 0
  | .seq a b => a.count maskBank + b.count maskBank

def reverse {Z : Type} : Program Z → Program Z
  | .mask c => .mask c.reverse
  | .head c => .head c.reverse
  | .localOp e => .localOp e.symm
  | .seq a b => .seq b.reverse a.reverse

theorem reverse_run {Z : Type} (k : MaskAddr → Capacity) (h : RateMask) (a : Program Z) :
    a.reverse.run k h = (a.run k h).symm := by
  induction a with
  | mask c => rw [reverse,run,Circuit.run_reverse]; rfl
  | head c => rw [reverse,run,Circuit.run_reverse]; rfl
  | localOp e => rfl
  | seq a b ha hb => simp only [reverse,run,ha,hb]; rfl

theorem reverse_count {Z : Type} (bank : Bool) (a : Program Z) :
    a.reverse.count bank = a.count bank := by
  induction a <;> simp [reverse,count,Circuit.reverse_cost,Nat.add_comm, *]

end Program

abbrev Work := Port × Words × Words
def onState (e : Bool → Equiv.Perm Words) : Equiv.Perm Work :=
  ⟨fun w => (w.1,w.2.1,e w.1.1 w.2.2),fun w => (w.1,w.2.1,(e w.1.1).symm w.2.2),
   fun _ => by simp, fun _ => by simp⟩

def capGate (c : Capacity) : Equiv.Perm Words := maskEquiv (fun _ => c)
def headGate (r : Rate) : Equiv.Perm Words := shearEquiv (fun _ => r)
def chooseHead (atInverse : Bool) (r : Rate) (d : Bool) : Equiv.Perm Words :=
  if d = atInverse then headGate r else Equiv.refl _

abbrev baseMask : MaskAddr := (false,0)

noncomputable def capRead (first : Bool) : Program Work :=
  .mask (lookup baseMask (fun w => (if first then w.1.1 else !w.1.1,rateOf w.2.2))
    (fun c => onState (fun _ => capGate c)))

noncomputable def headRead (atInverse : Bool) : Program Work :=
  .head (lookup 0 (fun w => capOf w.2.2) (fun r => onState (chooseHead atInverse r)))

def clean (a : Port) (y w : Words) : Reg Work :=
  ((baseMask,0),(0,0),a,y,w)

theorem capRead_clean (first : Bool) (k : MaskAddr → Capacity) (h : RateMask)
    (a : Port) (y w : Words) :
    (capRead first).run k h (clean a y w) =
      clean a y (mask (fun r => k (if first then a.1 else !a.1,r)) w) := by
  let select (w : Work) : MaskAddr := (if first then w.1.1 else !w.1.1,rateOf w.2.2)
  let act (v : Capacity) := onState (fun _ => capGate v)
  have hs (v : Capacity) (s : Work) : select (act v s) = select s := by
    change (_,rateOf (mask (fun _ => v) _)) = _
    rw [rate_mask]
    rfl
  have he := lookup_clean baseMask select act hs k (a,y,w)
  change ((maskOrder Work).symm (((lookup baseMask select act).run k) ((baseMask,0),a,y,w),((0,0):HeadReg))) = _
  rw [he]
  rfl

theorem headRead_clean (enabled : Bool) (k : MaskAddr → Capacity) (h : RateMask)
    (a : Port) (y w : Words) :
    (headRead enabled).run k h (clean a y w) =
      clean a y (if a.1 = enabled then shear h w else w) := by
  let select (w : Work) := capOf w.2.2
  let act (r : Rate) := onState (chooseHead enabled r)
  have hs (r : Rate) (s : Work) : select (act r s) = select s := by
    change capOf (chooseHead enabled r s.1.1 s.2.2) = _
    by_cases eq : s.1.1 = enabled
    · change capOf ((if s.1.1 = enabled then headGate r else Equiv.refl _) _) = _
      rw [ite_eq_left eq]
      exact cap_join ..
    · simp only [chooseHead,eq,ite_false,Equiv.refl_apply]; rfl
  have he := lookup_clean 0 select act hs h (a,y,w)
  change ((baseMask,0),((lookup 0 select act).run h) ((0,0),a,y,w)) = _
  rw [he]
  by_cases eq : a.1 = enabled <;> simp only [clean,act,onState,chooseHead,eq,ite_true,ite_false,
    Equiv.coe_fn_mk,Equiv.refl_apply] <;> rfl

def direction (π : Permutation) (d : Bool) : Permutation := if d then π.symm else π

noncomputable def round (π : Permutation) : Program Work :=
  .seq (headRead true) (.seq (capRead true) (.seq (.localOp (onState (direction π)))
    (.seq (capRead false) (headRead false))))

def bank (ki ko : Mask) : MaskAddr → Capacity := fun s => if s.1 then ko s.2 else ki s.2

theorem round_clean (π : Permutation) (ki ko : Mask) (h : RateMask) (d : Bool) (v y w : Words) :
    (round π).run (bank ki ko) h (clean (d,v) y w) =
      clean (d,v) y (oracle (salted ki ko h π) (d,w)) := by
  cases d <;> simp only [round,Program.run,Equiv.trans_apply,headRead_clean,capRead_clean,
    Bool.false_eq_true,ite_false,ite_true]
    <;> change (headRead false).run _ _ ((capRead false).run _ _ (clean _ _ _)) = _
    <;> rw [capRead_clean,headRead_clean] <;> rfl

def seed : Equiv.Perm Work := ⟨fun s => (s.1,s.2.1,s.2.2+s.1.2),
  fun s => (s.1,s.2.1,s.2.2-s.1.2),fun _ => by simp,fun _ => by simp⟩

def addAnswer : Equiv.Perm Work := ⟨fun s => (s.1,s.2.1+s.2.2,s.2.2),
  fun s => (s.1,s.2.1-s.2.2,s.2.2),fun _ => by simp,fun _ => by simp⟩

noncomputable def publicPort (π : Permutation) : Program Work :=
  .seq (.localOp seed) (.seq (round π) (.seq (.localOp addAnswer) (.seq (round π).reverse (.localOp seed.symm))))

theorem publicPort_cost (π : Permutation) :
    (publicPort π).count true = 8 ∧ (publicPort π).count false = 8 := by
  simp only [publicPort,Program.count,Program.reverse_count,round,capRead,headRead,lookup_cost]
  decide

theorem publicPort_clean (π : Permutation) (ki ko : Mask) (h : RateMask) (a : Port) (y : Words) :
    (publicPort π).run (bank ki ko) h (clean a y 0) =
      clean a (y + oracle (salted ki ko h π) a) 0 := by
  rcases a with ⟨d,v⟩
  let f := oracle (salted ki ko h π) (d,v)
  have hp := round_clean π ki ko h d v y v
  have hrev := (Equiv.symm_apply_eq (e := (round π).run (bank ki ko) h)).mpr
    (round_clean π ki ko h d v (y+f) v).symm
  change (.localOp seed.symm : Program Work).run (bank ki ko) h ((round π).reverse.run (bank ki ko) h
    ((.localOp addAnswer : Program Work).run (bank ki ko) h ((round π).run (bank ki ko) h (clean (d,v) y (0+v))))) = _
  rw [zero_add,hp,Program.reverse_run]
  change (.localOp seed.symm : Program Work).run (bank ki ko) h (((round π).run (bank ki ko) h).symm (clean (d,v) (y+f) f)) = _
  rw [hrev]
  simp [Program.run,clean,seed,f]

end Reduction.ShakePermutation.RoundPort
#print axioms Reduction.ShakePermutation.RoundPort.publicPort_clean
#print axioms Reduction.ShakePermutation.RoundPort.publicPort_cost
