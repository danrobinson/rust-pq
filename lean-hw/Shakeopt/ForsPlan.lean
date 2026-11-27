import Shakeopt.ForsHoriz

namespace Shakeopt.ForsPlan
open Spec

inductive Index where
  | lit (n : Nat)
  | sel (tree : Nat)
  | add (x y : Index)
  | mul (k : Nat) (x : Index)
  | shr (x : Index) (height : Nat)
  | xor (x : Index) (mask : Nat)
  deriving DecidableEq, Repr

def Index.eval (pick : Nat → Nat) : Index → Nat
  | .lit n => n
  | .sel t => pick t
  | .add x y => x.eval pick + y.eval pick
  | .mul k x => k*x.eval pick
  | .shr x h => x.eval pick / 2^h
  | .xor x m => x.eval pick ^^^ m

/-- A conservative upper bound at every intermediate. Every subtree must fit a Rust
    u32 before its parent can use it. The XOR cap covers all FIPS FORS tree indices. -/
def Index.bound (maxDigit : Nat) : Index → Option Nat
  | .lit n => if n < 2^32 then some n else none
  | .sel _ => if maxDigit < 2^32 then some maxDigit else none
  | .add x y => do
      let a ← x.bound maxDigit
      let b ← y.bound maxDigit
      if a+b < 2^32 then some (a+b) else none
  | .mul k x => do
      let a ← x.bound maxDigit
      if k*a < 2^32 then some (k*a) else none
  | .shr x h => do
      let a ← x.bound maxDigit
      if h < 32 then some (a/2^h) else none
  | .xor x m => do
      let a ← x.bound maxDigit
      if a < 2^22 ∧ m < 2^22 then some (2^22-1) else none

theorem Index.bound_sound (pick : Nat → Nat) (limit : Nat) (digits : ∀ j, pick j ≤ limit)
    (x : Index) (b : Nat) (checked : x.bound limit = some b) :
    x.eval pick ≤ b ∧ b < 2^32 := by
  induction x generalizing b with
  | lit n => simp only [bound] at checked; split at checked <;> simp_all [eval]
  | sel t => simp only [bound] at checked; split at checked <;> simp_all [eval]
  | add x y ix iy =>
    cases hx : x.bound limit <;> cases hy : y.bound limit <;> simp [bound,hx,hy] at checked
    obtain ⟨bounds,rfl⟩ := checked
    exact ⟨Nat.add_le_add (ix _ hx).1 (iy _ hy).1,by assumption⟩
  | mul k x ih =>
    cases hx : x.bound limit <;> simp [bound,hx] at checked
    obtain ⟨bounds,rfl⟩ := checked
    exact ⟨Nat.mul_le_mul_left _ (ih _ hx).1,by assumption⟩
  | shr x h ih =>
    cases hx : x.bound limit <;> simp [bound,hx] at checked
    obtain ⟨bounds,rfl⟩ := checked
    exact ⟨Nat.div_le_div_right (ih _ hx).1,(Nat.div_le_self ..).trans_lt (ih _ hx).2⟩
  | xor x m ih =>
    cases hx : x.bound limit <;> simp [bound,hx] at checked
    obtain ⟨bounds,rfl⟩ := checked
   

    have lt := Nat.xor_lt_two_pow (n:=22) ((ih _ hx).1.trans_lt bounds.1) bounds.2
    exact ⟨by change x.eval pick ^^^ m ≤ _;omega,by decide⟩

inductive Op where
  | secret
  | node (height : Nat)
  deriving DecidableEq, Repr

abbrev Field := Op × Index

def render (p : Params) (md sk pk : Bytes) (a : Adrs) (plan : List Field) : Bytes :=
  let pick := fun i => (base2b md p.a p.k)[i]!
  plan.flatMap fun (op, idx) => match op with
    | .secret => forsSkGen p sk pk a (idx.eval pick)
    | .node h => forsNode p sk (idx.eval pick) h pk a

def canonical (p : Params) (shiftZero : Bool) : List Field :=
  (List.range p.k).flatMap fun i =>
    let leaf : Index := .add (.lit (i*2^p.a)) (.sel i)
    (.secret,leaf) :: (List.range p.a).map fun h =>
      (.node h,.xor (if h=0 ∧ shiftZero=false then leaf else .shr leaf h) 1)

theorem render_fips (shiftZero : Bool) (p : Params) (md sk pk : Bytes) (a : Adrs) :
    render p md sk pk a (canonical p shiftZero) = forsSign p md sk pk a := by
  unfold render canonical forsSign
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro tree _
  simp only [List.flatMap_cons, List.flatMap_map, Index.eval]
  congr 1
  apply List.flatMap_congr
  intro h hh
  have eq := ForsHoriz.fors_sibling_index tree p.a (base2b md p.a p.k)[tree]! h (List.mem_range.mp hh)
  by_cases hz : h=0
  · subst h
    cases shiftZero <;> simpa [Index.eval] using congrArg (fun i => forsNode p sk i 0 pk a) eq
  · simpa [hz,Index.eval] using congrArg (fun i => forsNode p sk i h pk a) eq

end Shakeopt.ForsPlan
