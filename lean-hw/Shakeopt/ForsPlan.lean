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
