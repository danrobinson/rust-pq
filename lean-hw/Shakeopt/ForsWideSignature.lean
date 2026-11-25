import Shakeopt.ForsPlan
import Shakeopt.ForsTree
namespace Shakeopt.ForsWideSignature
open Spec ForsPlan

abbrev Parent := Bool → Nat → Nat → Bytes → Bytes → Bytes

/-- The first three levels use across-tree batches. Higher levels use the
    production horizontal traversal with its single and packed reductions. -/
def subtree (leaf : Nat → Bytes) (parent : Parent) (h i : Nat) : Bytes :=
  let first := fun k => parent true 1 k (leaf (2*k)) (leaf (2*k+1))
  match h with
  | 0 => leaf i
  | 1 => first i
  | 2 => parent true 2 i (first (2*i)) (first (2*i+1))
  | h+3 => ForsTree.root leaf parent (h+3) i

def execute (p : Params) (md : Bytes) (secret leaf : Nat → Bytes) (parent : Parent)
    (fields : List Field) : Bytes :=
  let pick := fun j => (base2b md p.a p.k)[j]!
  fields.flatMap fun (op,x) => match op with
    | .secret => secret (x.eval pick)
    | .node h => subtree leaf parent h (x.eval pick)

theorem sign_fips (p : Params) (md sk pk : Bytes) (a : Adrs) (height : p.a ≤ 14)
    (secret leaf : Nat → Bytes) (parent : Parent)
    (secrets : ∀ i, secret i=forsSkGen p sk pk a i)
    (leaves : ∀ i, leaf i=F p pk {a with word2:=0,word3:=i} (secret i))
    (parents : ∀ packed h i l r, parent packed (h+1) i l r=H p pk {a with word2:=h+1,word3:=i} (l++r)) :
    execute p md secret leaf parent (canonical p false)=forsSign p md sk pk a := by
  rw [←render_fips false]
  unfold execute render
  apply List.flatMap_congr
  rintro ⟨op,x⟩ mem
  cases op with
  | secret => exact secrets _
  | node h =>
    have bound : h<p.a := by
      simp only [canonical,List.mem_flatMap,List.mem_cons,List.mem_map] at mem
      obtain ⟨t,_,m⟩ := mem
      rcases m with impossible | ⟨n,hn,eq⟩
      · cases impossible
      · cases eq; exact List.mem_range.mp hn
    have value (i : Nat) : leaf i = F p pk {a with word2:=0,word3:=i} (forsSkGen p sk pk a i) := by rw [leaves,secrets]
    rcases h with _|h
    · exact value _
    rcases h with _|h
    · simp only [subtree,parents,value,forsNode]
    rcases h with _|h
    · simp only [subtree,parents,value,forsNode]
    exact ForsTree.root_fips p sk pk a leaf parent value parents _ _ (by omega) (by omega)

def signature (p : Params) (md sk pk : Bytes) (a : Adrs) : Bytes :=
  let secret := forsSkGen p sk pk a
  let leaf := fun i => F p pk {a with word2:=0,word3:=i} (secret i)
  let parent := fun (_ : Bool) h i l r => H p pk {a with word2:=h,word3:=i} (l++r)
  execute p md secret leaf parent (canonical p false)

theorem signature_eq (p : Params) (md sk pk : Bytes) (a : Adrs) (height : p.a≤14) :
    signature p md sk pk a = forsSign p md sk pk a :=
  sign_fips p md sk pk a height _ _ _ (fun _=>rfl) (fun _=>rfl) (fun _ _ _ _ _=>rfl)
end Shakeopt.ForsWideSignature
