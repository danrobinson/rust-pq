import Parentdriver.PathDispatch
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

theorem x86_tree_spec {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs)
    (s : Array U64 8#usize) (first : U32) (v : Nodes N) (count : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val)
    (hv : 2*count.val ≤ v.length) (hi : first.val + count.val ≤ 2^32) :
    Parentx86Rust.sha512.parents.parents s a first v count ⦃ n r =>
      n.val = processed GatherRust.avx512Available count.val 8 ∧ Reduced p pk a first v r n.val ⦄ := by
  rw [tree_x86]
  exact tree_parents x86 GatherRust.avx512Available p pk a s first v count shape rfl
    (fun _ => x86_correct p pk s shape fam width hlen hs) (by decide) hv hi

theorem x86_path_spec {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs)
    (s : Array U64 8#usize) (v : Nodes N) (idx : Slice U32) (sig : Slice U8) (h off : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val)
    (hi : v.length ≤ idx.length) (hh : h.val+1 ≤ Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    Parentx86Rust.sha512.parents.path_parents s a v idx sig h off ⦃ n r ix =>
      n.val = processed GatherRust.avx512Available v.length 8 ∧ Paths p pk a v idx sig h.val off.val n.val r ix ⦄ := by
  rw [path_x86]
  exact path_parents x86 GatherRust.avx512Available p pk a s v idx sig h off shape rfl
    (fun _ => x86_correct p pk s shape fam width hlen hs) (by decide) hi hh bounds

theorem arm_tree_spec {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs)
    (s : Array U64 8#usize) (first : U32) (v : Nodes N) (count : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val)
    (hv : 2*count.val ≤ v.length) (hi : first.val + count.val ≤ 2^32) :
    ParentarmRust.sha512.parents.parents s a first v count ⦃ n r =>
      n.val = processed Arm.haveSha512 count.val 2 ∧ Reduced p pk a first v r n.val ⦄ := by
  rw [tree_arm]
  exact tree_parents arm Arm.haveSha512 p pk a s first v count shape rfl
    (fun hw => arm_correct p pk s hw shape fam width hlen hs) (by decide) hv hi

theorem arm_path_spec {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : address.Adrs)
    (s : Array U64 8#usize) (v : Nodes N) (idx : Slice U32) (sig : Slice U8) (h off : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val)
    (hi : v.length ≤ idx.length) (hh : h.val+1 ≤ Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    ParentarmRust.sha512.parents.path_parents s a v idx sig h off ⦃ n r ix =>
      n.val = processed Arm.haveSha512 v.length 2 ∧ Paths p pk a v idx sig h.val off.val n.val r ix ⦄ := by
  rw [path_arm]
  exact path_parents arm Arm.haveSha512 p pk a s v idx sig h off shape rfl
    (fun hw => arm_correct p pk s hw shape fam width hlen hs) (by decide) hi hh bounds

#print axioms x86_tree_spec
#print axioms x86_path_spec
#print axioms arm_tree_spec
#print axioms arm_path_spec
end slhdsa.PlatformParent.Driver
