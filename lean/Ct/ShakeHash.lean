import Ct.ShakeSponge

/-! Component hash traces for equal-length messages and arbitrary seeds and digest values. -/

open Aeneas Aeneas.Std Ct slhdsa_leak

namespace Ct.Shake

@[ct_rel] theorem digest (N : Usize) (a b : slhdsa.shake256.Sponge) (h : a.pos = b.pos) :
    Rel (shake.hash.digest N a) (shake.hash.digest N b) (fun _ _ => True) := by
  unfold shake.hash.digest
  ct_steps

@[ct_rel] theorem start {N : Usize} (a b : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.hash.start a adrs) (shake.hash.start b adrs) (fun x y => x.pos = y.pos) := by
  unfold shake.hash.start
  ct_steps

@[ct_rel] theorem thash {N : Usize} (s s' x x' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.hash.thash s adrs x) (shake.hash.thash s' adrs x') (fun _ _ => True) := by
  unfold shake.hash.thash
  ct_steps

@[ct_rel] theorem thash_pair {N : Usize} (s s' x x' y y' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.hash.thash_pair s adrs x y) (shake.hash.thash_pair s' adrs x' y') (fun _ _ => True) := by
  unfold shake.hash.thash_pair
  ct_steps

@[ct_rel] theorem hash2 {N : Usize} (s s' x x' y y' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.xmss.hash2 s adrs x y) (shake.xmss.hash2 s' adrs x' y') (fun _ _ => True) :=
  thash_pair s s' x x' y y' adrs

@[ct_rel] theorem prf_msg {N : Usize} (sk sk' r r' : Array U8 N) (m m' : Slice U8)
    (hm : m.length = m'.length) :
    Rel (shake.hash.prf_msg sk r m) (shake.hash.prf_msg sk' r' m') (fun _ _ => True) := by
  unfold shake.hash.prf_msg
  ct_steps

@[ct_rel] theorem h_msg {N : Usize} (p : slhdsa.params.Params) (r r' s s' k k' : Array U8 N)
    (m m' : Slice U8) (hm : m.length = m'.length) :
    Rel (shake.hash.h_msg p r s k m) (shake.hash.h_msg p r' s' k' m') (fun x y => x.length = y.length) := by
  unfold shake.hash.h_msg
  ct_steps
  simp_all [alloc.vec.Vec.deref_mut, alloc.vec.Vec.length]
  rename_i h _
  rwa [← h.2]

end Ct.Shake
