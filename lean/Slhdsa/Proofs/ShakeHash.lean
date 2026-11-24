import Slhdsa.Proofs.Shake256
import Slhdsa.Proofs.ShakeAddress
open Aeneas Aeneas.Std Result
namespace slhdsa.Shake

def params (p : _root_.slhdsa.params.Params) : Spec.Params := { paramsS p with family := .shake }

def Absorbed (s : shake256.Sponge) (msg : Spec.Bytes) : Prop :=
  Keccak.view s = msg.foldl Spec.Keccak.feed Spec.Keccak.initial ∧ s.pos.val < 136

theorem empty_spec : shake256.Sponge.new ⦃ s => Absorbed s [] ⦄ := Keccak.new_spec

theorem append_spec (s : shake256.Sponge) (x : Spec.Bytes) (hs : Absorbed s x) (data : Slice U8) :
    shake256.Sponge.absorb s data ⦃ out => Absorbed out (x ++ bytes data.val) ⦄ := by
  apply WP.spec_mono (Keccak.absorb_spec s data hs.2)
  intro s' h
  exact ⟨by rw [h.1, hs.1, List.foldl_append], h.2⟩

theorem digest_spec (n : Usize) (s : shake256.Sponge) (x : Spec.Bytes) (hs : Absorbed s x) :
    shake.hash.digest n s ⦃ out => bytes out.val = Spec.shake256 x n.val ⦄ := by
  unfold shake.hash.digest
  simp only [lift, bind_ok, Array.to_slice_mut]
  let* ⟨buf, hbuf⟩ ← Keccak.finish_spec s _ hs.2
  have h : bytes buf.val = Spec.shake256 x n.val := by
    simpa only [Spec.shake256, hs.1, Slice.length, Array.val_to_slice, Array.length_eq] using hbuf
  have len : buf.val.length = n.val := by simpa using congrArg List.length h
  simpa only [WP.spec_ok, Array.from_slice_val _ _ len] using h

@[step] theorem start_spec {N : Usize} (pk : Array U8 N) (a : address.Adrs) :
    shake.hash.start pk a ⦃ s => Absorbed s (bytes pk.val ++ (adrsS a).bytes) ⦄ := by
  unfold shake.hash.start
  simp only [lift, bind_ok]
  let* ⟨s, hs⟩ ← empty_spec
  let* ⟨s1, hs1⟩ ← append_spec s _ hs
  let* ⟨addr, haddr⟩ ← adrs_full_spec
  simpa only [List.nil_append, Array.val_to_slice, haddr] using
    append_spec s1 _ hs1 addr.to_slice

@[step] theorem thash_spec {N : Usize} (pk : Array U8 N) (a : address.Adrs) (v : Array U8 N) :
    shake.hash.thash pk a v ⦃ out => bytes out.val =
      Spec.shake256 (bytes pk.val ++ (adrsS a).bytes ++ bytes v.val) N.val ⦄ := by
  unfold shake.hash.thash
  let* ⟨s, hs⟩ ← start_spec
  simp only [lift, bind_ok]
  let* ⟨s1, hs1⟩ ← append_spec s _ hs
  simpa only [Array.val_to_slice] using digest_spec N s1 _ hs1

@[step] theorem pair_spec {N : Usize} (pk : Array U8 N) (a : address.Adrs) (l r : Array U8 N) :
    shake.hash.thash_pair pk a l r ⦃ out => bytes out.val =
      Spec.shake256 (bytes pk.val ++ (adrsS a).bytes ++ (bytes l.val ++ bytes r.val)) N.val ⦄ := by
  unfold shake.hash.thash_pair
  let* ⟨s, hs⟩ ← start_spec
  simp only [lift, bind_ok]
  let* ⟨s1, h1⟩ ← append_spec s _ hs
  let* ⟨s2, h2⟩ ← append_spec s1 _ h1
  simpa only [Array.val_to_slice, List.append_assoc] using digest_spec N s2 _ h2

@[step] theorem prf_msg_spec {N : Usize} (k r : Array U8 N) (m : Slice U8) :
    shake.hash.prf_msg k r m ⦃ out => bytes out.val =
      Spec.shake256 (bytes k.val ++ bytes r.val ++ bytes m.val) N.val ⦄ := by
  unfold shake.hash.prf_msg
  simp only [lift, bind_ok]
  let* ⟨s, hs⟩ ← empty_spec
  let* ⟨s1, h1⟩ ← append_spec s _ hs
  let* ⟨s2, h2⟩ ← append_spec s1 _ h1
  let* ⟨s3, h3⟩ ← append_spec s2 _ h2
  simpa only [Array.val_to_slice, List.nil_append] using digest_spec N s3 _ h3

@[step] theorem h_msg_spec {N : Usize} (p : _root_.slhdsa.params.Params)
    (r pk root : Array U8 N) (m : Slice U8) :
    shake.hash.h_msg p r pk root m ⦃ out => bytes out.val =
      Spec.shake256 (bytes r.val ++ bytes pk.val ++ bytes root.val ++ bytes m.val) p.m.val ⦄ := by
  unfold shake.hash.h_msg
  simp only [lift, bind_ok]
  let* ⟨s, hs⟩ ← empty_spec
  let* ⟨s1, h1⟩ ← append_spec s _ hs
  let* ⟨s2, h2⟩ ← append_spec s1 _ h1
  let* ⟨s3, h3⟩ ← append_spec s2 _ h2
  let* ⟨s4, h4⟩ ← append_spec s3 _ h3
  step*
  simp only [alloc.vec.Vec.deref_mut]
  let* ⟨buf, hb⟩ ← Keccak.finish_spec s4 out.slice h4.2
  change bytes buf.val = _
  change out.slice.length = p.m.val at out_post1
  simpa only [Spec.shake256, h4.1, Array.val_to_slice, List.nil_append, out_post1] using hb

end slhdsa.Shake

#print axioms slhdsa.Shake.thash_spec
#print axioms slhdsa.Shake.pair_spec
#print axioms slhdsa.Shake.prf_msg_spec
#print axioms slhdsa.Shake.h_msg_spec
