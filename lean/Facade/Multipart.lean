import Facade.Funs
import Slhdsa.Proofs.Sha256

open Aeneas Aeneas.Std Result

namespace slh_dsa.multipart

private def prefixBytes (parts : Slice (Slice U8)) (i : Nat) : List U8 :=
  (parts.val.take i).flatMap (fun (s : Slice U8) => s.val)

private theorem prefix_succ (parts : Slice (Slice U8)) (i : Nat) (hi : i < parts.val.length) :
    prefixBytes parts (i + 1) = prefixBytes parts i ++ parts.val[i].val := by
  unfold prefixBytes
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
  simp

private theorem prefix_len (parts : Slice (Slice U8)) (i : Nat) :
    (prefixBytes parts i).length ≤ (parts.val.flatMap (fun (s : Slice U8) => s.val)).length := by
  have h := congrArg (fun l : List (Slice U8) => (l.flatMap (fun (s : Slice U8) => s.val)).length)
    (List.take_append_drop i parts.val)
  simp only [List.flatMap_append, List.length_append] at h
  unfold prefixBytes
  omega

private theorem append_range_spec (parts : Slice (Slice U8)) (lo hi : Usize)
    (out : alloc.vec.Vec U8) (order : lo.val ≤ hi.val) (bound : hi.val ≤ parts.length)
    (fits : (parts.val.flatMap (fun (s : Slice U8) => s.val)).length ≤ Usize.max)
    (init : out.val = prefixBytes parts lo.val) :
    append_range parts lo hi out ⦃ r => r.val = prefixBytes parts hi.val ⦄ := by
  rw [append_range]
  step as ⟨count, hc⟩
  split
  · rename_i one
    have he : hi.val = lo.val + 1 := by scalar_tac
    have hl : lo.val < parts.val.length := by change hi.val ≤ parts.val.length at bound; omega
    rw [he, prefix_succ _ _ hl]
    step as ⟨part, hp⟩
    have fitPart : out.length + part.length ≤ Usize.max := by
      have h := prefix_len parts (lo.val + 1)
      rw [prefix_succ _ _ hl, List.length_append] at h
      simpa [alloc.vec.Vec.length, Slice.length, init, hp] using h.trans fits
    simpa [init, hp] using slhdsa.extend_from_slice_u8_spec out part fitPart
  · split
    · rename_i gt
      step as ⟨half, hh⟩
      step as ⟨mid, hm⟩
      have left : lo.val < mid.val := by scalar_tac
      have right : mid.val < hi.val := by scalar_tac
      apply WP.spec_bind (append_range_spec parts lo mid out (by omega) (by omega) fits init)
      intro buf hb
      exact append_range_spec parts mid hi buf (by omega) bound fits hb
    · have : hi.val = lo.val := by scalar_tac
      simp [this, init]
termination_by hi.val - lo.val
decreasing_by all_goals omega

/-- The adapter passes every part in order, including empty parts, to the byte-level core. -/
theorem join_spec (parts : Slice (Slice U8))
    (fits : (parts.val.flatMap (fun (s : Slice U8) => s.val)).length ≤ Usize.max) :
    join parts ⦃ r => r.val = parts.val.flatMap (fun (s : Slice U8) => s.val) ⦄ := by
  unfold join
  simpa [prefixBytes, Slice.len, Slice.length] using
    append_range_spec parts 0#usize parts.len (alloc.vec.Vec.new U8)
      (by scalar_tac) (by scalar_tac) fits (by simp [prefixBytes, alloc.vec.Vec.new])

#print axioms join_spec
end slh_dsa.multipart
