import Chainwide.Step
import Chainwrite.Top
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain

def Rendered (N : Usize) (ends : Slice U32) (offset : Usize) (mask : U16) (hash : Hash) (before out : Rows) :=
  out.length = before.length ∧ ∀ k < before.length, bytes out.val[k]!.val =
    if h : mask.bv.getLsbD k then
      (bytes before.val[k]!.val).take 18 ++ Spec.toByte (ends.val[offset.val+k]!.val-1) 4 ++
        digestPart hash ⟨k,by
          by_contra! large
          exact Bool.noConfusion ((BitVec.getLsbD_of_ge _ k large).symm.trans h)⟩ 0 N.val ++
        (bytes before.val[k]!.val).drop (22+N.val)
    else bytes before.val[k]!.val

theorem flush_spec (N : Usize) (ends : Slice U32) (offset : Usize) (batch : Rows) (mask : U16) (hash : Hash)
    (hn : N.val ≤ 32) (he : offset.val+batch.length ≤ ends.length) (hb : Covers mask batch.length)
    (positive : ∀ k, mask.bv.getLsbD k → 0 < ends.val[offset.val+k]!.val) :
    flush N ends offset batch mask hash ⦃ flow => ∃ out, flow = done out ∧ Rendered N ends offset mask hash batch out ⦄ := by
  unfold flush
  step as ⟨tail,eq,len⟩
  have covers : Covers mask tail.length := by intro k hk; have := hb k hk; omega
  have pos k (h : mask.bv.getLsbD k = true) : 0 < tail.val[k]!.val := by
    simpa only [eq,List.getElem!_drop] using positive k h
  step with write_finished_spec N hash batch tail mask hn hb covers pos as ⟨out,lo,rows⟩
  refine ⟨_,rfl,lo,?_⟩
  simpa only [eq,List.getElem!_drop] using rows
end slhdsa.X86.Chain
