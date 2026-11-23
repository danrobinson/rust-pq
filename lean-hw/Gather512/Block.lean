import Gather512.Read
import Parent512.Compress
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.sha512.x86
open _root_.core.core_arch.x86

def laneBlock {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 8) (off : Nat) :=
  if j.val < rows.length then (bytes rows.val[j.val]!.val).slice off (off+128) else []

theorem word_at {L : Usize} (rows : Slice (Array U8 L)) (j : Fin 8) (off k : Nat)
    (hoff : off+128 ≤ L.val) (hk : k < 16) :
    laneWord rows j (off+8*k) = Spec.SHA512.word (laneBlock rows j off) (8*k) := by
  unfold laneWord laneBlock
  split
  · have len : (bytes rows.val[j.val]!.val).length = L.val := by simp
    have get (t : Nat) (ht : t < 128) :=
      List.getElem!_slice off (off+128) t (bytes rows.val[j.val]!.val) (by omega)
    simp (disch := omega) only [Spec.SHA512.word,get,Nat.add_assoc]
  · simp [Spec.SHA512.word,List.getElem!_eq_getElem?_getD]; rfl

theorem words_spec (N L : Usize) (rows : Slice (Array U8 L)) (mask : U8) (stride : __m256i) (off : Usize)
    (hm : Mask mask rows.length) (hs : Stride stride L.val) (hn : 0 < rows.length) (hoff : off.val+128 ≤ L.val) :
    core.array.from_fn 16#usize (digest_groups.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N L)
      (mask,stride,rows,off,swapControl) ⦃ w => ∀ k, k < 16 → ∀ j : Fin 8,
        word64 w.val[k]! j = Spec.SHA512.word (laneBlock rows j off.val) (8*k) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize
    (digest_groups.closure_1.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N L) _
    (fun k v => ∀ j : Fin 8, word64 v j = laneWord rows j (off.val+8*k))
    (fun k hk => read_spec N L rows mask stride off k hm hs hn hk hoff))
  intro a ha k hk j
  simpa only [Array.getElem!_Nat_eq, word_at _ _ _ _ hoff hk] using ha k hk j

private theorem same_step (i : Usize) (s : Array Reg 8#usize) (w : Array Reg 16#usize) :
    compression_step i s w = PlatformRust.sha512.x86.compression_step i s w := by
  have h : GatherRust.sha512.K = PlatformRust.sha512.K := by unfold GatherRust.sha512.K PlatformRust.sha512.K; rfl
  simp only [compression_step, PlatformRust.sha512.x86.compression_step, h]

set_option maxRecDepth 8000 in
theorem compress_eq (s : Array Reg 8#usize) (w : Array Reg 16#usize) :
    compress s w = PlatformRust.sha512.x86.compress s w := by
  simp only [compress, PlatformRust.sha512.x86.compress, same_step]

#print axioms words_spec
end slhdsa.X86.S512.Gather
