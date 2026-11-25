import Fused.Program
import Cachepath.NativeVerify.WotsPack
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused
open ShakeBatch
variable [kernel : Kernel]
local instance prefixMachine : Machine := machine kernel

/-- The actual fused T_len seed loop broadcasts each little-endian seed word
to all eight lanes and preserves every other word of the sponge matrix. -/
theorem seed_prefix (n : Usize) (sw : Array U64 4#usize) (pk : Matrix 8#usize) (cap : n.val ≤ 4) :
    xmss_sign_batch_loop1 ⟨0#usize,n⟩ sw pk ⦃ out => ∀ k l, l < 8 →
      cell out k l = if k < n.val then sw.val[k]!.bv else cell pk k l ⦄ := by
  unfold xmss_sign_batch_loop1
  apply range_fold (fun it s => xmss_sign_batch_loop1.body sw it s) n pk (fun i s =>
    ∀ k l, l < 8 → cell s k l = if k < i then sw.val[k]!.bv else cell pk k l)
  · simp
  · intro it st stop live prior
    unfold xmss_sign_batch_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step as ⟨word,read⟩
    step as ⟨out,write⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    intro k l hl
    have broadcast : cell (st.set it.start (Array.repeat 8#usize word)) k l =
        if k=it.start.val then word.bv else cell st k l :=
      @NativeVerify.Wots.broadcast (machine kernel) st it.start word k l (by omega) hl
    rw [write,broadcast,prior k l hl,inc,read,← getElem!_pos]
    split_ifs <;> first | rfl | omega | (congr 2 <;> omega)
  · intro it st last stop
    unfold xmss_sign_batch_loop1.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last,stop]))
    simp [no,tag]

end slhdsa.Fused
