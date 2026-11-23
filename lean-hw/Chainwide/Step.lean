import Chainwide.Prefix
import Chainwide.Counters
import Chainvectors.Words
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainWideRust
open ChainWideRust.sha256.x86.avx512
abbrev ChainStep := Result (ControlFlow (Reg × U16 × Array Reg 8#usize × Array Reg 16#usize) Rows)

def finishStep (N : Usize) (endsSlice : Slice U32) (offset : Usize) (batch : Rows) (ends : Reg)
    (original : U16) (half counter : Reg) (active : U16) (saved : Array Reg 8#usize) (words1 : Array Reg 16#usize)
    (hash : Array Reg 8#usize) : ChainStep := do
  let one ← core.core_arch.x86.avx512f._mm512_set1_epi32 1#i32
  let next ← core.core_arch.x86.avx512f._mm512_add_epi32 counter one
  let atEnd ← core.core_arch.x86.avx512f._mm512_cmpeq_epi32_mask next ends
  let finished ← lift (active &&& atEnd)
  if finished != 0#u16 then
    if finished = original then
      let tail ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U32)
        endsSlice { start := offset }
      let out ← write_finished N hash batch tail finished
      ok (done out)
    else
      let retained ← chain_done N saved hash finished
      let keep ← lift (~~~ finished)
      let remaining ← lift (active &&& keep)
      if remaining = 0#u16 then
        let tail ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U32)
          endsSlice { start := offset }
        let out ← write_finished N retained batch tail original
        ok (done out)
      else
        let words ← chain_value N words1 hash half
        ok (cont (next, remaining, retained, words))
  else
    let words ← chain_value N words1 hash half
    ok (cont (next, active, saved, words))

private theorem bind_congr {A B : Type} (x : Result A) {f g : A → Result B}
    (h : ∀ a, f a = g a) : Std.bind x f = Std.bind x g := by rw [funext h]

private theorem through_bind {A B C : Type} {x : Result A} {f : A → Result B} {g : B → Result C}
    {h : A → Result C} (eq : ∀ v, h v = Std.bind (f v) g) :
    Std.bind x h = Std.bind (Std.bind x f) g := by
  rw [Std.bind_assoc]
  exact bind_congr _ eq

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem step_eq (N : Usize) (e : Slice U32) (iv : Array Reg 8#usize) (off : Usize) (b : Rows) (ends : Reg)
    (orig : U16) (fixed half : Reg) (pre : Array Reg 8#usize) (counter : Reg) (active : U16)
    (saved : Array Reg 8#usize) (words : Array Reg 16#usize) :
    chains_loop0_loop1.body N e iv off b ends orig fixed half pre counter active saved words = (do
      let w ← chain_address words fixed counter half
      let hash ← PlatformRust.sha256.x86.avx512.compress iv pre w
      finishStep N e off b ends orig half counter active saved w hash) := by
  unfold chains_loop0_loop1.body PlatformRust.sha256.x86.avx512.compress
  apply bind_congr
  intro w
  iterate 60
    apply through_bind
    rintro ⟨a,b⟩
  iterate 24
    apply through_bind
    intro x
  rw [bind_ok]
  rfl

/-- The two copies introduced by extraction for the short-batch feature branch
execute the same inner loop. -/
theorem same_step : @chains_loop0_loop3.body = @chains_loop0_loop1.body := rfl

theorem compression_step_spec (N : Usize) (endsSlice : Slice U32) (iv : Array Reg 8#usize)
    (off : Usize) (batch : Rows) (ends : Reg) (orig : U16) (fixed : Reg) (pre : Array Reg 8#usize)
    (counter : Reg) (active : U16) (saved : Array Reg 8#usize) (words : Array Reg 16#usize)
    (blocks : Fin 16 → Spec.Bytes) (P : ControlFlow (Reg × U16 × Array Reg 8#usize × Array Reg 16#usize) Rows → Prop)
    (trace : Trace pre (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 4)
    (message : ∀ k, k < 16 → ∀ j, addressWord (fun t => words.val[t]! j) (fixed j) (counter j) k =
      Spec.SHA256.word (blocks j) (4*k))
    (finish : ∀ (w : Array Reg 16#usize) (h : Array Reg 8#usize),
      (∀ k, k < 16 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) →
      (∀ j, stateWords (laneState h j) = Spec.SHA256.compress (stateWords (laneState iv j)) (blocks j)) →
      finishStep N endsSlice off batch ends orig (fun _ => 0xffff) counter active saved w h ⦃ x => P x ⦄) :
    chains_loop0_loop1.body N endsSlice iv off batch ends orig fixed (fun _ => 0xffff) pre counter active saved words
      ⦃ x => P x ⦄ := by
  rw [step_eq]
  apply WP.spec_bind (address_spec words fixed counter)
  intro w hw
  have packed k hk j := (hw k hk j).trans (message k hk j)
  apply WP.spec_bind (compress_block_spec iv pre w blocks trace packed)
  exact fun h hh => finish w h packed hh

end slhdsa.X86.Chain
