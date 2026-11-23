import Wots.Pack
import Slhdsa.Proofs.Platform
import Leaf256.Block
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem bind_congr {A B : Type} (x : Result A) {f g : A → Result B}
    (h : ∀ a, f a = g a) : Std.bind x f = Std.bind x g := by rw [funext h]

private theorem through_bind {A B C : Type} {x : Result A} {f : A → Result B} {g : B → Result C}
    {h : A → Result C} (eq : ∀ v, h v = Std.bind (f v) g) :
    Std.bind x h = Std.bind (Std.bind x f) g := by
  rw [Std.bind_assoc]
  exact bind_congr _ eq

theorem step_eq (N : Usize) (iv : Hash) (half : Reg) (pre : Hash)
    (it : core.ops.range.Range I32) (w : Words) (hash : Hash) :
    wots_endpoints_loop1_loop0.body N iv half pre it w hash = (do
      let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepI32 it
      match o with
      | none => ok (done hash)
      | some t =>
        let words ← pack N w hash t half
        let out ← PlatformRust.sha256.x86.avx512.compress iv pre words
        ok (cont (next,words,out))) := by
  unfold wots_endpoints_loop1_loop0.body pack packHigh PlatformRust.sha256.x86.avx512.compress
  apply bind_congr
  rintro ⟨o,next⟩
  cases o with
  | none => rfl
  | some t =>
    iterate 16
      apply through_bind
      intro x
    apply bind_congr
    intro words
    iterate 60
      apply through_bind
      rintro ⟨a,b⟩
    iterate 24
      apply through_bind
      intro x
    rw [bind_ok]

def message (N : Usize) (w : Words) (h : Hash) (t : I32) (j : Fin 16) :=
  Leaf.blockOf (packedWord (fun i => w.val[i]! j) (fun i => h.val[i]! j) N.val t.bv)

/-- One live endpoint iteration updates the packed words and performs the FIPS
180-4 compression, independently for every lane. -/
theorem step_spec (N : Usize) (iv pre : Hash) (it next : core.ops.range.Range I32)
    (w : Words) (h : Hash) (t : I32) (shape : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepI32 it = ok (some t,next))
    (prefixOK : Trace pre (fun j => Spec.SHA256.schedule (message N w h t j)) (laneState iv) 4) :
    wots_endpoints_loop1_loop0.body N iv (fun _ => 0xffff) pre it w h ⦃ flow =>
      ∃ words out, flow = cont (next,words,out) ∧
        (∀ k < 16, ∀ j, words.val[k]! j = packedWord (fun i => w.val[i]! j) (fun i => h.val[i]! j) N.val t.bv k) ∧
        ∀ j, stateWords (laneState out j) = Spec.SHA256.compress (stateWords (laneState iv j)) (message N w h t j) ⦄ := by
  rw [step_eq,advance]
  simp only [bind_ok]
  step with pack_spec N w h t shape as ⟨words,hw⟩
  step with compress_block_spec iv pre words (message N w h t) prefixOK
    (fun k hk j => by rw [hw k hk j,message,Leaf.word_blockOf _ _ hk]) as ⟨out,hh⟩
  exact ⟨words,out,rfl,hw,hh⟩
end slhdsa.X86.Wots
