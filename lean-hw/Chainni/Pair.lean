import Chainni.Words
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Intel.Chain
open ChainNiRust.sha256.x86

def pairStep (N limit : Usize) (iv : Array Reg 2#usize) (starts : Slice U32)
    (t : U32) (pair : Rows) := do
  let left ← setIndex pair starts t 0#usize
  let both ← setIndex left starts t 1#usize
  let l ← Slice.index_usize both 0#usize
  let r ← Slice.index_usize both 1#usize
  let hashes ← ChainNiRust.sha256.x86.compress_pair iv l r
  let left ← putDigest N limit 0#usize hashes both
  putDigest N limit 1#usize hashes left

theorem pair_step_spec (N limit : Usize) (iv : Array Reg 2#usize) (starts : Slice U32)
    (t : U32) (pair : Rows) (hn : N.val ≤ 32) (hl : limit.val = 22+N.val)
    (hp : pair.length = 2) (hs : starts.length = 2)
    (bound : ∀ j < 2, starts.val[j]!.val + t.val ≤ U32.max) :
    pairStep N limit iv starts t pair ⦃ r => r.length = 2 ∧ ∀ j < 2, bytes r.val[j]!.val =
      stepBlock N.val (stateWords (packedState iv)) (bytes pair.val[j]!.val) (starts.val[j]!.val + t.val) ⦄ := by
  unfold pairStep
  step with set_index_spec pair starts t 0#usize (by scalar_tac) (by scalar_tac) (bound 0 (by decide)) as ⟨left,hleft,ol,bl⟩
  step with set_index_spec left starts t 1#usize (by scalar_tac) (by scalar_tac) (bound 1 (by decide)) as ⟨both,hboth,ob,br⟩
  have b0 : bytes both.val[0]!.val = withIndex (bytes pair.val[0]!.val) (starts.val[0]!.val+t.val) := by
    rw [ob 0 (by decide)]; exact bl
  have b1 : bytes both.val[1]!.val = withIndex (bytes pair.val[1]!.val) (starts.val[1]!.val+t.val) := by
    change bytes both.val[1]!.val = withIndex (bytes left.val[1]!.val) (starts.val[1]!.val+t.val) at br
    rw [ol 1 (by decide)] at br; exact br
  step as ⟨l,hl'⟩
  step as ⟨r,hr'⟩
  step with compress_pair_spec iv l r as ⟨hash,hh⟩
  step with put_digest_spec N limit 0#usize hash both hn hl (by scalar_tac) (by decide) as ⟨first,hf,of',bf⟩
  step with put_digest_spec N limit 1#usize hash first hn hl (by scalar_tac) (by decide) as ⟨out,ho,oo,bo⟩
  have h0 := congrArg (fun xs : List (List U8) => xs[0]!) hh
  have h1 := congrArg (fun xs : List (List U8) => xs[1]!) hh
  simp (disch := simp) only [getElem!_pos,List.getElem_map,List.getElem_cons_zero,List.getElem_cons_succ] at h0 h1
  refine ⟨by omega,fun j hj => ?_⟩
  interval_cases j
  · rw [oo 0 (by decide),bf]
    rw [← getElem!_pos hash.val 0 (by simp)] at h0
    rw [h0,digest_bytes,hl',← getElem!_pos,b0,hl]
    rfl
  · rw [bo,of' 1 (by decide)]
    rw [← getElem!_pos hash.val 1 (by simp)] at h1
    rw [h1,digest_bytes,hr',← getElem!_pos,b1,hl]
    rfl

end slhdsa.Intel.Chain
