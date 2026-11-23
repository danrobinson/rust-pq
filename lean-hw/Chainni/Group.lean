import Chainni.Residual
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.Chain

def group (N : Usize) (initial : Array Reg 2#usize) (state : Array U32 8#usize)
    (pair : Rows) (starts ends : Slice U32) := do
  let i2 ← Slice.index_usize ends 0#usize
  let i3 ← Slice.index_usize starts 0#usize
  let i4 ← lift (core.num.U32.saturating_sub i2 i3)
  let i5 ← Slice.index_usize ends 1#usize
  let i6 ← Slice.index_usize starts 1#usize
  let i7 ← lift (core.num.U32.saturating_sub i5 i6)
  let shared ← lift (core.cmp.impls.OrdU32.min i4 i7)
  let pair1 ←
    ChainNiRust.sha256.x86.chains_loop0_loop0 N { start := 0#u32, «end» := shared }
      initial pair starts
  let i8 ← Slice.index_usize starts 0#usize
  let i9 ← i8 + shared
  let i10 ← Slice.index_usize starts 1#usize
  let i11 ← i10 + shared
  let i12 ← Array.index_usize (Array.make 2#usize [ i9, i11 ]) 0#usize
  let i13 ← Slice.index_usize ends 0#usize
  if i12 < i13
  then
    let s ← lift (Array.to_slice (Array.make 2#usize [ i9, i11 ]))
    let pair2 ← ChainNiRust.hash.chain_blocks_portable N state pair1 s ends
    ok pair2
  else
    let i14 ← Array.index_usize (Array.make 2#usize [ i9, i11 ]) 1#usize
    let i15 ← Slice.index_usize ends 1#usize
    if i14 < i15
    then
      let s ← lift (Array.to_slice (Array.make 2#usize [ i9, i11 ]))
      let pair2 ← ChainNiRust.hash.chain_blocks_portable N state pair1 s ends
      ok pair2
    else ok pair1

theorem group_spec (N : Usize) (initial : Array Reg 2#usize) (state : Array U32 8#usize)
    (pair : Rows) (starts ends : Slice U32) (hn : N.val ≤ 32)
    (init : stateWords (packedState initial) = wv state.val)
    (lp : pair.length = 2) (ls : starts.length = 2) (le : ends.length = 2) :
    group N initial state pair starts ends ⦃ out => Ended N state pair out starts ends ⦄ := by
  unfold group
  simp only [lift,bind_tc_eq,bind_ok]
  step as ⟨e0,he0⟩
  step as ⟨s0,hs0⟩
  step as ⟨e1,he1⟩
  step as ⟨s1,hs1⟩
  let shared := core.cmp.impls.OrdU32.min (core.num.U32.saturating_sub e0 s0) (core.num.U32.saturating_sub e1 s1)
  have sat (e s : U32) : (core.num.U32.saturating_sub e s).val = e.val-s.val := by
    change (0 ⊔ (e.val-s.val)) % 2^32 = _
    rw [Nat.max_eq_right (Nat.zero_le _),Nat.mod_eq_of_lt (by have := e.bv.isLt; change e.val < 2^32 at this; omega)]
  have v : shared.val = min (e0.val-s0.val) (e1.val-s1.val) := by simp [shared,sat]
  simp only [← getElem!_pos] at hs0 hs1 he0 he1
  have steps (i : Nat) (hi : i < 2) : shared.val ≤ ends.val[i]!.val-starts.val[i]!.val := by
    interval_cases i <;> simp_all
  have bounds (i : Nat) (hi : i < 2) : starts.val[i]!.val+shared.val ≤ U32.max := by
    have h := steps i hi
    have a : starts.val[i]!.val ≤ U32.max := by scalar_tac
    have b : ends.val[i]!.val ≤ U32.max := by scalar_tac
    omega
  step with shared_spec N initial starts shared pair hn lp ls bounds as ⟨tmp,ht⟩
  step as ⟨a,ha⟩
  step as ⟨u,hu⟩
  · simpa [ha,← getElem!_pos,shared] using bounds 0 (by decide)
  step as ⟨b,hb⟩
  step as ⟨v',hv⟩
  · simpa [hb,← getElem!_pos,shared] using bounds 1 (by decide)
  let next := (Array.make 2#usize [u,v']).to_slice
  have ns : next.length = 2 := by rfl
  have vals (i : Nat) (hi : i < 2) : next.val[i]!.val = starts.val[i]!.val+shared.val := by
    interval_cases i
    · change u.val = _; rw [hu,ha,← getElem!_pos]
    · change v'.val = _; rw [hv,hb,← getElem!_pos]
  have tail := residual N state initial starts ends next pair tmp shared.val hn init lp le ns ht steps vals
  step as ⟨x,hx⟩
  step as ⟨y,hy⟩
  split
  · apply WP.spec_bind tail; intro r hr; exact (WP.spec_ok _).2 hr
  · rename_i hx'
    step as ⟨z,hz⟩
    step as ⟨w,hw⟩
    split
    · apply WP.spec_bind tail; intro r hr; exact (WP.spec_ok _).2 hr
    · rename_i hz'
      apply (WP.spec_ok _).2
      apply already_done N state initial starts ends pair tmp shared.val init lp ht steps
      intro i hi
      interval_cases i
      · have h := vals 0 (by decide)
        change u.val = _ at h
        change x = u at hx
        rw [hx,hy,← getElem!_pos] at hx'
        rw [← h]; exact Nat.le_of_not_lt hx'
      · have h := vals 1 (by decide)
        change v'.val = _ at h
        change z = v' at hz
        rw [hz,hw,← getElem!_pos] at hz'
        rw [← h]; exact Nat.le_of_not_lt hz'

end slhdsa.Intel.Chain
