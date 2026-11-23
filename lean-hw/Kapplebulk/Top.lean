import Kapplebulk.Blocks
open Aeneas Aeneas.Std Result ControlFlow Spec.Keccak
namespace slhdsa.Kapplebulk
open Ksha3 (Rows lane)
open KapplebulkRust.shake256.parallel
set_option maxHeartbeats 2000000

theorem duplicate (s : Array U64 25#usize) :
    core.array.Array.map sha3.blocks.closure.Insts.CoreOpsFunctionFnMutTupleU64uint64x2_t s ()
      ⦃ out => lane out 0 = Keccak.words s ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 25#usize _ _
    (fun i (v : Ksha3.Reg) => v 0 = s.val[i]!.bv) ?_)
  · intro out h
    apply ext25 _ _ (by simp [lane]) (by simp [Keccak.words])
    intro i hi
    unfold lane
    rw [ofFnAt _ _ hi]
    simpa [Array.getElem!_Nat_eq,Keccak.words,getElem!_pos,hi] using h i hi
  intro i hi
  simp only [sha3.blocks.closure.Insts.CoreOpsFunctionFnMutTupleU64uint64x2_t]
  step as ⟨word,hw⟩
  simp [sha3.blocks.closure.Insts.CoreOpsFunctionFnMutTupleU64uint64x2_t.call_mut,
    KapplebulkRust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,
    Ksha3Rust.core.core_arch.arm_shared.neon.generated.vdupq_n_u64,hw,getElem!_pos,hi,getElem?_pos s.val i.val (by simpa using hi)]

theorem first (s : Array U64 25#usize) (words : Rows) :
    sha3.blocks_loop1 ⟨0#usize,25#usize⟩ s words ⦃ out => Keccak.words out = lane words 0 ⦄ := by
  unfold sha3.blocks_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 25#usize) => 25-p.1.start.val)
    (inv := fun p => p.1.end = 25#usize ∧ p.1.start.val ≤ 25 ∧
      ∀ j, j < p.1.start.val → p.2.val[j]!.bv = words.val[j]! 0)
  · rintro ⟨it,st⟩ ⟨he,hb,prior⟩
    simp only at *
    unfold sha3.blocks_loop1.body
    by_cases more : it.start.val < 25
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok]
      step as ⟨row,r⟩
      simp only [KapplebulkRust.core.core_arch.arm_shared.neon.generated.vgetq_lane_u64,show (0#i32).bv.toNat<2 by decide,dif_pos,bind_ok]
      step as ⟨out,hout⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      intro j hj
      rw [hout,Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set]
      split
      · subst j
        simp [r,getElem!_pos,more]
      · rename_i ne
        rw [← getElem!_pos st.val j (by simp; omega)]
        exact prior j (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      apply ext25 _ _ (by simp [Keccak.words]) (by simp [lane])
      intro j hj
      unfold lane
      rw [ofFnAt _ _ hj]
      simpa [Keccak.words,getElem!_pos,hj] using prior j (by omega)
  · exact ⟨rfl,Nat.zero_le _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

theorem blocks_fips (state : Array U64 25#usize) (data : Slice U8) (whole : data.length%136=0) :
    KapplebulkRust.shake256.parallel.blocks state data ⦃ out =>
      (Keccak.words out,0) = (bytes data.val).foldl feed (Keccak.words state,0) ⦄ := by
  unfold KapplebulkRust.shake256.parallel.blocks sha3.blocks
  simp only [KapplebulkRust.sha512.hw.arm.available,massert,ite_true,bind_ok]
  step with duplicate state as ⟨a,ha⟩
  step with chunks data whole as ⟨it,hb,sz⟩
  step with allBlocks it a sz as ⟨p,hp⟩
  step with first state p as ⟨out,ho⟩
  simpa only [ho,ha,hb] using hp
end slhdsa.Kapplebulk
