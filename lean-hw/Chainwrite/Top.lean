import Chainwrite.Group
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainWriteRust.sha256.x86.avx512

private theorem lane_bound (mask : U16) (k : Nat) (set : mask.bv.getLsbD k = true) : k < 16 := by
  by_contra! h
  exact Bool.noConfusion ((BitVec.getLsbD_of_ge mask.bv k h).symm.trans set)

def digestPrefix (hash : Hash) (j : Fin 16) (n : Nat) (row : Spec.Bytes) :=
  row.take 22 ++ digestPart hash j 0 n ++ row.drop (22+n)

private theorem extend_prefix (hash : Hash) (j : Fin 16) (n w : Nat) (row : Spec.Bytes)
    (len : row.length = 64) :
    (digestPrefix hash j n row).take (22+n) ++ digestPart hash j n w ++ (digestPrefix hash j n row).drop (22+n+w) =
      digestPrefix hash j (n+w) row := by
  have l : (row.take 22 ++ digestPart hash j 0 n).length = 22+n := by simp [len,digestPart]
  have t := List.take_left (l₁ := row.take 22 ++ digestPart hash j 0 n) (l₂ := row.drop (22+n))
  rw [l] at t
  unfold digestPrefix
  rw [t,List.drop_append,l,List.drop_eq_nil_of_le (by omega),List.nil_append,List.drop_drop]
  simp [digestPart,List.range_add,List.map_append,List.map_map,Function.comp_def,List.append_assoc,Nat.add_assoc,Nat.add_comm w]

private def Written (hash : Hash) (mask : U16) (orig out : Rows) (n : Nat) :=
  out.length = orig.length ∧ ∀ k < orig.length, bytes out.val[k]!.val =
    if h : mask.bv.getLsbD k then digestPrefix hash ⟨k,lane_bound mask k h⟩ n (bytes orig.val[k]!.val)
    else bytes orig.val[k]!.val

theorem digest_loop_spec (N : Usize) (hash : Hash) (batch : Rows) (mask : U16) (it : Iter)
    (hn : N.val ≤ 32) (he : it.iter.end = N) (hs : it.step_by = 16#usize)
    (hz : it.iter.start = 0#usize) (hb : Covers mask batch.length) :
    write_finished_loop1 N it hash batch Store.control mask ⦃ out => Written hash mask batch out N.val ⦄ := by
  unfold write_finished_loop1
  apply loop.spec_decr_nat (measure := fun p : Iter × Rows => N.val-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end = N ∧ p.1.step_by = 16#usize ∧ p.1.iter.start.val ≤ N.val ∧
      (p.1.iter.start.val % 16 = 0 ∨ p.1.iter.start = N) ∧ Written hash mask batch p.2 p.1.iter.start.val)
  · rintro ⟨i,b⟩ ⟨iend,istep,bound,aligned,bl,br⟩
    simp only at iend istep bound aligned bl br
    by_cases lt : i.iter.start.val < N.val
    · have al : i.iter.start.val % 16 = 0 := aligned.resolve_right (by intro h; rw [h] at lt; omega)
      have off : i.iter.start.val ≤ 16 := by omega
      step with group_spec N hash b mask i iend istep off al lt hn (bl ▸ hb) as ⟨flow,nxt,out,eq,nx,ne,ns,ol,orr⟩
      subst flow
      simp only
      refine ⟨ne,ns,by omega,?_,⟨ol.trans bl,?_⟩,by omega⟩
      · by_cases h : i.iter.start.val+16 ≤ N.val
        · left; omega
        · right; apply UScalar.eq_of_val_eq; omega
      · intro k hk
        rw [orr k (bl ▸ hk),br k hk]
        split <;> rename_i h
        · rw [extend_prefix _ _ _ _ _ (by simp [bytes])]
          congr 1
          omega
        · simp [h]
    · unfold write_finished_loop1.body
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec i (by rw [iend]; omega) as ⟨opt,i',hopt,hi⟩
      simp only [hopt,step_simps]
      have done : i.iter.start.val = N.val := by omega
      exact ⟨bl,done ▸ br⟩
  · refine ⟨he,hs,by simp [hz],Or.inl (by simp [hz]),rfl,?_⟩
    intro k hk
    simp [hz,digestPrefix,digestPart]
/-- Every active lane receives its final counter and digest. All remaining bytes agree
with the input, including the unmodified suffix when the digest is truncated. -/
theorem write_finished_spec (N : Usize) (hash : Hash) (batch : Rows) (ends : Slice U32) (mask : U16)
    (hn : N.val ≤ 32) (hb : Covers mask batch.length) (he : Covers mask ends.length)
    (hp : ∀ k, mask.bv.getLsbD k = true → 0 < ends.val[k]!.val) :
    write_finished N hash batch ends mask ⦃ out => out.length = batch.length ∧
      ∀ k < batch.length, bytes out.val[k]!.val = if h : mask.bv.getLsbD k then
        (bytes batch.val[k]!.val).take 18 ++ Spec.toByte (ends.val[k]!.val-1) 4 ++
          digestPart hash ⟨k,lane_bound mask k h⟩ 0 N.val ++ (bytes batch.val[k]!.val).drop (22+N.val)
        else bytes batch.val[k]!.val ⦄ := by
  unfold write_finished
  simp only [core.core_arch.x86.sse2._mm_set_epi32,ChainWriteRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    StoreRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,
    GatherRust.core.core_arch.x86.avx512f._mm512_broadcast_i32x4,bind_ok]
  step with write_index_spec batch ends mask hb he hp as ⟨b,bl,br⟩
  step as ⟨it,hit,hs⟩
  change write_finished_loop1 N it hash b Store.control mask ⦃ _ => _ ⦄
  apply WP.spec_mono (digest_loop_spec N hash b mask it hn (by simp [hit]) hs (by simp [hit]) (bl ▸ hb))
  rintro out ⟨ol,orr⟩
  refine ⟨ol.trans bl,?_⟩
  intro k hk
  rw [orr k (bl ▸ hk),br k hk]
  split
  · unfold digestPrefix Intel.Chain.withIndex
    have l : ((bytes batch.val[k]!.val).take 18 ++ Spec.toByte (ends.val[k]!.val-1) 4).length = 22 := by
      simp [bytes,Spec.toByte]
    have t := List.take_left (l₁ := (bytes batch.val[k]!.val).take 18 ++ Spec.toByte (ends.val[k]!.val-1) 4)
      (l₂ := (bytes batch.val[k]!.val).drop 22)
    rw [l] at t
    rw [t,List.drop_append,l,List.drop_eq_nil_of_le (by omega),List.nil_append,List.drop_drop]
    simp [Nat.add_comm]
  · rfl

#print axioms write_finished_spec
end slhdsa.X86.Chain
