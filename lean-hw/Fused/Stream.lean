import Fused.Program
import Cachepath.WotsFusedStream

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused.Stream
open ShakeBatch Spec.Keccak
open cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [kernel : Kernel]
local instance : Machine := machine kernel

theorem absorb_word (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize) (j : Usize)
    (rate : pos.val<17) (bound : j.val<25) :
    xmss_sign_batch_loop2_loop1_loop0 ⟨0#usize,8#usize⟩ pk pos state j ⦃ out =>
    ∀ l<8, ShakeBatch.lane out l = (ShakeBatch.lane pk l).setIfInBounds pos.val
      ((ShakeBatch.lane pk l)[pos.val]! ^^^ cell state j.val l) ⦄ := by
  obtain ⟨row,read,eq⟩ := spec_imp_exists (Array.index_usize_spec state j (by simpa using bound))
  have same : xmss_sign_batch_loop2_loop1_loop0.body pos state j =
      generate_loop0_loop1_loop0.body pos row := by
    funext it s
    simp only [xmss_sign_batch_loop2_loop1_loop0.body,generate_loop0_loop1_loop0.body,read,bind_ok]
    rfl
  unfold xmss_sign_batch_loop2_loop1_loop0
  rw [same]
  apply WP.spec_mono (absorb_row pk pos row rate)
  intro out h l hl
  rw [h l hl,eq,← getElem!_pos]
  rfl

/-- The production range iterator streams each column's endpoint, including blocks that
cross or finish exactly on the SHAKE rate boundary. -/
theorem absorb_tip (n : Usize) (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize)
    (rate : pos.val<17) (small : n.val≤25) (permutes : PermutationCorrect)
    (tip : Nat → Spec.Bytes) (lengths : ∀ l<8, (tip l).length=8*n.val)
    (words : ∀ l<8, ∀ j<n.val, cell state j l=messageWord (tip l) j) :
    xmss_sign_batch_loop2_loop1 8#usize ⟨0#usize,n⟩ pk pos state ⦃ out =>
      out.2.val<17 ∧ ∀ l<8, (ShakeBatch.lane out.1 l,8*out.2.val) = (tip l).foldl feed (ShakeBatch.lane pk l,8*pos.val) ⦄ := by
  let inv (j : Nat) (q : Matrix 8#usize × Usize) := q.2.val<17 ∧ ∀ l<8,
    (ShakeBatch.lane q.1 l,q.2.val) = (List.range j).foldl
      (fun a w => FusedStream.absorb a (messageWord (tip l) w)) (ShakeBatch.lane pk l,pos.val)
  unfold xmss_sign_batch_loop2_loop1
  apply WP.spec_mono (range_fold (fun it q => xmss_sign_batch_loop2_loop1.body 8#usize state it q.1 q.2)
    n (pk,pos) inv (by simpa [inv] using rate) ?_ ?_)
  · rintro ⟨acc,cursor⟩ ⟨hr,h⟩
    refine ⟨hr,?_⟩
    intro l hl
    have ref := FusedStream.absorb_tip (tip l) n.val (lengths l hl) (ShakeBatch.lane pk l)
      (by simp [ShakeBatch.lane]) pos.val rate
    rw [← h l hl] at ref
    exact ref
  · rintro it ⟨acc,cursor⟩ stop live ⟨hr,old⟩
    unfold xmss_sign_batch_loop2_loop1.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live)
      as ⟨_,next,ho,inc,he⟩
    simp only [ho]
    step with absorb_word acc cursor state it.start hr (by omega) as ⟨updated,absorbed⟩
    step as ⟨p,advance⟩
    have folded (l : Nat) (hl : l<8) :
        (List.range next.start.val).foldl (fun a w => FusedStream.absorb a (messageWord (tip l) w))
          (ShakeBatch.lane pk l,pos.val) = FusedStream.absorb (ShakeBatch.lane acc l,cursor.val) (cell state it.start.val l) := by
      rw [inc,List.range_succ,List.foldl_append,← old l hl,words l hl _ live]
      rfl
    by_cases boundary : p=17#usize
    · simp only [boundary,ite_true]
      step with permutes updated as ⟨mixed,permuted⟩
      refine ⟨next,(mixed,0#usize),rfl,he.trans stop,inc,by dsimp; decide,?_⟩
      intro l hl
      have last : cursor.val=16 := by rw [boundary] at advance; scalar_tac
      rw [folded l hl,permuted l hl,absorbed l hl]
      simp [FusedStream.absorb,last]
    · simp only [boundary,ite_false,step_simps]
      have last : cursor.val≠16 := by intro e; apply boundary; apply UScalar.eq_of_val_eq; scalar_tac
      refine ⟨next,(updated,p),rfl,he.trans stop,inc,by dsimp at hr ⊢; omega,?_⟩
      intro l hl
      rw [folded l hl,absorbed l hl]
      simp [FusedStream.absorb,last,advance]
  · rintro it ⟨s,p⟩ last stop
    unfold xmss_sign_batch_loop2_loop1.body
    obtain ⟨⟨_,_⟩,next,ho,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [next,ho]

/-- The 15-step chain loop already identifies every lane's squeezed digest. That
postcondition suffices to stream the exact endpoint without another extraction callback. -/
theorem absorb_digest (N n : Usize) (pk : Matrix 8#usize) (pos : Usize) (state : Matrix 8#usize)
    (rate : pos.val<17) (width : n.val=N.val/8) (bound : N.val≤136) (align : N.val%8=0)
    (permutes : PermutationCorrect) (tip : Nat → Spec.Bytes)
    (digests : ∀ l<8, NativeVerify.Wots.digest N state l=tip l) :
    xmss_sign_batch_loop2_loop1 8#usize ⟨0#usize,n⟩ pk pos state ⦃ out =>
      out.2.val<17 ∧ ∀ l<8, (ShakeBatch.lane out.1 l,8*out.2.val) =
        (tip l).foldl feed (ShakeBatch.lane pk l,8*pos.val) ⦄ := by
  obtain ⟨raw,packed,rows⟩ := digest_words (N:=N) state bound align
  have equal (l : Nat) (hl : l<8) : bytes raw.val[l]!.val=tip l := (packed l hl).trans (digests l hl)
  apply absorb_tip n pk pos state rate (by omega) permutes tip
  · intro l hl
    rw [← equal l hl]
    simp [bytes]
    omega
  · intro l hl j hj
    rw [← equal l hl,← inputWord_eq,rows l hl _ (by omega)]

theorem finish_rows (pk : Matrix 8#usize) (pos : Usize) (rate : pos.val<17)
    (permutes : PermutationCorrect) :
    (do let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ pk pos
        kernel.permute padded) ⦃ out => ∀ l<8, ShakeBatch.lane out l=finalize (ShakeBatch.lane pk l,8*pos.val) ⦄ :=
  cache.builder.nativeShake.Vector.Fused.finish_rows pk pos rate permutes

theorem finish_read (N : Usize) (pk : Matrix 8#usize) (pos : Usize) (rate : pos.val<17)
    (permutes : PermutationCorrect) (bound : N.val≤136) (align : N.val%8=0) :
    (do let padded ← xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ pk pos
        let final ← kernel.permute padded
        NativeVerify.ActiveHash.read_active N final 8#usize) ⦃ out => ∀ l<8,
      bytes out.val[l]!.val = squeeze (finalize (ShakeBatch.lane pk l,8*pos.val)) 0 N.val ⦄ := by
  have pad : xmss_sign_batch_loop3 ⟨0#usize,8#usize⟩ pk pos ⦃ out => ∀ l<8,
      ShakeBatch.lane out l=padWords pos.val (ShakeBatch.lane pk l) ⦄ := pad_rows pk pos rate
  step with pad as ⟨padded,tag⟩
  step with permutes padded as ⟨final,eq⟩
  apply WP.spec_mono (NativeVerify.ActiveHash.read_digest N final 8#usize (Nat.le_refl _) bound align)
  intro out read l hl
  rw [read l hl,eq l hl,tag l hl]
  exact congrArg (fun st => squeeze st 0 N.val) (FusedStream.finish_eq _ _)

end slhdsa.Fused.Stream
