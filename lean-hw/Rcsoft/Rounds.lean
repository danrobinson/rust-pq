import Rcsoft.Schedule
import Rcsoft.Read
open Aeneas Aeneas.Std Result
namespace slhdsa.RcSoftProof
open Spec.SHA512 RcSoft.sha512.soft.unroll

attribute [local step] constant_spec

abbrev Words := U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64
abbrev Iter := core.ops.range.Range Usize
abbrev Work := Iter × Array U64 16#usize × Words

def invariant (B : Spec.Bytes) (initial : State) (p : Work) : Prop :=
  p.1.end.val = 80 ∧ p.1.start.val ≤ 80 ∧ Ring (schedule B) p.2.1 p.1.start.val ∧
    S512.st8 p.2.2 = (List.range p.1.start.val).foldl (round (schedule B)) initial

private theorem move_last (a b c d e : Word) : a+b+c+d+e = e+a+b+c+d := by ac_rfl

set_option maxHeartbeats 3500000 in
theorem round_loop (B : Spec.Bytes) (initial : State) (it : Iter) (ring : Array U64 16#usize)
    (a b c d e f g h : U64) (valid : invariant B initial (it,ring,a,b,c,d,e,f,g,h)) :
    compress_block_loop it ring a b c d e f g h ⦃ out =>
      S512.st8 out = (List.range 80).foldl (round (schedule B)) initial ⦄ := by
  unfold compress_block_loop
  apply loop.spec_decr_nat (measure := fun (p : Work) => 80-p.1.start.val)
    (inv := invariant B initial)
  · rintro ⟨it,ring,a,b,c,d,e,f,g,h⟩ ⟨hend,hbound,hRing,hState⟩
    dsimp only at hend hbound hRing hState
    simp only [compress_block_loop.body]
    by_cases live : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it live as ⟨opt,iter1,hsome,hincr,hend'⟩
      simp only [hsome]
      apply WP.spec_bind (next_word B ring it.start (by omega) hRing)
      rintro ⟨ring1,w⟩ ⟨hRing1,hw⟩
      step*
      refine ⟨⟨?_,?_,?_,?_⟩, by omega⟩
      · exact (congrArg (·.val) hend').trans hend
      · change iter1.start.val ≤ 80; omega
      · change Ring _ ring1 iter1.start.val
        rwa [hincr]
      · change S512.st8 _ = (List.range iter1.start.val).foldl _ _
        rw [hincr,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,← hState]
        have first : t1.bv = h.bv + bsig1 e.bv + Spec.SHA512.ch e.bv f.bv g.bv +
            K[it.start.val]! + (schedule B)[it.start.val]! := by
          have hs : s1.bv = bsig1 e.bv := by
            simp only [s1_post1, i3_post1, i1_post, i2_post, i4_post, S512.rotr_bv, bsig1]
            rfl
          have hc : ch.bv = Spec.SHA512.ch e.bv f.bv g.bv := by
            simp only [ch_post1, i5_post1, i7_post1, i6_post, Spec.SHA512.ch]
            rfl
          change w.bv = _ at hw
          rw [t1_post, core.num.U64.wrapping_add_bv_eq, i11_post, core.num.U64.wrapping_add_bv_eq,
            i10_post, core.num.U64.wrapping_add_bv_eq, i8_post, core.num.U64.wrapping_add_bv_eq,
            i9_post, hw, hs, hc]
          exact move_last _ _ _ _ _
        have second : t2.bv = bsig0 a.bv + Spec.SHA512.maj a.bv b.bv c.bv := by
          simp only [t2_post,core.num.U64.wrapping_add_bv_eq,s0_post1,i14_post1,i12_post,i13_post,
            i15_post,S512.rotr_bv, maj_post1,i18_post1,i16_post1,i17_post1,i19_post1,bsig0,Spec.SHA512.maj]
          rfl
        simp only [S512.st8,round,a1_post,e1_post,core.num.U64.wrapping_add_bv_eq,first,second]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨opt,iter1,hnone,_⟩
      simp only [hnone, WP.spec_ok]
      have doneAt : it.start.val = 80 := by omega
      simpa only [doneAt] using hState
  · exact valid
end slhdsa.RcSoftProof
