import Rcavx.Inner
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def Good2 (W V : Words) (iv : Spec.SHA512.State) (g : Nat) (s : St)
    (x : Array Wide 8#usize) (ms : Ms) (saved : Array Lane 40#usize) (idx : Usize) :=
  state512 s = after W iv (2*g) ∧ x=window (Both W V) g ∧ Cache W g ms ∧ Archive V (g+8) saved ∧ idx.val=2*(g+8)

theorem paired_inner (W V : Words) (iv : Spec.SHA512.State) (group : Nat) (limit : group<4)
    (s : St) (x : Array Wide 8#usize) (ms : Ms) (saved : Array Lane 40#usize) (idx outer : Usize)
    (outer_eq : outer.val=group+1) (rec : Rec W) (recV : Rec V) (pre : Good2 W V iv (8*group) s x ms saved idx) :
    rounds_0_63_avx2_loop0_loop0 ⟨0#usize,8#usize⟩ s x ms saved idx outer ⦃ s x ms saved idx => Good2 W V iv (8*group+8) s x ms saved idx ⦄ := by
  unfold rounds_0_63_avx2_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × St × Array Wide 8#usize × Ms × Array Lane 40#usize × Usize => 8-q.1.start.val)
    (inv := fun q => q.1.end=8#usize ∧ q.1.start.val≤8 ∧ Good2 W V iv (8*group+q.1.start.val) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
  · rintro ⟨it,s,x,ms,saved,idx⟩ ⟨stop,bound,hs,hx,hcache,arch,hidx⟩
    simp only at stop bound hs hx hcache arch hidx
    let g := 8*group+it.start.val
    change idx.val=2*(g+8) at hidx
    change state512 s=after W iv (2*g) at hs
    change x=window (Both W V) g at hx
    change Cache W g ms at hcache
    change Archive V (g+8) saved at arch
    unfold rounds_0_63_avx2_loop0_loop0.body
    by_cases more : it.start.val<8
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop]; exact more) as ⟨j,next,hj,hn,he⟩
      simp only [hj,bind_ok]
      have slot : it.start.val=g%8 := by dsimp [g]; omega
      have room : idx.val+2≤roundConstants.length := by change idx.val+2≤80; dsimp [g] at hidx; omega
      have rk_eq : rk idx = ok (pair Spec.SHA512.K (g+8)) := by
        unfold rk
        rw [if_pos room]
        simp only [hidx,k_eq,pair]
      have v : g<32 := by dsimp [g]; omega
      rw [rk_eq,hx]
      simp only [bind_ok,core.core_arch.x86.avx._mm256_set_m128i,advance2 W V g v rec recV,cast_ms]
      step with cast_spec (len := 16#usize) ms (by rfl) as ⟨words,reads⟩
      have old := hcache g (by omega) (by omega)
      rw [← slot] at old
      have eq := (reads it.start.val more).trans old
      step as ⟨i,hi⟩
      step as ⟨lo,hlo⟩
      have loWord : lo.bv=Spec.SHA512.K[2*g]!+W[2*g]! := by
        rw [hlo,← getElem!_eq _ _ (by scalar_tac),hi]
        exact (congrArg Prod.fst eq).trans (weight0 W g)
      step with next_round s lo W iv (2*g) hs loWord as ⟨s1,hs1⟩
      step as ⟨i1,hi1⟩
      step as ⟨hiWord,hr⟩
      have hiWord' : hiWord.bv=Spec.SHA512.K[2*g+1]!+W[2*g+1]! := by
        rw [hr,← getElem!_eq _ _ (by scalar_tac),hi1,hi]
        exact (congrArg Prod.snd eq).trans (weight1 W g)
      step with next_round s1 hiWord W iv (2*g+1) hs1 hiWord' as ⟨s2,hs2⟩
      simp only [core.core_arch.x86.avx2._mm256_extracti128_si256,bind_ok]
      step as ⟨ms',updated⟩
      step as ⟨index8,mul8⟩
      step as ⟨index,addSlot⟩
      step as ⟨saved',stored⟩
      step as ⟨k,hk⟩
      have incr : 8*group+next.start.val=g+1 := by dsimp [g]; omega
      refine ⟨he.trans stop,by omega,?_,by omega⟩
      rw [incr]
      refine ⟨by simpa only [show 2*(g+1)=2*g+1+1 by omega] using hs2,rfl,by rw [updated]; exact cache_advance _ _ _ _ hcache slot,?_,by omega⟩
      rw [stored,show g+1+8 = g+8+1 by omega]
      apply archive_advance _ _ _ _ arch ?_ (by omega)
      dsimp [g]; omega
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop]; exact Nat.le_of_not_gt more) as ⟨j,next,hj,_⟩
      simp only [hj,step_simps]
      have eq : g=8*group+8 := by dsimp [g]; omega
      rw [← eq]
      exact ⟨hs,hx,hcache,arch,hidx⟩
  · exact ⟨rfl,Nat.zero_le _,pre⟩
end slhdsa.X86.RustCrypto512
