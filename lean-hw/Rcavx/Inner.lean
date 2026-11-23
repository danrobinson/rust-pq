import Rcavx.Round
import Rcavx.Cache
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

abbrev St := Array U64 8#usize
abbrev Ms := Array Lane 8#usize
def after (W : Words) (iv : Spec.SHA512.State) (t : Nat) := (List.range t).foldl (Spec.SHA512.round W) iv
theorem next_round (v : St) (wk : U64) (W : Words) (iv : Spec.SHA512.State) (t : Nat)
    (h : state512 v = after W iv t) (val : wk.bv=Spec.SHA512.K[t]!+W[t]!) :
    sha512.x86_avx2.sha_round v wk ⦃ out => state512 out = after W iv (t+1) ⦄ := by
  apply WP.spec_mono (sha_round v wk W t val)
  intro out eq
  simp only [eq,h,after,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem weight0 (W : Words) (g : Nat) : (weighted W g).1 = Spec.SHA512.K[2*g]!+W[2*g]! := BitVec.add_comm _ _
theorem weight1 (W : Words) (g : Nat) : (weighted W g).2 = Spec.SHA512.K[2*g+1]!+W[2*g+1]! := BitVec.add_comm _ _

def Good (W : Words) (iv : Spec.SHA512.State) (g : Nat) (s : St) (x ms : Ms) (idx : Usize) :=
  state512 s = after W iv (2*g) ∧ x=window (pair W) g ∧ Cache W g ms ∧ idx.val=2*(g+8)

theorem single_inner (W : Words) (iv : Spec.SHA512.State) (group : Nat) (limit : group<4)
    (s : St) (x ms : Ms) (idx : Usize) (rec : Rec W) (pre : Good W iv (8*group) s x ms idx) :
    rounds_0_63_avx_loop0_loop0 ⟨0#usize,8#usize⟩ s x ms idx ⦃ s x ms idx => Good W iv (8*group+8) s x ms idx ⦄ := by
  unfold rounds_0_63_avx_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × St × Ms × Ms × Usize => 8-q.1.start.val)
    (inv := fun q => q.1.end=8#usize ∧ q.1.start.val≤8 ∧ Good W iv (8*group+q.1.start.val) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  · rintro ⟨it,s,x,ms,idx⟩ ⟨stop,bound,hs,hx,hcache,hidx⟩
    simp only at stop bound hs hx hcache hidx
    let g := 8*group+it.start.val
    change idx.val=2*(g+8) at hidx
    change state512 s=after W iv (2*g) at hs
    change x=window (pair W) g at hx
    change Cache W g ms at hcache
    unfold rounds_0_63_avx_loop0_loop0.body
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
      simp only [bind_ok,advance W g v rec,cast_ms]
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
      step as ⟨ms',updated⟩
      step as ⟨k,hk⟩
      have incr : 8*group+next.start.val=g+1 := by dsimp [g]; omega
      refine ⟨he.trans stop,by omega,?_,by omega⟩
      rw [incr]
      exact ⟨by simpa only [show 2*(g+1)=2*g+1+1 by omega] using hs2,rfl,by rw [updated]; exact cache_advance _ _ _ _ hcache slot,by omega⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop]; exact Nat.le_of_not_gt more) as ⟨j,next,hj,_⟩
      simp only [hj,step_simps]
      have eq : g=8*group+8 := by dsimp [g]; omega
      rw [← eq]
      exact ⟨hs,hx,hcache,hidx⟩
  · exact ⟨rfl,Nat.zero_le _,pre⟩
end slhdsa.X86.RustCrypto512
