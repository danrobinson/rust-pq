import Cachepath.NativeVerify.ForsPairFips
import Shakebatch.RecoverRoots

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
set_option maxHeartbeats 1400000
variable [machine : Machine] [accelerator : ActiveKernel machine]

private abbrev State := Matrix machine.width
private abbrev Indices := Array U32 machine.width

def Level {N : Usize} (p : params.Params) (sig : Slice U8) (seed : Array U8 N) (a : address.Adrs)
    (choices : List Nat) (first active : Usize) (height : Nat) (ix : Indices) (s : State) :=
  ∀ l<active.val, AtLevel (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) choices
    (first.val+l) height ix.val[l]!.val (Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val)

theorem all_levels {N : Usize} (p : params.Params) (hp : PN p N) (seed : Array U8 N)
    (a : address.Adrs) (sig : Slice U8) (choices : List Nat) (n offset pad stride first active : Usize)
    (sw aw : Array U64 4#usize) (s : State) (initial : Indices)
    (count : n.val=N.val/8) (off : offset.val=n.val+4) (padEq : pad.val=offset.val+2*n.val)
    (live : active.val≤machine.width.val) (str : stride.val=p.a.val+1)
    (fit : (first.val+active.val)*stride.val*N.val≤sig.length)
    (seeds : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addr : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (permutes : ActiveCorrect machine accelerator.run)
    (start : Level p sig seed a choices first active 0 initial s) :
    recover_loop0_loop4 N 0x8000000000000000#u64 ⟨0#u32,p.a⟩ sig n offset pad stride sw aw s first active initial ⦃ out =>
      ∀ j<active.val, Spec.Keccak.squeeze (ShakeBatch.lane out j) 0 N.val =
        forsRoot (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) choices (first.val+j) ⦄ := by
  have small := hp.le32
  have align := aligned_hash hp
  have pos : 0<N.val := by rcases hp.nok with h|h|h <;> omega
  have cap : p.a.val≤14 := hp.valid.a_le
  unfold recover_loop0_loop4
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × State × Indices => p.a.val-q.1.start.val)
    (inv := fun q => q.1.end=p.a ∧ q.1.start.val≤p.a.val ∧ Level p sig seed a choices first active q.1.start.val q.2.2 q.2.1)
  · rintro ⟨it,st,ix⟩ ⟨he,hi,prior⟩
    dsimp only at he hi prior ⊢
    rw [split_level]
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val<p.a.val := he ▸ more
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step with parent_fips seed a sig n offset pad stride first active sw aw it.start st ix (by omega) (by omega) off padEq live
        (by omega) (by omega) fit pos seeds addr permutes as ⟨out,updated,hash⟩
      refine ⟨ends.trans he,by omega,?_,by omega⟩
      intro l hl
      obtain ⟨index,value⟩ := hash l hl
      rw [index,inc,value]
      have blocks : bytes ((sig.val.drop (((first.val+l)*stride.val+it.start.val+1)*N.val)).take N.val) =
        Spec.block (Shake.params p) (bytes sig.val) ((first.val+l)*(p.a.val+1)+1+it.start.val) := by
        simp only [Spec.block,Shake.params,paramsS_n,hp.n_eq,bytes_take,bytes_drop,str]
        rw [show (first.val+l)*(p.a.val+1)+it.start.val+1=(first.val+l)*(p.a.val+1)+1+it.start.val by omega]
      rw [blocks]
      simpa only [Spec.H,Shake.params,paramsS_n,paramsS_a,hp.n_eq,List.append_assoc] using
        climb_step (Shake.params p) (bytes sig.val) (bytes seed.val) (adrsS a) choices (first.val+l) it.start.val
          ix.val[l]!.val (Spec.Keccak.squeeze (ShakeBatch.lane st l) 0 N.val) lt (prior l hl)
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      intro j hj
      have final := (prior j hj).1
      rw [forsRoot_eq]
      have eq : it.start.val=p.a.val := by rw [he] at more;omega
      simpa only [eq,Shake.params,paramsS_a] using final
  · exact ⟨rfl,Nat.zero_le _,start⟩

end slhdsa.NativeVerify.Fors
