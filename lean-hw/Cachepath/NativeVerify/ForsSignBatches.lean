import Cachepath.NativeVerify.ForsSignAuth
import Shakebatch.ForsSign
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
private abbrev Steps := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
def Ready {N : Usize} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (choices : Slice U32) (stride count : Nat) (s : Buffer) :=
  s.length=choices.length*stride ∧ ∀ t < choices.length, ∀ z ≤ p.a.val, ∀ b < N.val,
    t < count ∨ z=0 → sigByte s stride N.val t z b = (treeBlock p sk seed a choices t z)[b]!

theorem auth_batches (nodes : Nodes) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (choices : Slice U32) (stride k : Usize)
    (it : Steps) (s : Buffer) (start : it.iter.start=0#usize) (stop : it.iter.end.val=choices.length)
    (stepBy : it.step_by=machine.width) (keys : Ready p sk seed a choices stride.val 0 s)
    (count : k.val=choices.length) (shape : stride.val=(p.a.val+1)*N.val)
    (hk : choices.length ≤ 35) (enabled : 0 < machine.width.val)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (hash : ∀ (ids : Array U32 machine.width) (z : U32) (active : Usize), z.val < p.a.val →
      active.val ≤ machine.width.val →
      (∀ j < machine.width.val, (ids.val[j]!.val+1)*2^z.val < 2^32) →
      nodes sk seed a ids z active ⦃ out => ∀ j < active.val,
        bytes out.val[j]!.val=Spec.forsNode (Shake.params p) (bytes sk.val) ids.val[j]!.val z.val (bytes seed.val) (adrsS a) ⦄) :
    sign_loop1 nodes it choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 k p.a stride s ⦃ out =>
      SigPrefix p sk seed a choices stride.val choices.length out ⦄ := by
  have ha := hp.valid.a_le
  unfold sign_loop1
  apply loop.spec_decr_nat (measure := fun q : Steps × Buffer => choices.length-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end.val=choices.length ∧ q.1.step_by=machine.width ∧
      q.1.iter.start.val ≤ choices.length ∧ Ready p sk seed a choices stride.val q.1.iter.start.val q.2)
  · rintro ⟨iter,cur⟩ ⟨he,hs,hi,prior⟩
    simp only at he hs hi prior
    unfold sign_loop1.body
    step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter (by rw [hs];exact enabled)
      as ⟨o,nxt,splitNext,hend,hwidth⟩
    by_cases more : iter.iter.start.val < iter.iter.end.val
    · simp only [if_pos more] at splitNext
      obtain ⟨some,advance⟩ := splitNext
      simp only [some]
      step as ⟨rem,remaining⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min rem machine.width
      have av : active.val = min (choices.length-iter.iter.start.val) machine.width.val := by
        simp [active,core.cmp.impls.OrdUsize.min_val,remaining,count]
      have fw : iter.iter.start.val+active.val ≤ choices.length := by omega
      have width : active.val ≤ machine.width.val := by omega
      have az : 0 < active.val := by omega
      have same : nxt.iter.start.val=iter.iter.start.val+active.val := by rw [advance,hs,he,av];omega
      step with indices p hp choices iter.iter.start active az fw hk index as ⟨ids,addr⟩
      have fit : (iter.iter.start.val+active.val)*stride.val ≤ cur.length := by
        rw [prior.1];exact Nat.mul_le_mul_right _ fw
      have bounds (z : Nat) (hz : z < p.a.val) (j : Nat) (hj : j < machine.width.val) :
          (((ids.val[j]!.val/2^z) ^^^ 1)+1)*2^z < 2^32 := by
        let t := treeAt iter.iter.start.val active.val j
        have tr : t < choices.length := by change iter.iter.start.val+min j (active.val-1) < choices.length;omega
        rw [addr j hj,sibling_eq _ _ _ _ hz]
        exact (fors_inner_arith p.a.val t choices.val[t]!.val z ha (by omega) (index t tr) hz).2.2
      step with auth_phase nodes p hp sk seed a cur stride iter.iter.start active ids
        (fun v z hz vb => hash v z active hz width vb) fit width shape bounds as ⟨out,path⟩
      refine ⟨hend ▸ he,hwidth.trans hs,by omega,⟨path.1.trans prior.1,?_⟩,by omega⟩
      intro t ht z hz b hb needed
      have inside : z*N.val+b < stride.val := by
        have := Nat.mul_le_mul_right N.val hz
        rw [shape,Nat.add_mul,Nat.one_mul];omega
      have rowFit := Nat.mul_le_mul_right stride.val (show t+1 ≤ choices.length by omega)
      rw [Nat.add_mul,Nat.one_mul] at rowFit
      have absolute : t*stride.val+(z*N.val+b)<cur.length := by rw [prior.1];omega
      rw [path.2 _ _ _ inside absolute hb]
      by_cases current : iter.iter.start.val ≤ t ∧ t < iter.iter.start.val+active.val ∧ 0 < z ∧ z ≤ p.a.val
      · have lane : t-iter.iter.start.val < active.val := by omega
        have tr : treeAt iter.iter.start.val active.val (t-iter.iter.start.val)=t := by
          unfold treeAt;rw [min_eq_left (by omega)];omega
        have v := addr (t-iter.iter.start.val) (by omega)
        change ids.val[t-iter.iter.start.val]!.val=treeAt iter.iter.start.val active.val (t-iter.iter.start.val)*2^p.a.val+_ at v
        rw [tr] at v
        rw [if_pos current]
        simp only [treeBlock,if_neg (by omega : ¬z=0),authNode,forsAuth,v,sibling_eq _ _ _ _ (by omega : z-1 < p.a.val)]
        rfl
      · rw [if_neg current]
        exact prior.2 _ ht _ hz _ hb (by omega)
    · simp only [if_neg more] at splitNext
      simp only [splitNext.1,step_simps]
      have eq : iter.iter.start.val=choices.length := by omega
      exact ⟨prior.1,fun t ht z hz b hb => prior.2 t ht z hz b hb (Or.inl (by omega))⟩
  · exact ⟨stop,stepBy,by simp [start],by simpa [start] using keys⟩
end slhdsa.NativeVerify.ForsSign
