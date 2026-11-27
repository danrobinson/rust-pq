import Cachepath.NativeVerify.ForsSignAuthProgram
import Shakebatch.Auth
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]

theorem siblings (N : Usize) (indices : Array U32 machine.width) (j : U32) (fit : j.val < 32) :
    core.array.Array.map (sign.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U32 N) indices j ⦃ out =>
      ∀ i < machine.width.val, out.val[i]!.val=(indices.val[i]!.val / 2^j.val) ^^^ 1 ⦄ :=
  sibling_indices N indices j fit

theorem indices {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (choices : Slice U32) (first active : Usize) (nonempty : 0 < active.val)
    (fit : first.val+active.val ≤ choices.length) (trees : choices.length ≤ 35)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    core.array.from_fn machine.width (sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (first,active,p.a,choices) ⦃ out => ∀ j < machine.width.val,
        let tree := treeAt first.val active.val j
        out.val[j]!.val=tree*2^p.a.val+choices.val[tree]!.val ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width
    (sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) (first,active,p.a,choices)
    (fun j (x : U32) => let tree := treeAt first.val active.val j; x.val=tree*2^p.a.val+choices.val[tree]!.val) ?_)
  · intro out h j hj
    simpa only [Array.getElem!_Nat_eq] using h j hj
  intro i hi
  have valid : treeAt first.val active.val i.val < choices.length := by unfold treeAt; omega
  have shift := fors_shl_arith p.a.val (treeAt first.val active.val i.val) hp.valid.a_le (by omega)
  have chosen := index _ valid
  simp only [sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32,sign.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut]
  step as ⟨last,limit⟩
  have cap : first.val + (core.cmp.impls.OrdUsize.min i last).val ≤ Usize.max := by
    simp only [core.cmp.impls.OrdUsize.min_val,limit]
    unfold treeAt at valid; scalar_tac
  simp only [lift,bind_ok]
  step as ⟨tree,ix⟩
  have tv : tree.val=treeAt first.val active.val i.val := by
    simp [ix,treeAt,limit,core.cmp.impls.OrdUsize.min_val]
  have treeBound : tree.val < choices.length := by rw [tv]; exact valid
  have height : p.a.val ≤ 14 := hp.valid.a_le
  have castVal : (UScalar.cast .U32 tree).val=tree.val := by
    simp [UScalar.cast_val_eq,Nat.mod_eq_of_lt (show tree.val < 2^32 by omega)] <;> omega
  step as ⟨shifted,sval⟩
  all_goals try scalar_tac
  have sv : shifted.val=tree.val*2^p.a.val := by
    rw [sval,castVal,tv]
    simpa [U32.size,U32.numBits] using shift.1
  step as ⟨sel,read⟩
  have selectedVal : sel.val=choices.val[tree.val]!.val := by rw [read,← getElem!_pos]
  step
  simp_all only [step_simps]
  rfl

theorem auth_phase (nodes : Nodes) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (s : Buffer) (stride first active : Usize) (indices : Array U32 machine.width)
    (hash : ∀ (ids : Array U32 machine.width) (level : U32), level.val < p.a.val →
      (∀ j < machine.width.val, (ids.val[j]!.val+1)*2^level.val < 2^32) →
      nodes sk seed a ids level active ⦃ out => ∀ j < active.val,
        bytes out.val[j]!.val=Spec.forsNode (Shake.params p) (bytes sk.val) ids.val[j]!.val level.val (bytes seed.val) (adrsS a) ⦄) (fit : (first.val+active.val)*stride.val ≤ s.length)
    (width : active.val ≤ machine.width.val) (str : stride.val=(p.a.val+1)*N.val)
    (bounds : ∀ j < p.a.val, ∀ lane < machine.width.val,
      (((indices.val[lane]!.val/2^j) ^^^ 1)+1)*2^j < 2^32) :
    sign_loop1_loop0 nodes ⟨0#u32,p.a⟩ sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 stride s first active indices ⦃ out =>
      AuthWritten p sk seed a indices first.val active.val stride.val p.a.val s out ⦄ := by
  unfold sign_loop1_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Buffer => p.a.val-q.1.start.val)
    (inv := fun q => q.1.end=p.a ∧ q.1.start.val ≤ p.a.val ∧
      AuthWritten p sk seed a indices first.val active.val stride.val q.1.start.val s q.2)
  · rintro ⟨it,cur⟩ ⟨he,hi,prior⟩
    simp only at he hi prior
    unfold sign_loop1_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < p.a.val := he ▸ more
      have ha : p.a.val ≤ 14 := hp.valid.a_le
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with siblings N indices it.start (by omega) as ⟨ids,idx⟩
      step with hash ids it.start lt (fun j hj => by rw [idx j hj];exact bounds _ lt j hj) as ⟨v,node⟩
      have off : (it.start.val+1)*N.val+N.val ≤ stride.val := by
        have := Nat.mul_le_mul_right N.val (show it.start.val+1+1 ≤ p.a.val+1 by omega)
        simpa only [Nat.add_mul,Nat.one_mul,str] using this
      step with store_siblings v first stride active it.start cur (prior.1.symm ▸ fit) width (by have := hp.nok.ge16; omega) off as ⟨out,written⟩
      refine ⟨hen.trans he,by omega,⟨written.1.trans prior.1,?_⟩,by omega⟩
      intro t z b localFit absolute byte
      have wrote := scattered_block v first.val stride.val (it.start.val+1) active.val cur out written t z b localFit (prior.1.symm ▸ absolute) byte
      rw [wrote,prior.2 t z b localFit absolute byte]
      by_cases tree : first.val ≤ t ∧ t < first.val+active.val
      · have lane : t-first.val < machine.width.val := by omega
        by_cases pos : z=it.start.val+1
        · subst z
          simp only [tree.1,tree.2,true_and,ite_true,hn,Nat.zero_lt_succ,Nat.le_refl,
            Nat.add_sub_cancel,authNode]
          have bv : b < v.val[t-first.val]!.val.length := by simpa using byte
          rw [getElem!_pos _ b bv,← bytes_getElem! _ _ bv,node _ (by omega),idx _ lane]
        · have e : (0 < z ∧ z ≤ nxt.start.val) ↔ (0 < z ∧ z ≤ it.start.val) := by omega
          simp [tree.1,tree.2,Ne.symm pos,pos,e]
      · by_cases ok : first.val ≤ t
        · simp [ok,show ¬t < first.val+active.val by omega]
        · simp [ok]
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=p.a.val := by rw [he] at more;omega
      simpa only [eq] using prior
  · simp [AuthWritten] <;> omega

end slhdsa.NativeVerify.ForsSign
