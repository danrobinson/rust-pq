import Shakebatch.SigBlocks
import Shakebatch.Selection
import Shakebatch.Sibling
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

def authNode {N} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs) (idx z : Nat) :=
  Spec.forsNode (Shake.params p) (bytes sk.val) ((idx/2^z) ^^^ 1) z (bytes seed.val) (adrsS a)

def AuthWritten {N} (p : slhdsa.params.Params) (sk seed : Array U8 N) (a : address.Adrs)
    (indices : Array U32 machine.width) (first active stride count : Nat) (s out : Buffer) :=
  out.length=s.length ∧ ∀ t z b, z*N.val+b < stride → t*stride+(z*N.val+b) < s.length → b < N.val →
    sigByte out stride N.val t z b =
      if first ≤ t ∧ t < first+active ∧ 0 < z ∧ z ≤ count then
        (authNode p sk seed a indices.val[t-first]!.val (z-1))[b]!
      else sigByte s stride N.val t z b

theorem write_auth {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (s : Buffer) (stride first active : Usize) (indices : Array U32 machine.width)
    (permutes : PermutationCorrect) (fit : (first.val+active.val)*stride.val ≤ s.length)
    (width : active.val ≤ machine.width.val) (str : stride.val=(p.a.val+1)*N.val)
    (bounds : ∀ j < p.a.val, ∀ lane < machine.width.val,
      (((indices.val[lane]!.val/2^j) ^^^ 1)+1)*2^j < 2^32) :
    shake.fors_batch.sign_loop0_loop1 ⟨0#u32,p.a⟩ sk seed a stride s first active indices ⦃ out =>
      AuthWritten p sk seed a indices first.val active.val stride.val p.a.val s out ⦄ := by
  unfold shake.fors_batch.sign_loop0_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Buffer => p.a.val-q.1.start.val)
    (inv := fun q => q.1.end=p.a ∧ q.1.start.val ≤ p.a.val ∧
      AuthWritten p sk seed a indices first.val active.val stride.val q.1.start.val s q.2)
  · rintro ⟨it,cur⟩ ⟨he,hi,prior⟩
    simp only at he hi prior
    unfold shake.fors_batch.sign_loop0_loop1.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < p.a.val := he ▸ more
      have ha : p.a.val ≤ 14 := hp.valid.a_le
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with sibling_indices N indices it.start (by omega) as ⟨ids,idx⟩
      step with fors_nodes p hp sk seed a permutes ids it.start (fun j hj => by rw [idx j hj];exact bounds _ lt j hj) as ⟨v,node⟩
      have off : (it.start.val+1)*N.val+N.val ≤ stride.val := by
        have := Nat.mul_le_mul_right N.val (show it.start.val+1+1 ≤ p.a.val+1 by omega)
        simpa only [Nat.add_mul,Nat.one_mul,str] using this
      step with write_siblings v first stride active it.start cur (prior.1.symm ▸ fit) width (by have := hp.nok.ge16; omega) off as ⟨out,written⟩
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
          rw [getElem!_pos _ b bv,← bytes_getElem! _ _ bv,node _ lane,idx _ lane]
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

end slhdsa.ShakeBatch
