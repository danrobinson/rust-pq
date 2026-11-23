import Xmsskeys.Funs
import Wots.KeyBatch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys
open XmssKeysRust (asChecked asPad)
abbrev RowIter (L : Usize) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array U8 L))

def initialized {L} (original result : Array U8 L) (a : XmssKeysRust.address.Adrs)
    (first : U32) (size block : Usize) (j : Nat) :=
  ∃ k : U32, k.val=first.val+j ∧ PadRust.xmss.wide.prepare_message original (asPad a) k size block = ok result

private def invariant {L} (rows : Wots.Rows L) (it : RowIter L) (back : RowIter L → RowIter L)
    (a : XmssKeysRust.address.Adrs) (first : U32) (size block : Usize) :=
  it.iter.slice=rows ∧ it.iter.i=it.count.val ∧ it.iter.i≤rows.length ∧
  ∀ other : RowIter L, other.iter.slice.length=rows.length →
    (back other).iter.slice.length=rows.length ∧
    (∀ j < it.iter.i, initialized rows.val[j]! (back other).iter.slice.val[j]! a first size block j) ∧
    (∀ j, it.iter.i≤j → j<rows.length → (back other).iter.slice.val[j]! = other.iter.slice.val[j]!)

theorem preparedRows {L} (rows : Wots.Rows L) (a : XmssKeysRust.address.Adrs) (first : U32)
    (size block : Usize) (keys : first.val+rows.length≤2^32)
    (minSize : 22≤size.val) (maxSize : size.val+3≤L.val) (bits : (block.val+size.val)*8<65536) :
    XmssKeysRust.xmss.wide.keys_loop0_loop0 ⟨⟨rows,0⟩,0#usize⟩ id a first size block ⦃ it back =>
      (back it).iter.slice.length=rows.length ∧
        ∀ j<rows.length, initialized rows.val[j]! (back it).iter.slice.val[j]! a first size block j ⦄ := by
  unfold XmssKeysRust.xmss.wide.keys_loop0_loop0
  apply loop.spec_decr_nat (measure := fun p : RowIter L × (RowIter L → RowIter L) => rows.length-p.1.iter.i)
    (inv := fun p => invariant rows p.1 p.2 a first size block)
  · rintro ⟨it,back⟩ ⟨slice,idx,bound,restore⟩
    simp only at slice idx bound restore ⊢
    unfold XmssKeysRust.xmss.wide.keys_loop0_loop0.body XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT]
    simp only [bind_tc_eq,Std.bind_assoc]
    apply WP.spec_bind (core.slice.iter.IteratorIterMut.next.spec it.iter)
    rintro ⟨item,next,back1⟩ ⟨hs,hnone,status⟩
    cases item with
    | none =>
      simp only [hnone,Option.map_none,bind_ok,step_simps]
      obtain ⟨length,done,_⟩ := restore ⟨next,it.count⟩ (by rw [hs,slice])
      exact ⟨length,fun j hj => done j (by rw [slice] at status; omega)⟩
    | some x =>
      obtain ⟨valid,rfl,advanced,restored⟩ := status
      have valid' : it.iter.i<rows.length := slice ▸ valid
      simp only [bind_ok,Std.bind_assoc,step_simps]
      step as ⟨nextCount,hCount⟩
      all_goals try (have cap := rows.property; change rows.length ≤ Usize.max at cap; scalar_tac)
      step as ⟨converted,hConverted⟩
      have cast : converted.val = it.iter.i := by rw [hConverted,idx]; scalar_tac
      step as ⟨key,hKey⟩
      all_goals try scalar_tac
      obtain ⟨row,op,_⟩ := spec_imp_exists (Keypadding.prepare_message_spec _ (asPad a) key size block minSize maxSize bits)
      unfold XmssKeysRust.xmss.wide.prepare_message
      rw [op]
      simp only [bind_ok,step_simps]
      refine ⟨⟨hs.trans slice,by change next.i=nextCount.val; omega,by change next.i≤rows.length; omega,fun other same => ?_⟩,by omega⟩
      simp only [Option.map_some,restored]
      let changed : RowIter L := {other with iter := {other.iter with slice := other.iter.slice.setAtNat it.iter.i row}}
      obtain ⟨length,done,suffix⟩ := restore changed (by simp [changed,same])
      have write := fun j => Slice.getElem!_Nat_setAtNat other.iter.slice it.iter.i j row (by simpa [same] using valid')
      refine ⟨length,fun j hj => ?_,fun j hj hj' => ?_⟩
      · by_cases eq : j=it.iter.i
        · subst j
          rw [suffix _ (by omega) valid']
          simp only [changed,write,ite_true]
          exact ⟨key,by omega,by simpa only [slice,getElem!_pos rows.val it.iter.i valid'] using op⟩
        · exact done j (by omega)
      · rw [suffix j (by omega) hj']
        simp only [changed,write,if_neg (show j ≠ it.iter.i by omega)]
  · simp [invariant]

end slhdsa.X86.XmssKeys
