import Cachepath.BuilderShakeProgram
import Cachepath.BuilderSha2
open Aeneas Aeneas.Std Result
namespace slhdsa.cache.builder.nativeShake
set_option linter.concreteInstances false

abbrev Rows (N : Usize) := Slice (Array U8 N)
abbrev It (N : Usize) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut (Array U8 N))
abbrev Value {N : Usize} (p : params.Params) (sk pk : Array U8 N) (a : address.Adrs) (z i : Nat) :=
  Spec.xmssNode (Shake.params p) (bytes sk.val) i z (bytes pk.val) (adrsS a)

def Row {N : Usize} (s : Rows N) (size : Nat) (expected : Nat → Spec.Bytes) :=
  s.length = size ∧ ∀ j < size, bytes s.val[j]!.val = expected j

/-- Contracts only on an active batched operation. Scalar-only execution discharges
these implications by its false detector. -/
structure Correct (b : Backend) (N : Usize) : Prop where
  detector : ∃ v, b.available N = ok v
  leaves : b.available N = ok true →
    ∀ (p : params.Params) (_ : PN p N) (sk pk : Array U8 N) (a : address.Adrs) (out : Rows N),
      out.length = 2^p.hp.val →
      @Backend.fill b N sk pk a 0#usize out ⦃ r => Row r out.length (Value p sk pk a 0) ⦄
  parents : b.available N = ok true →
    ∀ (p : params.Params) (_ : PN p N) (sk pk : Array U8 N) (a : address.Adrs) (z : U32)
      (children parents : Rows N), 0 < z.val → z.val ≤ p.hp.val →
      Row children (2 * width p.hp.val z.val) (Value p sk pk a (z.val-1)) →
      parents.length = width p.hp.val z.val →
      @Backend.pairs b N pk a z 0#usize children parents ⦃ r => Row r parents.length (Value p sk pk a z.val) ⦄

@[instance_reducible] def scalar : Backend where
  available _ := ok false
  fill _ _ _ _ _ := fail .panic
  pairs _ _ _ _ _ _ := fail .panic

theorem scalar_correct (N : Usize) : Correct scalar N := by
  refine ⟨⟨false,rfl⟩, ?_, ?_⟩ <;> intro h <;> have impossible : false = true := Result.ok_injective h <;> cases impossible

private def initialized {N : Usize} (rows : Rows N) (it : It N) (back : It N → It N)
    (f : Nat → Spec.Bytes) :=
  it.iter.slice = rows ∧ it.iter.i = it.count.val ∧ it.iter.i ≤ rows.length ∧
  ∀ other : It N, other.iter.slice.length = rows.length →
    (back other).iter.slice.length = rows.length ∧
    (∀ j < it.iter.i, bytes (back other).iter.slice.val[j]!.val = f j) ∧
    (∀ j, it.iter.i ≤ j → j < rows.length → (back other).iter.slice.val[j]! = other.iter.slice.val[j]!)

private theorem fill_loop {N : Usize} (p : params.Params) (hp : PN p N) (sk pk : Array U8 N)
    (a : address.Adrs) (rows : Rows N) (size : rows.length = 2^p.hp.val) :
    fill_leaves_chunk_loop ⟨⟨rows,0⟩,0#usize⟩ (fun e => e) sk pk a 0#usize ⦃ final =>
      Row final.iter.slice rows.length (Value p sk pk a 0) ⦄ := by
  unfold fill_leaves_chunk_loop
  apply loop.spec_decr_nat (measure := fun q : It N × (It N → It N) => rows.length-q.1.iter.i)
    (inv := fun q => initialized rows q.1 q.2 (Value p sk pk a 0))
  · rintro ⟨it,back⟩ ⟨slice,idx,bound,restore⟩
    simp only at slice idx bound restore ⊢
    unfold fill_leaves_chunk_loop.body XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
    simp only [XmssKeysRust.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT,
      bind_tc_eq,Std.bind_assoc]
    apply WP.spec_bind (core.slice.iter.IteratorIterMut.next.spec it.iter)
    rintro ⟨item,next,back1⟩ ⟨hs,hnone,status⟩
    cases item with
    | none =>
      simp only [hnone,Option.map_none,bind_ok,step_simps]
      obtain ⟨length,done,_⟩ := restore ⟨next,it.count⟩ (by rw [hs,slice])
      exact ⟨length,fun j hj => done j (by rw [slice] at status; omega)⟩
    | some x =>
      obtain ⟨valid,rfl,advanced,restored⟩ := status
      have valid' : it.iter.i < rows.length := slice ▸ valid
      simp only [bind_ok,Std.bind_assoc,step_simps]
      step as ⟨nextCount,hCount⟩
      all_goals try (have cap := rows.property; change rows.length ≤ Usize.max at cap; scalar_tac)
      step with with_type_spec as ⟨a1,_,ha1⟩
      step as ⟨k,hk⟩
      have cap := Nat.pow_le_pow_right (by decide : 0 < 2) (valid_hp_le p hp.valid)
      have cast : (UScalar.cast .U32 k).val = it.iter.i := by
        rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change k.val < 2^32; omega)]
        omega
      simp only [lift,bind_ok]
      step with with_keypair_spec as ⟨a2,ha2⟩
      rw [CacheScalar.wots_pk_gen_eq hp.le32]
      step with Shake.wots_pk_gen_spec p hp sk pk a2 as ⟨slot,hslot⟩
      refine ⟨⟨hs.trans slice,by change next.i = nextCount.val; omega,by change next.i ≤ rows.length; omega,
        fun other same => ?_⟩,by omega⟩
      simp only [Option.map_some,restored]
      let changed : It N := {other with iter := {other.iter with slice := other.iter.slice.setAtNat it.iter.i slot}}
      obtain ⟨length,done,suffix⟩ := restore changed (by simp [changed,same])
      have write := fun j => Slice.getElem!_Nat_setAtNat other.iter.slice it.iter.i j slot (by simpa [same] using valid')
      refine ⟨length,fun j hj => ?_,fun j hj hj' => ?_⟩
      · by_cases eq : j=it.iter.i
        · subst j
          rw [suffix _ (by omega) valid']
          simp only [changed,write,ite_true,hslot]
          simp [Value,Spec.xmssNode,ha2,ha1,adrsS,Spec.Adrs.setTypeAndClear,address.WOTS_HASH,Spec.WOTS_HASH,cast]
        · exact done j (by omega)
      · rw [suffix j (by omega) hj']
        simp only [changed,write,ite_eq_right (show j ≠ it.iter.i by omega)]
  · simp [initialized]

theorem fill_spec {N : Usize} [b : Backend] (hc : Correct b N) (p : params.Params) (hp : PN p N)
    (sk pk : Array U8 N) (a : address.Adrs) (rows : Rows N) (size : rows.length = 2^p.hp.val) :
    fill_leaves_chunk sk pk a 0#usize rows ⦃ out => Row out rows.length (Value p sk pk a 0) ⦄ := by
  obtain ⟨enabled,he⟩ := hc.detector
  unfold fill_leaves_chunk
  cases enabled
  · simp only [he,bind_ok,Bool.false_eq_true,↓reduceIte,core.slice.Slice.iter_mut,
      XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_eq]
    obtain ⟨final,run,post⟩ := spec_imp_exists (fill_loop p hp sk pk a rows size)
    change (do let e ← fill_leaves_chunk_loop ⟨⟨rows,0⟩,0#usize⟩ (fun x => x) sk pk a 0#usize; ok e.iter.slice) ⦃ out => Row out rows.length (Value p sk pk a 0) ⦄
    rw [run,bind_ok,WP.spec_ok]
    exact post
  · simpa only [he,bind_ok,↓reduceIte] using hc.leaves he p hp sk pk a rows size

end slhdsa.cache.builder.nativeShake
