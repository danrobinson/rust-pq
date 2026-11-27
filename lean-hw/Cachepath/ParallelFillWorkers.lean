import Cachepath.ParallelFillPlan
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.workers.fill
open nativeShake
set_option linter.concreteInstances false

private abbrev sha2Leaf {N : Usize} (p : params.Params) (sk : Array U8 N) (seed : hash.Seed N)
    (a : address.Adrs) (i : Nat) :=
  Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
    {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair := i}

theorem batch2 {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (start stop : Usize)
    (range : start.val≤stop.val) (cap : stop.val≤512) :
    sha2Batch start stop sk seed a ⦃ out => out.val.length=stop.val-start.val ∧
      ∀ j<out.val.length, bytes out.val[j]!.val=sha2Leaf p sk seed a (start.val+j) ⦄ := by
  unfold sha2Batch
  step as ⟨size,hsize⟩
  unfold sha2Batch_loop
  let I (q : Range × Nodes N) := q.1.end=stop ∧ start.val≤q.1.start.val ∧ q.1.start.val≤stop.val ∧
    q.2.val.length=q.1.start.val-start.val ∧
    ∀ j<q.2.val.length, bytes q.2.val[j]!.val=sha2Leaf p sk seed a (start.val+j)
  apply loop.spec_decr_nat (measure := fun q : Range × Nodes N => stop.val-q.1.start.val) (inv := I)
  · rintro ⟨it,v⟩ ⟨endEq,low,high,len,prior⟩
    simp only at endEq low high len prior ⊢
    unfold sha2Batch_loop.body
    by_cases live : it.start.val<stop.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [endEq] using live) as ⟨_,next,tag,idx,ends⟩
      simp only [tag,bind_ok]
      step with with_type_spec as ⟨a1,_,ha1⟩
      simp only [lift,bind_ok]
      step with with_keypair_spec as ⟨a2,ha2⟩
      step with wots_pk_gen_spec p hp sk seed hs a2 as ⟨item,value⟩
      step with alloc.vec.Vec.push_spec v item (by scalar_tac) as ⟨w,update⟩
      refine ⟨⟨ends.trans endEq,by change start.val≤next.start.val;omega,by change next.start.val≤stop.val;omega,by rw [update];simp;omega,?_⟩,by omega⟩
      intro j hj
      rw [update] at hj ⊢
      by_cases old : j<v.val.length
      · rw [List.getElem!_append_left _ _ _ old];exact prior j old
      · simp only [List.length_append,List.length_singleton] at hj
        have jeq : j=v.val.length := by omega
        subst j
        rw [List.getElem!_append_right _ _ _ (by omega),Nat.sub_self]
        have cast : (UScalar.cast .U32 it.start).val=it.start.val :=
          UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change it.start.val<2^32;omega)
        have index : start.val+v.val.length=it.start.val := by omega
        simpa [sha2Leaf,ha2,ha1,Spec.Adrs.setTypeAndClear,adrsS,address.WOTS_HASH,Spec.WOTS_HASH,cast,index] using value
    · have eq : it.start.val=stop.val := by omega
      step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [endEq];omega) as ⟨_,_,tag,_⟩
      simpa only [tag,step_simps,eq] using And.intro len prior
  · simpa [I,alloc.vec.Vec.with_capacity,alloc.vec.Vec.new] using range

theorem batchShake {N : Usize} [b : Backend] (s : Subtree.Single) (p : params.Params)
    (hp : PN p N) (detector : ∃ x, b.available N=ok x)
    (simd : b.available N=ok true → Subtree.Ops b s (N:=N) p)
    (sk pk : Array U8 N) (a : address.Adrs) (start stop : Usize)
    (range : start.val≤stop.val) (cap : stop.val≤512) :
    shakeBatch start stop sk pk a ⦃ out => out.val.length=stop.val-start.val ∧
      ∀ j<out.val.length, bytes out.val[j]!.val=Value p sk pk a 0 (start.val+j) ⦄ := by
  unfold shakeBatch
  step as ⟨n,size⟩
  have clone : (core.clone.CloneArray N core.clone.CloneU8).clone (Array.repeat N 0#u8) =
      ok (Array.repeat N 0#u8) := by
    obtain ⟨_,he,rfl⟩ := spec_imp_exists (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Array.repeat N 0#u8) (by intros; rfl))
    exact he
  step with alloc.vec.from_elem_spec _ _ n clone as ⟨v,_,len⟩
  simp only [lift,bind_ok,alloc.vec.Vec.deref_mut]
  have size' : v.slice.length=stop.val-start.val := len.trans size
  step with shake_offset s p hp detector simd sk pk a start v.slice (by omega) as ⟨r,row⟩
  obtain ⟨rl,values⟩ := row
  exact ⟨rl.trans size',fun j hj => values j (by change j<r.length at hj;omega)⟩

private def word (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩

private theorem word_val (n : Nat) (small : n≤512) : (word n).val=n := by
  change (BitVec.ofNat System.Platform.numBits n).toNat=n
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have := System.Platform.numBits_eq
  rcases this with h|h <;> rw [h] <;> omega

private def batchList {N : Usize} (job : Usize → Usize → Result (Nodes N))
    (start len : Nat) : Result (List (Array U8 N)) := do
  let v ← job (word start) (word (start+len))
  ok v.val

@[instance_reducible] def pool [b : Backend] (threads : Usize) : Pool where
  sha2 n sk seed a out := runtimeAttempt threads n out (batchList (fun start stop => sha2Batch start stop sk seed a))
  shake n sk pk a out := runtimeAttempt threads n out (batchList (fun start stop => shakeBatch start stop sk pk a))

theorem pool_correct [b : Backend] (s : Subtree.Single) (threads : Usize) {N : Usize}
    (detector : ∃ x, b.available N=ok x)
    (ops : b.available N=ok true → ∀ q, PN q N → Subtree.Ops b s (N:=N) q) :
    workers.Correct (pool threads) N := by
  constructor
  · intro p hp sk seed hs a n out pow size
    have small := Nat.pow_le_pow_right (by decide : 0<2) (valid_hp_le p hp.valid)
    have cap : n.val≤512 := by omega
    change runtimeAttempt threads n out _ ⦃ _ => _ ⦄
    rw [runtimeAttempt_eq _ _ _ _ cap]
    apply attempt_spec threads.val n.val out size
    intro start len fits
    have small := Nat.pow_le_pow_right (by decide : 0<2) (valid_hp_le p hp.valid)
    have cap : start+len≤512 := by omega
    have h0 := word_val start (by omega)
    have h1 := word_val (start+len) cap
    unfold batchList
    apply WP.spec_bind (batch2 p hp sk seed hs a _ _ (by rw [h0,h1];omega) (by rwa [h1]))
    intro v h; rw [WP.spec_ok]
    have extent : v.val.length=len := by rw [h.1,h0,h1];omega
    exact ⟨extent,fun j hj => by simpa only [h0] using h.2 j (extent ▸ hj)⟩
  · intro p hp sk pk a n out pow size
    have small := Nat.pow_le_pow_right (by decide : 0<2) (valid_hp_le p hp.valid)
    have cap : n.val≤512 := by omega
    change runtimeAttempt threads n out _ ⦃ _ => _ ⦄
    rw [runtimeAttempt_eq _ _ _ _ cap]
    apply attempt_spec threads.val n.val out size
    intro start len fits
    have small := Nat.pow_le_pow_right (by decide : 0<2) (valid_hp_le p hp.valid)
    have cap : start+len≤512 := by omega
    have h0 := word_val start (by omega)
    have h1 := word_val (start+len) cap
    unfold batchList
    apply WP.spec_bind (batchShake s p hp detector (fun active => ops active p hp) sk pk a _ _
      (by rw [h0,h1];omega) (by rwa [h1]))
    intro v h; rw [WP.spec_ok]
    have extent : v.val.length=len := by rw [h.1,h0,h1];omega
    exact ⟨extent,fun j hj => by simpa only [h0] using h.2 j (extent ▸ hj)⟩

end slhdsa.cache.builder.workers.fill
