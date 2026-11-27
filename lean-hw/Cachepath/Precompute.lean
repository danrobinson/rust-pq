import Cachepath.PrecomputeProgram

open Aeneas Aeneas.Std Result ControlFlow slhdsa slhdsa.cache slhdsa.cache.endtoend
namespace CacheopsRust.Public
open CacheopsRust.cache.constructor (TreeKernel)

private def Prefix {N : Usize} (p : Spec.Params) (sk pk : Spec.Bytes)
    (es : alloc.vec.Vec (CacheopsRust.cache.LayerD2Entry N)) (n : Nat) : Prop :=
  es.val.length = n ∧ ∀ i (h : i < es.val.length),
    let e := es.val[i]
    e.tree_index.val = i ∧ e.nodes.length = treeSize p.hp ∧
      Built e.nodes.deref p sk pk (layerAdrs (p.d-2) i)

private theorem fill {N : Usize} [b : Builders N] (p : Spec.Params)
    (d hp : U32) (hd : d.val = p.d) (hh : hp.val = p.hp) (layers : 2 ≤ p.d)
    (c : CacheopsRust.cache.TopTreeCache N) (secret pub : Array U8 N) (count : U64)
    (room : count.val ≤ Usize.max) (sha : c.family = .Sha2 → TreeKernel b.sha2 p)
    (shake : c.family = .Shake → TreeKernel b.shake p)
    (empty : alloc.vec.Vec (CacheopsRust.cache.LayerD2Entry N)) (start : empty.val = []) :
    cache.TopTreeCache.precompute_layer_d2_loop ⟨0#u64,count⟩ c d hp secret pub empty ⦃ out =>
      out.1 = c ∧ Prefix p (bytes secret.val) (bytes pub.val) out.2 count.val ⦄ := by
  unfold cache.TopTreeCache.precompute_layer_d2_loop
  apply loop.spec_decr_nat (measure := fun q => count.val-q.1.start.val)
    (inv := fun q => q.1.end = count ∧ q.1.start.val ≤ count.val ∧ q.2.1 = c ∧
      Prefix p (bytes secret.val) (bytes pub.val) q.2.2 q.1.start.val)
  · rintro ⟨it,self,es⟩ ⟨stop,bound,rfl,len,valid⟩
    simp only at stop bound len valid
    unfold cache.TopTreeCache.precompute_layer_d2_loop.body
    by_cases live : it.start.val < count.val
    · step with core.iter.range.IteratorRange.next_UScalar_some_spec
        (cloneInst := core.clone.CloneU64) (partialOrdInst := core.cmp.PartialOrdU64)
        (fun _ => rfl) (fun _ _ => rfl) it (by rwa [stop]) as ⟨o,it',item,inc,last⟩
      simp only [item]
      have build (builder : CacheopsRust.cache.mutation.Builder N) (kernel : TreeKernel builder p) :
          (do let layer ← d - 2#u32
              let ns ← builder hp layer it.start secret pub
              ok (self.family,ns)) ⦃ r => r.1 = self.family ∧ r.2.length = treeSize p.hp ∧
                Built r.2.deref p (bytes secret.val) (bytes pub.val) (layerAdrs (p.d-2) it.start.val) ⦄ := by
        step as ⟨l,hl⟩
        step with kernel hp l it.start secret pub hh as ⟨ns,sz,ok⟩
        exact ⟨sz,by simpa [hl,hd] using ok⟩
      have push (ns : alloc.vec.Vec (Array U8 N)) (sz : ns.length = treeSize p.hp)
          (ok : Built ns.deref p (bytes secret.val) (bytes pub.val) (layerAdrs (p.d-2) it.start.val)) :
          alloc.vec.Vec.push es (⟨it.start,ns⟩ : CacheopsRust.cache.LayerD2Entry N) ⦃ es' =>
            Prefix p (bytes secret.val) (bytes pub.val) es' it'.start.val ⦄ := by
        step as ⟨es',stored⟩
        constructor
        · simp [stored,len,inc]
        · intro i hi
          by_cases prev : i < es.val.length
          · simpa [stored,List.getElem_append_left prev] using valid i prev
          · have idx : i = it.start.val := by simp [stored] at hi; omega
            subst i
            simpa [stored,← len] using And.intro (rfl : it.start.val = it.start.val) (And.intro sz ok)
      cases hf : self.family with
      | Sha2 =>
        have h := build b.sha2 (sha hf)
        rw [hf] at h
        obtain ⟨⟨f,ns⟩,run,he,sz,ok⟩ := spec_imp_exists h
        obtain ⟨es',w,pref⟩ := spec_imp_exists (push ns sz ok)
        simp only [run,bind_ok,uncurry,w,WP.spec_ok]
        exact ⟨last.trans stop,by omega,by cases self; simp_all,pref,by omega⟩
      | Shake =>
        have h := build b.shake (shake hf)
        rw [hf] at h
        obtain ⟨⟨f,ns⟩,run,he,sz,ok⟩ := spec_imp_exists h
        obtain ⟨es',w,pref⟩ := spec_imp_exists (push ns sz ok)
        simp only [run,bind_ok,uncurry,w,WP.spec_ok]
        exact ⟨last.trans stop,by omega,by cases self; simp_all,pref,by omega⟩
    · step with core.iter.range.IteratorRange.next_UScalar_none_spec
        (partialOrdInst := core.cmp.PartialOrdU64) (fun _ _ => rfl) it (by rw [stop]; omega)
        as ⟨o,it',item,_⟩
      simp only [item,step_simps]
      exact ⟨len.trans (by omega),valid⟩
  · exact ⟨rfl,by simp,rfl, by simp [Prefix,start]⟩

/-- Every layer d-2 index has a correct tree in its direct lookup slot.
Precomputation preserves the key binding and grows capacity only if needed. -/
theorem precompute_spec {N : Usize} [b : Builders N] (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N) (c : CacheopsRust.cache.TopTreeCache N)
    (sk : Slice U8) (hs : sk.length = 4*N.val)
    (key : Spec.KeyOk (familyParams p c.family) (bytes sk.val))
    (hc : CacheValid c (familyParams p c.family) (Spec.block (familyParams p c.family) (bytes sk.val) 0)
      (Spec.block (familyParams p c.family) (bytes sk.val) 2))
    (sha : c.family = .Sha2 → TreeKernel b.sha2 (familyParams p c.family))
    (shake : c.family = .Shake → TreeKernel b.shake (familyParams p c.family)) :
    cache.TopTreeCache.precompute_layer_d2 c p sk ⦃ out =>
      let P := familyParams p c.family
      CacheValid out P (Spec.block P (bytes sk.val) 0) (Spec.block P (bytes sk.val) 2) ∧
      out.family = c.family ∧ out.layer_d2_capacity.val = max c.layer_d2_capacity.val (2^p.hp.val) ∧
      ∀ idx : U64, idx.val < 2^p.hp.val → ∃ h : idx.val < out.layer_d2.length,
        out.layer_d2.val[idx.val].tree_index = idx ⦄ := by
  let P := familyParams p c.family
  have hn : P.n = N.val := by cases h : c.family <;> simpa [P,h,familyParams,Shake.params,paramsS,toSlhParams] using hp.n
  have hd : p.d.val = P.d := by cases h : c.family <;> simp [P,h,familyParams,toSlhParams,paramsS,Shake.params]
  have hh : p.hp.val = P.hp := by cases h : c.family <;> simp [P,h,familyParams,toSlhParams,paramsS,Shake.params]
  have layers : 2 ≤ p.d.val := hp.valid.d_ge
  have small : p.hp.val ≤ 9 := hp.valid.hp_le
  have pow : 2^p.hp.val ≤ 512 := Nat.pow_le_pow_right (by decide : 0 < 2) small
  unfold cache.TopTreeCache.precompute_layer_d2
  simp only [compatible p hp c sk hs key hc,bind_ok,show ¬ p.d < 2#u32 by scalar_tac,ite_false]
  step with CacheopsRust.cache.constructor.keyBlock P hn sk 0#usize (by scalar_tac) as ⟨secret,hs0⟩
  step with CacheopsRust.cache.constructor.keyBlock P hn sk 2#usize (by scalar_tac) as ⟨pub,hs2⟩
  step as ⟨count,hcount⟩
  have cnt : count.val = 2^p.hp.val := by
    rw [hcount,Nat.one_shiftLeft]; apply Nat.mod_eq_of_lt; simp [U64.size,U64.numBits]; omega
  have room : count.val ≤ Usize.max := by have := usize_max_ge; omega
  let k := UScalar.cast .Usize count
  have cap : k.val = count.val := by apply UScalar.cast_val_mod_pow_of_inBounds_eq; scalar_tac
  simp only [lift,bind_ok]
  step with fill P p.d p.hp hd hh (hd ▸ layers) c secret pub count room sha shake
    (alloc.vec.Vec.with_capacity _ k) rfl as ⟨self,es,orig,filled⟩
  subst self
  obtain ⟨len,filled⟩ := filled
  rw [hs0,hs2] at filled
  have ready := fun cap' => precompute_d2_preserves_valid hc es (len.trans (cnt.trans (by rw [hh])))
    (fun i hi => filled i (by rw [len,cnt,hh]; exact hi)) cap'
  change (if c.layer_d2_capacity < k then _ else _) ⦃ _ => _ ⦄
  split <;> rename_i test
  · have h := ready k
    simp only [WP.spec_ok]
    exact ⟨h.1,trivial,by change k.val = max c.layer_d2_capacity.val (2^p.hp.val); rw [← cnt,← cap,Nat.max_eq_right (by scalar_tac : c.layer_d2_capacity.val ≤ k.val)],
      fun idx hi => h.2 idx (hh ▸ hi)⟩
  · have h := ready c.layer_d2_capacity
    simp only [WP.spec_ok]
    exact ⟨h.1,trivial,by change c.layer_d2_capacity.val = max c.layer_d2_capacity.val (2^p.hp.val); rw [← cnt,← cap,Nat.max_eq_left (by scalar_tac : k.val ≤ c.layer_d2_capacity.val)],
      fun idx hi => h.2 idx (hh ▸ hi)⟩

end CacheopsRust.Public
