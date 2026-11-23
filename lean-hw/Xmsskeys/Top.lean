import Xmsskeys.Iterator
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys

/-- The production batched XMSS leaf generator returns consecutive FIPS WOTS public keys,
including when its last digest group uses only part of a register. -/
theorem keys_fips {N} (G L : Usize) (p : params.Params) (hp : PN p N) (seed : XmssKeysRust.hash.Seed N)
    (hs : SeedOk (seedOf seed)) (sk : Array U8 N) (a : XmssKeysRust.address.Adrs) (first : U32)
    (roots : Wots.Rows N) (cpu : GatherRust.avx512Available=true) (format : shape N G L)
    (room : ∀ g, g*G.val<roots.length → first.val+g*G.val+G.val≤2^32) :
    XmssKeysRust.xmss.wide.keys G L seed sk a first roots ⦃ out => out.length=roots.length ∧ ∀ j<out.length,
      bytes out.val[j]!.val = Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
        (Wots.leafAddress (XmssKeysRust.asChecked a) (first.val+j)) ⦄ := by
  let expected := fun j => Spec.wotsPkGen (paramsS p) (bytes sk.val) (bytes seed.pk_seed.val)
      (Wots.leafAddress (XmssKeysRust.asChecked a) (first.val+j))
  have width : 0<G.val := by rcases format with h|h|h <;> omega
  have hn := hp.le32
  unfold XmssKeysRust.xmss.wide.keys
  simp only [XmssKeysRust.params.LEN2]
  step as ⟨twice,ht⟩
  step as ⟨len,hl⟩
  have count : len.val=2*N.val+3 := by rw [hl,ht]
  simp only [XmssKeysRust.core.slice.Slice.chunks_mut,if_neg (Nat.ne_of_gt width),
    XmssKeysRust.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_ok]
  let inv := fun (it : Groups N) (back : Back N) =>
    it.iter.slice=roots ∧ it.iter.width=G ∧ it.iter.offset≤roots.length ∧
    (it.iter.offset<roots.length → it.iter.offset=it.count.val*G.val) ∧
    ∀ e : Groups N, e.iter.slice.length=roots.length →
      (back e).iter.slice.length=roots.length ∧
      (∀ j < it.iter.offset, bytes (back e).iter.slice.val[j]!.val=expected j) ∧
      (∀ j, it.iter.offset≤j → j<roots.length → (back e).iter.slice.val[j]! = e.iter.slice.val[j]!)
  apply WP.spec_bind (Pₘ := fun e : Groups N => e.iter.slice.length=roots.length ∧
    ∀ j<e.iter.slice.length, bytes e.iter.slice.val[j]!.val=expected j)
  · unfold XmssKeysRust.xmss.wide.keys_loop0
    apply loop.spec_decr_nat (measure := fun q : Groups N × Back N => roots.length-q.1.iter.offset)
      (inv := fun q => inv q.1 q.2)
    · rintro ⟨it,back⟩ ⟨src,w,bound,aligned,prior⟩
      simp only at src w bound aligned prior ⊢
      by_cases more : it.iter.offset<roots.length
      · have base := aligned more
        have prod : it.count.val ≤ it.count.val*G.val := Nat.le_mul_of_pos_right _ width
        have limit := roots.property
        change roots.length≤Usize.max at limit
        obtain ⟨part,next,restore,get,source,groupWidth,inc,partLen,advance,write⟩ :=
          chunk_some it (by simpa [src] using more) (by omega)
        rw [src,w] at partLen
        have used : part.length≤G.val := by omega
        have positive : 0<part.length := by omega
        rw [group_body _ _ _ _ _ _ _ _ _ _ _ _ _ get]
        step with group_spec G L p hp seed hs sk a first len it.count part cpu format count
          (room _ (base ▸ more)) positive used as ⟨out,length,digests⟩
        refine ⟨⟨source.trans src,groupWidth.trans w,by omega,?_,?_⟩,by omega⟩
        · intro still
          rw [advance,base,inc,Nat.add_mul,Nat.one_mul]
          have full : part.length=G.val := by omega
          omega
        · intro e elen
          let changed := restore e (some (it.count,out))
          have x : changed.iter.slice=e.iter.slice.setSlice! it.iter.offset out.val := write e out
          obtain ⟨result,earlier,later⟩ := prior changed (by rw [x,Slice.setSlice!_length,elen])
          refine ⟨result,fun j hj => ?_,fun j hj endPos => ?_⟩
          · by_cases before : j < it.iter.offset
            · exact earlier j before
            · have endPos : j<roots.length := by omega
              rw [later j (by omega) endPos,x,Slice.setSlice!_val,List.getElem!_setSlice!_middle _ _ _ _
                ⟨by omega,by change _<out.length; omega,by change j<e.iter.slice.length; omega⟩]
              have inside : j-it.iter.offset<part.length := by omega
              simpa only [← base,show first.val+it.iter.offset+(j-it.iter.offset)=first.val+j by omega] using digests _ inside
          · rw [later j (by omega) endPos,x,Slice.setSlice!_val,List.getElem!_setSlice!_suffix _ _ _ _
                (by change it.iter.offset+out.length≤j; omega)]
      · have get := chunk_none it (by rw [src]; omega)
        unfold XmssKeysRust.xmss.wide.keys_loop0.body
        change XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next _ it = _ at get
        rw [get]
        simp only [bind_tc_eq,bind_ok,step_simps]
        obtain ⟨len,done,_⟩ := prior it (by rw [src])
        exact ⟨len,fun j hj => done j (by omega)⟩
    · simp [inv]
  · intro e proof
    exact (WP.spec_ok _).mpr proof
end slhdsa.X86.XmssKeys
