import Xmssroot.Levels
import Xmsskeys.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssRoot
open XmssRootRust (keySeed keyAddr parentSeed)

def fill {N} (G L : Usize) (seed : XmssRootRust.hash.Seed N) (sk : Array U8 N)
    (a : XmssRootRust.address.Adrs) (first : U32) (roots : Nodes N) (count : Usize) := do
  let (s,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) roots ⟨count⟩
  let keys ← XmssRootRust.xmss.wide.keys G L seed sk a first s
  ok (back keys)

theorem fill_spec {N} (G L : Usize) (p : params.Params) (hp : PN p N) (seed : XmssRootRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (parentSeed seed))) (sk : Array U8 N) (a : XmssRootRust.address.Adrs)
    (idx h : Nat) (first : U32) (roots : Nodes N) (count : Usize) (cpu : GatherRust.avx512Available=true)
    (format : XmssKeys.shape N G L) (base : first.val=idx*2^h) (size : count.val=2^h)
    (cap : count.val≤16) (room : (idx+1)*2^h≤2^p.hp.val) :
    fill G L seed sk a first roots count ⦃ out => levelSpec p seed sk a idx h 0 out ⦄ := by
  unfold fill XmssRootRust.xmss.wide.keys
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice roots ⟨count⟩ (by scalar_tac))
  rintro ⟨s,back⟩ ⟨_,slen,restore⟩
  have within : first.val+s.length≤2^p.hp.val := by rw [base,slen,size,← Nat.add_one_mul]; exact room
  step with XmssKeys.tree_leaves G L p hp (keySeed seed) hs sk (keyAddr a) first s cpu format within as ⟨out,len,leaves⟩
  change s.length=count.val at slen
  intro j hj
  simp only [Nat.sub_zero] at hj ⊢
  rw [restore,List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega,by change j-0<out.length; omega,by simp; omega⟩]
  simp only [Nat.sub_zero]
  simpa only [base,keySeed,keyAddr,addressOf,TreeHash.addr,XmssRootRust.parentAddr,WotsRust.addressOf,WotsX86Rust.asKernel,XmssKeysRust.asChecked] using leaves j (by omega)

/-- FIPS 205 Algorithm 9 for the AVX-512 subtree heights chosen by the x86 dispatcher. -/
theorem batch_root_fips {N} (p : params.Params) (hp : PN p N) (seed : XmssRootRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (parentSeed seed))) (sk : Array U8 N) (a : XmssRootRust.address.Adrs)
    (idx height : U32) (low : 2≤height.val) (high : height.val≤4) (cpu : GatherRust.avx512Available=true)
    (within : (idx.val+1)*2^height.val≤2^p.hp.val) :
    XmssRootRust.xmss.wide.batch_root sk idx height seed a ⦃ out =>
      bytes out.val=Spec.xmssNode (paramsS p) (bytes sk.val) idx.val height.val
        (bytes seed.pk_seed.val) (addressOf a) ⦄ := by
  have ph : p.hp.val≤9 := hp.valid.hp_le
  have treeCap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) ph
  have limit : (idx.val+1)*2^height.val≤2^32 := by omega
  have power : 2^height.val≤16 := Nat.pow_le_pow_right (by decide) high
  unfold XmssRootRust.xmss.wide.batch_root
  step as ⟨first,firstVal⟩
  step as ⟨count,countVal⟩
  · rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
  have base : first.val=idx.val*2^height.val := by
    rw [firstVal,Nat.shiftLeft_eq,U32.size_eq]
    apply Nat.mod_eq_of_lt
    rw [Nat.add_one_mul] at within
    exact lt_of_le_of_lt ((Nat.le_add_right _ _).trans (within.trans treeCap)) (by decide)
  have size : count.val=2^height.val := by
    simp only [countVal,Nat.shiftLeft_eq, Nat.one_mul,Usize.size_scalarTac_eq.2]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
  apply WP.spec_bind (Pₘ := levelSpec p seed sk a idx.val height.val 0)
  · split
    · apply fill_spec _ _ p hp seed hs sk a idx.val height.val _ _ _ cpu _ base size (by omega) within
      exact Or.inl ⟨by scalar_tac,rfl,rfl⟩
    · split
      · apply fill_spec _ _ p hp seed hs sk a idx.val height.val _ _ _ cpu _ base size (by omega) within
        exact Or.inr (Or.inl ⟨by scalar_tac,rfl,rfl⟩)
      · apply fill_spec _ _ p hp seed hs sk a idx.val height.val _ _ _ cpu _ base size (by omega) within
        have valid := hp.nok
        exact Or.inr (Or.inr ⟨by rcases valid with h|h|h <;> scalar_tac,rfl,rfl⟩)
  · intro roots leaves
    simp only [core.ops.range.RangeInclusive.new,bind_ok]
    step with reduceTree p hp seed hs sk a idx.val height first count roots (by omega) high base size leaves limit as ⟨out,done⟩
    step as ⟨value,read⟩
    have root := done 0 (by simp)
    simpa [read,getElem!_pos] using root
end slhdsa.X86.XmssRoot
