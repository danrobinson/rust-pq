import X86key.Leaf
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Key
set_option maxHeartbeats 400000

private theorem inRange (z : U32) :
    (do let ri ← core.ops.range.RangeInclusive.new 2#u32 4#u32
        X86KeyRust.core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32
          core.cmp.PartialOrdU32 core.cmp.PartialOrdU32 ri z) =
      ok (decide (2≤z.val ∧ z.val≤4)) := by
  simp only [core.ops.range.RangeInclusive.new,X86KeyRust.core.ops.range.RangeInclusive.contains,
    bind_tc_eq,bind_ok,Bool.false_eq_true,ite_false,core.cmp.PartialOrdU32,core.cmp.impls.PartialOrdU32.le,
    liftFun2,lift]
  by_cases h : 2≤z.val <;> simp [h]

private def scalarNode {N} (sk : Array U8 N) (i z : U32) (s : X86KeyRust.hash.Seed N) (a : X86KeyRust.address.Adrs) :=
  if z=0#u32 then do
    let a1 ← X86KeyRust.address.Adrs.with_type a X86KeyRust.address.WOTS_HASH
    let a2 ← X86KeyRust.address.Adrs.with_keypair a1 i
    X86KeyRust.wots.wots_pk_gen sk s a2
  else do
    let i1 ← 2#u32 * i
    let i2 ← z - 1#u32
    let l ← X86KeyRust.xmss.xmss_node sk i1 i2 s a
    let i3 ← i1 + 1#u32
    let r ← X86KeyRust.xmss.xmss_node sk i3 i2 s a
    let a1 ← X86KeyRust.address.Adrs.with_type a X86KeyRust.address.TREE
    let a2 ← X86KeyRust.address.Adrs.with_word2 a1 z
    let a3 ← X86KeyRust.address.Adrs.with_word3 a2 i
    X86KeyRust.xmss.hash2 s a3 l r

private theorem dispatch {N} (width : NOk N) (sk : Array U8 N) (i z : U32)
    (s : X86KeyRust.hash.Seed N) (a : X86KeyRust.address.Adrs) :
    X86KeyRust.xmss.xmss_node sk i z s a =
      if 2≤z.val ∧ z.val≤4 ∧ GatherRust.avx512Available=true
      then X86KeyRust.xmss.wide.batch_root sk i z s a else scalarNode sk i z s a := by
  rw [X86KeyRust.xmss.xmss_node]
  have contains : X86KeyRust.core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32 core.cmp.PartialOrdU32
        core.cmp.PartialOrdU32 ⟨2#u32,4#u32,false⟩ z = ok (decide (2≤z.val ∧ z.val≤4)) := by simpa only [core.ops.range.RangeInclusive.new,bind_tc_eq,bind_ok] using inRange z
  rcases width with h|h|h <;> simp only [h,bind_ok,ite_true,core.ops.range.RangeInclusive.new,contains,X86KeyRust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.avx512_available,WotsX86Rust.sha256.x86.has_avx512.get,GatherRust.sha256.x86.avx512_available]
  all_goals
    change (if decide (2≤z.val ∧ z.val≤4) then
      (if GatherRust.avx512Available then X86KeyRust.xmss.wide.batch_root sk i z s a else scalarNode sk i z s a)
      else scalarNode sk i z s a) = _
    by_cases low : 2≤z.val <;> by_cases high : z.val≤4 <;> simp [low,high]

theorem node_fips {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (s : X86KeyRust.hash.Seed N) (hs : SeedOk (seedOf s)) (a : X86KeyRust.address.Adrs)
    (height : Nat) : ∀ (i z : U32), z.val=height → (i.val+1)*2^height≤2^p.hp.val →
      X86KeyRust.xmss.xmss_node sk i z s a ⦃ out => bytes out.val=Spec.xmssNode (paramsS p) (bytes sk.val)
        i.val height (bytes s.pk_seed.val) (adrsS (addr a)) ⦄ := by
  induction height with
  | zero =>
    intro i z hz _
    have zero : z=0#u32 := by scalar_tac
    rw [dispatch hp.nok,if_neg (by omega)]
    simp only [scalarNode,zero,ite_true,X86KeyRust.address.Adrs.with_type,X86KeyRust.address.Adrs.with_keypair,bind_ok,
      leaf_eq hp.nok]
    simp only [bind_tc_eq,bind_ok]
    apply WP.spec_mono (wots_pk_gen_spec p hp sk (seedOf s) hs (addr {a with typ:=X86KeyRust.address.WOTS_HASH,keypair:=i,word2:=0#u32,word3:=0#u32}))
    intro out post
    rw [post]
    simp [Spec.xmssNode,addr,Wots.Wide.coreAddress,X86KeyRust.wideAddr,adrsS,Spec.Adrs.setTypeAndClear,
      Spec.WOTS_HASH,X86KeyRust.address.WOTS_HASH,seedOf,Wots.Wide.coreSeed,X86KeyRust.wideSeed]
  | succ n ih =>
    intro i z hz within
    rw [dispatch hp.nok]
    split
    · rename_i h
      apply WP.spec_mono (XmssRoot.batch_root_fips p hp (X86KeyRust.rootSeed s) hs sk (X86KeyRust.rootAddr a) i z h.1 h.2.1 h.2.2 (hz ▸ within))
      intro out post
      simpa only [hz,X86KeyRust.rootSeed,XmssRoot.addressOf,TreeHash.addr,XmssRootRust.parentAddr,X86KeyRust.rootAddr,addr,Wots.Wide.coreAddress,X86KeyRust.wideAddr] using post
    · have nonzero : z≠0#u32 := by scalar_tac
      simp only [scalarNode,if_neg nonzero]
      have he : (2*i.val+2)*2^n=(i.val+1)*2^(n+1) := by ring
      have h1 : (2*i.val+1+1)*2^n≤2^p.hp.val := by rw [← he] at within; exact within
      have h0 : (2*i.val+1)*2^n≤2^p.hp.val := le_trans (Nat.mul_le_mul_right _ (by omega)) h1
      have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
      have hb : 2*i.val+2≤512 := (Nat.le_mul_of_pos_right _ (by exact Nat.pow_pos (by decide : 0<2))).trans (h1.trans cap)
      step as ⟨left,le⟩
      step as ⟨child,ch⟩
      step with ih left child (by omega) (by simpa [le] using h0) as ⟨l,lh⟩
      step as ⟨right,ri⟩
      step with ih right child (by omega) (by simpa [ri,le] using h1) as ⟨r,rh⟩
      simp only [X86KeyRust.address.Adrs.with_type,X86KeyRust.address.Adrs.with_word2,
        X86KeyRust.address.Adrs.with_word3,bind_ok,X86KeyRust.xmss.hash2,XmssRootRust.xmss.hash2]
      apply WP.spec_mono (TreeHash.hash2_fips p hp (XmssRootRust.parentSeed (X86KeyRust.rootSeed s)) hs _ l r)
      intro out post
      rw [post,lh,rh,ri,le,Spec.xmssNode]
      simp [addr,Wots.Wide.coreAddress,X86KeyRust.wideAddr,TreeHash.addr,XmssRootRust.parentAddr,
        X86KeyRust.rootAddr,XmssRootRust.parentSeed,X86KeyRust.rootSeed,adrsS,Spec.Adrs.setTypeAndClear,
        Spec.TREE,X86KeyRust.address.TREE,hz]
end slhdsa.X86.Key
