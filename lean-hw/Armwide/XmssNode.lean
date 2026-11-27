import Armwide.XmssBatch
import Armwide.KeyDispatch
import X86key.FunsExternal
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves.Node
open Keygen Public.Dispatcher
noncomputable section

abbrev core.ops.range.RangeInclusive.contains := @X86KeyRust.core.ops.range.RangeInclusive.contains
abbrev wots.wots_pk_gen [Cpu] [Features] {N : Usize} := @Keygen.Dispatcher.wots.wots_pk_gen _ _ N
abbrev sha256.arm_wide.available [Cpu] := Public.Dispatcher.sha256.arm_wide.available

section
variable [Cpu] [Features]
def xmss.xmss_node
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  let b ←
    match N.val with
    | 16 => ok true
    | 24 => ok true
    | 32 => ok true
    | _ => ok false
  if b
  then
    let ri ← core.ops.range.RangeInclusive.new 1#u32 4#u32
    let b1 ←
      core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32
        core.cmp.PartialOrdU32 core.cmp.PartialOrdU32 ri z
    if b1
    then
      let b2 ← sha256.arm_wide.available
      if b2
      then xmss.arm.batch_root sk_seed i z seed adrs
      else
        if z = 0#u32
        then
          let a ← address.Adrs.with_type adrs address.WOTS_HASH
          let a1 ← address.Adrs.with_keypair a i
          wots.wots_pk_gen sk_seed seed a1
        else
          let i1 ← 2#u32 * i
          let i2 ← z - 1#u32
          let lnode ← xmss.xmss_node sk_seed i1 i2 seed adrs
          let i3 ← i1 + 1#u32
          let rnode ← xmss.xmss_node sk_seed i3 i2 seed adrs
          let a ← address.Adrs.with_type adrs address.TREE
          let a1 ← address.Adrs.with_word2 a z
          let a2 ← address.Adrs.with_word3 a1 i
          xmss.hash2 seed a2 lnode rnode
    else
      if z = 0#u32
      then
        let a ← address.Adrs.with_type adrs address.WOTS_HASH
        let a1 ← address.Adrs.with_keypair a i
        wots.wots_pk_gen sk_seed seed a1
      else
        let i1 ← 2#u32 * i
        let i2 ← z - 1#u32
        let lnode ← xmss.xmss_node sk_seed i1 i2 seed adrs
        let i3 ← i1 + 1#u32
        let rnode ← xmss.xmss_node sk_seed i3 i2 seed adrs
        let a ← address.Adrs.with_type adrs address.TREE
        let a1 ← address.Adrs.with_word2 a z
        let a2 ← address.Adrs.with_word3 a1 i
        xmss.hash2 seed a2 lnode rnode
  else
    if z = 0#u32
    then
      let a ← address.Adrs.with_type adrs address.WOTS_HASH
      let a1 ← address.Adrs.with_keypair a i
      wots.wots_pk_gen sk_seed seed a1
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let lnode ← xmss.xmss_node sk_seed i1 i2 seed adrs
      let i3 ← i1 + 1#u32
      let rnode ← xmss.xmss_node sk_seed i3 i2 seed adrs
      let a ← address.Adrs.with_type adrs address.TREE
      let a1 ← address.Adrs.with_word2 a z
      let a2 ← address.Adrs.with_word3 a1 i
      xmss.hash2 seed a2 lnode rnode
partial_fixpoint
end

private theorem inRange (z : U32) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdU32 core.cmp.PartialOrdU32
        core.cmp.PartialOrdU32 ⟨1#u32,4#u32,false⟩ z = ok (decide (1≤z.val ∧ z.val≤4)) := by
  simp only [core.ops.range.RangeInclusive.contains,X86KeyRust.core.ops.range.RangeInclusive.contains,
    Bool.false_eq_true,ite_false,core.cmp.PartialOrdU32,core.cmp.impls.PartialOrdU32.le,liftFun2,lift,bind_ok]
  by_cases h : 1≤z.val <;> simp [h]

private def scalarNode [Cpu] [Features] {N} (sk : Array U8 N) (i z : U32) (s : hash.Seed N) (a : address.Adrs) :=
  if z=0#u32 then do
    let a1 ← address.Adrs.with_type a address.WOTS_HASH
    let a2 ← address.Adrs.with_keypair a1 i
    wots.wots_pk_gen sk s a2
  else do
    let i1 ← 2#u32 * i
    let i2 ← z - 1#u32
    let l ← xmss.xmss_node sk i1 i2 s a
    let i3 ← i1 + 1#u32
    let r ← xmss.xmss_node sk i3 i2 s a
    let a1 ← address.Adrs.with_type a address.TREE
    let a2 ← address.Adrs.with_word2 a1 z
    let a3 ← address.Adrs.with_word3 a2 i
    xmss.hash2 s a3 l r

private theorem dispatch [cpu : Cpu] [Features] {N} (width : NOk N) (sk : Array U8 N) (i z : U32)
    (s : hash.Seed N) (a : address.Adrs) :
    xmss.xmss_node sk i z s a =
    if 1≤z.val ∧ z.val≤4 ∧ cpu.wide=true then xmss.arm.batch_root sk i z s a else scalarNode sk i z s a := by
  rw [xmss.xmss_node]
  rcases width with h|h|h <;> simp only [h,bind_ok,ite_true,core.ops.range.RangeInclusive.new,inRange,
      sha256.arm_wide.available,Public.Dispatcher.sha256.arm_wide.available]
  all_goals
    change (if decide (1≤z.val ∧ z.val≤4) then
      (if cpu.wide then xmss.arm.batch_root sk i z s a else scalarNode sk i z s a)
      else scalarNode sk i z s a) = _
    by_cases low : 1≤z.val <;> by_cases high : z.val≤4 <;> simp [low,high]

theorem node_fips [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (height : Nat) :
    ∀ (i z : U32), z.val=height → (i.val+1)*2^height≤2^32 →
    xmss.xmss_node sk i z seed a ⦃ out => slhdsa.bytes out.val=Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val)
      i.val height (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  induction height with
  | zero =>
    intro i z hz _
    have zero : z=0#u32 := by scalar_tac
    rw [dispatch hp.nok,if_neg (by omega)]
    simp only [scalarNode,zero,ite_true,address.Adrs.with_type,address.Adrs.with_keypair,bind_tc_eq,bind_ok,wots.wots_pk_gen]
    let leaf := {a with typ:=address.WOTS_HASH,keypair:=i,word2:=0#u32,word3:=0#u32}
    change Keygen.Dispatcher.wots.wots_pk_gen sk seed leaf ⦃ _ => _ ⦄
    rw [Keygen.Dispatcher.dispatch_eq_scalar p hp sk seed hs leaf (by with_unfolding_all rfl)]
    apply WP.spec_mono (wots_pk_gen_spec p hp sk seed hs leaf)
    intro out post
    simpa only [leaf,Spec.xmssNode,slhdsa.adrsS,Spec.Adrs.setTypeAndClear,Spec.WOTS_HASH,address.WOTS_HASH,show (0#u32 : U32).val=0 from rfl] using post
  | succ n ih =>
    intro i z hz limit
    rw [dispatch hp.nok]
    split
    · rename_i useWide
      have fast := batch_root_fips p hp seed hs sk a i z useWide.1 useWide.2.1 (hz ▸ limit)
      simpa only [hz] using fast
    · have nz : z≠0#u32 := by scalar_tac
      simp only [scalarNode,if_neg nz]
      have he : (2*i.val+2)*2^n=(i.val+1)*2^(n+1) := by ring
      have h1 : (2*i.val+1+1)*2^n≤2^32 := by rw [← he] at limit; exact limit
      have h0 : (2*i.val+1)*2^n≤2^32 := le_trans (Nat.mul_le_mul_right _ (by omega)) h1
      have hb : 2*i.val+2≤2^32 := (Nat.le_mul_of_pos_right _ (by exact Nat.pow_pos (by decide : 0<2))).trans h1
      step as ⟨left,le⟩
      step as ⟨child,ch⟩
      step with ih left child (by omega) (by simpa [le] using h0) as ⟨l,lh⟩
      step as ⟨right,ri⟩
      step with ih right child (by omega) (by simpa [ri,le] using h1) as ⟨r,rh⟩
      simp only [address.Adrs.with_type,address.Adrs.with_word2,address.Adrs.with_word3,bind_ok]
      apply WP.spec_mono (hash2_spec p hp seed hs _ l r)
      intro out post
      rw [post,lh,rh,ri,le,Spec.xmssNode]
      simp [slhdsa.adrsS,Spec.Adrs.setTypeAndClear,Spec.TREE,address.TREE,hz]

theorem node_eq_scalar [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (i z : U32)
    (limit : (i.val+1)*2^z.val≤2^32) :
    xmss.xmss_node sk i z seed a = slhdsa.xmss.xmss_node sk i z seed a := by
  obtain ⟨x,hx,xs⟩ := spec_imp_exists (node_fips p hp sk seed hs a z.val i z rfl limit)
  obtain ⟨y,hy,ys⟩ := spec_imp_exists (xmss_node_spec p hp sk i z seed hs a limit)
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (xs.trans ys.symm))

end
end slhdsa.Armwide.XmssLeaves.Node
