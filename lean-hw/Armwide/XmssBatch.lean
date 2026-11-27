import Armwide.XmssFill
import Armwide.Xmss.SmallLevels
import Slhdsa.Proofs.Xmss
import Armwide.KeygenProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves
open Keygen ArmXmss
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private def smallSeed (st : Array U32 8#usize) : hash.Seed 16#usize :=
  ⟨Array.repeat 16#usize 0#u8,st,Array.repeat 8#usize 0#u64⟩

def xmss.arm.batch_root_16 (sk : Array U8 16#usize) (idx height : U32) (st : Array U32 8#usize)
    (a : slhdsa.address.Adrs) : Result (Array U8 16#usize) := do
  let first ← idx <<< height
  let count ← 1#usize <<< height
  let filled := leafBuffer 640#usize false (smallSeed st) sk a idx.val height.val
  let levels ← core.ops.range.RangeInclusive.new 1#u32 height
  let roots ← ArmXmss.xmss.arm.batch_root_16_loop0 levels st a first count filled
  Array.index_usize roots 0#usize

def xmss.arm.batch_root_512 [cpu : Features] {N : Usize} (L : Usize) (sk : Array U8 N)
    (idx height : U32) (seed : hash.Seed N) (a : slhdsa.address.Adrs) : Result (Array U8 N) := do
  let first ← idx <<< height
  let count ← 1#usize <<< height
  let filled := leafBuffer L cpu.sha512 seed sk a idx.val height.val
  let levels ← core.ops.range.RangeInclusive.new 1#u32 height
  let roots ← ArmXmss.xmss.arm.batch_root_512_loop0 cpu.sha512 levels seed.pk_seed seed.state seed.state512 a first count filled
  Array.index_usize roots 0#usize

section
variable [Features]
def xmss.arm.batch_root
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (index : Std.U32)
  (height : Std.U32) (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if N = 16#usize
  then
    let sk16 := Array.repeat 16#usize 0#u8
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut sk16)
    let s1 ← lift (Array.to_slice sk_seed)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let sk161 := to_slice_mut_back s2
    let root16 ← xmss.arm.batch_root_16 sk161 index height seed.state adrs
    let out := Array.repeat N 0#u8
    let (s3, to_slice_mut_back1) ← lift (Array.to_slice_mut out)
    let s4 ← lift (Array.to_slice root16)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    ok (to_slice_mut_back1 s5)
  else
    if N = 24#usize
    then xmss.arm.batch_root_512 1280#usize sk_seed index height seed adrs
    else xmss.arm.batch_root_512 2304#usize sk_seed index height seed adrs
end

private theorem layout (idx h first : U32) (count : Usize) (high : h.val≤4) (limit : (idx.val+1)*2^h.val≤2^32)
    (fv : first.val=(idx.val <<< h.val)%U32.size) (cv : count.val=(1 <<< h.val)%Usize.size) :
    first.val=idx.val*2^h.val ∧ count.val=2^h.val := by
  constructor
  · rw [fv,Nat.shiftLeft_eq,U32.size_eq]
    apply Nat.mod_eq_of_lt
    rw [Nat.add_one_mul] at limit
    have positive := Nat.two_pow_pos h.val
    omega
  · simp only [cv,Nat.shiftLeft_eq,Nat.one_mul,Usize.size_scalarTac_eq.2]
    apply Nat.mod_eq_of_lt
    have cap : 2^h.val≤16 := Nat.pow_le_pow_right (by decide) high
    rcases System.Platform.numBits_eq with v|v <;> rw [v] <;> omega

private theorem small_seed_buffer (seed : hash.Seed 16#usize) (sk : Array U8 16#usize) (a : slhdsa.address.Adrs)
    (idx h : Nat) : leafBuffer 640#usize false (smallSeed seed.state) sk a idx h = leafBuffer 640#usize false seed sk a idx h := by
  unfold leafBuffer
  congr 1

theorem small_root (p : params.Params) (hp : PN p 16#usize) (seed : hash.Seed 16#usize) (hs : SeedOk seed)
    (sk : Array U8 16#usize) (a : slhdsa.address.Adrs) (idx h : U32) (pos : 0<h.val) (high : h.val≤4)
    (limit : (idx.val+1)*2^h.val≤2^32) :
    xmss.arm.batch_root_16 sk idx h seed.state a ⦃ out => slhdsa.bytes out.val =
      Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) idx.val h.val (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  unfold xmss.arm.batch_root_16
  simp only [core.ops.range.RangeInclusive.new,bind_ok,small_seed_buffer]
  have leaves := fill_correct p hp 640#usize rfl false seed hs sk a idx.val h.val pos high limit
  step as ⟨first,fv⟩
  step as ⟨count,cv⟩
  · rcases System.Platform.numBits_eq with v|v <;> rw [v] <;> omega
  have spec := layout idx h first count high limit fv cv
  step with reduceSmall p hp seed hs sk a idx.val h first count _ pos high spec.1 spec.2 leaves limit as ⟨out,correct⟩
  step as ⟨r,read⟩
  simpa [read,getElem!_pos] using correct 0 (by simp)

theorem large_root [cpu : Features] {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (L : Usize) (buffer : L.val=total N.val) (wide : N.val=24 ∨ N.val=32)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (idx h : U32) (pos : 0<h.val) (high : h.val≤4)
    (limit : (idx.val+1)*2^h.val≤2^32) :
    xmss.arm.batch_root_512 L sk idx h seed a ⦃ out => slhdsa.bytes out.val =
      Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) idx.val h.val (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  unfold xmss.arm.batch_root_512
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  have leaves := fill_correct p hp L buffer cpu.sha512 seed hs sk a idx.val h.val pos high limit
  step as ⟨first,fv⟩
  step as ⟨count,cv⟩
  · rcases System.Platform.numBits_eq with v|v <;> rw [v] <;> omega
  have spec := layout idx h first count high limit fv cv
  step with reduceTree p hp seed hs wide cpu.sha512 sk a idx.val h first count _ pos high spec.1 spec.2 leaves limit as ⟨out,correct⟩
  step as ⟨r,read⟩
  simpa [read,getElem!_pos] using correct 0 (by simp)

/-- FIPS 205 Algorithm 9 at all heights selected by the Arm dispatcher. -/
theorem batch_root_fips [Features] {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (idx h : U32) (pos : 0<h.val) (high : h.val≤4)
    (limit : (idx.val+1)*2^h.val≤2^32) :
    xmss.arm.batch_root sk idx h seed a ⦃ out => slhdsa.bytes out.val =
      Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) idx.val h.val (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  unfold xmss.arm.batch_root
  split
  · rename_i small
    subst N
    simp only [Array.to_slice_mut,lift,bind_ok]
    step as ⟨s,sv⟩
    subst s
    have back (x : Array U8 16#usize) : Array.from_slice (Array.repeat 16#usize 0#u8) x.to_slice = x := by
      apply Aeneas.Std.Array.ext
      rw [Array.from_slice_val _ _ (by simp),Array.val_to_slice]
    rw [back]
    step with small_root p hp seed hs sk a idx h pos high limit as ⟨r,correct⟩
    step as ⟨s,sv⟩
    subst s
    rwa [back]
  · rename_i small
    split
    · rename_i medium
      subst N
      exact large_root p hp seed hs 1280#usize rfl (.inl rfl) sk a idx h pos high limit
    · rename_i medium
      have width := hp.nok
      have n : N.val=32 := by rcases width with x|x|x <;> scalar_tac
      exact large_root p hp seed hs 2304#usize (by rw [n];rfl) (.inr n) sk a idx h pos high limit

theorem batch_root_eq_scalar [Features] {N} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (idx h : U32) (pos : 0<h.val) (high : h.val≤4)
    (limit : (idx.val+1)*2^h.val≤2^32) :
    xmss.arm.batch_root sk idx h seed a = slhdsa.xmss.xmss_node sk idx h seed a := by
  obtain ⟨x,hx,xs⟩ := spec_imp_exists (batch_root_fips p hp seed hs sk a idx h pos high limit)
  obtain ⟨y,hy,ys⟩ := spec_imp_exists (xmss_node_spec p hp sk idx h seed hs a limit)
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (xs.trans ys.symm))

end
end slhdsa.Armwide.XmssLeaves
