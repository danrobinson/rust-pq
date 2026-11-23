import Xfors.Levels
import Leaf256.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Fors

/-- Every leaf and each in-place reduction of the production AVX-512 FORS subtree. -/
theorem subtree_fips {N} (p : params.Params) (hp : PN p N) (seed : XForsRust.hash.Seed N)
    (hs : SeedOk (TreeHash.seedOf (XForsRust.scalarSeed seed))) (sk : Array U8 N) (a : XForsRust.address.Adrs)
    (idx height : U32) (low : 0<height.val) (high : height.val≤7) (cpu : GatherRust.avx512Available=true)
    (limit : (idx.val+1)*2^height.val≤2^32) :
    XForsRust.fors.wide.subtree sk idx height seed a ⦃ out =>
      bytes out.val=Spec.forsNode (paramsS p) (bytes sk.val) idx.val height.val (bytes seed.pk_seed.val) (addressOf a) ⦄ := by
  unfold XForsRust.fors.wide.subtree
  have cap : 2^height.val≤128 := Nat.pow_le_pow_right (by decide) high
  step as ⟨n,nv⟩
  · rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
  have size : n.val=2^height.val := by
    simp only [nv,Nat.shiftLeft_eq,Nat.one_mul,Usize.size_scalarTac_eq.2]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> omega
  step as ⟨first,fv⟩
  have base : first.val=idx.val*2^height.val := by
    rw [fv,Nat.shiftLeft_eq,U32.size_eq]
    apply Nat.mod_eq_of_lt
    rw [Nat.add_one_mul] at limit
    have pos : 0<2^height.val := Nat.two_pow_pos _
    omega
  let roots : Nodes N := Array.repeat 128#usize (Array.repeat N 0#u8)
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice roots ⟨n⟩ (by scalar_tac))
  rintro ⟨s,back⟩ ⟨_,slen,restore⟩
  change s.length=n.val at slen
  have room : first.val+s.length≤2^32 := by rw [base,slen,size,←Nat.add_one_mul]; exact limit
  unfold XForsRust.sha256.x86.fors_leaves
  step with Leaf.fors_node_spec (paramsS p) N seed.state (bytes seed.pk_seed.val) sk (XForsRust.leafAddr a)
    first s hp.nok rfl hp.n (by simp) hs.1 cpu room as ⟨out,len,leaves⟩
  have prior : levelSpec p seed sk a idx.val height.val 0 (back out) := by
    intro j hj
    simp only [Nat.sub_zero] at hj ⊢
    rw [restore,List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega,by change j-0<out.length; omega,by simp; omega⟩]
    simp only [Nat.sub_zero]
    simpa only [base,Leaf.addressOf,XForsRust.leafAddr,addressOf,TreeHash.addr,XForsRust.scalarAddr] using leaves j (by omega)
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  step with reduceTree p hp seed hs sk a idx height n (back out) low high size prior limit cpu as ⟨tree,done⟩
  step as ⟨value,read⟩
  have root := done 0 (by simp)
  simpa [read,getElem!_pos] using root
end slhdsa.X86.Fors
