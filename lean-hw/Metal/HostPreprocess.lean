import Metal.HostHash
import Metal.HostValues
open Aeneas Aeneas.Std Result slhdsa

namespace MetalHostHash
noncomputable section
def parameters (family : Spec.HashFamily) (p : params.Params) : Spec.Params :=
  {paramsS p with family}

def hashRequest {N : Usize} (family : Spec.HashFamily) (p : params.Params)
    (key rnd pk root : Array U8 N) (msg : Slice U8) :
    Result (Array U8 N × alloc.vec.Vec U8) := do
  match family with
  | .sha2 =>
    let r ← AppleInternal.slhdsa.hash.prf_msg key rnd msg
    let d ← AppleInternal.slhdsa.hash.h_msg p r pk root msg
    ok (r,d)
  | .shake =>
    let r ← shake_prf_msg key rnd msg
    let d ← shake_h_msg p r pk root msg
    ok (r,d)

def prepare {N : Usize} (family : Spec.HashFamily) (p : params.Params)
    (key rnd pk root : Array U8 N) (msg : Slice U8) := do
  let (r,d) ← hashRequest family p key rnd pk root msg
  let t ← digest_tree p d.deref
  let l ← digest_leaf p d.deref
  let n ← params.Params.md_bytes p
  let md ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8) d
    {start:=0#usize,«end»:=n}
  let indices ← util.base_2b md p.a (UScalar.cast .Usize p.k)
  ok (r,t,l,indices)

theorem hashRequest_fips {N : Usize} (family : Spec.HashFamily) (p : params.Params) (hp : PN p N)
    (key rnd pk root : Array U8 N) (msg : Slice U8) (room : Room msg.length (msgSlack N.val)) :
    hashRequest family p key rnd pk root msg ⦃ pair =>
      bytes pair.1.val=Spec.PRFmsg (parameters family p) (bytes key.val) (bytes rnd.val) (bytes msg.val) ∧
      bytes pair.2.val=Spec.Hmsg (parameters family p) (bytes pair.1.val) (bytes pk.val) (bytes root.val) (bytes msg.val) ∧
      pair.2.length=p.m.val ⦄ := by
  cases family with
  | sha2 =>
    unfold hashRequest
    step with AppleInternal.slhdsa.prf_msg_spec (paramsS p) hp.n hp.nok as ⟨r,hr⟩
    step with AppleInternal.slhdsa.h_msg_spec p hp.valid hp.n_eq as ⟨d,hd,size⟩
    exact ⟨hr,hd,size⟩
  | shake =>
    have space : msg.length+3*N.val≤Usize.max := by
      have n := hp.le32
      have cap := room.1
      unfold msgSlack at cap
      split at cap <;> omega
    unfold hashRequest
    step with shake_randomizer key rnd msg (by omega) as ⟨r,hr⟩
    step with shake_digest p r pk root msg space as ⟨d,hd⟩
    exact ⟨by simpa [parameters,Spec.PRFmsg,hp.n_eq] using hr,hd,
      by simpa [alloc.vec.Vec.length] using congrArg List.length hd⟩

theorem prepare_fips {N : Usize} (family : Spec.HashFamily) (p : params.Params) (hp : PN p N)
    (key rnd pk root : Array U8 N) (msg : Slice U8) (room : Room msg.length (msgSlack N.val)) :
    prepare family p key rnd pk root msg ⦃ v =>
      let P := parameters family p
      let r := Spec.PRFmsg P (bytes key.val) (bytes rnd.val) (bytes msg.val)
      let d := Spec.Hmsg P r (bytes pk.val) (bytes root.val) (bytes msg.val)
      bytes v.1.val=r ∧ v.2.1.val=Spec.digestTree P d ∧ v.2.2.1.val=Spec.digestLeaf P d ∧
      nats v.2.2.2.val=Spec.base2b (d.take P.mdBytes) P.a P.k ⦄ := by
  have hv := hp.valid
  unfold prepare
  step with hashRequest_fips family p hp key rnd pk root msg room as ⟨res,hr,hd,size⟩
  obtain ⟨r,d⟩ := res
  simp only at hr hd size
  step with tree_fips p d.deref hv (by simpa [vec_deref_length] using size) as ⟨t,tree,_⟩
  step with leaf_fips p d.deref hv (by simpa [vec_deref_length] using size) as ⟨l,leaf,_⟩
  have geometry := hv.m_eq
  simp only [paramsS_m] at geometry
  step with md_bytes_spec p hv as ⟨n,nb,ns⟩
  step with alloc.vec.Vec.index_Range_spec as ⟨md,read,len⟩
  step with base_2b_spec md p.a (UScalar.cast .Usize p.k) ⟨hv.a_pos,Nat.le_trans hv.a_le (by decide)⟩
    (by simp [len,nb];omega) as ⟨digits,decode,count,bound⟩
  simp only [vec_deref_val] at tree leaf
  rw [hr] at hd
  refine ⟨hr,?_,?_,?_⟩
  · rw [← hd]; exact tree
  · rw [← hd]; exact leaf
  · rw [← hd,decode,read]
    simp [List.slice,ns,parameters,Spec.Params.mdBytes]

end
end MetalHostHash
