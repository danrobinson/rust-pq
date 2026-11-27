import ForsDriver.Fields
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify ForsSign
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [kernel : Fused.Kernel]
local instance prepareMachine : Machine := Fused.machine kernel

def prepare
  {N : Std.Usize} (p : params.Params) (selections : Slice Std.U32)
  (sk : Array Std.U8 N) (seed : Array Std.U8 N) (addr : address.Adrs) :
  Result (Std.Usize × address.Adrs × Buffer)
  := do
  let k := Slice.len selections
  let i ← lift (UScalar.cast .Usize p.a)
  let i1 ← i + 1#usize
  let stride ← i1 * N
  let i2 ← k * stride
  let sig ← alloc.vec.from_elem core.clone.CloneU8 0#u8 i2
  let a ← address.Adrs.with_type addr address.FORS_PRF
  let prf ← address.Adrs.with_keypair a addr.keypair
  let a1 ← address.Adrs.with_type addr address.FORS_TREE
  let tree_adrs ← address.Adrs.with_keypair a1 addr.keypair
  let sig1 ←
    ForsSign.sign_loop0 (ActiveHash.short_active kernel.active) selections sk seed k p.a stride sig prf 0#usize
  ok (stride,tree_adrs,sig1)

theorem prepare_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (count : choices.length=p.k.val) (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    prepare p choices sk seed a ⦃ (stride,tree,once) =>
      stride.val=(p.a.val+1)*N.val ∧ adrsS tree=adrsS a ∧
      Fields N.val choices.length (p.a.val+1) stride.val (treeBlock p sk seed a choices)
        (fun _ z => z≤0) once ⦄ := by
  have ha : p.a.val ≤ 14 := hp.valid.a_le
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  have maxN := hp.le32
  have strideBound := Nat.mul_le_mul (show p.a.val+1 ≤ 15 by omega) maxN
  have sizeBound := Nat.mul_le_mul hk strideBound
  unfold prepare
  simp only [lift,bind_ok]
  have cast : (UScalar.cast .Usize p.a).val=p.a.val := by scalar_tac
  step as ⟨plus,pv⟩
  step as ⟨stride,sv⟩
  have shape : stride.val=(p.a.val+1)*N.val := by rw [sv,pv,cast]
  have fit : choices.length*stride.val ≤ Usize.max := by rw [shape];scalar_tac
  step as ⟨size,sz⟩
  all_goals try scalar_tac
  step as ⟨buf,zeros,len⟩
  step as ⟨typed,typeOf,rest⟩
  step as ⟨prf,key⟩
  step as ⟨tree,tag,clear⟩
  step as ⟨treeAddr,treeKey⟩
  let field := fun (idx b : Nat) => (⟨(Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) idx)[b]!⟩ : U8)
  let machine := Fused.machine kernel
  have activeHash (addrs : Array address.Adrs machine.width) (active : Usize) (_ : 0 < active.val)
      (bound : active.val ≤ machine.width.val)
      (normalized : ∀ j < machine.width.val, addrs.val[j]! = {prf with word3 := addrs.val[j]!.word3}) :
      (ActiveHash.short_active kernel.active) seed addrs (Array.repeat machine.width sk) active ⦃ out =>
        ∀ j < active.val, ∀ b < N.val, out.val[j]!.val[b]! = field addrs.val[j]!.word3.val b ⦄ := by
    apply WP.spec_mono (ActiveHash.short_correct kernel.active perm p hp seed addrs _ active bound)
    intro out f j hj b hb
    have h := f j hj
    have ix := normalized j (hj.trans_le bound)
    have exp : bytes out.val[j]!.val = Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val)
        (adrsS a) addrs.val[j]!.word3.val := by
      rw [h,Array.repeat_val]
      conv_lhs => arg 1; arg 2; arg 1; rw [ix]
      simp [key,rest,Spec.forsSkGen,Spec.PRF,Shake.params,paramsS_n,hp.n_eq,adrsS,
        Spec.Adrs.setTypeAndClear,Spec.FORS_PRF,fors_FORS_PRF_eq,hj.trans_le bound,List.append_assoc]
    apply congrArg (fun v : BitVec 8 => (⟨v⟩ : U8))
    have valid : b < out.val[j]!.val.length := by simpa using hb
    change (out.val[j]!.val[b]!).bv = _
    rw [getElem!_pos (out.val[j]!.val) b valid,←bytes_getElem! _ _ valid,exp]
  have room : choices.length*stride.val ≤ buf.length := by rw [len,sz];rfl
  have within : N.val ≤ stride.val := by rw [shape,Nat.add_mul];omega
  step with secret_phase (ActiveHash.short_active kernel.active) p hp choices sk seed prf buf (Slice.len choices) stride rfl hk index (by change 0<8; decide) within room field activeHash as ⟨once,length,secrets⟩
  have ready : Ready p sk seed a choices stride.val 0 once := by
    refine ⟨length.trans (len.trans sz),?_⟩
    intro t ht z hz b hb which
    obtain rfl : z=0 := by omega
    have endOfRow := Nat.mul_le_mul_right stride.val (show t+1 ≤ choices.length by omega)
    rw [Nat.add_mul,Nat.one_mul] at endOfRow
    have atByte := secrets t b (by omega) (by omega)
    simp only [ht,hb,true_and,ite_true] at atByte
    simpa only [sigByte,Nat.zero_mul,Nat.zero_add,atByte,field,treeBlock,ite_true]
  refine ⟨shape,?_,ready.1,?_⟩
  · simp [treeKey,clear,adrsS,domain.1,domain.2.1,domain.2.2]
  · intro t ht z hz b hb present
    exact ready.2 t ht z (by omega) b hb (by omega)
end slhdsa.ForsDriver
