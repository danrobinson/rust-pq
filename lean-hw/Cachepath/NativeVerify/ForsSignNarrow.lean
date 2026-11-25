import Cachepath.NativeVerify.ForsSignBatches
import Shakebatch.Sign
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]

def ShortLaw (short : Short) := ∀ {N : Usize} (p : slhdsa.params.Params), PN p N →
  ∀ (seed : Array U8 N) (addrs : Array address.Adrs machine.width) (values : Rows N) (active : Usize),
  active.val ≤ machine.width.val → short seed addrs values active ⦃ out => ∀ j < active.val,
    bytes out.val[j]!.val = Spec.shake256 (bytes seed.val ++ ((adrsS addrs.val[j]!).bytes ++ bytes values.val[j]!.val)) N.val ⦄

def NodesLaw (nodes : Nodes) := ∀ {N : Usize} (p : slhdsa.params.Params), PN p N →
  ∀ (sk seed : Array U8 N) (a : address.Adrs) (ids : Array U32 machine.width) (z : U32) (active : Usize),
  (a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) → active.val ≤ machine.width.val → (∀ j < machine.width.val, (ids.val[j]!.val+1)*2^z.val < 2^32) →
  nodes sk seed a ids z active ⦃ out => ∀ j < active.val, bytes out.val[j]!.val=
    Spec.forsNode (Shake.params p) (bytes sk.val) ids.val[j]!.val z.val (bytes seed.val) (adrsS a) ⦄

theorem narrow_spec (short : Short) (nodes : Nodes) (hs : ShortLaw short) (hn : NodesLaw nodes)
    {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (choices : Slice U32) (nw : machine.width ≠ 8#usize) (enabled : 0 < machine.width.val)
    (count : choices.length=p.k.val) (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val) :
    narrow short nodes p choices sk seed a ⦃ out =>
      bytes out.val=(List.range p.k.val).flatMap (forsSignTree (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) ∧
      out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  have ha : p.a.val ≤ 14 := hp.valid.a_le
  have hk : choices.length ≤ 35 := count.symm ▸ hp.valid.k_le
  have maxN := hp.le32
  have strideBound := Nat.mul_le_mul (show p.a.val+1 ≤ 15 by omega) maxN
  have sizeBound := Nat.mul_le_mul hk strideBound
  unfold narrow
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
  have activeHash (addrs : Array address.Adrs machine.width) (active : Usize) (_ : 0 < active.val)
      (bound : active.val ≤ machine.width.val)
      (normalized : ∀ j < machine.width.val, addrs.val[j]! = {prf with word3 := addrs.val[j]!.word3}) :
      short seed addrs (Array.repeat machine.width sk) active ⦃ out =>
        ∀ j < active.val, ∀ b < N.val, out.val[j]!.val[b]! = field addrs.val[j]!.word3.val b ⦄ := by
    apply WP.spec_mono (hs p hp seed addrs _ active bound)
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
  step with secret_phase short p hp choices sk seed prf buf (Slice.len choices) stride rfl hk index enabled within room field activeHash as ⟨once,length,secrets⟩
  have ready : Ready p sk seed a choices stride.val 0 once := by
    refine ⟨length.trans (len.trans sz),?_⟩
    intro t ht z hz b hb which
    obtain rfl : z=0 := by omega
    have endOfRow := Nat.mul_le_mul_right stride.val (show t+1 ≤ choices.length by omega)
    rw [Nat.add_mul,Nat.one_mul] at endOfRow
    have atByte := secrets t b (by omega) (by omega)
    simp only [ht,hb,true_and,ite_true] at atByte
    simpa only [sigByte,Nat.zero_mul,Nat.zero_add,atByte,field,treeBlock,ite_true]
  simp only [bne_iff_ne.mpr nw,Bool.true_or,massert,ite_true,bind_ok]
  step as ⟨it,init,width⟩
  step with auth_batches nodes p hp sk seed a choices stride (Slice.len choices) it once
    (by rw [init]) (by rw [init];rfl) width ready rfl shape hk enabled index
    (fun ids z active _ bound lim => hn p hp sk seed a ids z active domain bound lim) as ⟨out,fields⟩
  refine ⟨prefix_bytes p hp sk seed a choices out count (shape ▸ fields),?_⟩
  rw [fields.1,count,shape,Nat.mul_assoc,Nat.add_comm]
end slhdsa.NativeVerify.ForsSign
