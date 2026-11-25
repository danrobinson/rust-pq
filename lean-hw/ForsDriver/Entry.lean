import ForsDriver.Prepare
import ForsDriver.Low
import ForsDriver.Upper
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsDriver
open ShakeBatch NativeVerify
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel] [trees : Trees]

private def staged {N : Usize} (p : params.Params) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) := do
  let (stride,tree,once) ← prepare p choices sk seed a
  let s1 ← low0 p choices sk seed a stride once
  let s2 ← low1 p choices sk seed a tree stride s1
  let s3 ← low2 p choices sk seed a tree stride s2
  sign_loop8 ⟨0#usize,choices.len⟩ choices sk seed a.layer a.tree a.typ a.keypair a.word2 a.word3 p.a stride s3

theorem raw_eq {N : Usize} (p : params.Params) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs) (hk : choices.length≤35) (lo : 3≤p.a.val) :
    sign p choices sk seed a=staged p choices sk seed a := by
  have small : choices.len ≤ params.K_MAX := by rw [params.K_MAX]; exact hk
  have h0 : p.a > 0#u32 := by scalar_tac
  have h1 : p.a > 1#u32 := by scalar_tac
  have h2 : p.a > 2#u32 := by scalar_tac
  simp only [sign,staged,prepare,low0,low1,low2,leafPrefix,pairPrefix,h0,h1,h2,ite_true,
    bne_self_eq_false,Bool.false_or,decide_eq_true small,massert,bind_tc_eq,Std.bind_assoc,bind_ok]
  try rfl

theorem sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (choices : Slice U32)
    (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (count : choices.length=p.k.val) (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) (lo : 3≤p.a.val)
    (nodes : UpperNodes p sk seed a) :
    sign p choices sk seed a ⦃ out =>
      bytes out.val=(List.range p.k.val).flatMap (forsSignTree (Shake.params p)
        (bytes sk.val) (bytes seed.val) (adrsS a) (nats choices.val)) ∧
      out.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  have hk : choices.length≤35 := count.symm ▸ hp.valid.k_le
  rw [raw_eq p choices sk seed a hk lo]
  unfold staged
  step with prepare_spec p hp choices sk seed a domain count index perm as ⟨prepared,shape,eqTree,zero⟩
  rcases prepared with ⟨stride,tree,s0⟩
  dsimp only at shape eqTree zero ⊢
  step with low0_spec p hp choices sk seed a stride s0 hk index domain shape perm (by omega) zero as ⟨s1,one⟩
  step with low1_spec p hp choices sk seed a tree stride s1 hk index domain eqTree shape perm (by omega) one as ⟨s2,two⟩
  step with low2_spec p hp choices sk seed a tree stride s2 hk index domain eqTree shape perm (by omega) two as ⟨s3,three⟩
  apply WP.spec_mono (upper p hp choices sk seed a stride s3 shape lo hk index nodes three)
  intro out full
  have done : SigPrefix p sk seed a choices stride.val choices.length out :=
    ⟨full.1, fun t ht z hz b hb => full.2 t ht z (by omega) b hb trivial⟩
  refine ⟨prefix_bytes p hp sk seed a choices out count (shape ▸ done),?_⟩
  rw [full.1,count,shape,Nat.mul_assoc,Nat.add_comm]

end slhdsa.ForsDriver
