import Fused.OuterProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Fused.Outer
set_option linter.concreteInstances false
variable [b : Branches]
set_option maxHeartbeats 1500000

theorem off_key {N : Usize} (off : b.available N=ok false)
    (sk seed : Array U8 N) (a : address.Adrs) :
    shake.wots.wots_pk_gen sk seed a=slhdsa.shake.wots.wots_pk_gen sk seed a := by
  simp only [shake.wots.wots_pk_gen,shake.batch.available,off,bind_ok,Bool.false_eq_true,ite_false,
    slhdsa.shake.wots.wots_pk_gen]

theorem off_wots {N : Usize} (off : b.available N=ok false)
    (m sk seed : Array U8 N) (a : address.Adrs) :
    shake.wots.wots_sign m sk seed a=slhdsa.shake.wots.wots_sign m sk seed a := by
  simp only [shake.wots.wots_sign,shake.batch.available,off,bind_ok,Bool.false_eq_true,ite_false,
    slhdsa.shake.wots.wots_sign]

theorem off_node {N : Usize} (off : b.available N=ok false)
    (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) :
    shake.xmss.xmss_node sk i z seed a=slhdsa.shake.xmss.xmss_node sk i z seed a := by
  induction h : z.val generalizing z i with
  | zero =>
    have zero : z=0#u32 := by scalar_tac
    subst z
    rw [shake.xmss.xmss_node.eq_def,slhdsa.shake.xmss.xmss_node.eq_def]
    simp only [show ¬(1#u32 ≤ 0#u32) by decide,ite_false,ite_true,off_key off]
  | succ n ih =>
    have ge : z≥1#u32 := by scalar_tac
    have nz : z≠0#u32 := by scalar_tac
    obtain ⟨prev,sub,next⟩ := spec_imp_exists (U32.sub_spec (x:=z) (y:=1#u32) (by scalar_tac))
    have dec : prev.val=n := by scalar_tac
    rw [shake.xmss.xmss_node.eq_def,slhdsa.shake.xmss.xmss_node.eq_def]
    simp only [ge,ite_true,nz,ite_false,shake.batch.available,off,bind_ok,Bool.false_eq_true,sub,
      ih _ _ dec]

private theorem off_loop {N : Usize} (off : b.available N=ok false) (p : params.Params)
    (sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : address.Adrs) (s : alloc.vec.Vec U8) (j : U32) :
    shake.xmss.xmss_sign_loop0 p.hp sk idx seed a s j=slhdsa.shake.xmss.xmss_sign_loop p sk idx seed a s j := by
  have body : shake.xmss.xmss_sign_loop0.body p.hp sk idx seed a =
      slhdsa.shake.xmss.xmss_sign_loop.body p sk idx seed a := by
    funext sig i
    simp only [shake.xmss.xmss_sign_loop0.body,slhdsa.shake.xmss.xmss_sign_loop.body,off_node off]
  unfold shake.xmss.xmss_sign_loop0 slhdsa.shake.xmss.xmss_sign_loop
  rw [body]

/-- A negative feature decision gives exactly the portable signer, including
failure or divergence, for arbitrary raw parameter and input values. -/
theorem off_sign {N : Usize} (off : b.available N=ok false) (p : params.Params)
    (m sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : address.Adrs) :
    shake.xmss.xmss_sign p m sk idx seed a = slhdsa.shake.xmss.xmss_sign p m sk idx seed a := by
  unfold shake.xmss.xmss_sign slhdsa.shake.xmss.xmss_sign
  have other (sig : alloc.vec.Vec U8) :
      shake.xmss.xmss_sign_loop1 p.hp sk idx seed a sig 0#u32 =
      shake.xmss.xmss_sign_loop0 p.hp sk idx seed a sig 0#u32 := rfl
  split <;> simp only [shake.batch.available,off,bind_ok,Bool.false_eq_true,ite_false,other,off_loop off,off_wots off]

theorem on_sign {N : Usize} (on : b.available N=ok true) (p : params.Params) (height : 3≤p.hp.val)
    (m sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : address.Adrs) :
    shake.xmss.xmss_sign p m sk idx seed a = b.fused p m sk idx seed a := by
  simp only [shake.xmss.xmss_sign,show p.hp≥3#u32 by scalar_tac,ite_true,shake.batch.available,on,bind_ok]

end slhdsa.Fused.Outer
