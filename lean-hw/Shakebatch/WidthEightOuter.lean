import Shakebatch.WidthEightModel
import Fused.Outer
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight

/-- Concrete Rust dispatch from the public XMSS caller through both runtime
branches. Every published SHAKE parameter set has height at least three. -/
@[instance_reducible] noncomputable def Platform.outer (host : Platform) (p : params.Params) :
    Fused.Outer.Branches :=
  let hw := host.fused p
  { available := host.probe
    fused := fun p m sk idx seed a => @Fused.xmss_sign_batch (host.fused p) _ p m sk idx seed a
    subtree := hw.subtree
    keygen := fun {N} => match host with
      | .apple sha3 => @NativeShakeWots.keygen (AppleHybrid.machine sha3) ⟨NativeVerify.appleActive sha3⟩
          AppleSingleStream.ShakeForestApple.slhdsa.ShakeBatch.scalarStream N
      | .x86 => @NativeShakeWots.keygen Kxdispatch.machine
          ⟨NativeVerify.fullActive _ KxdispatchRust.shake256.parallel.available⟩ ShakeForestX86.slhdsa.ShakeBatch.scalarStream N
    sign := hw.narrowSign }

theorem outer_eq (host : Platform) {N : Usize} (p : params.Params) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (height : 3≤p.hp.val) :
    @Fused.Outer.shake.xmss.xmss_sign (host.outer p) N p m sk idx seed a =
      xmssSign host p m sk idx seed a := by
  cases on : host.available N with
  | false =>
    rw [Fused.Outer.off_sign (b:=host.outer p) (by exact (probe_eq host N).trans (by rw [on]))]
    simp [xmssSign,on]
  | true =>
    rw [Fused.Outer.on_sign (b:=host.outer p) (by exact (probe_eq host N).trans (by rw [on])) p height]
    simp only [xmssSign,height,decide_true,on,Bool.true_and,ite_true]
    rfl

end slhdsa.WidthEight
