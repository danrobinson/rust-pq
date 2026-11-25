import Buffered.SmallWotsProgram
import Buffered.Leaves
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered.SmallWots
open ShakeBatch Spec.Keccak cache.builder.nativeShake.Vector.Fused NativeVerify
set_option linter.concreteInstances false
variable [kernel : Fused.Kernel]
local instance finishMachine : Machine := Fused.machine kernel

def finish (N K : Usize) (pk : Matrix 8#usize) (pos : Usize) := do
  let padded ← leaves_loop3 ⟨0#usize,K⟩ pk pos
  let state ← kernel.active padded K
  core.array.from_fn K (leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N K) state

theorem finish_keys {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (first : U32) (K : Usize) (pk : Matrix 8#usize) (pos : Usize)
    (width : K.val≤8) (room : first.val+K.val≤512) (rate : pos.val<17)
    (active : ActiveCorrect (Fused.machine kernel) kernel.active)
    (streams : ∀ l<K.val, (ShakeBatch.lane pk l,8*pos.val) = Fused.streamPrefix p sk seed a first.val l (Shake.params p).len) :
    finish N K pk pos ⦃ rows => LeafRows p sk seed a first.val rows ⦄ := by
  unfold finish
  have pad : leaves_loop3 ⟨0#usize,K⟩ pk pos ⦃ out => ∀ l<K.val, ShakeBatch.lane out l=padWords pos.val (ShakeBatch.lane pk l) ⦄ :=
    pad_rows_to K width pk pos rate
  step with pad as ⟨padded,tag⟩
  step with active padded K width as ⟨state,permuted⟩
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! K _ state
    (fun l (v : Array U8 N) => bytes v.val=Wots.digest N state l) ?_)
  · intro out reads l hl
    have read := reads l hl
    simp only [Array.getElem!_Nat_eq] at read
    have fin := FusedStream.finish_eq (ShakeBatch.lane pk l) pos.val
    change permute (padWords pos.val (ShakeBatch.lane pk l))=finalize (ShakeBatch.lane pk l,8*pos.val) at fin
    unfold NativeVerify.Wots.digest at read
    rw [permuted l hl,tag l hl,fin] at read
    rw [streams l hl] at read
    rw [read,Spec.xmssNode]
    have h : adrsS (Fused.laneAddress a address.WOTS_HASH first.val l) =
        {(adrsS a).setTypeAndClear Spec.WOTS_HASH with keypair:=first.val+l} := by
      unfold adrsS Fused.laneAddress Spec.Adrs.setTypeAndClear address.WOTS_HASH Spec.WOTS_HASH
      congr 1
      exact Nat.mod_eq_of_lt (show first.val+l<2^32 by omega)
    rw [← h]
    change Spec.shake256 _ N.val = Spec.shake256 _ (Shake.params p).n
    rw [show (Shake.params p).n=N.val from hp.n]
    rfl
  intro i hi
  simp only [leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N,
    leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut]
  step with Wots.extract_digest N state i hp.le32 (aligned_hash hp) (hi.trans_le width) as ⟨v,read⟩
  exact read

end slhdsa.Buffered.SmallWots
