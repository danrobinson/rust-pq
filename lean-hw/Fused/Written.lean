import Fused.Capture
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused
open ShakeBatch NativeShakeWots.Signer
def WrittenPrefix {N : Usize} (p : params.Params) (sk seed : Array U8 N) (addr : address.Adrs)
    (digits : List U32) (slots stop : Nat) (before after : Signature) : Prop :=
  after.length=slots*N.val ∧ ∀ i<slots, ∀ b<N.val, Block after N.val i b=
    if i<stop then (signedChain p sk seed addr digits i)[b]! else Block before N.val i b


theorem written_wots {N : Usize} (p : params.Params) (hp : PN p N) (msg sk seed : Array U8 N)
    (a : address.Adrs) (digits : List U32) (slots : Nat) (initial out : Signature)
    (written : WrittenPrefix p sk seed a digits slots digits.length initial out)
    (room : digits.length≤slots) (count : digits.length=(Shake.params p).len)
    (decoded : nats digits=Spec.wotsDigits (Shake.params p) (bytes msg.val)) :
    bytes (out.val.take (digits.length*N.val))=Spec.wotsSign (Shake.params p) (bytes msg.val)
      (bytes sk.val) (bytes seed.val) (adrsS a) := by
  letI : Machine := Kldisp.machine
  let segment := out.val.take (digits.length*N.val)
  have bound : digits.length*N.val≤out.val.length := by
    change _≤out.length
    rw [written.1]
    exact Nat.mul_le_mul_right _ room
  have fits : out.val.length ≤ Usize.max := by simpa [alloc.vec.Vec.val] using out.slice.bound
  let v := alloc.vec.Vec.from segment (le_trans (List.length_take_le ..) (bound.trans fits))
  have bv : v.val=out.val.take (digits.length*N.val) := alloc.vec.Vec.from_val ..
  have values : SignedPrefix digits N.val (signedChain p sk seed a digits) digits.length v := by
    constructor
    · change v.val.length=_
      rw [bv,List.length_take,min_eq_left bound]
    · intro i hi _ b hb
      have last := Nat.mul_le_mul_right N.val hi
      have index : i*N.val+b<digits.length*N.val := by rw [Nat.succ_mul] at last;omega
      rw [bv]
      rw [getElem!_pos _ _ (by simp [index];omega),List.getElem_take,←getElem!_pos]
      exact (written.2 i (hi.trans_le room) b hb).trans (if_pos hi)
  have each (i : Nat) : (signedChain p sk seed a digits i).length=N.val := by
    unfold signedChain
    cases digit : (digits[i]!).val with
    | zero => simp [Spec.chain,Spec.PRF,Shake.params,hp.n_eq]
    | succ n => rw [chain_succ];simp [Spec.F,Shake.params,hp.n_eq]
  rw [←bv]
  change bytes v.val=(List.range (Shake.params p).len).flatMap (signStep _ _ _ _ (Spec.wotsDigits _ _))
  rw [signed_bytes v values each,←count,←decoded]
  apply List.flatMap_congr
  intro i hi
  simp only [signedChain,signStep,nats_getElem! _ _ (List.mem_range.mp hi)]

end slhdsa.Fused
