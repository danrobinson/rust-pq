import Ideal.Inst.MsgPrf128
open Ideal
instance (mlen : ℕ) : DecidablePred (msgLenLe mlen) := fun t => by
  rcases t with n | q | d <;> simp only [msgLenLe] <;> infer_instance
example (ℓ : ℕ) : DecidablePred (fun t => ¬ msgLenLe ℓ t) := inferInstance
example (ℓ : ℕ) : DecidablePred (fun t => ¬ msgLenLe ℓ t) := fun t => instDecidableNot
