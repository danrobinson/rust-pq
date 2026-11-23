import PeerEquality.CallerApi

namespace slhdsa.PeerCall
open Spec

theorem key_shape (c : Children) (p : Params) (valid : p.Valid) (node : c.xmss.node = xmssNode p)
    (a b d : Bytes) (ha : a.length=p.n) (hb : b.length=p.n) (hd : d.length=p.n) :
    (keygen c p a b d).Shape p :=
  ⟨ha,hb,hd,by simp [keygen,node,xmssNode_length p valid]⟩

theorem produced_shape (c : Children) (p : Params) (laws : ChildLaws c p) (valid : p.Valid)
    (k : Key) (shape : k.Shape p) (m : Parts) (r : Option Bytes) :
    (rawSign c p k m r).Shape p := by
  have pos : 0 < p.d := Nat.lt_of_lt_of_le (by decide : 0<2) valid.d_ge
  constructor
  · simpa [rawSign,laws.prfMsg _ _ _ shape.prf] using
      PRFmsg_length p valid k.prf (r.getD k.publicSeed) m.flatten.flatten
  · simp [rawSign,laws.forsSign,forsSign_length p valid]
  · rw [sign_fips c p laws pos k shape,slhSignInternal_length p valid]

/-- Every signature produced from the same three seeds is accepted by the
peer verification caller whenever the documented child contracts hold. -/
theorem round_trip (c : Children) (p : Params) (laws : ChildLaws c p) (valid : p.Valid)
    (a b d : Bytes) (ha : a.length=p.n) (hb : b.length=p.n) (hd : d.length=p.n)
    (msg : Parts) (rand : Option Bytes) :
    let k := keygen c p a b d
    rawVerify c k.public msg (rawSign c p k msg rand) = true := by
  let k := keygen c p a b d
  have shape : k.Shape p := key_shape c p valid laws.node _ _ _ ha hb hd
  have pos : 0 < p.d := Nat.lt_of_lt_of_le (by decide : 0<2) valid.d_ge
  have hgen := keygen_fips c p laws.node a b d
  have keyok := keygen_keyOk p valid a b d ha hb hd
  have hs : k.bytes = (slhKeygenInternal p a b d).1 := congrArg Prod.fst hgen
  have hp : k.public.bytes = (slhKeygenInternal p a b d).2 := congrArg Prod.snd hgen
  change rawVerify c k.public msg (rawSign c p k msg rand) = true
  rw [verify_fips c p laws k.public ⟨shape.publicSeed,shape.root⟩ _ _ (produced_shape c p laws valid k shape msg rand),
    sign_fips c p laws pos k shape,hs,hp,keyok.2]
  exact slh_complete_internal p valid _ _ _ keyok.1

end slhdsa.PeerCall
