import Shakebatch.PeerHashProgram

namespace PeerShake
open Spec (Bytes)
variable {S : Type} {x : Xof S}

/-- Contract of the lower-level SHAKE256 provider. The observer specifies precisely the
bytes already consumed, including the cached public seed. -/
structure Correct (x : Xof S) where
  consumed : S → Bytes → Prop
  empty : consumed x.empty []
  update : ∀ s pre part, consumed s pre → consumed (x.update s part) (pre ++ part)
  finish : ∀ s pre n, consumed s pre → x.finish s n = Spec.shake256 pre n

theorem fold_bytes (ok : Correct x) (parts : List Bytes) (s : S) (pre : Bytes) (h : ok.consumed s pre) :
    ok.consumed (parts.foldl x.update s) (pre ++ parts.flatten) := by
  induction parts generalizing pre s with
  | nil => simpa using h
  | cons a rest ih =>
    simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using
      ih (x.update s a) (pre++a) (ok.update s pre a h)

theorem seeded (ok : Correct x) (pk : Bytes) : ok.consumed (new_from_pk_seed x pk) pk := by
  simpa [new_from_pk_seed] using ok.update x.empty [] pk ok.empty

theorem prf_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (pk sk : Bytes) (a : Spec.Adrs) :
    prf_sk x p.n (new_from_pk_seed x pk) a.bytes sk=Spec.PRF p pk sk a := by
  rw [Spec.PRF,family]
  exact ok.finish _ _ _ (ok.update _ _ _ (ok.update _ _ _ (seeded ok pk)))

theorem f_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (pk m : Bytes) (a : Spec.Adrs) :
    f x p.n (new_from_pk_seed x pk) a.bytes m=Spec.F p pk a m := by
  rw [Spec.F,family]
  exact ok.finish _ _ _ (ok.update _ _ _ (ok.update _ _ _ (seeded ok pk)))

theorem h_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (pk a1 a2 : Bytes) (a : Spec.Adrs) :
    h x p.n (new_from_pk_seed x pk) a.bytes a1 a2=Spec.H p pk a (a1++a2) := by
  rw [Spec.H,family]
  simpa only [h,List.append_assoc] using ok.finish _ _ _
    (ok.update _ _ a2 (ok.update _ _ a1 (ok.update _ _ a.bytes (seeded ok pk))))

theorem t_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (pk : Bytes) (blocks : List Bytes) (a : Spec.Adrs) :
    t x p.n (new_from_pk_seed x pk) a.bytes blocks=Spec.T p pk a blocks.flatten := by
  rw [Spec.T,family]
  exact ok.finish _ _ _ (fold_bytes ok blocks _ _ (ok.update _ _ a.bytes (seeded ok pk)))

theorem prf_msg_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (sk_prf opt_rand : Bytes) (groups : List (List Bytes)) :
    prf_msg x p.n sk_prf opt_rand groups=Spec.PRFmsg p sk_prf opt_rand groups.flatten.flatten := by
  rw [Spec.PRFmsg,family]
  exact ok.finish _ _ _ (fold_bytes ok groups.flatten _ _
    (ok.update _ _ opt_rand (seeded ok sk_prf)))

theorem h_msg_fips (ok : Correct x) (p : Spec.Params) (family : p.family=.shake)
    (rand pk_seed pk_root : Bytes) (groups : List (List Bytes)) :
    h_msg x p.m rand pk_seed pk_root groups=Spec.Hmsg p rand pk_seed pk_root groups.flatten.flatten := by
  rw [Spec.Hmsg,family]
  exact ok.finish _ _ _ (fold_bytes ok groups.flatten _ _
    (ok.update _ _ pk_root (ok.update _ _ pk_seed (seeded ok rand))))

#print axioms prf_fips
#print axioms f_fips
#print axioms h_fips
#print axioms t_fips
#print axioms prf_msg_fips
#print axioms h_msg_fips
end PeerShake
