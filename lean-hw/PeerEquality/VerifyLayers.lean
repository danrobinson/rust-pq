import PeerEquality.Layers

namespace slhdsa.PeerCall
open Spec

private def row (p : Params) (sig : Bytes) (j : Nat) :=
  (sig.drop (j * p.xmssSigBytes)).take p.xmssSigBytes

private def recoverLater (x : Xmss) (p : Params) (sig pk : Bytes)
    (st : Bytes × Nat) (j : Nat) : Bytes × Nat :=
  let leaf := st.2 &&& (2^p.hp - 1)
  let tree := st.2 >>> p.hp
  (x.recover leaf (row p sig j) st.1 pk (layer j tree), tree)

/-- The first XMSS call consumes the supplied leaf index. Every subsequent call
derives its leaf and tree from the previous tree, and consumes signature row j. -/
def htVerifyWith (x : Xmss) (p : Params) (msg sig pk : Bytes)
    (tree leaf : Nat) (expected : Bytes) : Bool :=
  let root := x.recover leaf (row p sig 0) msg pk (layer 0 tree)
  ((List.range' 1 (p.d-1)).foldl (recoverLater x p sig pk) (root,tree)).1 == expected

private def next (p : Params) (sig pk : Bytes) (st : Bytes × Nat × Nat)
    (j : Nat) : Bytes × Nat × Nat :=
  (xmssPkFromSig p st.2.2 (row p sig j) st.1 pk (layer j st.2.1),
   st.2.1 >>> p.hp, st.2.1 % 2^p.hp)

private theorem later_eq (x : Xmss) (p : Params) (rec : x.recover = xmssPkFromSig p)
    (sig pk : Bytes) (js : List Nat) (root : Bytes) (tree : Nat) :
    (js.foldl (recoverLater x p sig pk) (root,tree)).1 =
    (js.foldl (next p sig pk) (root,tree >>> p.hp,tree % 2^p.hp)).1 := by
  induction js generalizing root tree with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons, recoverLater, next, rec, Nat.and_two_pow_sub_one_eq_mod]
    apply ih

theorem htVerifyWith_fips (x : Xmss) (p : Params) (positive : 0 < p.d)
    (rec : x.recover = xmssPkFromSig p) : htVerifyWith x p = htVerify p := by
  funext msg sig pk tree leaf expected
  have split : List.range p.d = 0 :: List.range' 1 (p.d-1) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    rw [hk,List.range_eq_range']; rfl
  change (((List.range' 1 (p.d-1)).foldl (recoverLater x p sig pk)
    (x.recover leaf (row p sig 0) msg pk (layer 0 tree),tree)).1 == expected) =
    (((List.range p.d).foldl (next p sig pk) (msg,tree,leaf)).1 == expected)
  rw [later_eq x p rec, rec, split]
  rfl

end slhdsa.PeerCall
