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

/-- RustCrypto retains the previous tree index between iterations. The local loop
already holds the next layer's split tree and leaf indices. -/
private def align (p : Params) (st : Bytes × Nat) : Bytes × Nat × Nat :=
  (st.1, st.2 >>> p.hp, st.2 % 2^p.hp)

private theorem later_state (x : Xmss) (p : Params) (rec : x.recover = xmssPkFromSig p)
    (sig pk : Bytes) (js : List Nat) (st : Bytes × Nat) :
    align p (js.foldl (recoverLater x p sig pk) st) =
      js.foldl (next p sig pk) (align p st) := by
  induction js generalizing st with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp only [align, recoverLater, next, rec, Nat.and_two_pow_sub_one_eq_mod]

/-- Intermediate verification state after exactly k layers, including the indices
to use for the next layer. The zero case is the original unsplit input. -/
def verifyPrefix (x : Xmss) (p : Params) (msg sig pk : Bytes) (tree leaf : Nat) :
    Nat → Bytes × Nat × Nat
  | 0 => (msg, tree, leaf)
  | k+1 => align p ((List.range' 1 k).foldl (recoverLater x p sig pk)
      (x.recover leaf (row p sig 0) msg pk (layer 0 tree), tree))

theorem verifyPrefix_fips (x : Xmss) (p : Params) (rec : x.recover = xmssPkFromSig p)
    (msg sig pk : Bytes) (tree leaf k : Nat) :
    verifyPrefix x p msg sig pk tree leaf k =
      (List.range k).foldl (next p sig pk) (msg,tree,leaf) := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [List.range_eq_range', List.range'_succ, List.foldl_cons, verifyPrefix, later_state x p rec, rec]
    rfl

theorem htVerifyWith_fips (x : Xmss) (p : Params) (positive : 0 < p.d)
    (rec : x.recover = xmssPkFromSig p) : htVerifyWith x p = htVerify p := by
  funext msg sig pk tree leaf expected
  have split : List.range p.d = 0 :: List.range' 1 (p.d-1) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    rw [hk,List.range_eq_range']; rfl
  change (((List.range' 1 (p.d-1)).foldl (recoverLater x p sig pk)
    (x.recover leaf (row p sig 0) msg pk (layer 0 tree),tree)).1 == expected) =
    (((List.range p.d).foldl (next p sig pk) (msg,tree,leaf)).1 == expected)
  rw [split, List.foldl_cons]
  exact congrArg (fun st : Bytes × Nat × Nat => st.1 == expected)
    (later_state x p rec sig pk _ _ ) |>.trans (by rw [rec]; rfl)

end slhdsa.PeerCall
