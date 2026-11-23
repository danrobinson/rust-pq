import Spec.SlhDsa

namespace slhdsa.PeerCall
open Spec

/-- XMSS observations at the peer's typed boundary. The serialized output
and recovered node are opaque until child correctness is supplied. -/
structure Xmss where
  sign : Bytes → Bytes → Nat → Bytes → Adrs → Bytes
  recover : Nat → Bytes → Bytes → Bytes → Adrs → Bytes
  node : Bytes → Nat → Nat → Bytes → Adrs → Bytes

def xmssSpec (p : Params) : Xmss := ⟨xmssSign p,xmssPkFromSig p,xmssNode p⟩

def layer (j tree : Nat) : Adrs := { Adrs.zero with layer := j, tree := tree }

private def later (c : Xmss) (p : Params) (sk pk : Bytes) :
    List Nat → Bytes → Bytes → Nat → Bytes
  | [], acc, _, _ => acc
  | j::js, acc, root, tree =>
    let leaf := tree % 2^p.hp
    let next := tree >>> p.hp
    let a := layer j next
    let sig := c.sign root sk leaf pk a
    let acc := acc ++ sig
    match js with
    | [] => acc
    | _::_ => later c p sk pk js acc (c.recover leaf sig root pk a) next

/-- First layer signs the original message. The peer recovers that first
root immediately, then skips recovery only after the final loop iteration. -/
def ht (c : Xmss) (p : Params) (msg sk pk : Bytes) (tree leaf : Nat) : Bytes :=
  let a := layer 0 tree
  let sig := c.sign msg sk leaf pk a
  let root := c.recover leaf sig msg pk a
  later c p sk pk (List.range' 1 (p.d-1)) sig root tree

private def step (c : Xmss) (p : Params) (sk pk : Bytes)
    (st : Bytes × Bytes × Nat × Nat) (j : Nat) : Bytes × Bytes × Nat × Nat :=
  let (acc,msg,tree,leaf) := st
  let a := layer j tree
  let s := c.sign msg sk leaf pk a
  (acc ++ s, c.recover leaf s msg pk a, tree >>> p.hp, tree % 2^p.hp)

private theorem later_is_fold (c : Xmss) (p : Params) (sk pk : Bytes) (js : List Nat)
    (acc root : Bytes) (tree : Nat) :
    later c p sk pk js acc root tree =
      (js.foldl (step c p sk pk) (acc,root,tree >>> p.hp,tree % 2^p.hp)).1 := by
  induction js generalizing acc root tree with
  | nil => rfl
  | cons j js ih =>
    cases js with
    | nil => rfl
    | cons k ks =>
      exact ih _ _ _

/-- The root component after the final layer is a mathematical observation;
the peer's signing routine only demands the accumulated signature at that point. -/
def signPrefix (c : Xmss) (p : Params) (msg sk pk : Bytes) (tree leaf k : Nat) :=
  (List.range k).foldl (step c p sk pk) ([],msg,tree,leaf)

/-- State at a nonfinal cut of the peer's later-layer loop. Its index is
the tree just used. The next iteration splits that index on entry. -/
def peerSignStep (c : Xmss) (p : Params) (sk pk : Bytes)
    (st : Bytes × Bytes × Nat) (j : Nat) : Bytes × Bytes × Nat :=
  let (acc,root,tree) := st
  let leaf := tree % 2^p.hp
  let next := tree >>> p.hp
  let a := layer j next
  let sig := c.sign root sk leaf pk a
  (acc ++ sig, c.recover leaf sig root pk a, next)

/-- Splitting the source loop at any nonfinal cut consumes exactly this
prefix of peer transitions, for every remaining layer and arbitrary children. -/
theorem later_cut (c : Xmss) (p : Params) (sk pk : Bytes) (js : List Nat)
    (j : Nat) (rest : List Nat) (acc root : Bytes) (tree : Nat) :
    later c p sk pk (js ++ j :: rest) acc root tree =
      let st := js.foldl (peerSignStep c p sk pk) (acc,root,tree)
      later c p sk pk (j :: rest) st.1 st.2.1 st.2.2 := by
  induction js generalizing acc root tree with
  | nil => rfl
  | cons k ks ih =>
    cases ks with
    | nil => rfl
    | cons l ls => exact ih _ _ _

private def alignSign (p : Params) (st : Bytes × Bytes × Nat) :=
  (st.1,st.2.1,st.2.2 >>> p.hp,st.2.2 % 2^p.hp)

private theorem alignSign_fold (c : Xmss) (p : Params) (sk pk : Bytes) (js : List Nat)
    (st : Bytes × Bytes × Nat) :
    alignSign p (js.foldl (peerSignStep c p sk pk) st) =
      js.foldl (step c p sk pk) (alignSign p st) := by
  induction js generalizing st with
  | nil => rfl
  | cons j js ih => exact ih _

/-- After the first signature and k further recoveries, all live peer
fields determine exactly the local signing prefix, including both next indices.
At the final layer only the signature component is demanded by the peer. -/
theorem signPrefix_peer_state (c : Xmss) (p : Params) (msg sk pk : Bytes)
    (tree leaf k : Nat) :
    let sig := c.sign msg sk leaf pk (layer 0 tree)
    let root := c.recover leaf sig msg pk (layer 0 tree)
    let st := (List.range' 1 k).foldl (peerSignStep c p sk pk) (sig,root,tree)
    (st.1,st.2.1,st.2.2 >>> p.hp,st.2.2 % 2^p.hp) =
      signPrefix c p msg sk pk tree leaf (k+1) := by
  dsimp only
  change alignSign p _ = _
  rw [alignSign_fold,signPrefix,List.range_eq_range',List.range'_succ,List.foldl_cons]
  rfl

theorem signPrefix_complete (c : Xmss) (p : Params) (positive : 0 < p.d)
    (msg sk pk : Bytes) (tree leaf : Nat) :
    ht c p msg sk pk tree leaf = (signPrefix c p msg sk pk tree leaf p.d).1 := by
  have split : List.range p.d = 0 :: List.range' 1 (p.d-1) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    rw [hk,List.range_eq_range']; rfl
  unfold ht signPrefix
  rw [split,later_is_fold]
  rfl

theorem ht_fips (p : Params) (positive : p.d > 0) (msg sk pk : Bytes) (tree leaf : Nat) :
    ht (xmssSpec p) p msg sk pk tree leaf = htSign p msg sk pk tree leaf := by
  exact signPrefix_complete (xmssSpec p) p positive msg sk pk tree leaf

end slhdsa.PeerCall
