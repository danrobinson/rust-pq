import PeerEquality.Layers

namespace slhdsa.PeerCall.PeerXmss
open Spec

structure Children where
  wotsKey : Bytes → Bytes → Adrs → Bytes
  wotsSign : Bytes → Bytes → Bytes → Adrs → Bytes
  wotsRecover : Bytes → Bytes → Bytes → Adrs → Bytes
  hash : Bytes → Adrs → Bytes → Bytes → Bytes

def children (p : Params) : Children :=
  ⟨wotsPkGen p,wotsSign p,wotsPkFromSig p,fun pk addr l r => H p pk addr (l ++ r)⟩

private def keyAt (a : Adrs) (i : Nat) : Adrs := { a.setTypeAndClear WOTS_HASH with keypair := i }

def node (c : Children) (sk : Bytes) (i h : Nat) (pk : Bytes) (a : Adrs) : Bytes :=
  match h with
  | 0 => c.wotsKey sk pk (keyAt a i)
  | k+1 =>
    let l := node c sk (2*i) k pk a
    let r := node c sk (2*i+1) k pk a
    c.hash pk { a.setTypeAndClear TREE with word2 := k+1, word3 := i } l r

theorem node_fips (p : Params) (sk : Bytes) (i h : Nat) (pk : Bytes) (a : Adrs) :
    node (children p) sk i h pk a = xmssNode p sk i h pk a := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => rw [node,xmssNode,ih,ih]; rfl

private theorem node_keyAt (p : Params) (sk : Bytes) (i h : Nat) (pk : Bytes) (a : Adrs) (leaf : Nat) :
    xmssNode p sk i h pk (keyAt a leaf) = xmssNode p sk i h pk a := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [xmssNode,ih]; rfl

private def authRows (c : Children) (sk pk : Bytes) (a : Adrs) (idx : Nat) : List Nat → Bytes
  | [] => []
  | j::js => node c sk (idx ^^^ 1) j pk a ++ authRows c sk pk a (idx >>> 1) js

def sign (c : Children) (p : Params) (msg sk : Bytes) (idx : Nat) (pk : Bytes) (a : Adrs) :=
  let adrs := keyAt a idx
  c.wotsSign msg sk pk adrs ++ authRows c sk pk adrs idx (List.range p.hp)

private theorem rows (p : Params) (sk pk : Bytes) (a : Adrs) (idx leaf start count : Nat) :
    authRows (children p) sk pk (keyAt a leaf) (idx / 2^start) (List.range' start count) =
      (List.range' start count).flatMap (fun j => xmssNode p sk ((idx / 2^j) ^^^ 1) j pk a) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [List.range'_succ,authRows,List.flatMap_cons,node_fips,node_keyAt]
    congr 1
    have shifted : (idx / 2^start) >>> 1 = idx / 2^(start+1) := by
      simp [Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul,Nat.pow_succ]
    rw [shifted]
    exact ih _

theorem sign_fips (p : Params) (msg sk : Bytes) (idx : Nat) (pk : Bytes) (a : Adrs) :
    sign (children p) p msg sk idx pk a = xmssSign p msg sk idx pk a := by
  unfold sign xmssSign
  rw [List.range_eq_range']
  simpa [children,keyAt] using congrArg
    (fun auth => wotsSign p msg sk pk (keyAt a idx) ++ auth) (rows p sk pk a idx idx 0 p.hp)

private def up (c : Children) (p : Params) (auth pk : Bytes) (a : Adrs)
    (st : Bytes × Nat) (j : Nat) : Bytes × Nat :=
  let parent := st.2 >>> 1
  let addr := { a.setTypeAndClear TREE with word2 := j+1, word3 := parent }
  let sibling := block p auth j
  let root := if st.2 &&& 1 == 0 then c.hash pk addr st.1 sibling else c.hash pk addr sibling st.1
  (root,parent)

def recover (c : Children) (p : Params) (idx : Nat) (sig msg pk : Bytes) (a : Adrs) :=
  let first := c.wotsRecover (sig.take (p.len*p.n)) msg pk (keyAt a idx)
  let auth := (sig.drop (p.len*p.n)).take (p.hp*p.n)
  ((List.range p.hp).foldl (up c p auth pk a) (first,idx)).1

private def fipsUp (p : Params) (idx : Nat) (auth pk : Bytes) (a : Adrs)
    (st : Bytes × Nat) (j : Nat) : Bytes × Nat :=
  let sibling := block p auth j
  if (idx / 2^j) % 2 = 0 then
    let parent := st.2 / 2
    (H p pk { a.setTypeAndClear TREE with word2 := j+1, word3 := parent } (st.1 ++ sibling),parent)
  else
    let parent := (st.2-1) / 2
    (H p pk { a.setTypeAndClear TREE with word2 := j+1, word3 := parent } (sibling ++ st.1),parent)

private theorem oddParent (i : Nat) (odd : i % 2 ≠ 0) : (i-1)/2 = i/2 := by omega

private theorem climb_eq (p : Params) (root : Bytes) (idx : Nat) (auth pk : Bytes) (a : Adrs) (n : Nat) :
    let peer := (List.range n).foldl (up (children p) p auth pk a) (root,idx)
    peer = (List.range n).foldl (fipsUp p idx auth pk a) (root,idx) ∧ peer.2 = idx / 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    obtain ⟨eq,index⟩ := ih
    rw [← eq]
    generalize (List.range n).foldl (up (children p) p auth pk a) (root,idx) = st at index ⊢
    obtain ⟨r,t⟩ := st
    change t = idx / 2^n at index
    subst t
    simp only [up,fipsUp,children,Nat.shiftRight_eq_div_pow,Nat.pow_one]
    have mask (t : Nat) : t &&& 1 = t % 2 := Nat.and_two_pow_sub_one_eq_mod t 1
    rw [mask]
    have div : idx / 2^(n+1) = idx / 2^n / 2 := by rw [Nat.pow_succ,Nat.div_div_eq_div_mul]
    by_cases even : idx / 2^n % 2 = 0
    · simp [even,div]
    · simp [even,oddParent _ even,div]

theorem recover_fips (p : Params) (idx : Nat) (sig msg pk : Bytes) (a : Adrs) :
    recover (children p) p idx sig msg pk a = xmssPkFromSig p idx sig msg pk a := by
  let first := wotsPkFromSig p (sig.take (p.len*p.n)) msg pk (keyAt a idx)
  let auth := (sig.drop (p.len*p.n)).take (p.hp*p.n)
  exact congrArg Prod.fst (climb_eq p first idx auth pk a p.hp).1

def operations (c : Children) (p : Params) : Xmss := ⟨sign c p,recover c p,node c⟩

theorem operations_fips (p : Params) : operations (children p) p = xmssSpec p := by
  unfold operations xmssSpec
  congr 1
  · funext msg sk idx pk a; exact sign_fips p msg sk idx pk a
  · funext idx sig msg pk a; exact recover_fips p idx sig msg pk a
  · funext sk i h pk a; exact node_fips p sk i h pk a

end slhdsa.PeerCall.PeerXmss
