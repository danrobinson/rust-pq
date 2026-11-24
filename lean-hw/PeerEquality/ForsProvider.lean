import PeerEquality.Wots
import Shakebatch.PeerForsTrace

namespace slhdsa.PeerCall.ConcreteFors
open Spec
open PeerWots (Hashes)

/-- The checked RustCrypto PRF address conversion, including its cleared height. -/
def secret (rows : Hashes) (sk pk : Bytes) (a : Adrs) (i : Nat) : Bytes :=
  rows.prf pk sk {a.setTypeAndClear FORS_PRF with keypair := a.keypair, word3 := i}

/-- The recursive FORS call graph uses one PRF/F for leaves or two recursive
    nodes and the suite's binary H for internal nodes. -/
def node (rows : Hashes) (sk pk : Bytes) (a : Adrs) (i : Nat) : Nat → Bytes
  | 0 => rows.f pk {a with word2 := 0, word3 := i} (secret rows sk pk a i)
  | z+1 => rows.h pk {a with word2 := z+1, word3 := i}
      (node rows sk pk a (2*i) z) (node rows sk pk a (2*i+1) z)

theorem node_eq (p : Params) (sk pk : Bytes) (a : Adrs) (i z : Nat) :
    node (PeerWots.hashes p) sk pk a i z = forsNode p sk i z pk a := by
  induction z generalizing i with
  | zero => rfl
  | succ z ih => simp only [node, forsNode, ih]; rfl

def sign (rows : Hashes) (p : Params) (md sk pk : Bytes) (a : Adrs) : Bytes :=
  (List.range p.k).flatMap fun t =>
    let i := t*2^p.a + (base2b md p.a p.k)[t]!
    secret rows sk pk a i ++ (List.range p.a).flatMap fun j =>
      node rows sk pk a ((i/2^j) ^^^ 1) j

def path (rows : Hashes) (p : Params) (sig pk : Bytes) (a : Adrs) (t leaf : Nat) : Nat → Bytes × Nat
  | 0 => (rows.f pk {a with word2 := 0, word3 := leaf} (block p sig (t*(p.a+1))),leaf)
  | j+1 =>
    let (child,i) := path rows p sig pk a t leaf j
    let sibling := block p sig (t*(p.a+1)+1+j)
    let parent := {a with word2 := j+1, word3 := i/2}
    (if i%2 = 0 then rows.h pk parent child sibling else rows.h pk parent sibling child,i/2)

theorem path_eq (p : Params) (sig pk : Bytes) (a : Adrs) (t leaf j : Nat) :
    path (PeerWots.hashes p) p sig pk a t leaf j = slhdsa.PeerFors.path p sig pk a t leaf j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [path, slhdsa.PeerFors.path, ih, pairMsg]
    split <;> simp_all [PeerWots.hashes]

def recover (rows : Hashes) (p : Params) (sig md pk : Bytes) (a : Adrs) : Bytes :=
  rows.t pk {a.setTypeAndClear FORS_ROOTS with keypair := a.keypair}
    ((List.range p.k).map fun t =>
      (path rows p sig pk a t (t*2^p.a + (base2b md p.a p.k)[t]!) p.a).1)

/-- Instantiating the checked call schedules removes the separate FORS
    assumptions from upper-level comparisons that already identify the provider. -/
theorem operations (p : Params) (rows : Hashes) (provider : rows = PeerWots.hashes p) :
    sign rows p = forsSign p ∧ recover rows p = forsPkFromSig p := by
  subst rows
  constructor
  · funext md sk pk a
    rw [← slhdsa.PeerFors.sign_eq]
    simp only [sign,slhdsa.PeerFors.sign,node_eq]; rfl
  · funext sig md pk a
    rw [← slhdsa.PeerFors.recover_eq]
    simp only [recover,slhdsa.PeerFors.recover,path_eq]; rfl

end slhdsa.PeerCall.ConcreteFors

#print axioms slhdsa.PeerCall.ConcreteFors.node_eq
#print axioms slhdsa.PeerCall.ConcreteFors.operations
