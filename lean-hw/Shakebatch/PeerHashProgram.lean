import Spec.SlhDsa
open Spec (Bytes)
namespace PeerShake

/-- SHAKE256 streaming operations cut at the RustCrypto digest provider. -/
structure Xof (S : Type) where
  empty : S
  update : S → Bytes → S
  finish : S → Nat → Bytes

variable {S : Type} (x : Xof S)

def new_from_pk_seed (pk_seed : Bytes) : S :=
  (x.update x.empty pk_seed)

def prf_sk (n : Nat) (cached : S) (adrs sk_seed : Bytes) : Bytes :=
  x.finish (x.update (x.update cached adrs) sk_seed) n

def f (n : Nat) (cached : S) (adrs m : Bytes) : Bytes :=
  x.finish (x.update (x.update cached adrs) m) n

def h (n : Nat) (cached : S) (adrs m1 m2 : Bytes) : Bytes :=
  x.finish (x.update (x.update (x.update cached adrs) m1) m2) n

def t (n : Nat) (cached : S) (adrs : Bytes) (m : List Bytes) : Bytes :=
  x.finish (m.foldl (fun st piece => (x.update st piece)) (x.update cached adrs)) n

def prf_msg (n : Nat) (sk_prf opt_rand : Bytes) (msg : List (List Bytes)) : Bytes :=
  x.finish (msg.flatten.foldl (fun st piece => (x.update st piece)) (x.update (x.update x.empty sk_prf) opt_rand)) n

def h_msg (mbytes : Nat) (rand pk_seed pk_root : Bytes) (msg : List (List Bytes)) : Bytes :=
  x.finish (msg.flatten.foldl (fun st piece => (x.update st piece)) (x.update (x.update (x.update x.empty rand) pk_seed) pk_root)) mbytes

end PeerShake
