-- Generated from the checksummed slh-dsa crate by scripts/extract-peer-sha2-suite.py.
import RcSlhSha2.Streams

namespace slhdsa.RcSlhSha2
open Spec

def compressed (addr : Bytes) : Bytes :=
  [addr[3]!] ++ (addr.drop 8).take 8 ++ [addr[19]!] ++ (addr.drop 20).take 12

def l1_cached_hasher (n : Nat) (seed : Bytes) : Bytes :=
  seed ++ List.replicate (64 - n) 0#8

def l1_prf_sk (n : Nat) (seed addr : Bytes) (secret : Bytes) : Bytes :=
  (digest256 (l1_cached_hasher n seed ++ compressed addr ++ secret)).take n

def l1_f (n : Nat) (seed addr : Bytes) (m : Bytes) : Bytes :=
  (digest256 (l1_cached_hasher n seed ++ compressed addr ++ m)).take n

def l1_h (n : Nat) (seed addr : Bytes) (m1 m2 : Bytes) : Bytes :=
  (digest256 (l1_cached_hasher n seed ++ compressed addr ++ m1 ++ m2)).take n

def l1_t (n : Nat) (seed addr : Bytes) (rows : List Bytes) : Bytes :=
  (digest256 (absorb (l1_cached_hasher n seed ++ compressed addr) rows)).take n

def l1_hmsg (len : Nat) (r seed root : Bytes) (msg : List (List Bytes)) : Bytes :=
  let inner := digest256 (absorb (r ++ seed ++ root) msg.flatten)
  mgf digest256 32 (r ++ seed ++ inner) len

def l1_prfmsg (n : Nat) (key rand : Bytes) (msg : List (List Bytes)) : Bytes :=
  (mac digest256 64 key (absorb rand msg.flatten)).take n

def l35_cached_hasher_256 (n : Nat) (seed : Bytes) : Bytes :=
  seed ++ List.replicate (64 - n) 0#8

def l35_cached_hasher_512 (n : Nat) (seed : Bytes) : Bytes :=
  seed ++ List.replicate (128 - n) 0#8

def l35_prf_sk (n : Nat) (seed addr : Bytes) (secret : Bytes) : Bytes :=
  (digest256 (l35_cached_hasher_256 n seed ++ compressed addr ++ secret)).take n

def l35_f (n : Nat) (seed addr : Bytes) (m : Bytes) : Bytes :=
  (digest256 (l35_cached_hasher_256 n seed ++ compressed addr ++ m)).take n

def l35_h (n : Nat) (seed addr : Bytes) (m1 m2 : Bytes) : Bytes :=
  (digest512 (l35_cached_hasher_512 n seed ++ compressed addr ++ m1 ++ m2)).take n

def l35_t (n : Nat) (seed addr : Bytes) (rows : List Bytes) : Bytes :=
  (digest512 (absorb (l35_cached_hasher_512 n seed ++ compressed addr) rows)).take n

def l35_hmsg (len : Nat) (r seed root : Bytes) (msg : List (List Bytes)) : Bytes :=
  let inner := digest512 (absorb (r ++ seed ++ root) msg.flatten)
  mgf digest512 64 (r ++ seed ++ inner) len

def l35_prfmsg (n : Nat) (key rand : Bytes) (msg : List (List Bytes)) : Bytes :=
  (mac digest512 128 key (absorb rand msg.flatten)).take n

def suite128s : Bool × Nat × Nat := (true, 16, 30)
def suite128f : Bool × Nat × Nat := (true, 16, 34)
def suite192s : Bool × Nat × Nat := (false, 24, 39)
def suite192f : Bool × Nat × Nat := (false, 24, 42)
def suite256s : Bool × Nat × Nat := (false, 32, 47)
def suite256f : Bool × Nat × Nat := (false, 32, 49)

end slhdsa.RcSlhSha2
