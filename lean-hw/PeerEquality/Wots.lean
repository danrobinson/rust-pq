import PeerEquality.Xmss
import Spec.Correctness

namespace slhdsa.PeerCall.PeerWots
open Spec

structure Hashes where
  prf : Bytes → Bytes → Adrs → Bytes
  f : Bytes → Adrs → Bytes → Bytes
  t : Bytes → Adrs → List Bytes → Bytes
  h : Bytes → Adrs → Bytes → Bytes → Bytes

def hashes (p : Params) : Hashes :=
  ⟨PRF p,F p,fun pk a rows => T p pk a rows.flatten,fun pk a l r => H p pk a (l ++ r)⟩

def iterate (h : Hashes) (x : Bytes) (start count : Nat) (pk : Bytes) (a : Adrs) :=
  (List.range' start count).foldl (fun v j => h.f pk { a with word3 := j } v) x

theorem iterate_eq (p : Params) (x : Bytes) (i s : Nat) (pk : Bytes) (a : Adrs) :
    iterate (hashes p) x i s pk a = chain p x i s pk a := by
  simp [iterate,chain,List.range'_eq_map_range,List.foldl_map,hashes]

private def checksum (ds : List Nat) := (ds.map (fun x => 15-x)).sum

private theorem checksum_fold (ds : List Nat) (acc : Nat) :
    ds.foldl (fun n x => n+(15-x)) acc = acc + checksum ds := by
  induction ds generalizing acc with
  | nil => simp [checksum]
  | cons x xs ih => simp [List.foldl_cons,ih,checksum,Nat.add_assoc]

private theorem checksum_bound (ds : List Nat) : checksum ds ≤ 15*ds.length := by
  induction ds with
  | nil => decide
  | cons x xs ih =>
    simp only [checksum,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ] at *
    omega

/-- Four-bit specialization of the peer's masked accumulator. After the high
nibble, only the low nibble is retained. After the low nibble the buffer is empty. -/
private def nibbles (x : Bytes) : Nat → Nat → Option Nat → List Nat
  | 0, _, _ => []
  | count+1, i, none =>
    let b := x[i]!.toNat
    ((b >>> 4) &&& 15) :: nibbles x count (i+1) (some (b &&& 15))
  | count+1, i, some lo => lo :: nibbles x count i none

private theorem nibbles_go (x : Bytes) (count : Nat) :
    (∀ i t, nibbles x count i none = base2bGo x 4 count i 0 t) ∧
    (∀ i t, nibbles x count i (some (t % 16)) = base2bGo x 4 count i 4 t) := by
  induction count with
  | zero => exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  | succ count ih =>
    have mask (t : Nat) : t &&& 15 = t % 16 := Nat.and_two_pow_sub_one_eq_mod t 4
    constructor
    · intro i t
      have fill : base2bFill x 4 i 0 t =
          (i+1,8,(t <<< 8) + x[i]!.toNat) := by
        rw [base2bFill,if_pos (by decide),base2bFill,if_neg (by decide)]
      simp only [nibbles,base2bGo,fill,mask,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq]
      change (x[i]!.toNat / 16 % 16) :: _ =
        ((t * 256 + x[i]!.toNat) / 16 % 16) :: base2bGo x 4 count (i+1) 4 _
      congr 1
      · omega
      · rw [← ih.2]; congr 2; omega
    · intro i t
      have fill : base2bFill x 4 i 4 t = (i,4,t) := by rw [base2bFill,if_neg (by decide)]
      simp only [nibbles,base2bGo,fill]
      exact congrArg (List.cons (t%16)) (ih.1 i t)

private theorem nibbles_eq (x : Bytes) (count : Nat) :
    nibbles x count 0 none = base2b x 4 count := (nibbles_go x count).1 0 0

/-- Fixed-width sum and shift, followed by the first three nibbles of the
two-byte big-endian result. The length proof below excludes wraparound. -/
def digits (p : Params) (m : Bytes) :=
  let ds := nibbles m (2*p.n) 0 none
  ds ++ nibbles (toByte (((checksum ds % 65536) <<< 4) % 65536) 2) 3 0 none

private theorem lengths (p : Params) (valid : p.Valid) :
    p.len1 = 2*p.n ∧ p.len2 = 3 ∧ p.w = 16 := by
  rcases valid.n_cases with n | n | n <;>
    simp [Params.len1,Params.len2,Params.w,valid.lgw_eq,n] <;> decide

theorem digits_eq (p : Params) (valid : p.Valid) (m : Bytes) : digits p m = wotsDigits p m := by
  obtain ⟨l1,l2,w⟩ := lengths p valid
  let ds := base2b m 4 (2*p.n)
  have h := checksum_bound ds
  have size : ds.length = 2*p.n := base2b_length _ _ _
  have small : checksum ds < 4096 := by rcases valid.n_cases with a|a|a <;> omega
  have shift : checksum ds <<< 4 < 65536 := by rw [Nat.shiftLeft_eq]; omega
  unfold digits wotsDigits
  simp only [nibbles_eq,valid.lgw_eq,l1,l2,w,checksum_fold,Nat.zero_add]
  change ds ++ base2b (toByte (((checksum ds % 65536) <<< 4) % 65536) 2) 4 3 =
    ds ++ base2b (toByte (checksum ds <<< 4) 2) 4 3
  rw [Nat.mod_eq_of_lt (by omega : checksum ds < 65536),Nat.mod_eq_of_lt shift]

private def seed (h : Hashes) (sk pk : Bytes) (a : Adrs) (i : Nat) :=
  h.prf pk sk { wotsSkAdrs a with word2 := i }

def key (h : Hashes) (p : Params) (sk pk : Bytes) (a : Adrs) :=
  h.t pk (wotsPkAdrs a) ((List.range p.len).map fun i =>
    iterate h (seed h sk pk a i) 0 15 pk { a with word2 := i })

def sign (h : Hashes) (p : Params) (msg sk pk : Bytes) (a : Adrs) :=
  let ds := digits p msg
  ((List.range p.len).map fun i =>
    iterate h (seed h sk pk a i) 0 ds[i]! pk { a with word2 := i }).flatten

def recover (h : Hashes) (p : Params) (sig msg pk : Bytes) (a : Adrs) :=
  let ds := digits p msg
  h.t pk (wotsPkAdrs a) ((List.range p.len).map fun i =>
    iterate h (block p sig i) ds[i]! (15-ds[i]!) pk { a with word2 := i })

def operations (h : Hashes) (p : Params) : PeerXmss.Children := ⟨key h p,sign h p,recover h p,h.h⟩

theorem operations_fips (p : Params) (valid : p.Valid) :
    operations (hashes p) p = PeerXmss.children p := by
  obtain ⟨_,_,w⟩ := lengths p valid
  have hk : key (hashes p) p = wotsPkGen p := by
    funext sk pk a
    simp only [key,wotsPkGen,w,iterate_eq,seed]
    rfl
  have hs : sign (hashes p) p = wotsSign p := by
    funext msg sk pk a
    simp only [sign,wotsSign,digits_eq p valid,iterate_eq,seed]
    rfl
  have hr : recover (hashes p) p = wotsPkFromSig p := by
    funext sig msg pk a
    simp only [recover,wotsPkFromSig,w,digits_eq p valid,iterate_eq]
    rfl

  unfold operations PeerXmss.children
  rw [hk,hs,hr]
  rfl

end slhdsa.PeerCall.PeerWots
