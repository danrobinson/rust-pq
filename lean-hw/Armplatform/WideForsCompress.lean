import Armplatform.WideForsHashes

namespace slhdsa.WideFors
open Armwide Spec.SHA256
set_option maxHeartbeats 1400000

/-- Four consecutive 128-bit loads from each physical SHA-256 block. -/
def group (msg : Spec.Bytes) (k : Nat) : Spec.Bytes :=
  [64*k,64*k+16,64*k+32,64*k+48].flatMap (fun i => (msg.drop i).take 16)

theorem group_eq (msg : Spec.Bytes) (k : Nat) : group msg k = blockAt msg k := by
  unfold group blockAt
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [show 64=16+(16+(16+16)) by decide,List.take_add,List.take_add (i:=16) (j:=16+16),List.take_add (i:=16) (j:=16)]
  simp only [List.drop_drop,Nat.add_assoc]

def compression256 (st : List Word) (msg : Spec.Bytes) :=
  let step (s : List Word) (k : Nat) :=
    let regs := Kernel.compressBlockLane true s (group msg k)
    vwords regs.1 ++ vwords regs.2
  (ser ((List.range (msg.length/64)).foldl step st)).take 16

theorem compression256_spec (st : List Word) (size : st.length=8) (msg : Spec.Bytes) :
    compression256 st msg = (ser (hashFrom st msg)).take 16 := by
  unfold compression256 hashFrom
  let step (s : List Word) (k : Nat) :=
    let regs := Kernel.compressBlockLane true s (group msg k)
    vwords regs.1 ++ vwords regs.2
  have walk (k : Nat) (lim : k≤msg.length/64) :
      ((List.range k).foldl step st).length=8 ∧ (List.range k).foldl step st =
      (List.range k).foldl (fun acc i => compress acc (blockAt msg i)) st := by
    induction k with
    | zero => simpa using size
    | succ k ih =>
      have ⟨len,eq⟩ := ih (by omega)
      have bl : (blockAt msg k).length=64 := by simp only [blockAt,List.length_take,List.length_drop]; omega
      simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      have ch := Kernel.compressBlockLane_true_eq_compress _ len _ bl
      dsimp only at ch
      have single : step ((List.range k).foldl step st) k = compress ((List.range k).foldl step st) (blockAt msg k) := by
        unfold step; rw [group_eq]; exact ch
      rw [single,eq]; exact ⟨by simp [compress],rfl⟩
  change (ser ((List.range (msg.length/64)).foldl step st)).take 16 = _
  rw [(walk _ (by omega : msg.length/64≤msg.length/64)).2]

def final (p : Spec.Params) (pk : Spec.Bytes) (addr : Spec.Adrs) (roots : Spec.Bytes) (fast : Bool) :=
  if p.n=16 then compression256 (seedState 16 pk) (padFrom 64 (addr.compress ++ roots))
  else if fast then
    let full := Spec.SHA512.pad ((pk ++ Spec.toByte 0 (128-p.n)) ++ (addr.compress ++ roots))
    H512.Multi.compressMulti1 p.n (H512.Multi.pkState512 p.n pk) (full.drop 128)
  else
    let st := Spec.SHA512.compress Spec.SHA512.H0 (pk ++ List.replicate (128-p.n) 0#8)
    (S512.ser (S512.hashFrom st (S512.padFrom 128 (addr.compress ++ roots)))).take p.n

theorem final_eq (p : Spec.Params) [f : Fact (p.family=.sha2)] (valid : p.Valid) (pk : Spec.Bytes)
    (hp : pk.length=p.n) (addr : Spec.Adrs) (roots : Spec.Bytes) (fast : Bool) :
    final p pk addr roots fast = Spec.T p pk addr roots := by
  unfold final
  rcases valid.n_cases with pn|pn
  · rw [if_pos pn,T_eq_H,H_eq,if_pos pn,pn,compression256_spec _ (by simp [seedState,compress]),th256_eq _ _ (by omega) (by decide)]
    rfl
  · have neq : p.n≠16 := by rcases pn with eq|eq <;> omega
    rw [if_neg neq]
    cases fast with
    | true => exact H512.Multi.compress_multi_1_eq_fips_T p f.out pn pk roots hp addr
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,T_eq_H,H_eq,if_neg neq,th512_eq _ _ hp (by rcases pn with eq|eq <;> omega)]

end slhdsa.WideFors
