import Armwide.KeyPadding
import Armwide.MultiProgram
import Paired.Multi

namespace slhdsa.Armwide.Keygen
open Spec.SHA256
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

private def gather (msg : Spec.Bytes) (offsets : List Nat) := offsets.flatMap (fun i => (msg.drop i).take 16)
private def chunk (i : Nat) := [64*i,64*i+16,64*i+32,64*i+48]

private theorem gathered (msg : Spec.Bytes) (i : Nat) : gather msg (chunk i) = blockAt msg i := by
  unfold gather chunk blockAt
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [show 64=16+(16+(16+16)) by decide,List.take_add,List.take_add (i:=16) (j:=16+16),List.take_add (i:=16) (j:=16)]
  simp only [List.drop_drop,Nat.add_assoc]

private def step (msg : Spec.Bytes) (st : List Word) (offsets : List Nat) :=
  let (lo,hi) := Kernel.compressBlockLane true st (gather msg offsets)
  vwords lo ++ vwords hi

private def multi256 (st : List Word) (msg : Spec.Bytes) : Spec.Bytes :=
  (ser (blocks.foldl (step msg) st)).take 16

private theorem state256 (st : List Word) (len : st.length=8) (msg : Spec.Bytes) (geom : msg.length=640) :
    multi256 st msg = (ser (hashFrom st msg)).take 16 := by
  have sequence : blocks=(List.range 10).map chunk := by decide
  have calcBlocks (k : Nat) (bound : k≤10) :
      (((List.range k).map chunk).foldl (step msg) st).length=8 ∧
      ((List.range k).map chunk).foldl (step msg) st =
        (List.range k).foldl (fun acc j => compress acc (blockAt msg j)) st := by
    induction k with
    | zero => exact ⟨len,rfl⟩
    | succ k ih =>
      obtain ⟨l,e⟩ := ih (by omega)
      rw [List.range_succ,List.map_append,List.foldl_append,List.foldl_append]
      simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,step,gathered]
      have bl : (blockAt msg k).length=64 := by
        simp only [blockAt,List.length_take,List.length_drop,geom]; omega
      have one := Kernel.compressBlockLane_true_eq_compress _ l _ bl
      dsimp only at one ⊢
      rw [one,e]
      exact ⟨by simp [compress],rfl⟩
  simp only [multi256,sequence,(calcBlocks 10 (by decide)).2,hashFrom,geom,Nat.reduceDiv]

private def scalar512 (n : Nat) (st : List Spec.SHA512.Word) (msg : Spec.Bytes) :=
  ((H512.Multi.iterCompress st msg).flatMap (fun w => Spec.toByte w.toNat 8)).take n

def compression (n : Nat) (hard : Bool) (st : List Word) (wide : List Spec.SHA512.Word) (msg : Spec.Bytes) :=
  let route := (calls[hard.toNat]!)[group n]!
  if route=[(256,msg.length)] then multi256 st msg
  else if route=[(512,msg.length)] then H512.Multi.compressMulti1 n wide msg
  else if route=List.replicate (msg.length/128) (1,128) then scalar512 n wide msg else []

private theorem shape256 (hard : Bool) : (calls[hard.toNat]!)[group 16]! = [(256,640)] := by cases hard <;> decide

private theorem shape512 (n : Nat) (width : n=24 ∨ n=32) (hard : Bool) :
    (calls[hard.toNat]!)[group n]! = if hard then [(512,total n)] else List.replicate (total n/128) (1,128) := by
  rcases width with rfl|rfl <;> cases hard <;> decide

private theorem route512 (n : Nat) (width : n=24 ∨ n=32) (hard : Bool) (st : List Word)
    (wide : List Spec.SHA512.Word) (size : wide.length=8) (msg : Spec.Bytes) (geom : msg.length=total n) :
    compression n hard st wide msg = scalar512 n wide msg := by
  unfold compression
  rw [shape512 n width hard,geom]
  rcases width with rfl|rfl <;> cases hard <;>
    simp (config := {decide:=true}) only [total,↓reduceIte,Bool.false_eq_true]
  all_goals apply H512.Multi.compress_multi_1_eq_iter _ (by decide) _ size

theorem compression_T (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (pk payload : Spec.Bytes) (plen : pk.length=p.n) (len : payload.length=payLen p.n) (a : Spec.Adrs) (hard : Bool) (wide : List Spec.SHA512.Word)
    (wide_ok : p.n≠16 → wide=H512.Multi.pkState512 p.n pk) :
    compression p.n hard (seedState p.n pk) wide (padded p.n a (filled p.n payload)) =
      Spec.T p pk (Spec.wotsPkAdrs a) payload := by
  rw [padded_eq p.n valid.n_cases a payload len,T_eq_H,H_eq]
  by_cases small : p.n=16
  · simp only [small,ite_true]
    rw [compression,shape256]
    have msg : (padFrom 64 ((Spec.wotsPkAdrs a).compress ++ payload)).length=640 := by
      rw [small] at len
      simp [padFrom,List.length_append,show (Spec.wotsPkAdrs a).compress.length=22 from rfl,len,payLen,Spec.toByte]
    rw [msg,ite_eq_left rfl,state256 _ (by simp [seedState,compress]) _ msg,th256_eq _ _ (by rwa [small] at plen) (by decide)]
    rfl
  · rw [wide_ok small]
    simp only [small,↓reduceIte]
    have width : p.n=24 ∨ p.n=32 := by have := valid.n_cases; omega
    have state : (H512.Multi.pkState512 p.n pk).length=8 := by simp [H512.Multi.pkState512,Spec.SHA512.compress]
    have geom : (S512.padFrom 128 ((Spec.wotsPkAdrs a).compress ++ payload)).length=total p.n := by
      simp only [S512.padFrom,List.length_append,List.length_replicate,List.length_cons,List.length_nil,
        show (Spec.wotsPkAdrs a).compress.length=22 from rfl,len,Spec.toByte,List.length_map,List.length_range]
      rcases width with h|h <;> rw [h] <;> decide
    rw [route512 _ width hard _ _ state _ geom,th512_eq _ _ plen (by omega)]
    simp only [scalar512,H512.Multi.iterCompress,H512.Multi.pkState512,toByte_zero,S512.hashFrom,S512.ser]

end slhdsa.Armwide.Keygen
