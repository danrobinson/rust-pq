import Wots.RecoveryValue
import Wots.Address
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

/-- Changing the chain index (at most 66) replaces exactly native word 4 of
the seed-padded template. The keypair may use all 32 bits. -/
theorem change_chain_word (a : Spec.Adrs) (m : Spec.Bytes) (old new k : Nat)
    (key : a.keypair < 2^32) (small : m.length ≤ 33) (ho : old < 67) (hn : new < 67) :
    word (template {a with word2 := new} m) (4*k) =
      if k=4 then BitVec.ofNat 32 new <<< 16 else word (template {a with word2 := old} m) (4*k) := by
  let kv := BitVec.ofNat 32 a.keypair
  have repr (i : Nat) (hi : i < 67) :
      template {a with word2 := i} m = keyPacket (a.compress.take 10) kv
        ((BitVec.ofNat 16 i).setWidth 32) (m ++ padTail m.length) := by
    rw [← key_packet a kv _ m small]
    unfold template keyAddress
    simp [kv,BitVec.toNat_ofNat,BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (by omega : a.keypair < 4294967296),Nat.mod_eq_of_lt (by omega : i < 65536),
      Nat.mod_eq_of_lt (by omega : i < 4294967296)]
  rw [repr old ho,repr new hn]
  have hh : (a.compress.take 10).length = 10 := by simp [adrs_compress_length]
  rw [← key_words_layout _ _ kv (BitVec.ofNat 16 new) k hh,← key_words_layout _ _ kv (BitVec.ofNat 16 old) k hh]
  have narrow : (BitVec.ofNat 16 new).setWidth 32 = BitVec.ofNat 32 new := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat,BitVec.toNat_setWidth]; omega
  unfold keyWords
  split_ifs <;> simp_all

/-- Besides the current chain index, a lane's previous digest and step counter
can be arbitrary: packing the next hash overwrites their fields. -/
def addressReady (w : Words) (j : Fin 16) (n : Nat) (a : Spec.Adrs) (i : Nat) :=
  ∀ g t k, k < 16 → packedWord (chainWords w j) g n t k =
    packedWord (fun l => word (template {a with word2 := i} (List.replicate n 0)) (4*l)) g n t k

theorem address_initial (base : Words) (n : Nat) (a : Spec.Adrs)
    (shape : n=16 ∨ n=24 ∨ n=32)
    (words : ∀ j k, k < 16 → base.val[k]! j = word (template {a with word2 := 0} (List.replicate n 0)) (4*k)) :
    ∀ j, addressReady base j n a 0 := by
  intro j g t k hk
  exact packed_congr _ _ _ _ _ _ _ (words j k hk) (fun _ _ => rfl) shape

theorem address_after_hash (w stored : Words) (h : Hash) (counter : Reg) (j : Fin 16) (n : Nat)
    (a : Spec.Adrs) (i : Nat) (shape : n=16 ∨ n=24 ∨ n=32) (ready : addressReady w j n a i)
    (words : ∀ k < 16, stored.val[k]! j = packedWord (chainWords w j) (fun l => h.val[l]! j) n (counter j) k) :
    addressReady stored j n a i := by
  intro g t k hk
  rw [packed_congr _ _ g g n k t (words k hk) (fun _ _ => rfl) shape,packed_overwrite]
  exact ready g t k hk

theorem address_after_refill (w patched : Words) (j : Fin 16) (n : Nat) (a : Spec.Adrs) (old new : Nat)
    (shape : n=16 ∨ n=24 ∨ n=32) (key : a.keypair < 2^32) (ho : old < 67) (hn : new < 67)
    (ready : addressReady w j n a old)
    (patch : ∀ k < 16, patched.val[k]! j = if k=4 then BitVec.ofNat 32 new <<< 16 else w.val[k]! j) :
    addressReady patched j n a new := by
  intro g t k hk
  have templateWord := change_chain_word a (List.replicate n 0) old new k key (by simp; omega) ho hn
  by_cases atIndex : k=4
  · subst k
    simp only [packedWord,Chain.valueWord,show (4:Nat) ≠ 5 by decide,
      show (4:Nat) ≠ 5+n/4 by omega,show ¬6 ≤ (4:Nat) by decide,false_and,ite_false,chainWords,
      patch 4 (by decide),ite_true,templateWord]
  · rw [if_neg atIndex] at templateWord
    have eq := patch k hk
    rw [if_neg atIndex] at eq
    exact (packed_congr _ _ g g n k t eq (fun _ _ => rfl) shape).trans ((ready g t k hk).trans
      (packed_congr _ _ g g n k t templateWord.symm (fun _ _ => rfl) shape))

end slhdsa.X86.Wots
