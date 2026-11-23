import Chainavx2.Store
open Aeneas Aeneas.Std Result
open ChainAvx2Rust.sha256.x86.avx2
namespace slhdsa.Avx2.Chain

def digestBytes (digest : DigestWords) (lane : Nat) : Nat → Spec.Bytes
  | 0 => []
  | k+1 => digestBytes digest lane k ++ Spec.toByte digest.val[k]!.val[lane]!.val 4

theorem digestBytes_length (d : DigestWords) (lane k : Nat) : (digestBytes d lane k).length = 4*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [digestBytes,List.length_append,ih,Spec.toByte,List.length_map,List.length_range]; omega

theorem prefix_layout (b : Spec.Bytes) (n : Nat) (d : DigestWords) (lane k : Nat)
    (hb : b.length = 64) (budget : k ≤ (n+3)/4) :
    writePrefix b n d lane k = b.take 22 ++ (digestBytes d lane k).take n ++ b.drop (22+min n (4*k)) := by
  induction k with
  | zero => simp [writePrefix,digestBytes]
  | succ k ih =>
    have active : 4*k < n := by omega
    have before := ih (by omega)
    rw [Nat.min_eq_right (by omega : 4*k ≤ n),List.take_of_length_le (l := digestBytes d lane k) (i := n) (by rw [digestBytes_length]; omega)] at before
    let header := b.take 22 ++ digestBytes d lane k
    have hlen : header.length = 22+4*k := by simp [header,hb,digestBytes_length]
    have file : writePrefix b n d lane k = header ++ b.drop header.length := by rw [hlen]; exact before
    have saved : (writePrefix b n d lane k).take (22+4*k) = header := by
      rw [file,← hlen,List.take_append_length]
    let count := min 4 (n-4*k)
    have tail : (writePrefix b n d lane k).drop (22+4*k+count) = b.drop (22+4*k+count) := by
      rw [file,List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,List.drop_drop,hlen]
      congr 1; omega
    rw [writePrefix,storeWord,saved,tail,digestBytes,List.take_append,digestBytes_length,
      List.take_of_length_le (l := digestBytes d lane k) (i := n) (by rw [digestBytes_length]; omega)]
    have minlen : min n (4*(k+1)) = 4*k+count := by dsimp [count]; omega
    rw [minlen,← Nat.add_assoc]
    have trim : (Spec.toByte d.val[k]!.val[lane]!.val 4).take count =
        (Spec.toByte d.val[k]!.val[lane]!.val 4).take (n-4*k) := by
      simp only [count, List.take_eq_take_iff]
      simp [Spec.toByte,Nat.min_comm]
    change (header ++ (Spec.toByte _ 4).take count) ++ _ = _
    rw [trim]
    simp only [header,List.append_assoc]

theorem digest_take (d : DigestWords) (lane n k m : Nat) (km : k ≤ m) (enough : n ≤ 4*k) :
    (digestBytes d lane m).take n = (digestBytes d lane k).take n := by
  induction m with
  | zero => rw [show k = 0 by omega]
  | succ m ih =>
    by_cases same : k = m+1
    · subst k; rfl
    · rw [digestBytes,List.take_append_of_le_length (by rw [digestBytes_length]; omega),ih (by omega)]

/-- Active lanes receive exactly N digest bytes. Idle lanes retain the complete prior block. -/
theorem store_bytes_spec (N : Usize) (batch : Batch) (lengths : Array U32 8#usize)
    (step : U32) (digest : DigestWords) (hn : N.val ≤ 32) :
    chains_loop0_loop1_loop1 N ⟨0#usize,8#usize⟩ batch lengths step digest ⦃ r =>
      ∀ j < 8, bytes r.val[j]!.val =
        if step.val < lengths.val[j]!.val then (bytes batch.val[j]!.val).take 22 ++
          (digestBytes digest j 8).take N.val ++ (bytes batch.val[j]!.val).drop (22+N.val)
        else bytes batch.val[j]!.val ⦄ := by
  apply WP.spec_mono (stores_spec N batch lengths step digest hn)
  intro r h j hj
  rw [h j hj]
  split
  · rw [prefix_layout _ _ _ _ _ (by simp [bytes]) (by omega),
      digest_take digest j N.val ((N.val+3)/4) 8 (by omega) (by omega),Nat.min_eq_left (by omega)]
  · rfl
end slhdsa.Avx2.Chain
