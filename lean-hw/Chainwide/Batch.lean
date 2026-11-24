import Chainwide.Loop
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Chain
open Spec.SHA256
open ChainWideRust.sha256.x86.avx512

private def laneModel (n : Nat) (iv : Hash) (b : Rows) (start : Reg) (j : Fin 16) :=
  laneOf n (stateWords (laneState iv j)) (bytes b.val[j.val]!.val) (start j).toNat

private theorem digest_of (h : Hash) (j : Fin 16) (ws : List Word) (n : Nat)
    (hn : n=16 ∨ n=24 ∨ n=32) (length : ws.length = 8)
    (words : ∀ k < n/4, h.val[k]! j = ws[k]!) :
    digestPart h j 0 n = (ser ws).take n := by
  apply List.ext_getElem
  · simp [digestPart,ser_length,length]; omega
  · intro k hk hk'
    have bound : k < n := by simpa [digestPart] using hk
    have safe : k < (ser ws).length := by rw [ser_length,length]; omega
    simp only [digestPart,List.getElem_map,List.getElem_range,Nat.zero_add,Store.digestByte,List.getElem_take]
    rw [← getElem!_pos (ser ws) k safe,Digest.ser_byte _ _ (by omega),words _ (by omega)]

def BatchResult (N : Usize) (iv : Hash) (b out : Rows) (start stop : Reg) :=
  out.length = b.length ∧ ∀ (j : Fin 16), j.val < b.length →
    bytes out.val[j.val]!.val = runBlock N.val (stateWords (laneState iv j)) (bytes b.val[j.val]!.val)
      (start j).toNat (stop j).toNat

theorem batch_loop_spec (N : Usize) (ends : Slice U32) (iv : Hash) (off : Usize) (b : Rows)
    (start stop fixed : Reg) (orig : U16) (saved pre : Hash) (base : Words)
    (hn : N.val=16 ∨ N.val=24 ∨ N.val=32) (he : off.val+b.length ≤ ends.length)
    (hb : Covers orig b.length) (work : orig ≠ 0#u16) (sched : Schedule start stop start orig 0)
    (endsOk : ∀ j : Fin 16, j.val < b.length → stop j = ends.val[off.val+j.val]!.bv)
    (input : ∀ k < 16, ∀ j, base.val[k]! j = inputWord orig b k j)
    (hfixed : ∀ j, fixed j = (base.val[4]! j &&& 0xffff0000))
    (trace : Trace pre (fun j => schedule (Leaf.blockOf (lanes base j))) (laneState iv) 4) :
    chains_loop0_loop1 N ends iv off b start stop orig orig saved base fixed (fun _ => 0xffff) pre
      ⦃ out => BatchResult N iv b out start stop ⦄ := by
  let p := laneModel N.val iv b start
  have pos k (set : orig.bv.getLsbD k = true) : 0 < ends.val[off.val+k]!.val := by
    have small : k < 16 := by by_contra! large; rw [BitVec.getLsbD_of_ge _ k large] at set; contradiction
    let j : Fin 16 := ⟨k,small⟩
    have e := sched.1 j
    rw [show orig.bv.getLsbD j.val = true from set] at e
    have h := of_decide_eq_true e.symm
    unfold Live at h
    rw [endsOk j (hb k set)] at h
    exact Nat.zero_lt_of_lt h
  apply WP.spec_mono (chain_loop_spec N ends iv off b start stop fixed orig saved pre base p hn he hb pos work
    sched (fun _ => rfl) (fun _ => rfl) ?_ ?_ trace)
  · rintro out ⟨finalHash,⟨lo,rows⟩,hh⟩
    refine ⟨lo,?_⟩
    intro j hj
    let row := bytes b.val[j.val]!.val
    have len : row.length = 64 := by simp [row,bytes]
    rw [rows j.val hj]
    split <;> rename_i set
    · have eq := sched.1 j
      rw [set] at eq
      have live := of_decide_eq_true eq.symm
      unfold Live at live
      let t := (stop j).toNat-1-(start j).toNat
      have sum : (start j).toNat+t+1 = (stop j).toNat := by dsimp [t]; omega
      have limit : (start j).toNat+t < 2^32 := by have := (stop j).isLt; omega
      have history := portable_history row (stateWords (laneState iv j)) N.val (start j).toNat t len (by omega) limit
      rw [show (start j).toNat+(t+1) = (stop j).toNat by omega] at history
      rw [history,digest_of finalHash j (lastHash (p j) N.val (stop j)) N.val hn (sha_compress_length _ _) (hh j set)]
      have lastEq : ends.val[off.val+j.val]!.val-1 = (start j).toNat+t := by
        have h := congrArg BitVec.toNat (endsOk j hj); change (stop j).toNat = ends.val[off.val+j.val]!.val at h
        omega
      simp only [packet,Lane.value,laneModel,laneOf,Lane.hash,lastHash,p,row,
        show (stop j).toNat-1-(start j).toNat = t from rfl,BitVec.toNat_ofNat,Nat.mod_eq_of_lt limit,lastEq,List.append_assoc]
    · have eq := sched.1 j
      have rev : (stop j).toNat ≤ (start j).toNat := by
        by_contra! h
        exact set ((eq.trans (decide_eq_true (by simpa [Live] using h))))
      rw [runBlock_le _ _ _ _ _ rev]
  · intro j; simp [p,laneModel,laneOf,bytes]; omega
  · intro j live ctr k hk
    have set := (sched.1 j).trans (decide_eq_true live)
    let row := bytes b.val[j.val]!.val
    have len : row.length = 64 := by simp [row,bytes]
    have initial i (hi : i<16) : base.val[i]! j = word row (4*i) := by
      simp only [input i hi,inputWord,set,ite_true,row]
    let old := (row.drop 18).take 4
    have ho : old.length = 4 := by simp [old,len]
    have shape := input_parts row N.val len (by omega)
    have layout := address_layout (row.take 18) old ((row.drop 22).take N.val ++ row.drop (22+N.val)) ctr k
      (by simp [len]) ho
    change addressWord (lanes base j) (fixed j) ctr k = word (packet _ ctr _ _) (4*k)
    change addressWord _ _ _ _ = _ at layout
    simp only [old,← shape] at layout
    change addressWord _ _ _ _ = word (row.take 18 ++ (Spec.toByte ctr.toNat 4 ++ ((row.drop 22).take N.val ++ row.drop (22+N.val)))) (4*k)
    rw [← layout]
    simp only [addressWord,lanes,hfixed,initial 4 (by decide),initial 5 (by decide),initial k hk]
end slhdsa.X86.Chain
