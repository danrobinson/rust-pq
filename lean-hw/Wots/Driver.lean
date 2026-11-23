import Wots.Placement
import Wots.Entry
import Digest256.Fips
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open Spec.SHA256
open WotsRust.sha256.x86.avx512

def endpoint (P : Spec.Params) (a : Spec.Adrs) (pk sk : Spec.Bytes) (key id : Nat) :=
  let adrs := {a with typ := 0,keypair := key,word2 := id,word3 := 0}
  Spec.chain P (Spec.PRF P pk sk {Spec.wotsSkAdrs adrs with word2 := id}) 0 15 pk adrs

def processed {L} (n len : Nat) (expected : Nat → Spec.Bytes) (before after : Rows L) (done : Nat) :=
  after.length = before.length ∧
  (∀ t < done, ∀ k < n, (after.val[t/len]!.val[22+t%len*n+k]!).bv = (expected t)[k]!) ∧
  ∀ r < before.length, ∀ b < L.val, b < 22 ∨ 22+len*n ≤ b →
    after.val[r]!.val[b]! = before.val[r]!.val[b]!

private theorem separate (len n a b k : Nat) (hk : k<n) (distinct : a ≠ b) :
    a/len ≠ b/len ∨ 22+a%len*n+k < 22+b%len*n ∨ 22+b%len*n+n ≤ 22+a%len*n+k := by
  by_cases keys : a/len=b/len
  · have different : a%len ≠ b%len := by
      intro h
      have one := Nat.mod_add_div a len
      rw [h,keys,Nat.mod_add_div] at one
      exact distinct one.symm
    by_cases low : a%len < b%len
    · have h := Nat.mul_le_mul_right n (by omega : a%len+1 ≤ b%len)
      rw [Nat.succ_mul] at h
      omega
    · have h := Nat.mul_le_mul_right n (by omega : b%len+1 ≤ a%len)
      rw [Nat.succ_mul] at h
      omega
  · exact Or.inl keys

theorem advance {N L} (hash : Hash) (before buf after : Rows L) (len pos used : Nat) (expected : Nat → Spec.Bytes)
    (prior : processed N.val len expected before buf pos) (updated : batchWrites (N := N) hash buf after len pos used)
    (lo : 16 ≤ len) (hu : used ≤ 16) (positive : 0 < N.val) (room : 22+len*N.val ≤ L.val)
    (correct : ∀ j : Fin 16, j.val < used → ∀ k < N.val, Store.digestByte hash j k = (expected (pos+j.val))[k]!) :
    processed N.val len expected before after (pos+used) := by
  have size : after.length = buf.length := by
    obtain ⟨_,mid,_,first,second⟩ := updated
    split at second
    · exact second.1.trans first.1
    · simpa only [second] using first.1
  refine ⟨size.trans prior.1,?_,?_⟩
  · intro t ht k hk
    by_cases old : t < pos
    · rw [batch_frame hash buf after len pos used updated lo hu positive room _ _
        (fun j _ => separate len N.val t (pos+j) k hk (by omega))]
      exact prior.2.1 t old k hk
    · let j : Fin 16 := ⟨t-pos,by omega⟩
      have eq : pos+j.val=t := by dsimp [j]; omega
      have live : j.val < used := by dsimp [j]; omega
      have placed := placed_lane hash buf after len pos used updated lo hu room j live k hk
      simpa only [eq] using placed.trans (correct j live k hk)
  · intro r hr b hb guard
    rw [batch_frame hash buf after len pos used updated lo hu positive room]
    · exact prior.2.2 r hr b hb guard
    · intro j hj
      rcases guard with header|suffix
      · right; left; omega
      · have le : (pos+j)%len+1 ≤ len := Nat.mod_lt _ (by omega)
        have fit := Nat.mul_le_mul_right N.val le
        rw [Nat.succ_mul] at fit
        omega

theorem digest_byte_eq (hash : Hash) (j : Fin 16) (k n : Nat) (hk : k<n) (hn : n ≤ 32) :
    Store.digestByte hash j k = ((ser (stateWords (laneState hash j))).take n)[k]! := by
  rw [List.getElem!_eq_getElem?_getD,List.getElem?_take_of_lt hk,← List.getElem!_eq_getElem?_getD,Digest.ser_byte]
  · unfold Store.digestByte
    rw [← Leaf.lane_lookup hash j (k/4) (by omega)]
  · simp [stateWords,laneState]; omega


set_option maxHeartbeats 1500000 in
theorem batches {N L} (P : Spec.Params) [Fact (P.family = .sha2)] (first : U32)
    (base : Words) (iv two : Hash) (out : Rows L) (len total : Usize)
    (a : Spec.Adrs) (pk sk : Spec.Bytes) (hn : N.val=P.n)
    (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length=P.n) (hsk : sk.length=P.n)
    (lo : 16 ≤ len.val) (hi : len.val ≤ 67) (count : total.val = len.val*out.length)
    (keys : first.val+out.length ≤ 2^32) (room : 22+len.val*N.val ≤ L.val)
    (seed : ∀ j, stateWords (laneState iv j) = seedState P.n pk)
    (ready : ∀ j k, k < 16 → base.val[k]! j = word (padFrom 64 ((a.setTypeAndClear Spec.WOTS_PRF).compress ++ sk)) (4*k))
    (pre : Trace two (fun j => schedule (laneBlock base j)) (laneState iv) 2) :
    wots_endpoints_loop1 N ⟨⟨0#usize,total⟩,16#usize⟩ first out base iv
      (fun j => BitVec.ofNat 32 j.val) (fun _ => 0xffff) (fun _ => 0x50000) len two ⦃ r =>
        processed N.val len.val (fun t => endpoint P a pk sk (first.val+t/len.val) (t%len.val)) out r total.val ⦄ := by
  let expected := fun t => endpoint P a pk sk (first.val+t/len.val) (t%len.val)
  unfold wots_endpoints_loop1
  apply loop.spec_decr_nat (measure := fun p : Leaf.Iter × Rows L => total.val-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end = total ∧ p.1.step_by = 16#usize ∧ p.1.iter.start.val ≤ total.val ∧
      processed N.val len.val expected out p.2 p.1.iter.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hs,hle,prior⟩
    simp only at he hs hle prior
    dsimp only
    rw [batch_body_eq]
    by_cases more : it.iter.start.val < it.iter.end.val
    · step with Leaf.next it more hs as ⟨o,t,ho,ht,he',hs'⟩
      simp only [ho,lift,bind_ok]
      have hlen := prior.1
      have limit : len.val*buf.length = total.val := by rw [hlen,count]
      have max : total.val ≤ Usize.max := by scalar_tac
      have run : it.iter.start.val < total.val := he ▸ more
      step as ⟨size,hsize⟩
      step as ⟨remaining,hr⟩
      let used := core.cmp.impls.OrdUsize.min 16#usize remaining
      have hu : used.val = min 16 (total.val-it.iter.start.val) := by
        change size.val = len.val*buf.length at hsize
        simp [used,hr,hsize,limit]
      have live : it.iter.start.val < len.val*buf.length := by omega
      have safe : first.val+it.iter.start.val/len.val < 2^32 := by
        have : it.iter.start.val/len.val < buf.length := Nat.div_lt_of_lt_mul live
        omega
      step with batch_fips P N len it.iter.start first iv two base pk sk a hn shape hpk hsk lo hi safe seed ready pre as ⟨hash,hh⟩
      rw [store_batch_eq]
      step with write_batch_spec N len it.iter.start used hash buf (hn ▸ shape) lo (by omega) live (by omega) room as ⟨after,ha⟩
      have newEnd : t.iter.start.val = it.iter.start.val+used.val := by rw [ht,he,hu]; omega
      refine ⟨he'.trans he,hs'.trans hs,by omega,?_,by omega⟩
      rw [newEnd]
      apply advance hash out buf after len.val it.iter.start.val used.val expected prior ha lo (by omega) (by omega) room
      intro j hj k hk
      have inBounds : it.iter.start.val+j.val < buf.length*len.val := by rw [Nat.mul_comm,limit]; omega
      have keyFits : first.val+(it.iter.start.val+j.val)/len.val < 2^32 := by
        have : (it.iter.start.val+j.val)/len.val < buf.length := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using inBounds)
        omega
      rw [digest_byte_eq hash j k P.n (by omega) (by omega),hh j]
      simp only [expected,endpoint,BitVec.toNat_ofNat,Nat.mod_eq_of_lt keyFits]
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,t,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.iter.start.val = total.val := by rw [he] at more; omega
      exact eq ▸ prior
  · simp [processed]

/-- Complete extracted AVX-512 WOTS endpoint kernel, including both keypair
destinations and every preserved byte surrounding the packed endpoint region. -/
theorem endpoints_fips {N L} (P : Spec.Params) [Fact (P.family = .sha2)] (state : Array U32 8#usize)
    (sk : Array U8 N) (a : WotsRust.address.Adrs) (first : U32) (out : Rows L) (pk : Spec.Bytes)
    (hn : N.val=P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length=P.n)
    (seed : state.val.map (·.bv) = seedState P.n pk)
    (fits : (2*N.val+3)*out.length ≤ Usize.max) (keys : first.val+out.length ≤ 2^32)
    (room : 22+(2*N.val+3)*N.val ≤ L.val) :
    wots_endpoints state sk a first out ⦃ r =>
      let len := 2*N.val+3
      processed N.val len (fun t => endpoint P (adrsS (WotsRust.addressOf a)) pk (bytes sk.val)
        (first.val+t/len) (t%len)) out r (len*out.length) ⦄ := by
  apply entry_spec P state sk a first out pk hn shape seed fits
  intro base iv two len total hlen htotal hs hw ht
  have h := batches P first base iv two out len total (adrsS (WotsRust.addressOf a)) pk (bytes sk.val)
    hn shape hpk (by simp [hn]) (by omega) (by omega) htotal keys (by simpa only [hlen] using room) hs hw ht
  simpa only [htotal,hlen] using h

end slhdsa.X86.Wots
