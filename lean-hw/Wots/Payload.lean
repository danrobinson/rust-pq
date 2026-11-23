import Wotsx86.Proof
import Keypadding.Proof
import Spec.Correctness
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

private theorem payload_byte (f : Nat → Spec.Bytes) (n len i k : Nat)
    (width : ∀ j, (f j).length = n) (hi : i < len) (hk : k < n) :
    ((List.range len).flatMap f)[i*n+k]! = (f i)[k]! := by
  have sub := Spec.flatMap_piece f n width len i k 1 hi (by omega)
  have first := congrArg (fun l : Spec.Bytes => l[0]!) sub
  simpa [List.getElem!_eq_getElem?_getD,List.getElem?_take,List.getElem?_drop] using first

/-- The endpoint writer inserts precisely the concatenation consumed by the batched
digest, preserving all other bytes of each initialized message row. -/
theorem payload_row {L} (n len : Nat) (expect : Nat → Nat → Spec.Bytes) (before after : Rows L)
    (width : ∀ r j, (expect r j).length=n) (positive : 0<n) (nonempty : 0<len)
    (done : processed n len (fun t => expect (t/len) (t%len)) before after (len*before.length))
    (r : Nat) (row : r < before.length) :
    bytes after.val[r]!.val = (bytes before.val[r]!.val).setSlice! 22 ((List.range len).flatMap (expect r)) := by
  let payload := (List.range len).flatMap (expect r)
  have size : payload.length=len*n := Spec.length_flatMap_const _ _ (width r) _
  change _ = (bytes before.val[r]!.val).setSlice! 22 payload
  apply List.ext_getElem
  · simp
  · intro b hb hb'
    have bound : b<L.val := by simpa using hb
    rw [← getElem!_pos (bytes after.val[r]!.val) b hb,← getElem!_pos ((bytes before.val[r]!.val).setSlice! 22 payload) b hb']
    by_cases outside : b<22 ∨ 22+len*n ≤ b
    · rw [List.getElem!_setSlice!_same _ _ _ _ (by simpa [size] using outside)]
      simpa (disch := simpa using bound) [bytes,getElem!_pos] using congrArg (fun x : U8 => x.bv) (done.2.2 r row b bound outside)
    · have pos : b-22<len*n := by omega
      let j := (b-22)/n
      let k := (b-22)%n
      have hj : j<len := (Nat.div_lt_iff_lt_mul positive).mpr pos
      have hk : k<n := Nat.mod_lt _ positive
      have split : b-22=j*n+k := by simpa [j,k,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div (b-22) n).symm
      have offset : (r*len+j)/len=r := by rw [Nat.mul_comm r len,Nat.mul_add_div nonempty,Nat.div_eq_of_lt hj,Nat.add_zero]
      have slot : (r*len+j)%len=j := by simp [Nat.mod_eq_of_lt hj]
      have range : r*len+j<len*before.length := by
        have limit := Nat.mul_le_mul_right len row
        rw [Nat.succ_mul] at limit
        rw [Nat.mul_comm len]; omega
      have wrote := done.2.1 (r*len+j) range k hk
      dsimp only at wrote
      rw [offset,slot,show 22+j*n+k=b by omega] at wrote
      rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega,by omega,by simpa using bound⟩,split,
        payload_byte _ _ _ _ _ (width r) hj hk]
      simpa (disch := simpa using bound) [bytes,getElem!_pos] using wrote

def keyPayload (p : Spec.Params) (a : Spec.Adrs) (pk sk : Spec.Bytes) (key len : Nat) :=
  (List.range len).flatMap (endpoint p a pk sk key)

/-- All endpoint bytes in each checked writer output form one contiguous WOTS message. -/
theorem endpoint_payload {N L} (p : Spec.Params) [Fact (p.family=.sha2)] (hv : p.Valid)
    (st : Array U32 8#usize) (sk : Array U8 N) (a : WotsX86Rust.address.Adrs) (first : U32)
    (before : Rows L) (pk : Spec.Bytes) (cpu : GatherRust.avx512Available=true) (shape : Checked.supported N L)
    (batch : before.length ≤ 16) (width : N.val=p.n) (hpk : pk.length=p.n)
    (seed : st.val.map (·.bv)=seedState p.n pk) (keys : first.val+before.length ≤ 2^32) :
    WotsX86Rust.sha256.x86.wots_endpoints st sk a first before ⦃ after =>
      after.length=before.length ∧ ∀ r < before.length, bytes after.val[r]!.val =
        (bytes before.val[r]!.val).setSlice! 22 (keyPayload p (adrsS (WotsRust.addressOf (WotsX86Rust.asKernel a)))
            pk (bytes sk.val) (first.val+r) (2*N.val+3)) ⦄ := by
  apply WP.spec_mono (Checked.endpoints_fips p st sk a first before pk cpu shape batch width hpk seed keys)
  intro after done
  refine ⟨done.1,?_⟩
  apply payload_row N.val (2*N.val+3) _ before after _ _ (by omega) done
  · intro r j
    rw [width]
    exact Spec.chain_length p hv _ (Spec.PRF_length p hv _ _ _) _ _ _ _
  · rcases shape with h|h|h <;> omega

/-- The row initializer and endpoint insertion together yield the exact FIPS padding. -/
theorem prepared_payload {L} (a : PadRust.address.Adrs) (k : U32) (size block : Usize)
    (payload : Spec.Bytes) (row : Array U8 L)
    (shape : (payload.length=560 ∧ L.val=640 ∧ block.val=64) ∨
      (payload.length=1224 ∧ L.val=1280 ∧ block.val=128) ∨ (payload.length=2144 ∧ L.val=2304 ∧ block.val=128))
    (sizeEq : size.val=22+payload.length)
    (prepared : PadRust.xmss.wide.prepare_message (Array.repeat L 0#u8) a k size block = ok row) :
    (bytes row.val).setSlice! 22 payload =
      let msg := (adrsS (Keypadding.keyAddress a k)).compress ++ payload
      if block.val=64 then padFrom 64 msg else slhdsa.S512.padFrom 128 msg := by
  let raw : List U8 := payload.map UScalar.mk
  have same : bytes raw = payload := by simp [raw,bytes,List.map_map,Function.comp_def]
  have len : raw.length=payload.length := by simp [raw]
  have proof := Keypadding.padded_endpoints a k size block raw (by rwa [len]) (by rwa [len])
  rw [prepared] at proof
  have result := (WP.spec_ok _).mp proof
  change bytes (row.val.setSlice! 22 raw) = _ at result
  simpa only [bytes,List.map_setSlice!,show raw.map (·.bv) = payload from same] using result
end slhdsa.X86.Wots
