import Rcavx.Paired
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

def rawWord (data : List U8) (i : Nat) : BitVec 64 :=
  data[i]!.bv ++ data[i+1]!.bv ++ data[i+2]!.bv ++ data[i+3]!.bv ++ data[i+4]!.bv ++ data[i+5]!.bv ++ data[i+6]!.bv ++ data[i+7]!.bv

theorem unpackWords (data : List U8) (i : Nat) :
    unpack data i mask128 = (rawWord data (16*i),rawWord data (16*i+8)) := by rfl

private theorem raw_fips (data : List U8) (i : Nat) (room : i+8 ≤ data.length) :
    rawWord data i = Spec.SHA512.word (bytes data) i := by
  simp (disch := omega) only [rawWord,Spec.SHA512.word,bytes_getElem!,getElem!_pos]

private theorem leftWord (a b : List U8) (i : Nat) (h : i+8 ≤ a.length) :
    rawWord (a++b) i = rawWord a i := by
  simp (disch := omega) only [rawWord,List.getElem!_append_left]

private theorem rightWord (a b : List U8) (i : Nat) :
    rawWord (a++b) (a.length+i) = rawWord b i := by
  simp (disch := omega) only [rawWord,List.getElem!_append_right]
  simp only [Nat.add_assoc,Nat.add_sub_cancel_left]

abbrev Block := Array U8 128#usize
def msgW (b : Block) := Spec.SHA512.schedule (bytes b.val)
theorem input (b : Block) (i : Nat) (h : i<8) :
    unpack b.val i mask128 = pair (msgW b) i := by
  rw [unpackWords]
  have len : b.val.length=128 := by simp
  simp (disch := omega) only [raw_fips,pair,msgW,slhdsa.H512.schedule_lt16]
  rw [show 8*(2*i)=16*i by omega,show 8*(2*i+1)=16*i+8 by omega]

theorem initial (b : Block) (x ms : Ms) :
    load_data_avx x ms b.val ⦃ x ms => x=window (pair (msgW b)) 0 ∧ Cache (msgW b) 0 ms ⦄ := by
  have readable : ¬ b.val.length < 128 := by simp
  simp (disch := decide) only [load_data_avx,readable,ite_false,lanes,window,input,bind_ok,step_simps,constantsAt,k_eq]
  intro p lo hi
  change p<8 at hi
  interval_cases p <;> rfl

private theorem left_input (a b : Block) (i : Nat) (h : i<8) :
    unpack (a.val++b.val) i mask256half = pair (msgW a) i := by
  change unpack (a.val++b.val) i mask128 = _
  rw [← input a i h,unpackWords,unpackWords]
  simp (disch := simp; omega) only [leftWord]

private theorem right_input (a b : Block) (i : Nat) (h : i<8) :
    unpack (a.val++b.val) (8+i) mask256half = pair (msgW b) i := by
  change unpack (a.val++b.val) (8+i) mask128 = _
  rw [← input b i h,unpackWords,unpackWords]
  have len : a.val.length=128 := by simp
  rw [show 16*(8+i)+8=a.val.length+(16*i+8) by omega,show 16*(8+i)=a.val.length+16*i by omega,rightWord,rightWord]

theorem initial2 (blocks : Array Block 2#usize) (x : Array Wide 8#usize) (ms : Ms) (saved : Array Lane 40#usize) :
    load_data_avx2 x ms saved blocks ⦃ x ms saved =>
      x=window (Both (msgW blocks.val[0]!) (msgW blocks.val[1]!)) 0 ∧
      Cache (msgW blocks.val[0]!) 0 ms ∧ Archive (msgW blocks.val[1]!) 8 saved ⦄ := by
  let a := blocks.val[0]!
  let b := blocks.val[1]!
  have split : blocks.val.flatMap (·.val) = a.val++b.val := by
    have h : blocks.val = [a,b] := by
      apply List.ext_getElem
      · simp
      · intro i hi _
        have bound : i<2 := by simpa using hi
        interval_cases i <;> simp [a,b]
    conv_lhs => rw [h]
    simp
  unfold load_data_avx2
  simp (disch := decide) only [split,lanes,window,Both,left_input,right_input,constantsAt,k_eq,step_simps]
  refine ⟨rfl,?_,?_⟩
  · intro p _ hi
    change p<8 at hi
    interval_cases p <;> rfl
  · intro p hi
    simp only [Array.from_val]
    interval_cases p <;> rfl
end slhdsa.X86.RustCrypto512
