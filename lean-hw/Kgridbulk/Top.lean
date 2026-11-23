import Kgridbulk.Blocks
import Kgridbulk.Restore
import Kdiag.Fips
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86

private theorem wordsAt (s : Array U64 25#usize) (i : Nat) (hi : i<25) :
    (Keccak.words s)[i]! = s.val[i]!.bv := by
  simp (disch := simpa using hi) [Keccak.words,getElem!_pos]

theorem absorb_fips (s : Array U64 25#usize) (input : Slice U8) (whole : input.length%136=0) :
    absorb s input ⦃ out => (Keccak.words out,0) = (bytes input.val).foldl feed (Keccak.words s,0) ⦄ := by
  unfold absorb
  step with pack s as ⟨grid,loaded⟩
  have unpack : flatState grid = Keccak.words s := by
    apply ext25 _ _ (by simp [flatState]) (by simp [Keccak.words])
    intro i hi
    rw [wordsAt _ _ hi]
    unfold flatState
    rw [ofFnAt _ _ hi,loaded _ (by omega) _ (by dsimp; omega)]
    change s.val[5*(i/5)+i%5]!.bv = s.val[i]!.bv
    rw [show 5*(i/5)+i%5=i by omega]
  rw [show KgridbulkRust.shake256.RATE=KapplebulkRust.shake256.RATE by unfold KgridbulkRust.shake256.RATE KapplebulkRust.shake256.RATE; rfl]
  step with Kapplebulk.chunks input whole as ⟨it,full,sizes⟩
  have transform (g : Kdiag.Grid) := rounds Kdiag.gridView Kdiag.even_fips Kdiag.odd_fips g
  step with blocks it grid sizes transform as ⟨last,hashed⟩
  step with restore s last as ⟨out,hout⟩
  have written : Keccak.words out = flatState last := by
    apply ext25 _ _ (by simp [Keccak.words]) (by simp [flatState])
    intro i hi
    rw [wordsAt _ _ hi]
    simpa only [flatState,ofFnAt _ _ hi] using hout ⟨i,hi⟩
  rw [written]
  simpa only [full,unpack] using hashed

theorem blocks_fips (s : Array U64 25#usize) (input : Slice U8) (whole : input.length%136=0)
    (available : GatherRust.avx512Available=true) :
    KgridbulkRust.shake256.stream_x86.blocks s input ⦃ out => (Keccak.words out,0) =
      (bytes input.val).foldl feed (Keccak.words s,0) ⦄ := by
  unfold KgridbulkRust.shake256.stream_x86.blocks
  simp only [KgridbulkRust.sha256.x86.avx512_available,GatherRust.sha256.x86.avx512_available,
    available,massert,ite_true,bind_ok]
  step with UScalar.rem_spec input.len (y := KgridbulkRust.shake256.RATE) (by unfold KgridbulkRust.shake256.RATE; decide) as ⟨r,hr⟩
  have eq : r=0#usize := by apply UScalar.eq_of_val_eq; rw [hr]; unfold KgridbulkRust.shake256.RATE; exact whole
  simp only [eq,massert,ite_true,bind_ok]
  exact absorb_fips s input whole
end slhdsa.Kgridbulk
