import Cachepath.NativeShakeWots.Layout
import Cachepath.NativeVerify.WotsState
import Cachepath.NativeVerify.WotsHash
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

def packedWord (n : Nat) (sw : Array U64 4#usize) (w0 w1 : U64) (w2 w3 : Array U64 machine.width)
    (payload : Nat → Nat → BitVec 64) (k l : Nat) : BitVec 64 :=
  headerWord n w0 w1 w2 w3 (fun i j => if i<n then sw.val[i]!.bv else payload (i-(n+4)) j) k l

private theorem combine {n : Nat} (sw : Array U64 4#usize) (w0 w1 : U64) (w2 w3 : Array U64 machine.width)
    (old mid out : Matrix machine.width) (payload : Nat → Nat → BitVec 64)
    (pre : Prefix n (n+4) sw payload old mid)
    (headerWords : ∀ k<25, ∀ l<machine.width.val, cell out k l = headerWord n w0 w1 w2 w3 (cell mid) k l) :
    ∀ k<25, ∀ l<machine.width.val, cell out k l = packedWord n sw w0 w1 w2 w3 payload k l := by
  intro k hk l hl
  rw [headerWords k hk l hl]
  unfold packedWord headerWord
  rw [pre k l hl]
  dsimp only
  split_ifs <;> first | rfl | omega

theorem fill_layout (N : Usize) (s : Matrix machine.width) (sw skw : Array U64 4#usize) (w0 w1 : U64)
    (w2 w3 : Array U64 machine.width) (small : N.val≤32) :
    fill_prf N s sw skw w0 w1 w2 w3 ⦃ out => ∀ k<25, ∀ l<machine.width.val,
      cell out k l = packedWord (N.val/8) sw w0 w1 w2 w3 (fun j _ => skw.val[j]!.bv) k l ⦄ := by
  unfold fill_prf
  step as ⟨n,div⟩
  step as ⟨offset,off⟩
  step with fill_prefix n offset s sw skw (by omega) (by omega) as ⟨st,pre⟩
  change header n offset st w0 w1 w2 w3 ⦃ _ => _ ⦄
  apply WP.spec_mono (header_spec n offset st w0 w1 w2 w3 (by omega) (by omega))
  intro out head
  rw [← div]
  rw [off] at pre
  exact combine sw w0 w1 w2 w3 s st out _ pre head

theorem refill_layout (N : Usize) (s : Matrix machine.width) (sw : Array U64 4#usize) (w0 w1 : U64)
    (w2 w3 : Array U64 machine.width) (small : N.val≤32) :
    refill_short_inplace N s sw w0 w1 w2 w3 ⦃ out => ∀ k<25, ∀ l<machine.width.val,
      cell out k l = packedWord (N.val/8) sw w0 w1 w2 w3 (cell s) k l ⦄ := by
  unfold refill_short_inplace
  step as ⟨n,div⟩
  step as ⟨offset,off⟩
  step with refill_prefix n offset s sw (by omega) (by omega) as ⟨st,pre⟩
  change header n offset st w0 w1 w2 w3 ⦃ _ => _ ⦄
  apply WP.spec_mono (header_spec n offset st w0 w1 w2 w3 (by omega) (by omega))
  intro out head
  rw [← div]
  rw [off] at pre
  exact combine sw w0 w1 w2 w3 s st out _ pre head

set_option maxHeartbeats 2000000 in
theorem packed_fips {N : Usize} (seed value : Array U8 N) (a : address.Adrs) (chain index : U32)
    (sw : Array U64 4#usize) (w0 w1 : U64) (w2 w3 : Array U64 machine.width)
    (payload : Nat → Nat → BitVec 64) (before after : Matrix machine.width) (l : Nat)
    (small : N.val≤32) (align : N.val%8=0)
    (seedWords : ∀ k<N.val/8, sw.val[k]!.bv = inputWord seed.val k)
    (a0 : w0.bv=addressWord a 0) (a1 : w1.bv=addressWord a 1)
    (a2 : w2.val[l]!.bv=addressWord a 2) (tag : w3.val[l]!.bv=addressLow chain ||| wordTag index)
    (words : ∀ j<N.val/8, payload j l=inputWord value.val j)
    (written : ∀ k<25, cell before k l=packedWord (N.val/8) sw w0 w1 w2 w3 payload k l)
    (permuted : ShakeBatch.lane after l=Spec.Keccak.permute (ShakeBatch.lane before l)) :
    digest N after l = Spec.shake256 (bytes seed.val ++ ((adrsS {a with word2:=chain,word3:=index}).bytes ++ bytes value.val)) N.val := by
  apply hashed_short seed value a chain index before after l small align permuted
  intro k hk
  rw [written k hk]
  unfold packedWord headerWord baseWord initialWord
  dsimp only
  have pad : (2*N.val+32)/8=2*(N.val/8)+4 := by omega
  rw [pad]
  by_cases pl : N.val/8+4≤k ∧ k<N.val/8+4+N.val/8
  · simp only [ite_eq_left pl,ite_eq_right (by omega : k≠16),ite_eq_right (by omega : ¬2*(N.val/8)+4<k),
      ite_eq_right (by omega : k≠2*(N.val/8)+4),ite_eq_right (by omega : k≠N.val/8+3),
      ite_eq_right (by omega : k≠N.val/8+2),ite_eq_right (by omega : k≠N.val/8+1),
      ite_eq_right (by omega : k≠N.val/8),ite_eq_right (by omega : ¬k<N.val/8)]
    exact words _ (by omega)
  · rw [ite_eq_right pl]
    split_ifs <;> first | omega | rfl | decide | exact tag | exact seedWords _ (by omega) |
      (rw [a0]; congr 1 <;> omega) | (rw [a1]; congr 1 <;> omega) | (rw [a2]; congr 1 <;> omega)

end slhdsa.NativeShakeWots
