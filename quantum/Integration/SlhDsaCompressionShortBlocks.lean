import Integration.SlhDsaCompressionWotsSmallNative

namespace Reduction.Compression.ShortBlocks
open Ideal Ideal.HP Wots256 SLHDSA MLink TweakableHash OracleSpec OracleComp PQ.Interactive
abbrev Msg (ar : ℕ) := {xs : List Node // xs.length = ar}
def block {ar : ℕ} (x : Bytes 22 × Msg ar) := (tblocks x.1 x.2.1).1

theorem noTail {ar : ℕ} (ha : ar ≤ 2) (a : Bytes 22) (x : Msg ar) : (tblocks a x.val).2 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [tblocks_snd_length,x.property]
  omega

theorem injective {ar : ℕ} (ha : ar ≤ 2) : Function.Injective (@block ar) := by
  rintro ⟨a,m⟩ ⟨b,n⟩ h
  have e : tblocks a m.val = tblocks b n.val := Prod.ext h ((noTail ha a m).trans (noTail ha b n).symm)
  obtain ⟨h₁,h₂⟩ := tblocks_injective e
  exact Prod.ext h₁ (Subtype.ext h₂)

private theorem seed_zero (pk : Node) (j : ℕ) (hl : 16 ≤ j) (hh : j < 64) : (sb128 pk)[j] = 0 := by
  have h : (sb128 pk).toList[j]? = some 0 := by
    rw [sb128_toList, List.getElem?_append_right (by simpa using hl)]
    simp only [Vector.length_toList,List.getElem?_replicate_of_lt (show j-16 < 48 by omega)]
  have h2 : (sb128 pk).toList[j]? = some (sb128 pk)[j] := by
    rw [List.getElem?_eq_getElem (by simpa using hh)]
    simp
  exact Option.some.inj (h2.symm.trans h)

theorem seed_ne {ar : ℕ} (ha : ar ≤ 2) (pk : Node) (a : Bytes 22) (x : Msg ar) : sb128 pk ≠ block (a,x) := by
  let j := 22+16*ar
  have hj : j < 64 := by dsimp [j]; omega
  have pad : (tblocks a x.val).1[j] = 0x80 := by
    rw [tblocks_fst_eq]
    simp only [Vector.getElem_ofFn,tbytes]
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp [x.property,j])]
    simp [j,x.property,tailL]
  intro eq
  have h := congrArg (fun v : Blk => v[j]) eq
  rw [seed_zero pk j (by dsimp [j]; omega) hj] at h
  exact absurd (h.trans pad) (by decide)

def family (seeds : ProbComp Node) (ar n : ℕ) : THFam St Blk Node (Bytes 22) (Msg ar) Node Unit where
  IV := IV128
  sb := sb128
  seedGen := seeds
  tch := fun a m => tblocks a m.val
  out := out16
  Msg := fun _ => List Node
  cch := fun _ => tblocks
  cout := fun _ => out16
  numTargets := n

def tcrP (seeds : ProbComp Node) (ar n : ℕ) (c : Blk × List Blk → St) :=
  WotsPhase.chainTcr (family seeds ar n) c

noncomputable def classFirst {σ : Type} (seeds : ProbComp Node) (ar n : ℕ)
    (choose : OracleComp (TcrSpec (tcrP seeds ar n (fun _ => IV128))) σ) : TcrAdv (family seeds ar n) where
  State := σ
  choose := simulateQ Realize.embImpl choose
  forge := fun _ _ => pure (0,⟨List.replicate ar default,by simp⟩)

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.injective
#print axioms Reduction.Compression.ShortBlocks.seed_ne
