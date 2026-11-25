import Parallel.FusedShapeTable
import Parallel.Subtree
import Parallel.FusedWots
import Spec.Correctness

namespace ParallelFusedSignature
open Spec ParallelKeygen.Tree

/-- Value seen by one leaf in the production two-, four-, or eight-key batch. -/
def leaf (p : Params) (sk pk : Bytes) (a : Adrs) (count key : Nat) : Bytes :=
  let width := min 8 (max 1 count)
  let offset := key % width
  let addresses := fun i : Fin 8 => { a.setTypeAndClear WOTS_HASH with keypair := key-offset+i.val }
  ParallelSubtree.leaves p sk pk addresses ⟨offset%8,Nat.mod_lt _ (by decide)⟩

private theorem leaf_eq (p : Params) (sk pk : Bytes) (a : Adrs) (count i : Nat)
    (len : p.len = 2*p.n+3) (win : p.w=16) : leaf p sk pk a count i = xmssNode p sk i 0 pk a := by
  let width := min 8 (max 1 count)
  have hw : 0<width ∧ width≤8 := by dsimp [width];omega
  have small : i%width < 8 := (Nat.mod_lt _ hw.1).trans_le hw.2
  have low := Nat.mod_le i width
  unfold leaf
  rw [ParallelSubtree.leaves_eq _ _ _ _ len win]
  change wotsPkGen _ _ _ {a.setTypeAndClear WOTS_HASH with keypair:=i-i%width+(i%width)%8} = _
  rw [Nat.mod_eq_of_lt small, Nat.sub_add_cancel low]
  rfl

/-- The fused kernel observes the selected lane after permutation zero or the
    digit-th chain step. The authentication tail reads the source-derived tree
    for each level. The initial value in every signature slot is arbitrary. -/
def sign (p : Params) (m sk : Bytes) (idx : Nat) (pk : Bytes) (a : Adrs)
    (scratch : Nat → Bytes) : Bytes :=
  let selected := {(a.setTypeAndClear WOTS_HASH) with keypair := 8*(idx/8)+idx%8}
  let sig := (List.range (2*p.n+3)).flatMap fun c =>
    let secret := PRF p pk sk {wotsSkAdrs selected with word2:=c}
    ParallelFusedWots.capture (fun z => chain p secret 0 z pk {selected with word2:=c})
      (wotsDigits p m)[c]! (scratch c) 15
  sig ++ (List.range p.hp).flatMap fun z =>
    let root := (idx/2^z) ^^^ 1
    let parent := fun (_ : Bool) h i l r =>
      H p pk {a.setTypeAndClear TREE with word2:=h,word3:=i} (l++r)
    eval (leaf p sk pk a) parent (schedule[z]?.getD (.leaf 0 0)) z root

private theorem shapes (z : Nat) (hz : z < 9) :
    valid (schedule[z]?.getD (.leaf 0 0)) z=true := by
  have each : ∀ t : Fin 9, valid (schedule[t.val]?.getD (.leaf 0 0)) t.val=true := by decide
  exact each ⟨z,hz⟩

theorem sign_fips (p : Params) (m sk : Bytes) (idx : Nat) (pk : Bytes) (a : Adrs)
    (scratch : Nat → Bytes) (len : p.len=2*p.n+3) (win : p.w=16) (height : p.hp ≤ 9) :
    sign p m sk idx pk a scratch = xmssSign p m sk idx pk a := by
  unfold sign xmssSign wotsSign
  rw [show 8*(idx/8)+idx%8=idx by omega,←len]
  dsimp only
  apply congrArg₂ List.append
  · apply List.flatMap_congr
    intro c hc
    have digit := wotsDigits_lt p m c (List.mem_range.mp hc)
    exact ParallelFusedWots.selected _ _ _ _ (by omega)
  · apply List.flatMap_congr
    intro z hz
    apply eval_valid _ _ (fun h i => xmssNode p sk i h pk a)
    · exact fun ct i => leaf_eq p sk pk a ct i len win
    · intros; rfl
    · exact shapes z ((List.mem_range.mp hz).trans_le height)
end ParallelFusedSignature
