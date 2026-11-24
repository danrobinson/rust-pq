import Integration.SlhDsaShakePermutationAbsorb
import Integration.SlhDsaShakeXofPrf

/-! The complete, single-block SHAKE SK.PRF row as a permutation input, and
the output prefix/suffix bijection for that row. -/
namespace Reduction.ShakePermutation.SkFormat
open Classical MLink SLHDSA SLHDSA.Security ShakeXof
variable (S : Sha2Set)
abbrev Row := S.Node × (S.Node × Bytes 32)
def rowBytes (x : Row S) := x.2.1.toList ++ x.2.2.toList ++ x.1.toList

private theorem short (x : Row S) : (sp (rowBytes S x)).length < 136 := by
  have h : 2*S.vp.params.n+32 < 136 := by cases S <;> decide
  simp only [sp,List.length_map,rowBytes,List.length_append,Vector.length_toList]
  omega

private theorem one_block (x : Row S) :
    messageBlocks (sp (rowBytes S x)) = [rateBlock (padded (sp (rowBytes S x))) 0] := by
  unfold messageBlocks
  have hq := Nat.div_eq_of_lt (short S x)
  simp only [hq, Nat.zero_add, List.ofFn_succ, List.ofFn_zero, Fin.val_cast, Fin.val_zero]

def input : Row S ↪ Words where
  toFun x := join (rateBlock (padded (sp (rowBytes S x))) 0) 0
  inj' x y h := by
    have e := congrArg rateOf h
    simp only [rate_join] at e
    have p : messageBlocks (sp (rowBytes S x)) = messageBlocks (sp (rowBytes S y)) := by
      rw [one_block,one_block,e]
    have eq := congrArg cv (messageBlocks_injective p)
    have row : rowBytes S x = rowBytes S y := by simpa [cv,sp,List.map_map,Function.comp_def] using eq
    rcases x with ⟨k,pk,a⟩
    rcases y with ⟨l,p,b⟩
    obtain ⟨left,he⟩ := List.append_inj row (by simp)
    obtain ⟨hk,ha⟩ := List.append_inj left (by simp)
    exact Prod.ext (Vector.toList_inj.mp he) (Prod.ext (Vector.toList_inj.mp hk) (Vector.toList_inj.mp ha))

abbrev Suffix := Bytes (136 - S.vp.params.n) × Capacity

private def splitBytes {n m : ℕ} (h : n ≤ m) : Bytes m ≃ Bytes n × Bytes (m-n) where
  toFun v := (head h v,Vector.ofFn fun i => v[n+i.val]'(by omega))
  invFun p := Vector.ofFn fun i => if e : i.val < n then p.1[i.val]'e else p.2[i.val-n]'(by omega)
  left_inv v := by
    apply Vector.ext
    intro i hi
    by_cases e : i < n
    · simp [head,e]
    · simp [e,Nat.add_sub_of_le (Nat.le_of_not_gt e)]
  right_inv p := by
    apply Prod.ext
    · apply Vector.ext; intro i hi; simp [head]
    · apply Vector.ext; intro i hi; simp

def split : Words ≃ S.Node × Suffix S :=
  let rs : Words ≃ Rate × Capacity := ⟨(fun w => (rateOf w,capOf w)),(fun p => join p.1 p.2),
    join_split,fun p => Prod.ext (rate_join p.1 p.2) (cap_join p.1 p.2)⟩
  let b := Completion.equiv.trans (splitBytes (n := S.vp.params.n) (m := 136)
    (by have := (output_sizes S).2; have := node_le_digest S; omega))
  rs.trans ((b.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc ..))

theorem split_fst (w : Words) : (split S w).1 =
    head (by have := (output_sizes S).2; have := node_le_digest S; omega) (Completion.bytes (rateOf w)) := rfl

private theorem nested {n m k : ℕ} (h : n ≤ m) (g : m ≤ k) (v : Bytes k) :
    head h (head g v) = head (h.trans g) v := by
  apply Vector.ext
  intro i hi
  simp [head]

theorem prf_eq (π : Permutation) (pk sk : S.Node) (a : Adrs) :
    (primitives (lanes π) S.vp.params).PRF pk sk a = (split S (π (input S (sk,pk,a.toVector)))).1 := by
  change hash (lanes π) (nd pk ++ nd a.toVector ++ nd sk) S.vp.params.n = _
  have e : sp (rowBytes S (sk,pk,a.toVector)) = nd pk ++ nd a.toVector ++ nd sk := by
    simp only [rowBytes,sp_append]; rfl
  rw [← e,← hash_prefix]
  rw [answer_blocks,one_block,← head_eq_prefix (node_le_digest S)]
  have st (r : Rate) : Fix.ordinary π [r] = π (join r 0) := by
    apply congrArg π
    apply congrArg₂ join _ rfl
    funext i
    exact UInt64.xor_zero
  rw [st,nested,split_fst]
  rfl

theorem card_suffix : Fintype.card (Suffix S) = 2 ^ (1600-8*S.vp.params.n) := by
  have c : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64,← pow_mul]
  rw [Fintype.card_prod,c,card_bytes']
  cases S <;> decide +kernel

end Reduction.ShakePermutation.SkFormat
#print axioms Reduction.ShakePermutation.SkFormat.prf_eq
#print axioms Reduction.ShakePermutation.SkFormat.card_suffix
