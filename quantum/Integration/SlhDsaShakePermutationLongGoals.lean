import Integration.SlhDsaShakePermutationLongSparsity
import Integration.SlhDsaShakePermutationSparseSignature

/-! Challenge extraction and initial cleanliness of the multi-block search
predicate. An encoded candidate prefixes another honest hash only at the
same tweak. The challenge protocol reserves that tweak for its target. -/
namespace Reduction.ShakePermutation.Long
open Classical MLink Classic SLHDSA SparsePort
noncomputable section
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ)

def blocks (d : Bytes 32) (xs : List S.Node) := messageBlocks (sp (ShakeXof.thBytes S pk d xs))

def encode : Arity.Row S ar ↪ List Rate where
  toFun j := blocks S pk j.1 j.2.val
  inj' x y he := by
    have eq := congrArg cv (messageBlocks_injective he)
    have h : ShakeXof.thBytes S pk x.1 x.2.val = ShakeXof.thBytes S pk y.1 y.2.val :=
      by simpa [cv,sp,List.map_map,Function.comp_def] using eq
    obtain ⟨hl,hr⟩ := List.append_inj h (by simp)
    exact Prod.ext (Vector.toList_inj.mp (List.append_cancel_left hl))
      (Subtype.ext (MIdeal.Sha512.payload_injective S hr))

theorem prefix_tweak (d e : Bytes 32) (xs ys : List S.Node)
    (h : blocks S pk d xs <+: blocks S pk e ys) : d=e := by
  obtain ⟨l,eq⟩ := h
  have he := congrArg List.head? eq
  simp only [blocks,messageBlocks,List.ofFn_succ,List.cons_append,List.head?_cons,Option.some.injEq] at he
  apply Vector.ext; intro i hi
  let w : Fin 32 := ⟨i,hi⟩
  have byte := congrArg (fun r => blockByte r ⟨S.vp.params.n+w.val,by
    have : S.vp.params.n ≤ 32 := by cases S <;> decide
    omega⟩) he
  have b := (Arity.tweak_byte S pk d xs w).symm.trans (byte.trans (Arity.tweak_byte S pk e ys w))
  exact UInt8.toBitVec_inj.mp b

abbrev Targets := Bytes 32 → Option (Arity.Msg S ar × S.Node)

def goal (targets : Targets S ar) (p : List Rate) : Option S.Node := do
  let j ← ShakeXof.locate (encode S pk ar) p
  let (m,v) ← targets j.1
  if j.2=m then none else some v

theorem goal_hit (targets : Targets S ar) (p : List Rate) (v : S.Node) (h : goal S pk ar targets p = some v) :
    ∃ j m, encode S pk ar j = p ∧ targets j.1 = some (m,v) ∧ j.2 ≠ m := by
  unfold goal at h
  cases eq : ShakeXof.locate (encode S pk ar) p with
  | none => simp [eq] at h
  | some j =>
    cases ht : targets j.1 with
    | none => simp [eq,ht] at h
    | some pair =>
      rcases pair with ⟨m,w⟩
      by_cases same : j.2 = m
      · simp [eq,ht,same] at h
      · have heq : w = v := by simpa [eq,ht,same] using h
        subst v
        exact ⟨j,m,ShakeXof.located _ eq,ht,same⟩

theorem goal_candidate (targets : Targets S ar) (d : Bytes 32) (m m₀ : Arity.Msg S ar) (v : S.Node)
    (h : targets d = some (m₀,v)) (ne : m ≠ m₀) : goal S pk ar targets (blocks S pk d m.val) = some v := by
  change goal S pk ar targets (encode S pk ar (d,m)) = _
  simp [goal,ShakeXof.locate_emb,h,ne]

def covered (t : EdgeTrace Words) (L : List (Bytes 32 × List S.Node)) :=
  ∀ ⦃p w⦄, Trail t p w → p = [] ∨ ∃ e ∈ L, p <+: blocks S pk e.1 e.2

def reserved (targets : Targets S ar) (L : List (Bytes 32 × List S.Node)) :=
  ∀ d m v, targets d = some (m,v) → ∀ xs, (d,xs) ∈ L → xs = m.val

theorem initially_clear (targets : Targets S ar) (L : List (Bytes 32 × List S.Node)) (t : EdgeTrace Words)
    (uniq : UniquePaths t) (cover : covered S pk t L) (once : reserved S ar targets L) :
    ¬bad (SkFormat.split S) (goal S pk ar targets) t := by
  rintro (loss|⟨p,w,path,hit⟩)
  · exact loss uniq
  obtain ⟨j,m,fmt,target,ne⟩ := goal_hit S pk ar targets p _ hit
  rcases cover path with nil|⟨⟨d,xs⟩,seen,pref⟩
  · have he := congrArg List.length (fmt.trans nil)
    change (messageBlocks _).length = 0 at he
    rw [messageBlocks_length] at he; omega
  · rw [← fmt] at pref
    have same := prefix_tweak S pk j.1 d j.2.val xs pref
    subst d
    have old := once _ _ _ target xs seen
    subst xs
    have l : (blocks S pk j.1 j.2.val).length = (blocks S pk j.1 m.val).length := by
      simp only [blocks,messageBlocks_length,sp,List.length_map,ShakeXof.thBytes,List.length_append,
        Vector.length_toList,MIdeal.Sha512.payload_length,j.2.property,m.property]
    have blockEq := pref.eq_of_length l
    have both : encode S pk ar j = encode S pk ar (j.1,m) := blockEq
    exact ne (congrArg Prod.snd ((encode S pk ar).injective both))

end
end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.initially_clear
