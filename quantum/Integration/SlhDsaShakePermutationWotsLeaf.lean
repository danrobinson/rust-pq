import Integration.SlhDsaShakePermutationSparseCap
import Integration.SlhDsaShakePermutationWotsMachine

namespace Reduction.ShakePermutation.SparsePort.Wots
open Classical OracleComp OracleSpec SLHDSA SLHDSA.Security MLink SetOracle Phase PQ.Interactive
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
variable (S : Sha2Set)
abbrev Row := Bytes 32 × S.Node
def asArity : Row S ↪ Arity.Row S 1 where
  toFun j := (j.1,⟨[j.2],rfl⟩)
  inj' := by rintro ⟨a,m⟩ ⟨b,n⟩ e; exact Prod.ext (congrArg (fun j : Arity.Row S 1 => j.1) e) (List.cons.inj (congrArg (fun j => j.2.val) e)).1

def input (pk : S.Node) : Row S ↪ Words := (asArity S).trans (Arity.input S 1 pk (by decide))
local notation "N" => ShakeApi.rawCap S 67 65536

def fits (pk : S.Node) (d : Bytes 32) (xs : List S.Node) := (ShakeXof.thBytes S pk d xs).length ≤ N
instance (pk : S.Node) (d : Bytes 32) (xs : List S.Node) : Decidable (fits S pk d xs) := inferInstanceAs (Decidable (_ ≤ _))
def overflow := prefixBytes S.vp.params.n (default : Bytes S.vp.params.m)
def eval (pk : S.Node) (d : Bytes 32) (xs : List S.Node) : Select.Prog S.Node :=
  if fits S pk d xs then evalHash S pk d xs else pure (overflow S)
def value (f : Bytes 32 → Words → Words) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :=
  if fits S pk d xs then Select.value S f pk d xs else overflow S

theorem one_fits (pk : S.Node) (d : Bytes 32) (m : S.Node) : fits S pk d [m] := by
  exact (ShakeApi.in_range S 67 65536 N le_rfl).1 pk d [m] (by simp)

theorem value_real (π : Permutation) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :
    value S (fun _ => π) pk d xs =
      (ShakeApi.primitives S (ShakeApi.extend (SkCost.table S N (oracle π)))).Thash pk d xs := by
  unfold value
  split
  · rename_i yes
    change _ = prefixBytes S.vp.params.n (ShakeApi.extend (SkCost.table S N (oracle π)) (ShakeXof.thBytes S pk d xs))
    rw [Select.value_actual,SkCost.table,ShakeApi.extend_restrict _ _ _ _ yes,hash_prefix]
    change hash (lanes π) (nd pk ++ nd d ++ nds xs) _ = hash _ (sp (ShakeXof.thBytes S pk d xs)) _
    rw [Arity.fmt]; rfl
  · rename_i no
    change _ = prefixBytes _ (ShakeApi.extend (SkCost.table S N (oracle π)) (ShakeXof.thBytes S pk d xs))
    unfold fits at no
    rw [ShakeApi.extend,dite_eq_right no]; rfl

theorem eval_close (f : Bytes 32 → Words → Words) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :
    simulateQ (Select.close f) (eval S pk d xs) = pure (value S f pk d xs) := by
  by_cases h : fits S pk d xs <;> simp [eval,value,h,Select.close_hash]

private theorem valid_map {T J K A : Type} [DecidableEq T] (a : J ↪ Words) (e : K ↪ J) (tag : J → T)
    (p : OracleComp (Tagged T) A) (cert : valid a tag p) : valid (e.trans a) (tag ∘ e) p := by
  induction p using OracleComp.inductionOn with
  | pure x => trivial
  | query_bind t k ih =>
    rcases t with n|⟨d,w⟩
    · exact fun r => ih r (cert r)
    · exact ⟨fun j eq => cert.1 (e j) eq,fun y hy => ih y (cert.2 y hy)⟩

theorem eval_valid (pk : S.Node) (d : Bytes 32) (xs : List S.Node) : valid (input S pk) Prod.fst (eval S pk d xs) := by
  unfold eval
  split
  · exact valid_map _ (asArity S) Prod.fst _ (evalHash_valid S pk 1 (by decide) d xs)
  · trivial

private theorem absorb_cost (d : Bytes 32) (rs : List Rate) (w : Words) :
    WCount Select.wt (simulateQ erase (Phase.absorb d w rs)) rs.length := by
  induction rs generalizing w with
  | nil => simp [Phase.absorb,wCount_pure]
  | cons r rs ih =>
    simp only [Phase.absorb,simulateQ_bind,simulateQ_spec_query,erase,wCount_query_bind]
    exact ⟨by simp [Select.wt],fun y => by simpa [Select.wt] using ih y⟩

theorem eval_cost (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :
    WCount Select.wt (simulateQ erase (eval S pk d xs)) 483 := by
  unfold eval
  split
  · rename_i h
    have b : N ≤ 65632 := by cases S <;> decide +kernel
    have len : (messageBlocks (sp (ShakeXof.thBytes S pk d xs))).length ≤ 483 := by
      rw [messageBlocks_length]; simp only [sp,List.length_map]
      unfold fits at h; omega
    simp only [evalHash,simulateQ_bind,simulateQ_pure]
    exact (WCount.bind (absorb_cost _ _ _) (m:=0) (fun _ => wCount_pure _ _ _)).mono (by simpa using len)
  · simp only [simulateQ_pure]; trivial

theorem value_leaf (pk : S.Node) (π : Permutation) (s : Row S → SkFormat.Suffix S) (F : Row S → S.Node)
    (d : Bytes 32) (m : S.Node) :
    value S (shadow (SkFormat.split S) (input S pk) π s Prod.fst F) pk d [m] = F (d,m) := by
  rw [value,ite_eq_left (one_fits S pk d m)]
  unfold Select.value
  let j : Row S := (d,m)
  rw [show ShakeXof.thBytes S pk d [m] = Arity.data S 1 pk (asArity S j) from rfl,Arity.single _ _ _ _ (by decide)]
  simp only [List.foldl_cons,List.foldl_nil]
  have eq : join (rateXor (rateBlock (padded (sp (Arity.data S 1 pk (asArity S j)))) 0) (rateOf 0)) (capOf 0) = input S pk j := by
    apply congrArg₂ join _ rfl; funext i; exact UInt64.xor_zero
  rw [eq,shadow,ShakeXof.locate_emb]
  simp only [j,ite_true,target,Equiv.apply_symm_apply]

theorem value_local (pk : S.Node) (π : Permutation) (s : Row S → SkFormat.Suffix S) (F G : Row S → S.Node)
    (d : Bytes 32) (xs : List S.Node) (eq : ∀ m, F (d,m) = G (d,m)) :
    value S (shadow (SkFormat.split S) (input S pk) π s Prod.fst F) pk d xs =
    value S (shadow (SkFormat.split S) (input S pk) π s Prod.fst G) pk d xs := by
  have hh (j : Row S) (same : j.1 = d) : F j = G j := by rcases j with ⟨w,m⟩; change w = d at same; subst w; exact eq m
  simp only [value,Select.value,shadow_local _ _ _ _ Prod.fst F G d _ hh]

end
end Reduction.ShakePermutation.SparsePort.Wots
#print axioms Reduction.ShakePermutation.SparsePort.Wots.value_real
#print axioms Reduction.ShakePermutation.SparsePort.Wots.eval_cost
