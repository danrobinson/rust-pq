import Integration.SlhDsaShakePermutationShear
import Integration.SlhDsaSetClosed

/-! The rate-block change of coordinates between ordinary absorption (XOR) and
overwrite absorption, and its action on a uniform bounded table. This is the
finite-table version of Alagic, Carolan, Majenz and Tokat, Definition 5.2 and
Lemmas 5.5–5.6, https://arxiv.org/pdf/2504.16887. -/
namespace Reduction.ShakePermutation.Fix
open OracleComp OracleSpec PQ.Interactive ENNReal

/-- The first block enters an empty sponge with its rate unchanged. -/
def maskNext (f : List Rate → Rate) (past : List Rate) (x : Rate) : Rate :=
  if past.isEmpty then x else rateXor x (f past)

def fix (f : List Rate → Rate) (xs : List Rate) : List Rate :=
  xs.foldl (fun p x => p ++ [maskNext f p x]) []

@[simp] theorem fix_nil (f : List Rate → Rate) : fix f [] = [] := rfl
@[simp] theorem fix_append (f : List Rate → Rate) (xs : List Rate) (x : Rate) :
    fix f (xs ++ [x]) = fix f xs ++ [maskNext f (fix f xs) x] := by simp [fix]

@[simp] theorem fix_length (f : List Rate → Rate) (xs : List Rate) : (fix f xs).length = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [ih]

@[simp] theorem fix_empty (f : List Rate → Rate) (xs : List Rate) : (fix f xs).isEmpty = xs.isEmpty := by
  cases xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton => simp

def transform (f : List Rate → Rate) (xs : List Rate) : Rate := f (fix f xs)

theorem fix_left (f : List Rate → Rate) (xs : List Rate) : fix (transform f) (fix f xs) = xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [fix_append,ih,maskNext,fix_empty,transform]
    cases xs.isEmpty <;> simp

theorem fix_right (f : List Rate → Rate) (xs : List Rate) : fix f (fix (transform f) xs) = xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [fix_append,ih,maskNext,fix_empty,transform]
    cases xs.isEmpty <;> simp_all

def fixEquiv (f : List Rate → Rate) : Equiv.Perm (List Rate) :=
  ⟨fix f,fix (transform f),fix_left f,fix_right f⟩

@[simp] theorem transform_twice (f : List Rate → Rate) : transform (transform f) = f :=
  funext fun xs => congrArg f (fix_right f xs)

/-- Absorb rate blocks with ordinary XOR, starting from zero lanes. -/
def ordinary (π : Permutation) (xs : List Rate) : Words :=
  xs.foldl (fun s x => π (join (rateXor x (rateOf s)) (capOf s))) 0

/-- Absorb rate blocks by overwriting the rate, keeping the capacity. -/
def overwrite (π : Permutation) (xs : List Rate) : Words :=
  xs.foldl (fun s x => π (join x (capOf s))) 0

/-- Fixing inputs preserves the entire state after every prefix, including
the capacity used by the next permutation round. -/
theorem fixed_absorption (π : Permutation) (xs : List Rate) :
    ordinary π xs = overwrite π (fix (rateOf ∘ overwrite π) xs) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [fix_append]
    simp only [ordinary,overwrite,List.foldl_append,List.foldl_cons,List.foldl_nil] at ⊢
    change π (join (rateXor x (rateOf (ordinary π xs))) (capOf (ordinary π xs))) = _
    change _ = π (join (maskNext (rateOf ∘ overwrite π) (fix (rateOf ∘ overwrite π) xs) x)
      (capOf (overwrite π (fix (rateOf ∘ overwrite π) xs))))
    rw [ih]
    cases xs using List.reverseRecOn with
    | nil =>
      congr 2
      funext i
      simp [rateXor,rateOf,overwrite,maskNext]
    | append_singleton => simp [maskNext]

abbrev Domain (L : ℕ) := BList Rate L
abbrev Table (L : ℕ) := Domain L → Rate

def extend {L : ℕ} (f : Table L) (xs : List Rate) : Rate :=
  if h : xs.length ≤ L then f (BList.ofList xs h) else 0

def liftBounded {L : ℕ} (f : Table L) (x : Domain L) : Domain L :=
  BList.ofList (fix (extend f) (List.ofFn x.2)) (by simp; omega)

def tableMap {L : ℕ} (f : Table L) : Table L := f ∘ liftBounded f

theorem extend_map {L : ℕ} (f : Table L) : extend (tableMap f) = transform (extend f) := by
  funext xs
  by_cases h : xs.length ≤ L
  · have hh : (fix (extend f) xs).length ≤ L := by simpa using h
    simp only [transform,extend, dite_eq_left h, dite_eq_left hh,tableMap,Function.comp_apply,liftBounded,BList.ofFn_ofList]
  · simp [transform,extend,h]

theorem table_involution {L : ℕ} : Function.Involutive (tableMap (L := L)) := by
  intro f
  funext x
  have hx : (List.ofFn x.2).length ≤ L := by simp; omega
  have atInput (g : Table L) : extend g (List.ofFn x.2) = g x := by
    rw [extend,dite_eq_left hx,BList.ofList_ofFn]
  rw [← atInput (tableMap (tableMap f)),extend_map,extend_map,transform_twice,atInput]

/-- The full induced table retains the uniform law. This allows any experiment
on its values, including coherent queries. -/
theorem uniform_transform (L : ℕ) (w : Table L → ℝ≥0∞) :
    SetOracle.uniformMean (fun h => w (tableMap h)) = SetOracle.uniformMean w := by
  exact Equiv.sum_comp (Function.Involutive.toPerm tableMap table_involution)
    (fun h => unifW _ h * w h)

end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.uniform_transform
#print axioms Reduction.ShakePermutation.Fix.fixed_absorption
