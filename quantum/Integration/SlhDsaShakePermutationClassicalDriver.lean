import Integration.SlhDsaShakePermutationClassicalCoefficient
import Integration.SlhDsaShakePermutationClassicalPaths
import Integration.SlhDsaShakePermutationAccess

/-! Label each private sponge round by its message prefix. The public
permutation simulator keeps its own edge transcript, which is untouched
by private hash queries. -/
namespace Reduction.ShakePermutation.Classic
open OracleSpec OracleComp Classical SLHDSA MLink
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
abbrev Row (T : ℕ) := Fix.Domain T ⊕ Port
def rowId (T : ℕ) (p : List Rate) : Row T :=
  Sum.inl (if h : p.length ≤ T then BList.ofList p h else BList.ofList [] (by simp))

def ask {T : ℕ} (j : Row T) (d : Bool) (x : Words) : OracleComp (Tagged (Row T) Words) Words :=
  (Tagged (Row T) Words).query (.inr (j,d,x))

def absorb (T : ℕ) (p : List Rate) (w : Words) : List Rate → OracleComp (Tagged (Row T) Words) Words
  | [] => pure w
  | r::rs => do
    let s ← ask (rowId T (p ++ [r])) false (join (rateXor r (rateOf w)) (capOf w))
    absorb T (p ++ [r]) s rs

def rootAt (t : EdgeTrace Words) (c : Capacity) := ∃ p : List Rate, ∃ s : Words, Trail t p s ∧ capOf s = c

def publicRow (T : ℕ) (t : EdgeTrace Words) (d : Bool) (x : Words) : Row T :=
  if d then Sum.inr (true,x)
  else if h : rootAt t (capOf x) then
    rowId T (h.choose ++ [nextBlock h.choose_spec.choose x])
  else Sum.inr (false,x)

def publicStep (T : ℕ) (t : EdgeTrace Words) (d : Bool) (x : Words) :
    OracleComp (Tagged (Row T) Words) (Words × EdgeTrace Words) :=
  if h : old t d x then pure (h.choose,t)
  else ask (publicRow T t d x) d x >>= fun y => pure (y,edge d x y::t)

abbrev Outer (S : Sha2Set) (N : ℕ) := unifSpec + ((Port →ₒ Words) + (ShakeApi.Input N →ₒ Bytes S.vp.params.m))

def driver (S : Sha2Set) (N T : ℕ) {Z : Type} (P : OracleComp (Outer S N) Z) :
    EdgeTrace Words → OracleComp (Tagged (Row T) Words) Z :=
  OracleComp.construct (C := fun _ => EdgeTrace Words → OracleComp (Tagged (Row T) Words) Z)
    (fun z _ => pure z) (fun i _ k t => match i with
      | .inl n => (Tagged (Row T) Words).query (.inl n) >>= fun v => k v t
      | .inr (.inl (d,x)) => publicStep T t d x >>= fun z => k z.1 z.2
      | .inr (.inr x) => absorb T [] 0 (messageBlocks (sp (List.ofFn x.2))) >>= fun s =>
          k (ShakeXof.head (output_sizes S).2 (Completion.bytes (rateOf s))) t) P

def labelled {I A Z : Type} [Fintype A] (H : I → Bool → A → A) (ev : Z → ℝ≥0∞) (P : OracleComp (Tagged I A) Z) : ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℝ≥0∞) ev (fun i _ k => match i with
    | .inl _ => uniformMean k
    | .inr (j,d,x) => k (H j d x)) P

theorem labelled_bind {I A Z V : Type} [Fintype A] (H : I → Bool → A → A) (ev : V → ℝ≥0∞)
    (P : OracleComp (Tagged I A) Z) (k : Z → OracleComp (Tagged I A) V) :
    labelled H ev (P >>= k) = labelled H (fun z => labelled H ev (k z)) P := by
  induction P using OracleComp.inductionOn with
  | pure => simp only [pure_bind]; rfl
  | query_bind i f ih =>
    rw [bind_assoc]
    rcases i with n|⟨j,d,x⟩
    · exact congrArg uniformMean (funext ih)
    · exact ih _

theorem labelled_forget {I A Z : Type} [Fintype A] (π : Equiv.Perm A) (ev : Z → ℝ≥0∞)
    (P : OracleComp (Tagged I A) Z) :
    eager π ev (simulateQ forgetTag P) = labelled (fun _ => call π) ev P := by
  induction P using OracleComp.inductionOn with
  | pure => rfl
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    rcases i with n|⟨j,d,x⟩
    · exact congrArg uniformMean (funext ih)
    · exact ih _

theorem absorb_real (T : ℕ) (π : Permutation) (ev : Words → ℝ≥0∞) (xs p : List Rate) (w : Words) :
    labelled (fun _ : Row T => call π) ev (absorb T p w xs) =
    ev (xs.foldl (fun s r => π (join (rateXor r (rateOf s)) (capOf s))) w) := by
  induction xs generalizing w p with
  | nil => rfl
  | cons r rs ih =>
    rw [absorb,labelled_bind]
    exact ih _ _

def bankState (T : ℕ) (H : Row T → Words) (p : List Rate) : Words :=
  if p.isEmpty then 0 else H (rowId T p)

theorem absorb_ideal (T : ℕ) (H : Row T → Words) (ev : Words → ℝ≥0∞) (xs p : List Rate) :
    labelled (fun j _ _ => H j) ev (absorb T p (bankState T H p) xs) =
    ev (bankState T H (p ++ xs)) := by
  induction xs generalizing p with
  | nil => simp only [absorb,List.append_nil]; rfl
  | cons r rs ih =>
    rw [absorb,labelled_bind]
    have e : bankState T H (p++[r]) = H (rowId T (p++[r])) := by simp [bankState]
    change labelled _ _ (absorb T (p++[r]) (H (rowId T (p++[r]))) rs) = _
    rw [← e,ih]
    simp

def realOuter (S : Sha2Set) (N : ℕ) {Z : Type} (π : Permutation) (ev : Z → ℝ≥0∞)
    (P : OracleComp (Outer S N) Z) : ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℝ≥0∞) ev (fun i _ k => match i with
    | .inl _ => uniformMean k
    | .inr (.inl x) => k (oracle π x)
    | .inr (.inr x) => k (answer S (lanes π) (List.ofFn x.2))) P

def Respects (π : Permutation) (t : EdgeTrace Words) := ∀ a ∈ t, π a.1 = a.2

theorem edge_respects (π : Permutation) (t : EdgeTrace Words) (ok : Respects π t) (d : Bool) (x : Words) :
    Respects π (edge d x (call π d x)::t) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl|ha
  · cases d <;> simp [edge,call]
  · exact ok _ ha

theorem old_real (π : Permutation) (t : EdgeTrace Words) (ok : Respects π t) (d : Bool) (x : Words) (h : old t d x) :
    call π d x = h.choose := by
  have e := h.choose_spec
  cases d with
  | false => exact ok _ e
  | true =>
    obtain ⟨⟨a,b⟩,he,hp⟩ := List.mem_map.mp e
    obtain ⟨e₁,e₂⟩ := Prod.mk.inj hp
    exact π.symm_apply_eq.mpr (e₁.symm.trans ((ok _ he).symm.trans (congrArg π e₂)))

theorem driver_real (S : Sha2Set) (N T : ℕ) {Z : Type} (π : Permutation) (ev : Z → ℝ≥0∞)
    (P : OracleComp (Outer S N) Z) (t : EdgeTrace Words) (ok : Respects π t) :
    labelled (fun _ : Row T => call π) ev (driver S N T P t) = realOuter S N π ev P := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩|x
    · change labelled _ _ (_ >>= _) = _
      rw [labelled_bind]
      exact congrArg uniformMean (funext fun r => ih r t ok)
    · change labelled _ _ (publicStep T t d x >>= _) = _
      rw [labelled_bind,publicStep]
      split
      · rename_i h
        change labelled _ _ (driver S N T (k h.choose) t) = realOuter S N π ev (k (call π d x))
        rw [← old_real π t ok d x h]
        exact ih _ t ok
      · change labelled _ _ (ask _ d x >>= _) = _
        rw [labelled_bind]
        exact ih _ _ (edge_respects π t ok d x)
    · change labelled _ _ (absorb T [] 0 _ >>= _) = _
      rw [labelled_bind,absorb_real]
      change labelled _ _ (driver S N T (k _) t) = realOuter S N π ev (k (answer S _ _))
      rw [answer_blocks]
      exact ih _ t ok

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.driver_real
#print axioms Reduction.ShakePermutation.Classic.absorb_ideal
