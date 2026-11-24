import Integration.SlhDsaShakeAdaptiveRows

/-! SHAKE ITSR honest hash support at each target phase. The table supplying
the public quantum port can change at future target rows. Key generation and
signing touch only the public seed and the supplied signing salt as prefixes. -/

namespace Reduction.ShakeAdaptive
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg
open scoped ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

section Support
variable {vp : ValidatedParams} (P : Primitives vp.params) {ι : Type} (G : OracleSpec ι)

/-- Honest public hashes in the open lazy scheme. Game, secret-cache and
sampling operations remain unrestricted. -/
def honestPrefix (seed : P.PkSeed) (salt : P.Y → Prop) : (Lazy.OSpec P G).Domain → Prop
  | .inr (.inr (.inr (.thash pk _ _))) => pk = seed
  | .inr (.inr (.inr (.hmsg r pk _ _))) => pk = seed ∧ salt r
  | _ => True

theorem keygen_prefix (seed : P.PkSeed) :
    AllQueries (honestPrefix P G seed (fun _ => False)) (fun _ => True)
      (Lazy.openKeygen P G seed) := by
  unfold Lazy.openKeygen
  apply keygenInternalWithSecretM_pred_of_ledger
    (m := OracleComp (Lazy.OSpec P G)) (fun {α} oa => AllQueries _ (fun _ : α => True) oa)
    (fun _ => trivial) (fun _ _ h1 h2 => allQ_bind h1 fun a _ => h2 a) P.core
  · exact fun a _ _ _ => allQ_query _ _ trivial
  · exact fun a _ xs => allQ_query _ _ rfl

theorem sign_prefix (msg : List SLHDSA.Byte) (seed : P.PkSeed) (root R : P.Y) :
    AllQueries (honestPrefix P G seed (· = R)) (fun _ => True)
      (Lazy.openSign P G msg seed root R) := by
  unfold Lazy.openSign
  apply signInternalWithSecretRandomizerM_pred_of_ledger
    (m := OracleComp (Lazy.OSpec P G)) (fun {α} oa => AllQueries _ (fun _ : α => True) oa)
    (fun _ => trivial) (fun _ _ h1 h2 => allQ_bind h1 fun a _ => h2 a) P.core
  · exact fun a _ _ _ => allQ_query _ _ trivial
  · exact fun a _ xs => allQ_query _ _ rfl
  · exact allQ_query _ _ ⟨rfl,rfl⟩

end Support

open Classical

/-- At a fixed independently sampled public seed, the probability that any
of the potential target salts equals it is at most s divided by the row count. -/
theorem seed_collision {K : Type} [Fintype K] [DecidableEq K] (s : ℕ) (seed : K) :
    (avg fun Rs : Fin s → K => if issued Rs s seed then (1 : ℝ≥0∞) else 0) ≤
      s / (Fintype.card K : ℝ≥0∞) := by
  classical
  let : Nonempty K := ⟨seed⟩
  have count (Rs : Fin s → K) : (if issued Rs s seed then (1 : ℝ≥0∞) else 0) ≤
      ∑ j, (if Rs j = seed then (1 : ℝ≥0∞) else 0) := by
    split_ifs with h
    · obtain ⟨j,_,hj⟩ := h
      have bound := Finset.single_le_sum (f := fun j => if Rs j = seed then (1 : ℝ≥0∞) else 0)
        (fun _ _ => zero_le) (Finset.mem_univ j)
      simpa [hj] using bound
    · exact zero_le
  refine (avg_mono count).trans ?_
  rw [avg_finset_sum]
  simp_rw [avg_coord_eq _ _ (fun _ => 1) (fun _ _ => rfl),avg_const,mul_one]
  simp [div_eq_mul_inv]

/-- The entire exceptional tape event, including repeated target salts. Both
conditions hold uniformly over the independent key-generation seed law. -/
theorem bad_tape {K : Type} [Fintype K] [DecidableEq K] (s : ℕ) (seed : K) :
    (avg fun Rs : Fin s → K => if Function.Injective Rs ∧ ¬issued Rs s seed then
      (0 : ℝ≥0∞) else 1) ≤ (s.choose 2 + s : ℕ) / (Fintype.card K : ℝ≥0∞) := by
  classical
  have split (Rs : Fin s → K) :
      (if Function.Injective Rs ∧ ¬issued Rs s seed then (0 : ℝ≥0∞) else 1) ≤
        (if Function.Injective Rs then 0 else 1) + (if issued Rs s seed then 1 else 0) := by
    by_cases inj : Function.Injective Rs <;> by_cases hit : issued Rs s seed <;> simp [*]
  apply (avg_mono split).trans
  rw [avg_add, Nat.cast_add, div_eq_mul_inv, add_mul]
  simpa only [div_eq_mul_inv] using add_le_add (avg_not_injective_le_choose s) (seed_collision s seed)

theorem bad_tape_192 {K : Type} [Fintype K] [DecidableEq K] (size : Fintype.card K = 2^192)
    (seed : K) :
    (avg fun Rs : Fin (2^64) → K => if Function.Injective Rs ∧ ¬issued Rs (2^64) seed then
      (0 : ℝ≥0∞) else 1) ≤ (2^64 : ℝ≥0∞)⁻¹ := by
  apply (bad_tape (2^64) seed).trans
  rw [size, Nat.choose_two_right]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  norm_num

variable (S : Sha2Set) (c : Caps) {N s : ℕ} (cap : 3*S.vp.params.n+c.ml ≤ N)
    (g : ShakeApi.RawTable S N) (Rs : Fin s → S.Node)
    (Φ : (Row S c × Bool) → Bytes S.vp.params.m)

/-- The row embedding preserves the leading node of every encoded bounded
raw input. Agreement on that row suffices for every possible suffix. -/
theorem prefix_of_rows (f h : Row S c → Bytes S.vp.params.m) (lead : S.Node)
    (tail : List SLHDSA.Byte) (agree : ∀ z : Row S c, z.1 = lead → f z = h z) :
    ShakeApi.extend (ShakeXof.write (embedding S c cap) g f) (lead.toList ++ tail) =
      ShakeApi.extend (ShakeXof.write (embedding S c cap) g h) (lead.toList ++ tail) := by
  classical
  by_cases hcap : (lead.toList ++ tail).length ≤ N
  · rw [ShakeApi.extend_apply _ _ hcap, ShakeApi.extend_apply _ _ hcap]
    apply ShakeXof.local_at
    intro j located
    have e := congrArg (fun x : ShakeApi.Input N => List.ofFn x.2)
      (ShakeXof.located (embedding S c cap) located)
    have fits : (ShakeSingle.encode S (expand S c j)).length ≤ N := by
      simp only [ShakeSingle.encode,expand,List.length_append,Vector.length_toList,List.length_ofFn]
      have := j.2.2.2.1.isLt
      omega
    change List.ofFn (BList.ofList (ShakeSingle.encode S (expand S c j)) fits).2 =
      List.ofFn (BList.ofList (lead.toList ++ tail) hcap).2 at e
    have raw := (BList.ofFn_ofList _ fits).symm.trans (e.trans (BList.ofFn_ofList _ hcap))
    change j.1.toList ++ _ = lead.toList ++ tail at raw
    have first : j.1 = lead := Vector.toList_inj.mp ((List.append_inj raw (by simp)).1)
    exact agree j first
  · simp only [ShakeApi.extend,dite_eq_right hcap]

/-- Preload the current-phase public hashes into the honest interpreter. On
admissible inputs the entire probabilistic computation, including its final
secret cache, agrees with the final-table computation at every starting cache. -/
theorem lazy_eq_of_rows (base : ShakeApi.Xof S) {ι α : Type} (G : OracleSpec ι)
    (seed : S.Node) (allow : S.Node → Prop) (f h : Row S c → Bytes S.vp.params.m)
    (same : ∀ z : Row S c, z.1 = seed ∨ allow z.1 → f z = h z)
    (P : OracleComp (Lazy.OSpec (ShakeApi.primitives S base) G) α)
    (scope : AllQueries (honestPrefix (ShakeApi.primitives S base) G seed allow)
      (fun _ => True) P) :
    simulateQ (Lazy.lazyImpl (gspec := G)
      (ShakeApi.hashPort S N base (ShakeXof.write (embedding S c cap) g f))) P =
    simulateQ (Lazy.lazyImpl (gspec := G)
      (ShakeApi.hashPort S N base (ShakeXof.write (embedding S c cap) g h))) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases scope with ⟨ok, rest⟩
    simp only [simulateQ_bind, simulateQ_spec_query, funext (fun r => ih r (rest r))]
    congr 1
    rcases t with n | tgt | secret | t
    · rfl
    · rfl
    · rfl
    · cases t with
      | thash pk a xs =>
        change pk = seed at ok
        subst pk
        apply congrArg Pure.pure
        change prefixBytes _ (ShakeApi.extend _ _) = prefixBytes _ (ShakeApi.extend _ _)
        apply congrArg
        simp only [List.append_assoc]
        apply prefix_of_rows S c cap g f h seed
        exact fun z hz => same z (Or.inl hz)
      | hmsg r pk root msg =>
        change _ ∧ allow r at ok
        apply congrArg Pure.pure
        change ShakeApi.extend _ _ = ShakeApi.extend _ _
        simp only [List.append_assoc]
        apply prefix_of_rows S c cap g f h r
        exact fun z hz => same z (Or.inr (hz ▸ ok.2))

/-- The final last-issuance table and the current-phase table of the coverage
hybrid agree on every admissible honest row, whenever the salt tape has no
repetition and the public seed is absent. -/
theorem nFn_honest_rows (Ψ : Row S c × Option (Fin s) → Bytes S.vp.params.m) (m : ℕ)
    (seed : S.Node) (goodSeed : ¬issued Rs s seed) (injective : Function.Injective Rs)
    (z : Row S c) (ok : z.1 = seed ∨ issued Rs m z.1) :
    nFn Rs Ψ s z = nFn Rs Ψ m z := by
  apply congrArg (fun i => Ψ (z,i))
  by_contra different
  obtain ⟨j,hj,equal⟩ := lastIdx_ne different
  rcases ok with h | ⟨i,hi,ei⟩
  · exact goodSeed ⟨j,j.isLt,equal.trans h⟩
  · have same := injective (equal.trans ei.symm)
    subst i
    omega

/-- In the two-bank reprogramming hybrid, an issued prefix never changes
again, even for a repeated salt. -/
theorem mpFn_honest_rows (m : ℕ) (seed : S.Node) (goodSeed : ¬issued Rs s seed)
    (z : Row S c) (ok : z.1 = seed ∨ issued Rs m z.1) :
    mpFn Rs Φ s z = mpFn Rs Φ m z := by
  have eq : issued Rs s z.1 ↔ issued Rs m z.1 := by
    constructor
    · intro h
      rcases ok with e | hm
      · exact (goodSeed (e ▸ h)).elim
      · exact hm
    · rintro ⟨i,_,hi⟩
      exact ⟨i,i.isLt,hi⟩
  simp [mpFn,eq]

variable (base : ShakeApi.Xof S) (Ψ : Row S c × Option (Fin s) → Bytes S.vp.params.m)
local notation "pr" => ShakeApi.primitives S base
local notation "game" => Lazy.itsrG pr
local notation "handler" => fun l : ℕ => Lazy.lazyImpl (gspec := game) (D := SecIdx) (V := S.Node)
  (ShakeApi.hashPort S N base (ShakeXof.write (embedding S c cap) g (nFn Rs Ψ l)))

theorem keygen_phase (seed : S.Node) (goodSeed : ¬issued Rs s seed) (inj : Function.Injective Rs) :
    simulateQ (handler s) (Lazy.openKeygen pr game seed) =
      simulateQ (handler 0) (Lazy.openKeygen pr game seed) := by
  apply lazy_eq_of_rows S c cap g base game seed (fun _ => False) _ _ _ _ (keygen_prefix pr game seed)
  intro z hz
  exact nFn_honest_rows S c Rs Ψ 0 seed goodSeed inj z (Or.inl (hz.resolve_right id))

theorem sign_phase (m : ℕ) (seed root R : S.Node) (msg : List SLHDSA.Byte)
    (goodSeed : ¬issued Rs s seed) (inj : Function.Injective Rs) (old : issued Rs m R) :
    simulateQ (handler s) (Lazy.openSign pr game msg seed root R) =
      simulateQ (handler m) (Lazy.openSign pr game msg seed root R) := by
  apply lazy_eq_of_rows S c cap g base game seed (· = R) _ _ _ _ (sign_prefix pr game msg seed root R)
  intro z hz
  apply nFn_honest_rows S c Rs Ψ m seed goodSeed inj z
  rcases hz with h | h
  · exact Or.inl h
  · change z.1 = R at h
    exact Or.inr (h ▸ old)

/-- On a cache hit the actual ITSR randomizer returns a previously logged
salt. A miss requests a new salt from the target oracle. -/
theorem randomizer_source (seed root addrnd : S.Node) (msg : List SLHDSA.Byte) (log : G2Log pr)
    (phase : ℕ) (history : ∀ e ∈ log, issued Rs phase e.2.2) :
    (∃ R : S.Node, issued Rs phase R ∧
      Lazy.itsrRandomizerO (prims := pr) seed root log msg addrnd = pure R) ∨
      Lazy.itsrRandomizerO (prims := pr) seed root log msg addrnd = Lazy.gameQ pr game (seed,root,msg) := by
  unfold Lazy.itsrRandomizerO
  cases h : log.find? _ with
  | none => exact Or.inr rfl
  | some entry => exact Or.inl ⟨_,history entry (List.mem_of_find?_eq_some h),rfl⟩

end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.keygen_prefix
#print axioms Reduction.ShakeAdaptive.sign_prefix
#print axioms Reduction.ShakeAdaptive.seed_collision
#print axioms Reduction.ShakeAdaptive.prefix_of_rows
#print axioms Reduction.ShakeAdaptive.lazy_eq_of_rows
#print axioms Reduction.ShakeAdaptive.nFn_honest_rows
#print axioms Reduction.ShakeAdaptive.mpFn_honest_rows
#print axioms Reduction.ShakeAdaptive.keygen_phase
#print axioms Reduction.ShakeAdaptive.sign_phase
#print axioms Reduction.ShakeAdaptive.randomizer_source
#print axioms Reduction.ShakeAdaptive.bad_tape_192
