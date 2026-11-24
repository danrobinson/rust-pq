import Integration.SlhDsaCompressionQuantum
import Integration.SlhDsaSetPrf
import MIdeal.SkPrf

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker
variable (S : Sha2Set)

abbrev AddressInput := St × Bytes 22
abbrev Rows := S.Node × AddressInput → St

/-- Locations of the final SHA-256 call with the secret bytes placed after the address. -/
def location : S.Node × AddressInput → St × Blk :=
  fun (key,st,a) => (st, MIdeal.SkPrf.singletonBlock S a key)

theorem location_injective : Function.Injective (location S) := by
  rintro ⟨k,s,a⟩ ⟨l,t,b⟩ h
  obtain ⟨rfl, e⟩ := Prod.mk.inj h
  have he := congrArg Vector.toList e
  change _ ++ tailL _ = _ ++ tailL _ at he
  obtain ⟨ea,ek⟩ := List.append_inj (List.append_cancel_right he) (by simp)
  rw [Vector.toList_inj.mp ea, Vector.toList_inj.mp ek]

private noncomputable def readLocation (i : St × Blk) : Option (S.Node × AddressInput) := by
  classical
  exact if h : ∃ p, location S p = i then some h.choose else none

private theorem read_at (p : S.Node × AddressInput) :
    readLocation S (location S p) = some p := by
  classical
  unfold readLocation
  rw [dite_eq_left (show ∃ x, location S x = location S p from ⟨p,rfl⟩)]
  congr 1
  exact location_injective S (Exists.choose_spec (show ∃ x, location S x = location S p from ⟨p,rfl⟩))

def readRows (g : CompressionTables) : Rows S := fun p => g.1 (location S p)

noncomputable def withRows (g : CompressionTables) (r : Rows S) : CompressionTables :=
  (fun i => (readLocation S i).elim (g.1 i) r, g.2)

private theorem swap_rows : Function.Involutive
    (fun z : CompressionTables × Rows S => (withRows S z.1 z.2, readRows S z.1)) := by
  rintro ⟨⟨g,h⟩,r⟩
  apply Prod.ext
  · refine Prod.ext ?_ rfl
    funext i
    change (readLocation S i).elim _ (readRows S (g,h)) = _
    classical
    unfold readLocation
    split_ifs with hm
    · exact congrArg g hm.choose_spec
    · simp only [Option.elim_none, withRows, readLocation, dite_eq_right hm]
  · funext p
    change (readLocation S (location S p)).elim _ r = _
    rw [read_at]; rfl

private noncomputable def portLocation : Input → Option (S.Node × AddressInput)
  | .inl i => readLocation S i
  | .inr _ => none

private theorem local_port (g : CompressionTables) (r t : Rows S) (x : Input)
    (h : ∀ p, portLocation S x = some p → r p = t p) :
    oracle (withRows S g r) x = oracle (withRows S g t) x := by
  rcases x with i|i
  · change ((readLocation S i).elim _ r, _) = ((readLocation S i).elim _ t, _)
    cases e : readLocation S i with
    | none => rfl
    | some p => exact congrArg (fun v => (v,0)) (h p e)
  · rfl

/-- Full-state PRF for the secret-bearing compression call. Its input is the
already-computed chaining state and the 22 address bytes. -/
noncomputable def terminalScheme (g : CompressionTables) := keyedScheme id (readRows S g)

theorem node_card_real : (Fintype.card S.Node : ℝ) = 2^(8*S.vp.params.n) := by
  rw [card_bytes', Nat.cast_pow, Nat.cast_ofNat, pow_mul]; norm_num

theorem column_prf {K : Type} [Fintype K] [DecidableEq K] [SampleableType K] [Nonempty K]
    {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (loc : Input → Option (K × X)) {R : Type} [Fintype R] [DecidableEq R] [SampleableType R] [Nonempty R]
    (put : CompressionTables → (K × X → R) → CompressionTables)
    (read : CompressionTables → K × X → R)
    (swap : Function.Involutive (fun z : CompressionTables × (K × X → R) => (put z.1 z.2,read z.1)))
    (he : ∀ g r, read (put g r) = r)
    (locality : ∀ g r t x, (∀ p, loc x = some p → r p = t p) → oracle (put g r) x = oracle (put g t) x)
    {D : Type} [DecidableEq D]
    (address : CompressionTables → D → X)
    (inj : ∀ g, Function.Injective (address g))
    (outside : ∀ g r, address (put g r) = address g)
    {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec D R) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (keyedScheme (address g) (read g)) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K) := by
  let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
  have hr (g : CompressionTables) := prf_answer_real_le_ideal_add (K := K) (Dm := X)
    (address g) (inj g) A q hA (fun r => oracle (put g r)) loc (locality g) ρ
  rw [SetOracle.avg_resample (put) (read) swap
    (fun g => qPrfRealPr (keyedScheme (address g) (read g)) (A (oracle g)) M)]
  rw [SetOracle.avg_resample (put) (read) swap
    (fun g => qPrfIdealPr (A (oracle g)) M)]
  simp only [he, outside]
  calc _ ≤ ∑ g : CompressionTables, unifW _ g * (_ + ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K)) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hr g)
       _ = _ := by
         simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]
         rfl
private theorem terminal_prf_at {D : Type} [DecidableEq D]
    (address : CompressionTables → D → AddressInput)
    (inj : ∀ g, Function.Injective (address g))
    (outside : ∀ g r, address (withRows S g r) = address g)
    {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec D St) Bool)
    (q : ℕ) (hA : PU A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (keyedScheme (address g) (readRows S g)) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  rw [← node_card_real S]
  apply column_prf (portLocation S) (withRows S) (readRows S) (swap_rows S) _ (local_port S) address inj outside A q hA.toPUE.prfAnswerCost ρ
  intro g r
  funext p
  change (readLocation S (location S p)).elim _ r = _
  rw [read_at]; rfl

/-- Against quantum access to both sampled compression tables, replacing the
secret-bearing call by a lazy random function on (chaining state, address) costs
at most 8 q²/2^(8n). This theorem allows classical requests for the full state. -/
theorem terminal_prf {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec AddressInput St) Bool)
    (q : ℕ) (hA : PU A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (terminalScheme S g) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) :=
  terminal_prf_at S (fun _ => id) (fun _ => Function.injective_id) (fun _ _ => rfl) A q hA ρ


def seedAddress (g : CompressionTables) (pk : S.Node) (a : Bytes 22) : AddressInput :=
  (g.1 (IV128,MIdeal.SkPrf.seedBlock S pk),a)

private theorem seed_outside (pk : S.Node) : readLocation S (IV128,MIdeal.SkPrf.seedBlock S pk) = none := by
  classical
  unfold readLocation
  apply dite_eq_right
  rintro ⟨⟨k,st,a⟩,h⟩
  exact MIdeal.SkPrf.seed_ne_singleton S pk a k (congrArg Prod.snd h).symm

/-- Fixing the public seed permits all addresses to share its actual first
compression value. The challenger returns the full terminal SHA-256 state. -/
theorem fixed_seed_prf (pk : S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (Bytes 22) St) Bool)
    (q : ℕ) (hA : PU A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (keyedScheme (seedAddress S g pk) (readRows S g))
      (A (oracle g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  apply terminal_prf_at S (fun g => seedAddress S g pk) (fun _ _ _ h => congrArg Prod.snd h) _ A q hA ρ
  intro g r
  funext a
  simp only [seedAddress, withRows, seed_outside, Option.elim_none]

/-- Truncating the fixed-seed challenger's full response gives exactly the
standardized address PRF at every permitted address. -/
theorem fixed_seed_eval (g : CompressionTables) (pk key : S.Node) (a : SkAdrs S.vp) :
    MIdeal.SkPrf.output S ((keyedScheme (seedAddress S g pk) (readRows S g)).eval key (Concrete.sha2AdrsKey a.val)) =
      (tablePrimitives g S.vp.params).PRF pk key a.val :=
  (MIdeal.SkPrf.mixed_shape S g pk key a).symm

def setPrefix (st : St) (out : S.Node) : St :=
  Vector.ofFn fun i => if h : i.val < S.vp.params.n then out[i.val]'h else st[i.val]

theorem read_prefix (st : St) (out : S.Node) : MIdeal.SkPrf.output S (setPrefix S st out) = out := by
  ext i hi; simp [MIdeal.SkPrf.output, setPrefix, hi]

theorem undo_prefix (st : St) (out : S.Node) :
    setPrefix S (setPrefix S st out) (MIdeal.SkPrf.output S st) = st := by
  ext i hi; by_cases h : i < S.vp.params.n <;> simp [setPrefix, MIdeal.SkPrf.output, h]

private def outputs (g : CompressionTables) (p : S.Node × AddressInput) := MIdeal.SkPrf.output S (readRows S g p)

private noncomputable def withOutputs (g : CompressionTables) (r : S.Node × AddressInput → S.Node) :=
  withRows S g fun p => setPrefix S (readRows S g p) (r p)

private theorem read_set (g : CompressionTables) (r : S.Node × AddressInput → S.Node) (p : S.Node × AddressInput) :
    readRows S (withOutputs S g r) p = setPrefix S (readRows S g p) (r p) := by
  change (readLocation S (location S p)).elim _ _ = _
  rw [read_at]; rfl

private theorem swap_outputs : Function.Involutive
    (fun z : CompressionTables × (S.Node × AddressInput → S.Node) => (withOutputs S z.1 z.2,outputs S z.1)) := by
  rintro ⟨g,r⟩
  refine Prod.ext (Prod.ext ?_ rfl) ?_
  · funext i
    change (withOutputs S (withOutputs S g r) (outputs S g)).1 i = g.1 i
    classical
    by_cases h : ∃ p, location S p = i
    · obtain ⟨p,rfl⟩ := h
      change readRows S (withOutputs S (withOutputs S g r) (outputs S g)) p = readRows S g p
      rw [read_set, read_set, outputs, undo_prefix]
    · simp only [withOutputs, withRows, readLocation, dite_eq_right h, Option.elim_none]
  · funext p
    exact (congrArg (MIdeal.SkPrf.output S) (read_set S g r p)).trans (read_prefix S _ _)

noncomputable def addressScheme (g : CompressionTables) (pk : S.Node) : PRFScheme S.Node (SkAdrs S.vp) S.Node :=
  ⟨$ᵗ S.Node, fun k a => (tablePrimitives g S.vp.params).PRF pk k a.val⟩

/-- Exact fixed-public-seed PRF from the scheme, including the address check and
digest truncation. Both public compression functions are accessible in superposition. -/
theorem address_prf_answer (pk : S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (addressScheme S g pk)
      (A (oracle g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  let address (g : CompressionTables) (a : SkAdrs S.vp) := seedAddress S g pk (Concrete.sha2AdrsKey a.val)
  have eq (g) : addressScheme S g pk = keyedScheme (address g) (outputs S g) := by
    apply congrArg (fun f => (⟨$ᵗ S.Node,f⟩ : PRFScheme S.Node (SkAdrs S.vp) S.Node))
    funext k a
    exact (fixed_seed_eval S g pk k a).symm
  simp_rw [eq]
  rw [← node_card_real S]
  apply column_prf (portLocation S) (withOutputs S) (outputs S) (swap_outputs S) _ _ address _ _ A q hA ρ
  · intro g r; funext p
    exact (congrArg (MIdeal.SkPrf.output S) (read_set S g r p)).trans (read_prefix S _ _)
  · intro g r t x h
    apply local_port S g _ _ x
    intro p hp
    rw [h p hp]
  · intro g a b h
    exact Subtype.ext ((MReduction.structural S).keyInj a.property.addressFacts b.property.addressFacts (congrArg Prod.snd h))
  · intro g r; funext a
    simp only [address, seedAddress, withOutputs, withRows, seed_outside, Option.elim_none]

theorem address_prf (pk : S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec (SkAdrs S.vp) S.Node) Bool)
    (q : ℕ) (hA : PU A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (addressScheme S g pk)
      (A (oracle g)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  exact address_prf_answer S pk A q hA.toPUE.prfAnswerCost ρ

end Reduction.Compression

#print axioms Reduction.Compression.terminal_prf

#print axioms Reduction.Compression.fixed_seed_prf
#print axioms Reduction.Compression.fixed_seed_eval

#print axioms Reduction.Compression.address_prf
