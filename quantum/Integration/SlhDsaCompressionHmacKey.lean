import Integration.SlhDsaCompressionPrf
import Integration.SlhDsaCompressionMsgCost

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker
variable (S : Sha2Set)

private def wideBlock (p : S.Node × Bool) : Block512 :=
  if p.2 then MIdeal.Sha512.okey S p.1 else MIdeal.Sha512.ikey S p.1

private theorem different (k l : S.Node) : MIdeal.Sha512.ikey S k ≠ MIdeal.Sha512.okey S l := by
  intro h
  have e := congrArg (fun b : Block512 => b.toList[S.vp.params.n]?) h
  have hw : S.vp.params.n < 128 := by cases S <;> decide
  simp [MIdeal.Sha512.ikey, MIdeal.Sha512.okey, MIdeal.Sha512.key0L,
    Vector.toList, hw] at e

private theorem block_injective : Function.Injective (wideBlock S) := by
  rintro ⟨k,b⟩ ⟨l,c⟩ h
  cases b <;> cases c <;> simp only [wideBlock, Bool.false_eq_true, ↓reduceIte] at h
  · rw [MIdeal.Sha512.ikey_injective S h]
  · exact False.elim (different S k l h)
  · exact False.elim (different S l k h.symm)
  · rw [MIdeal.Sha512.okey_injective S h]

private def location (p : S.Node × Bool) : Chain512 × Block512 := (MIdeal.Sha512.initial, wideBlock S p)

private theorem injective : Function.Injective (location S) :=
  fun _ _ h => block_injective S (congrArg Prod.snd h)

private noncomputable def decode (i : Chain512 × Block512) : Option (S.Node × Bool) := by
  classical
  exact if h : ∃ p, location S p = i then some h.choose else none

private theorem decode_at (p : S.Node × Bool) : decode S (location S p) = some p := by
  classical
  unfold decode
  rw [dite_eq_left (show ∃ x, location S x = location S p from ⟨p,rfl⟩)]
  congr 1
  exact injective S (Exists.choose_spec (show ∃ x, location S x = location S p from ⟨p,rfl⟩))

private def read (g : CompressionTables) (p : S.Node × Bool) := g.2 (location S p)

private noncomputable def put (g : CompressionTables) (r : S.Node × Bool → Chain512) : CompressionTables :=
  (g.1, fun i => (decode S i).elim (g.2 i) r)

private theorem read_put (g : CompressionTables) (r : S.Node × Bool → Chain512) :
    read S (put S g r) = r := by
  funext p
  change (decode S (location S p)).elim _ _ = _
  rw [decode_at]; rfl

private theorem swap : Function.Involutive
    (fun z : CompressionTables × (S.Node × Bool → Chain512) => (put S z.1 z.2, read S z.1)) := by
  rintro ⟨g,r⟩
  refine Prod.ext (Prod.ext rfl ?_) (read_put S g r)
  funext i
  classical
  by_cases h : ∃ p, location S p = i
  · obtain ⟨p,rfl⟩ := h
    change read S (put S (put S g r) (read S g)) p = _
    rw [read_put]; rfl
  · simp only [put, decode, dite_eq_right h, Option.elim_none]

private noncomputable def loc : Input → Option (S.Node × Bool)
  | .inl _ => none
  | .inr i => decode S i

/-- The two keyed starting states of the SHA-512 HMAC computation. -/
def wideScheme (g : CompressionTables) : PRFScheme S.Node Bool Chain512 :=
  ⟨$ᵗ S.Node, fun k outer => g.2 (MIdeal.Sha512.initial, wideBlock S (k,outer))⟩

/-- Continue HMAC from the two chaining states produced by the key blocks. -/
def wideMessage (g : CompressionTables) (start : Bool → Chain512) (r : S.Node) (m : List Byte) : S.Node :=
  byteArrayPrefixOrZero (VCVio.Algorithms.Sha2.stateBytes64
    (g.2 (start true, MIdeal.Sha512.oblock
      (mdFold g.2 (start false) (MIdeal.Sha512.iblocks S r m)))).toArray) S.vp.params.n

theorem wide_message_real (g : CompressionTables) (hw : S.vp.params.n ≠ 16) (k r : S.Node) (m : List Byte) :
    (tablePrimitives g S.vp.params).PRFmsg k r m = wideMessage S g ((wideScheme S g).eval k) r m :=
  MIdeal.Sha512.msgPrf_shape S g hw k r m

/-- Cost after replacing the two key-block evaluations. -/
theorem wide_message_cost (start : Bool → Chain512) (r : S.Node) (m : List Byte) :
    EvalCost (fun H => (pure (wideMessage S (tablesOf H) start r m) : ProbComp S.Node))
      ((m.length + S.vp.params.n + 16) / 128 + 2) := by
  have inner := fold512_cost (start false) (MIdeal.Sha512.iblocks S r m)
  have outer (s : Chain512) := (fold512_cost (start true) [MIdeal.Sha512.oblock s]).map
    (fun t => byteArrayPrefixOrZero (VCVio.Algorithms.Sha2.stateBytes64 t.toArray) S.vp.params.n)
  have h := EvalCost.bind inner outer
  simpa only [wideMessage, pure_bind, mdFold, List.foldl_cons, List.foldl_nil, map_pure,
    List.length_cons, List.length_nil, MIdeal.Sha512.iblocks_length, Nat.add_assoc] using h

/-- Replace both keyed compression results with independent uniform chaining states
in the presence of superposition access to both shared tables. -/
theorem wide_key_hop {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec Bool Chain512) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (wideScheme S g) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  rw [← node_card_real S]
  apply column_prf (loc S) (put S) (read S) (swap S) (read_put S) _ (fun _ => id)
    (fun _ => Function.injective_id) (fun _ _ => rfl) A q hA ρ
  intro g r t x h
  cases x with
  | inl i => rfl
  | inr i =>
    change (0, arrayVectorEquivFin UInt64 8 ((decode S i).elim (g.2 i) r)) =
      (0, arrayVectorEquivFin UInt64 8 ((decode S i).elim (g.2 i) t))
    cases e : decode S i with
    | none => rfl
    | some p => rw [Option.elim_some, Option.elim_some, h p e]

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.wide_key_hop

#print axioms Reduction.Compression.HmacKey.wide_message_real
#print axioms Reduction.Compression.HmacKey.wide_message_cost
