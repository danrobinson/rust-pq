import Integration.SlhDsaCompressionHmacSignature
import Ideal.Inst.MsgPrf128
import Integration.SlhDsaCompressionPrf
import Integration.SlhDsaCompressionMsgCost

set_option maxRecDepth 8192

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

private def keyBlock (p : (Bytes 16) × Bool) : Blk :=
  if p.2 then Ideal.okey p.1 else Ideal.ikey p.1

private theorem block_injective : Function.Injective (keyBlock ) := by
  rintro ⟨k,b⟩ ⟨l,c⟩ h
  cases b <;> cases c <;> simp only [keyBlock, Bool.false_eq_true, ↓reduceIte] at h
  · rw [Ideal.ikey_injective h]
  · exact False.elim (ikey_ne_okey k l h)
  · exact False.elim (ikey_ne_okey l k h.symm)
  · rw [Ideal.okey_injective h]

private def location (p : (Bytes 16) × Bool) : St × Blk := (IV128, keyBlock p)

private theorem injective : Function.Injective (location ) :=
  fun _ _ h => block_injective (congrArg Prod.snd h)

private noncomputable def decode (i : St × Blk) : Option ((Bytes 16) × Bool) := by
  classical
  exact if h : ∃ p, location p = i then some h.choose else none

private theorem decode_at (p : (Bytes 16) × Bool) : decode (location p) = some p := by
  classical
  unfold decode
  rw [dite_eq_left (show ∃ x, location x = location p from ⟨p,rfl⟩)]
  congr 1
  exact injective (Exists.choose_spec (show ∃ x, location x = location p from ⟨p,rfl⟩))

private def read (g : CompressionTables) (p : (Bytes 16) × Bool) := g.1 (location p)

private noncomputable def put (g : CompressionTables) (r : (Bytes 16) × Bool → St) : CompressionTables :=
  (fun i => (decode i).elim (g.1 i) r, g.2)

private theorem read_put (g : CompressionTables) (r : (Bytes 16) × Bool → St) :
    read (put g r) = r := by
  funext p
  simp only [read,put,decode_at,Option.elim_some]

private theorem replace_left_involutive {I V U K : Type} (idx : K → I) (dec : I → Option K)
    (hdec : ∀ k, dec (idx k) = some k) (hinv : ∀ i k, dec i = some k → idx k = i) :
    Function.Involutive (fun z : ((I → V) × U) × (K → V) =>
      ((fun i => (dec i).elim (z.1.1 i) z.2, z.1.2),fun k => z.1.1 (idx k))) := by
  rintro ⟨⟨g,u⟩,r⟩
  apply Prod.ext
  · apply Prod.ext
    · funext i
      change (dec i).elim ((dec i).elim (g i) r) (fun k => g (idx k)) = g i
      cases e : dec i with
      | none => rfl
      | some k => exact congrArg g (hinv i k e)
    · rfl
  · funext k
    change (dec (idx k)).elim _ _ = r k
    rw [hdec]
    rfl

private theorem swap : Function.Involutive
    (fun z : CompressionTables × ((Bytes 16) × Bool → St) => (put z.1 z.2, read z.1)) := by
  apply replace_left_involutive location decode decode_at
  intro i k h
  classical
  unfold decode at h
  split at h
  next he =>
    obtain rfl := Option.some.inj h
    exact he.choose_spec
  next => contradiction

private noncomputable def loc : Input → Option ((Bytes 16) × Bool)
  | .inr _ => none
  | .inl i => decode i

/-- The two keyed starting states of the SHA-256 HMAC computation. -/
def keyScheme (g : CompressionTables) : PRFScheme (Bytes 16) Bool St :=
  ⟨$ᵗ (Bytes 16), fun k outer => g.1 (IV128, keyBlock (k,outer))⟩

/-- Continue HMAC from the two chaining states produced by the key blocks. -/
def message (g : CompressionTables) (start : Bool → St) (r : (Bytes 16)) (m : List Byte) : (Bytes 16) :=
  Ideal.out16 (g.1 (start true, Ideal.oblock (mdFold g.1 (start false) (Ideal.iblocks r m))))

theorem message_real (g : CompressionTables) (k r : Bytes 16) (m : List Byte) :
    (tablePrimitives g Sha2Set.s128s.vp.params).PRFmsg k r m = message g ((keyScheme g).eval k) r m := by
  refine Eq.trans ?_ (Ideal.msgPrf_shape g.1 k r m)
  change @sha2PRFmsgMixed (liftC g.1) (lift512 g.2) 16 k r m = @sha2PRFmsgG (liftC g.1) 16 k r m
  simp only [sha2PRFmsgMixed, sha2PRFmsgG, ite_true]

theorem message_cost (start : Bool → St) (r : Bytes 16) (m : List Byte) :
    EvalCost (fun H => (pure (message (tablesOf H) start r m) : ProbComp (Bytes 16)))
      ((m.length + 24)/64 + 2) := by
  have inner := fold256_cost (start false) (Ideal.iblocks r m)
  have outer (s : St) := (fold256_cost (start true) [Ideal.oblock s]).map out16
  simpa only [message,pure_bind,mdFold,List.foldl_cons,List.foldl_nil,map_pure,List.length_cons,List.length_nil,
    Ideal.iblocks_length,Nat.add_assoc] using EvalCost.bind inner outer

/-- Replace both keyed compression results with independent uniform chaining states
in the presence of superposition access to both shared tables. -/
theorem key_hop {E : Type} [Fintype E] [DecidableEq E]
    (A : (Input → Output) → QOC (WS Input Output E) (PRFScheme.PRFOracleSpec Bool St) Bool)
    (q : ℕ) (hA : PrfAnswerCost A q) (ρ : SubState ((Input × Output) × E)) :
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (keyScheme g) (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^128) := by
  have card : (Fintype.card (Bytes 16) : ℝ) = 2^128 := node_card_real Sha2Set.s128s
  rw [← card]
  apply column_prf loc put read swap read_put _ (fun _ => id)
    (fun _ => Function.injective_id) (fun _ _ => rfl) A q hA ρ
  intro g r t x h
  cases x with
  | inr i => simp only [oracle,put]
  | inl i =>
    simp only [oracle,put]
    cases e : decode i with
    | none => rfl
    | some p => rw [Option.elim_some, Option.elim_some, h p e]

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.key_hop
#print axioms Reduction.Compression.Hmac256.message_real
#print axioms Reduction.Compression.Hmac256.message_cost
