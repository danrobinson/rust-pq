import MIdeal.Hmsg
import MIdeal.MsgPrf512
import Ideal.Inst.Itsr128

namespace MIdeal.Hmsg
open MLink Ideal Ideal.Itsr Ideal.HP SLHDSA SLHDSA.Concrete OracleComp OracleSpec ENNReal KeyedHash KeyedHash.Covering
open VCVio.Algorithms.Sha2
variable (S : Sha2Set)

abbrev Input := S.Node × S.Node × List Byte

def ib (x : S.Node × Input S) := inner S x.1 x.2.1 x.2.2.1 x.2.2.2
def ob (x : S.Node × Input S) := outer S x.1 x.2.1

theorem ib_injective : Function.Injective (ib S) := by
  rintro ⟨r,pk,root,m⟩ ⟨r',pk',root',m'⟩ h
  have e := congrArg (fun b : ByteArray => b.data.toList) (Sha512.padBlocks_injective h)
  change ((_ ++ _ ++ _ ++ _ : ByteArray).data.toList) = ((_ ++ _ ++ _ ++ _ : ByteArray).data.toList) at e
  simp only [ByteArray.data_append, Array.toList_append, List.append_assoc] at e
  obtain ⟨h₁,h₂⟩ := List.append_inj e (by simp [bytesToByteArray])
  obtain ⟨h₂,h₃⟩ := List.append_inj h₂ (by simp [bytesToByteArray])
  obtain ⟨h₃,h₄⟩ := List.append_inj h₃ (by simp [bytesToByteArray])
  rw [Vector.toList_inj.mp h₁, Vector.toList_inj.mp h₂, Vector.toList_inj.mp h₃, h₄]

theorem ob_injective_state (x y : S.Node × Input S) (s t : Chain512)
    (h : ob S x s = ob S y t) : s = t := by
  have e := congrArg (fun b : ByteArray => b.data.toList) (Sha512.padBlocks_injective h)
  change ((_ ++ _ ++ _ ++ _ : ByteArray).data.toList) = ((_ ++ _ ++ _ ++ _ : ByteArray).data.toList) at e
  simp only [ByteArray.data_append, Array.toList_append, List.append_assoc] at e
  have h₂ := (List.append_inj e (by simp [bytesToByteArray])).2
  have h₃ := (List.append_inj h₂ (by simp [bytesToByteArray])).2
  apply Sha512.serialize_bijective.injective
  exact Vector.toList_inj.mp (List.append_cancel_right h₃)

private theorem m_le : S.vp.params.m ≤ 64 := by cases S <;> decide

def digest (s : Chain512) := Sha512.takeBytes S.vp.params.m (m_le S) (Sha512.serialize s)

theorem digest_uniform (P : Bytes S.vp.params.m → Prop) :
    Pr{let u ← $ᵗ Chain512}[P (digest S u)] = Pr{let y ← $ᵗ (Bytes S.vp.params.m)}[P y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective Sha512.serialize_bijective
    (fun s => P (Sha512.takeBytes _ (m_le S) s))).trans (Sha512.takeBytes_balanced _ _ P)

theorem digest_eq (s : Chain512) : byteArrayPrefixOrZero
    ((stateBytes64 s.toArray).extract 0 S.vp.params.m) S.vp.params.m = digest S s := by
  let m := S.vp.params.m
  let v := Sha512.serialize s
  change byteArrayPrefixOrZero ((bytesToByteArray v).extract 0 m) m = _
  have hraw : (((bytesToByteArray v).extract 0 m).extract 0 m).toList = v.toList.take m := by
    rw [ByteArray.toList_eq_toList_data, ByteArray.data_extract, Array.toList_extract,
      ByteArray.data_extract, Array.toList_extract]
    simp [bytesToByteArray, Vector.toList]
  have hl : (((bytesToByteArray v).extract 0 m).extract 0 m).toList.length = m := by
    rw [hraw]; simp [Nat.min_eq_left (m_le S), m]
  simp only [byteArrayPrefixOrZero, byteArrayPrefixChecked, decodeExact, hl, dite_true]
  apply Vector.ext
  intro i hi
  simp [digest, Sha512.takeBytes, hraw, v, m]

noncomputable section
local instance (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

theorem itsr_problem (g : CompressionTables) (hw : S.vp.params.n ≠ 16) :
    Reduction.itsrProblem S.vp (tablePrimitives g S.vp.params) =
      probI Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) g.2 := by
  have he (r : S.Node) (x : Input S) : (tablePrimitives g S.vp.params).Hmsg r x.1 x.2.1 x.2.2 =
      hashG Sha512.initial (ib S) (ob S) (digest S) g.2 (r,x) :=
    (hmsg_wide S g hw r x.1 x.2.1 x.2.2).trans (digest_eq S _)
  exact congrArg (fun f : S.Node → Input S → Bytes S.vp.params.m =>
    ({ khf := { keygen := $ᵗ S.Node, hash := f }, indices := idxOf S.vp } :
      ITSRProblem S.Node (Input S) (Bytes S.vp.params.m) (Adrs × ℕ)))
    (funext fun r => funext (he r))

theorem itsr_bound (hw : S.vp.params.n ≠ 16) (A : ItsrAdvI Chain512 Block512 S.Node (Input S))
    (n Q : ℕ)
    (hn : IsQueryBoundP (gameProg Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) A)
      (fun i => lgB Prod.snd i = true) n)
    (hQ : IsQueryBoundP (gameProg Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) A)
      (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g => ITSRExperiment (ItsrAdvI.inst A
      (probI Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) g) g)) ≤
      reuseSum S.vp.params.h S.vp.params.a S.vp.params.k n +
        ((Q^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^512)⁻¹ := by
  have h := itsr_le Sha512.initial (ib S) (ob S) (digest S) (idxOf S.vp) (ib_injective S)
    (ob_injective_state S) (fun x s => outer_length S hw x.1 x.2.1 s) (digest_uniform S) A n Q hn hQ
  have hc : (Fintype.card Chain512 : ℝ≥0∞) = (2:ℝ≥0∞)^512 := by
    simp only [Sha512.card_chain512, Nat.cast_pow, Nat.cast_ofNat]
  rw [hc] at h
  exact h.trans (add_le_add (prT_tape_cov_le S.vp n) le_rfl)
def msgLimit (ℓ : ℕ) (x : S.Node × Input S) := x.2.2.2.length ≤ ℓ

theorem ib_length (x : S.Node × Input S) :
    (ib S x).length = (x.2.2.2.length + 3*S.vp.params.n + 16)/128+1 := by
  rw [ib, inner, Sha512.padBlocks_length]
  simp [bytesToByteArray, ByteArray.size]
  omega

/-- Bound for an adversary with public SHA-512 compression access and bounded target and output messages. -/
theorem itsr_query_bound (hw : S.vp.params.n ≠ 16)
    (A : OracleComp (unifSpec + (hS Chain512 Block512 + ITSRTargetSpec (Input S) S.Node)) (S.Node × Input S))
    (g256 : CF St Blk) (q qs ℓ : ℕ) (hq : IsQueryBoundP A (fun i => isCompI i = true) q)
    (hqs : IsQueryBoundP A (fun i => isTgtI i = true) qs)
    (htgt : AllQueriesSatisfy A (tgtOK (msgLimit S ℓ)))
    (hout : ∀ x ∈ support A, msgLimit S ℓ x) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g => ITSRExperiment (ItsrAdvI.inst A
      (Reduction.itsrProblem S.vp (tablePrimitives (g256,g) S.vp.params)) g)) ≤
      reuseSum S.vp.params.h S.vp.params.a S.vp.params.k (q + (qs+1)*2) +
        (((q + (qs+1)*((ℓ+3*S.vp.params.n+16)/128+3))^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^512)⁻¹ := by
  have eq (g : CF Chain512 Block512) := congrArg
    (fun prob : ITSRProblem S.Node (Input S) (Bytes S.vp.params.m) (Adrs × ℕ) =>
      ITSRExperiment (ItsrAdvI.inst A prob g)) (itsr_problem S (g256,g) hw)
  simp_rw [eq]
  apply itsr_bound S hw A
  · exact gameProg_bound (fun n h => by simp [lgB] at h) _ _ _ _ _ 2 (msgLimit S ℓ)
      (fun x _ => hashM_bound2 (fun t h => by simp [lgB] at h) _ _ _ _ x)
      A q qs hq hqs htgt hout
  · refine gameProg_bound (fun n h => by simp at h) _ _ _ _ _ _ (msgLimit S ℓ) ?_
      A q qs hq hqs htgt hout
    intro x hx
    apply hashM_bound
    intro st
    rw [ib_length, show (ob S x st).length = 2 from outer_length S hw _ _ st]
    change x.2.2.2.length ≤ ℓ at hx
    omega
end
end MIdeal.Hmsg
