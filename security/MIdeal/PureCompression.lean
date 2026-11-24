import MIdeal.MixedTables
import Ideal.Realize.PureForger
import MReduction.Instances

/-! Classical pure-byte forgery with public access to both SHA-2 compression tables. -/
namespace MIdeal.PureCompression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction ENNReal

abbrev Sign := (List Byte × List Byte) →ₒ Option (List Byte)
abbrev Ports := unifSpec + (hS Chain512 Block512 + (hS St Blk + Sign))

structure Forger where
  main : List Byte → OracleComp Ports ((List Byte × List Byte) × Option (List Byte))

/-- Condition on the public SHA-512 table, preserving the SHA-256 and signing oracles. -/
def Forger.at512 (A : Forger) (g : CF Chain512 Block512) : ForgerP where
  main pk := simulateQ (instImpl g) (A.main pk)

variable (S : Sha2Set)
local notation "P" => fun g => tablePrimitives g S.vp.params

local instance (g : CompressionTables) : SampleableType (P g).Y :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : SampleableType (P g).SkSeed :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf :=
  inferInstanceAs (SampleableType (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).Y :=
  inferInstanceAs (DecidableEq (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed :=
  inferInstanceAs (DecidableEq (Bytes S.vp.params.n))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey :=
  inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Inhabited (P g).Y :=
  inferInstanceAs (Inhabited (Bytes S.vp.params.n))
local instance (g : CompressionTables) : Fintype (P g).Y :=
  inferInstanceAs (Fintype (Bytes S.vp.params.n))

def codec (g : CompressionTables) : CoreWireCodec S.vp.params (P g).core where
  pkSeed := WireCodec.bytes _
  skSeed := WireCodec.bytes _
  skPrf := WireCodec.bytes _
  y := WireCodec.bytes _
  y_toBytes := fun _ => rfl

set_option maxHeartbeats 1600000 in
theorem structural (g : CompressionTables) : Structural S.vp (P g) :=
  by
  refine ⟨⟨fun _ _ h => h⟩, ?_, (MReduction.structural S).bounds⟩
  intro a ha b hb h
  have bound := fipsApprovedAddressBounds S.fips
  obtain ⟨hac,hal,hat⟩ := sha2Domain_of_addressFacts bound ha
  obtain ⟨hbc,hbl,hbt⟩ := sha2Domain_of_addressFacts bound hb
  exact Concrete.sha2AdrsKey_injective_of_domain hac hal hat hbc hbl hbt h

variable (rand : Bytes S.vp.params.n → Bytes S.vp.params.n → ProbComp (Bytes S.vp.params.n))
    (seeds : ProbComp (Bytes S.vp.params.n)) (A : Forger)

def strong (g : CompressionTables) : PureBytesStrongForger S.vp (P g) (codec S g)
    (fun k => rand k.pkSeed k.pkRoot) seeds where
  main pk := simulateQ (instImpl g.1) ((A.at512 g.2).main pk)

noncomputable def average (f : CompressionTables → ℝ≥0∞) : ℝ≥0∞ :=
  cfAvg fun g₅₁₂ => cfAvg fun g₂₅₆ => f (g₂₅₆,g₅₁₂)

theorem average_add (f h : CompressionTables → ℝ≥0∞) :
    average (fun g => f g + h g) = average f + average h := by
  unfold average
  simp only [cfAvg_add]

theorem average_mono {f h : CompressionTables → ℝ≥0∞} (le : ∀ g, f g ≤ h g) :
    average f ≤ average h := cfAvg_mono fun g => cfAvg_mono fun h => le (h,g)

local notation "F" => strong S rand seeds A
set_option quotPrecheck false in
local notation "Q" => fun g => toInternal (pureBytesToTyped (F g).toUnforgeableAdversary)

theorem suf_linear :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g)) +
        average (fun g => linIdealSuf (Q g)) ≤ average (fun g => linRealSuf (Q g)) := by
  rw [← average_add]
  exact average_mono fun g => slhdsa_pure_bytes_suf_cma_linear (structural S g) (F g)

theorem euf_linear :
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (F g).toUnforgeableAdversary) +
        average (fun g => linIdealEuf (Q g)) ≤ average (fun g => linRealEuf (Q g)) := by
  rw [← average_add]
  exact average_mono fun g => slhdsa_pure_bytes_euf_cma_linear (structural S g) (F g).toUnforgeableAdversary

/-- Erase the extra SHA-512 port from a query predicate when conditioning on its table. -/
def retained (p : PSpec.Domain → Bool) : Ports.Domain → Bool
  | .inl n => p (.inl n)
  | .inr (.inl _) => false
  | .inr (.inr t) => p (.inr t)

theorem Forger.at512_bound (B : Forger) (g : CF Chain512 Block512) (pk : List Byte)
    (p : PSpec.Domain → Bool) (n : ℕ) (h : IsQueryBoundP (B.main pk) (fun t => retained p t = true) n) :
    IsQueryBoundP ((B.at512 g).main pk) (fun t => p t = true) n := by
  refine h.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | t
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · simp [retained] at ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | q | t
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => (ht h).elim
    · exact isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => (ht h).elim

/-- Internal byte forger whose SHA-256 queries are kept as oracle calls through
pure message encoding. This gives a single program for every SHA-256 table. -/
def internalBytes (g : CompressionTables) : BytesStrongForger S.vp (P g) (codec S g)
    (fun k => rand k.pkSeed k.pkRoot) seeds where
  main pk := simulateQ (instImpl g.1) ((A.at512 g.2).toI.main pk)

open Ideal.Pure

private theorem internalBytes_eq (g : CompressionTables) :
    internalBytes S rand seeds A g =
      OptGuard.reduceS (alg := bytesAlg S.vp (P g) (codec S g) (fun k => rand k.pkSeed k.pkRoot) seeds)
        pureEncode fallbackB (F g) := by
  simp only [internalBytes, strong, OptGuard.reduceS, ForgerP.toI, simulateQ_map,
    simulateQ_instImpl_portImplP]

/-- Forgery reduction with a public SHA-256 port that can be counted before either
compression table is sampled. Malformed contexts require no internal signing query. -/
theorem suf_internal_linear :
    let B := internalBytes S rand seeds A
    let T := fun g => bytesToTyped (B g).toUnforgeableAdversary
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (F g)) +
      average (fun g => linIdealSuf (T g)) ≤ average (fun g => linRealSuf (T g)) := by
  dsimp only
  rw [← average_add]
  apply average_mono
  intro g
  apply le_trans _ (slhdsa_bytes_suf_cma_linear (structural S g) (internalBytes S rand seeds A g))
  apply add_le_add_left
  rw [internalBytes_eq]
  exact pure_bytes_strong_le_bytes _

theorem euf_internal_linear :
    let B := internalBytes S rand seeds A
    let T := fun g => bytesToTyped (B g).toUnforgeableAdversary
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (F g).toUnforgeableAdversary) +
      average (fun g => linIdealEuf (T g)) ≤ average (fun g => linRealEuf (T g)) := by
  dsimp only
  rw [← average_add]
  apply average_mono
  intro g
  apply le_trans _ (slhdsa_bytes_euf_cma_linear (structural S g) (internalBytes S rand seeds A g).toUnforgeableAdversary)
  apply add_le_add_left
  rw [internalBytes_eq]
  exact pure_bytes_le_bytes _

open Ideal.Realize

/-- Typed forger used by the component reductions, retaining the public SHA-256 port.
The carrier only fixes the node types and codec. -/
def typed (model : CompressionTables) (g512 : CF Chain512 Block512) :
    PortForgerProg S.vp (P model) :=
  typedP (codec S model) (A.at512 g512).toI.main

theorem typed_at (g : CompressionTables) (pk : PublicKeyCore (P g).core) :
    simulateQ (instImpl g.1) (typed S A g g.2 pk) =
      (bytesToTyped (internalBytes S rand seeds A g).toUnforgeableAdversary).main pk :=
  typedP_inst (prims := P g) (codec S g) (fun k => rand k.pkSeed k.pkRoot)
    seeds g.1 (A.at512 g.2).toI.main pk

variable (model : CompressionTables) {q qs L : ℕ}

theorem typed_port (g : CF Chain512 Block512)
    (h : ∀ pk, IsQueryBoundP (A.main pk) (fun i => retained isPortQP i = true) q)
    (pk : PublicKeyCore (P model).core) :
    IsQueryBoundP (typed S A model g pk) (fun i => isPortQ (S := GeneralScheme.SignatureCore S.vp (P model).core) i = true) q :=
  typedP_bound (prims := P model) (codec S model) (isPortQ (S := List Byte)) (isPortQ (S := GeneralScheme.SignatureCore S.vp (P model).core))
    (fun _ _ _ => ⟨rfl,rfl,rfl⟩) _ _ _ (toI_port _ _ (A.at512_bound g _ _ _ (h _)))

theorem typed_sign (g : CF Chain512 Block512)
    (h : ∀ pk, IsQueryBoundP (A.main pk) (fun i => retained isSignQP i = true) qs)
    (pk : PublicKeyCore (P model).core) :
    IsQueryBoundP (typed S A model g pk) (fun i => isSignQ (S := GeneralScheme.SignatureCore S.vp (P model).core) i = true) qs :=
  typedP_bound (prims := P model) (codec S model) (isSignQ (S := List Byte)) (isSignQ (S := GeneralScheme.SignatureCore S.vp (P model).core))
    (fun _ _ _ => ⟨rfl,rfl,rfl⟩) _ _ _ (toI_sign _ _ (A.at512_bound g _ _ _ (h _)))

theorem typed_long (g : CF Chain512 Block512)
    (h : ∀ pk, IsQueryBoundP (A.main pk) (fun i => retained (isLongQP L) i = true) 0)
    (pk : PublicKeyCore (P model).core) :
    IsQueryBoundP (typed S A model g pk) (fun i => isLongQ (S := GeneralScheme.SignatureCore S.vp (P model).core) (L+257) i = true) 0 :=
  typedP_bound (prims := P model) (codec S model) (isLongQ (S := List Byte) (L+257)) (isLongQ (S := GeneralScheme.SignatureCore S.vp (P model).core) (L+257))
    (fun _ _ _ => ⟨rfl,rfl,rfl⟩) _ _ _ (toI_long _ _ (A.at512_bound g _ _ _ (h _)))

theorem typed_out (g : CF Chain512 Block512)
    (h : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)
    (pk : PublicKeyCore (P model).core) :
    ∀ z ∈ support (typed S A model g pk), z.1.length ≤ L+257 := by
  intro z hz
  obtain ⟨v,hv,eq⟩ := typedP_out (prims := P model) (codec S model) _ pk z hz
  have le := toI_out (A.at512 g) _ (fun v hv => h _ _ (support_simulateQ_subset _ _ hv)) v hv
  simpa only [eq] using le

end MIdeal.PureCompression
#print axioms MIdeal.PureCompression.suf_internal_linear
#print axioms MIdeal.PureCompression.euf_internal_linear
#print axioms MIdeal.PureCompression.suf_linear
#print axioms MIdeal.PureCompression.euf_linear
