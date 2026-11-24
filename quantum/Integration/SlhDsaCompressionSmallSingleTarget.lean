import Integration.SlhDsaCompressionSmallItsr

namespace Reduction.Compression.SmallItsr
open MLink Ideal Ideal.Itsr MIdeal.Hmsg SLHDSA SLHDSA.Security SLHDSA.DigestTransport
open OracleComp OracleSpec PQ.Interactive Quantum ENNReal Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
abbrev Indices (S : Sha2Set) := Fin S.vp.params.k → Fin (2^S.vp.params.a)

private theorem vector_uniform (S : Sha2Set) (P : Indices S → Prop) :
    Pr{let b ← $ᵗ (Bytes S.vp.params.m)}[P (coveringDigest S.vp b).2] =
      Pr{let v ← $ᵗ (Indices S)}[P v] := by
  have h := MessageHash.covering_uniform S (fun d => P d.2)
  rw [digest_uniform S (fun b => P (coveringDigest S.vp b).2)] at h
  exact h.trans ((SampleableType.prEvent_uniformSample_comp_of_bijective
    (Equiv.prodComm (Fin (2^S.vp.params.h)) (Indices S)).bijective (fun d => P d.1)).trans
    (SampleableType.prEvent_uniformSample_fst P))

def slowVector (s : St) : Indices .s128s := fun i => (Slow.key i s).2
def fastVector (s : St) : Indices .s128f := fun i => (Fast.key i s).2

private theorem slow_uniform (P : Indices .s128s → Prop) :
    Pr{let s ← $ᵗ St}[P (slowVector s)] = Pr{let v ← $ᵗ (Indices .s128s)}[P v] :=
  (prEvent_dig30 (fun d => P (coveringDigest Slow.vp d).2)).trans (vector_uniform _ P)

private theorem fast_uniform (P : Indices .s128f → Prop) :
    Pr{let s ← $ᵗ St}[P (fastVector s)] = Pr{let v ← $ᵗ (Indices .s128f)}[P v] := by
  have eq (s t : St) : fastVector s = (coveringDigest Fast.vp (digest128f (s,t))).2 := by
    funext i
    exact congrArg Prod.snd (Fast.trim_independent s default t i)
  calc _ = Pr{let z ← $ᵗ (St × St)}[P (fastVector z.1)] := (SampleableType.prEvent_uniformSample_fst _).symm
       _ = Pr{let z ← $ᵗ (St × St)}[P (coveringDigest Fast.vp (digest128f z)).2] := congrArg (fun f : St × St → Prop => Pr{let z ← $ᵗ (St × St)}[f z]) (funext fun z => congrArg P (eq z.1 z.2))
       _ = _ := (digest128f_uniform (fun d => P (coveringDigest Fast.vp d).2)).trans (vector_uniform .s128f P)

noncomputable local instance (S : Sha2Set) (g : CompressionTables) : SampleableType (tablePrimitives g S.vp.params).Y :=
  inferInstanceAs (SampleableType S.Node)

private theorem single_match (S : Sha2Set) (g : CompressionTables) (cand : Query S) (ts : List (Query S))
    (len : ts.length ≤ 1) (win : (itsrProblem S.vp (tablePrimitives g S.vp.params)).Wins ts cand) :
    ∃ y ∈ ts, coveringDigest S.vp (msg S g cand) = coveringDigest S.vp (msg S g y) := by
  have component (i : Fin S.vp.params.k) : ∃ y ∈ ts,
      (coveringDigest S.vp (msg S g y)).1 = (coveringDigest S.vp (msg S g cand)).1 ∧
      (coveringDigest S.vp (msg S g y)).2 i = (coveringDigest S.vp (msg S g cand)).2 i := by
    let d := msg S g cand
    let needle := ((splitDigest S.vp.params d).forsAdrs, i.val * 2^S.vp.params.a +
      forsIdx S.vp.params (splitDigest S.vp.params d).md.toList i.val)
    have hn : needle ∈ idxOf S.vp d := by
      simp only [idxOf,Reduction.forsIndices,List.mem_map,List.mem_range]
      exact ⟨i.val,i.isLt,rfl⟩
    obtain ⟨y,hy,hit⟩ := List.mem_flatMap.mp (win.2 needle hn)
    exact Exists.intro y (And.intro hy (match_of_mem_idxOf S.vp d (msg S g y) i hit))
  let i : Fin S.vp.params.k := ⟨0,by cases S <;> decide⟩
  obtain ⟨y,hy,addr,_⟩ := component i
  refine ⟨y,hy,Prod.ext addr.symm (funext fun j => ?_)⟩
  obtain ⟨z,hz,_,eq⟩ := component j
  have same : z = y := by
    rcases ts with _|⟨t,tail⟩
    · simp at hy
    cases tail with
    | nil => simp_all
    | cons => simp only [List.length_cons] at len; omega
  subst z
  exact eq.symm

variable (S : Sha2Set) (hn : S.vp.params.n = 16)
variable (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
variable (c : Caps) (q qs : ℕ) (single : qs ≤ 1)
variable (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
variable (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))

include single hq hs hc in
private theorem bound (key : St → Indices S)
    (uniform : ∀ P : Indices S → Prop, Pr{let s ← $ᵗ St}[P (key s)] = Pr{let z ← $ᵗ (Indices S)}[P z])
    (hit : ∀ g x y, coveringDigest S.vp (msg S g x) = coveringDigest S.vp (msg S g y) →
      key (g.1 (last S hn g x)) = key (g.1 (last S hn g y))) :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ loss S c.ml q qs (S.vp.params.a*S.vp.params.k) := by
  apply itsr_bound_of key S hn _ _ r seeds F c q qs hq hs hc
  · intro g cand ts len win
    apply selected_of_target S hn key g cand ts win
    obtain ⟨y,hy,e⟩ := single_match S g cand ts (len.trans single) win
    exact ⟨y,hy,hit g cand y e⟩
  · intro B
    have h := uniform (fun z => z ∈ B)
    simp only [SampleableType.prEvent_uniformSample] at h
    have card : Fintype.card (Indices S) = 2^(S.vp.params.a*S.vp.params.k) := by
      change Fintype.card (Fin S.vp.params.k → Fin (2^S.vp.params.a)) = _
      rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,← pow_mul]
    have e := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,Finset.filter_mem_eq_inter,Finset.univ_inter,card,
      Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using e.le

include hn single hq hs hc in
/-- At most one signing query forces all FORS indices to match the same target.
The retained projection has 168 bits at 128s and 198 bits at 128f. -/
theorem single_itsr :
    SetOracle.uniformMean (fun g => qItsrAdvantage (itsrProblem S.vp (randPrims (functions S g)))
      (qbItsrL (reduced S r seeds F g)) F.ρ₀) ≤ loss S c.ml q qs (S.vp.params.a*S.vp.params.k) := by
  cases S <;> try contradiction
  · apply bound .s128s rfl r seeds F c q qs single hq hs hc slowVector slow_uniform
    intro g x y e
    funext i
    exact congrArg Prod.snd ((Slow.covers i).hit g x y (congrArg Prod.fst e)
      (congrArg (fun z => z.2 i) e))
  · apply bound .s128f rfl r seeds F c q qs single hq hs hc fastVector fast_uniform
    intro g x y e
    funext i
    exact congrArg Prod.snd ((Fast.covers i).hit g x y (congrArg Prod.fst e)
      (congrArg (fun z => z.2 i) e))
end Reduction.Compression.SmallItsr
#print axioms Reduction.Compression.SmallItsr.single_itsr
