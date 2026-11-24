import Integration.SlhDsaShakePermutationLongSelectTrace

/-! An honest sponge evaluation extends the recorded forest by prefixes of its own padded input. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort Phase OracleSpec OracleComp MLink SLHDSA
noncomputable section
set_option maxRecDepth 8192
variable (S : Sha2Set) (pk : S.Node)
abbrev Log := List (Bytes 32 × List S.Node)

theorem cover_cons (t : Trace) (L : Log S) (e : Bytes 32 × List S.Node) (h : covered S pk t L) :
    covered S pk t (e::L) := by
  intro p w hpath
  rcases h hpath with empty|⟨e',mem,pref⟩
  · exact Or.inl empty
  · exact Or.inr ⟨e',List.mem_cons_of_mem _ mem,pref⟩

private theorem step {d : Bytes 32} {xs : List S.Node} {t u : Trace} {L : Log S} {p : List Rate}
    {w y : Words} {b : Rate} (tr : Trail t p w) (uq : UniquePaths t) (cov : covered S pk t L)
    (seen : (d,xs) ∈ L) (pref : p++[b] <+: blocks S pk d xs)
    (mv : Move t (join (rateXor b (rateOf w)) (capOf w)) y u) :
    Trail u (p++[b]) y ∧ UniquePaths u ∧ covered S pk u L ∧ ∀ e ∈ t, e ∈ u := by
  let x := join (rateXor b (rateOf w)) (capOf w)
  have sc : capOf w = capOf x := (cap_join _ _).symm
  have nx : nextBlock w x = b := by simp [nextBlock,x]
  cases mv with
  | replay mem => exact ⟨nx ▸ tr.step mem sc,uq,cov,fun _ h => h⟩
  | fresh _ iso =>
    have sub (e) (h : e ∈ t) : e ∈ (x,y)::t := List.mem_cons_of_mem _ h
    refine ⟨(congrArg (fun r => Trail ((x,y)::t) (p++[r]) y) nx).mp ((tr.weaken sub).step (List.mem_cons_self ..) sc),unique_forward uq iso,?_,sub⟩
    intro q z trail
    rcases forward_paths iso trail with old|⟨_,p',w',old,sc',rfl⟩
    · exact cov old
    · obtain ⟨rfl,rfl⟩ := uq old tr (sc'.trans sc.symm)
      exact Or.inr ⟨(d,xs),seen,nx.symm ▸ pref⟩

theorem absorb_all (d : Bytes 32) (xs : List S.Node) (L : Log S) (seen : (d,xs) ∈ L)
    (rs p : List Rate) (w : Words) (t : Trace) (uq : UniquePaths t) (cov : covered S pk t L)
    (tr : Trail t p w) (eq : p++rs = blocks S pk d xs) (post : Words → Trace → Prop)
    (done : ∀ y u, Trail u (blocks S pk d xs) y → UniquePaths u → covered S pk u L → (∀ e ∈ t, e ∈ u) → post y u) :
    all (Phase.absorb d w rs) t post := by
  induction rs generalizing p w t with
  | nil =>
    have h : p = blocks S pk d xs := by simpa using eq
    exact done _ _ (h ▸ tr) uq cov (fun _ h => h)
  | cons b rs ih =>
    intro y u hm
    have he : (p++[b])++rs = blocks S pk d xs := by simpa using eq
    obtain ⟨next,uq',c',sub⟩ := step S pk tr uq cov seen ⟨rs,he⟩ hm
    exact ih (p++[b]) y u uq' c' next he (fun z v h1 h2 h3 h4 => done z v h1 h2 h3 (fun e he' => h4 _ (sub e he')))

theorem hash_all (d : Bytes 32) (xs : List S.Node) (L : Log S) (t : Trace) (uq : UniquePaths t)
    (cov : covered S pk t L) (post : S.Node → Trace → Prop) (done : ∀ w u, Trail u (blocks S pk d xs) w →
      UniquePaths u → covered S pk u ((d,xs)::L) → (∀ e ∈ t, e ∈ u) → post (SkFormat.split S w).1 u) :
    all (Phase.evalHash S pk d xs) t post := by
  unfold Phase.evalHash
  apply bind _ (fun w => pure (SkFormat.split S w).1) t post (fun w u => post (SkFormat.split S w).1 u) _ (fun _ _ h => h)
  exact absorb_all S pk d xs ((d,xs)::L) (List.mem_cons_self ..) _ [] 0 t uq (cover_cons _ _ _ _ _ cov) .root rfl _ done
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.hash_all
