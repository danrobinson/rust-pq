import PQ.Interactive.EUFCMA

namespace PQ.Interactive
open OracleComp OracleSpec
open scoped Classical

/-- A successful forgery on a fresh message also has a fresh message-signature pair. -/
theorem quantum_euf_le_suf {W M PK SK Sig : Type} [Fintype W]
    {alg : SignatureAlg ProbComp M PK SK Sig} (Q : QForger W alg) :
    qUnforgeableAdvantage Q ≤ qStrongUnforgeableAdvantage Q := by
  classical
  let transcript : Closed W ((M × Sig) × QueryLog (M →ₒ Sig) × Bool) := do
    let ks ← liftU alg.keygen
    let r ← close (signImpl alg ks.1 ks.2) (Q.main ks.1) []
    let ok ← liftU (alg.verify ks.1 r.1.1 r.1.2)
    pure (r.1, r.2, ok)
  have eq (fresh : QueryLog (M →ₒ Sig) → M → Sig → Bool) :
      qSigExperiment fresh Q = (fun r => fresh r.2.1 r.1.1 r.1.2 && r.2.2) <$> transcript := by
    simp [qSigExperiment, transcript, map_bind]
  unfold qUnforgeableAdvantage qStrongUnforgeableAdvantage qUnforgeableExperiment qStrongUnforgeableExperiment
  rw [eq, eq, qWeight_map, qWeight_map]
  apply qWeight_mono
  rintro ⟨⟨m,s⟩,log,ok⟩ h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  exact ⟨Bool.eq_false_iff.mpr fun hs => Bool.noConfusion (h.1.symm.trans
    (SignatureAlg.wasQueried_eq_true_of_signingLogContains_eq_true log m s hs)), h.2⟩
end PQ.Interactive

#print axioms PQ.Interactive.quantum_euf_le_suf
