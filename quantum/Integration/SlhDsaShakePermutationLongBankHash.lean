import Integration.SlhDsaShakePermutationLongBankReads

namespace Reduction.ShakePermutation.Long.BankRun
open Classical ItsrLabel SparsePort MLink SLHDSA OracleSpec OracleComp PQ.Interactive Tails
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (pk : S.Node) (π : Permutation) (H : Table)

def report (p : List Rate) := replay π H p.reverse

def Known (D : Bank) (p : List Rate) := Matches D (report π H p).log

def Cover (D : Bank) (L : SelectTrace.Log S) := ∀ z v, D (tailHead z)=some v →
  ∃ e ∈ L, ∃ p, p <+: blocks S pk e.1 e.2 ∧ (report π H p).cap=z ∧ Known π H D p

theorem report_snoc (p : List Rate) (b : Rate) : report π H (p++[b]) = step π H (report π H p) b := by
  simp [report,List.reverse_append,replay]

theorem known_ext {D U : Bank} {p : List Rate} (h : Ext D U) (k : Known π H D p) : Known π H U p :=
  fun i y mem => h i y (k i y mem)

theorem cover_cons (D : Bank) (L : SelectTrace.Log S) (e : Bytes 32 × List S.Node) (h : Cover S pk π H D L) :
    Cover S pk π H D (e::L) := by
  intro z v mem; obtain ⟨a,ha,p,hp,hz,km⟩ := h z v mem
  exact ⟨a,List.mem_cons_of_mem _ ha,p,hp,hz,km⟩

theorem absorb_all (d : Bytes 32) (xs : List S.Node) (L : SelectTrace.Log S) (seen : (d,xs) ∈ L)
    (rs p : List Rate) (D : Bank) (pin : Pins D H) (cov : Cover S pk π H D L) (known : Known π H D p)
    (eq : p++rs=blocks S pk d xs) (post : Words → Bank → Prop)
    (done : ∀ U, Pins U H → Ext D U → Cover S pk π H U L → Known π H U (blocks S pk d xs) →
      post (result (report π H (blocks S pk d xs))) U) :
    fixedAll H (simulateQ (impl π) (Phase.absorb d (result (report π H p)) rs)) D post := by
  induction rs generalizing p D with
  | nil =>
    have e : p=blocks S pk d xs := by simpa using eq
    exact e ▸ done D pin (fun _ _ h => h) cov (e ▸ known)
  | cons b rs ih =>
    simp only [Phase.absorb,simulateQ_bind,simulateQ_spec_query,impl]
    let pr := report π H p
    let u := advance π H D pr b
    have pin' := advance_pins π H D pr b pin
    have sub := advance_ext π H D pr b pin
    have eq' : (p++[b])++rs=blocks S pk d xs := by simpa using eq
    have k' : Known π H u (p++[b]) := by
      unfold Known; rw [report_snoc]; exact advance_known π H D pr b pin known
    have cover' : Cover S pk π H u L := by
      intro z v last
      rcases advance_origin π H D pr b z v last with prev|new
      · obtain ⟨e,he,qs,hp,hz,kn⟩ := cov z v prev
        exact ⟨e,he,qs,hp,hz,known_ext π H sub kn⟩
      · exact ⟨(d,xs),seen,p++[b],⟨rs,eq'⟩,(report_snoc π H p b ▸ new.symm),k'⟩
    apply fixed_bind H _ _ D (fun v d => v=result (step π H pr b) ∧ d=u) post
    · exact read_step π H D pr b _ ⟨rfl,rfl⟩
    · rintro w U ⟨rfl,rfl⟩
      rw [← report_snoc π H]
      exact ih _ u pin' cover' k' eq' (fun dst a b c e => done dst a (ext_trans sub b) c e)

theorem hash_all (d : Bytes 32) (xs : List S.Node) (L : SelectTrace.Log S) (D : Bank) (pin : Pins D H)
    (cov : Cover S pk π H D L) (post : S.Node → Bank → Prop)
    (done : ∀ U, Pins U H → Ext D U → Cover S pk π H U ((d,xs)::L) → Known π H U (blocks S pk d xs) →
      post (SkFormat.split S (result (report π H (blocks S pk d xs)))).1 U) :
    fixedAll H (simulateQ (impl π) (Phase.evalHash S pk d xs)) D post := by
  simp only [Phase.evalHash,simulateQ_bind,simulateQ_pure]
  apply fixed_bind H _ (fun w => pure (SkFormat.split S w).1) D (fun w U => post (SkFormat.split S w).1 U) post _ (fun _ _ h => h)
  have zero : result (report π H [])=0 := replay_result π H []
  rw [← zero]
  exact absorb_all S pk π H d xs _ (List.mem_cons_self ..) _ [] D pin (cover_cons S pk π H D L _ cov)
    (by intro i y mem; contradiction) rfl _ done
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.hash_all
