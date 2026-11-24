import Integration.SlhDsaShakeXofTcr

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
variable (S : Sha2Set) {N : ℕ}
abbrev SingletonRow := Bytes 32 × S.Node → S.Node
abbrev FitsSingleton := 2*S.vp.params.n + 32 ≤ N
private theorem fits (cap : FitsSingleton S (N := N)) (m : S.Node) :
    S.vp.params.n + 32 + S.vp.params.n * [m].length ≤ N := by
  unfold FitsSingleton at cap
  simp; omega

def singletonEmbedding (cap : FitsSingleton S (N := N)) (pk : S.Node) :=
  thEmb S pk (fun x => [x]) (fun _ _ h => (List.cons.inj h).1) (fits S cap)

noncomputable abbrev replaceSingleton (cap : FitsSingleton S (N := N)) (pk : S.Node) (g : ShakeApi.RawTable S N)
    (r : SingletonRow S) := write (singletonEmbedding S cap pk) g r

theorem replacedF (cap : FitsSingleton S (N := N)) (g : ShakeApi.RawTable S N) (pk : S.Node)
    (r : SingletonRow S) (a : Bytes 32) (m : S.Node) :
    (ShakeApi.primitives S (ShakeApi.extend (replaceSingleton S cap pk g r))).Thash pk a [m] = r (a,m) :=
  thLeaf S pk _ _ (fits S cap) g r a m

theorem collection_local (cap : FitsSingleton S (N := N)) (g : ShakeApi.RawTable S N) (pk : S.Node)
    (r t : SingletonRow S) (a : Bytes 32) (xs : List S.Node) (h : ∀ m, r (a,m) = t (a,m)) :
    (ShakeApi.primitives S (ShakeApi.extend (replaceSingleton S cap pk g r))).Thash pk a xs =
    (ShakeApi.primitives S (ShakeApi.extend (replaceSingleton S cap pk g t))).Thash pk a xs :=
  thLocal S pk _ _ (fits S cap) g r t a xs h

theorem average_singleton (cap : FitsSingleton S (N := N)) (pk : S.Node) (f : ShakeApi.RawTable S N → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ g, unifW _ g * ∑ r : SingletonRow S, unifW _ r * f (replaceSingleton S cap pk g r) :=
  resample (singletonEmbedding S cap pk) (node_le_digest S) f

theorem average_seed (seeds : ProbComp S.Node) (f : ShakeApi.RawTable S N → S.Node → ℝ≥0∞) :
    (∑ g, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) =
    ∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g, unifW _ g * f g pk := mean_seed seeds f
end Reduction.ShakeXof
