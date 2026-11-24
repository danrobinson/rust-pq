import Ct.ShakeSigning
import Facade.Suite

/-! Public key generation and signing of each fixed-size SHAKE parameter set. -/
open Aeneas Aeneas.Std Ct

namespace Ct.Shake

/-- For correctly sized buffers the functional proof guarantees both runs return. -/
theorem keygen_trace {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (s s' sk sk' pk pk' : Slice U8)
    (hs : s.length = 3 * N.val) (hs' : s'.length = 3 * N.val)
    (hk : sk.length = 4 * N.val) (hk' : sk'.length = 4 * N.val)
    (hp₁ : pk.length = 2 * N.val) (hp₂ : pk'.length = 2 * N.val) :
    ∃ a b t, (slhdsa_leak.shake.api.keygen N p s sk pk).run = .ok (a,t) ∧
      (slhdsa_leak.shake.api.keygen N p s' sk' pk').run = .ok (b,t) := by
  obtain ⟨a, ha, _⟩ := slhdsa.spec_imp_exists (slhdsa.Shake.api_keygen_spec p hp s sk pk hs hk hp₁)
  obtain ⟨b, hb, _⟩ := slhdsa.spec_imp_exists (slhdsa.Shake.api_keygen_spec p hp s' sk' pk' hs' hk' hp₂)
  obtain ⟨t, h₁, h₂, _⟩ := (keygen N p s s' sk sk' pk pk' (hs.trans hs'.symm)
    (hk.trans hk'.symm) (hp₁.trans hp₂.symm)).same_trace
    ((slhdsa_leak.shake.api.keygen.erase_eq _ _ _ _ _).trans ha)
    ((slhdsa_leak.shake.api.keygen.erase_eq _ _ _ _ _).trans hb)
  exact ⟨a,b,t,h₁,h₂⟩

/-- A common statement for the three public wrappers of each set. The simulator receives
the public-key suffix of the signing key. Its only signature input is the returned bytes. -/
structure SuiteTraces (N S K P : Usize) (p : slhdsa.params.Params)
    (kg : Array U8 S → Array U8 K → Array U8 P → Leak (Array U8 K × Array U8 P))
    (sign : Slice U8 → Slice U8 → Array U8 K → Array U8 N → Leak (Option (alloc.vec.Vec U8)))
    (det : Slice U8 → Slice U8 → Array U8 K → Leak (Option (alloc.vec.Vec U8))) : Prop where
  keygen : ∀ s s' sk sk' pk pk', ∃ a b t,
    (kg s sk pk).run = .ok (a,t) ∧ (kg s' sk' pk').run = .ok (b,t)
  hedged : ∀ m ctx sk rnd (pk : Array U8 P), pk.val = sk.val.drop (2 * N.val) →
    ∀ sig t, (sign m ctx sk rnd).run = .ok (some sig,t) →
      (slhdsa_leak.ShakeSim.sign N p pk.to_slice m ctx sig.deref).run = .ok ((),t)
  deterministic : ∀ m ctx sk (pk : Array U8 P), pk.val = sk.val.drop (2 * N.val) →
    ∀ sig t, (det m ctx sk).run = .ok (some sig,t) →
      (slhdsa_leak.ShakeSim.signDeterministic N p pk.to_slice m ctx sig.deref).run = .ok ((),t)

macro "suite_traces" kg:ident s:ident d:ident pn:ident p:ident : tactic => `(tactic| (
  constructor
  · intro s₀ s₁ sk₀ sk₁ pk₀ pk₁
    obtain ⟨⟨a,a₁⟩,⟨b,b₁⟩,t,ha,hb⟩ := keygen_trace _ $pn:ident s₀.to_slice s₁.to_slice
      sk₀.to_slice sk₁.to_slice pk₀.to_slice pk₁.to_slice
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    unfold $kg:ident
    simp only [Leak.pure_bind, $p:ident, Std.Array.to_slice_mut]
    simp [Leak.run_bind, ha, hb, bind_ok, Leak.run_pure]
  · intro m ctx sk rnd pk hk sig t h
    unfold $s:ident at h
    simp only [Leak.pure_bind, $p:ident] at h
    exact ShakeSigning.api_sign _ $pn:ident m ctx _ (by simp) rnd _ (by simpa using hk) sig t h
  · intro m ctx sk pk hk sig t h
    unfold $d:ident at h
    simp only [Leak.pure_bind, $p:ident] at h
    exact ShakeSigning.api_sign_deterministic _ $pn:ident m ctx _ (by simp) _ (by simpa using hk) sig t h))

open slhdsa_leak.sets.shake_128s in
theorem shake_128s_traces : SuiteTraces 16#usize 48#usize 64#usize 32#usize
    slhdsa.sets.shake_128s.params.PARAMS slhdsa_leak.sets.shake_128s.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_128s.keygen slhdsa_leak.sets.shake_128s.sign
    slhdsa_leak.sets.shake_128s.sign_deterministic slhdsa.shake_128s.pn
    slhdsa_leak.sets.shake_128s.params.PARAMS.erase_eq

open slhdsa_leak.sets.shake_128f in
theorem shake_128f_traces : SuiteTraces 16#usize 48#usize 64#usize 32#usize
    slhdsa.sets.shake_128f.params.PARAMS slhdsa_leak.sets.shake_128f.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_128f.keygen slhdsa_leak.sets.shake_128f.sign
    slhdsa_leak.sets.shake_128f.sign_deterministic slhdsa.shake_128f.pn
    slhdsa_leak.sets.shake_128f.params.PARAMS.erase_eq

open slhdsa_leak.sets.shake_192s in
theorem shake_192s_traces : SuiteTraces 24#usize 72#usize 96#usize 48#usize
    slhdsa.sets.shake_192s.params.PARAMS slhdsa_leak.sets.shake_192s.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_192s.keygen slhdsa_leak.sets.shake_192s.sign
    slhdsa_leak.sets.shake_192s.sign_deterministic slhdsa.shake_192s.pn
    slhdsa_leak.sets.shake_192s.params.PARAMS.erase_eq

open slhdsa_leak.sets.shake_192f in
theorem shake_192f_traces : SuiteTraces 24#usize 72#usize 96#usize 48#usize
    slhdsa.sets.shake_192f.params.PARAMS slhdsa_leak.sets.shake_192f.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_192f.keygen slhdsa_leak.sets.shake_192f.sign
    slhdsa_leak.sets.shake_192f.sign_deterministic slhdsa.shake_192f.pn
    slhdsa_leak.sets.shake_192f.params.PARAMS.erase_eq

open slhdsa_leak.sets.shake_256s in
theorem shake_256s_traces : SuiteTraces 32#usize 96#usize 128#usize 64#usize
    slhdsa.sets.shake_256s.params.PARAMS slhdsa_leak.sets.shake_256s.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_256s.keygen slhdsa_leak.sets.shake_256s.sign
    slhdsa_leak.sets.shake_256s.sign_deterministic slhdsa.shake_256s.pn
    slhdsa_leak.sets.shake_256s.params.PARAMS.erase_eq

open slhdsa_leak.sets.shake_256f in
theorem shake_256f_traces : SuiteTraces 32#usize 96#usize 128#usize 64#usize
    slhdsa.sets.shake_256f.params.PARAMS slhdsa_leak.sets.shake_256f.keygen sign sign_deterministic := by
  suite_traces slhdsa_leak.sets.shake_256f.keygen slhdsa_leak.sets.shake_256f.sign
    slhdsa_leak.sets.shake_256f.sign_deterministic slhdsa.shake_256f.pn
    slhdsa_leak.sets.shake_256f.params.PARAMS.erase_eq

end Ct.Shake
#print axioms Ct.Shake.shake_128s_traces
#print axioms Ct.Shake.shake_128f_traces
#print axioms Ct.Shake.shake_192s_traces
#print axioms Ct.Shake.shake_192f_traces
#print axioms Ct.Shake.shake_256s_traces
#print axioms Ct.Shake.shake_256f_traces
#print axioms Ct.Shake.keygen_trace
#print axioms Ct.ShakeSigning.api_long_ctx
#print axioms Ct.Shake.xof
