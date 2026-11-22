import Ct.Sign
import Slhdsa.Theorems

/-!
# Constant time: the headline theorems

The leakage model is `Ct/Model.lean` (which primitive emits which event); the instrumented
program is `Ct/Funs.lean` (the verified program's text), and `Ct/Erase.lean` proves that it
computes exactly the verified functions. A run returning `(r, t)` returns `r` with trace `t`.

* **(K) Key generation leaks nothing**: any two runs of `slh_keygen_internal` / `api.keygen`
  have the same trace, whatever the seeds; and they do return.
* **(S) Signing leaks only what the signature shows**: for each signing entry point, if it
  returns a signature `sig` with trace `t`, then a simulator that is given only the public key
  `pk` (`= api.public_key sk`), the message, the context and `sig` returns with the same trace
  `t` (`slhdsa_leak.Sim.*`, defined in `Ct/Sign.lean`). The checked signers may return `none`
  after a failed recomputation; no claim is made then. A context longer than 255 bytes: the
  trace is fixed (or the simulator's).
* **(V) Verification**: all its inputs are public (`Ct.Slh.verify` etc. are `Rel.refl`).

The message-length hypotheses (`Room m.length 409`: the message and 409 more bytes fit, under
2^61 bytes) are those of the functional theorems; they are needed for the simulator's `PRF_msg`
(on zero keys) to return.
-/

open Aeneas Aeneas.Std Ct

namespace Ct.Theorems

/-! ## (K) Key generation -/

/-- Any two runs of `slh_keygen_internal` that return have the same trace, with no hypothesis
relating the seeds. -/
theorem keygen_internal_ct (sk_seed sk_prf pk_seed sk_seed' sk_prf' pk_seed' : Std.Array U8 16#usize) :
    Rel (slhdsa_leak.slh.slh_keygen_internal sk_seed sk_prf pk_seed)
      (slhdsa_leak.slh.slh_keygen_internal sk_seed' sk_prf' pk_seed') (fun _ _ => True) :=
  Ct.Slh.slh_keygen_internal _ _ _ _ _ _

/-- And they return: the verified keys, with one and the same trace. -/
theorem keygen_internal_trace (sk_seed sk_prf pk_seed sk_seed' sk_prf' pk_seed' : Std.Array U8 16#usize) :
    ∃ r r' t, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = .ok r ∧
      slhdsa.slh.slh_keygen_internal sk_seed' sk_prf' pk_seed' = .ok r' ∧
      (slhdsa_leak.slh.slh_keygen_internal sk_seed sk_prf pk_seed).run = .ok (r, t) ∧
      (slhdsa_leak.slh.slh_keygen_internal sk_seed' sk_prf' pk_seed').run = .ok (r', t) := by
  obtain ⟨sk, pk, h, -⟩ := slhdsa.keygen_correct sk_seed sk_prf pk_seed
  obtain ⟨sk', pk', h', -⟩ := slhdsa.keygen_correct sk_seed' sk_prf' pk_seed'
  obtain ⟨t, h1, h2, -⟩ := (keygen_internal_ct sk_seed sk_prf pk_seed sk_seed' sk_prf' pk_seed').same_trace
    ((slhdsa_leak.slh.slh_keygen_internal.erase_eq _ _ _).trans h)
    ((slhdsa_leak.slh.slh_keygen_internal.erase_eq _ _ _).trans h')
  exact ⟨_, _, t, h, h', h1, h2⟩

/-- `api.keygen`: any two runs that return have the same trace, whatever the seeds and the
previous contents of the output buffers. -/
theorem keygen_ct (seeds seeds' : Std.Array U8 48#usize) (sk sk' : Std.Array U8 64#usize)
    (pk pk' : Std.Array U8 32#usize) :
    Rel (slhdsa_leak.api.keygen seeds sk pk) (slhdsa_leak.api.keygen seeds' sk' pk')
      (fun _ _ => True) :=
  Ct.Slh.keygen _ _ _ _ _ _

theorem keygen_trace (seeds seeds' : Std.Array U8 48#usize) (sk sk' : Std.Array U8 64#usize)
    (pk pk' : Std.Array U8 32#usize) :
    ∃ r r' t, slhdsa.api.keygen seeds sk pk = .ok r ∧ slhdsa.api.keygen seeds' sk' pk' = .ok r' ∧
      (slhdsa_leak.api.keygen seeds sk pk).run = .ok (r, t) ∧
      (slhdsa_leak.api.keygen seeds' sk' pk').run = .ok (r', t) := by
  obtain ⟨r, h, -⟩ := slhdsa.spec_imp_exists (slhdsa.api_keygen_spec seeds sk pk)
  obtain ⟨r', h', -⟩ := slhdsa.spec_imp_exists (slhdsa.api_keygen_spec seeds' sk' pk')
  obtain ⟨t, h1, h2, -⟩ := (keygen_ct seeds seeds' sk sk' pk pk').same_trace
    ((slhdsa_leak.api.keygen.erase_eq _ _ _).trans h)
    ((slhdsa_leak.api.keygen.erase_eq _ _ _).trans h')
  exact ⟨r, r', t, h, h', h1, h2⟩

/-! ## (S) Signing: the trace is the simulator's -/

/-- `api.sign` (hedged, plain `slh_sign`). -/
theorem sign_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.api.sign m ctx sk addrnd).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.sign pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.api_sign m ctx sk addrnd pk hpk hm sig t h

/-- `api.sign_deterministic`. -/
theorem sign_deterministic_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.api.sign_deterministic m ctx sk).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.signDeterministic pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.api_sign_deterministic m ctx sk pk hpk hm sig t h

/-- `api.sign_checked`, when it returns a signature. -/
theorem sign_checked_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.api.sign_checked m ctx sk addrnd).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.signChecked pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.api_sign_checked m ctx sk addrnd pk hpk hm sig t h

/-- `api.sign_deterministic_checked`, when it returns a signature. -/
theorem sign_deterministic_checked_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.api.sign_deterministic_checked m ctx sk).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.signDeterministicChecked pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.api_sign_deterministic_checked m ctx sk pk hpk hm sig t h

/-- `slh_sign` (Algorithm 22). -/
theorem slh_sign_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.slh.slh_sign m ctx sk addrnd).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.sign pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.slh_sign m ctx sk addrnd pk hpk hm sig t h

/-- `slh_sign_checked`, when it returns a signature. -/
theorem slh_sign_checked_simulated (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.slh.slh_sign_checked m ctx sk addrnd).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.signChecked pk m ctx sig.deref).run = .ok ((), t) :=
  Ct.Sign.slh_sign_checked m ctx sk addrnd pk hpk hm sig t h

/-- `slh_sign_internal` (Algorithm 19). -/
theorem slh_sign_internal_simulated (m : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 152)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.slh.slh_sign_internal m sk addrnd).run = .ok (sig, t)) :
    (slhdsa_leak.Sim.signInternal pk m sig.deref).run = .ok ((), t) :=
  Ct.Sign.sign_internal m sk addrnd pk hpk hm sig t h

/-- `slh_sign_internal_checked`, when it returns a signature. -/
theorem slh_sign_internal_checked_simulated (m : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 152)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slhdsa_leak.slh.slh_sign_internal_checked m sk addrnd).run = .ok (some sig, t)) :
    (slhdsa_leak.Sim.signInternalChecked pk m sig.deref).run = .ok ((), t) :=
  Ct.Sign.sign_internal_checked m sk addrnd pk hpk hm sig t h

/-- The early exit (context longer than 255 bytes): `slh_sign`, `slh_sign_checked`,
`api.sign`, `api.sign_checked` emit only the outcome of the length test; the deterministic
signers' trace is their simulator's (on any signature argument). -/
theorem sign_long_context (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize) (s : Slice U8)
    (hc : 255 < ctx.length) :
    (slhdsa_leak.slh.slh_sign m ctx sk addrnd).run = .ok (none, [.branch true]) ∧
    (slhdsa_leak.slh.slh_sign_checked m ctx sk addrnd).run = .ok (none, [.branch true]) ∧
    (∀ t, (slhdsa_leak.api.sign m ctx sk addrnd).run = .ok (none, t) ↔ t = [.branch true]) ∧
    (∀ t, (slhdsa_leak.api.sign_checked m ctx sk addrnd).run = .ok (none, t) ↔
      t = [.branch true]) ∧
    (∃ t, (slhdsa_leak.api.sign_deterministic m ctx sk).run = .ok (none, t) ∧
      (slhdsa_leak.Sim.signDeterministic pk m ctx s).run = .ok ((), t)) ∧
    (∃ t, (slhdsa_leak.api.sign_deterministic_checked m ctx sk).run = .ok (none, t) ∧
      (slhdsa_leak.Sim.signDeterministicChecked pk m ctx s).run = .ok ((), t)) :=
  ⟨(Ct.Sign.slh_sign_long_ctx m ctx sk addrnd hc).1, (Ct.Sign.slh_sign_long_ctx m ctx sk addrnd hc).2,
    Ct.Sign.api_long_ctx m ctx sk addrnd pk s hc⟩

/-- A consequence in two-run form: two signing runs with keys of the same public key that
return the same signature (for the same message and context) have the same trace, whatever the
secret seeds and the randomness. -/
theorem sign_two_runs (m ctx : Slice U8) (sk sk' : Std.Array U8 64#usize)
    (addrnd addrnd' : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hpk' : slhdsa.api.public_key sk' = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t t' : Trace)
    (h : (slhdsa_leak.api.sign m ctx sk addrnd).run = .ok (some sig, t))
    (h' : (slhdsa_leak.api.sign m ctx sk' addrnd').run = .ok (some sig, t')) : t = t' := by
  have e := sign_simulated m ctx sk addrnd pk hpk hm sig t h
  have e' := sign_simulated m ctx sk' addrnd' pk hpk' hm sig t' h'
  rw [e] at e'
  simp only [Result.ok.injEq, Prod.mk.injEq, true_and] at e'
  exact e'

/-! ## (V) Verification: everything is public -/

theorem verify_ct (m sig ctx : Slice U8) (pk : Std.Array U8 32#usize) :
    Rel (slhdsa_leak.api.verify m sig ctx pk) (slhdsa_leak.api.verify m sig ctx pk)
      (fun a b => a = b) :=
  Ct.Slh.verify m sig ctx pk

/-! ## Headline: SHA-256 is constant time

The instrumented `sha256` on any two messages of the same length (within the size limit of the
functional theorem) returns the digests computed by the verified `slhdsa.sha256.sha256`, with
the same trace. -/

theorem sha256_trace_eq (msg msg' : Slice U8) (h : msg.length = msg'.length)
    (hr : slhdsa.Room msg.length 72) :
    ∃ d d' t, slhdsa.sha256.sha256 msg = .ok d ∧ slhdsa.sha256.sha256 msg' = .ok d' ∧
      (slhdsa_leak.sha256.sha256 msg).run = .ok (d, t) ∧
      (slhdsa_leak.sha256.sha256 msg').run = .ok (d', t) := by
  obtain ⟨d, hd, -⟩ := slhdsa.sha256_correct msg hr
  obtain ⟨d', hd', -⟩ := slhdsa.sha256_correct msg' (h ▸ hr)
  obtain ⟨t, h1, h2, -⟩ := (Ct.Sha256.sha256 msg msg' h).same_trace
    ((slhdsa_leak.sha256.sha256.erase_eq msg).trans hd)
    ((slhdsa_leak.sha256.sha256.erase_eq msg').trans hd')
  exact ⟨d, d', t, hd, hd', h1, h2⟩


end Ct.Theorems

#print axioms Ct.Theorems.keygen_internal_ct
#print axioms Ct.Theorems.keygen_internal_trace
#print axioms Ct.Theorems.keygen_ct
#print axioms Ct.Theorems.keygen_trace
#print axioms Ct.Theorems.sign_simulated
#print axioms Ct.Theorems.sign_deterministic_simulated
#print axioms Ct.Theorems.sign_checked_simulated
#print axioms Ct.Theorems.sign_deterministic_checked_simulated
#print axioms Ct.Theorems.slh_sign_simulated
#print axioms Ct.Theorems.slh_sign_checked_simulated
#print axioms Ct.Theorems.slh_sign_internal_simulated
#print axioms Ct.Theorems.slh_sign_internal_checked_simulated
#print axioms Ct.Theorems.sign_long_context
#print axioms Ct.Theorems.sign_two_runs
#print axioms Ct.Theorems.verify_ct
#print axioms Ct.Theorems.sha256_trace_eq
