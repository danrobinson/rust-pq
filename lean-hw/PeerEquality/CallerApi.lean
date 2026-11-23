import PeerEquality.Callers

namespace slhdsa.PeerCall
open Spec

inductive Outcome (A : Type) where
  | success (x : A)
  | error
  | panic
  deriving Repr

/-- The public context bound is checked before the raw randomizer conversion. -/
def signEntry (c : Children) (p : Params) (k : Key) (m : List Bytes) (ctx : Bytes)
    (rand : Option Bytes) : Outcome Signature :=
  if ctx.length > 255 then .error
  else if (rand.getD k.publicSeed).length = p.n then .success (rawSign c p k (contextParts ctx m) rand)
  else .panic

theorem sign_entry_rejects (c : Children) (p : Params) (k : Key) (m : List Bytes) (ctx : Bytes)
    (rand : Option Bytes) (bad : 255 < ctx.length) : signEntry c p k m ctx rand = .error := by
  simp [signEntry,bad]

theorem sign_entry_wrong_randomness (c : Children) (p : Params) (k : Key) (m : List Bytes) (ctx rand : Bytes)
    (fits : ctx.length ≤ 255) (bad : rand.length ≠ p.n) :
    signEntry c p k m ctx (some rand) = .panic := by simp [signEntry,Nat.not_lt.mpr fits,bad]

theorem sign_entry_accepted (c : Children) (p : Params) (laws : ChildLaws c p) (positive : 0 < p.d)
    (k : Key) (shape : k.Shape p) (m : List Bytes) (ctx : Bytes) (rand : Option Bytes)
    (fits : ctx.length ≤ 255) (size : (rand.getD k.publicSeed).length = p.n) :
    ∃ sig, signEntry c p k m ctx rand = .success sig ∧
      some sig.bytes = slhSign p m.flatten ctx k.bytes (rand.getD k.publicSeed) := by
  refine ⟨rawSign c p k (contextParts ctx m) rand, by simp [signEntry,Nat.not_lt.mpr fits,size], ?_⟩
  simpa [signCtx,fits] using sign_context c p laws positive k shape m ctx rand

/-- A failed RNG draw returns the public error before any child hash is called.
A successful draw contains the N bytes written by the RNG into the fixed array. -/
def signRng (c : Children) (p : Params) (k : Key) (m : List Bytes) (draw : Option Bytes) : Outcome Signature :=
  match draw with
  | none => .error
  | some r => signEntry c p k m [] (some r)

theorem rng_fails (c : Children) (p : Params) (k : Key) (m : List Bytes) :
    signRng c p k m none = .error := rfl

def keygenEntry (c : Children) (p : Params) (seed prf pk : Bytes) : Outcome Key :=
  if seed.length = p.n ∧ prf.length = p.n ∧ pk.length = p.n then .success (keygen c p seed prf pk)
  else .panic

theorem keygen_entry_accepted (c : Children) (p : Params) (node : (c.xmss p).node = xmssNode p)
    (a b d : Bytes) (ha : a.length=p.n) (hb : b.length=p.n) (hd : d.length=p.n) :
    ∃ k, keygenEntry c p a b d = .success k ∧ (k.bytes,k.public.bytes) = slhKeygenInternal p a b d :=
  ⟨keygen c p a b d,by simp [keygenEntry,ha,hb,hd],keygen_fips _ _ node _ _ _⟩

end slhdsa.PeerCall
