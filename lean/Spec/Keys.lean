import Spec.SlhDsa

/-!
# Two definitions about keys

Not part of FIPS 205's algorithms: what the completeness statements
(`Spec/Correctness.lean`, `Slhdsa/ApiTheorems.lean`) say about a private key.
-/

namespace Spec

/-- A private key is well formed when its last block is the root that key
generation (Algorithm 18) derives from its first and third blocks. -/
def KeyOk (p : Params) (sk : Bytes) : Prop :=
  block p sk 3 = xmssNode p (block p sk 0) 0 p.hp (block p sk 2) { Adrs.zero with layer := p.d - 1 }

/-- The public key held in a private key: `PK.seed ‖ PK.root`, its last two blocks. -/
def skPk (p : Params) (sk : Bytes) : Bytes := sk.drop (2 * p.n)

end Spec
