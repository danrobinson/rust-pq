import Ct.Fors

/-!
# Constant time: `ht.rs`, `slh.rs`, `api.rs` (the relational lemmas)

(Adapted from the main tree's `lean/Ct/Slh.lean`: the generic functions take the hash length
`N`, the parameter set `p` and the keys as slices, so the lemmas relate runs with the same `N`,
`p` and the same key and buffer *lengths*.)

* Key generation (`slh_keygen_internal`, `api.keygen`) and `api.public_key`: no argument
  reaches the trace except through the (public) lengths of the buffers.
* The small helpers of signing (`digest_tree`, `digest_leaf`, `with_context`): only lengths.
* One layer of the hypertree signer (`ht_sign_loop.body`): given the message it signs (public:
  it is a root the verifier recomputes), the trace does not depend on the seeds.
* Verification: all inputs are public; `Rel.refl` (the same run twice).
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Slh

open slhdsa_leak

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem slh_keygen_internal {N : Usize} (p : slhdsa.params.Params)
    (sk sk' prf prf' ps ps' : Array U8 N) (skb skb' pkb pkb' : Slice U8)
    (hs : skb.length = skb'.length) (hp : pkb.length = pkb'.length) :
    Rel (slh.slh_keygen_internal p sk prf ps skb pkb) (slh.slh_keygen_internal p sk' prf' ps' skb' pkb')
      (fun a b => a.1.length = b.1.length ∧ a.2.length = b.2.length) := by
  unfold slh.slh_keygen_internal
  ct_steps
  all_goals ct_side

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem keygen (N : Usize) (p : slhdsa.params.Params) (seeds seeds' sk sk' pk pk' : Slice U8)
    (h1 : seeds.length = seeds'.length) (h2 : sk.length = sk'.length) (h3 : pk.length = pk'.length) :
    Rel (api.keygen N p seeds sk pk) (api.keygen N p seeds' sk' pk')
      (fun a b => a.1.length = b.1.length ∧ a.2.length = b.2.length) := by
  unfold api.keygen
  ct_steps
  all_goals ct_side

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem public_key (N : Usize) (sk sk' pk pk' : Slice U8) (h1 : sk.length = sk'.length)
    (h2 : pk.length = pk'.length) :
    Rel (api.public_key N sk pk) (api.public_key N sk' pk') (fun a b => a.length = b.length) := by
  unfold api.public_key
  ct_steps
  all_goals ct_side

@[ct_rel] theorem digest_tree (p : slhdsa.params.Params) (d d' : Slice U8) (h : d.length = d'.length) :
    Rel (slh.digest_tree p d) (slh.digest_tree p d') (fun _ _ => True) := by
  unfold slh.digest_tree
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem digest_leaf (p : slhdsa.params.Params) (d d' : Slice U8) (h : d.length = d'.length) :
    Rel (slh.digest_leaf p d) (slh.digest_leaf p d') (fun _ _ => True) := by
  unfold slh.digest_leaf
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem with_context (m m' ctx ctx' : Slice U8) (hm : m.length = m'.length)
    (hc : ctx.length = ctx'.length) :
    Rel (slh.with_context m ctx) (slh.with_context m' ctx') (fun p q => p.length = q.length) := by
  unfold slh.with_context
  simp only [(Ct.Facts.slice_len_congr hc).symm]
  ct_steps
  all_goals (ct_facts; simp_all)

/-- One layer of `ht_sign`: the message signed (`root`) is public. -/
theorem ht_sign_loop_body {N : Usize} (p : slhdsa.params.Params) (sk sk' : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (sig sig' : alloc.vec.Vec U8) (root : Array U8 N)
    (tree : U64) (leaf j : U32) (h : sig.length = sig'.length) :
    Rel (ht.ht_sign_loop.body p sk seed sig root tree leaf j)
      (ht.ht_sign_loop.body p sk' seed' sig' root tree leaf j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2.2 = q.2.2) (fun p q => p.length = q.length)) := by
  unfold ht.ht_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

/-! ## Verification: everything is public -/

@[ct_rel] theorem ht_verify {N : Usize} (p : slhdsa.params.Params) (m : Array U8 N) (sig : Slice U8)
    (seed : slhdsa.hash.Seed N) (t : U64) (l : U32) (r : Array U8 N) :
    Rel (ht.ht_verify p m sig seed t l r) (ht.ht_verify p m sig seed t l r)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem slh_verify_internal (N : Usize) (p : slhdsa.params.Params) (m sig pk : Slice U8) :
    Rel (slh.slh_verify_internal N p m sig pk) (slh.slh_verify_internal N p m sig pk)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem slh_verify (N : Usize) (p : slhdsa.params.Params) (m sig ctx pk : Slice U8) :
    Rel (slh.slh_verify N p m sig ctx pk) (slh.slh_verify N p m sig ctx pk)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem verify (N : Usize) (p : slhdsa.params.Params) (m sig ctx pk : Slice U8) :
    Rel (api.verify N p m sig ctx pk) (api.verify N p m sig ctx pk) (fun a b => a = b) :=
  (Rel.refl _).mono fun _ _ h => h.1

end Ct.Slh
