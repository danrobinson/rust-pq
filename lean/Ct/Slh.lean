import Ct.Fors

/-!
# Constant time: `ht.rs`, `slh.rs`, `api.rs` (the relational lemmas)

* Key generation (`slh_keygen_internal`, `api.keygen`) and `api.public_key`: no argument
  reaches the trace at all.
* The small helpers of signing (`digest_tree`, `digest_leaf`, `with_context`): only lengths.
* One layer of the hypertree signers (`ht_sign_loop.body`): given the message it signs (public:
  it is a root the verifier recomputes), the trace does not depend on the seeds. The layers are
  composed in `Ct/Sign.lean`, where the message of each layer is supplied by the simulator.
* Verification: all inputs are public; `Rel.refl` (the same run twice).
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Slh

open slhdsa_leak

@[ct_rel] theorem slh_keygen_internal (sk sk' prf prf' ps ps' : Array U8 16#usize) :
    Rel (slh.slh_keygen_internal sk prf ps) (slh.slh_keygen_internal sk' prf' ps')
      (fun _ _ => True) := by
  unfold slh.slh_keygen_internal
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem keygen (seeds seeds' : Array U8 48#usize) (sk sk' : Array U8 64#usize)
    (pk pk' : Array U8 32#usize) :
    Rel (api.keygen seeds sk pk) (api.keygen seeds' sk' pk') (fun _ _ => True) := by
  unfold api.keygen
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem public_key (sk sk' : Array U8 64#usize) :
    Rel (api.public_key sk) (api.public_key sk') (fun _ _ => True) := by
  unfold api.public_key
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem digest_tree (d d' : Slice U8) (h : d.length = d'.length) :
    Rel (slh.digest_tree d) (slh.digest_tree d') (fun _ _ => True) := by
  unfold slh.digest_tree
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem digest_leaf (d d' : Slice U8) (h : d.length = d'.length) :
    Rel (slh.digest_leaf d) (slh.digest_leaf d') (fun _ _ => True) := by
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
theorem ht_sign_loop_body (sk sk' : Array U8 16#usize) (seed seed' : slhdsa.hash.Seed)
    (sig sig' : alloc.vec.Vec U8) (root : Array U8 16#usize) (tree : U64) (leaf j : U32)
    (h : sig.length = sig'.length) :
    Rel (ht.ht_sign_loop.body sk seed sig root tree leaf j)
      (ht.ht_sign_loop.body sk' seed' sig' root tree leaf j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2.2 = q.2.2) (fun p q => p.length = q.length)) := by
  unfold ht.ht_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

/-! ## Verification: everything is public -/

@[ct_rel] theorem ht_verify (m : Array U8 16#usize) (sig : Slice U8) (seed : slhdsa.hash.Seed)
    (t : U64) (l : U32) (r : Array U8 16#usize) :
    Rel (ht.ht_verify m sig seed t l r) (ht.ht_verify m sig seed t l r)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem slh_verify_internal (m sig : Slice U8) (pk : Array U8 32#usize) :
    Rel (slh.slh_verify_internal m sig pk) (slh.slh_verify_internal m sig pk)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem slh_verify (m sig ctx : Slice U8) (pk : Array U8 32#usize) :
    Rel (slh.slh_verify m sig ctx pk) (slh.slh_verify m sig ctx pk)
      (fun a b => a = b) := (Rel.refl _).mono fun _ _ h => h.1

@[ct_rel] theorem verify (m sig ctx : Slice U8) (pk : Array U8 32#usize) :
    Rel (api.verify m sig ctx pk) (api.verify m sig ctx pk) (fun a b => a = b) :=
  (Rel.refl _).mono fun _ _ h => h.1

end Ct.Slh
