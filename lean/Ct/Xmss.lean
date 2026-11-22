import Ct.Wots

/-!
# Constant time: `xmss.rs`

(The single-set tree's `lean/Ct/Xmss.lean`, with the hash length `N` and the parameter set `p`.)

`xmss_node`: nothing but the (public) position `i, z` and address reaches the trace.
`xmss_sign`, `xmss_pk_from_sig`: the message signed is public (its digits are chain lengths),
the leaf index is public; the seeds and the signature values are secret (lengths only).
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Ct.Xmss

open slhdsa_leak

/-- `xmss_node`, by strong induction on the height. -/
@[ct_rel] theorem xmss_node {N : Usize} (sk sk' : Array U8 N) (i z : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) :
    Rel (xmss.xmss_node sk i z seed adrs) (xmss.xmss_node sk' i z seed' adrs)
      (fun _ _ => True) := by
  induction hz : z.val using Nat.strong_induction_on generalizing i z with
  | _ n ih =>
    rw [xmss.xmss_node, xmss.xmss_node]
    ct_steps
    all_goals first
      | (simp only [Ct.Facts.erase_liftM] at *
         ct_facts
         refine ih _ ?_ _ _ rfl
         simp_all; omega)
      | (ct_facts; simp_all)

theorem climb_loop_body {N : Usize} (auth auth' : Slice U8) (first : Usize) (height : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (node node' : Array U8 N)
    (index k : U32) (h : auth.length = auth'.length) :
    Rel (xmss.climb_loop.body auth first height seed adrs node index k)
      (xmss.climb_loop.body auth' first height seed' adrs node' index k)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold xmss.climb_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem climb_loop {N : Usize} (auth auth' : Slice U8) (first : Usize) (height : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (node node' : Array U8 N)
    (index k : U32) (h : auth.length = auth'.length) :
    Rel (xmss.climb_loop auth first height seed adrs node index k)
      (xmss.climb_loop auth' first height seed' adrs node' index k) (fun _ _ => True) := by
  unfold xmss.climb_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j, l⟩ ⟨x', j', l'⟩ hj
  obtain ⟨rfl, rfl⟩ : j = j' ∧ l = l' := by simpa using hj
  exact climb_loop_body auth auth' first height seed seed' adrs x x' j l h

/-- `climb`: the index (left or right child) is public; the nodes and the authentication path
are secret (lengths only). -/
@[ct_rel] theorem climb {N : Usize} (node node' : Array U8 N) (idx : U32) (auth auth' : Slice U8)
    (first : Usize) (height : U32) (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs)
    (h : auth.length = auth'.length) :
    Rel (xmss.climb node idx auth first height seed adrs)
      (xmss.climb node' idx auth' first height seed' adrs) (fun _ _ => True) := by
  unfold xmss.climb
  exact climb_loop auth auth' first height seed seed' adrs node node' idx _ h

@[ct_rel] theorem xmss_pk_from_sig {N : Usize} (p : slhdsa.params.Params) (idx : U32)
    (sig sig' : Slice U8) (m : Array U8 N)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (h : sig.length = sig'.length) :
    Rel (xmss.xmss_pk_from_sig p idx sig m seed adrs) (xmss.xmss_pk_from_sig p idx sig' m seed' adrs)
      (fun _ _ => True) := by
  unfold xmss.xmss_pk_from_sig
  ct_steps

theorem xmss_sign_loop_body {N : Usize} (p : slhdsa.params.Params) (sk sk' : Array U8 N) (idx : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) (sig sig' : alloc.vec.Vec U8)
    (j : U32) (h : sig.length = sig'.length) :
    Rel (xmss.xmss_sign_loop.body p sk idx seed adrs sig j)
      (xmss.xmss_sign_loop.body p sk' idx seed' adrs sig' j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold xmss.xmss_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem xmss_sign_loop {N : Usize} (p : slhdsa.params.Params) (sk sk' : Array U8 N)
    (idx : U32) (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs)
    (sig sig' : alloc.vec.Vec U8) (j : U32) (h : sig.length = sig'.length) :
    Rel (xmss.xmss_sign_loop p sk idx seed adrs sig j) (xmss.xmss_sign_loop p sk' idx seed' adrs sig' j)
      (fun p q => p.length = q.length) := by
  unfold xmss.xmss_sign_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact xmss_sign_loop_body p sk sk' idx seed seed' adrs x x' k hx

/-- `xmss_sign`: the message and the leaf index are public. -/
@[ct_rel] theorem xmss_sign {N : Usize} (p : slhdsa.params.Params) (m : Array U8 N)
    (sk sk' : Array U8 N) (idx : U32)
    (seed seed' : slhdsa.hash.Seed N) (adrs : slhdsa.address.Adrs) :
    Rel (xmss.xmss_sign p m sk idx seed adrs) (xmss.xmss_sign p m sk' idx seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold xmss.xmss_sign
  ct_steps

end Ct.Xmss
