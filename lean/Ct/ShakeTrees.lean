import Ct.ShakeHash
import Ct.Wots

/-! Seed-independent traces for WOTS chains, XMSS, FORS, and SHAKE key generation. -/

open Aeneas Aeneas.Std Ct slhdsa_leak

namespace Ct.Shake

set_option maxHeartbeats 1000000

@[ct_rel] theorem chain {N : Usize} (v v' s s' : Array U8 N) (a : slhdsa.address.Adrs) (j e : U32) :
    Rel (shake.wots.chain v s a j e) (shake.wots.chain v' s' a j e) (fun _ _ => True) := by
  unfold shake.wots.chain shake.wots.chain_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x,i⟩ ⟨y,i'⟩ (rfl : i=i')
  unfold shake.wots.chain_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem secret {N : Usize} (sk sk' s s' : Array U8 N) (a : slhdsa.address.Adrs) (j : Usize) :
    Rel (shake.wots.secret sk s a j) (shake.wots.secret sk' s' a j) (fun _ _ => True) := by
  unfold shake.wots.secret
  ct_steps

@[ct_rel] theorem wots_pk_loop {N : Usize} (sk sk' s s' : Array U8 N) (layer : U32)
    (tree : U64) (typ pair w2 w3 : U32) (a b : slhdsa.shake256.Sponge) (i : Usize)
    (hp : a.pos=b.pos) :
    Rel (shake.wots.wots_pk_gen_loop sk s layer tree typ pair w2 w3 a i)
      (shake.wots.wots_pk_gen_loop sk' s' layer tree typ pair w2 w3 b i) (fun x y => x.pos=y.pos) := by
  unfold shake.wots.wots_pk_gen_loop
  refine Rel.loop (fun x y => x.1.pos=y.1.pos ∧ x.2=y.2) ?_ ⟨hp,rfl⟩
  rintro ⟨v,j⟩ ⟨w,j'⟩ ⟨hv,(rfl : j=j')⟩
  unfold shake.wots.wots_pk_gen_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem wots_pk_gen {N : Usize} (sk sk' s s' : Array U8 N) (a : slhdsa.address.Adrs) :
    Rel (shake.wots.wots_pk_gen sk s a) (shake.wots.wots_pk_gen sk' s' a) (fun _ _ => True) := by
  unfold shake.wots.wots_pk_gen
  ct_steps

@[ct_rel] theorem wots_sign {N : Usize} (msg sk sk' s s' : Array U8 N) (a : slhdsa.address.Adrs) :
    Rel (shake.wots.wots_sign msg sk s a) (shake.wots.wots_sign msg sk' s' a)
      (fun x y => x.length=y.length) := by
  unfold shake.wots.wots_sign
  apply Rel.bind_refl
  intro digits _
  unfold shake.wots.wots_sign_loop
  refine Rel.loop (fun x y => x.1.length=y.1.length ∧ x.2=y.2) ?_ ⟨rfl,rfl⟩
  rintro ⟨v,j⟩ ⟨w,j'⟩ ⟨hv,(rfl : j=j')⟩
  unfold shake.wots.wots_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sk_gen {N : Usize} (sk sk' s s' : Array U8 N) (a : slhdsa.address.Adrs) (i : U32) :
    Rel (shake.fors.fors_sk_gen sk s a i) (shake.fors.fors_sk_gen sk' s' a i) (fun _ _ => True) := by
  unfold shake.fors.fors_sk_gen
  ct_steps

/-- `xmss_node`, by strong induction on the height. -/
@[ct_rel] theorem xmss_node {N : Usize} (sk sk' : Array U8 N) (i z : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.xmss.xmss_node sk i z seed adrs) (shake.xmss.xmss_node sk' i z seed' adrs)
      (fun _ _ => True) := by
  induction hz : z.val using Nat.strong_induction_on generalizing i z with
  | _ n ih =>
    rw [shake.xmss.xmss_node, shake.xmss.xmss_node]
    ct_steps
    all_goals first
      | (simp only [Ct.Facts.erase_liftM] at *
         ct_facts
         refine ih _ ?_ _ _ rfl
         simp_all; omega)

/-- `fors_node`, by strong induction on the height. -/
@[ct_rel] theorem fors_node {N : Usize} (sk sk' : Array U8 N) (i z : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.fors.fors_node sk i z seed adrs) (shake.fors.fors_node sk' i z seed' adrs)
      (fun _ _ => True) := by
  induction hz : z.val using Nat.strong_induction_on generalizing i z with
  | _ n ih =>
    rw [shake.fors.fors_node, shake.fors.fors_node]
    ct_steps
    all_goals first
      | (simp only [Ct.Facts.erase_liftM] at *
         ct_facts
         refine ih _ ?_ _ _ rfl
         simp_all; omega)

theorem climb_loop_body {N : Usize} (auth auth' : Slice U8) (first : Usize) (height : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (node node' : Array U8 N)
    (index k : U32) (h : auth.length = auth'.length) :
    Rel (shake.xmss.climb_loop.body auth first height seed adrs node index k)
      (shake.xmss.climb_loop.body auth' first height seed' adrs node' index k)
      (CFRel (fun p q => p.2 = q.2) (fun _ _ => True)) := by
  unfold shake.xmss.climb_loop.body
  ct_steps
  all_goals simp_all

@[ct_rel] theorem climb_loop {N : Usize} (auth auth' : Slice U8) (first : Usize) (height : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (node node' : Array U8 N)
    (index k : U32) (h : auth.length = auth'.length) :
    Rel (shake.xmss.climb_loop auth first height seed adrs node index k)
      (shake.xmss.climb_loop auth' first height seed' adrs node' index k) (fun _ _ => True) := by
  unfold shake.xmss.climb_loop
  refine Rel.loop (fun p q => p.2 = q.2) ?_ rfl
  rintro ⟨x, j, l⟩ ⟨x', j', l'⟩ hj
  obtain ⟨rfl, rfl⟩ : j = j' ∧ l = l' := by simpa using hj
  exact climb_loop_body auth auth' first height seed seed' adrs x x' j l h

/-- `climb`: the index (left or right child) is public; the nodes and the authentication path
are secret (lengths only). -/
@[ct_rel] theorem climb {N : Usize} (node node' : Array U8 N) (idx : U32) (auth auth' : Slice U8)
    (first : Usize) (height : U32) (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs)
    (h : auth.length = auth'.length) :
    Rel (shake.xmss.climb node idx auth first height seed adrs)
      (shake.xmss.climb node' idx auth' first height seed' adrs) (fun _ _ => True) := by
  unfold shake.xmss.climb
  exact climb_loop auth auth' first height seed seed' adrs node node' idx _ h

theorem xmss_sign_loop_body {N : Usize} (p : slhdsa.params.Params) (sk sk' : Array U8 N) (idx : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (sig sig' : alloc.vec.Vec U8)
    (j : U32) (h : sig.length = sig'.length) :
    Rel (shake.xmss.xmss_sign_loop.body p sk idx seed adrs sig j)
      (shake.xmss.xmss_sign_loop.body p sk' idx seed' adrs sig' j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold shake.xmss.xmss_sign_loop.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem xmss_sign_loop {N : Usize} (p : slhdsa.params.Params) (sk sk' : Array U8 N)
    (idx : U32) (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs)
    (sig sig' : alloc.vec.Vec U8) (j : U32) (h : sig.length = sig'.length) :
    Rel (shake.xmss.xmss_sign_loop p sk idx seed adrs sig j) (shake.xmss.xmss_sign_loop p sk' idx seed' adrs sig' j)
      (fun p q => p.length = q.length) := by
  unfold shake.xmss.xmss_sign_loop
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact xmss_sign_loop_body p sk sk' idx seed seed' adrs x x' k hx

/-- `xmss_sign`: the message and the leaf index are public. -/
@[ct_rel] theorem xmss_sign {N : Usize} (p : slhdsa.params.Params) (m : Array U8 N)
    (sk sk' : Array U8 N) (idx : U32)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.xmss.xmss_sign p m sk idx seed adrs) (shake.xmss.xmss_sign p m sk' idx seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold shake.xmss.xmss_sign
  ct_steps

theorem fors_sign_loop0_loop0_body {N : Usize} (sk sk' : Array U8 N)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (a i idx : U32)
    (sig sig' : alloc.vec.Vec U8) (j : U32) (h : sig.length = sig'.length) :
    Rel (shake.fors.fors_sign_loop0_loop0.body sk seed adrs a i idx sig j)
      (shake.fors.fors_sign_loop0_loop0.body sk' seed' adrs a i idx sig' j)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold shake.fors.fors_sign_loop0_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0_loop0 {N : Usize} (sk sk' : Array U8 N)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (a : U32)
    (sig sig' : alloc.vec.Vec U8) (i idx j : U32) (h : sig.length = sig'.length) :
    Rel (shake.fors.fors_sign_loop0_loop0 sk seed adrs a sig i idx j)
      (shake.fors.fors_sign_loop0_loop0 sk' seed' adrs a sig' i idx j)
      (fun p q => p.length = q.length) := by
  unfold shake.fors.fors_sign_loop0_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_loop0_body sk sk' seed seed' adrs a i idx x x' k hx

theorem fors_sign_loop0_body {N : Usize} (i : U32) (sk sk' : Array U8 N)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (a : U32)
    (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i1 : U32)
    (h : sig.length = sig'.length) :
    Rel (shake.fors.fors_sign_loop0.body i sk seed adrs a ind sig i1)
      (shake.fors.fors_sign_loop0.body i sk' seed' adrs a ind sig' i1)
      (CFRel (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) (fun p q => p.length = q.length)) := by
  unfold shake.fors.fors_sign_loop0.body
  ct_steps
  all_goals (ct_facts; simp_all)

@[ct_rel] theorem fors_sign_loop0 {N : Usize} (i : U32) (sk sk' : Array U8 N)
    (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) (a : U32)
    (ind : alloc.vec.Vec U32) (sig sig' : alloc.vec.Vec U8) (i1 : U32)
    (h : sig.length = sig'.length) :
    Rel (shake.fors.fors_sign_loop0 i sk seed adrs a ind sig i1)
      (shake.fors.fors_sign_loop0 i sk' seed' adrs a ind sig' i1)
      (fun p q => p.length = q.length) := by
  unfold shake.fors.fors_sign_loop0
  refine Rel.loop (fun p q => p.1.length = q.1.length ∧ p.2 = q.2) ?_ ⟨h, rfl⟩
  rintro ⟨x, k⟩ ⟨x', k'⟩ ⟨hx, (rfl : k = k')⟩
  exact fors_sign_loop0_body i sk sk' seed seed' adrs a ind x x' k hx

/-- `fors_sign`: the digest is public (its indices select the revealed leaves and the
authentication paths). -/
@[ct_rel] theorem fors_sign {N : Usize} (p : slhdsa.params.Params) (md : Slice U8)
    (sk sk' : Array U8 N) (seed seed' : Array U8 N) (adrs : slhdsa.address.Adrs) :
    Rel (shake.fors.fors_sign p md sk seed adrs) (shake.fors.fors_sign p md sk' seed' adrs)
      (fun p q => p.length = q.length) := by
  unfold shake.fors.fors_sign
  ct_steps

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem slh_keygen_internal {N : Usize} (p : slhdsa.params.Params)
    (sk sk' prf prf' ps ps' : Array U8 N) (skb skb' pkb pkb' : Slice U8)
    (hs : skb.length = skb'.length) (hp : pkb.length = pkb'.length) :
    Rel (shake.slh.slh_keygen_internal p sk prf ps skb pkb) (shake.slh.slh_keygen_internal p sk' prf' ps' skb' pkb')
      (fun a b => a.1.length = b.1.length ∧ a.2.length = b.2.length) := by
  unfold shake.slh.slh_keygen_internal shake.hash.seed_ctx
  ct_steps
  ct_side

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem keygen (N : Usize) (p : slhdsa.params.Params) (seeds seeds' sk sk' pk pk' : Slice U8)
    (h1 : seeds.length = seeds'.length) (h2 : sk.length = sk'.length) (h3 : pk.length = pk'.length) :
    Rel (shake.api.keygen N p seeds sk pk) (shake.api.keygen N p seeds' sk' pk')
      (fun a b => a.1.length = b.1.length ∧ a.2.length = b.2.length) := by
  unfold shake.api.keygen
  ct_steps

set_option maxHeartbeats 1000000 in
@[ct_rel] theorem public_key (N : Usize) (sk sk' pk pk' : Slice U8) (h1 : sk.length = sk'.length)
    (h2 : pk.length = pk'.length) :
    Rel (shake.api.public_key N sk pk) (shake.api.public_key N sk' pk') (fun a b => a.length = b.length) := by
  unfold shake.api.public_key
  ct_steps
  ct_side

end Ct.Shake
