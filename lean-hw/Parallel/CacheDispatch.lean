import Parallel.CacheDispatchProgram

open Aeneas Aeneas.Std Result
namespace CacheopsRust.cache.parallelSign

structure Prepared (Seed : Type) where
  zero : address.Adrs
  tree : U64
  leaf : U32
  address : address.Adrs
  seed : Seed
  md : Slice U8

/-- A pool that returns a signature must satisfy the same postcondition as the
fallback. The worker obligation is restricted to inputs the caller can produce. -/
private theorem choose {I S : Type} (prepared : Result I) (worker : I → Result (Option S))
    (fallback : I → Result S) (post : S → Prop)
    (serial : (prepared >>= fallback) ⦃ out => post out ⦄)
    (parallel : ∀ input, prepared = ok input → worker input ⦃ opt => ∀ out, opt = some out → post out ⦄) :
    (do let input ← prepared
        let opt ← worker input
        match opt with
        | none => fallback input
        | some out => ok out) ⦃ out => post out ⦄ := by
  cases e : prepared with
  | vis ev k => simp [e,bind_tc_eq,bind_vis] at serial
  | div => simp [e] at serial
  | ret input =>
    have hw := parallel input e
    simp only [bind_ok]
    apply WP.spec_bind hw
    intro opt ho
    cases opt with
    | none => simpa [e,bind_tc_eq] using serial
    | some out => exact (WP.spec_ok _).mpr (ho out rfl)


private theorem bindCong {A B : Type} {a : Result A} {f g : A → Result B}
    (eq : ∀ x, f x = g x) : Std.bind a f = Std.bind a g := congrArg (Std.bind a) (funext eq)

def sha2Prepare {N : Usize} (p : params.Params) (pk_seed : Array U8 N) (digest : Slice U8) :
    Result (Prepared (hash.Seed N)) := do
  let idx_tree ← cache.digest_tree p digest
  let idx_leaf ← cache.digest_leaf p digest
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let fors_adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := 0#usize, «end» := i }
  ok ⟨a,idx_tree,idx_leaf,fors_adrs,seed,md⟩

private def sha2Resume {N : Usize} (p : params.Params) (sk_seed r : Array U8 N)
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (i : Prepared (hash.Seed N)) : Result (alloc.vec.Vec U8) := do
    let sig_fors ← fors.fors_sign p i.md sk_seed i.seed i.address
    let s := alloc.vec.Vec.deref sig_fors
    let root ← fors.fors_pk_from_sig p s i.md i.seed i.address
    let i1 ← params.Params.sig_bytes p
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s1 ← lift (Array.to_slice r)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    let s2 := alloc.vec.Vec.deref sig_fors
    let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s2
    cache.sha2_ops.sign_from_digest_loop i.zero { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m sk_seed top_tree layer_d2_hit i.seed root sig2
      i.tree i.leaf


theorem sha2_dispatch {N : Usize} (worker : sha2Worker N) (p : params.Params)
    (sk pk r : Array U8 N) (digest : Slice U8)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (post : alloc.vec.Vec U8 → Prop)
    (serial : cache.sha2_ops.sign_from_digest p sk pk r digest top hit ⦃ out => post out ⦄)
    (parallel : ∀ i, sha2Prepare p pk digest = ok i →
      worker p i.md sk i.seed i.address r i.tree i.leaf top hit
        ⦃ opt => ∀ out, opt = some out → post out ⦄) :
    sha2Caller worker p sk pk r digest top hit ⦃ out => post out ⦄ := by
  have baseline : (sha2Prepare p pk digest >>= sha2Resume p sk r top hit) ⦃ out => post out ⦄ := by
    simpa only [sha2Prepare,sha2Resume,cache.sha2_ops.sign_from_digest,bind_tc_eq,Std.bind_assoc,bind_ok] using serial
  have proof := choose (sha2Prepare p pk digest) _ _ post baseline parallel
  simp only [sha2Caller,sha2Prepare,sha2Resume,Std.bind_assoc,bind_ok] at proof ⊢
  convert proof using 1
  repeat' (apply bindCong; intro x)
  cases x <;> rfl

def shakePrepare {N : Usize} (p : params.Params) (pk_seed : Array U8 N) (digest : Slice U8) :
    Result (Prepared (Array Std.U8 N)) := do
  let idx_tree ← cache.digest_tree p digest
  let idx_leaf ← cache.digest_leaf p digest
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let fors_adrs ← address.Adrs.with_keypair a2 idx_leaf
  let i ← params.Params.md_bytes p
  let md ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) digest { start := 0#usize, «end» := i }
  ok ⟨a,idx_tree,idx_leaf,fors_adrs,pk_seed,md⟩

private def shakeResume {N : Usize} (p : params.Params) (sk_seed r : Array U8 N)
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (i : Prepared (Array Std.U8 N)) : Result (alloc.vec.Vec U8) := do
    let sig_fors ← cache.shake_ops.fors_sign p i.md sk_seed i.seed i.address
    let s := alloc.vec.Vec.deref sig_fors
    let root ← cache.shake_ops.fors_pk_from_sig p s i.md i.seed i.address
    let i1 ← params.Params.sig_bytes p
    let sig := alloc.vec.Vec.with_capacity Std.U8 i1
    let s1 ← lift (Array.to_slice r)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s1
    let s2 := alloc.vec.Vec.deref sig_fors
    let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s2
    cache.shake_ops.sign_from_digest_loop i.zero { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m sk_seed i.seed top_tree layer_d2_hit root
      sig2 i.tree i.leaf


theorem shake_dispatch {N : Usize} (worker : shakeWorker N) (p : params.Params)
    (sk pk r : Array U8 N) (digest : Slice U8)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (post : alloc.vec.Vec U8 → Prop)
    (serial : cache.shake_ops.sign_from_digest p sk pk r digest top hit ⦃ out => post out ⦄)
    (parallel : ∀ i, shakePrepare p pk digest = ok i →
      worker p i.md sk i.seed i.address r i.tree i.leaf top hit
        ⦃ opt => ∀ out, opt = some out → post out ⦄) :
    shakeCaller worker p sk pk r digest top hit ⦃ out => post out ⦄ := by
  have baseline : (shakePrepare p pk digest >>= shakeResume p sk r top hit) ⦃ out => post out ⦄ := by
    simpa only [shakePrepare,shakeResume,cache.shake_ops.sign_from_digest,bind_tc_eq,Std.bind_assoc,bind_ok] using serial
  have proof := choose (shakePrepare p pk digest) _ _ post baseline parallel
  simp only [shakeCaller,shakePrepare,shakeResume,Std.bind_assoc,bind_ok] at proof ⊢
  convert proof using 1
  repeat' (apply bindCong; intro x)
  cases x <;> rfl

end CacheopsRust.cache.parallelSign
