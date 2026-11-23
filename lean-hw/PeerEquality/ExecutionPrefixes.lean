import PeerEquality.SignBoundary

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall

/-- Execute exactly k continuing iterations of the extracted program. -/
def runLayers {S T : Type} (body : S → Result (ControlFlow S T)) (initial : S) :
    Nat → Result S
  | 0 => ok initial
  | k+1 => do
    let s ← runLayers body initial k
    let r ← body s
    match r with
    | .cont next => ok next
    | .done _ => fail .panic

private theorem runLayers_spec {S T : Type} (body : S → Result (ControlFlow S T))
    (initial : S) (d : Nat) (inv : Nat → S → Prop) (start : inv 0 initial)
    (advance : ∀ k s, k < d → inv k s → body s ⦃ r => match r with
      | .cont t => inv (k+1) t | .done _ => False ⦄) (k : Nat) (hk : k ≤ d) :
    runLayers body initial k ⦃ s => inv k s ⦄ := by
  induction k with
  | zero => exact (WP.spec_ok _).2 start
  | succ k ih =>
    apply WP.spec_bind (ih (by omega))
    intro s hs
    apply WP.spec_bind (advance k s (by omega) hs)
    rintro (_ | _) h
    all_goals first | exact (WP.spec_ok _).2 h | contradiction

theorem sha2_verify_prefix (set : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing) {N : Usize}
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (sig : Slice U8) (seed : hash.Seed N) (hs : SeedOk seed) (xs : Usize)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (paramsS p).xmssSigBytes) (hlen : sig.length = p.d.val * xs.val)
    (msg : Array U8 N) (t0 : U64) (l0 : U32) (hl : l0.val < 2 ^ p.hp.val)
    (suite : RcSlhSha2.params set = paramsS p)
    (k : Nat) (hk : k ≤ p.d.val) :
    runLayers (fun (root,tree,leaf,j) => ht.ht_verify_loop.body p sig seed xs root tree leaf j)
      (msg,t0,l0,0#u32) k ⦃ s => let (root,tree,leaf,j) := s
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      (bytes root.val,tree.val,leaf.val) =
        boundary (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) (bytes msg.val) (bytes sig.val) (bytes seed.pk_seed.val) t0.val l0.val j.val ⦄ := by
  apply runLayers_spec (S := Array U8 N × U64 × U32 × U32) (d := p.d.val) (inv := fun k (root,tree,leaf,j) =>
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      (bytes root.val,tree.val,leaf.val) =
        boundary (Providers.sha2 set RcSlhSha2.nativeAlgorithms) (paramsS p) (bytes msg.val) (bytes sig.val) (bytes seed.pk_seed.val) t0.val l0.val j.val)
  · exact ⟨rfl, hl, rfl⟩
  · rintro i ⟨root,tree,leaf,j⟩ hi ⟨hj,hleaf,heq⟩
    apply WP.spec_mono (sha2_verify_layer set route p hp sig seed hs xs (bytes msg.val) root tree leaf j t0.val l0.val hxs hxs' hlen (by omega) hleaf suite heq)
    rintro (_ | _) h
    all_goals first | contradiction | simpa [hj] using h
  · exact hk

theorem shake_verify_prefix (impl : PeerShake.Backend.Implementation) {N : Usize}
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (sig : Slice U8) (seed : Array U8 N) (xs : Usize)
    (hxs : xs.val = (2 * N.val + 3 + p.hp.val) * N.val)
    (hxs' : xs.val = (Shake.params p).xmssSigBytes) (hlen : sig.length = p.d.val * xs.val)
    (msg : Array U8 N) (t0 : U64) (l0 : U32) (hl : l0.val < 2 ^ p.hp.val)
    (k : Nat) (hk : k ≤ p.d.val) :
    runLayers (fun (root,tree,leaf,j) => shake.ht.ht_verify_loop.body p sig seed xs root tree leaf j)
      (msg,t0,l0,0#u32) k ⦃ s => let (root,tree,leaf,j) := s
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      (bytes root.val,tree.val,leaf.val) =
        boundary (Providers.nativeShake impl (Shake.params p)) (Shake.params p) (bytes msg.val) (bytes sig.val) (bytes seed.val) t0.val l0.val j.val ⦄ := by
  apply runLayers_spec (S := Array U8 N × U64 × U32 × U32) (d := p.d.val) (inv := fun k (root,tree,leaf,j) =>
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      (bytes root.val,tree.val,leaf.val) =
        boundary (Providers.nativeShake impl (Shake.params p)) (Shake.params p) (bytes msg.val) (bytes sig.val) (bytes seed.val) t0.val l0.val j.val)
  · exact ⟨rfl, hl, rfl⟩
  · rintro i ⟨root,tree,leaf,j⟩ hi ⟨hj,hleaf,heq⟩
    apply WP.spec_mono (shake_verify_layer impl p hp sig seed xs (bytes msg.val) root tree leaf j t0.val l0.val hxs hxs' hlen (by omega) hleaf heq)
    rintro (_ | _) h
    all_goals first | contradiction | simpa [hj] using h
  · exact hk

theorem sha2_sign_prefix (set : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing) {N : Usize}
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed)
    (msg : Array U8 N) (t0 : U64) (l0 : U32) (hl : l0.val < 2 ^ p.hp.val)
    (suite : RcSlhSha2.params set = paramsS p)
    (k : Nat) (hk : k ≤ p.d.val) :
    runLayers (fun (acc,root,tree,leaf,j) => ht.ht_sign_loop.body p sk seed acc root tree leaf j)
      (alloc.vec.Vec.new U8,msg,t0,l0,0#u32) k ⦃ s => let (acc,root,tree,leaf,j) := s
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      acc.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val ∧
      (bytes acc.val,bytes root.val,tree.val,leaf.val) =
        signPrefix ((Providers.sha2 set RcSlhSha2.nativeAlgorithms).xmss (paramsS p)) (paramsS p) (bytes msg.val) (bytes sk.val) (bytes seed.pk_seed.val) t0.val l0.val j.val ⦄ := by
  apply runLayers_spec (S := alloc.vec.Vec U8 × Array U8 N × U64 × U32 × U32) (d := p.d.val) (inv := fun k (acc,root,tree,leaf,j) =>
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      acc.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val ∧
      (bytes acc.val,bytes root.val,tree.val,leaf.val) =
        signPrefix ((Providers.sha2 set RcSlhSha2.nativeAlgorithms).xmss (paramsS p)) (paramsS p) (bytes msg.val) (bytes sk.val) (bytes seed.pk_seed.val) t0.val l0.val j.val)
  · exact ⟨rfl, hl, rfl, rfl⟩
  · rintro i ⟨acc,root,tree,leaf,j⟩ hi ⟨hj,hleaf,hsize,heq⟩
    apply WP.spec_mono (sha2_sign_layer set route p hp sk seed hs (bytes msg.val) acc root tree leaf j t0.val l0.val (by omega) hleaf hsize suite heq)
    rintro (_ | _) h
    all_goals first | contradiction | simpa [hj] using h
  · exact hk

theorem shake_sign_prefix (impl : PeerShake.Backend.Implementation) {N : Usize}
    (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N) (seed : Array U8 N)
    (msg : Array U8 N) (t0 : U64) (l0 : U32) (hl : l0.val < 2 ^ p.hp.val)
    (k : Nat) (hk : k ≤ p.d.val) :
    runLayers (fun (acc,root,tree,leaf,j) => shake.ht.ht_sign_loop.body p sk seed acc root tree leaf j)
      (alloc.vec.Vec.new U8,msg,t0,l0,0#u32) k ⦃ s => let (acc,root,tree,leaf,j) := s
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      acc.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val ∧
      (bytes acc.val,bytes root.val,tree.val,leaf.val) =
        signPrefix ((Providers.nativeShake impl (Shake.params p)).xmss (Shake.params p)) (Shake.params p) (bytes msg.val) (bytes sk.val) (bytes seed.val) t0.val l0.val j.val ⦄ := by
  apply runLayers_spec (S := alloc.vec.Vec U8 × Array U8 N × U64 × U32 × U32) (d := p.d.val) (inv := fun k (acc,root,tree,leaf,j) =>
      j.val = k ∧ leaf.val < 2 ^ p.hp.val ∧
      acc.length = (2 * N.val + 3 + p.hp.val) * N.val * j.val ∧
      (bytes acc.val,bytes root.val,tree.val,leaf.val) =
        signPrefix ((Providers.nativeShake impl (Shake.params p)).xmss (Shake.params p)) (Shake.params p) (bytes msg.val) (bytes sk.val) (bytes seed.val) t0.val l0.val j.val)
  · exact ⟨rfl, hl, rfl, rfl⟩
  · rintro i ⟨acc,root,tree,leaf,j⟩ hi ⟨hj,hleaf,hsize,heq⟩
    apply WP.spec_mono (shake_sign_layer impl p hp sk seed (bytes msg.val) acc root tree leaf j t0.val l0.val (by omega) hleaf hsize heq)
    rintro (_ | _) h
    all_goals first | contradiction | simpa [hj] using h
  · exact hk

end slhdsa.PeerCall
