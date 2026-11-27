import Cachepath.Proof

open Aeneas Aeneas.Std Result

namespace slhdsa.cache

/-- The node at index i of row h in the level-contiguous cache. -/
def cachedNode {N : Usize} (tree : Slice (Array U8 N)) (hp h i : Nat) : Spec.Bytes :=
  bytes tree.val[2^(hp+1) - 2^(hp+1-h) + i]!.val

/-- Local write obligations of the builder. Neither premise requires a
recursive call to Algorithm 9. The parent premise refers only to values
in the preceding row of the same buffer. -/
structure Built {N : Usize} (tree : Slice (Array U8 N)) (p : Spec.Params)
    (sk pk : Spec.Bytes) (a : Spec.Adrs) : Prop where
  leaves : ∀ i < 2^p.hp, cachedNode tree p.hp 0 i =
    Spec.wotsPkGen p sk pk {a.setTypeAndClear Spec.WOTS_HASH with keypair := i}
  parents : ∀ h < p.hp, ∀ i < 2^(p.hp-(h+1)), cachedNode tree p.hp (h+1) i =
    Spec.H p pk {a.setTypeAndClear Spec.TREE with word2 := h+1, word3 := i}
      (cachedNode tree p.hp h (2*i) ++ cachedNode tree p.hp h (2*i+1))

theorem constructed {N : Usize} {tree : Slice (Array U8 N)} {p : Spec.Params}
    {sk pk : Spec.Bytes} {a : Spec.Adrs} (built : Built tree p sk pk a) :
    TreeContents tree p sk pk a := by
  intro h
  induction h with
  | zero => intro _ i hi; exact built.leaves i (by simpa using hi)
  | succ h ih =>
    intro height i hi
    have exp : p.hp-h = p.hp-(h+1)+1 := by omega
    have twice : 2^(p.hp-h) = 2^(p.hp-(h+1))*2 := by rw [exp, pow_succ]
    change cachedNode tree p.hp (h+1) i = _
    rw [built.parents h (by omega) i hi, Spec.xmssNode]
    unfold cachedNode
    rw [ih (by omega) (2*i) (by omega), ih (by omega) (2*i+1) (by omega)]

theorem built_xmss {N : Usize} (tree : Slice (Array U8 N)) (hp leaf : U32)
    (out : alloc.vec.Vec U8) (p : Spec.Params) (m sk pk : Spec.Bytes) (a : Spec.Adrs)
    (levels : hp.val ≤ 9) (sameHeight : hp.val = p.hp) (valid : leaf.val < 2^hp.val)
    (size : tree.length = 2^(hp.val+1)-1) (room : out.length + hp.val*N.val ≤ Usize.max)
    (built : Built tree p sk pk a) (sig : bytes out.val =
      Spec.wotsSign p m sk pk { a.setTypeAndClear Spec.WOTS_HASH with keypair := leaf.val }) :
    append_auth_path tree hp leaf out ⦃ r => bytes r.val = Spec.xmssSign p m sk leaf.val pk a ⦄ :=
  cached_xmss tree hp leaf out p m sk pk a levels sameHeight valid size room (constructed built) sig

end slhdsa.cache
