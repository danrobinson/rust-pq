import Parallel.KeygenTree
import Cachepath.NativePlatforms
import Shakebatch.WotsDispatch

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost.ShNode
open cache.builder.nativeShake slhdsa.ShakeBatch
noncomputable section
variable [machine : Machine] [stream : Stream]
variable [ops : TreeOps]

class Detector where
  available : Usize → Result Bool

variable [d : Detector]
abbrev shake.batch.available := d.available
abbrev shake.batch.xmss_subtree {N : Usize} (sk seed : Array U8 N) (i z : U32) (a : address.Adrs) :=
  tree sk seed i z a
abbrev shake.wots.wots_pk_gen {N : Usize} := @ShakeBatch.shake.wots.wots_pk_gen machine stream d.available N

def shake.xmss.xmss_node
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (i : Std.U32) (z : Std.U32)
  (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (Array Std.U8 N)
  := do
  if z >= 1#u32
  then
    let b ← shake.batch.available N
    if b
    then shake.batch.xmss_subtree sk_seed seed i z adrs
    else
      if z = 0#u32
      then
        let a ← address.Adrs.with_type adrs address.WOTS_HASH
        let a1 ← address.Adrs.with_keypair a i
        shake.wots.wots_pk_gen sk_seed seed a1
      else
        let i1 ← 2#u32 * i
        let i2 ← z - 1#u32
        let lnode ← shake.xmss.xmss_node sk_seed i1 i2 seed adrs
        let i3 ← i1 + 1#u32
        let rnode ← shake.xmss.xmss_node sk_seed i3 i2 seed adrs
        let a ← address.Adrs.with_type adrs address.TREE
        let a1 ← address.Adrs.with_word2 a z
        let a2 ← address.Adrs.with_word3 a1 i
        shake.xmss.hash2 seed a2 lnode rnode
  else
    if z = 0#u32
    then
      let a ← address.Adrs.with_type adrs address.WOTS_HASH
      let a1 ← address.Adrs.with_keypair a i
      shake.wots.wots_pk_gen sk_seed seed a1
    else
      let i1 ← 2#u32 * i
      let i2 ← z - 1#u32
      let lnode ← shake.xmss.xmss_node sk_seed i1 i2 seed adrs
      let i3 ← i1 + 1#u32
      let rnode ← shake.xmss.xmss_node sk_seed i3 i2 seed adrs
      let a ← address.Adrs.with_type adrs address.TREE
      let a1 ← address.Adrs.with_word2 a z
      let a2 ← address.Adrs.with_word3 a1 i
      shake.xmss.hash2 seed a2 lnode rnode
partial_fixpoint


private theorem node_aux [StreamCorrect] {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : Array U8 N) (a : address.Adrs)
    (flag : Bool) (decision : d.available N=ok flag) (permutes : flag=true → PermutationCorrect)
    (positive : flag=true → 0<machine.width.val) (width : flag=true → machine.width.val≤8)
    (primitives : flag=true → TreeOpsCorrect ops p N) (n : Nat) :
    ∀ (i z : U32), z.val = n → (i.val + 1) * 2 ^ n ≤ 512 →
    shake.xmss.xmss_node sk i z seed a ⦃ r =>
      bytes r.val = Spec.xmssNode (Shake.params p) (bytes sk.val) i.val n (bytes seed.val)
        (adrsS a) ⦄ := by
  have valBound : (0#u32).val=0 := rfl
  induction n with
  | zero =>
    intro i z hz h
    rw [shake.xmss.xmss_node.eq_def]
    have hz0 : z = 0#u32 := by scalar_tac
    simp only [hz0, show ¬(1#u32 ≤ 0#u32) by decide, ↓reduceIte]
    let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
    let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
    let* ⟨ r, r_post ⟩ ← ShakeBatch.wots_pk_gen_spec d.available p hp _ _ _ flag decision permutes positive width
    rw [r_post]
    simp [a2_post, a1_post1, Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH,
      address.WOTS_HASH]
  | succ n ih =>
    intro i z hz h
    rw [shake.xmss.xmss_node.eq_def]
    have hz0 : ¬ z = 0#u32 := by scalar_tac
    have ge : 1#u32 ≤ z := by scalar_tac
    simp only [ge,ite_true,shake.batch.available,decision,bind_ok,hz0,ite_false]
    cases flag with
    | true =>
      simp only [ite_true]
      have atHeight : 2^n.succ≤512 := (Nat.le_mul_of_pos_left (2^n.succ) (Nat.succ_pos i.val)).trans h
      have small : z.val≤9 := by
        by_contra! big
        have power := Nat.pow_le_pow_right (by decide : 0<2) (show 10≤n.succ by omega)
        omega
      simpa only [hz] using tree_spec p (primitives rfl) sk seed i z a (by omega) small (hz ▸ h)
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
      have he : (2 * i.val + 2) * 2 ^ n = (i.val + 1) * 2 ^ (n + 1) := by ring
      have h1 : (2 * i.val + 1 + 1) * 2 ^ n ≤ 512 := by rw [← he] at h; exact h
      have h0 : (2 * i.val + 1) * 2 ^ n ≤ 512 :=
        le_trans (Nat.mul_le_mul_right _ (by omega)) h1
      have hb : 2 * i.val + 2 ≤ 2 ^ 32 := le_trans (Nat.le_mul_of_pos_right _ hpos) (h1.trans (by decide))
      let* ⟨ i1, i1_post ⟩ ← U32.mul_spec
      let* ⟨ i2, i2_post ⟩ ← U32.sub_spec
      step with ih i1 i2 (by omega) (by simpa [i1_post] using h0) as ⟨lnode,lnode_post⟩
      let* ⟨ i3, i3_post ⟩ ← U32.add_spec
      step with ih i3 i2 (by omega) (by simpa [i3_post,i1_post] using h1) as ⟨rnode,rnode_post⟩
      let* ⟨ a1, a1_post, a1_post1 ⟩ ← with_type_spec
      let* ⟨ a2, a2_post ⟩ ← with_word2_spec
      let* ⟨ a3, a3_post ⟩ ← with_word3_spec
      let* ⟨ r, r_post ⟩ ← Shake.hash2_spec p hp
      rw [r_post]
      simp [lnode_post, rnode_post, i1_post, i3_post, a3_post, a2_post, a1_post1, hz,
        Spec.xmssNode, adrsS, Spec.Adrs.setTypeAndClear, Spec.TREE, address.TREE]


def engine : Engine ShakeSeed where
  node := shake.xmss.xmss_node
  seedCtx := slhdsa.shake.hash.seed_ctx
  seedBytes s := bytes s.val

def KeyPair (e : Engine ShakeSeed) (x86 : Bool) (threads : Nat) (pool : PoolOutcome) {N : Usize} (p : params.Params) :=
  ∀ (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8), sk.length=4*N.val → pk.length=2*N.val →
    @Sh.shake.slh.slh_keygen_internal e ⟨x86,threads,pool⟩ N p skSeed skPrf pkSeed sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p) (bytes skSeed.val)
        (bytes skPrf.val) (bytes pkSeed.val) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄

theorem host_keys [StreamCorrect] {N : Usize} (p : params.Params) (hp : PN p N)
    (flag : Bool) (decision : d.available N=ok flag)
    (permutes : flag=true → PermutationCorrect) (positive : flag=true → 0<machine.width.val)
    (width : flag=true → machine.width.val≤8) (primitives : flag=true → TreeOpsCorrect ops p N)
    (x86 : Bool) (threads : Nat) (pool : PoolOutcome) : KeyPair engine x86 threads pool (N:=N) p := by
  intro skSeed skPrf pkSeed sk pk ss ps
  apply @Sh.caller_fips engine ⟨x86,threads,pool⟩ N p hp skSeed skPrf pkSeed sk pk ss ps
  · intro sk i z seed a _ room
    have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
    exact node_aux p hp sk seed a flag decision permutes positive width primitives z.val i z rfl (room.trans cap)
  · exact ⟨pkSeed,rfl,rfl,trivial⟩

end
end slhdsa.ParallelKeygenHost.ShNode
