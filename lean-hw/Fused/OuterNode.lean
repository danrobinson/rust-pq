import Fused.Outer
import Parallel.KeygenPublic
open Aeneas Aeneas.Std Result
namespace slhdsa.Fused.Outer
open ParallelKeygenHost
set_option linter.concreteInstances false
section
variable [b : Branches]

theorem node_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (i z : U32) (a : address.Adrs) (flag : Bool) (check : b.available N=ok flag)
    (room : (i.val+1)*2^z.val≤512)
    (leaves : flag=true → ∀ (addr : address.Adrs), addr.typ=address.WOTS_HASH →
      addr.word2=0#u32 → addr.word3=0#u32 →
      b.keygen sk seed addr ⦃ out => bytes out.val=Spec.wotsPkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr) ⦄)
    (tree : flag=true → 1≤z.val → z.val≤9 → b.subtree sk seed i z a ⦃ out =>
      bytes out.val=Spec.xmssNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄) :
    shake.xmss.xmss_node sk i z seed a ⦃ out =>
      bytes out.val=Spec.xmssNode (Shake.params p) (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄ := by
  cases flag with
  | false =>
    rw [off_node check]
    exact Shake.xmss_node_spec p hp sk i z seed a (by omega)
  | true =>
    rw [shake.xmss.xmss_node.eq_def]
    by_cases positive : z≥1#u32
    · have limit : z.val≤9 := by
        have h := (Nat.le_mul_of_pos_left (2^z.val) (Nat.succ_pos i.val)).trans room
        by_contra! big
        have := Nat.pow_le_pow_right (by decide : 0<2) (show 10≤z.val by omega)
        omega
      simpa only [positive,ite_true,shake.batch.available,check,bind_ok] using tree rfl (by scalar_tac) limit
    · have zero : z=0#u32 := by scalar_tac
      subst z
      simp only [positive,ite_false,ite_true,address.Adrs.with_type,address.Adrs.with_keypair,
        shake.wots.wots_pk_gen,shake.batch.available,check,bind_ok]
      apply WP.spec_mono (leaves rfl _ rfl rfl rfl)
      intro out spec
      simpa [Spec.xmssNode,adrsS,Spec.Adrs.setTypeAndClear,address.WOTS_HASH,Spec.WOTS_HASH] using spec

end

/-- The public key writer and split tickets use the same feature-dispatched
native node operation, including the feature-off recursive implementation. -/
@[instance_reducible] noncomputable def keyEngine (b : Branches) : Engine ShakeSeed where
  node := @shake.xmss.xmss_node b
  seedCtx := slhdsa.shake.hash.seed_ctx
  seedBytes s := bytes s.val

theorem keypair (b : Branches) {N : Usize} (p : params.Params) (hp : PN p N)
    (x86 : Bool) (threads : Nat) (pool : PoolOutcome)
    (node : ∀ (sk : Array U8 N) (i z : U32) (seed : Array U8 N) (a : address.Adrs), (i.val+1)*2^z.val≤512 →
      @shake.xmss.xmss_node b N sk i z seed a ⦃ out => bytes out.val=Spec.xmssNode (Shake.params p)
        (bytes sk.val) i.val z.val (bytes seed.val) (adrsS a) ⦄) :
    ShNode.KeyPair (keyEngine b) x86 threads pool (N:=N) p := by
  intro skSeed skPrf pkSeed sk pk ks ps
  apply @Sh.caller_fips (keyEngine b) ⟨x86,threads,pool⟩ N p hp skSeed skPrf pkSeed sk pk ks ps
  · intro secret i z seed a _ bound
    exact node secret i z seed a (bound.trans (Nat.pow_le_pow_right (by decide) hp.valid.hp_le))
  · exact ⟨pkSeed,rfl,rfl,trivial⟩

end slhdsa.Fused.Outer
