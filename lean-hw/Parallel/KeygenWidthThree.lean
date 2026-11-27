import Parallel.KeygenPublic
import Shakebatch.WidthThreeKeygen
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section

/-- The Arm Linux worker calls the same extracted narrow SIMD node on each ticket
    and when the pool declines the job. -/
@[instance_reducible] def linuxNarrow : Engine ShakeSeed where
  node := WidthThree.linuxNode
  seedCtx := shake.hash.seed_ctx
  seedBytes s := bytes s.val

theorem linux_narrow_keys {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat)
    (pool : PoolOutcome) : ShNode.KeyPair linuxNarrow false threads pool (N:=N) p := by
  intro skSeed skPrf pkSeed sk pk ks ps
  apply @Sh.caller_fips linuxNarrow ⟨false,threads,pool⟩ N p hp skSeed skPrf pkSeed sk pk ks ps
  · intro secret i z seed a _ fits
    apply WidthThree.linuxNodeSpec p hp secret i z seed a
    have maxHeight : p.hp.val ≤ 32 := hp.valid.hp_le.trans (by decide)
    change (i.val+1)*2^z.val ≤ 2^p.hp.val at fits
    exact fits.trans (Nat.pow_le_pow_right (by decide) maxHeight)
  · exact ⟨pkSeed,rfl,rfl,trivial⟩

theorem linux_narrow_public {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat)
    (pool : PoolOutcome) (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.api.keygen linuxNarrow ⟨false,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @Sh.public_keygen linuxNarrow ⟨false,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (linux_narrow_keys p hp threads pool)

end
end slhdsa.ParallelKeygenHost
