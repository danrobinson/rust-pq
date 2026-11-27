import Parallel.KeygenPlatforms
import Slhdsa.Proofs.ShakeApi
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section
namespace S2
variable [e : Engine hash.Seed] [host : Host]

def api.keygen
  (N : Std.Usize) (p : params.Params) (seeds : Slice Std.U8)
  (sk : Slice Std.U8) (pk : Slice Std.U8) :
  Result ((Slice Std.U8) × (Slice Std.U8))
  := do
  let sk_seed ← util.block N seeds 0#usize
  let sk_prf ← util.block N seeds 1#usize
  let pk_seed ← util.block N seeds 2#usize
  slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk

theorem public_keygen {N : Usize} (p : params.Params) (hp : PN p N) (seeds sk pk : Slice U8)
    (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val)
    (keys : ParallelKeygenHost.KeyPair e host.x86 host.threads host.pool (N:=N) p) :
    api.keygen N p seeds sk pk ⦃ out =>
      (bytes out.1.val, bytes out.2.val)=Spec.slhKeygenInternal (paramsS p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ := by
  unfold api.keygen
  let* ⟨skSeed,h1⟩ ← block_spec
  let* ⟨skPrf,h2⟩ ← block_spec
  let* ⟨pkSeed,h3⟩ ← block_spec
  apply WP.spec_mono (keys skSeed skPrf pkSeed sk pk ks ps)
  intro out proof
  simpa only [←bytes_block_N p hp seeds skSeed 0 h1,←bytes_block_N p hp seeds skPrf 1 h2,
    ←bytes_block_N p hp seeds pkSeed 2 h3] using proof
end S2
namespace Sh
variable [e : Engine ShakeSeed] [host : Host]

def shake.api.keygen
  (N : Std.Usize) (p : params.Params) (seeds : Slice Std.U8)
  (sk : Slice Std.U8) (pk : Slice Std.U8) :
  Result ((Slice Std.U8) × (Slice Std.U8))
  := do
  let sk_seed ← util.block N seeds 0#usize
  let sk_prf ← util.block N seeds 1#usize
  let pk_seed ← util.block N seeds 2#usize
  shake.slh.slh_keygen_internal p sk_seed sk_prf pk_seed sk pk

theorem public_keygen {N : Usize} (p : params.Params) (hp : PN p N) (seeds sk pk : Slice U8)
    (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val)
    (keys : ShNode.KeyPair e host.x86 host.threads host.pool (N:=N) p) :
    shake.api.keygen N p seeds sk pk ⦃ out =>
      (bytes out.1.val, bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ := by
  unfold shake.api.keygen
  let* ⟨skSeed,h1⟩ ← block_spec
  let* ⟨skPrf,h2⟩ ← block_spec
  let* ⟨pkSeed,h3⟩ ← block_spec
  apply WP.spec_mono (keys skSeed skPrf pkSeed sk pk ks ps)
  intro out proof
  simpa only [←bytes_block_N p hp seeds skSeed 0 h1,←bytes_block_N p hp seeds skPrf 1 h2,
    ←bytes_block_N p hp seeds pkSeed 2 h3] using proof
end Sh

theorem s2_arm_public [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features] {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @S2.api.keygen (@arm cpu features)
      ⟨false,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (paramsS p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @S2.public_keygen (@arm cpu features) ⟨false,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (arm_keys p hp threads pool)

theorem s2_x86_public {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @S2.api.keygen (x86)
      ⟨true,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (paramsS p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @S2.public_keygen (x86) ⟨true,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (x86_keys p hp threads pool)

theorem sh_linux_public {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.api.keygen (@ShNode.engine Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream p false) (ShNode.detector KldispRust.shake256.parallel.available))
      ⟨false,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @Sh.public_keygen (@ShNode.engine Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives Kldisp.machine ShakeForestLinux.slhdsa.ShakeBatch.scalarStream p false) (ShNode.detector KldispRust.shake256.parallel.available)) ⟨false,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (ShNode.linux_keys p hp threads pool)

theorem sh_apple_public (sha3 : Bool) {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.api.keygen (@ShNode.engine (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream p true) (ShNode.detector (ok true)))
      ⟨false,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @Sh.public_keygen (@ShNode.engine (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives (AppleHybrid.machine sha3) ShakeForestApple.slhdsa.ShakeBatch.scalarStream p true) (ShNode.detector (ok true))) ⟨false,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (ShNode.apple_keys sha3 p hp threads pool)

theorem sh_x86_public {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome)
    (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    @Sh.shake.api.keygen (@ShNode.engine Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream p true) (ShNode.detector KxdispatchRust.shake256.parallel.available))
      ⟨true,threads,pool⟩ N p seeds sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (Shake.params p)
        (Spec.block (paramsS p) (bytes seeds.val) 0) (Spec.block (paramsS p) (bytes seeds.val) 1)
        (Spec.block (paramsS p) (bytes seeds.val) 2) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄ :=
  @Sh.public_keygen (@ShNode.engine Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream (@ShNode.primitives Kxdispatch.machine ShakeForestX86.slhdsa.ShakeBatch.scalarStream p true) (ShNode.detector KxdispatchRust.shake256.parallel.available)) ⟨true,threads,pool⟩ N p hp seeds sk pk ss ks ps
    (ShNode.x86_keys p hp threads pool)
end
end slhdsa.ParallelKeygenHost
