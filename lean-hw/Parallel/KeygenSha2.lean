import Parallel.KeygenHost
import X86key.Seed

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section

def arm [Armwide.Public.Dispatcher.Cpu] [Armwide.Keygen.Features] : Engine hash.Seed where
  node := Armwide.XmssLeaves.Node.xmss.xmss_node
  seedCtx := hash.seed_ctx
  seedBytes s := bytes s.pk_seed.val

def x86 : Engine hash.Seed where
  node := X86.Platform.node
  seedCtx := fun pk => do
    let s ← X86KeyRust.hash.seed_ctx pk
    ok (X86.Key.seedOf s)
  seedBytes s := bytes s.pk_seed.val

def KeyPair (e : Engine hash.Seed) (isX86 : Bool) (threads : Nat) (pool : PoolOutcome) {N : Usize} (p : params.Params) :=
  ∀ (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8), sk.length=4*N.val → pk.length=2*N.val →
    @S2.slh.slh_keygen_internal e ⟨isX86,threads,pool⟩ N p skSeed skPrf pkSeed sk pk ⦃ out =>
      (bytes out.1.val,bytes out.2.val)=Spec.slhKeygenInternal (paramsS p) (bytes skSeed.val)
        (bytes skPrf.val) (bytes pkSeed.val) ∧ out.1.length=4*N.val ∧ out.2.length=2*N.val ⦄

theorem arm_keys [Armwide.Public.Dispatcher.Cpu] [Armwide.Keygen.Features] {N : Usize}
    (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome) : KeyPair arm false threads pool (N:=N) p := by
  intro skSeed skPrf pkSeed sk pk ss ps
  apply @S2.caller_fips arm ⟨false,threads,pool⟩ N p hp skSeed skPrf pkSeed sk pk ss ps
  · intro sk i z s a hs room
    change (i.val+1)*2^z.val ≤ 2^p.hp.val at room
    have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
    exact Armwide.XmssLeaves.Node.node_fips p hp sk s hs a z.val i z rfl (room.trans (cap.trans (by decide)))
  · obtain ⟨s,get,pub,valid⟩ := spec_imp_exists (seed_ctx_spec hp.nok pkSeed)
    exact ⟨s,get,congrArg (fun arr : Array U8 N => bytes arr.val) pub,valid⟩

theorem x86_keys {N : Usize} (p : params.Params) (hp : PN p N) (threads : Nat) (pool : PoolOutcome) :
    KeyPair x86 true threads pool (N:=N) p := by
  intro skSeed skPrf pkSeed sk pk ss ps
  apply @S2.caller_fips x86 ⟨true,threads,pool⟩ N p hp skSeed skPrf pkSeed sk pk ss ps
  · exact fun sk i z s a hs room => X86.Platform.node_spec p hp sk i z s hs a room
  · obtain ⟨s,get,pub,valid⟩ := spec_imp_exists (X86.Key.seed_spec hp.nok pkSeed)
    exact ⟨X86.Key.seedOf s,by change Std.bind (X86KeyRust.hash.seed_ctx pkSeed) _ = _; rw [get,bind_ok],congrArg (fun arr : Array U8 N => bytes arr.val) pub,valid⟩
end
end slhdsa.ParallelKeygenHost
