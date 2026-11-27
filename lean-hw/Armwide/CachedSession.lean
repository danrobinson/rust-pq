import Armwide.CachedPublic
import Armwide.XmssParallelBuilder

open Aeneas Aeneas.Std Result slhdsa CacheopsRust CacheopsRust.Public
namespace slhdsa.CachedArm
noncomputable section
variable [cpu : Armwide.Public.Dispatcher.Cpu] [features : Armwide.Keygen.Features]

/-- The same native constructor is used for initial cache creation and for
the missing layer-d−2 tree on mutation. -/
@[instance_reducible] def builders (N : Usize) (workers : Option Usize) : Builders N where
  sha2 := match workers with
    | none => @Armwide.XmssLeaves.Generate.cache.sha2_ops.build_xmss_tree cpu features N
    | some count => @Armwide.XmssLeaves.Generate.sha2Tree cpu features (Armwide.XmssLeaves.Generate.workerPool count) N
  shake := @slhdsa.cache.builder.nativeShake.build_xmss_tree slhdsa.cache.builder.nativeShake.scalar N

theorem keygen_sign_stream {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (toSlhParams p) N)
    (workers : Option Usize) (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val)
    (ps : pk.length=2*N.val) (capacity : Usize) (requests : List (Request N))
    (room : ∀ q ∈ requests, Room q.message.length (msgSlack N.val+257)) :
    @ArmCachedApi.CacheopsRust.Public.generatedSession cpu features N Closed.scalar (builders N workers)
      .Sha2 p seeds sk pk capacity requests ⦃ out =>
        generatedSessionPost (paramsS (toSlhParams p)) .Sha2 seeds capacity requests out ⦄ := by
  apply @ArmCachedApi.CacheopsRust.Public.keygen_then_sign_many cpu features N Closed.scalar
    inferInstance (builders N workers) p hp .Sha2
  · intro _
    cases workers with
    | none => exact Armwide.XmssLeaves.Generate.tree_kernel (toSlhParams p) hp
    | some threads => exact Armwide.XmssLeaves.Generate.parallel_tree_kernel (toSlhParams p) hp threads
  · intro h; cases h
  all_goals first | assumption | exact fun q h _ => room q h

end
end slhdsa.CachedArm
