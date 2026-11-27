import Parallel.PhaseTwoJoin
import Parallel.RootTableHosted
import Shakebatch.WidthEightModel
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.Ticket
open ParallelRootWalk ParallelSigning ParallelSignJoin

def rootHost : Platform → ParallelRootWalk.Host
  | .apple sha3 => .apple sha3
  | .x86 => .x86

/-- The physical rows supplied by phase one. The actual signer builds its
layer and root tables and computes all WOTS signatures from these values. -/
structure ForestInputs (N : Usize) where
  forest : alloc.vec.Vec U8
  auth : alloc.vec.Vec (Array U8 N)
  leaves : alloc.vec.Vec (Option (Array U8 N))
  leafCount : Usize
  issued : Nat
  completed : List Nat

def ForestCorrect {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N)
    (a : address.Adrs) (tree : U64) (leaf : U32) (s : ForestInputs N) : Prop :=
  let P := Shake.params p
  bytes s.forest.val=(ParallelCached.forsRows P (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)).flatten ∧
  PublishedAuth P (bytes sk.val) (bytes seed.val) tree.val leaf.val p.d.val s.auth ∧
  PublishedLeaves P (bytes sk.val) (bytes seed.val) tree.val leaf.val s.leafCount.val s.leaves ∧
  s.leafCount.val+1=p.d.val ∧ Trace p.d.val s.issued [] s.completed ∧ p.d.val < s.issued

noncomputable def rootInputs (host : Platform) {N : Usize} (p : params.Params) (md : Slice U8)
    (seed : Array U8 N) (a : address.Adrs) (tree : U64) (leaf : U32) (s : ForestInputs N) : Result (PublishedInputs N) := do
  let layers ← ParallelXmssTicket.build_layers p tree leaf
  let roots ← @all_roots (hosted (rootHost host)) N p (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp)
    s.forest md seed a layers s.leaves s.leafCount s.auth
  ok ⟨s.forest,s.auth,layers,roots,s.issued,s.completed⟩

theorem root_inputs (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (tree : U64) (leaf : U32) (s : ForestInputs N)
    (mdLen : md.length=(Shake.params p).mdBytes) (leafBound : leaf.val<2^p.hp.val)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32)
    (source : ForestCorrect p md sk seed a tree leaf s) :
    rootInputs host p md seed a tree leaf s ⦃ out => InputsCorrect p md sk seed a tree leaf out ⦄ := by
  obtain ⟨forest,auth,leaves,count,trace,joinedTrace⟩ := source
  have good : (Shake.params p).Valid := Suite.valid .shake hp
  have fs : s.forest.deref.length=p.k.val*(1+p.a.val)*N.val := by
    have b := congrArg List.length forest
    rw [ParallelCached.fors_bytes,Spec.forsSign_length (Shake.params p) good,bytes_length] at b
    simpa only [vec_deref_length,Spec.Params.forsSigBytes,show (Shake.params p).k=p.k.val from rfl,
      show (Shake.params p).a=p.a.val from rfl,show (Shake.params p).n=N.val from hp.n] using b
  have part : PublishedAuth (Shake.params p) (bytes sk.val) (bytes seed.val) tree.val leaf.val s.leafCount.val s.auth :=
    ⟨(Nat.mul_le_mul_right _ (show s.leafCount.val≤p.d.val by omega)).trans auth.1,
      fun j hj => auth.2 j (by omega)⟩
  unfold rootInputs
  step with ParallelXmssTicket.layer_table p hp.valid.hp_le tree leaf as ⟨layers,table⟩
  step with @hosted_table N (rootHost host) p hp (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) s.forest md seed a layers s.leaves s.leafCount s.auth (bytes sk.val)
      tree.val leaf.val (by scalar_tac) count leafBound table leaves part (by simpa using fs) mdLen domain as ⟨roots,rootRows⟩
  exact ⟨forest,auth.1,auth.2,table,rootRows.1.ge,rootRows.2,trace,joinedTrace⟩

abbrev ForestWorker := {N : Usize} → params.Params → Slice U8 → Array U8 N → Array U8 N →
  address.Adrs → Array U8 N → U64 → U32 → Usize → Result (ForestInputs N)

noncomputable def rootsFrom (host : Platform) (worker : ForestWorker) : PhaseOne :=
  fun p md sk seed a r tree leaf threads => do
    let published ← worker p md sk seed a r tree leaf threads
    rootInputs host p md seed a tree leaf published

def ForestLaw (worker : ForestWorker) (N : Usize) (p : params.Params) : Prop :=
  ∀ (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (r : Array U8 N)
      (tree : U64) (leaf : U32) (threads : Usize), 2≤threads.val → md.length=(Shake.params p).mdBytes →
      tree.val<2^(p.h.val-p.hp.val) → leaf.val<2^p.hp.val → adrsS a={{Spec.Adrs.zero with tree:=tree.val}.setTypeAndClear
        Spec.FORS_TREE with keypair:=leaf.val} →
      worker p md sk seed a r tree leaf threads ⦃ s => ForestCorrect p md sk seed a tree leaf s ⦄

theorem joined_from_forest (host : Platform) (worker : ForestWorker) {N : Usize}
    (p : params.Params) (hp : PN p N)
    (source : ForestLaw worker N p) :
    JoinLawAt (completedJoin host (rootsFrom host worker)) N p := by
  apply joined_from_tickets host _ p hp
  intro md sk seed a r tree leaf threads enabled mdLen trees leafBound address
  unfold rootsFrom
  step with source md sk seed a r tree leaf threads enabled mdLen trees leafBound address as ⟨s,rows⟩
  apply root_inputs host p hp md sk seed a tree leaf s mdLen leafBound _ rows
  exact ⟨UScalar.eq_of_val_eq (by simpa [adrsS,Spec.Adrs.setTypeAndClear,Spec.FORS_TREE,global_simps] using congrArg Spec.Adrs.typ address),
    UScalar.eq_of_val_eq (congrArg Spec.Adrs.word2 address),
    UScalar.eq_of_val_eq (congrArg Spec.Adrs.word3 address)⟩

end slhdsa.WidthEight.Ticket
