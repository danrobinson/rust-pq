import Parallel.RawChunkFields
import Parallel.RawForestCells
import Parallel.AuthTableHosted
import Parallel.LeafTable
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawWorker
open WidthEight.Ticket ParallelRootWalk ParallelAuthTable ParallelXmssTicket ParallelSignJoin

noncomputable def assembleAuth {N : Usize} (host : Host) (d w : Usize) (layers : Layers)
    (metas : ParallelRawChunks.Metadata) (slots : Slots N) (seed : Array U8 N) :=
  match host with
  | .apple _ => AuthTableApple.slhdsa.ParallelAuthTable.auth_table d w layers metas slots seed
  | .linuxArm => AuthTableLinux.slhdsa.ParallelAuthTable.auth_table d w layers metas slots seed
  | .x86 => AuthTableX86.slhdsa.ParallelAuthTable.auth_table d w layers metas slots seed

theorem auth_spec {N : Usize} (host : Host) (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (tree leaf : Nat) (layers : Layers) (metas : ParallelRawChunks.Metadata) (slots : Slots N)
    (layout : LayerTable p.hp.val tree leaf p.d.val layers) (fields : ParallelRawChunks.Fields p sk seed tree leaf metas slots) :
    assembleAuth host (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) layers metas slots seed ⦃ out =>
      PublishedAuth (Shake.params p) (bytes sk.val) (bytes seed.val) tree leaf p.d.val out ⦄ := by
  have d : (UScalar.cast .Usize p.d).val=p.d.val := by scalar_tac
  have w : (UScalar.cast .Usize p.hp).val=p.hp.val := by scalar_tac
  cases host with
  | apple sha3 =>
    simpa only [assembleAuth,d,w] using
      AuthTableApple.slhdsa.ParallelAuthTable.published_auth p hp (bytes sk.val) seed tree leaf
        (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) layers metas slots w (by simpa only [d,w] using layout)
        (by simpa only [d,w] using fields.1) (by simpa only [d,w] using fields.2)
  | linuxArm =>
    simpa only [assembleAuth,d,w] using
      AuthTableLinux.slhdsa.ParallelAuthTable.published_auth p hp (bytes sk.val) seed tree leaf
        (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) layers metas slots w (by simpa only [d,w] using layout)
        (by simpa only [d,w] using fields.1) (by simpa only [d,w] using fields.2)
  | x86 =>
    simpa only [assembleAuth,d,w] using
      AuthTableX86.slhdsa.ParallelAuthTable.published_auth p hp (bytes sk.val) seed tree leaf
        (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) layers metas slots w (by simpa only [d,w] using layout)
        (by simpa only [d,w] using fields.1) (by simpa only [d,w] using fields.2)

/-- The last finisher consumes the physical FORS cells, raw XMSS subtree and leaf tickets. -/
noncomputable def inputs (host : Host) (plan : PhysicalRows) (schedule : ∀ d, Schedule d) : ForestWorker :=
  fun p md sk seed a _ tree leaf _ => do
    let forest ← ParallelForestPack.pack_fors p (ParallelRawForest.cells plan p md sk seed a)
    let ls ← build_layers p tree leaf
    let (metas,slots) ← ParallelRawChunks.produce p (ParallelLeafTable.nodeFor host p) ls sk seed schedule
    let auth ← assembleAuth host (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp) ls metas slots seed
    let count := core.num.Usize.saturating_sub (UScalar.cast .Usize p.d) 1#usize
    let live ← ParallelLeafTable.leaves (ParallelLeafTable.nodeFor host p) p sk seed tree leaf count.val (schedule count.val).completed
    ok ⟨forest,auth,live,count,(schedule p.d.val).issued,(schedule p.d.val).completed⟩

theorem law (host : Host) (schedule : ∀ d, Schedule d) {N : Usize} (p : params.Params) (hp : PN p N)
    (plan : PhysicalRows) (found : lookup (Shake.params p)=some plan) : ForestLaw (inputs host plan schedule) N p := by
  intro md sk seed a r tree leaf threads enabled size treeMax leafBound address
  let node := ParallelLeafTable.nodeFor (N:=N) host p
  let count := core.num.Usize.saturating_sub (UScalar.cast .Usize p.d) 1#usize
  have num : count.val+1=p.d.val := by
    have d : 2≤p.d.val := hp.valid.d_ge
    have cast : (UScalar.cast .Usize p.d).val=p.d.val := by scalar_tac
    change (0 ⊔ ((UScalar.cast .Usize p.d).val-1)) % 2^UScalarTy.Usize.numBits + 1 = _
    rw [Nat.max_eq_right (Nat.zero_le _),Nat.mod_eq_of_lt (by
      have bound := (UScalar.cast .Usize p.d).bv.isLt
      change (UScalar.cast .Usize p.d).val < 2^UScalarTy.Usize.numBits at bound
      omega),cast];omega
  unfold inputs
  step with ParallelRawForest.pack plan p hp found md sk seed a as ⟨forest,packed⟩
  step with layer_table p hp.valid.hp_le tree leaf as ⟨ls,layout⟩
  step with ParallelRawChunks.produce_spec p hp node (ParallelLeafTable.node_law host p hp) ls sk seed tree.val leaf.val leafBound layout schedule as ⟨ms,cs,fields⟩
  step with auth_spec host p hp sk seed tree.val leaf.val ls ms cs layout fields as ⟨auth,rows⟩
  step with ParallelLeafTable.leaves_spec node p hp (ParallelLeafTable.node_law host p hp) sk seed tree leaf count.val
    (schedule count.val).issued (schedule count.val).completed (by omega) leafBound (schedule count.val).trace
    (schedule count.val).drained as ⟨live,leaves⟩
  exact ⟨packed,rows,leaves,num,(schedule _).trace,(schedule _).drained⟩

end slhdsa.ParallelRawWorker
