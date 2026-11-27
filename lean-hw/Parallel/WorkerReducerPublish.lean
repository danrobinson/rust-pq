import Parallel.WorkerReducerCut

open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety
open ParallelWorkerFrozenReads ParallelDispatchWrites ParallelPhaseOne ParallelPhaseOne.Mixed
namespace ParallelReducerPeers

/-- A successful full join must schedule a pending leader instruction. Up
to that instruction the other callbacks can only retire their last tickets
or poll READY; no cell or phase-two counter changes. -/
theorem first_leader (p : Plan N J) (next : Bool → Program (Shared N) Unit)
    {h final : Shared N} {roles lead out} (openStep : lead≠pure ())
    (valid : Valid p h roles) (history : Steps h (roles.map (Role.code p next lead)) final out)
    (normal : ∀ x∈out,x=pure ()) :
    ∃ old new roles' q, Valid p old roles' ∧ old.cells=h.cells ∧ old.counts .phase2Next=h.counts .phase2Next ∧
      roles'.length=roles.length ∧ Step old [lead] new [q] ∧
      Steps h (roles.map (Role.code p next lead)) old (roles'.map (Role.code p next lead)) ∧
      Steps new (roles'.map (Role.code p next q)) final out := by
  let start := (h,roles.map (Role.code p next lead))
  change Relation.ReflTransGen (fun (a b : Shared N × List (Program (Shared N) Unit)) =>
    Step a.1 a.2 b.1 b.2) start (final,out) at history
  generalize source : start=z at history
  suffices result : ∀ roles, z.2=roles.map (Role.code p next lead) → Valid p z.1 roles →
      ∃ old new roles' q, Valid p old roles' ∧ old.cells=z.1.cells ∧ old.counts .phase2Next=z.1.counts .phase2Next ∧
        roles'.length=roles.length ∧ Step old [lead] new [q] ∧
        Steps z.1 z.2 old (roles'.map (Role.code p next lead)) ∧
        Steps new (roles'.map (Role.code p next q)) final out by
    subst z; exact result roles rfl valid
  clear source
  induction history using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro roles shape ok
    have member : Role.leader∈roles := List.count_pos_iff.mp (ok.unique ▸ Nat.zero_lt_one)
    have ended := normal _ (shape ▸ List.mem_map_of_mem (f:=Role.code p next lead) member)
    exact False.elim (openStep ended)
  | @head a b edge more ih =>
    intro roles shape ok
    have step := edge; change Step a.1 a.2 b.1 b.2 at step; rw [shape] at step
    obtain ⟨q,worker,whereAt⟩|⟨rs,whereAt,ok',cells,count,length⟩ := observe next ok step
    · exact ⟨a.1,b.1,roles,q,ok,rfl,rfl,rfl,worker,shape ▸ .refl,whereAt ▸ more⟩
    · obtain ⟨old,new,ts,q,v,c,n,l,w,before,after⟩ := ih rs whereAt ok'
      exact ⟨old,new,ts,q,v,c.trans cells,n.trans count,l.trans length,w,.head edge before,after⟩

/-- OnceLock.set with its returned Result discarded, as in the three Rust
output publications. The occupied-cell case leaves the old value intact. -/
def store (pub : Publication N) (after : Program (Shared N) Unit) : Program (Shared N) Unit :=
  .vis (.atomic (put pub.key pub.value)) (fun _ => after)

def stores (ws : List (Publication N)) (after : Program (Shared N) Unit) : Program (Shared N) Unit :=
  ws.foldr store after

theorem stores_cut (p : Plan N J) (next : Bool → Program (Shared N) Unit) {h final : Shared N} {roles out}
    (ws : List (Publication N)) (after : Program (Shared N) Unit)
    (distinct : (ws.map Publication.key).Nodup) (empty : ∀ w∈ws,h.cells w.key=none)
    (valid : Valid p h roles) (history : Steps h (roles.map (Role.code p next (stores ws after))) final out)
    (normal : ∀ x∈out,x=pure ()) :
    ∃ mid rs, Valid p mid rs ∧ Changed h mid ws ∧ rs.length=roles.length ∧
      Steps mid (rs.map (Role.code p next after)) final out := by
  induction ws generalizing roles h with
  | nil => exact ⟨h,roles,valid,Changed.initial _,rfl,history⟩
  | cons w ws ih =>
    let tail := stores ws after
    change Steps h (roles.map (Role.code p next (store w tail))) final out at history
    have live : store w tail ≠ pure () := fun bad => not_vis_ret bad.symm
    obtain ⟨old,new,rs,q,ok,cells,count,length,own,_,rest⟩ := first_leader p next live valid history normal
    obtain ⟨rfl,rfl⟩ := own.unique_worker (Step.atomic old [] [] _ _)
    have fresh : old.cells w.key=none := (congrFun cells _).trans (empty w List.mem_cons_self)
    have still : Valid p (put w.key w.value old) rs := by
      simp [put,slot,fresh]; exact ⟨ok.unique,ok.waiting,ok.used,ok.space⟩
    simp only [List.map_cons,List.nodup_cons] at distinct
    have vacant (u) (mem : u∈ws) : (put w.key w.value old).cells u.key=none := by
      have neq : w.key≠u.key := fun eq => distinct.1 (eq ▸ List.mem_map_of_mem mem)
      simpa [put,slot,fresh,ParallelWorkerHeap.frame _ _ _ neq,cells] using empty u (List.mem_cons_of_mem _ mem)
    obtain ⟨mid,rs',good,changed,l,done⟩ := ih distinct.2 vacant still rest
    exact ⟨mid,rs',good,(changed.prepend w fresh).peer cells count,l.trans length,done⟩

def releasing (p : Plan N J) (next : Bool → Program (Shared N) Unit) : Program (Shared N) Unit :=
  publish >>= fun _ => throughWait p.worker next

def Role.lateFlag : Role → Bool := Role.needsFetch

/-- The release store changes only READY. The last finisher still owes an
exit fetch and so joins the late group at release. -/
theorem release_cut (p : Plan N J) (next : Bool → Program (Shared N) Unit) {h final : Shared N} {roles out}
    (valid : Valid p h roles) (history : Steps h (roles.map (Role.code p next (releasing p next))) final out)
    (normal : ∀ x∈out,x=pure ()) :
    ∃ mid : Shared N, ∃ flags : List Bool, mid.ready=true ∧ mid.cells=h.cells ∧ mid.counts .phase2Next=h.counts .phase2Next ∧
      p.jobs.length≤mid.counts .phase1Next ∧ mid.counts .phase1Next+flags.countP id<2^System.Platform.numBits ∧
      flags.length=roles.length ∧ Steps mid (flags.map (fun b => if b then throughWait p.worker next else afterWait next)) final out := by
  have live : releasing p next ≠ pure () := by
    unfold releasing ParallelWorkerRuntime.publish
    rw [vis_bind]; exact fun bad => not_vis_ret bad.symm
  obtain ⟨old,new,rs,q,ok,cells,count,length,own,_,rest⟩ := first_leader p next live valid history normal
  obtain ⟨rfl,rfl⟩ := own.unique_worker (publish_step old (fun _ => throughWait p.worker next) [] [])
  refine ⟨{old with ready := true},rs.map Role.needsFetch,rfl,cells,count,ok.used,?_,by simpa using length,?_⟩
  · simpa [List.countP_map] using ok.space
  · rw [List.map_map]
    convert rest using 2
    funext x; cases x <;> rfl

end ParallelReducerPeers
