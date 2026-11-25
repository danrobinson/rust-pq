import Parallel.CacheAssembly
import Parallel.CacheDispatch
import Cachepath.ShakeEndToEnd

open Aeneas Aeneas.Std Result slhdsa slhdsa.cache.endtoend
namespace CacheopsRust.cache.parallelSign

abbrev rows {N : Usize} (s : Slice (Array U8 N)) := s.val.map (fun row => bytes row.val)

private def address (p : Spec.Params) (d : Spec.Bytes) :=
  { { Spec.Adrs.zero with tree := Spec.digestTree p d }.setTypeAndClear Spec.FORS_TREE with
    keypair := Spec.digestLeaf p d }

/-- Normal worker return with evidence of the per-ticket cells and the bytes read by
assembly. A single-worker fallback has no publication obligations. -/
def Published {N : Usize} (p : Spec.Params) (sk pk r : Array U8 N) (digest : Slice U8)
    (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (result : Option (alloc.vec.Vec U8)) : Prop :=
  let d := bytes digest.val
  let md := d.take p.mdBytes
  let tree := Spec.digestTree p d
  let leaf := Spec.digestLeaf p d
  let a := address p d
  let cached := hit.map rows
  match result with
  | none => True
  | some sig => ∃ jobs cells,
    jobs.flatten.Perm (List.range (ParallelCached.activeLayers p cached*p.hp+p.k*(1+p.a))) ∧
    ParallelCached.Run jobs.length (ParallelCached.planWrites jobs (fun _ =>
      ParallelCached.desired p md (bytes sk.val) (bytes pk.val) a tree leaf cached)) jobs.length [] cells ∧
    bytes sig.val = ParallelCached.assemble p (bytes r.val) md (bytes sk.val) (bytes pk.val)
      a tree leaf (rows top) cached cells

def signatureBody {N : Usize} (p : Spec.Params) (sk pk r : Array U8 N) (digest : Slice U8) :=
  let d := bytes digest.val
  let md := d.take p.mdBytes
  let a := address p d
  let fors := Spec.forsSign p md (bytes sk.val) (bytes pk.val) a
  bytes r.val ++ fors ++ Spec.htSign p (Spec.forsPkFromSig p fors md (bytes pk.val) a)
    (bytes sk.val) (bytes pk.val) (Spec.digestTree p d) (Spec.digestLeaf p d)

theorem published_fips {N : Usize} (p : Spec.Params) (valid : p.Valid) (sk pk r : Array U8 N)
    (digest : Slice U8) (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (len : top.length=treeSize p.hp)
    (built : slhdsa.cache.Built top p (bytes sk.val) (bytes pk.val) (layerAdrs (p.d-1) 0))
    (d2 : ∀ tree, hit=some tree → tree.length=treeSize p.hp ∧
      slhdsa.cache.Built tree p (bytes sk.val) (bytes pk.val)
        (layerAdrs (p.d-2) (Spec.digestTree p (bytes digest.val) >>> ((p.d-2)*p.hp))))
    (sig : alloc.vec.Vec U8) (published : Published p sk pk r digest top hit (some sig)) :
    bytes sig.val = signatureBody p sk pk r digest := by
  obtain ⟨jobs,cells,geometry,run,bytesEq⟩ := published
  have height : p.h/p.d=p.hp := by
    have dpos : 0<p.d := by have := valid.d_ge; omega
    rw [valid.h_eq,Nat.mul_div_cancel_left _ dpos]
  apply bytesEq.trans
  apply ParallelCached.assemble_fips p valid _ _ _ _ _ _ _ _ _ _ _
    (SpecTreeOk.of_built len built) _ jobs geometry run
  · rw [← height]; exact Spec.digestTree_lt _ _
  · exact Spec.digestLeaf_lt _ valid _
  · intro nodes found
    cases hit with
    | none => cases found
    | some tree =>
      cases found
      exact SpecTreeOk.of_built (d2 tree rfl).1 (d2 tree rfl).2

/-- The parallel-enabled sha2 caller returns the FIPS signature body for both the
joined worker return and the serial fallback. -/
theorem sha2_joined {N : Usize} (worker : sha2Worker N) (p : params.Params) (hp : PN (toSlhParams p) N)
    (sk pk r : Array U8 N) (digest : Slice U8) (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (size : digest.length=p.m.val) (len : top.length=treeSize p.hp.val)
    (built : slhdsa.cache.Built top (paramsS (toSlhParams p)) (bytes sk.val) (bytes pk.val) (layerAdrs (p.d.val-1) 0))
    (d2 : ∀ tree, hit=some tree → tree.length=treeSize p.hp.val ∧
      slhdsa.cache.Built tree (paramsS (toSlhParams p)) (bytes sk.val) (bytes pk.val)
        (layerAdrs (p.d.val-2) (Spec.digestTree (paramsS (toSlhParams p)) (bytes digest.val) >>> ((p.d.val-2)*p.hp.val))))
    (workerRuns : ∀ i, sha2Prepare p pk digest=ok i →
      worker p i.md sk i.seed i.address r i.tree i.leaf top hit
        ⦃ opt => Published (paramsS (toSlhParams p)) sk pk r digest top hit opt ⦄) :
    sha2Caller worker p sk pk r digest top hit
      ⦃ sig => bytes sig.val = signatureBody (paramsS (toSlhParams p)) sk pk r digest ⦄ := by
  apply sha2_dispatch worker p sk pk r digest top hit
  · exact slhdsa.cache.endtoend.sign_from_digest_spec p hp sk pk r digest top hit size len built d2
  · intro i prepared
    apply WP.spec_mono (workerRuns i prepared)
    rintro _ published sig rfl
    exact published_fips _ hp.valid sk pk r digest top hit len built d2 sig published

/-- The parallel-enabled shake caller returns the FIPS signature body for both the
joined worker return and the serial fallback. -/
theorem shake_joined {N : Usize} (worker : shakeWorker N) (p : params.Params) (hp : PN (toSlhParams p) N)
    (sk pk r : Array U8 N) (digest : Slice U8) (top : Slice (Array U8 N)) (hit : Option (Slice (Array U8 N)))
    (size : digest.length=p.m.val) (len : top.length=treeSize p.hp.val)
    (built : slhdsa.cache.Built top (Shake.params (toSlhParams p)) (bytes sk.val) (bytes pk.val) (layerAdrs (p.d.val-1) 0))
    (d2 : ∀ tree, hit=some tree → tree.length=treeSize p.hp.val ∧
      slhdsa.cache.Built tree (Shake.params (toSlhParams p)) (bytes sk.val) (bytes pk.val)
        (layerAdrs (p.d.val-2) (Spec.digestTree (Shake.params (toSlhParams p)) (bytes digest.val) >>> ((p.d.val-2)*p.hp.val))))
    (workerRuns : ∀ i, shakePrepare p pk digest=ok i →
      worker p i.md sk i.seed i.address r i.tree i.leaf top hit
        ⦃ opt => Published (Shake.params (toSlhParams p)) sk pk r digest top hit opt ⦄) :
    shakeCaller worker p sk pk r digest top hit
      ⦃ sig => bytes sig.val = signatureBody (Shake.params (toSlhParams p)) sk pk r digest ⦄ := by
  apply shake_dispatch worker p sk pk r digest top hit
  · exact slhdsa.cache.endtoend.shake.sign_from_digest_spec p hp sk pk r digest top hit size len built d2
  · intro i prepared
    apply WP.spec_mono (workerRuns i prepared)
    rintro _ published sig rfl
    have valid : (Shake.params (toSlhParams p)).Valid :=
      ⟨hp.valid.n_cases, hp.valid.lgw_eq, hp.valid.d_ge, hp.valid.d_le,
       hp.valid.hp_pos, hp.valid.hp_le, hp.valid.h_eq, hp.valid.tree_le, hp.valid.a_pos,
       hp.valid.a_le, hp.valid.k_pos, hp.valid.k_le, hp.valid.m_eq⟩
    exact published_fips _ valid sk pk r digest top hit len built d2 sig published

end CacheopsRust.cache.parallelSign
