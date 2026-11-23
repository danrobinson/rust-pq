import Parentdriver.Program
import Parentarm.Funs
import Parentx86.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver
def x86 : Kernel 8#usize := ⟨GatherRust.sha256.x86.avx512_available,ParentsRust.sha512.x86.compress_parents⟩
def arm : Kernel 2#usize := ⟨ok Arm.haveSha512,PairedRust.sha512.paired.compress_parents⟩

set_option maxRecDepth 4096
theorem tree_x86 {N : Usize} :
    @Parentx86Rust.sha512.parents.parents N = treeParents x86 := by
  unfold Parentx86Rust.sha512.parents.parents treeParents
  unfold Parentx86Rust.sha512.parents.parents_active treeActive
  unfold Parentx86Rust.sha512.parents.parents_active_loop0 treeBatches
  unfold Parentx86Rust.sha512.parents.parents_active_loop0.body treeBatchStep
  unfold Parentx86Rust.sha512.parents.LANES
  rfl
theorem path_x86 {N : Usize} :
    @Parentx86Rust.sha512.parents.path_parents N = pathParents x86 := by
  unfold Parentx86Rust.sha512.parents.path_parents pathParents
  unfold Parentx86Rust.sha512.parents.path_parents_active pathActive
  unfold Parentx86Rust.sha512.parents.path_parents_active_loop0 pathBatches
  unfold Parentx86Rust.sha512.parents.path_parents_active_loop0.body pathBatchStep
  unfold Parentx86Rust.sha512.parents.LANES
  rfl
theorem tree_arm {N : Usize} :
    @ParentarmRust.sha512.parents.parents N = treeParents arm := by
  unfold ParentarmRust.sha512.parents.parents treeParents
  unfold ParentarmRust.sha512.parents.parents_active treeActive
  unfold ParentarmRust.sha512.parents.parents_active_loop0 treeBatches
  unfold ParentarmRust.sha512.parents.parents_active_loop0.body treeBatchStep
  unfold ParentarmRust.sha512.parents.LANES
  rfl
theorem path_arm {N : Usize} :
    @ParentarmRust.sha512.parents.path_parents N = pathParents arm := by
  unfold ParentarmRust.sha512.parents.path_parents pathParents
  unfold ParentarmRust.sha512.parents.path_parents_active pathActive
  unfold ParentarmRust.sha512.parents.path_parents_active_loop0 pathBatches
  unfold ParentarmRust.sha512.parents.path_parents_active_loop0.body pathBatchStep
  unfold ParentarmRust.sha512.parents.LANES
  rfl
end slhdsa.PlatformParent.Driver
