import Armplatform.ForsProgram
import Armplatform.ForsTree
import Armplatform.ForsPath
import Armplatform.Replay
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean Elab Command
namespace slhdsa.PlatformFors
def armTree := @tree .arm
def armTreeSpec := @tree_spec .arm
def armPath := @path .arm
def armPathSpec := @path_spec .arm
def x86Tree := @tree .x86
def x86TreeSpec := @tree_spec .x86
def x86Path := @path .x86
def x86PathSpec := @path_spec .x86
end slhdsa.PlatformFors

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  for (dest,target) in [(`ArmForsReplay,"arm"), (`X86ForsReplay,"x86")] do
    let select := fun suffix => Name.str `slhdsa.PlatformFors (target ++ suffix)
    PlatformProof.replay dest [
      (`slhdsa.fors.fors_batch_loop3_loop2, select "Tree"),
      (`slhdsa.fors_batch_loop3_loop2_spec, select "TreeSpec"),
      (`slhdsa.fors.fors_pk_from_sig_loop2_loop2, select "Path"),
      (`slhdsa.fors_pk_from_sig_loop2_loop2_spec, select "PathSpec")]
      #[`slhdsa.fors_batch_loop3_spec, `slhdsa.fors_pk_from_sig_loop2_spec]

namespace slhdsa.PlatformFors

private theorem bindRight {α β : Type} (r : Result α) {f g : α → Result β}
    (h : ∀ a,f a = g a) : Std.bind r f = Std.bind r g := by rw [funext h]

theorem armTreeEq : @ArmForsReplay.slhdsa.fors.fors_batch_loop3 = @Program.fors.fors_batch_loop3 .arm := by
  funext N i z pk st st5 i1 i2 i3 i4 i5 i6 blocks start stop vals lvl cnt
  unfold ArmForsReplay.slhdsa.fors.fors_batch_loop3 Program.fors.fors_batch_loop3
  congr 1
  funext q
  rcases q with ⟨b,s,e,v,l,c⟩
  change ArmForsReplay.slhdsa.fors.fors_batch_loop3.body i z pk st st5 i1 i2 i3 i4 i5 i6 b s e v l c =
    Program.fors.fors_batch_loop3.body .arm i z pk st st5 i1 i2 i3 i4 i5 i6 b s e v l c
  unfold ArmForsReplay.slhdsa.fors.fors_batch_loop3.body Program.fors.fors_batch_loop3.body
  split
  · split
    · rfl
    · simp only [armTree,tree,ne_eq,not_true_eq_false,ite_false,bind_tc_eq,Std.bind_assoc]
      repeat' (apply bindRight; intro x; try rcases x with ⟨_,_⟩)
      rfl
  · rfl

theorem armPathEq : @ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2 = @Program.fors.fors_pk_from_sig_loop2 .arm := by
  funext N sig pk st st5 adr a k blocks idx stop vals h
  unfold ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2 Program.fors.fors_pk_from_sig_loop2
  congr 1
  funext q
  rcases q with ⟨b,indices,e,v,l⟩
  change ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2.body sig pk st st5 adr a k b indices e v l =
    Program.fors.fors_pk_from_sig_loop2.body .arm sig pk st st5 adr a k b indices e v l
  unfold ArmForsReplay.slhdsa.fors.fors_pk_from_sig_loop2.body Program.fors.fors_pk_from_sig_loop2.body
  split
  · split
    · rfl
    · simp only [armPath,path,ne_eq,not_true_eq_false,ite_false,bind_tc_eq,Std.bind_assoc,lift,bind_ok]
      simp only [Array.to_slice_mut]
      repeat' (apply bindRight; intro x; try rcases x with ⟨_,_⟩)
      rfl
  · rfl
theorem x86TreeEq : @X86ForsReplay.slhdsa.fors.fors_batch_loop3 = @Program.fors.fors_batch_loop3 .x86 := by
  funext N i z pk st st5 i1 i2 i3 i4 i5 i6 blocks start stop vals lvl cnt
  unfold X86ForsReplay.slhdsa.fors.fors_batch_loop3 Program.fors.fors_batch_loop3
  congr 1
  funext q
  rcases q with ⟨b,s,e,v,l,c⟩
  change X86ForsReplay.slhdsa.fors.fors_batch_loop3.body i z pk st st5 i1 i2 i3 i4 i5 i6 b s e v l c =
    Program.fors.fors_batch_loop3.body .x86 i z pk st st5 i1 i2 i3 i4 i5 i6 b s e v l c
  unfold X86ForsReplay.slhdsa.fors.fors_batch_loop3.body Program.fors.fors_batch_loop3.body
  split
  · split
    · rfl
    · simp only [x86Tree,tree,ne_eq,not_true_eq_false,ite_false,bind_tc_eq,Std.bind_assoc]
      repeat' (apply bindRight; intro x; try rcases x with ⟨_,_⟩)
      rfl
  · rfl

theorem x86PathEq : @X86ForsReplay.slhdsa.fors.fors_pk_from_sig_loop2 = @Program.fors.fors_pk_from_sig_loop2 .x86 := by
  funext N sig pk st st5 adr a k blocks idx stop vals h
  unfold X86ForsReplay.slhdsa.fors.fors_pk_from_sig_loop2 Program.fors.fors_pk_from_sig_loop2
  congr 1
  funext q
  rcases q with ⟨b,indices,e,v,l⟩
  change X86ForsReplay.slhdsa.fors.fors_pk_from_sig_loop2.body sig pk st st5 adr a k b indices e v l =
    Program.fors.fors_pk_from_sig_loop2.body .x86 sig pk st st5 adr a k b indices e v l
  unfold X86ForsReplay.slhdsa.fors.fors_pk_from_sig_loop2.body Program.fors.fors_pk_from_sig_loop2.body
  split
  · split
    · rfl
    · simp only [x86Path,path,ne_eq,not_true_eq_false,ite_false,bind_tc_eq,Std.bind_assoc,lift,bind_ok]
      simp only [Array.to_slice_mut]
      repeat' (apply bindRight; intro x; try rcases x with ⟨_,_⟩)
      rfl
  · rfl
end slhdsa.PlatformFors

namespace slhdsa.PlatformFors
abbrev armTreeLoop := @Program.fors.fors_batch_loop3 .arm
abbrev x86TreeLoop := @Program.fors.fors_batch_loop3 .x86
abbrev armPathLoop := @Program.fors.fors_pk_from_sig_loop2 .arm
abbrev x86PathLoop := @Program.fors.fors_pk_from_sig_loop2 .x86
end slhdsa.PlatformFors

run_cmd liftTermElabM do
  for (ns,target) in [(`ArmForsReplay,"arm"), (`X86ForsReplay,"x86")] do
    for (base,stem) in [("fors_batch_loop3","Tree"),("fors_pk_from_sig_loop2","Path")] do
      let label := fun suffix => Name.str `slhdsa.PlatformFors (target ++ stem ++ suffix)
      PlatformProof.transport (ns ++ Name.str `slhdsa (base ++ "_spec"))
        (ns ++ Name.str `slhdsa.fors base) (label "Loop") (label "Eq") (label "LoopSpec")

#print axioms slhdsa.PlatformFors.armTreeLoopSpec
#print axioms slhdsa.PlatformFors.armPathLoopSpec
#print axioms slhdsa.PlatformFors.x86TreeLoopSpec
#print axioms slhdsa.PlatformFors.x86PathLoopSpec
