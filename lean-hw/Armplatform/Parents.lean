import Parentdriver.Proof
import Slhdsa.Proofs.Fors
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformFors
open PlatformParent.Driver

inductive Target | arm | x86

def parents (target : Target) {N : Usize} : Array U64 8#usize → address.Adrs → U32 → Nodes N → Usize → Result (Usize × Nodes N) := match target with
  | .arm => @ParentarmRust.sha512.parents.parents N
  | .x86 => @Parentx86Rust.sha512.parents.parents N

def pathParents (target : Target) {N : Usize} : Array U64 8#usize → address.Adrs → Nodes N → Slice U32 → Slice U8 → Usize → Usize → Result (Usize × Nodes N × Slice U32) := match target with
  | .arm => @ParentarmRust.sha512.parents.path_parents N
  | .x86 => @Parentx86Rust.sha512.parents.path_parents N

theorem parent_prefix (target : Target) {N} (p : params.Params) (hp : PN p N) (pk : Array U8 N)
    (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk (⟨pk,st,st5⟩ : hash.Seed N)) (a : address.Adrs) (first : U32) (v : Nodes N)
    (cnt : Usize) (space : 2*cnt.val≤v.length) (room : first.val+cnt.val≤2^32) :
    parents target st5 a first v cnt ⦃ n out =>
      n.val≤cnt.val ∧ Reduced (paramsS p) (bytes pk.val) a first v out n.val ⦄ := by
  cases target with
  | arm =>
    simp only [parents]
    rcases hp.nok with small | wide
    · rw [tree_arm,(unsupported_width arm a st5 first v cnt (Slice.from [] (by simp)) (Slice.from [] (by simp)) 0#usize 0#usize
        (by omega) (by omega)).1]
      simp [Reduced,step_simps]
    · apply WP.spec_mono (arm_tree_spec (paramsS p) (bytes pk.val) a st5 first v cnt wide rfl hp.n
        (by simp) (hs.2 (by rcases wide with h|h <;> omega)) space room)
      rintro ⟨n,out⟩ ⟨hn,post⟩
      exact ⟨by rw [hn]; unfold processed; split <;> omega,post⟩
  | x86 =>
    simp only [parents]
    rcases hp.nok with small | wide
    · rw [tree_x86,(unsupported_width x86 a st5 first v cnt (Slice.from [] (by simp)) (Slice.from [] (by simp)) 0#usize 0#usize
        (by omega) (by omega)).1]
      simp [Reduced,step_simps]
    · apply WP.spec_mono (x86_tree_spec (paramsS p) (bytes pk.val) a st5 first v cnt wide rfl hp.n
        (by simp) (hs.2 (by rcases wide with h|h <;> omega)) space room)
      rintro ⟨n,out⟩ ⟨hn,post⟩
      exact ⟨by rw [hn]; unfold processed; split <;> omega,post⟩

theorem path_prefix (target : Target) {N} (p : params.Params) (hp : PN p N) (pk : Array U8 N)
    (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk (⟨pk,st,st5⟩ : hash.Seed N)) (a : address.Adrs) (v : Nodes N)
    (idx : Slice U32) (sig : Slice U8) (h off : Usize) (size : v.length ≤ idx.length)
    (height : h.val+1≤Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    pathParents target st5 a v idx sig h off ⦃ n out ix =>
      n.val≤v.length ∧ Paths (paramsS p) (bytes pk.val) a v idx sig h.val off.val n.val out ix ⦄ := by
  cases target with
  | arm =>
    simp only [pathParents]
    rcases hp.nok with small | wide
    · rw [path_arm,(unsupported_width arm a st5 0#u32 v 0#usize idx sig h off (by omega) (by omega)).2]
      simp [Paths,IndexRange,step_simps]
    · apply WP.spec_mono (arm_path_spec (paramsS p) (bytes pk.val) a st5 v idx sig h off wide rfl hp.n
        (by simp) (hs.2 (by rcases wide with h|h <;> omega)) size height bounds)
      rintro ⟨n,out,ix⟩ ⟨hn,post⟩
      exact ⟨by rw [hn]; unfold processed; split <;> omega,post⟩
  | x86 =>
    simp only [pathParents]
    rcases hp.nok with small | wide
    · rw [path_x86,(unsupported_width x86 a st5 0#u32 v 0#usize idx sig h off (by omega) (by omega)).2]
      simp [Paths,IndexRange,step_simps]
    · apply WP.spec_mono (x86_path_spec (paramsS p) (bytes pk.val) a st5 v idx sig h off wide rfl hp.n
        (by simp) (hs.2 (by rcases wide with h|h <;> omega)) size height bounds)
      rintro ⟨n,out,ix⟩ ⟨hn,post⟩
      exact ⟨by rw [hn]; unfold processed; split <;> omega,post⟩

end slhdsa.PlatformFors
