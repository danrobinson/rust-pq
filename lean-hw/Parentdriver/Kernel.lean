import Parentdriver.Targets
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

/-- A full batch writes one FIPS parent per row in a destination of exactly G rows. -/
def Correct {G N : Usize} (K : Kernel G) (p : Spec.Params) (pk : Spec.Bytes) (s : Array U64 8#usize) :=
  ∀ (blocks : Blocks G) (out : Nodes N) (a : Nat → Spec.Adrs) (data : Nat → Spec.Bytes),
    out.length = G.val →
    (∀ k, k < G.val → (data k).length = 2*N.val) →
    (∀ k, k < G.val → bytes blocks.val[k]!.val = S512.padFrom 128 ((a k).compress ++ data k)) →
    K.compress s blocks out ⦃ r => r.length = G.val ∧
      ∀ k, k < G.val → bytes r.val[k]!.val = Spec.H p pk (a k) (data k) ⦄

theorem x86_correct {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (s : Array U64 8#usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val) :
    Correct (N := N) x86 p pk s := by
  intro blocks out a data ho hd hb
  apply WP.spec_mono (x86_parents p pk (fun j => a j.val) (fun j => data j.val) s blocks out
    shape fam width hlen (by rw [ho]; decide) (fun j => hd j.val j.isLt) hs (fun j => hb j.val j.isLt))
  rintro r ⟨hl,hr,-⟩
  exact ⟨hl.trans ho,fun k hk => hr ⟨k,hk⟩⟩

theorem arm_correct {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (s : Array U64 8#usize)
    (hw : Arm.haveSha512 = true) (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hs : s.val.map (·.bv) = seedState pk N.val) :
    Correct (N := N) arm p pk s := by
  intro blocks out a data ho hd hb
  apply WP.spec_mono (arm_parents p pk (fun j => a j.val) (fun j => data j.val) s blocks out hw
    shape fam width hlen (by rw [ho]; decide) (fun j => hd j.val j.isLt) hs (fun j => hb j.val j.isLt))
  rintro r ⟨hl,hr,-⟩
  exact ⟨hl.trans ho,fun k hk => hr ⟨k,hk⟩⟩

end slhdsa.PlatformParent.Driver
