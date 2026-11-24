import Parentblock.Proof
import Gather512.Fips
import Paired.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent

def seedState (pk : Spec.Bytes) (n : Nat) :=
  Spec.SHA512.compress Spec.SHA512.H0 (pk ++ List.replicate (128-n) 0#8)

private theorem parent_digest {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs)
    (data : Spec.Bytes) (state : Array U64 8#usize) (block : Array U8 128#usize)
    (shape : N.val = 24 ∨ N.val = 32) (fam : p.family = .sha2) (width : p.n = N.val)
    (hlen : pk.length = N.val) (hdata : data.length = 2*N.val)
    (hs : state.val.map (·.bv) = seedState pk N.val)
    (hb : bytes block.val = S512.padFrom 128 (a.compress ++ data)) :
    bytes (X86.S512.Parents.encoded ((Spec.SHA512.compress (state.val.map (·.bv))
        (bytes block.val)).take (N.val/8))) = Spec.H p pk a data := by
  rw [X86.S512.Gather.encode_take, show 8*(N.val/8) = N.val by omega,hs,hb]
  have h := th512_one N.val pk hlen (by omega) a data (by omega)
  rw [seedState,h]
  simp only [Spec.H,fam,width,show ¬N.val = 16 by omega,↓reduceIte,th512]

theorem x86_parents {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : Fin 8 → Spec.Adrs)
    (data : Fin 8 → Spec.Bytes) (s : Array U64 8#usize) (blocks : X86.S512.Parents.Blocks)
    (out : Slice (Array U8 N)) (shape : N.val = 24 ∨ N.val = 32)
    (fam : p.family = .sha2) (width : p.n = N.val) (hlen : pk.length = N.val)
    (ho : 8 ≤ out.length) (hdata : ∀ j, (data j).length = 2*N.val)
    (hs : s.val.map (·.bv) = seedState pk N.val)
    (hb : ∀ j : Fin 8, bytes blocks.val[j.val]!.val = S512.padFrom 128 ((a j).compress ++ data j)) :
    ParentsRust.sha512.x86.compress_parents s blocks out ⦃ r => r.length = out.length ∧
      (∀ j : Fin 8, bytes r.val[j.val]!.val = Spec.H p pk (a j) (data j)) ∧
      ∀ j, 8 ≤ j → j < out.length → r.val[j]!.val = out.val[j]!.val ⦄ := by
  apply WP.spec_mono (X86.S512.Parents.parents_spec N s blocks out shape ho)
  rintro r ⟨hl,hr,ht⟩
  refine ⟨hl,fun j => ?_,ht⟩
  rw [hr j]
  exact parent_digest p pk (a j) (data j) s blocks.val[j.val]! shape fam width hlen (hdata j) hs (hb j)

theorem arm_parents {N : Usize} (p : Spec.Params) (pk : Spec.Bytes) (a : Fin 2 → Spec.Adrs)
    (data : Fin 2 → Spec.Bytes) (s : Array U64 8#usize) (blocks : Array (Array U8 128#usize) 2#usize)
    (out : Slice (Array U8 N)) (hw : Arm.haveSha512 = true) (shape : N.val = 24 ∨ N.val = 32)
    (fam : p.family = .sha2) (width : p.n = N.val) (hlen : pk.length = N.val)
    (ho : 2 ≤ out.length) (hdata : ∀ j, (data j).length = 2*N.val)
    (hs : s.val.map (·.bv) = seedState pk N.val)
    (hb : ∀ j : Fin 2, bytes blocks.val[j.val]!.val = S512.padFrom 128 ((a j).compress ++ data j)) :
    PairedRust.sha512.paired.compress_parents s blocks out ⦃ r => r.length = out.length ∧
      (∀ j : Fin 2, bytes r.val[j.val]!.val = Spec.H p pk (a j) (data j)) ∧
      ∀ j, 2 ≤ j → j < out.length → r.val[j]!.val = out.val[j]!.val ⦄ := by
  apply WP.spec_mono (H512.Paired.parents_spec hw N s blocks out shape ho)
  intro r hr
  have len := congrArg List.length hr
  simp only [List.length_map,List.length_append,List.length_drop] at len
  have bl : blocks.val.length = 2 := by simp
  have ol : out.val.length = out.length := rfl
  have rl : r.length = r.val.length := rfl
  refine ⟨by omega,fun j => ?_,fun j hj hj' => ?_⟩
  · have h := congrArg (fun l : List (List U8) => l[j.val]!) hr
    simp only at h
    rw [getElem!_pos _ _ (by simp; omega),List.getElem_map,getElem!_pos _ _ (by simp; omega),
      List.getElem_append_left (by simp; omega),List.getElem_map,← getElem!_pos,← getElem!_pos] at h
    rw [h]
    exact parent_digest p pk (a j) (data j) s blocks.val[j.val]! shape fam width hlen (hdata j) hs (hb j)
  · have h := congrArg (fun l : List (List U8) => l[j]!) hr
    simp only at h
    rw [getElem!_pos _ _ (by simp; omega),List.getElem_map,getElem!_pos _ _ (by simp; omega),
      List.getElem_append_right (by simp; omega),List.getElem_map,List.getElem_drop] at h
    simpa [← getElem!_pos, show 2+(j-2) = j by omega] using h

#print axioms x86_parents
#print axioms arm_parents
end slhdsa.PlatformParent
