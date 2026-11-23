import Chainwide.Invariant
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open Spec.SHA256
open ChainWideRust.sha256.x86.avx512

def elapsed (start current : Reg) (mask : U16) : Nat :=
  let j : Fin 16 := ⟨mask.bv.ctz.toNat % 16,Nat.mod_lt _ (by decide)⟩
  (current j).toNat-(start j).toNat

private theorem elapsed_eq (start stop current : Reg) (mask : U16) (t : Nat) (work : mask ≠ 0#u16)
    (sched : Schedule start stop current mask t) : elapsed start current mask = t := by
  have nz : mask.bv ≠ 0 := by intro eq; apply work; apply U16.bv_eq_imp_eq; exact eq
  have bound : mask.bv.ctz.toNat < 16 := BitVec.ctz_lt_iff_ne_zero.mpr nz
  let j : Fin 16 := ⟨mask.bv.ctz.toNat,bound⟩
  have bit : mask.bv.getLsbD j.val = true := BitVec.getLsbD_true_ctz_of_ne_zero nz
  rw [sched.1 j] at bit
  have e := sched.2 j (of_decide_eq_true bit)
  unfold elapsed
  simp only [Nat.mod_eq_of_lt bound]
  change (current j).toNat-(start j).toNat = t
  omega

private def PrefixWords (base w : Words) := ∀ k < 4, ∀ j : Fin 16, w.val[k]! j = base.val[k]! j

private theorem step_trace (base w : Words) (fixed current : Reg) (iv pre : Hash)
    (prefixWords : PrefixWords base w)
    (trace : Trace pre (fun j => schedule (Leaf.blockOf (lanes base j))) (laneState iv) 4) :
    Trace pre (fun j => schedule (blockAtStep w fixed current j)) (laneState iv) 4 := by
  apply Leaf.transfer_prefix (a := fun j => Leaf.blockOf (lanes base j)) (by decide) _ trace
  intro j k hk
  simp (disch := omega) only [blockAtStep,Leaf.word_blockOf,addressWord,if_neg,lanes,prefixWords k hk]

theorem chain_loop_spec (N : Usize) (ends : Slice U32) (iv : Hash) (off : Usize) (batch : Rows)
    (start stop fixed : Reg) (orig : U16) (initialSaved pre : Hash) (base : Words) (p : Fin 16 → Lane)
    (hn : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (he : off.val+batch.length ≤ ends.length) (hb : Covers orig batch.length)
    (positive : ∀ k, orig.bv.getLsbD k → 0 < ends.val[off.val+k]!.val) (nonempty : orig ≠ 0#u16)
    (startSched : Schedule start stop start orig 0) (state : ∀ j, (p j).state = stateWords (laneState iv j))
    (first : ∀ j, (p j).first = (start j).toNat)
    (length : ∀ j, (p j).head.length = 18 ∧ (p j).initial.length = N.val ∧ 22+N.val+(p j).tail.length = 64)
    (ready : Ready p N.val 0 start stop fixed base)
    (trace : Trace pre (fun j => schedule (Leaf.blockOf (lanes base j))) (laneState iv) 4) :
    chains_loop0_loop1 N ends iv off batch start stop orig orig initialSaved base fixed (fun _ => 0xffff) pre
      ⦃ out => ∃ finalHash, Rendered N ends off orig finalHash batch out ∧
        ∀ j : Fin 16, orig.bv.getLsbD j.val → ∀ k < N.val/4,
          finalHash.val[k]! j = (lastHash (p j) N.val (stop j))[k]! ⦄ := by
  unfold chains_loop0_loop1
  apply loop.spec_decr_nat (measure := fun q : Reg × U16 × Hash × Words => 2^32-elapsed start q.1 q.2.1)
    (inv := fun q => ∃ t, q.2.1 ≠ 0#u16 ∧ Schedule start stop q.1 q.2.1 t ∧ PrefixWords base q.2.2.2 ∧
      Ready p N.val t start stop fixed q.2.2.2 ∧ Kept p N.val t start stop orig q.2.2.1)
  · rintro ⟨current,active,saved,w⟩ ⟨t,work,sched,unchanged,valid,kept⟩
    have hlen j := value_length (p j) N.val t (by omega) (length j).2.1
    let blocks := blockAtStep w fixed current
    have packed k (hk : k<16) (j : Fin 16) : addressWord (lanes w j) (fixed j) (current j) k =
        word (blocks j) (4*k) := (Leaf.word_blockOf _ _ hk).symm
    apply WP.spec_mono (iteration_spec N ends iv off batch start stop orig fixed pre current active saved w t blocks
      hn he hb positive work sched startSched.1 (step_trace base w fixed current iv pre unchanged trace) packed)
    rintro flow ⟨aw,hash,fin,awords,hashes,last,done⟩
    have wire k (hk : k<16) j := (awords k hk j).trans (packed k hk j).symm
    have actual := hash_active p N.val t start stop current fixed iv hash w valid
      (fun j => ⟨(length j).1,hlen j,(length j).2.2⟩) first state sched.2 hashes
    cases flow with
    | done out =>
      obtain ⟨noWork,fh,select,render⟩ := done
      have kept' := kept_next p N.val t start stop orig fin saved hash fh (by omega) first kept actual last select
      exact ⟨fh,render,fun j hj => kept' j hj (noWork j)⟩
    | cont q =>
      rcases q with ⟨next,mask,retain,out⟩
      obtain ⟨work',sched',select,words'⟩ := done
      refine ⟨⟨t+1,work',sched',?_,?_,?_⟩,?_⟩
      · intro k hk j
        have h := words' k (by omega) j
        rw [h]
        simp (disch := omega) only [valueWord,if_neg,wire k (by omega),addressWord,lanes,unchanged k hk]
      · exact ready_next p N.val t start stop current fixed w aw out hash hn valid
          (fun j => ⟨(length j).1,hlen j⟩) wire actual words'
      · exact kept_next _ _ _ _ _ _ _ _ _ _ (by omega) first kept actual last select
      · change 2^32-elapsed start next mask < 2^32-elapsed start current active
        rw [elapsed_eq _ _ _ _ _ work' sched',elapsed_eq _ _ _ _ _ work sched]
        have lim := active_has_budget _ _ _ _ _ sched work
        omega
  · refine ⟨0,nonempty,startSched,fun _ _ _ => rfl,ready,?_⟩
    intro j set ended
    have eq := startSched.1 j
    rw [set] at eq
    exact False.elim (ended (of_decide_eq_true eq.symm))
end slhdsa.X86.Chain
