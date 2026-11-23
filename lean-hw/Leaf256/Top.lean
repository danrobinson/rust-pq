import Leaf256.Driver
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512
open Spec.SHA256

def template (a : LeafRust.address.Adrs) (sk : Spec.Bytes) :=
  let clear : LeafRust.address.Adrs := { a with typ := 6#u32, word2 := 0#u32, word3 := 0#u32 }
  padFrom 64 ((adrsS (addressOf clear)).compress ++ sk)

def typeChange (a : LeafRust.address.Adrs) : Word :=
  ((UScalar.hcast .I32 ((UScalar.cast .U8 a.typ) ^^^ (UScalar.cast .U8 (6#u32)))).bv) <<< 16

theorem trace_round (st : VecState) (v : Reg) (k : U32) (B : Fin 16 → Spec.Bytes) (iv : Fin 16 → State) (t : Nat)
    (small : t < 16) (c : k.bv = K[t]!) (hw : ∀ j, v j = word (B j) (4*t))
    (h : Trace st (fun j => schedule (B j)) iv t) :
    LeafRust.sha256.x86.avx512.round st v k ⦃ r => Trace r (fun j => schedule (B j)) iv (t+1) ⦄ := by
  apply WP.spec_mono (round_spec st v k (fun j => schedule (B j)) t c (fun j => by
    rw [schedule_lt16 _ _ small,hw]))
  intro r hr j
  rw [hr,h j,List.range_succ,List.foldl_append]; rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem kernel_spec (N : Usize) (s : Array U32 8#usize) (sk : Array U8 N) (a : LeafRust.address.Adrs)
    (first : U32) (out : Nodes N) (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32)
    (bound : first.val+out.length ≤ 2^32) :
    fors_leaves s sk a first out ⦃ r => r.length = out.length ∧ ∀ k, k < out.length → ∀ i, i < N.val →
      (r.val[k]!.val[i]!).bv = ((leafDigest (s.val.map (·.bv))
        (fun n => word (template a (bytes sk.val)) (4*n)) (BitVec.ofNat 32 (first.val+k))
        (typeChange a) N.val)[i/4]!).extractLsb' (8*(3-i%4)) 8 ⦄ := by
  unfold fors_leaves
  simp only [LeafRust.address.Adrs.with_type,LeafRust.address.Adrs.with_keypair,LeafRust.address.FORS_PRF,lift,bind_ok]
  step with short_block _ (Array.to_slice sk) (by simp; omega) as ⟨b,hb⟩
  step with words_spec N b as ⟨w,hw⟩
  step with initial_spec N s as ⟨st,hs⟩
  simp only [_root_.core.core_arch.x86.avx512f._mm512_set1_epi32,bind_ok]
  step as ⟨chg,hchg⟩
  let B := fun j => blockOf (laneWords w j)
  let C := fun j => blockOf (withType (laneWords w j) chg.bv)
  step with first_two st w B (fun k hk j => (word_blockOf (laneWords w j) k (by omega)).symm) as ⟨prefixState,pre⟩
  have preF : Trace prefixState (fun j => schedule (C j)) (laneState st) 2 := by
    apply transfer_prefix (by decide) _ pre
    intro j k hk; simp (disch := omega) only [B,C,word_blockOf,withType,if_neg]
  step as ⟨v2,h2⟩
  step as ⟨k2,c2⟩
  step with trace_round prefixState v2 k2 B _ 2 (by decide) (by rw [c2,← getElem!_pos]; exact constants ⟨2,by decide⟩)
    (fun j => by rw [word_blockOf _ _ (by decide),h2,← getElem!_pos] <;> rfl) pre as ⟨p3,h3⟩
  step as ⟨v3,hv3⟩
  step as ⟨k3,c3⟩
  step with trace_round p3 v3 k3 B _ 3 (by decide) (by rw [c3,← getElem!_pos]; exact constants ⟨3,by decide⟩)
    (fun j => by rw [word_blockOf _ _ (by decide),hv3,← getElem!_pos] <;> rfl) h3 as ⟨pp,hp⟩
  simp only [LeafRust.core.core_arch.x86.avx512f._mm512_xor_si512,bind_ok]
  step with trace_round prefixState (fun j => v2 j ^^^ chg.bv) k2 C _ 2 (by decide) (by rw [c2,← getElem!_pos]; exact constants ⟨2,by decide⟩)
    (fun j => by rw [word_blockOf _ _ (by decide),h2,← getElem!_pos] <;> rfl) preF as ⟨f3,hf3⟩
  step with trace_round f3 v3 k3 C _ 3 (by decide) (by rw [c3,← getElem!_pos]; exact constants ⟨3,by decide⟩)
    (fun j => by rw [word_blockOf _ _ (by decide),hv3,← getElem!_pos] <;> rfl) hf3 as ⟨pf,hf⟩
  simp only [LeafRust.core.core_arch.x86.avx512f._mm512_set_epi32,
    DigestRust.core.core_arch.x86.avx512f._mm512_set_epi32,bind_ok]
  step as ⟨it,hit,hstep⟩
  have eit : it = ⟨⟨0#usize,out.len⟩,16#usize⟩ := by cases it; simp_all
  rw [eit]
  have laneIds : (fun j : Fin 16 => [(0#i32).bv,(1#i32).bv,(2#i32).bv,(3#i32).bv,(4#i32).bv,(5#i32).bv,(6#i32).bv,(7#i32).bv,(8#i32).bv,(9#i32).bv,(10#i32).bv,(11#i32).bv,(12#i32).bv,(13#i32).bv,(14#i32).bv,(15#i32).bv][j.val]!) =
      fun j => BitVec.ofNat 32 j.val := by funext j; fin_cases j <;> decide
  rw [laneIds]
  apply WP.spec_mono (batches_spec first w st pp pf (fun _ => chg.bv) out shape bound hp hf)
  rintro r ⟨hlen,all⟩
  refine ⟨hlen,fun k hk i hi => ?_⟩
  have actual := all k hk
  rw [if_pos hk] at actual
  rw [actual i hi]
  unfold computed
  rw [initial_words st s hs,show first.val + k/16*16 + k%16 = first.val+k by omega]
  have hc : chg.bv = typeChange a := by assumption
  rw [hc]
  let j : Fin 16 := ⟨k%16,by omega⟩
  have words (t : Nat) (ht : t < 16) : laneWords w j t = word (template a (bytes sk.val)) (4*t) := by
    rw [show laneWords w j t = _ from hw t ht j,hb]
    simp only [template,Array.val_to_slice]
  exact congrArg (fun ws : List Word => ws[i/4]!.extractLsb' (8*(3-i%4)) 8)
    (digest_congr (s.val.map (·.bv)) (BitVec.ofNat 32 (first.val+k)) (typeChange a) N.val words)

theorem fors_leaves_spec (N : Usize) (s : Array U32 8#usize) (sk : Array U8 N) (a : LeafRust.address.Adrs)
    (first : U32) (out : Nodes N) (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32)
    (cpu : GatherRust.avx512Available = true) (bound : first.val+out.length ≤ 2^32) :
    LeafRust.sha256.x86.fors_leaves s sk a first out ⦃ r => r.length = out.length ∧ ∀ k, k < out.length →
      ∀ i, i < N.val → (r.val[k]!.val[i]!).bv = ((leafDigest (s.val.map (·.bv))
        (fun t => word (template a (bytes sk.val)) (4*t)) (BitVec.ofNat 32 (first.val+k))
        (typeChange a) N.val)[i/4]!).extractLsb' (8*(3-i%4)) 8 ⦄ := by
  unfold LeafRust.sha256.x86.fors_leaves
  apply WP.spec_bind (Pₘ := fun b => b = true)
  · rcases shape with h | h | h <;> rw [h] <;> exact (WP.spec_ok _).2 rfl
  rintro _ rfl
  simp only [LeafRust.sha256.x86.avx512_available,DigestRust.sha256.x86.avx512_available,
    GatherRust.sha256.x86.avx512_available,cpu,bind_ok,massert,↓reduceIte]
  exact kernel_spec N s sk a first out shape bound

#print axioms fors_leaves_spec
end slhdsa.X86.Leaf
