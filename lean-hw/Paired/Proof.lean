import Paired.Funs
import Slhdsa.Proofs.Hw512.Compress
open Aeneas Aeneas.Std Result
namespace slhdsa.H512.Paired

local instance : Inhabited V64 := inferInstanceAs (Inhabited Arm.V2)

def state (v : Array V64 4#usize) (w : Array V64 8#usize) : KState :=
  ⟨v.val[0]!, v.val[1]!, v.val[2]!, v.val[3]!, w.val⟩

private theorem read_reg {n : Usize} (a : Array V64 n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok (a.val[i.val]!) := by
  have hi : i.val < a.val.length := by simpa using h
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

@[step] theorem lane_spec (hw : Arm.haveSha512 = true) (round : Usize) (v : Array V64 4#usize)
    (w : Array V64 8#usize) (k : V64) (hi : round.val < 40) (hk : k = vOf2 Spec.SHA512.K (2*round.val)) :
    PairedRust.sha512.paired.lane_step round v w k ⦃ v' w' => state v' w' = kstep (state v w) round.val ⦄ := by
  unfold PairedRust.sha512.paired.lane_step
  simp (disch := decide) only [read_reg, bind_ok, PairedRust.sha512.hw.arm.add,
    PairedRust.sha512.hw.arm.ext1, PairedRust.sha512.hw.arm.sha512h, PairedRust.sha512.hw.arm.sha512h2,
    PairedRust.sha512.hw.arm.sha512su0, PairedRust.sha512.hw.arm.sha512su1,
    wr512_add hw, wr512_ext1 hw, wr512_sha512h hw, wr512_sha512h2 hw,
    wr512_sha512su0 hw, wr512_sha512su1 hw, bind_ok]
  step*
  · rename_i h
    have small : round.val < 32 := by scalar_tac
    simp only [state, kstep, small, ↓reduceIte, *, Array.set_val_eq, ← getElem!_pos]
    congr 1
    exact set_val' w i (round.val % 8) i_post _
  · rename_i h
    have large : ¬round.val < 32 := by scalar_tac
    simp only [state, kstep, large, ↓reduceIte, *, ← getElem!_pos]
    rfl

@[step] theorem load_spec (hw : Arm.haveSha512 = true) (block : Array U8 128#usize) :
    PairedRust.sha512.paired.load_block block ⦃ r => (r.val : List Arm.V2) = blockVs (bytes block.val) ⦄ := by
  unfold PairedRust.sha512.paired.load_block
  simp only [PairedRust.sha512.hw.arm.load_be, lift, bind_ok]
  step*
  simp_all [blockVs]
  rfl

open PairedRust.sha512.paired
def lane (s : PairedRust.sha512.paired.Lane) := state s.state s.schedule

@[step] theorem pair_spec (hw : Arm.haveSha512 = true) (i : Usize)
    (l r : PairedRust.sha512.paired.Lane) (hi : i.val < 40) :
    PairedRust.sha512.paired.paired_step i l r ⦃ l' r' => lane l' = kstep (lane l) i.val ∧
      lane r' = kstep (lane r) i.val ⦄ := by
  unfold PairedRust.sha512.paired.paired_step
  have same : S512.wv PairedRust.sha512.K.to_slice.val = Spec.SHA512.K := by
    unfold PairedRust.sha512.K Spec.SHA512.K
    rfl
  simp only [PairedRust.sha512.hw.arm.load_words, lift, bind_ok]
  step as ⟨idx, hidx⟩
  step as ⟨k, hk⟩
  have hc : k = vOf2 Spec.SHA512.K (2*i.val) := by simpa only [same, hidx] using hk
  step with lane_spec hw i l.state l.schedule k hi hc
  step with lane_spec hw i r.state r.schedule k hi hc
  simp_all [lane, step_simps]

private def serialize (words : List U64) := words.flatMap fun w => w.bv.toBEBytes.map (fun b => (⟨b⟩ : U8))

private theorem take_write (x s : List U8) (i : Nat) (h : i+s.length ≤ x.length) :
    (x.setSlice! i s).take (i+s.length) = x.take i ++ s := by
  simp only [List.setSlice!, min_eq_left (by omega : s.length ≤ x.length-i), List.take_length]
  have he : i+s.length = (x.take i ++ s).length := by simp [List.length_take, min_eq_left (by omega : i ≤ x.length)]
  rw [he, List.take_append_length]

theorem store_loop_spec (N : Usize) (out : Array U8 N) (words : Array U64 4#usize)
    (hn : N.val = 24 ∨ N.val = 32) :
    PairedRust.sha512.paired.store_parent_loop out words 0#usize ⦃ r =>
      r.val = serialize (words.val.take (N.val/8)) ⦄ := by
  unfold PairedRust.sha512.paired.store_parent_loop
  apply loop.spec_decr_nat (measure := fun (p : Array U8 N × Usize) => N.val/8 - p.2.val)
    (inv := fun p => p.2.val ≤ N.val/8 ∧ p.1.val.take (8*p.2.val) = serialize (words.val.take p.2.val))
  · rintro ⟨out,i⟩ ⟨hi,hh⟩
    simp only at hi hh
    simp only [PairedRust.sha512.paired.store_parent_loop.body]
    step*
    · scalar_tac
    · scalar_tac
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [s_post2, s2_post, s1_post, Array.val_to_slice]
      change (out.val.setSlice! i2.val a.val).take (8*i5.val) = _
      have len : a.val.length = 8 := by scalar_tac
      rw [show 8*i5.val = 8*i.val + a.val.length by scalar_tac, i2_post, take_write _ _ _ (by scalar_tac),
        hh, i5_post, List.take_succ_eq_append_getElem (by scalar_tac)]
      simp only [serialize, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, a_post, i4_post]
    · have he : i.val = N.val/8 := by scalar_tac
      have hl : 8*i.val = out.val.length := by scalar_tac
      rw [hl, List.take_length, he] at hh
      exact hh
  · simp [serialize]
def encode (ws : List Spec.SHA512.Word) : List U8 := ws.flatMap fun w => w.toBEBytes.map (fun b => (⟨b⟩ : U8))

private theorem ser_take (xs : List U64) (n : Nat) :
    serialize (xs.take n) = encode ((S512.wv xs).take n) := by
  simp [serialize, encode, S512.wv, ← List.map_take, List.flatMap_map, Function.comp_def]

def firstFour (iv v : Array V64 4#usize) :=
  vwords2 (Arm.ADD2 iv.val[0]! v.val[0]!) ++ vwords2 (Arm.ADD2 iv.val[1]! v.val[1]!)

@[step] theorem store_spec (hw : Arm.haveSha512 = true) (N : Usize) (iv v : Array V64 4#usize)
    (out : Array U8 N) (hn : N.val = 24 ∨ N.val = 32) :
    PairedRust.sha512.paired.store_parent iv v out ⦃ r => r.val = encode ((firstFour iv v).take (N.val/8)) ⦄ := by
  unfold PairedRust.sha512.paired.store_parent
  simp (disch := decide) only [read_reg, PairedRust.sha512.hw.arm.add, PairedRust.sha512.hw.arm.store_words, bind_ok]
  step*
  step with store_loop_spec N out words hn
  simp_all [ser_take, firstFour]

def After (l : PairedRust.sha512.paired.Lane) (s : KState) (n : Nat) := lane l = (List.range n).foldl kstep s

theorem advance (hw : Arm.haveSha512 = true) (i : Usize) (l r : PairedRust.sha512.paired.Lane)
    (L R : KState) (hi : i.val < 40) (hl : After l L i.val) (hr : After r R i.val) :
    PairedRust.sha512.paired.paired_step i l r ⦃ l' r' => After l' L (i.val+1) ∧ After r' R (i.val+1) ⦄ := by
  apply WP.spec_mono (pair_spec hw i l r hi)
  rintro ⟨l',r'⟩ ⟨h1,h2⟩
  unfold After at hl hr
  simpa [After, List.range_succ, List.foldl_append, ← hl, ← hr] using And.intro h1 h2

private def initialState (st : List Spec.SHA512.Word) (B : Spec.Bytes) : KState :=
  ⟨vOf2 st 0,vOf2 st 2,vOf2 st 4,vOf2 st 6,blockVs B⟩

private theorem add_comm (a b : Arm.V2) : Arm.ADD2 a b = Arm.ADD2 b a := by
  cases a; cases b; simp [Arm.ADD2, BitVec.add_comm]

private theorem finish (N : Usize) (st : List Spec.SHA512.Word) (B : Spec.Bytes)
    (iv : Array V64 4#usize) (s : PairedRust.sha512.paired.Lane)
    (hiv : iv.val = [vOf2 st 0,vOf2 st 2,vOf2 st 4,vOf2 st 6])
    (hs : After s (initialState st B) 40) (hn : N.val = 24 ∨ N.val = 32) :
    (firstFour iv s.state).take (N.val/8) = (Spec.SHA512.compress st B).take (N.val/8) := by
  let result := kcompress (vOf2 st 0) (vOf2 st 2) (vOf2 st 4) (vOf2 st 6) (blockVs B)
  have ha : s.state.val[0]! = result.ab := congrArg KState.ab hs
  have hc : s.state.val[1]! = result.cd := congrArg KState.cd hs
  have he := kcompress_eq st B
  change (_ ++ _ ++ _) = Spec.SHA512.compress st B at he
  rw [← he, List.take_append_of_le_length (by simp [vwords2]; omega)]
  unfold firstFour
  rw [hiv, ha, hc]
  change (vwords2 (Arm.ADD2 (vOf2 st 0) result.ab) ++ vwords2 (Arm.ADD2 (vOf2 st 2) result.cd)).take _ = _
  rw [add_comm (vOf2 st 0), add_comm (vOf2 st 2)]
private theorem elements2 {α : Type} [Inhabited α] (xs : List α) (h : xs.length = 2) :
    xs = [xs[0]!,xs[1]!] := by
  rcases xs with _ | ⟨x, xs⟩ <;> simp_all
  rcases xs with _ | ⟨y, xs⟩ <;> simp_all

private theorem write2 {α : Type} (xs : List α) (a b : α) (h : 2 ≤ xs.length) :
    (xs.set 0 a).set 1 b = a :: b :: xs.drop 2 := by
  rcases xs with _ | ⟨x, xs⟩ <;> simp_all
  rcases xs with _ | ⟨y, xs⟩ <;> simp_all

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
/-- The first two parents are written with their truncated FIPS SHA-512 digests.
Every later element of the output slice retains its input value. -/
theorem parents_spec (hw : Arm.haveSha512 = true) (N : Usize) (st : Array U64 8#usize)
    (blocks : Array (Array U8 128#usize) 2#usize) (out : Slice (Array U8 N))
    (hn : N.val = 24 ∨ N.val = 32) (ho : 2 ≤ out.length) :
    PairedRust.sha512.paired.compress_parents st blocks out ⦃ r =>
      r.val.map (·.val) = (blocks.val.map (fun b => encode ((Spec.SHA512.compress (S512.wv st.val)
        (bytes b.val)).take (N.val/8)))) ++ (out.val.drop 2).map (·.val) ⦄ := by
  unfold PairedRust.sha512.paired.compress_parents
  simp only [PairedRust.sha512.hw.arm.load_words, lift, bind_ok]
  step as ⟨a,ha⟩
  step as ⟨b,hb⟩
  step as ⟨c,hc⟩
  step as ⟨d,hd⟩
  step as ⟨b0,hb0⟩
  step with load_spec hw b0 as ⟨m0,hm0⟩
  step as ⟨b1,hb1⟩
  step with load_spec hw b1 as ⟨m1,hm1⟩
  let iv := Array.make 4#usize [a,b,c,d]
  let L := initialState (S512.wv st.val) (bytes b0.val)
  let R := initialState (S512.wv st.val) (bytes b1.val)
  have hiv : iv.val = [vOf2 (S512.wv st.val) 0, vOf2 (S512.wv st.val) 2,
      vOf2 (S512.wv st.val) 4, vOf2 (S512.wv st.val) 6] := by
    simp only [Array.val_to_slice] at ha hb hc hd
    simp only [iv, ha, hb, hc, hd]; rfl
  have l0 : After ⟨iv,m0⟩ L 0 := by
    unfold After lane state L initialState
    simp only [hiv, hm0]; rfl
  have r0 : After ⟨iv,m1⟩ R 0 := by
    unfold After lane state R initialState
    simp only [hiv, hm1]; rfl
  iterate 40
    apply WP.spec_bind (advance hw _ _ _ L R (by decide) (by assumption) (by assumption))
    rintro ⟨l,r⟩ ⟨hl,hr⟩
  step*
  · rw [index_mut_back_post]
    rw [Slice.set_length]
    change 1 < out.length
    omega
  · change (a5.val = _) at a5_post
    have f0 := finish N (S512.wv st.val) (bytes b0.val) iv l hiv hl hn
    have f1 := finish N (S512.wv st.val) (bytes b1.val) iv r hiv hr hn
    change a5.val = encode ((firstFour iv l.state).take (N.val/8)) at a5_post
    change a7.val = encode ((firstFour iv r.state).take (N.val/8)) at a7_post
    rw [f0] at a5_post
    rw [f1] at a7_post
    have both : blocks.val = [b0,b1] := by
      rw [hb0,hb1]
      simpa only [getElem!_pos blocks.val 0 (by scalar_tac), getElem!_pos blocks.val 1 (by scalar_tac)] using
        elements2 blocks.val (by scalar_tac)
    rw [index_mut_back1_post, index_mut_back_post, Slice.set_val_eq, Slice.set_val_eq]
    change List.map _ ((out.val.set 0 a5).set 1 a7) = _
    rw [write2 _ _ _ ho, both]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, a5_post, a7_post]

#print axioms parents_spec
#print axioms pair_spec
#print axioms lane_spec
#print axioms load_spec
end slhdsa.H512.Paired
