import Wots.Plan
import Chainwrite.Index
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512

abbrev LaneArray := Array I32 16#usize
abbrev FillState := LaneArray × LaneArray × U16 × Usize × U16

def enabled (mask : U16) (j : Fin 16) := mask.bv.getLsbD j.val

/-- One iteration installs a signature index and its digit in a previously free
lane, advances one queue position and sets exactly that bit in both masks. -/
def installed (digits : Slice U32) (order : Order) (old newState : FillState) (lane : Fin 16) :=
  let (indices,starts,active,pos,assigned) := old
  let (indices',starts',active',pos',assigned') := newState
  let index := order.val[pos.val]!
  enabled active lane = false ∧ pos'.val = pos.val+1 ∧
    (∀ j, enabled active' j = (enabled active j || decide (j=lane))) ∧
    (∀ j, enabled assigned' j = (enabled assigned j || decide (j=lane))) ∧
    (∀ j : Fin 16, indices'.val[j.val]! =
      if j=lane then UScalar.hcast .I32 index else indices.val[j.val]!) ∧
    ∀ j : Fin 16, starts'.val[j.val]! =
      if j=lane then UScalar.hcast .I32 digits.val[index.val]! else starts.val[j.val]!

private theorem free_lane (m : U16) (room : m ≠ core.num.U16.MAX) :
    ∃ j : Fin 16, (Chain.firstLane (~~~m)).val = j.val ∧ enabled m j = false := by
  have nz : (~~~m).bv ≠ 0 := by
    intro h
    apply room
    apply UScalar.eq_of_val_eq
    apply congrArg BitVec.toNat
    change ~~~m.bv = 0 at h
    have eq := congrArg (fun v : BitVec 16 => ~~~v) h
    change m.bv = 65535#16
    simpa using eq
  have first := Chain.first_val (~~~m) nz
  have lt := BitVec.ctz_lt_iff_ne_zero.mpr nz
  change (~~~m).bv.ctz.toNat < 16 at lt
  refine ⟨⟨_,lt⟩,first,?_⟩
  have bit := BitVec.getLsbD_true_ctz_of_ne_zero nz
  change (~~~m.bv).getLsbD _ = true at bit
  simp only [BitVec.getLsbD_not,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at bit
  exact bit.2

private theorem mask_bit (m bit : U16) (lane : Fin 16)
    (hv : bit.val = (1 <<< lane.val) % U16.size) (j : Fin 16) :
    enabled (m ||| bit) j = (enabled m j || decide (j=lane)) := by
  have bv : bit.bv = (1 : BitVec 16) <<< lane.val := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft]; simpa [U16.size,U16.numBits] using hv
  unfold enabled
  change (m.bv ||| bit.bv).getLsbD _ = _
  rw [bv,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft]
  congr 1
  simp [j.isLt,BitVec.getLsbD_one,Fin.ext_iff]
  by_cases lt : j < lane
  · simp [lt,show j.val ≠ lane.val by change j.val < lane.val at lt; omega]
  · simp [lt,Nat.sub_eq_zero_iff_le]; change ¬j.val < lane.val at lt; omega

theorem install_step (digits : Slice U32) (order : Order) (work : Usize)
    (indices starts : LaneArray) (active : U16) (pos : Usize) (assigned : U16)
    (room : active ≠ core.num.U16.MAX) (pending : pos.val < work.val) (cap : work.val ≤ 67)
    (indexOK : order.val[pos.val]!.val < digits.length) :
    recover_loop5_loop0.body digits order work indices starts active pos assigned ⦃ flow =>
      ∃ s lane, flow = cont s ∧ installed digits order (indices,starts,active,pos,assigned) s lane ⦄ := by
  obtain ⟨lane,hl,free⟩ := free_lane active room
  unfold recover_loop5_loop0.body
  simp only [bne_iff_ne,if_pos room,if_pos (show pos < work from pending),lift,
    WotsRust.core.num.U16.trailing_zeros,ChainWriteRust.core.num.U16.trailing_zeros,bind_ok]
  step as ⟨index,hi⟩
  step as ⟨p,hp⟩
  step as ⟨ix,hix⟩
  all_goals try (change (Chain.firstLane (~~~active)).val < 16; rw [hl]; exact lane.isLt)
  step as ⟨digit,hd⟩
  all_goals try (rw [hi,← getElem!_pos]; exact indexOK)
  step as ⟨st,hst⟩
  step as ⟨bit,hbit⟩
  all_goals try (change (Chain.firstLane (~~~active)).val < 16; rw [hl]; exact lane.isLt)
  refine ⟨_,lane,rfl,free,?_,?_,?_,?_,?_⟩
  · omega
  · exact mask_bit active bit lane (by simpa only [← hl] using hbit)
  · exact mask_bit assigned bit lane (by simpa only [← hl] using hbit)
  all_goals intro j
  all_goals simp only [hix,hst,Array.set_val_eq,show (Chain.firstLane (~~~active)).val = lane.val from hl,
    ← getElem!_pos,hi,hd]
  all_goals by_cases eq : j=lane
  all_goals first
    | subst j; rw [if_pos rfl,Avx2.setSame _ _ _ (by simp)]
    | rw [if_neg eq,Avx2.setOther _ _ _ _ (fun h => eq (Fin.ext h.symm))]

inductive FillHistory (digits : Slice U32) (order : Order) (initial : FillState) : FillState → Prop where
  | empty : FillHistory digits order initial initial
  | push {s t} (lane : Fin 16) : FillHistory digits order initial s →
      installed digits order s t lane → FillHistory digits order initial t

/-- The actual refill loop terminates with either all lanes active or all tasks
consumed. Each transition consumes the next queued task into a free lane. -/
theorem refill_loop (digits : Slice U32) (order : Order) (work : Usize)
    (indices starts : LaneArray) (active : U16) (pos : Usize)
    (startOK : pos.val ≤ work.val) (cap : work.val ≤ 67)
    (indexOK : ∀ i < work.val, order.val[i]!.val < digits.length) :
    recover_loop5_loop0 digits order work indices starts active pos 0#u16 ⦃ result =>
      let (_,_,mask,p,_) := result
      FillHistory digits order (indices,starts,active,pos,0#u16) result ∧
      p.val ≤ work.val ∧ (mask = core.num.U16.MAX ∨ p = work) ⦄ := by
  unfold recover_loop5_loop0
  let initial : FillState := (indices,starts,active,pos,0#u16)
  apply loop.spec_decr_nat (measure := fun s : FillState => work.val-s.2.2.2.1.val)
    (inv := fun s => FillHistory digits order initial s ∧ s.2.2.2.1.val ≤ work.val)
  · rintro ⟨ix,st,m,p,a⟩ ⟨history,le⟩
    simp only at le
    by_cases full : m = core.num.U16.MAX
    · simp only [recover_loop5_loop0.body,bne_iff_ne,if_neg (not_not_intro full),step_simps]
      exact ⟨history,le,Or.inl full⟩
    · by_cases pending : p.val < work.val
      · apply WP.spec_mono (install_step digits order work ix st m p a full pending cap (indexOK _ pending))
        rintro flow ⟨⟨ix',st',m',p',a'⟩,lane,rfl,update⟩
        have inc := update.2.1
        change p'.val = p.val+1 at inc
        refine ⟨⟨.push lane history update,?_⟩,?_⟩ <;> simp only <;> omega
      · have eq : p=work := UScalar.eq_of_val_eq (by omega)
        simp only [recover_loop5_loop0.body,bne_iff_ne,if_pos full,if_neg (show ¬p<work from pending),step_simps]
        exact ⟨history,le,Or.inr eq⟩
  · exact ⟨.empty,startOK⟩


/-- A lane either retains its previous state or owns one position in the exact
queue interval consumed by this refill. Each such position has one owner. -/
def mapped (digits : Slice U32) (order : Order) (ix st : LaneArray) (active : U16) (start : Usize)
    (s : FillState) :=
  let (ix',st',m,p,a) := s
  ∃ job : Fin 16 → Option Nat, start.val ≤ p.val ∧
    (∀ q, start.val ≤ q → q < p.val → ∃! j, job j = some q) ∧
    ∀ j, match job j with
      | none => enabled a j = false ∧ enabled m j = enabled active j ∧
          ix'.val[j.val]! = ix.val[j.val]! ∧ st'.val[j.val]! = st.val[j.val]!
      | some q => start.val ≤ q ∧ q < p.val ∧ enabled active j = false ∧ enabled a j = true ∧
          enabled m j = true ∧ ix'.val[j.val]! = UScalar.hcast .I32 order.val[q]! ∧
          st'.val[j.val]! = UScalar.hcast .I32 digits.val[order.val[q]!.val]!

theorem history_mapped {digits order ix st active start s}
    (h : FillHistory digits order (ix,st,active,start,0#u16) s) :
    mapped digits order ix st active start s := by
  induction h with
  | empty =>
    refine ⟨fun _ => none,by rfl,fun _ _ _ => by omega,?_⟩
    intro j
    simp [enabled]
  | @push prev next lane _ installed ih =>
    obtain ⟨px,ps,pm,pp,pa⟩ := prev
    obtain ⟨nx,ns,nm,np,na⟩ := next
    obtain ⟨free,inc,mask,assigned,index,digit⟩ := installed
    obtain ⟨job,le,unique,lanes⟩ := ih
    have vacant : job lane = none := by
      cases e : job lane with
      | none => rfl
      | some q => have v := lanes lane; rw [e] at v; simp only at v; simp_all
    let job' := fun j => if j=lane then some pp.val else job j
    refine ⟨job',by omega,?_,?_⟩
    · intro q first last
      by_cases newest : q=pp.val
      · subst q
        refine ⟨lane,by simp [job'],?_⟩
        intro j assigned
        by_contra other
        simp only [job',if_neg other] at assigned
        have v := lanes j
        rw [assigned] at v; simp only at v; omega
      · obtain ⟨j,hj,uniqueOwner⟩ := unique q first (by omega)
        have different : j ≠ lane := by intro eq; subst j; rw [vacant] at hj; contradiction
        refine ⟨j,by simpa [job',different] using hj,?_⟩
        intro k hk
        by_cases e : k=lane
        · subst k; simp [job',Ne.symm newest] at hk
        · exact uniqueOwner k (by simpa [job',e] using hk)
    · intro j
      by_cases e : j=lane
      · subst j
        have v := lanes lane
        rw [vacant] at v
        simp only at v
        simp only [job',if_pos rfl,mask,assigned,index,digit,decide_true,Bool.or_true]
        exact ⟨le,by omega,v.2.1 ▸ free,True.intro,True.intro,rfl,rfl⟩
      · have v := lanes j
        simp only [job',if_neg e,mask,assigned,index,digit,decide_eq_false e,Bool.or_false]
        cases eq : job j with
        | none => simpa only [eq] using v
        | some q =>
          rw [eq] at v; simp only at v
          exact ⟨v.1,by omega,v.2.2⟩

theorem refill_spec (digits : Slice U32) (order : Order) (work : Usize)
    (indices starts : LaneArray) (active : U16) (pos : Usize)
    (startOK : pos.val ≤ work.val) (cap : work.val ≤ 67)
    (indexOK : ∀ i < work.val, order.val[i]!.val < digits.length) :
    recover_loop5_loop0 digits order work indices starts active pos 0#u16 ⦃ s =>
      mapped digits order indices starts active pos s ∧ s.2.2.2.1.val ≤ work.val ∧
        (s.2.2.1 = core.num.U16.MAX ∨ s.2.2.2.1 = work) ⦄ := by
  apply WP.spec_mono (refill_loop digits order work indices starts active pos startOK cap indexOK)
  rintro ⟨ix,st,m,p,a⟩ ⟨hist,le,stop⟩
  exact ⟨history_mapped hist,le,stop⟩

end slhdsa.X86.Wots
