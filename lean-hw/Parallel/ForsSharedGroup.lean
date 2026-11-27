import Parallel.ForsNativeField
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

private theorem coordinates (q w lane : Nat) (inside : lane<w) :
    groupFirst w (q*w+lane)=q*w ∧ (q*w+lane)%w=lane := by
  have pos : 0<w := by omega
  constructor
  · unfold groupFirst
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt inside,Nat.zero_add]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt inside]

private theorem journal_spec {N} (mode : Mode) (d : Data N) (valid : Valid d) (first : U16) (active depth : U8)
    (grouped : mode.policy≠.scalar) (bounded : active.val≤width mode.policy)
    (capacity : first.val+active.val≤d.choices.length) (pos : 0<active.val) (height : depth.val≤d.p.a.val)
    (narrow : mode.policy=.three ∨ depth.val≤3) :
    lowJournal mode d first active depth ⦃ rows => ParallelLowFors.Fields first.val active.val d.stride.val (depth.val+1) (ParallelLowFors.field d.p d.sk d.seed d.addr d.choices) rows ⦄ := by
  have count : d.choices.length≤35 := by rw [valid.count];exact valid.pn.valid.k_le
  cases mode with
  | fallback h => exact False.elim (grouped rfl)
  | linux => exact (@ParallelLowFors.linux_spec unreachableLow N d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height valid.stride)
  | apple b => exact (ParallelLowFors.apple_spec b d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height (narrow.resolve_left (by simp [Mode.policy])) valid.stride)
  | x86 flag => exact (ParallelLowFors.x86_spec flag d.p valid.pn d.sk d.seed d.addr d.choices first active depth d.stride
      valid.domain valid.pn.valid.a_le count valid.digits pos bounded capacity height (narrow.resolve_left (by simp [Mode.policy])) valid.stride)

/-- One successful low FORS group call supplies all its secret and
authentication fields. The public field projection reads exactly these returned physical rows. -/
theorem shared_low {N} (mode : Mode) (d : Data N) (valid : Valid d) (q : Nat)
    (grouped : mode.policy≠.scalar) (issued : q*width mode.policy<d.choices.length) :
    let w := width mode.policy
    let first := q*w
    let active := min (d.choices.length-first) w
    let D := low mode.policy d.p.a.val
    ∃ journal, lowJournal mode d (word .U16 first) (word .U8 active) (word .U8 D)=ok journal ∧
      ParallelLowFors.Fields first active d.stride.val (D+1) (ParallelLowFors.field d.p d.sk d.seed d.addr d.choices) journal ∧
      ∀ lane<active, ∀ col≤D, nativeAction mode d (first+lane) col=ok journal.val[col*active+lane]! := by
  dsimp only
  let w := width mode.policy
  let first := q*w
  let active := min (d.choices.length-first) w
  let D := low mode.policy d.p.a.val
  have maxK : d.choices.length≤35 := by rw [valid.count];exact valid.pn.valid.k_le
  have maxA : d.p.a.val≤14 := valid.pn.valid.a_le
  have pos : 0<w := by cases mode <;> simp [w,Mode.policy,width]
  have size : w≤8 := by cases mode <;> simp [w,Mode.policy,width]
  have live : 0<active := Nat.lt_min.mpr ⟨by change first<d.choices.length at issued;omega,pos⟩
  have bound : active≤w := Nat.min_le_right ..
  have Dle : D≤d.p.a.val := by unfold D low;split <;> exact Nat.min_le_left ..
  have Dval : (word .U8 D).val=D := word_eq _ (by change D<256;omega)
  have fval : (word .U16 first).val=first := word_eq _ (by change first<d.choices.length at issued; change first<65536;omega)
  have aval : (word .U8 active).val=active := word_eq _ (by change active<256;omega)
  have capacity : first+active≤d.choices.length := by have part : active≤d.choices.length-first := Nat.min_le_left ..;omega
  have run : lowJournal mode d (word .U16 first) (word .U8 active) (word .U8 D) ⦃ journal =>
      ParallelLowFors.Fields first active d.stride.val (D+1) (ParallelLowFors.field d.p d.sk d.seed d.addr d.choices) journal ⦄ := by
    have short : mode.policy=.three ∨ D≤3 := by
      by_cases three : mode.policy=.three
      · exact Or.inl three
      · have eight : mode.policy=.eight := by cases e : mode.policy <;> simp_all
        right;change low mode.policy d.p.a.val≤3;rw [eight];exact Nat.min_le_right ..
    simpa only [fval,aval,Dval] using journal_spec mode d valid (word .U16 first) (word .U8 active) (word .U8 D)
      grouped (by simpa only [aval] using bound) (by simpa only [fval,aval] using capacity)
      (by simpa only [aval] using live) (by simpa only [Dval] using Dle) (by simpa only [Dval] using short)
  obtain ⟨journal,called,fields⟩ := spec_imp_exists run
  refine ⟨journal,called,fields,?_⟩
  intro lane inside col lo
  have coord := coordinates q w lane (inside.trans_le bound)
  change nativeAction mode d (first+lane) col=ok journal.val[col*active+lane]!
  change col≤low mode.policy d.p.a.val at lo
  unfold nativeAction selectAction
  simp only [ite_eq_left lo,ite_eq_right grouped]
  change groupedLow mode d (word .U16 (groupFirst w (q*w+lane))) (word .U8 (min (d.choices.length-groupFirst w (q*w+lane)) w))
    (word .U8 D) col ((q*w+lane)%w) = _
  rw [coord.1,coord.2]
  unfold groupedLow
  rw [called,bind_ok,aval]

/-- The width-three upper direct group writes one row per live lane from the same
native call, including when the final group contains only one or two trees. -/
theorem shared_direct {N} (d : Data N) (valid : Valid d) (q h : Nat) (issued : q*3<d.choices.length)
    (height : h<d.p.a.val) (above : low .three d.p.a.val<h+1) (direct : h≤target .three d.p.a.val) :
    let first := q*3
    let active := min (d.choices.length-first) 3
    ∃ rows, @ParallelForsTicket.direct_ticket unreachableHigh N d.sk d.seed d.addr d.choices d.p.a
        (word .U16 first) (word .U8 active) (word .U8 h) d.stride=ok rows ∧
      ∀ lane<active, nativeAction .linux d (first+lane) (h+1)=ok rows.val[lane]! ∧
        Value d (first+lane) (h+1) rows.val[lane]! := by
  dsimp only
  let first := q*3
  let active := min (d.choices.length-first) 3
  have limit : d.choices.length≤35 := by rw [valid.count];exact valid.pn.valid.k_le
  have hmax : d.p.a.val≤14 := valid.pn.valid.a_le
  change first<d.choices.length at issued
  have bound : active≤3 := Nat.min_le_right ..
  have live : 0<active := Nat.lt_min.mpr ⟨by omega,by decide⟩
  have cap : first+active≤d.choices.length := by have hp : active≤d.choices.length-first := Nat.min_le_left ..;omega
  have fv : (word .U16 first).val=first := word_eq _ (by change first<65536;omega)
  have av : (word .U8 active).val=active := word_eq _ (by change active<256;omega)
  have hv : (word .U8 h).val=h := word_eq _ (by change h<256;omega)
  obtain ⟨rows,call,fields⟩ := spec_imp_exists (@ParallelForsTicket.direct_ticket_spec unreachableHigh N d.p valid.pn
    d.sk d.seed d.addr d.choices (word .U16 first) (word .U8 active) (word .U8 h) d.stride valid.domain hmax
    (by simpa [hv] using height) limit (by simpa [av] using live) (by simpa [av] using bound)
    (by simpa [av,fv] using cap) valid.digits valid.stride)
  refine ⟨rows,call,?_⟩
  intro lane inside
  have coord := coordinates q 3 lane (inside.trans_le bound)
  obtain ⟨dest,digest⟩ := fields lane (by rwa [av])
  constructor
  · unfold nativeAction selectAction
    simp only [Mode.policy,width,Nat.add_sub_cancel,ite_eq_right (Nat.not_le.mpr above),ite_eq_left direct,ite_true]
    rw [coord.1,coord.2]
    unfold groupedDirect
    rw [call,bind_ok]
  · simpa [Value,ParallelLowFors.field,hv,fv,valid.stride,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using And.intro dest digest

/-- The scalar fallback also computes all low columns in a single invocation. -/
theorem shared_scalar {N} (host : ParallelScalarFors.Platform) (d : Data N) (valid : Valid d) (t : Nat) (tree : t<d.p.k.val) :
    let depth := low .scalar d.p.a.val
    ∃ rows, ParallelScalarFors.hostedLow host d.p d.sk d.seed d.addr d.choices (word .U32 t) d.p.a (word .U32 depth) d.stride default = ok rows ∧
      ∀ c≤depth, nativeAction (.fallback host) d t c=ok (if c=0 then rows.1 else rows.2.val[c-1]!) := by
  dsimp only
  let depth := low .scalar d.p.a.val
  have small : depth≤d.p.a.val := Nat.min_le_left ..
  have hmax : d.p.a.val≤14 := valid.pn.valid.a_le
  have kmax : d.p.k.val≤35 := valid.pn.valid.k_le
  have tv : (word .U32 t).val=t := word_eq _ (by change t<4294967296;omega)
  have hv : (word .U32 depth).val=depth := word_eq _ (by change depth<4294967296;omega)
  have inside : (word .U32 t).val<d.choices.length := by rw [tv,valid.count];exact tree
  obtain ⟨rows,run,_⟩ := spec_imp_exists (ParallelScalarFors.low_published host d.p valid.pn d.sk d.seed d.addr valid.domain d.choices
    (word .U32 t) d.p.a (word .U32 depth) d.stride default inside (by rw [tv];omega) hmax (valid.digits _ inside)
    (by rwa [hv]) valid.stride)
  refine ⟨rows,run,?_⟩
  intro c inRange
  unfold nativeAction selectAction
  simp only [Mode.policy,ite_eq_left inRange,ite_true,Mode.host,scalarLow]
  dsimp only [depth] at run
  rw [run,bind_ok]

end slhdsa.RawFors
