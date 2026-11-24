import Integration.SlhDsaShakePermutationLongBankPath

/-! The target for a candidate overwrite path is fixed by the phase-one
transcript. Proper prefixes cannot match the padded arity length, and the full
honest overwrite path is excluded. Different payloads can share a tweak while
having different first blocks, so only the tweak field of that block is used. -/
namespace Reduction.ShakePermutation.Long.BankRun
open Classical ItsrLabel SparsePort MLink SLHDSA Tails PQ.Interactive
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
variable (S : Sha2Set) (pk : S.Node) (ar : ℕ) (π : Permutation) (H : Table)
local notation "blocksAt" => Long.blocks S pk

def accepts (rows : List (Arity.Row S ar)) (p : List Rate) (j : Arity.Row S ar) : Prop :=
  j ∈ rows ∧ (∃ xs, p.head? = (blocksAt j.1 xs).head?) ∧
    p.length = (blocksAt j.1 j.2.val).length ∧ p ≠ (report π H (blocksAt j.1 j.2.val)).path.reverse

def assignment (rows : List (Arity.Row S ar)) (p : List Rate) : Option S.Node :=
  if h : ∃ j, accepts S pk ar π H rows p j then
    let j := h.choose
    some ((SkFormat.split S (result (report π H (blocksAt j.1 j.2.val)))).1)
  else none

private theorem possible {rows p v} (h : assignment S pk ar π H rows p = some v) :
    ∃ j, accepts S pk ar π H rows p j := by
  unfold assignment at h
  split at h
  · assumption
  · contradiction

private theorem clear {h D log} (ok : Recorded S pk ar π H h D log) (g : graphClean π D) :
    Target.Good S π 17 (assignment S pk ar π H h.1) (masks D false) (masks D true) (held D) := by
  refine Target.good_of_clear g (fun path pre z y _ run has hit => ?_)
  obtain ⟨j,hj,⟨xs,first⟩,hlen,deny⟩ := possible S pk ar π H hit
  obtain ⟨v,cell,vy⟩ := Option.map_eq_some_iff.mp has
  obtain ⟨⟨d,ys⟩,seen,p,pref,endAt,known⟩ := ok.cover z v cell
  have replayed := (logged π H D p.reverse known).1
  have trail : Graph.Tail (layout π) (masks D false) (masks D true) (report π H p).path.reverse (report π H p).cap :=
    (Relabel.run_tail ..).mp ⟨(report π H p).pre,by simpa only [report,List.reverse_reverse] using replayed⟩
  have same : path = (report π H p).path.reverse := g.uniqueTail ((Relabel.run_tail ..).mp ⟨_,run⟩) (endAt ▸ trail)
  rw [same,overwrite_eq,fix_first] at first
  have plen : p.length = (blocksAt j.1 j.2.val).length := by
    simpa only [same,overwrite_eq,Fix.fix_length] using hlen
  have pn : p ≠ [] := by
    intro emp
    rw [emp] at plen
    simp only [List.length_nil,Long.blocks,messageBlocks_length] at plen
    omega
  have first_p : p.head? = (blocksAt d ys).head? := by
    obtain ⟨tail,eq⟩ := pref
    rw [← eq]
    cases p with
    | nil => exact False.elim (pn rfl)
    | cons b bs => rfl
  have addr : d = j.1 := same_tweak S pk d j.1 ys xs (first_p.symm.trans first)
  subst d
  have msg : ys = j.2.val := ok.messages j hj ys seen
  rw [msg] at pref
  exact deny (same.trans (congrArg (fun q => (report π H q).path.reverse) (pref.eq_of_length plen)))

private theorem winning {h D log} (ok : Recorded S pk ar π H h D log) (F : Table) (pin : Pins D F)
    (jm : ℕ × Arity.Msg S ar) (win : tcrWin h.1 (SelectTrace.row S pk ar (perm π F)) jm) :
    Target.hit S (perm π F) (assignment S pk ar π H h.1) (SelectTrace.path S pk ar h.1 jm) := by
  obtain ⟨⟨d,m⟩,idx,ne,eq⟩ := win
  have mem := List.mem_of_getElem? idx
  have addr : tweakAt h.1 jm.1 = d := by simp [tweakAt,idx]
  let w (x : List Rate) := Fix.fix (rateOf ∘ Fix.overwrite (perm π F)) x
  let candidate := blocksAt d jm.2.val
  let original := blocksAt d m.val
  have same : report π F original = report π H original := known_congr π pin (ok.target (d,m) mem)
  have ow_old : (report π H original).path.reverse = w original := by rw [← same,overwrite_eq]
  have no : w candidate ≠ (report π H original).path.reverse := by
    rw [ow_old]
    intro same
    have unmasked := (Fix.fixEquiv (rateOf ∘ Fix.overwrite (perm π F))).injective same
    have both : Long.encode S pk ar (d,jm.2) = Long.encode S pk ar (d,m) := unmasked
    exact ne (congrArg Prod.snd ((Long.encode S pk ar).injective both))
  have yes : ∃ j, accepts S pk ar π H h.1 (w candidate) j :=
    ⟨(d,m),mem,⟨jm.2.val,fix_first _ _⟩,(Fix.fix_length _ _).trans (same_length S pk ar d d jm.2 m),no⟩
  obtain ⟨old,⟨payload,hfirst⟩,_,_⟩ := yes.choose_spec
  have same_d : d = yes.choose.1 := same_tweak S pk d _ jm.2.val payload
    ((fix_first _ candidate).symm.trans hfirst)
  have logj := ok.logged yes.choose old
  rw [← same_d] at logj
  have same_m : yes.choose.2.val = m.val := ok.messages (d,m) mem _ logj
  have eqj : yes.choose = (d,m) := Prod.ext same_d.symm (Subtype.ext same_m)
  unfold Target.hit SelectTrace.path
  rw [addr]
  change assignment S pk ar π H h.1 (w candidate) = _
  rw [assignment,dite_eq_left yes]
  simp only [eqj]
  have row : (SkFormat.split S (result (report π H original))).1 = SelectTrace.row S pk ar (perm π F) (d,m) := by
    rw [← same,result_eq]; rfl
  exact congrArg some (row.trans eq.symm)

theorem target_ready (h : Select.History S ar) (D : Bank) (log : SelectTrace.Log S)
    (ok : Recorded S pk ar π H h D log) (gc : graphClean π D) :
    ∃ go : Target.Goal S, Target.label S π 17 go D = true ∧ ∀ F, Pins D F → ∀ jm,
      tcrWin h.1 (SelectTrace.row S pk ar (perm π F)) jm → Target.hit S (perm π F) go (SelectTrace.path S pk ar h.1 jm) :=
  ⟨assignment S pk ar π H h.1,decide_eq_true (clear S pk ar π H ok gc),winning S pk ar π H ok⟩

end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.target_ready
