import Integration.SlhDsaShakePermutationLongSelectGame

/-! Reading an output's padded blocks certifies acceptance on a short extension of the selected forest. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic MLink OracleComp OracleComp.PermutationConditioning
noncomputable section
set_option maxRecDepth 8192

def word (r : Rate) (w : Words) := join (rateXor r (rateOf w)) (capOf w)

def freshPath (π : Permutation) (t : Trace) (w : Words) : List Rate → Trace
  | [] => []
  | r::rs =>
    let x := word r w
    let y := π x
    if (x,y) ∈ t then freshPath π t y rs else freshPath π ((x,y)::t) y rs ++ [(x,y)]

private theorem walk (π : Permutation) (t : Trace) (p rs : List Rate) (s : Words) (tr : Trail t p s) :
    let extra := freshPath π t s rs
    extra.length ≤ rs.length ∧ extra.Nodup ∧ (∀ e ∈ extra, e ∉ t ∧ π e.1 = e.2) ∧
    Trail (extra++t) (p++rs) (rs.foldl (fun w r => π (word r w)) s) := by
  induction rs generalizing t p s with
  | nil => exact ⟨le_rfl,by simp [freshPath],by simp [freshPath],by simpa [freshPath] using tr⟩
  | cons r rs ih =>
    let x := word r s
    let y := π x
    have step' {u : Trace} (h : Trail u p s) (mem : (x,y) ∈ u) : Trail u (p++[r]) y := by
      have path := h.step mem (show capOf s = capOf x from (cap_join _ _).symm)
      simpa [nextBlock,x,word] using path
    by_cases prior : (x,y) ∈ t
    · obtain ⟨len,nod,sub,end'⟩ := ih t _ y (step' tr prior)
      simp only [freshPath,show word r s = x from rfl,show π x = y from rfl,ite_eq_left prior,List.length_cons,List.foldl_cons]
      exact ⟨by omega,nod,sub,by simpa using end'⟩
    · let u := (x,y)::t
      obtain ⟨len,nod,sub,end'⟩ := ih u _ y (step' (tr.weaken (fun _ h => List.mem_cons_of_mem _ h)) (List.mem_cons_self ..))
      simp only [freshPath,show word r s = x from rfl,show π x = y from rfl,ite_eq_right prior,List.length_cons,List.foldl_cons]
      let extra := freshPath π u y rs
      have new : (x,y) ∉ extra := fun mem => (sub _ mem).1 (List.mem_cons_self ..)
      refine ⟨by simpa using len,?_,?_,?_⟩
      · exact List.nodup_append.mpr ⟨nod,by simp,by intro e he z hz hez; obtain rfl := List.mem_singleton.mp hz; exact new (hez ▸ he)⟩
      · intro e he
        rcases List.mem_append.mp he with h|h
        · exact ⟨fun h' => (sub e h).1 (List.mem_cons_of_mem _ h'),(sub e h).2⟩
        · obtain rfl := List.mem_singleton.mp h; exact ⟨prior,rfl⟩
      · simpa [u,x,y] using end'

theorem certify (S : Sha2Set) (t : Trace) (π : Extensions t) (dest : List Rate → Option S.Node) (p : List Rate)
    (len : p.length ≤ 17) (win : hits S dest π.val p) :
    ∃ extra : Trace, extra.length ≤ 17 ∧ extra.Nodup ∧ (∀ e ∈ extra, e ∉ t ∧ π.val e.1=e.2) ∧
      bad (SkFormat.split S) dest (extra++t) := by
  obtain ⟨hn,nd,extras,tr⟩ := walk π.val t [] p 0 .root
  exact ⟨_,hn.trans len,nd,extras,Or.inr ⟨p,Fix.ordinary π.val p,tr,win⟩⟩
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.certify
