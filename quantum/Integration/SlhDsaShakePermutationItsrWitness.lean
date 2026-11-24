import Integration.SlhDsaShakePermutationItsrReplay
import Integration.SlhDsaCompressionConstraintReadout

namespace Reduction.ShakePermutation.ItsrLabel
open Classical Tails MLink SLHDSA
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem cap_mask_eq (k : Mask) (w : Words) :
    capOf (ShakePermutation.mask k w) = xorCap (capOf w) (k (rateOf w)) := by
  funext i
  simp [capOf,ShakePermutation.mask,xorCap]

theorem mask_join_eq (k : Mask) (r : Rate) (z : Capacity) :
    ShakePermutation.mask k (join r z) = join r (xorCap z (k r)) := by
  rw [← join_split (ShakePermutation.mask k (join r z))]
  simp only [rate_mask,rate_join,cap_mask_eq,cap_join]

theorem step_result (π H p b) : result (step π H p b) =
    perm π H (join (rateXor b (rateOf (result p))) (capOf (result p))) := by
  simp only [step,push,result,perm,salted,masked,Equiv.trans_apply,maskEquiv,shearEquiv,
    Function.Involutive.toPerm,Equiv.coe_fn_mk,cap_join,mask_join_eq,shear,rate_mask,cap_mask_eq]
  rfl

private theorem blank : result empty = 0 := by
  change join (rateXor 0 0) 0 = _
  rw [← join_split (0 : Words)]
  congr 1
  funext i
  simp [rateXor,rateOf]

theorem replay_result (π H) (xs : List Rate) : result (replay π H xs) = Fix.ordinary (perm π H) xs.reverse := by
  induction xs with
  | nil => exact blank
  | cons b bs ih => simp only [replay,step_result,ih,List.reverse_cons,Fix.ordinary,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem replay_digest (S π H) (xs : List SLHDSA.Byte) :
    let w := replay π H (messageBlocks (sp xs)).reverse
    DigestTransport.coveringDigest S.vp (answer S (lanes (perm π H)) xs) = key S w.pre w.head := by
  dsimp only
  have e := replay_result π H (messageBlocks (sp xs)).reverse
  rw [List.reverse_reverse] at e
  rw [answer_blocks,← e]
  simp only [result,rate_join,key]

private theorem seen_report {S π H L D} {xs : List Rate} (ne : xs ≠ []) (len : xs.length ≤ L)
    (mem : Matches D (replay π H xs).log) :
    let w := replay π H xs
    Seen S π L (masks D false) (masks D true) (held D) w.cap (key S w.pre w.head) := by
  let w := replay π H xs
  have short : w.path.reverse.length ≤ L := by simpa only [w,List.length_reverse,(replay_length π H xs).2] using len
  let p := BList.ofList w.path.reverse short
  have hp : List.ofFn p.2 = w.path.reverse := List.ofFn_get _
  obtain ⟨hr,he⟩ := logged π H D xs mem
  exact ⟨p,w.pre,w.head,by simpa only [Relabel.visit,hp,List.reverse_reverse] using hr,he ne,rfl⟩

theorem certify (S π H L D) (xs ys : List Rate) (xs_ne : xs ≠ []) (ys_ne : ys ≠ [])
    (xlen : xs.length ≤ L) (ylen : ys.length ≤ L) (distinct : xs ≠ ys)
    (mem : Matches D ((replay π H xs).log ++ (replay π H ys).log))
    (digest : key S (replay π H xs).pre (replay π H xs).head = key S (replay π H ys).pre (replay π H ys).head) :
    label S π L D = false := by
  apply decide_eq_false
  intro good
  have mx : Matches D (replay π H xs).log := fun i y h => mem i y (List.mem_append_left _ h)
  have my : Matches D (replay π H ys).log := fun i y h => mem i y (List.mem_append_right _ h)
  have sx := seen_report (S := S) xs_ne xlen mx
  have sy := seen_report (S := S) ys_ne ylen my
  dsimp only at sx sy
  rw [← digest] at sy
  have same := good.2 _ _ _ sx sy
  obtain ⟨rx,_⟩ := logged π H D xs mx
  obtain ⟨ry,_⟩ := logged π H D ys my
  let x := replay π H xs
  let y := replay π H ys
  have tx : Graph.Tail (layout π) (masks D false) (masks D true) x.path.reverse x.cap :=
    (Relabel.run_tail ..).mp ⟨x.pre,by simpa only [List.reverse_reverse] using rx⟩
  have ty : Graph.Tail (layout π) (masks D false) (masks D true) y.path.reverse y.cap :=
    (Relabel.run_tail ..).mp ⟨y.pre,by simpa only [List.reverse_reverse] using ry⟩
  have paths := good.1.uniqueTail (same ▸ tx) ty
  exact distinct (replay_injective π H (List.reverse_injective paths))

end
end Reduction.ShakePermutation.ItsrLabel
