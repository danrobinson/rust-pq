import Ct.ShakePermutation

/-! Public sponge positions and buffer lengths suffice to determine the SHAKE256 trace. -/

open Aeneas Aeneas.Std Ct slhdsa_leak

namespace Ct.Shake

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem update_length {x y : Slice U8} {i : Usize} {v : U8}
    (h : Aeneas.Std.Slice.update x i v = Result.ok y) : y.length = x.length := by
  unfold Aeneas.Std.Slice.update at h
  split at h
  · simp at h
  · simp only [Result.ok.injEq] at h
    subst y
    simp [Aeneas.Std.Slice.length]

/-- Both branches return a public cursor and secret lanes. Keep the cursor relation when
the loop continues past the permutation. -/
macro "sponge_steps" : tactic => `(tactic|
  repeat' first
    | (with_reducible refine Rel.bind_of (Rel.cond (R := fun x y => x.2 = y.2) rfl (fun _ _ => ?_) (fun _ _ => ?_)) (fun _ _ _ => ?_))
    | ct_step)

@[ct_rel] theorem absorb (a b : slhdsa.shake256.Sponge) (m m' : Slice U8)
    (hp : a.pos = b.pos) (hm : m.length = m'.length) :
    Rel (shake256.Sponge.absorb a m) (shake256.Sponge.absorb b m')
      (fun x y => x.pos = y.pos) := by
  unfold shake256.Sponge.absorb shake256.Sponge.absorb_loop
  refine Rel.loop (fun p q => p.1.pos = q.1.pos ∧ p.2 = q.2) ?_ ⟨hp,rfl⟩
  rintro ⟨⟨s,p⟩,i⟩ ⟨⟨s',p'⟩,i'⟩ ⟨(rfl : p=p'),(rfl : i=i')⟩
  unfold shake256.Sponge.absorb_loop.body
  simp only [(Facts.slice_len_congr hm).symm]
  sponge_steps
  all_goals simp_all

@[ct_rel] theorem squeeze (a b : Array U64 25#usize) (o o' : Slice U8) (pos i : Usize)
    (ho : o.length = o'.length) :
    Rel (shake256.Sponge.finish_loop a o pos i) (shake256.Sponge.finish_loop b o' pos i)
      (fun x y => x.length = y.length) := by
  unfold shake256.Sponge.finish_loop
  refine Rel.loop (fun p q => p.2.1.length = q.2.1.length ∧ p.2.2 = q.2.2) ?_ ⟨ho,rfl⟩
  rintro ⟨v,x,p,j⟩ ⟨w,y,p',j'⟩ ⟨hl,he⟩
  obtain ⟨rfl,rfl⟩ : p=p' ∧ j=j' := by simpa using he
  unfold shake256.Sponge.finish_loop.body
  simp only [(Facts.slice_len_congr hl).symm]
  sponge_steps
  all_goals try (simp_all; done)
  simp only [CFRel_cont_cont, and_true]
  exact (update_length (by assumption)).trans (hl.trans (update_length (by assumption)).symm)

@[ct_rel] theorem finish (a b : slhdsa.shake256.Sponge) (o o' : Slice U8)
    (hp : a.pos = b.pos) (ho : o.length = o'.length) :
    Rel (shake256.Sponge.finish a o) (shake256.Sponge.finish b o')
      (fun x y => x.length = y.length) := by
  rcases a with ⟨v,p⟩
  rcases b with ⟨w,q⟩
  change p = q at hp
  subst q
  unfold shake256.Sponge.finish
  ct_steps

theorem xof (m m' o o' : Slice U8) (hm : m.length = m'.length) (ho : o.length = o'.length) :
    Rel (shake256.shake256 m o) (shake256.shake256 m' o')
      (fun x y => x.length = y.length) := by
  unfold shake256.shake256
  ct_steps

end Ct.Shake
