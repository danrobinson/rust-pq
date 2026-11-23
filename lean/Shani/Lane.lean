import Shani.Schedule
import Avx2.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open core.core_arch.x86
open ShaNiRust.sha256.x86

def Ring (w : Array Reg 4#usize) (W : List Word) (t : Nat) :=
  ∀ g, t-4 ≤ g → g < max 4 t → w.val[g%4]! = group W (4*g)

def Work (v : Array Reg 2#usize) (s : State) := v.val[0]! = abef s ∧ v.val[1]! = cdgh s

def Good (l : ShaLane) (W : List Word) (init : State) (t : Nat) :=
  Ring l.words W t ∧ Work l.work (after W init (4*t))

def Rec (W : List Word) := ∀ k, 16 ≤ k → k < 64 → W[k]! = Spec.SHA256.ssig1 W[k-2]! +
  W[k-7]! + Spec.SHA256.ssig0 W[k-15]! + W[k-16]!

private theorem read_reg {n : Usize} (a : Array Reg n) (i : Usize) (h : i.val < n.val) :
    a.index_usize i = ok (a.val[i.val]!) := by
  have hi : i.val < a.val.length := by simpa using h
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

set_option maxHeartbeats 1200000 in
theorem lane_spec (t : Usize) (l : ShaLane) (k : Reg) (W : List Word) (init : State) (ht : t.val < 16)
    (hg : Good l W init t.val) (hk : k = group Spec.SHA256.K (4*t.val)) (rec : Rec W) :
    lane_group t l k ⦃ r => Good r W init (t.val+1) ⦄ := by
  obtain ⟨hr,hw⟩ := hg
  unfold lane_group
  step as ⟨slot,hslot⟩
  apply WP.spec_bind (Pₘ := fun r => Ring r W (t.val+1) ∧ r.val[slot.val]! = group W (4*t.val))
  · split
    · have h4 : 4 ≤ t.val := by scalar_tac
      simp only [sha._mm_sha256msg1_epu32, align4, sse2._mm_add_epi32, sha._mm_sha256msg2_epu32, bind_ok]
      step*
      have read (v : Reg) (idx : Usize) (g : Nat) (ev : v = l.words.val[idx.val]!) (ei : idx.val = g%4)
          (lo : t.val-4 ≤ g) (hi : g < t.val) : v = group W (4*g) := by
        rw [ev,ei]; exact hr _ lo (by omega)
      have ha := read mi slot (t.val-4) (by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi_post) (by omega) (by omega) (by omega)
      have hb := read mi1 i2 (t.val-3) (by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi1_post) (by omega) (by omega) (by omega)
      have hc := read mi3 i6 (t.val-2) (by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi3_post) (by omega) (by omega) (by omega)
      have hd := read mi2 i4 (t.val-1) (by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi2_post) (by omega) (by omega) (by omega)
      have hd' := read mi5 i7 (t.val-1) (by rw [getElem!_pos _ _ (by scalar_tac)]; exact mi5_post) (by omega) (by omega) (by omega)
      let p := 4*(t.val-4)
      have ex := expand_spec W p (by dsimp [p]; omega) rec
      simp only [expand, align4, sse2._mm_add_epi32, sha._mm_sha256msg1_epu32, sha._mm_sha256msg2_epu32, bind_ok, ok.injEq] at ex
      have hn : r.val[slot.val]! = group W (4*t.val) := by
        rw [r_post, Array.set_val_eq, Avx2.setSame _ _ _ (by scalar_tac)]
        rw [ha,hb,hc,hd,hd']
        simpa only [show p+4 = 4*(t.val-3) by dsimp [p]; omega,
          show p+8 = 4*(t.val-2) by dsimp [p]; omega, show p+12 = 4*(t.val-1) by dsimp [p]; omega,
          show p+16 = 4*t.val by dsimp [p]; omega] using ex
      refine ⟨?_,hn⟩
      intro g lo hi
      by_cases eq : g = t.val
      · subst g; simpa only [hslot] using hn
      · rw [r_post, Array.set_val_eq, Avx2.setOther _ _ _ _ (by omega)]
        exact hr _ (by omega) (by omega)
    · have h4 : t.val < 4 := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, ?_⟩
      · intro g lo hi; exact hr _ (by omega) (by omega)
      · rw [hslot]; exact hr _ (by omega) (by omega)
  · rintro w ⟨hr',hget⟩
    simp (disch := first | decide | scalar_tac) only [read_reg, bind_ok]
    rw [hget,hk]
    obtain ⟨h0,h1⟩ := hw
    simp only [show (0#usize).val = 0 by rfl, show (1#usize).val = 1 by rfl, h0,h1]
    rw [abef_rounds (fun l h => ok ({work := Array.make 2#usize [l,h], words := w} : ShaLane))]
    simp only [step_simps]
    refine ⟨hr', ?_⟩
    rw [show 4*(t.val+1) = 4*t.val+4 by omega]
    exact ⟨rfl,rfl⟩
#print axioms lane_spec

end slhdsa.Intel
