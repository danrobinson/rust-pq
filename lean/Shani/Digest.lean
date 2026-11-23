import Shani.Pair
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open core.core_arch.x86 ShaNiRust.sha256.x86
def stateWords (s : State) : List Word :=
  let (a,b,c,d,e,f,g,h) := s
  [a,b,c,d,e,f,g,h]

def serialize (ws : List Word) : List U8 := ws.flatMap fun w => w.toBEBytes.map (fun b => (⟨b⟩ : U8))

private theorem prefix_write (x s : List U8) (i : Nat) (h : i+s.length ≤ x.length) :
    (x.setSlice! i s).take (i+s.length) = x.take i ++ s := by
  simp only [List.setSlice!, min_eq_left (by omega : s.length ≤ x.length-i), List.take_length]
  have he : i+s.length = (x.take i ++ s).length := by simp [List.length_take, min_eq_left (by omega : i ≤ x.length)]
  rw [he, List.take_append_length]

private theorem write4 (x : Array U8 32#usize) (a : Array U8 4#usize) (i j : Nat) (he : i+4=j)
    (hj : j ≤ 32) : (x.val.setSlice! i a.val).take j = x.val.take i ++ a.val := by
  have h : a.val.length = 4 := by scalar_tac
  have eqn : j = i + a.val.length := by omega
  exact eqn ▸ prefix_write x.val a.val i (by scalar_tac)

set_option maxHeartbeats 2000000 in
theorem digest_spec (iv v : Array Reg 2#usize) (s u : State) (hi : Work iv s) (hu : Work v u) :
    digest_pair iv v ⦃ r => r.val = serialize (stateWords (X86.feedForward s u)) ⦄ := by
  rcases s with ⟨a0,b0,c0,d0,e0,f0,g0,h0⟩
  rcases u with ⟨a',b',c',d',e',f',g',h'⟩
  unfold digest_pair
  simp only [sse2._mm_add_epi32, sse41._mm_extract_epi32, bind_ok]
  step*
  all_goals try scalar_tac
  have p0 : (index_mut_back s2).val.take 4 = a.val := by
    rw [s_post2, s2_post, s1_post, Array.val_to_slice, write4 _ _ 0 4 (by decide) (by decide)]
    simp
  have p1 : (index_mut_back1 s5).val.take 8 = a.val ++ a1.val := by
    rw [s3_post2, s5_post, s4_post, Array.val_to_slice, write4 _ _ 4 8 (by decide) (by decide)]
    rw [p0]
  have p2 : (index_mut_back2 s8).val.take 12 = a.val ++ a1.val ++ a2.val := by
    rw [s6_post2, s8_post, s7_post, Array.val_to_slice, write4 _ _ 8 12 (by decide) (by decide)]
    rw [p1]
  have p3 : (index_mut_back3 s11).val.take 16 = a.val ++ a1.val ++ a2.val ++ a3.val := by
    rw [s9_post2, s11_post, s10_post, Array.val_to_slice, write4 _ _ 12 16 (by decide) (by decide)]
    rw [p2]
  have p4 : (index_mut_back4 s14).val.take 20 = a.val ++ a1.val ++ a2.val ++ a3.val ++ a4.val := by
    rw [s12_post2, s14_post, s13_post, Array.val_to_slice, write4 _ _ 16 20 (by decide) (by decide)]
    rw [p3]
  have p5 : (index_mut_back5 s17).val.take 24 = a.val ++ a1.val ++ a2.val ++ a3.val ++ a4.val ++ a5.val := by
    rw [s15_post2, s17_post, s16_post, Array.val_to_slice, write4 _ _ 20 24 (by decide) (by decide)]
    rw [p4]
  have p6 : (index_mut_back6 s20).val.take 28 = a.val ++ a1.val ++ a2.val ++ a3.val ++ a4.val ++ a5.val ++ a6.val := by
    rw [s18_post2, s20_post, s19_post, Array.val_to_slice, write4 _ _ 24 28 (by decide) (by decide)]
    rw [p5]
  have p7 : (index_mut_back7 s23).val.take 32 = a.val ++ a1.val ++ a2.val ++ a3.val ++ a4.val ++ a5.val ++ a6.val ++ a7.val := by
    rw [s21_post2, s23_post, s22_post, Array.val_to_slice, write4 _ _ 28 32 (by decide) (by decide)]
    rw [p6]
  rw [List.take_of_length_le (by scalar_tac)] at p7
  rw [p7]
  obtain ⟨sa,sc⟩ := hi
  obtain ⟨ua,uc⟩ := hu
  simp only [getElem!_pos iv.val 0 (by scalar_tac), getElem!_pos iv.val 1 (by scalar_tac), getElem!_pos v.val 0 (by scalar_tac), getElem!_pos v.val 1 (by scalar_tac)] at sa sc ua uc
  simp only [a_post, a1_post, a2_post, a3_post, a4_post, a5_post, a6_post, a7_post, mi_post,mi1_post,mi2_post,mi3_post,sa,sc,ua,uc,abef,cdgh,
    stateWords, X86.feedForward, serialize, List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rfl

#print axioms digest_spec
end slhdsa.Intel
