import Parallel.ForsPacket
import Parallel.ForsSplitCells
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

noncomputable def splitAction {N} (mode : Mode) (d : Data N) (t j : Nat) : Result (Cell N) :=
  let sub := target mode.policy d.p.a.val
  if mode.policy=.three then
    let first := groupFirst 3 t
    let active := min (d.choices.length-first) 3
    Std.bind (buildGroupMerge d (word .U16 first) (word .U8 active) (word .U8 j) (word .U8 sub) (word .U32 j) (word .U32 sub))
      (fun m => m.action d (t%3))
  else
    let sat := decide (mode.policy=.eight)
    Std.bind (buildScalarMerge mode.host d sat (word .U32 t) (word .U32 j) (word .U32 sub))
      (fun m => m.action mode.host d sat)

theorem split_receipt {N} (mode : Mode) (d : Data N) (valid : Valid d) (t j : Nat)
    (tree : t<d.p.k.val) (height : j<d.p.a.val) (split : target mode.policy d.p.a.val<j) :
    Receipt mode d (.reduced t j) (splitAction mode d t j) := by
  let sub := target mode.policy d.p.a.val
  have low : sub<j := split
  have count : d.p.k.val≤35 := valid.pn.valid.k_le
  have maxH : d.p.a.val≤14 := valid.pn.valid.a_le
  have ju : (word .U32 j).val=j := word_eq _ (by change j<4294967296;omega)
  have su : (word .U32 sub).val=sub := word_eq _ (by change sub<4294967296;omega)
  unfold splitAction
  split
  · rename_i linux
    let first := groupFirst 3 t
    let active := min (d.choices.length-first) 3
    have sum : first+t%3=t := group_lane 3 t
    have bound : active≤3 := Nat.min_le_right ..
    have lane : t%3<active := Nat.lt_min.mpr ⟨by rw [valid.count];omega,Nat.mod_lt _ (by decide)⟩
    have room : first+active≤d.choices.length := by have part : active≤d.choices.length-first := Nat.min_le_left ..;omega
    have f : (word .U16 first).val=first := word_eq _ (by change first<65536;omega)
    have av : (word .U8 active).val=active := word_eq _ (by change active<256;omega)
    have h8 : (word .U8 j).val=j := word_eq _ (by change j<256;omega)
    have s8 : (word .U8 sub).val=sub := word_eq _ (by change sub<256;omega)
    obtain ⟨m,run,ready,firstEq,activeEq,jEq,sEq⟩ := spec_imp_exists
      (buildGroupMerge_spec d valid (word .U16 first) (word .U8 active) (word .U8 j) (word .U8 sub) (word .U32 j) (word .U32 sub)
        (by simpa only [h8] using height) (by simpa only [s8,h8] using low) (ju.trans h8.symm) (su.trans s8.symm)
        (by rw [av];omega) (by simpa only [av] using bound) (by simpa only [f,av] using room))
    dsimp only
    rw [run,bind_ok]
    simpa only [firstEq,f,sum,jEq,ju] using Receipt.groupedMerge (mode:=mode) (d:=d) m (t%3) linux
      (by rwa [activeEq,av]) (by rw [sEq,su]) (by rw [activeEq,av,firstEq,f]) ready
  · rename_i plain
    have tu : (word .U32 t).val=t := word_eq _ (by change t<4294967296;omega)
    obtain ⟨m,run,ready,tEq,jEq,sEq⟩ := spec_imp_exists
      (buildScalarMerge_spec mode.host d valid (decide (mode.policy=.eight)) (word .U32 t) (word .U32 j) (word .U32 sub)
        (by simpa only [tu] using tree) (by simpa only [ju] using height) (by simpa only [su,ju] using low))
    dsimp only
    rw [run,bind_ok]
    simpa only [tEq,tu,jEq,ju] using Receipt.scalarMerge (mode:=mode) (d:=d) m plain (by rw [sEq,su]) ready

noncomputable def nativeAction {N} (mode : Mode) (d : Data N) := selectAction mode d (splitAction mode d)

theorem native_receipt {N} (mode : Mode) (d : Data N) (valid : Valid d) (t : Nat) (tree : t<d.p.k.val)
    (c : Nat) (col : c≤d.p.a.val) : Receipt mode d (owner mode.policy d.p.a.val t c) (nativeAction mode d t c) :=
  select_receipt mode d valid ⟨splitAction mode d,split_receipt mode d valid⟩ t c tree col

noncomputable def nativePacket {N} (mode : Mode) (d : Data N) (valid : Valid d) : Packet mode d :=
  ⟨nativeAction mode d,native_receipt mode d valid⟩

end slhdsa.RawFors
