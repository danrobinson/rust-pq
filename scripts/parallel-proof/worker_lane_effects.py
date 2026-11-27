"""Physical publications from the four extracted FORS SIMD lane loops."""

import re
from pathlib import Path


def simd_lane_witness(generated):
    (width,) = set(
        re.findall(r"\(secret : Array \(Array Std.U8 N\) (\d+)#usize\)", generated)
    )
    specs = [
        ("1", "secret", "unique SHAKE FORS sk slot"),
        ("2_loop0", "sibling", "unique SHAKE FORS low slot"),
        ("3", "sibling", "unique SHAKE FORS direct slot"),
        ("4", "split", "unique SHAKE FORS split slot"),
    ]
    output = """
private theorem spec_imp_exists {T : Type} {m : Result T} {p : T → Prop} (h : WP.spec m p) :
    ∃ v, m = ok v ∧ p v := by cases m <;> simp_all
"""
    for suffix, mode, message in specs:
        name = "interpreted.dispatch_loop" + suffix
        param = "(stride first : Usize)" + (
            " (level : U32)" if mode == "sibling" else ""
        )
        call = "stride refs first" + (" level" if mode == "sibling" else "") + " rows"
        index = "(first.val + it.start.val) * stride.val"
        cap = "(sumFits : first.val + it.start.val ≤ Usize.max)"
        arith = """
  obtain ⟨tree, e₁, h₁⟩ := spec_imp_exists (UScalar.add_spec (x:=first) (y:=it.start) (by rwa [UScalar.max_USize_eq]))
  obtain ⟨base, e₂, h₂⟩ := spec_imp_exists (UScalar.mul_spec (x:=tree) (y:=stride)
    (by rw [h₁]; omega))
"""
        rewrites = "e₁, e₂"
        hslot = "by rw [h₂,h₁]"
        slot = "base"
        if mode == "sibling":
            index += " + 1 + level.val"
            arith += """
  obtain ⟨off, e₃, h₃⟩ := spec_imp_exists (UScalar.add_spec (x:=base) (y:=1#usize)
    (by rw [h₂,h₁]; change _+1 ≤ _; omega))
  obtain ⟨slot, e₄, h₄⟩ := spec_imp_exists (UScalar.add_spec (x:=off) (y:=UScalar.cast .Usize level)
    (by rw [h₃,h₂,h₁,U32.cast_Usize_val_eq]; change _+1+_ ≤ _; omega))
"""
            slot = "slot"
            rewrites += ", e₃, lift, e₄"
            hslot = "by rw [h₄,h₃,h₂,h₁,U32.cast_Usize_val_eq]; rfl"
        if mode == "split":
            param = "(chunk : U32) (base chunks : Usize)"
            call = "refs chunk base chunks rows"
            index = "base.val + it.start.val * chunks.val + chunk.val"
            cap = ""
            arith = """
  obtain ⟨off, e₁, h₁⟩ := spec_imp_exists (UScalar.mul_spec (x:=it.start) (y:=chunks) (by omega))
  obtain ⟨pre, e₂, h₂⟩ := spec_imp_exists (UScalar.add_spec (x:=base) (y:=off) (by rw [h₁]; omega))
  obtain ⟨slot, e₃, h₃⟩ := spec_imp_exists (UScalar.add_spec (x:=pre) (y:=UScalar.cast .Usize chunk)
    (by rw [h₂,h₁,U32.cast_Usize_val_eq]; omega))
"""
            rewrites = "e₁, e₂, lift, e₃"
            hslot = "by rw [h₃,h₂,h₁,U32.cast_Usize_val_eq]"
            slot = "slot"
        cast_simp = "" if mode == "secret" else ", lift"
        output += f"""
open ParallelWorkerInterleave in
theorem lane_{suffix}_step {{N : Usize}} {{H A : Type}}
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    {param} (rows : Array (Array U8 N) {width}#usize)
    (it : core.ops.range.Range Usize) (h : H) (k : Unit → Program H A) (l r : List (Program H A))
    (live : it.start.val < it.end.val) (lane : it.start.val < rows.length) {cap}
    (room : {index} < refs.length)
    (empty : refs.val[{index}].read h = none) :
    ∃ next : core.ops.range.Range Usize, next.start.val=it.start.val+1 ∧ next.end=it.end ∧
      Step h (l ++ ({name} concurrentOps it {call} >>= k) :: r)
        (refs.val[{index}].write rows.val[it.start.val] h)
        (l ++ ({name} concurrentOps next {call} >>= k) :: r) := by
  obtain ⟨⟨tag,next⟩, advance, tagEq, inc, stop⟩ := spec_imp_exists
    (core.iter.range.IteratorRange.next_Usize_some_spec it live)
  subst tag
  have bound := refs.property
  change refs.length ≤ Usize.max at bound
  have maximum := UScalar.max_USize_eq
{arith}
  have position : {slot}.val = {index} := {hslot}
  obtain ⟨ref, findRef, found⟩ := spec_imp_exists
    (alloc.vec.Vec.index_usize_spec refs {slot} (position ▸ room))
  obtain ⟨v, findValue, value⟩ := spec_imp_exists (Array.index_usize_spec rows it.start lane)
  subst ref v
  refine ⟨next, inc, stop, ?_⟩
  unfold {name}
  change Step h (l ++ (runLoop _ it >>= k) :: r) _ (l ++ (runLoop _ next >>= k) :: r)
  rw [runLoop_unfold _ it]
  simp only [{name}.body, advance, lifted_ok, pure_bind, {rewrites},
    alloc.vec.Vec.index_slice_index, findRef, findValue, concurrentOps, bind_assoc]
  have store := set_step (refs.val[{slot}.val]'(position ▸ room)) rows.val[it.start.val]
    (fun res => do
      let _ ← (liftM (core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) res
        (toStr "{message}")) : Program H Unit)
      runLoop (fun it' => {name}.body concurrentOps {call} it') next >>= k) h l r
  simp only [position, empty, core.result.Result.expect, lifted_ok, pure_bind, {name}.body,
    concurrentOps, alloc.vec.Vec.index_slice_index{cast_simp}] at store ⊢
  exact store
"""
        idx = index.replace("it.start.val", "i")
        sum_fit = "(sumFits : ∀ i < active.val, first.val+i ≤ Usize.max)" if cap else ""
        fit_arg = "(sumFits it.start.val live)" if cap else ""
        params = (
            "chunk base chunks"
            if mode == "split"
            else "stride first" + (" level" if mode == "sibling" else "")
        )
        step_proof = f"""    obtain ⟨free, rfl⟩ := (storeAt_eq refs rows.val (fun i => {idx}) it.start.val h dest
      (room _ live) (by change it.start.val < rows.length; omega)).mp written
    obtain ⟨next,inc,ends,step⟩ := lane_{suffix}_step refs {params} rows it h k [] peers
      (stop ▸ live) (by omega) {fit_arg} (room _ live) free
    exact ⟨next,inc,ends.trans stop,step⟩"""
        exhaustion_proof = f"""  · intro it stop past
    obtain ⟨⟨opt,tail⟩, no, optEq, tailEq⟩ := spec_imp_exists
      (core.iter.range.IteratorRange.next_Usize_none_spec it (stop ▸ past))
    subst opt tail
    change (runLoop _ it >>= k) = _
    rw [runLoop_unfold]
    simp only [{name}.body, no, lifted_ok, pure_bind]"""
        output += f"""
open ParallelWorkerInterleave ParallelWorkerScatter in
theorem lane_{suffix}_complete {{N : Usize}} {{H A : Type}}
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    {param} (rows : Array (Array U8 N) {width}#usize)
    (active : Usize) (k : Unit → Program H A)
    (width : active.val ≤ rows.length) {sum_fit}
    (room : ∀ i < active.val, {idx} < refs.length)
    (h dest : H) (peers finalPeers : List (Program H A))
    (sched : Scatter active.val (storeAt refs rows.val (fun i => {idx}))
        0 h peers dest finalPeers) :
    Steps h (({name} concurrentOps ⟨0#usize,active⟩ {call} >>= k) :: peers)
      dest (k () :: finalPeers) := by
  refine realize active _ (fun it => {name} concurrentOps it {call} >>= k)
    (k ()) ?_ ?_ sched _ rfl rfl
  · intro it h dest peers stop live written
{step_proof}
{exhaustion_proof}
"""
        own = step_proof.replace(
            "it h k [] peers", "it h (pure : Unit → Program H Unit) [] []"
        )
        end = exhaustion_proof.replace(
            "(runLoop _ it >>= k) = _",
            "(runLoop _ it >>= (pure : Unit → Program H Unit)) = _",
        )
        output += f"""
open ParallelWorkerInterleave ParallelWorkerScatter in
theorem lane_{suffix}_reflect {{N : Usize}} {{H : Type}}
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    {param} (rows : Array (Array U8 N) {width}#usize)
    (active : Usize) (width : active.val ≤ rows.length) {sum_fit}
    (room : ∀ i < active.val, {idx} < refs.length)
    (fresh : H) (init : ∀ i, (hi : i < active.val) → (refs.val[{idx}]'(room i hi)).read fresh = none)
    (h dest : H) (peers finalPeers : List (Program H Unit))
    (run : Observed (fun i s => i < active.val → ∃ out,
      storeAt refs rows.val (fun i => {idx}) i s = some out) 0 h
        ({name} concurrentOps ⟨0#usize,active⟩ {call}) peers dest finalPeers) :
    Scatter active.val (storeAt refs rows.val (fun i => {idx})) 0 h peers dest finalPeers := by
  refine reflect active _ (fun it => {name} concurrentOps it {call} >>= (pure : Unit → Program H Unit))
    ?_ ?_ ?_ run ⟨0#usize,active⟩ rfl rfl (by simp)
  · intro i hi
    exact ⟨fresh,_, (storeAt_eq refs rows.val (fun i => {idx}) i fresh _ (room i hi)
      (by change i < rows.length; omega)).mpr ⟨init i hi,rfl⟩⟩
  · intro it h dest stop live written
{own}
{end}
"""
        site = "split" if mode == "split" else "direct"
        positive = "chunks" if mode == "split" else "stride"
        compare = (
            "Nat.mul_lt_mul_of_pos_right less positive"
            if mode == "split"
            else "Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left less first.val) positive"
        )
        heap_args = call.replace("refs", f"(ForsTable.{site}.cells N count)")
        output += f"""
open ParallelWorkerInterleave ParallelWorkerScatter ParallelWorkerRuntime in
theorem lane_{suffix}_fresh {{N : Usize}} {{A : Type}} (count : Usize)
    {param} (rows : Array (Array U8 N) {width}#usize)
    (active : Usize) (k : Unit → Program (Shared N) A)
    (width : active.val ≤ rows.length) {sum_fit} (positive : 0 < {positive}.val)
    (room : ∀ i < active.val, {idx} < count.val)
    (peers : List (Program (Shared N) A)) :
    ∃ dest, Steps (fresh N)
      (({name} concurrentOps ⟨0#usize,active⟩ {heap_args} >>= k) :: peers) dest (k () :: peers) := by
  obtain ⟨dest,sched⟩ := serial_fors .{site} N count rows.val (fun i => {idx}) active.val width
    room (by intro i j less _; have := {compare}; omega) peers
  exact ⟨dest, lane_{suffix}_complete _ {params} rows active k width {"sumFits" if cap else ""}
    (fun i hi => ForsTable.length .{site} N count ▸ room i hi) _ _ _ _ sched⟩
"""
    return output + Path(__file__).with_name(
        "worker-simd-entry.lean"
    ).read_text().replace("WIDTH", width)
