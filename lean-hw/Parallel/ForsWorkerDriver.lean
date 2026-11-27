import Parallel.ForsPublicationTable
import Parallel.RawChunkTable
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors

noncomputable def modeFor : ParallelRootWalk.Host → Mode
  | .apple sha3 => .apple sha3
  | .linuxArm => .linux
  | .x86 => if available : GatherRust.avx512Available=true then .x86 available else .fallback .x86

theorem host_mode (host : ParallelRootWalk.Host) : (modeFor host).rootHost=host := by
  cases host with
  | apple _ | linuxArm => rfl
  | x86 => cases e : GatherRust.avx512Available <;> simp [modeFor,e,Mode.rootHost]

noncomputable def probe : ParallelRootWalk.Host → Usize → Result Bool
  | .apple sha3 => (WidthEight.Platform.apple sha3).probe
  | .linuxArm => ShakeBatch.shake.batch.available KldispRust.shake256.parallel.available
  | .x86 => WidthEight.Platform.x86.probe

theorem mode_for_host {N : Usize} (host : ParallelRootWalk.Host) (p : params.Params) (hp : PN p N) :
    probe host N=ok (decide ((modeFor host).policy ≠ .scalar)) := by
  cases host with
  | apple sha3 =>
    change ShakeBatch.shake.batch.available _ N=ok true
    rw [ShakeBatch.available_for_fips _ p hp]
  | linuxArm =>
    change ShakeBatch.shake.batch.available _ N=ok true
    rw [ShakeBatch.available_for_fips _ p hp];rfl
  | x86 =>
    change ShakeBatch.X86.available N=_
    rw [ShakeBatch.X86.available_spec p hp]
    cases eq : GatherRust.avx512Available <;> simp [modeFor,eq,Mode.policy]

noncomputable def selectMode (host : ParallelRootWalk.Host) (on : Bool) : Mode :=
  if on then modeFor host else .fallback (modeFor host).host

theorem selected (host : ParallelRootWalk.Host) :
    selectMode host (decide ((modeFor host).policy≠Policy.scalar))=modeFor host := by
  cases host with
  | apple _ | linuxArm => rfl
  | x86 => cases e : GatherRust.avx512Available <;> simp [selectMode,modeFor,e,Mode.host,Mode.policy]

abbrev ActionSource := {N : Usize} → Mode → Data N → Action N

def SourceCorrect (source : ActionSource) := ∀ {N} (mode : Mode) (d : Data N), Valid d → Issued mode d (source mode d)

noncomputable def run {N : Usize} (source : ActionSource) (host : ParallelRootWalk.Host) (p : params.Params)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) (schedule : ∀ n, WidthEight.Ticket.Schedule n) := do
  let choices ← util.base_2b md p.a (UScalar.cast .Usize p.k)
  let stride ← UScalar.cast .Usize p.a + 1#usize
  let useSimd ← probe host N
  let mode := selectMode host useSimd
  let data : Data N := ⟨p,sk,seed,a,choices,stride⟩
  let cells ← publish p (source mode data) schedule
  pack host p md sk seed a cells

theorem run_spec {N : Usize} (source : ActionSource) (works : SourceCorrect source) (host : ParallelRootWalk.Host)
    (p : params.Params) (hp : PN p N) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (schedule : ∀ n, WidthEight.Ticket.Schedule n) (mdLen : md.length=(Shake.params p).mdBytes)
    (domain : ForsHorizontal.Domain a) :
    run source host p md sk seed a schedule ⦃ out => bytes out.val=
      (ParallelCached.forsRows (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a)).flatten ⦄ := by
  have maxA : p.a.val≤14 := hp.valid.a_le
  have posA : 1≤p.a.val := hp.valid.a_pos
  have bits : p.k.val*p.a.val≤8*md.length := by change md.length=(p.k.val*p.a.val+7)/8 at mdLen;omega
  unfold run
  step with base_2b_spec md p.a (UScalar.cast .Usize p.k) (by omega) (by simpa using bits) as ⟨choices,digits,count,bounds⟩
  simp only [U32.cast_Usize_val_eq] at digits count
  step as ⟨stride,size⟩
  simp only [mode_for_host host p hp,bind_tc_eq,bind_ok,selected]
  let mode := modeFor host
  let d : Data N := ⟨p,sk,seed,a,choices,stride⟩
  have good : Valid d := ⟨hp,domain,count,by
    intro i hi
    rw [getElem!_pos choices.val i hi]
    exact bounds _ (List.getElem_mem _),by simpa using size⟩
  rw [ParallelCached.fors_bytes]
  simpa only [mode,d,host_mode] using packed mode d good md digits _ (works mode d good) schedule

end slhdsa.RawFors
