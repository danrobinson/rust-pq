import Cachepath.NativeVerify.ForsSignNarrow
import Shakebatch.WidthThreeHost
import Shakebatch.LinuxFors
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
section
variable [machine : Machine]
def dispatched (short : Short) (nodes : Nodes) (available : Usize → Result Bool)
  {N : Std.Usize} (p : params.Params) (md : Slice Std.U8)
  (sk_seed : Array Std.U8 N) (seed : Array Std.U8 N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let i ← lift (UScalar.cast .Usize p.k)
  let indices ← util.base_2b md p.a i
  let b ← available N
  if b
  then
    let s := alloc.vec.Vec.deref indices
    narrow short nodes p s sk_seed seed adrs
  else
    shake.fors.fors_sign_loop0 p.k sk_seed seed adrs p.a indices
      (alloc.vec.Vec.new Std.U8) 0#u32


end
local instance : Machine := Kldisp.machine

/-- Linux Arm runs the live narrow FORS schedule. Its two primitive providers
    are exposed so that the executable nodes and active short hash can refine them. -/
def linux (short : @Short Kldisp.machine) (nodes : @Nodes Kldisp.machine)
    (hs : @ShortLaw Kldisp.machine short) (hn : @NodesLaw Kldisp.machine nodes) : WidthThree.ForsSigner where
  run := dispatched short nodes Linux.available
  correct := by
    intro N p hp md sk seed a hmd domain
    have ha : p.a.val ≤ 14 := hp.valid.a_le
    have pos : 1 ≤ p.a.val := hp.valid.a_pos
    unfold dispatched
    step as ⟨k,hk⟩
    have kval : k.val=p.k.val := by simp [hk]
    let* ⟨digits,ind,len,valid⟩ ← base_2b_spec md p.a k (by omega) (by rw [kval,hmd];omega)
    rw [kval] at ind len
    have view : digits.deref=digits.slice := by apply Slice.ext; simp [alloc.vec.Vec.deref,Slice.from_val];rfl
    simp only [available_for_fips _ p hp,show KldispRust.shake256.parallel.available = ok true from rfl,bind_ok,ite_true,view]
    let* ⟨out,bytesEq,size⟩ ← narrow_spec short nodes hs hn p hp sk seed a domain digits.slice (by decide) (by decide)
      len (fun t ht => valid _ (by change digits.val[t]! ∈ digits.val; rw [getElem!_pos digits.val t ht]; exact List.getElem_mem _))
    refine ⟨?_,size⟩
    rw [forsSign_eq,bytesEq]
    change (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (nats digits.val)) =
      (List.range p.k.val).flatMap (forsSignTree _ _ _ _ (Spec.base2b _ p.a.val p.k.val))
    rw [ind]


/-- Full-width primitive representatives of the live-lane observation. Inactive
    results can differ because the narrow signer neither writes nor reads them. -/
def observedShort : @Short Kldisp.machine :=
  fun seed addresses values _ => @ShakeBatch.shake.batch.short Kldisp.machine _ seed addresses values

def observedNodes : @Nodes Kldisp.machine :=
  fun sk seed a ids z _ => @ShakeBatch.shake.fors_batch.nodes Kldisp.machine _ sk seed a ids z

theorem observedShort_correct : ShortLaw observedShort := by
  intro N p hp seed addrs values active bound
  apply WP.spec_mono (@short_fips Kldisp.machine N seed addrs values Kldisp.permutation_correct hp.le32 (aligned_hash hp))
  intro out values j hj
  exact values _ (hj.trans_le bound)

theorem observedNodes_correct : NodesLaw observedNodes := by
  intro N p hp sk seed a ids z active _ bound fits
  apply WP.spec_mono (@fors_nodes Kldisp.machine N p hp sk seed a Kldisp.permutation_correct ids z fits)
  intro out values j hj
  exact values _ (hj.trans_le bound)

def linuxProjected : WidthThree.ForsSigner :=
  linux observedShort observedNodes observedShort_correct observedNodes_correct

end slhdsa.NativeVerify.ForsSign
