import Wotsx86.Funs
import Wots.Recovery
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots.Checked
open WotsX86Rust
open Spec.SHA256

def supported (N L : Usize) :=
  (N.val=16 ∧ L.val=640) ∨ (N.val=24 ∧ L.val=1280) ∨ (N.val=32 ∧ L.val=2304)

theorem endpoints_fips {N L} (P : Spec.Params) [Fact (P.family=.sha2)] (state : Array U32 8#usize)
    (sk : Array U8 N) (a : WotsX86Rust.address.Adrs) (first : U32) (out : Rows L) (pk : Spec.Bytes)
    (cpu : GatherRust.avx512Available=true) (shape : supported N L) (batch : out.length ≤ 16)
    (width : N.val=P.n) (hpk : pk.length=P.n) (seed : state.val.map (·.bv)=seedState P.n pk)
    (keys : first.val+out.length ≤ 2^32) :
    sha256.x86.wots_endpoints state sk a first out ⦃ final =>
      let len := 2*N.val+3
      processed N.val len (fun t => endpoint P (adrsS (WotsRust.addressOf (asKernel a))) pk (bytes sk.val)
        (first.val+t/len) (t%len)) out final (len*out.length) ⦄ := by
  have cap : out.len ≤ 16#usize := batch
  have numeric : (2*N.val+3)*out.length ≤ Usize.max := by
    have small : 2*N.val+3 ≤ 67 := by rcases shape with h|h|h <;> omega
    have limit := Nat.mul_le_mul small batch
    scalar_tac
  have room : 22+(2*N.val+3)*N.val ≤ L.val := by
    rcases shape with ⟨n,l⟩|⟨n,l⟩|⟨n,l⟩ <;> rw [n,l] <;> decide
  have widths : P.n=16 ∨ P.n=24 ∨ P.n=32 := by rcases shape with h|h|h <;> omega
  have kernel := Wots.endpoints_fips P state sk (asKernel a) first out pk width widths hpk seed numeric keys room
  unfold sha256.x86.wots_endpoints sha256.x86.avx512_available sha256.x86.has_avx512.get
  rcases shape with ⟨n,l⟩|⟨n,l⟩|⟨n,l⟩ <;>
    simpa only [GatherRust.sha256.x86.avx512_available,cpu,bind_tc_eq,bind_ok,n,l,massert,cap,ite_true,
      sha256.x86.avx512.wots_endpoints] using kernel

theorem recover_fips (P : Spec.Params) [Fact (P.family=.sha2)] (N : Usize)
    (pk : Spec.Bytes) (state : Array U32 8#usize) (a : WotsX86Rust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Buffers)
    (cpu : GatherRust.avx512Available=true) (width : N.val=P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32)
    (hpk : pk.length=P.n) (seed : state.val.map (·.bv)=seedState P.n pk)
    (count : digits.length = 2*N.val+3) (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (room : digits.length ≤ out.length) (available : N.val*digits.length ≤ sig.length) :
    sha256.x86.recover N state a sig digits out ⦃ final => endpointsInRows N digits
      (fun i => chainAt P N pk (adrsS (WotsRust.addressOf (asKernel a))) sig digits i 15) out final ⦄ := by
  have widths : N.val=16 ∨ N.val=24 ∨ N.val=32 := width ▸ shape
  have kernel := Wots.recover_fips P N pk state (asKernel a) sig digits out width shape hpk seed (by omega) valid room available
  let tail : Result Buffers := do
    let twice ← 2#usize * N
    let n ← twice + 3#usize
    massert (digits.len=n)
    let needed ← digits.len * N
    massert (sig.len ≥ needed)
    massert (out.len ≥ digits.len)
    sha256.x86.avx512.recover N state a sig digits out
  have eq : sha256.x86.recover N state a sig digits out = tail := by
    unfold sha256.x86.recover
    rcases widths with n|n|n <;> simp only [sha256.x86.avx512_available,sha256.x86.has_avx512.get,
      GatherRust.sha256.x86.avx512_available,cpu,bind_ok,n,massert,ite_true] <;> rfl
  rw [eq]
  unfold tail
  step as ⟨twice,ht⟩
  all_goals try scalar_tac
  step as ⟨n,hn⟩
  all_goals try scalar_tac
  have same : digits.len=n := UScalar.eq_of_val_eq (by change digits.length=_; scalar_tac)
  simp only [massert,same,ite_true,bind_ok]
  step as ⟨needed,hneeded⟩
  all_goals try (have max := sig.property; change sig.length ≤ Usize.max at max; rw [Nat.mul_comm] at available; scalar_tac +nonLin)
  have sigOK : needed ≤ sig.len := by change needed.val ≤ sig.length; rw [hneeded,← same]; exact Nat.mul_comm _ _ ▸ available
  have outOK : n ≤ out.len := by rw [← same]; exact room
  simpa only [sigOK,outOK,ite_true,bind_tc_eq,bind_ok,sha256.x86.avx512.recover] using kernel

theorem no_cpu {N L} (state : Array U32 8#usize) (sk : Array U8 N) (a : WotsX86Rust.address.Adrs)
    (first : U32) (out : Rows L) (sig : Slice U8) (digits : Slice U32) (buf : Buffers)
    (cpu : GatherRust.avx512Available=false) :
    sha256.x86.wots_endpoints state sk a first out = fail .assertionFailure ∧
    sha256.x86.recover N state a sig digits buf = fail .assertionFailure := by
  simp [sha256.x86.wots_endpoints,sha256.x86.recover,sha256.x86.avx512_available,
    sha256.x86.has_avx512.get,GatherRust.sha256.x86.avx512_available,cpu,massert,bind_tc_eq]

end slhdsa.X86.Wots.Checked
