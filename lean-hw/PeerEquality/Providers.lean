import PeerEquality.CallerSha2
import PeerEquality.Wots
import Peerarmkeccak.Provider
import PeerEquality.ForsProvider

namespace slhdsa.PeerCall.Providers
open Spec

private def hashRows (s : RcSlhSha2.StandardSet) (algs : RcSlhSha2.Algorithms)
    (pk : Bytes) (a : Adrs) (sk l r : Bytes) (rows : List Bytes) :=
  RcSlhSha2.suite s pk a.bytes sk l r rows [] [] (List.replicate (RcSlhSha2.params s).n 0#8) [] [] algs

def sha2Rows (s : RcSlhSha2.StandardSet) (a : RcSlhSha2.Algorithms) : PeerWots.Hashes :=
  ⟨fun pk sk addr => (hashRows s a pk addr sk [] [] []).prf,
   fun pk addr m => (hashRows s a pk addr [] m [] []).f,
   fun pk addr rows => (hashRows s a pk addr [] [] [] rows).t,
   fun pk addr l r => (hashRows s a pk addr [] l r []).h⟩

theorem sha2Rows_fips (s : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing)
    (a : RcSlhSha2.Algorithms) (seen : RcSlhSha2.Observed route a) :
    sha2Rows s a = PeerWots.hashes (RcSlhSha2.params s) := by
  rw [(RcSlhSha2.observed_iff _ _).mp seen]
  have eq (pk : Bytes) (ad : Adrs) (sk l r : Bytes) (rows : List Bytes) :=
    RcSlhSha2.suite_is_fips s pk ad sk l r rows [] [] (List.replicate (RcSlhSha2.params s).n 0#8) [] [] (by simp)
  unfold sha2Rows PeerWots.hashes
  congr 1
  · funext pk sk ad; exact congrArg RcSlhSha2.Hashes.prf (eq pk ad sk [] [] [])
  · funext pk ad m; exact congrArg RcSlhSha2.Hashes.f (eq pk ad [] m [] [])
  · funext pk ad rows; exact congrArg RcSlhSha2.Hashes.t (eq pk ad [] [] [] rows)
  · funext pk ad l r; exact congrArg RcSlhSha2.Hashes.h (eq pk ad [] l r [])

private def shakeRowsWith (p : Params) (x : PeerShake.Xof PeerShake.Buffer.Buffered) : PeerWots.Hashes :=
  ⟨fun pk sk a => PeerShake.prf_sk x p.n (PeerShake.new_from_pk_seed x pk) a.bytes sk,
   fun pk a m => PeerShake.f x p.n (PeerShake.new_from_pk_seed x pk) a.bytes m,
   fun pk a rows => PeerShake.t x p.n (PeerShake.new_from_pk_seed x pk) a.bytes rows,
   fun pk a l r => PeerShake.h x p.n (PeerShake.new_from_pk_seed x pk) a.bytes l r⟩

abbrev shakeRows (p : Params) := shakeRowsWith p PeerShake.Buffer.provider

theorem shakeRows_fips (p : Params) (family : p.family=.shake) : shakeRows p = PeerWots.hashes p := by
  dsimp only [shakeRows,shakeRowsWith,PeerWots.hashes]
  congr 1
  · funext pk sk a; exact PeerShake.prf_fips PeerShake.Buffer.providerCorrect p family pk sk a
  · funext pk a m; exact PeerShake.f_fips PeerShake.Buffer.providerCorrect p family pk m a
  · funext pk a rows; exact PeerShake.t_fips PeerShake.Buffer.providerCorrect p family pk rows a
  · funext pk a l r; exact PeerShake.h_fips PeerShake.Buffer.providerCorrect p family pk l r a

private def children (p : Params) (w : PeerWots.Hashes) (prf : Bytes → Bytes → Parts → Bytes)
    (h : Bytes → Bytes → Bytes → Parts → Bytes) : Children :=
  ⟨PeerWots.operations w p,prf,h,ConcreteFors.sign w p,ConcreteFors.recover w p⟩

def shake (p : Params) : Children :=
  children p (shakeRows p) (PeerShake.prf_msg PeerShake.Buffer.provider p.n)
    (PeerShake.h_msg PeerShake.Buffer.provider p.m)

/-- The same concrete backend is used by message hashing, chain hashing, and both tree recursions. -/
noncomputable def nativeShake (impl : PeerShake.Backend.Implementation) (p : Params) : Children :=
  let x := PeerShake.Backend.xof (PeerShake.Backend.kernel impl)
  children p (shakeRowsWith p x) (PeerShake.prf_msg x p.n) (PeerShake.h_msg x p.m)

theorem nativeShake_eq (impl : PeerShake.Backend.Implementation) (p : Params) :
    nativeShake impl p = shake p := by
  simp only [nativeShake, PeerShake.Backend.provider_eq, shake, shakeRows]

def sha2 (s : RcSlhSha2.StandardSet) (a : RcSlhSha2.Algorithms) : Children :=
  let p := RcSlhSha2.params s
  sha2Messages s a (children p (sha2Rows s a) (fun _ _ _ => []) (fun _ _ _ _ => []))

private theorem certify (p : Params) (v : p.Valid) (c : Children)
    (w : c.wots = PeerXmss.children p)
    (random : ∀ key rand msg, key.length=p.n → c.prfMsg key rand msg = PRFmsg p key rand msg.flatten.flatten)
    (h : c.hMsg=(specChildren p).hMsg)
    (fs : c.forsSign = forsSign p) (fr : c.forsRecover = forsPkFromSig p) : ChildLaws c p := by
  refine ⟨congrArg PeerXmss.Children.wotsKey w,congrArg PeerXmss.Children.wotsSign w,
    congrArg PeerXmss.Children.wotsRecover w,congrArg PeerXmss.Children.hash w,random,h,v,fs,fr⟩

theorem shake_laws (p : Params) (v : p.Valid) (family : p.family=.shake) : ChildLaws (shake p) p := by
  have fors := ConcreteFors.operations p _ (shakeRows_fips p family)
  apply certify p v _ _ _ _ fors.1 fors.2
  · change PeerWots.operations (shakeRows p) p = _
    rw [shakeRows_fips p family,PeerWots.operations_fips p v]
  · intro k r m _; exact PeerShake.prf_msg_fips PeerShake.Buffer.providerCorrect _ family _ _ _
  · funext r seed root m; exact PeerShake.h_msg_fips PeerShake.Buffer.providerCorrect _ family _ _ _ _

theorem sha2_laws (s : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing)
    (a : RcSlhSha2.Algorithms) (seen : RcSlhSha2.Observed route a) : ChildLaws (sha2 s a) (RcSlhSha2.params s) := by
  have v : (RcSlhSha2.params s).Valid := by cases s <;> constructor <;> decide
  have fors := ConcreteFors.operations _ _ (sha2Rows_fips s route a seen)
  apply certify _ v _ _ _ _ fors.1 fors.2
  · change PeerWots.operations (sha2Rows s a) (RcSlhSha2.params s) = _
    rw [sha2Rows_fips s route a seen,PeerWots.operations_fips _ v]
  · exact sha2_prf s route a seen _
  · exact sha2_hmsg s route a seen _

end slhdsa.PeerCall.Providers
