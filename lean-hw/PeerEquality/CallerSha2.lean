import PeerEquality.Callers
import RcSlhSha2.Peer

namespace slhdsa.PeerCall
open Spec

/-- Use the actual pinned peer H_msg and PRF_msg method projections. The
unrelated tweakable inputs are discarded by projection. -/
def sha2Messages (s : RcSlhSha2.StandardSet) (a : RcSlhSha2.Algorithms) (other : Children) : Children :=
  {other with
    prfMsg := fun k r m => (RcSlhSha2.suite s [] Adrs.zero.bytes [] [] [] [] [] [] k r m a).prfmsg
    hMsg := fun r seed root m =>
      (RcSlhSha2.suite s seed Adrs.zero.bytes [] [] [] [] r root
        (List.replicate (RcSlhSha2.params s).n 0#8) [] m a).hmsg}

theorem sha2_prf (s : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing)
    (a : RcSlhSha2.Algorithms) (seen : RcSlhSha2.Observed route a) (other : Children)
    (k r : Bytes) (m : Parts) (h : k.length = (RcSlhSha2.params s).n) :
    (sha2Messages s a other).prfMsg k r m = PRFmsg (RcSlhSha2.params s) k r m.flatten.flatten := by
  rw [(RcSlhSha2.observed_iff _ _).mp seen]
  exact congrArg RcSlhSha2.Hashes.prfmsg (RcSlhSha2.suite_is_fips s [] Adrs.zero [] [] [] [] [] [] k r m h)

theorem sha2_hmsg (s : RcSlhSha2.StandardSet) (route : RcSlhSha2.Routing)
    (a : RcSlhSha2.Algorithms) (seen : RcSlhSha2.Observed route a) (other : Children) :
    (sha2Messages s a other).hMsg = (specChildren (RcSlhSha2.params s)).hMsg := by
  rw [(RcSlhSha2.observed_iff _ _).mp seen]
  funext r seed root m
  exact congrArg RcSlhSha2.Hashes.hmsg (RcSlhSha2.suite_is_fips s seed Adrs.zero [] [] [] [] r root
    (List.replicate (RcSlhSha2.params s).n 0#8) [] m (by simp))

end slhdsa.PeerCall
