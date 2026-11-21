import Integration.SlhDsaBridgePrf
import Ideal.Transport.AdvPrf
import Ideal.Transport.AdvMsg

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
namespace Reduction
example {c : Caps} (ω : Ω128 c) (g : Bytes Link.vp.params.n → Bytes Link.vp.params.n → Bytes 22 → Bytes Link.vp.params.n) :
  primsΩ (ω.withPrf g) = Ideal.Transport.setPrf (primsΩ ω) (fun pk sk a => g pk sk (Concrete.sha2AdrsKey a)) (primsΩ ω).PRFmsg := rfl
#check @Guarded.signingImpl
#print pureEncode
#print SigLog
#print WinCheck
#print sufCheck
end Reduction
