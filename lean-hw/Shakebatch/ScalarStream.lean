import Shakebatch.RecoverStream
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
noncomputable section

def scalarStream : Stream where
  State := slhdsa.shake256.Sponge
  start := @slhdsa.shake.hash.start
  absorb := slhdsa.shake256.Sponge.absorb
  digest := slhdsa.shake.hash.digest

def scalarStreamCorrect : @StreamCorrect scalarStream where
  Absorbed := slhdsa.Shake.Absorbed
  start := @slhdsa.Shake.start_spec
  append := slhdsa.Shake.append_spec
  digest := slhdsa.Shake.digest_spec

end
end slhdsa.ShakeBatch
