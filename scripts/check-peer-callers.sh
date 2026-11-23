#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
python3 scripts/extract-peer-callers.py "$scratch/CallGraph.lean"
cmp "$scratch/CallGraph.lean" lean-hw/PeerEquality/CallGraph.lean
cd lean-hw
lake build PeerEquality.Wire PeerEquality.Library PeerEquality.Multipart PeerEquality.Wots PeerEquality.Xmss PeerEquality.ExecutionPrefixes PeerEquality.CallerFacade PeerEquality.CallerComplete PeerEquality.CallerSha2 PeerEquality.Slots
lake env lean --stdin >"$scratch/axioms" <<'LEAN'
import PeerEquality.Wire
import PeerEquality.Library
import PeerEquality.Multipart
import PeerEquality.Wots
import PeerEquality.Xmss
import PeerEquality.ExecutionPrefixes
import PeerEquality.CallerFacade
import PeerEquality.CallerComplete
import PeerEquality.Slots
import PeerEquality.CallerSha2
#print axioms slhdsa.PeerCall.sha2_128s_wire
#print axioms slhdsa.PeerCall.sha2_128f_wire
#print axioms slhdsa.PeerCall.sha2_192s_wire
#print axioms slhdsa.PeerCall.sha2_192f_wire
#print axioms slhdsa.PeerCall.sha2_256s_wire
#print axioms slhdsa.PeerCall.sha2_256f_wire
#print axioms slhdsa.PeerCall.shake_128s_wire
#print axioms slhdsa.PeerCall.shake_128f_wire
#print axioms slhdsa.PeerCall.shake_192s_wire
#print axioms slhdsa.PeerCall.shake_192f_wire
#print axioms slhdsa.PeerCall.shake_256s_wire
#print axioms slhdsa.PeerCall.shake_256f_wire
#print axioms slhdsa.PeerCall.sha2_128s_peer
#print axioms slhdsa.PeerCall.sha2_128f_peer
#print axioms slhdsa.PeerCall.sha2_192s_peer
#print axioms slhdsa.PeerCall.sha2_192f_peer
#print axioms slhdsa.PeerCall.sha2_256s_peer
#print axioms slhdsa.PeerCall.sha2_256f_peer
#print axioms slhdsa.PeerCall.shake_128s_peer
#print axioms slhdsa.PeerCall.shake_128f_peer
#print axioms slhdsa.PeerCall.shake_192s_peer
#print axioms slhdsa.PeerCall.shake_192f_peer
#print axioms slhdsa.PeerCall.shake_256s_peer
#print axioms slhdsa.PeerCall.shake_256f_peer
#print axioms slhdsa.PeerCall.Providers.sha2Rows_fips
#print axioms slhdsa.PeerCall.Providers.shakeRows_fips
#print axioms slhdsa.PeerCall.htVerifyWith_fips
#print axioms slhdsa.PeerCall.split_correct
#print axioms slhdsa.PeerCall.sha2_128s_facades
#print axioms slhdsa.PeerCall.sha2_128f_facades
#print axioms slhdsa.PeerCall.sha2_192s_facades
#print axioms slhdsa.PeerCall.sha2_192f_facades
#print axioms slhdsa.PeerCall.sha2_256s_facades
#print axioms slhdsa.PeerCall.sha2_256f_facades
#print axioms slhdsa.PeerCall.shake_128s_facades
#print axioms slhdsa.PeerCall.shake_128f_facades
#print axioms slhdsa.PeerCall.shake_192s_facades
#print axioms slhdsa.PeerCall.shake_192f_facades
#print axioms slhdsa.PeerCall.shake_256s_facades
#print axioms slhdsa.PeerCall.shake_256f_facades
#print axioms slhdsa.PeerCall.all_slots
#print axioms slhdsa.PeerCall.round_trip
#print axioms slhdsa.PeerCall.multipart_sign_peer
#print axioms slhdsa.PeerCall.multipart_verify_peer
#print axioms slhdsa.PeerCall.PeerWots.operations_fips
#print axioms slhdsa.PeerCall.PeerWots.digits_eq
#print axioms slhdsa.PeerCall.PeerXmss.operations_fips
#print axioms slhdsa.PeerCall.ht_fips
#print axioms slhdsa.PeerCall.keygen_fips
#print axioms slhdsa.PeerCall.sign_fips
#print axioms slhdsa.PeerCall.verify_fips
#print axioms slhdsa.PeerCall.sign_entry_accepted
#print axioms slhdsa.PeerCall.verify_context
#print axioms slhdsa.PeerCall.sha2_prf
#print axioms slhdsa.PeerCall.sha2_hmsg
#print axioms slhdsa.PeerCall.sha2_sign_layer
#print axioms slhdsa.PeerCall.shake_sign_layer
#print axioms slhdsa.PeerCall.sha2_verify_layer
#print axioms slhdsa.PeerCall.shake_verify_layer
#print axioms slhdsa.PeerCall.verifyPrefix_fips
#print axioms slhdsa.PeerCall.sha2_sign_prefix
#print axioms slhdsa.PeerCall.sha2_verify_prefix
#print axioms slhdsa.PeerCall.shake_sign_prefix
#print axioms slhdsa.PeerCall.shake_verify_prefix
#print axioms slhdsa.PeerCall.later_cut
#print axioms slhdsa.PeerCall.signPrefix_peer_state
#print axioms slhdsa.PeerCall.liveSignPrefix_before
#print axioms slhdsa.PeerCall.liveSignPrefix_complete
#print axioms slhdsa.PeerCall.signPrefix_complete
#print axioms slhdsa.PeerCall.Providers.nativeShake_eq
LEAN
python3 - "$scratch/axioms" <<'PY'
import sys
from pathlib import Path
import re
lines=Path(sys.argv[1]).read_text().splitlines()
if len(lines)!=70: raise SystemExit("missing proof audit")
for line in lines:
    if not re.fullmatch(r"'slhdsa\.PeerCall\.(?:(?:PeerXmss|PeerWots|Providers)\.)?\w+' (?:does not depend on any axioms|depends on axioms: \[(?:propext|Classical\.choice|Quot\.sound)(?:, (?:propext|Classical\.choice|Quot\.sound))*\])",line):
        raise SystemExit(line)
    print(line)
PY
