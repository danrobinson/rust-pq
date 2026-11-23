#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
python3 scripts/extract-peer-callers.py "$scratch/CallGraph.lean"
cmp "$scratch/CallGraph.lean" lean-hw/PeerEquality/CallGraph.lean
cd lean-hw
lake build PeerEquality.CallerApi PeerEquality.CallerSha2
lake env lean --stdin >"$scratch/axioms" <<'LEAN'
import PeerEquality.CallerApi
import PeerEquality.CallerSha2
#print axioms slhdsa.PeerCall.ht_fips
#print axioms slhdsa.PeerCall.keygen_fips
#print axioms slhdsa.PeerCall.sign_fips
#print axioms slhdsa.PeerCall.verify_fips
#print axioms slhdsa.PeerCall.sign_entry_accepted
#print axioms slhdsa.PeerCall.verify_context
#print axioms slhdsa.PeerCall.sha2_prf
#print axioms slhdsa.PeerCall.sha2_hmsg
LEAN
python3 - "$scratch/axioms" <<'PY'
import sys
from pathlib import Path
import re
lines=Path(sys.argv[1]).read_text().splitlines()
if len(lines)!=8: raise SystemExit("missing proof audit")
for line in lines:
    if not re.fullmatch(r"'slhdsa\.PeerCall\.\w+' (?:does not depend on any axioms|depends on axioms: \[(?:propext|Classical\.choice|Quot\.sound)(?:, (?:propext|Classical\.choice|Quot\.sound))*\])",line):
        raise SystemExit(line)
    print(line)
PY
