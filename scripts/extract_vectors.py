#!/usr/bin/env python3
"""Split the NIST ACVP SLH-DSA internalProjection.json files into one file per
parameter set, dropping the pre-hash (HashSLH-DSA) groups.

usage: extract_vectors.py <dir with keyGen.json sigGen.json sigVer.json> <out dir>
The three inputs are gen-val/json-files/SLH-DSA-{keyGen,sigGen,sigVer}-FIPS205/internalProjection.json
from https://github.com/usnistgov/ACVP-Server."""
import json, sys
src, out = sys.argv[1], sys.argv[2]
SETS = ["128s", "128f", "192s", "192f", "256s", "256f"]
data = {k: json.load(open(f"{src}/{k}.json"))["testGroups"] for k in ["keyGen", "sigGen", "sigVer"]}
for family in ["SHA2", "SHAKE"]:
    for s in SETS:
        name = f"SLH-DSA-{family}-{s}"
        res = {}
        for k, groups in data.items():
            res[k] = [g for g in groups if g["parameterSet"] == name and g.get("preHash", "none") != "preHash"]
        with open(f"{out}/slh-dsa-{family.lower()}-{s}.json", "w") as f:
            json.dump(res, f, indent=1)
        print(name, {k: sum(len(g["tests"]) for g in v) for k, v in res.items()})
