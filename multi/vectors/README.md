NIST ACVP test vectors for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}, extracted from
https://github.com/usnistgov/ACVP-Server (gen-val/json-files/SLH-DSA-{keyGen,sigGen,sigVer}-FIPS205/internalProjection.json)
by `scripts/extract_vectors.py`. One file per parameter set; only the SHA-2 groups are kept, and the
pre-hash (HashSLH-DSA) groups are dropped. Each file has 10 keyGen, 28 sigGen and 28 sigVer cases.
`slh-dsa-sha2-128s.json` is identical to `../../vectors/slh-dsa-sha2-128s.json`.
