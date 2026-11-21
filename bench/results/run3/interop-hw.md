| implementation | scheme | same SK/PK from seeds | verifies verified-crate sig | its sig verifies under verified crate | sig bytes identical | rejects tampered |
|---|---|---|---|---|---|---|
| verified+hw-sha2 | FIPS 205 | yes | yes | yes | yes | yes |
| verified-before | FIPS 205 | yes | yes | yes | yes | yes |
| rustcrypto-slh-dsa | FIPS 205 | yes | yes | yes | yes | yes |
| fips205 | FIPS 205 | yes | yes | yes | yes | yes |
| openssl | FIPS 205 | yes | yes | yes | yes | yes |
| slhdsa-c | FIPS 205 | yes | yes | yes | yes | yes |
| pqclean-r3 | SPHINCS+ r3 | yes | NO | NO | n/a (randomised) | yes |
| variant-A | FIPS 205 | yes | yes | yes | yes | yes |
| variant-B | FIPS 205 | yes | yes | yes | yes | yes |
| variant-C | FIPS 205 | yes | yes | yes | yes | yes |
| variant-D | FIPS 205 | yes | yes | yes | yes | yes |
