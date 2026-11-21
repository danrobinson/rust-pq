| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 4195 | 368 | 875 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 3991 | 322 | 790 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 3548 | 231 | 608 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 7435 | 547 | 1318 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 7302 | 517 | 1260 | 4 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 6752 | 408 | 1040 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 10586 | 710 | 1724 | 4 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 16914 | 1048 | 2556 | 4 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 29250 | 1660 | 4092 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 16159 | 1399 | 3228 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 22667 | 1773 | 4132 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 19729 | 1686 | 3836 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 16484 | 1476 | 3368 | 21 | yes | PASS (all identical) |
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 7275 | 501 | 1285 | 9 | yes | PASS (all identical) |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 7115 | 469 | 1221 | 9 | yes | PASS (all identical) |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 36506 | 2172 | 5332 | 10 | yes | PASS (all identical) |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 16802 | 1014 | 2548 | 10 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 16445 | 1457 | 3359 | 23 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 16207 | 1409 | 3264 | 25 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 19371 | 1578 | 3680 | 25 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 68031 | 4353 | 10400 | 25 | yes | PASS (all identical) |
| chain/i=0,s=15 | start value x | 4 | 68 | 68 | 0 | 108983 | 7505 | 19109 | 135 | yes | PASS (all identical) |
| chain/i=0,s=1 | start value x | 4 | 68 | 68 | 0 | 7315 | 505 | 1329 | 9 | yes | PASS (all identical) |
| chain/i=3,s=7 | start value x | 4 | 68 | 68 | 0 | 50887 | 3505 | 8949 | 63 | yes | PASS (all identical) |
| chain/i=15,s=0 | start value x | 4 | 68 | 68 | 0 | 47 | 5 | 54 | 0 | yes | PASS (all identical) |
| chain/i=0,s=0 | start value x | 4 | 68 | 68 | 0 | 47 | 5 | 54 | 0 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 4102897 | 281796 | 716871 | 5058 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 2653109 | 182979 | 464417 | 3303 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 4102922 | 281800 | 716897 | 5058 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 8213146 | 564108 | 1435078 | 10128 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 16433594 | 1128724 | 2871440 | 20268 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 32874490 | 2257956 | 5744164 | 40548 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 65756282 | 4516420 | 11489612 | 81108 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 2102476069 | 144407798 | 367367034 | 2593425 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 7294 | 502 | 1302 | 9 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 14578 | 1006 | 2587 | 18 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 36459 | 2520 | 6459 | 48 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 167745 | 11604 | 29691 | 228 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 1393081 | 96388 | 246523 | 1908 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 89617273 | 6200836 | 15858427 | 122868 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 1253313492 | 86719802 | 221780489 | 1718025 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 2104427421 | 144541190 | 367707462 | 2595828 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 2104427421 | 144541190 | 367707462 | 2595828 | yes | PASS (all identical) |
| fors_sign, PUBLIC md varied (informational) | public digest md (SK.seed fixed) | 1 | 5 | 5 | 0 | 1253313492 | 86719802 | 221780489 | 1718025 | yes | PASS (all identical) |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 32 | 33 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 17 | 48 | 11331 | 827 | 2096 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 2217388 | 152979 | 388277 | 2763 | yes | PASS (control: difference detected) |
| CONTROL chain, PUBLIC s varied | public step count s | 1 | 33 | 0 | 33 | 181603 | 12505 | 31809 | 225 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 10246 | 642 | 1588 | 4 | yes | PASS (control: difference detected) |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x102764aa7 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102764a00 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #2551: last common event: write 0x50007ffdb8 (size/arg 8) in basic block slhdsa::wots::wots_sign+0x98; A: exec block slhdsa::wots::wots_sign+0xac (size/arg 44) in basic block slhdsa::wots::wots_sign+0xac | B: exec block slhdsa::wots::wots_sign+0xec (size/arg 24) in basic block slhdsa::wots::wots_sign+0xec
- `CONTROL chain, PUBLIC s varied`: first divergence at event #37: last common event: write 0x50007ffe18 (size/arg 8) in basic block slhdsa::wots::chain+0x0; A: exec block slhdsa::wots::chain+0x30 (size/arg 64) in basic block slhdsa::wots::chain+0x30 | B: exec block slhdsa::wots::chain+0x84 (size/arg 32) in basic block slhdsa::wots::chain+0x84
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #23: last common event: write 0x50007ffd60 (size/arg 8) in basic block slhdsa::sha256::sha256+0x0; A: exec block slhdsa::sha256::sha256+0x904 (size/arg 28) in basic block slhdsa::sha256::sha256+0x904 | B: exec block slhdsa::sha256::sha256+0x40 (size/arg 16) in basic block slhdsa::sha256::sha256+0x40

overall: ALL ROWS AS EXPECTED
