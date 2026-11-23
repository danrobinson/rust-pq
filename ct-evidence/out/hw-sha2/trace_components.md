crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 1490 | 242 | 613 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 1241 | 196 | 528 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 682 | 105 | 346 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 1943 | 291 | 812 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 1868 | 286 | 794 | 5 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 1077 | 152 | 530 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 2338 | 338 | 996 | 5 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 3035 | 424 | 1322 | 5 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 3890 | 487 | 1790 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 4936 | 824 | 2208 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 5897 | 950 | 2626 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 5864 | 1005 | 2604 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 5461 | 931 | 2399 | 23 | yes | PASS (all identical) |
| compress (copy inlined into the wrapper) | state and block | 1 | 65 | 65 | 0 | 392 | 46 | 184 | 0 | yes | PASS (all identical) |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 495 | 53 | 263 | 1 | yes | PASS (all identical) |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 495 | 53 | 263 | 1 | yes | PASS (all identical) |
| thash/len=16 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 1159 | 181 | 557 | 8 | yes | PASS (all identical) |
| thash/len=32 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 951 | 149 | 493 | 8 | yes | PASS (all identical) |
| thash/len=224 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 2124 | 288 | 1029 | 8 | yes | PASS (all identical) |
| thash/len=560 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 5189 | 690 | 2328 | 10 | yes | PASS (all identical) |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 4 | 68 | 68 | 0 | 4071 | 466 | 1973 | 0 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 3108 | 458 | 1395 | 11 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 2721 | 397 | 1274 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 3064 | 436 | 1442 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 9733 | 1261 | 4360 | 13 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1877 | 54 | 439 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=3..10 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1029 | 38 | 423 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=5..5 (none) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 210 | 16 | 338 | 1 | yes | PASS (all identical) |
| chain_blocks/n=3,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 5581 | 71 | 2003 | 1 | yes | PASS (all identical) |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 7585 | 91 | 2715 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 64477 | 659 | 20971 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 41371 | 782 | 16490 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=d_i..15 (wots_pk_from_sig) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 44173 | 803 | 17145 | 1 | yes | PASS (all identical) |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 68 | 68 | 0 | 2857 | 133 | 1654 | 1 | yes | PASS (all identical) |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 24076 | 1022 | 12340 | 1 | yes | PASS (all identical) |
| chain_blocks/n=7,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 144 | 144 | 0 | 5365 | 156 | 2305 | 1 | yes | PASS (all identical) |
| chain_blocks/n=64,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 32361 | 824 | 13996 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,random ranges,distinct prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 18380 | 535 | 8177 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 23290 | 2794 | 10699 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=35,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 36 | 36 | 0 | 48067 | 5837 | 21950 | 1 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 75867 | 1436 | 26735 | 2 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 51246 | 1529 | 20987 | 20 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 75893 | 1439 | 26765 | 2 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 152270 | 2932 | 53749 | 5 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 305024 | 5918 | 107717 | 11 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 610532 | 11890 | 215653 | 23 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 1221548 | 23834 | 431525 | 47 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 39071767 | 763925 | 13806316 | 1544 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 513 | 54 | 280 | 1 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 905 | 52 | 790 | 2 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 1737 | 97 | 1360 | 2 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 5876 | 278 | 3850 | 2 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 42012 | 1851 | 23852 | 2 | yes | PASS (all identical) |
| fors_node/z=7 | SK.seed | 4 | 68 | 68 | 0 | 82912 | 3622 | 46216 | 2 | yes | PASS (all identical) |
| fors_node/z=8 | SK.seed | 2 | 18 | 18 | 0 | 166310 | 7297 | 92652 | 5 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 2668250 | 117547 | 1485732 | 95 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 37376192 | 1647132 | 20857671 | 1457 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 39104965 | 764410 | 13815845 | 1535 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 39104965 | 764410 | 13815845 | 1535 | yes | PASS (all identical) |
| api::keygen | SK.seed and SK.prf (PK.seed fixed) | 2 | 18 | 18 | 0 | 39104989 | 764412 | 13815881 | 1535 | yes | PASS (all identical) |
| wots_pk_from_sig | WOTS+ signature bytes (m public, fixed) | 4 | 36 | 36 | 0 | 42515 | 1525 | 17504 | 10 | yes | PASS (all identical) |
| xmss_pk_from_sig | XMSS signature bytes (m, idx public, fixed) | 4 | 36 | 36 | 0 | 50373 | 2019 | 20594 | 19 | yes | PASS (all identical) |
| fors_pk_from_sig | FORS signature bytes (md public, fixed) | 4 | 36 | 36 | 0 | 50393 | 2755 | 30372 | 19 | yes | PASS (all identical) |
| INFO fors_sign, PUBLIC md varied | public digest md (SK.seed fixed) | 1 | 9 | 9 | 0 | 37376192 | 1647132 | 20857671 | 1457 | yes | info: identical |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 35 | 30 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 12 | 53 | 2931 | 449 | 1310 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 45597 | 1450 | 18862 | 20 | yes | PASS (control: difference detected) |
| CONTROL chain_blocks n=4, PUBLIC end of block 0 varied | public step count of one block (0..255) | 1 | 33 | 0 | 33 | 4832 | 85 | 1751 | 1 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 1323 | 189 | 606 | 4 | yes | PASS (control: difference detected) |
| PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix | one public bit: block 2 starts like the other blocks, or not | 1 | 8 | 0 | 8 | 4560 | 97 | 1974 | 1 | yes | PASS (control: difference detected) |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x102b75d8c (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102b75cc0 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #5277: last common event: read 0x40000000f0 (size/arg 4) in basic block slhdsa::hash::chain_blocks+0x1f4; A: exec block slhdsa::hash::chain_blocks+0x204 (size/arg 40) in basic block slhdsa::hash::chain_blocks+0x204 | B: exec block slhdsa::hash::chain_blocks+0x1e4 (size/arg 16) in basic block slhdsa::hash::chain_blocks+0x1e4
- `CONTROL chain_blocks n=4, PUBLIC end of block 0 varied`: first divergence at event #346: last common event: read 0x50007ffcb0 (size/arg 4) in basic block slhdsa::hash::chain_blocks+0x1f4; A: exec block slhdsa::hash::chain_blocks+0x204 (size/arg 40) in basic block slhdsa::hash::chain_blocks+0x204 | B: exec block slhdsa::hash::chain_blocks+0x1e4 (size/arg 16) in basic block slhdsa::hash::chain_blocks+0x1e4
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #29: last common event: write 0x50007ffe18 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x0; A: exec block slhdsa::sha256::sha256_from+0x50 (size/arg 20) in basic block slhdsa::sha256::sha256_from+0x50 | B: exec block slhdsa::sha256::sha256_from+0x48 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x48
- `PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix`: first divergence at event #443: last common event: read 0x6000010088 (size/arg 8) in basic block slhdsa::hash::chain_blocks+0x204; A: exec block slhdsa::hash::chain_blocks+0x22c (size/arg 36) in basic block slhdsa::hash::chain_blocks+0x22c | B: exec block slhdsa::hash::chain_blocks+0x194 (size/arg 96) in basic block slhdsa::hash::chain_blocks+0x194

overall: ALL ROWS AS EXPECTED
