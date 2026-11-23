use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake256;

#[test]
fn shake256_matches_rustcrypto_across_rate_boundaries() {
    for length in [0, 1, 8, 135, 136, 137, 271, 272, 273, 512] {
        let message: Vec<_> = (0..length).map(|i| (i * 37 + 13) as u8).collect();
        for output_length in [0, 16, 24, 32, 49, 135, 136, 137, 273] {
            let mut expected = vec![0; output_length];
            Shake256::default()
                .chain(&message)
                .finalize_xof_into(&mut expected);
            let mut actual = vec![0; output_length];
            slhdsa::shake256::shake256(&message, &mut actual);
            assert_eq!(actual, expected, "input {length}, output {output_length}");
        }
    }
}
