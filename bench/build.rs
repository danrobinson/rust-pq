// Builds the two C implementations linked into the benchmark:
//  * c/ossl_harness.c against Homebrew OpenSSL (override with OPENSSL_DIR);
//  * vendor/slhdsa-c (portable C FIPS 205), with the flags of its own Makefile.
fn main() {
    let ossl = std::env::var("OPENSSL_DIR").unwrap_or_else(|_| "/opt/homebrew/opt/openssl@4".to_string());
    println!("cargo:rerun-if-env-changed=OPENSSL_DIR");
    println!("cargo:rerun-if-changed=c/ossl_harness.c");
    cc::Build::new()
        .file("c/ossl_harness.c")
        .include(format!("{ossl}/include"))
        .compile("ossl_harness");
    println!("cargo:rustc-link-search=native={ossl}/lib");
    println!("cargo:rustc-link-lib=dylib=crypto");

    let d = "vendor/slhdsa-c";
    let mut b = cc::Build::new();
    for f in ["sha2_256.c", "sha2_512.c", "sha3_api.c", "sha3_f1600.c", "slh_dsa.c", "slh_prehash.c", "slh_sha2.c", "slh_shake.c"] {
        b.file(format!("{d}/{f}"));
        println!("cargo:rerun-if-changed={d}/{f}");
    }
    b.include(d).flag("-O3").flag("-fomit-frame-pointer").flag("-std=c99").warnings(false).compile("slhdsac_ref");
}
