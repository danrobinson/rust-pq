// Links the `cttrace` binary against libunicorn (taken from the `unicorn`
// Python wheel, see run.sh). The `dudect` binary does not need it.
fn main() {
    println!("cargo:rerun-if-env-changed=UNICORN_LIB_DIR");
    println!("cargo:rerun-if-changed=build.rs");
    match std::env::var("UNICORN_LIB_DIR") {
        Ok(dir) => {
            println!("cargo:rustc-link-arg-bin=cttrace=-L{dir}");
            println!("cargo:rustc-link-arg-bin=cttrace=-lunicorn.2");
            println!("cargo:rustc-link-arg-bin=cttrace=-Wl,-rpath,{dir}");
        }
        Err(_) => {
            println!("cargo:warning=UNICORN_LIB_DIR not set: the cttrace binary will fail to link (use ./run.sh, or build only --bin dudect)");
        }
    }
}
