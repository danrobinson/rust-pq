use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=src/bridge.m");
    println!("cargo:rerun-if-changed=shaders/slhdsa.metal");
    println!("cargo:rerun-if-changed=shaders/slhdsa_shake.metal");

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os != "macos" {
        panic!("slhdsa-metal requires macOS with Apple Metal framework");
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let obj_path = out_dir.join("bridge.o");
    let lib_path = out_dir.join("libmetal_bridge.a");

    let status = Command::new("clang")
        .args([
            "-c",
            "-fobjc-arc",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "src/bridge.m",
            "-o",
        ])
        .arg(&obj_path)
        .status()
        .expect("failed to invoke clang for src/bridge.m");
    assert!(status.success(), "clang failed compiling src/bridge.m");

    let status = Command::new("ar")
        .args(["rcs"])
        .arg(&lib_path)
        .arg(&obj_path)
        .status()
        .expect("failed to invoke ar for libmetal_bridge.a");
    assert!(status.success(), "ar failed creating libmetal_bridge.a");

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static=metal_bridge");
    println!("cargo:rustc-link-lib=framework=Metal");
    println!("cargo:rustc-link-lib=framework=Foundation");
}
