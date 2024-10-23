use cc::Build;
use std::env;

const PLATFORMS: [&str; 2] = ["crosvm", "qemu"];

fn main() {
    println!(
        "cargo::rustc-check-cfg=cfg(platform, values(\"{}\"))",
        PLATFORMS.join("\", \"")
    );

    env::set_var("CROSS_COMPILE", "aarch64-none-elf");
    env::set_var("CC", "clang");

    let platform = env::var("CARGO_CFG_PLATFORM").expect("Missing platform name");
    assert!(
        PLATFORMS.contains(&platform.as_str()),
        "Unexpected platform name {:?}. Supported platforms: {:?}",
        platform,
        PLATFORMS,
    );
    Build::new()
        .file("entry.S")
        .file("exceptions.S")
        .file(format!("idmap_{platform}.S"))
        .compile("example");
    println!("cargo:rustc-link-arg=-T{platform}.ld");
    println!("cargo:rustc-link-arg=-Timage.ld");
}
