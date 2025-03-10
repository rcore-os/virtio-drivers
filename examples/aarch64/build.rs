use std::env;

const PLATFORMS: [&str; 2] = ["crosvm", "qemu"];

fn main() {
    println!(
        "cargo::rustc-check-cfg=cfg(platform, values(\"{}\"))",
        PLATFORMS.join("\", \"")
    );

    let platform = env::var("CARGO_CFG_PLATFORM").expect("Missing platform name");
    assert!(
        PLATFORMS.contains(&platform.as_str()),
        "Unexpected platform name {:?}. Supported platforms: {:?}",
        platform,
        PLATFORMS,
    );
    println!("cargo:rustc-link-arg=-Timage.ld");
    println!("cargo:rustc-link-arg=-T{platform}.ld");
    println!("cargo:rerun-if-changed={platform}.ld");
}
