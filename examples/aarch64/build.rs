use cc::Build;
use std::env;

fn main() {
    env::set_var("CROSS_COMPILE", "aarch64-linux-gnu");
    let platform = env::var("CARGO_CFG_PLATFORM").expect("Missing platform name");
    match platform.as_ref() {
        "qemu" => {
            Build::new()
                .file("entry.S")
                .file("exceptions.S")
                .file("idmap.S")
                .compile("empty");
            println!("cargo:rustc-link-arg=-Tqemu.ld");
        }
        "crosvm" => {
            Build::new()
                .file("entry.S")
                .file("exceptions.S")
                .file("idmap_crosvm.S")
                .compile("empty");
            println!("cargo:rustc-link-arg=-Tcrosvm.ld");
        }
        _ => {
            panic!("Unexpected platform name \"{}\"", platform);
        }
    }
    println!("cargo:rustc-link-arg=-Timage.ld");
}
