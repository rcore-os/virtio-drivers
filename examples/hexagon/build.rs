fn main() {
    println!("cargo:rerun-if-changed=src/startup.S");

    cc::Build::new()
        .file("src/startup.S")
        .compiler("hexagon-unknown-none-elf-clang")
        .flags(["-G0", "-fno-PIC",])
        .compile("startup");
}
