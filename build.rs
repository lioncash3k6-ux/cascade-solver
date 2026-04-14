fn main() {
    // Compile the C++ FFI wrapper
    cc::Build::new()
        .cpp(true)
        .file("cadical_ffi.cpp")
        .include("/root/cadical-src/src")
        .include("/root/cadical-src/build")
        .flag("-O3")
        .compile("cadical_ffi");

    // Link with CaDiCaL static library
    println!("cargo:rustc-link-search=/root/cadical-src/build");
    println!("cargo:rustc-link-lib=static=cadical");
    println!("cargo:rustc-link-lib=stdc++");

    // Rebuild if FFI wrapper changes
    println!("cargo:rerun-if-changed=cadical_ffi.cpp");
    println!("cargo:rerun-if-changed=cadical_ffi.h");
}
