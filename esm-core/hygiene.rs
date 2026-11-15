//! Determinism hygiene of the guest-facing crate: no platform-width integers outside `util.rs`, no floating point,
//! no `HashMap`/`HashSet`, no threads, no `std`, no `unsafe`, no dependencies.
use std::fs;
use std::path::Path;

fn sources() -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut v = Vec::new();
    for e in fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().map_or(false, |x| x == "rs") {
            v.push((p.file_name().unwrap().to_string_lossy().to_string(), fs::read_to_string(&p).unwrap()));
        }
    }
    v
}

fn code_lines(src: &str) -> impl Iterator<Item = &str> {
    src.lines().filter(|l| !l.trim_start().starts_with("//"))
}

#[test]
fn forbidden_constructs_are_absent() {
    let banned = ["f32", "f64", "HashMap", "HashSet", "std::", "extern crate std", "thread", "unsafe {", "unsafe fn", "unsafe impl", "static mut", "Instant", "SystemTime", "rand"];
    for (name, src) in sources() {
        for (i, l) in code_lines(&src).enumerate() {
            for b in banned {
                assert!(!l.contains(b), "{name}: line {i} contains `{b}`: {l}");
            }
        }
    }
}

#[test]
fn platform_width_integer_only_in_util() {
    let word = ["us", "ize"].concat();
    for (name, src) in sources() {
        let n = code_lines(&src).filter(|l| l.contains(&word)).count();
        if name == "util.rs" {
            assert!(n > 0);
        } else {
            assert_eq!(n, 0, "{name} must use explicit-width integers only");
        }
    }
}

#[test]
fn crate_is_no_std_forbid_unsafe_and_dependency_free() {
    let lib = sources().into_iter().find(|(n, _)| n == "lib.rs").unwrap().1;
    assert!(lib.contains("#![no_std]") && lib.contains("#![forbid(unsafe_code)]") && lib.contains("extern crate alloc;"));
    let toml = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml")).unwrap();
    let deps = toml.split("[dependencies]").nth(1).unwrap().split('[').next().unwrap();
    assert!(deps.lines().all(|l| l.trim().is_empty() || l.trim().starts_with('#')), "no dependencies allowed: {deps}");
}
