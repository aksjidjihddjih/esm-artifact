#![allow(dead_code)]
use esm_core::{Arena, Big};
use std::collections::BTreeMap;

pub fn golden_lines() -> Vec<Vec<String>> {
    let p = concat!(env!("CARGO_MANIFEST_DIR"), "/../spec/vectors/golden.txt");
    let s = std::fs::read_to_string(p).expect("golden.txt missing: run ref-py/gen_golden.py");
    s.lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| l.split_whitespace().map(|t| t.to_string()).collect())
        .collect()
}

pub fn of_kind<'a>(g: &'a [Vec<String>], k: &str) -> Vec<&'a Vec<String>> {
    g.iter().filter(|l| l[0] == k).collect()
}

pub fn bits(s: &str) -> Vec<u8> {
    if s == "-" {
        Vec::new()
    } else {
        s.bytes().map(|b| b - b'0').collect()
    }
}

pub fn to_str(b: &[u8]) -> String {
    b.iter().map(|&x| (b'0' + x) as char).collect()
}

pub fn programs(g: &[Vec<String>]) -> BTreeMap<String, Vec<u8>> {
    of_kind(g, "PROG").iter().map(|l| (l[1].clone(), bits(&l[2]))).collect()
}

pub fn parse_in(a: &mut Arena, b: &[u8]) -> u32 {
    esm_core::blc::parse_blc(a, b).expect("program must parse")
}

pub fn n<T: std::str::FromStr>(s: &str) -> T
where
    T::Err: std::fmt::Debug,
{
    s.parse::<T>().unwrap()
}

/// lowercase hex (no prefix) -> Big
pub fn hex_big(s: &str) -> Big {
    let mut limbs: Vec<u64> = Vec::new();
    let b = s.as_bytes();
    let mut end = b.len();
    while end > 0 {
        let start = end.saturating_sub(16);
        limbs.push(u64::from_str_radix(&s[start..end], 16).unwrap());
        end = start;
    }
    Big::from_limbs_le(&limbs).expect("fits")
}

pub fn eq_opt(s: &str) -> Option<bool> {
    match s {
        "True" => Some(true),
        "False" => Some(false),
        "None" => None,
        _ => panic!("bad eq token {s}"),
    }
}

pub fn status_str(s: esm_core::bohm::T6Status) -> &'static str {
    use esm_core::bohm::T6Status::*;
    match s {
        Equal => "equal",
        NotEqual => "not-equal",
        FuelExhausted => "fuel-exhausted",
        ResourceLimit => "resource-limit",
    }
}
