//! The Rust constants must equal the frozen `spec/params.toml` (single source of truth).
use esm_core::params::*;
use std::collections::BTreeMap;

fn load() -> BTreeMap<String, String> {
    let p = concat!(env!("CARGO_MANIFEST_DIR"), "/../spec/params.toml");
    let text = std::fs::read_to_string(p).expect("spec/params.toml");
    let (mut section, mut map) = (String::new(), BTreeMap::new());
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') {
            section = line.trim_matches(|c| c == '[' || c == ']').to_string();
            continue;
        }
        let (k, v) = line.split_once('=').expect("key = value");
        let v = v.split('#').next().unwrap().trim().trim_matches('"').replace('_', "");
        map.insert(format!("{}.{}", section, k.trim()), v);
    }
    map
}

fn int(m: &BTreeMap<String, String>, k: &str) -> u128 {
    m.get(k).unwrap_or_else(|| panic!("missing {k}")).parse().unwrap_or_else(|_| panic!("not an integer: {k}"))
}

#[test]
fn rust_constants_equal_params_toml() {
    let m = load();
    assert_eq!(int(&m, "time.n_com") as u64, N_COM);
    assert_eq!(int(&m, "time.n_delay") as u64, N_DELAY);
    assert_eq!(int(&m, "time.n_rev") as u64, N_REV);
    assert_eq!(int(&m, "time.n_batch") as u64, N_BATCH);
    assert_eq!(int(&m, "time.n_epoch") as u64, N_EPOCH);
    assert_eq!(int(&m, "time.n_lock") as u64, N_LOCK);
    assert_eq!(N_COM + N_DELAY + N_REV, N_BATCH);
    assert_eq!(166 * N_BATCH, N_EPOCH);
    assert_eq!(int(&m, "bounds.mint_cap"), MINT_CAP);
    assert_eq!(MINT_CAP, (1u128 << 96) - 1);
    assert_eq!(int(&m, "bounds.max_n_k") as u64, MAX_N_K);
    assert_eq!(int(&m, "bounds.max_b_k") as u32, MAX_B_K);
    assert_eq!(MAX_N_K * MAX_B_K as u64, 1u64 << 40);
    assert_eq!(int(&m, "bounds.max_phi0_bits") as u64, MAX_N_K * MAX_B_K as u64);
    assert_eq!(int(&m, "bounds.t_max") as u64, T_MAX);
    assert_eq!(int(&m, "bounds.delta_cap_v1") as u64, DELTA_CAP_V1);
    assert_eq!(int(&m, "bounds.max_cited_axioms") as u32, MAX_CITED_AXIOMS);
    assert_eq!(int(&m, "bounds.max_rbf_sponsors") as u32, MAX_RBF_SPONSORS);
    assert_eq!(int(&m, "bounds.max_prog_bits") as u32, MAX_PROG_BITS);
    assert_eq!(int(&m, "bounds.kam_heap_per_step") as u64, KAM_HEAP_PER_STEP);
    assert_eq!(int(&m, "bounds.max_debruijn_index") as u32, MAX_DEBRUIJN_INDEX);
    assert_eq!(MAX_DEBRUIJN_INDEX, 255);
    assert_eq!(DELTA_CAP_V1, 65_536);
    assert_eq!(int(&m, "bounds.c_hdr_bits") as u64, C_HDR);
    for (k, c) in [
        ("epsilon_bps", EPSILON_BPS),
        ("gamma_bps", GAMMA_BPS),
        ("beta_d_bps", BETA_D_BPS),
        ("kappa_bps", KAPPA_BPS),
        ("sigma_col_bps", SIGMA_COL_BPS),
        ("sigma_dict_bps", SIGMA_DICT_BPS),
        ("m_cap_bps", M_CAP_BPS),
    ] {
        assert_eq!(int(&m, &format!("protocol.{k}")) as u64, c, "{k}");
    }
    assert_eq!(m["asset.symbol"], "WETH");
    assert_eq!(m["asset.decimals"], "18");
    assert_eq!(m["execution.jets"], "false");
    assert_eq!(m["execution.stylus"], "false");
    assert!(delta_in_profile(1) && delta_in_profile(DELTA_CAP_V1) && !delta_in_profile(0) && !delta_in_profile(DELTA_CAP_V1 + 1));
}
