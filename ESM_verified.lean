namespace ESM

def escrowAlloc (B Phi d : Nat) : Nat :=
  (B * d) / Phi

def ceilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

theorem div_le_div_right {a b c : Nat} (h : a ≤ b) : a / c ≤ b / c := by
  by_cases hc : c = 0
  · subst hc; simp [Nat.div_zero]
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc
    have h1 : a / c * c ≤ a := Nat.div_mul_le_self a c
    exact (Nat.le_div_iff_mul_le hc_pos).mpr (Nat.le_trans h1 h)

theorem add_div_le_div_add (x y c : Nat) : (x / c) + (y / c) ≤ (x + y) / c := by
  by_cases hc : c = 0
  · subst hc; simp [Nat.div_zero]
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc
    have hx : x / c * c ≤ x := Nat.div_mul_le_self x c
    have hy : y / c * c ≤ y := Nat.div_mul_le_self y c
    have hxy : (x / c + y / c) * c ≤ x + y := by
      rw [Nat.add_mul]; exact Nat.add_le_add hx hy
    exact (Nat.le_div_iff_mul_le hc_pos).mpr hxy

theorem mul_bps_div_le (rate_bps X : Nat) (h_rate : rate_bps ≤ 10000) :
    (rate_bps * X) / 10000 ≤ X := by
  have h_m : rate_bps * X ≤ 10000 * X := Nat.mul_le_mul_right X h_rate
  have h_d := div_le_div_right (c := 10000) h_m
  rw [Nat.mul_div_cancel_left X (by decide : 0 < 10000)] at h_d
  exact h_d

theorem escrowAlloc_mono (B Phi d1 d2 : Nat) (h : d1 ≤ d2) :
    escrowAlloc B Phi d1 ≤ escrowAlloc B Phi d2 := by
  unfold escrowAlloc
  exact div_le_div_right (Nat.mul_le_mul_left B h)

theorem escrowAlloc_superadd (B Phi d1 d2 : Nat) :
    escrowAlloc B Phi d1 + escrowAlloc B Phi d2 ≤ escrowAlloc B Phi (d1 + d2) := by
  unfold escrowAlloc
  rw [Nat.mul_add]
  exact add_div_le_div_add (B * d1) (B * d2) Phi

theorem pool_lower_bound_ceil
    (B Phi0 Phi_best d_used e_used B_rem : Nat)
    (h_Phi_pos : Phi0 > 0)
    (h_front   : Phi_best + d_used = Phi0)
    (h_escrow  : e_used ≤ escrowAlloc B Phi0 d_used)
    (h_cons    : B_rem + e_used = B) :
    B_rem ≥ ceilDiv (B * Phi_best) Phi0 := by
  unfold ceilDiv
  unfold escrowAlloc at h_escrow
  have h_mul_eq : B * Phi_best + B * d_used = B * Phi0 := by
    rw [← Nat.mul_add, h_front]
  have h_div_le : (B * d_used) / Phi0 * Phi0 ≤ B * d_used :=
    Nat.div_mul_le_self (B * d_used) Phi0
  have h_e_mul : e_used * Phi0 ≤ B * d_used :=
    Nat.le_trans (Nat.mul_le_mul_right Phi0 h_escrow) h_div_le
  have h_rem_mul : B * Phi_best ≤ B_rem * Phi0 := by
    have h_tot : B_rem * Phi0 + e_used * Phi0 = B * Phi0 := by
      rw [← Nat.add_mul, h_cons]
    omega
  have h_num : B * Phi_best + Phi0 - 1 ≤ B_rem * Phi0 + Phi0 - 1 := by omega
  have h_d := div_le_div_right (c := Phi0) h_num
  have h_rhs : (B_rem * Phi0 + Phi0 - 1) / Phi0 ≤ B_rem := by
    have h_lt : (B_rem * Phi0 + Phi0 - 1) < (B_rem + 1) * Phi0 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h_le_succ : (B_rem * Phi0 + Phi0 - 1) / Phi0 < B_rem + 1 :=
      (Nat.div_lt_iff_lt_mul h_Phi_pos).mpr h_lt
    omega
  exact Nat.le_trans h_d h_rhs

theorem local_desc_ge_one (w_len omega_len ell_delta L_res d_punct anc_sum : Nat)
    (h_elias : ell_delta ≥ 1) :
    let L_local := w_len + omega_len + ell_delta
    let Phi_local := L_local + L_res + d_punct + anc_sum
    Phi_local ≥ 1 := by
  intro L_local Phi_local; omega

def calcRoyalty (gamma_bps E_net x d_tr : Nat) : Nat :=
  (gamma_bps * E_net * x) / (10000 * d_tr)

theorem syntactic_reduction_waterfall_valid
    (gamma_bps E_net a_u cap_s d_tr : Nat) :
    let x_s := Nat.min a_u cap_s
    let x_u := a_u - x_s
    let R_s := calcRoyalty gamma_bps E_net x_s d_tr
    let R_u := calcRoyalty gamma_bps E_net x_u d_tr
    let R_orig := calcRoyalty gamma_bps E_net a_u d_tr
    x_s + x_u = a_u ∧ R_s + R_u ≤ R_orig := by
  intro x_s x_u R_s R_u R_orig
  have h_le : x_s ≤ a_u := Nat.min_le_left a_u cap_s
  have h_sum : x_s + x_u = a_u := Nat.add_sub_of_le h_le
  constructor
  · exact h_sum
  · dsimp [R_s, R_u, R_orig, calcRoyalty]
    have h_ineq := add_div_le_div_add (gamma_bps * E_net * x_s) (gamma_bps * E_net * x_u) (10000 * d_tr)
    rw [← Nat.mul_add, h_sum] at h_ineq
    exact h_ineq

def capStep (st : Nat × Nat) (p : Nat × Nat) : Nat × Nat :=
  let x := Nat.min p.1 (Nat.min p.2 st.1)
  (st.1 - x, st.2 + x)

theorem capStep_conserves (st : Nat × Nat) (p : Nat × Nat) :
    (capStep st p).1 + (capStep st p).2 = st.1 + st.2 := by
  dsimp [capStep]
  have h1 : Nat.min p.2 st.1 ≤ st.1 := Nat.min_le_right p.2 st.1
  have h2 : Nat.min p.1 (Nat.min p.2 st.1) ≤ st.1 :=
    Nat.le_trans (Nat.min_le_right p.1 _) h1
  omega

theorem capFold_conserves (l : List (Nat × Nat)) :
    ∀ (R acc : Nat),
      (l.foldl capStep (R, acc)).1 + (l.foldl capStep (R, acc)).2 = R + acc := by
  induction l with
  | nil => intro R acc; simp
  | cons hd tl ih =>
    intro R acc
    simp only [List.foldl_cons]
    have h_ih : (List.foldl capStep (capStep (R, acc) hd) tl).1 + (List.foldl capStep (capStep (R, acc) hd) tl).2 = (capStep (R, acc) hd).1 + (capStep (R, acc) hd).2 := ih _ _
    have h_step := capStep_conserves (R, acc) hd
    omega

theorem capFold_general_bound (l : List (Nat × Nat)) (Saved S0 d_amort : Nat)
    (h_saved : Saved ≤ d_amort)
    (h_s0    : S0 ≤ d_amort) :
    (l.foldl capStep (Saved - S0, S0)).2 ≤ Nat.max S0 Saved ∧
    (l.foldl capStep (Saved - S0, S0)).2 ≤ d_amort := by
  have h_cons := capFold_conserves l (Saved - S0) S0
  have h_max_le : Nat.max S0 Saved ≤ d_amort := by
    by_cases h : S0 ≤ Saved
    · have hm : Nat.max S0 Saved = Saved := Nat.max_eq_right h
      omega
    · have hm : Nat.max S0 Saved = S0 := Nat.max_eq_left (by omega)
      omega
  have h_sum_le : (Saved - S0) + S0 ≤ Nat.max S0 Saved := by
    by_cases h : S0 ≤ Saved
    · have hm : Nat.max S0 Saved = Saved := Nat.max_eq_right h
      omega
    · have hm : Nat.max S0 Saved = S0 := Nat.max_eq_left (by omega)
      omega
  omega

def sumDiv (c : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => a / c + sumDiv c t

theorem sumDiv_le (c : Nat) (l : List Nat) : sumDiv c l ≤ l.sum / c := by
  induction l with
  | nil => simp [sumDiv]
  | cons a t ih =>
    simp only [sumDiv, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (add_div_le_div_add a t.sum c)

def sumRoyalty (gamma_bps E_net d_tr : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => calcRoyalty gamma_bps E_net x d_tr + sumRoyalty gamma_bps E_net d_tr xs

theorem sumRoyalty_le_total (gamma_bps E_net d_tr : Nat) (xs : List Nat) :
    sumRoyalty gamma_bps E_net d_tr xs ≤ calcRoyalty gamma_bps E_net xs.sum d_tr := by
  induction xs with
  | nil => simp [sumRoyalty, calcRoyalty]
  | cons x tl ih =>
    simp only [sumRoyalty, List.sum_cons]
    have h1 := Nat.add_le_add_left ih (calcRoyalty gamma_bps E_net x d_tr)
    dsimp [calcRoyalty] at h1 ⊢
    have h2 := add_div_le_div_add (gamma_bps * E_net * x) (gamma_bps * E_net * tl.sum) (10000 * d_tr)
    rw [← Nat.mul_add] at h2
    exact Nat.le_trans h1 h2

theorem settle_general_list_conserves
    (E_tr d_tr eps_bps gamma_bps phi_guar_bps : Nat) (xs : List Nat)
    (h_d_pos : d_tr > 0)
    (h_x_sum : xs.sum ≤ d_tr)
    (h_eps   : eps_bps ≤ 10000)
    (h_gamma : gamma_bps ≤ 10000)
    (h_phi   : phi_guar_bps ≤ 10000) :
    let E_burn     := (eps_bps * E_tr) / 10000
    let E_net      := E_tr - E_burn
    let R_anc      := sumRoyalty gamma_bps E_net d_tr xs
    let R_rem      := E_net - R_anc
    let R_guar     := (phi_guar_bps * R_rem) / 10000
    let R_proposer := R_rem - R_guar
    R_anc ≤ E_net ∧ E_burn + R_anc + R_guar + R_proposer = E_tr := by
  intro E_burn E_net R_anc R_rem R_guar R_proposer
  have h_burn_le : E_burn ≤ E_tr := mul_bps_div_le eps_bps E_tr h_eps
  have h_sum_le : R_anc ≤ calcRoyalty gamma_bps E_net xs.sum d_tr :=
    sumRoyalty_le_total gamma_bps E_net d_tr xs
  have h_le_d : calcRoyalty gamma_bps E_net xs.sum d_tr ≤ calcRoyalty gamma_bps E_net d_tr d_tr := by
    dsimp [calcRoyalty]
    exact div_le_div_right (Nat.mul_le_mul_left (gamma_bps * E_net) h_x_sum)
  have h_le_net : calcRoyalty gamma_bps E_net d_tr d_tr ≤ E_net := by
    dsimp [calcRoyalty]
    have h_num : gamma_bps * E_net * d_tr ≤ 10000 * d_tr * E_net := by
      have h1 : gamma_bps * E_net ≤ 10000 * E_net := Nat.mul_le_mul_right E_net h_gamma
      have h2 : gamma_bps * E_net * d_tr ≤ 10000 * E_net * d_tr := Nat.mul_le_mul_right d_tr h1
      have h_comm : 10000 * E_net * d_tr = 10000 * d_tr * E_net := by
        rw [Nat.mul_assoc, Nat.mul_comm E_net d_tr, ← Nat.mul_assoc]
      rw [h_comm] at h2; exact h2
    have h_denom_pos : 0 < 10000 * d_tr := Nat.mul_pos (by decide) h_d_pos
    have h_div := div_le_div_right (c := 10000 * d_tr) h_num
    rw [Nat.mul_div_cancel_left E_net h_denom_pos] at h_div
    exact h_div
  have h_anc_le : R_anc ≤ E_net := Nat.le_trans h_sum_le (Nat.le_trans h_le_d h_le_net)
  have h_guar_le : R_guar ≤ R_rem := mul_bps_div_le phi_guar_bps R_rem h_phi
  constructor
  · exact h_anc_le
  · show E_burn + R_anc + R_guar + (E_tr - E_burn - R_anc - R_guar) = E_tr
    omega

theorem slot_four_way_split_conserves
    (R_x beta_D_bps D_tot phi_dict_bps S_st_bar S_tot_bar : Nat)
    (rbf_paid_sum dict_div_sum : Nat)
    (h_beta   : beta_D_bps ≤ 10000)
    (h_phi_d  : phi_dict_bps ≤ 10000)
    (h_st_le  : S_st_bar ≤ S_tot_bar)
    (h_rbf_le : rbf_paid_sum ≤ Nat.min (R_x - (beta_D_bps * R_x) / 10000) D_tot)
    (h_div_le : dict_div_sum ≤
      if S_tot_bar = 0 then 0
      else (phi_dict_bps * S_st_bar * ((R_x - (beta_D_bps * R_x) / 10000) - rbf_paid_sum)) / (10000 * S_tot_bar)) :
    let R_anchor := (beta_D_bps * R_x) / 10000
    let R_net    := R_x - R_anchor
    let R_rem    := R_net - rbf_paid_sum
    let R_owner  := R_rem - dict_div_sum
    R_anchor + rbf_paid_sum + dict_div_sum + R_owner = R_x := by
  intro R_anchor R_net R_rem R_owner
  have h_anc : R_anchor ≤ R_x := mul_bps_div_le beta_D_bps R_x h_beta
  have h_rbf_net : rbf_paid_sum ≤ R_net :=
    Nat.le_trans h_rbf_le (Nat.min_le_left R_net D_tot)
  have h_dict_rem :
      (if S_tot_bar = 0 then 0 else (phi_dict_bps * S_st_bar * R_rem) / (10000 * S_tot_bar)) ≤ R_rem := by
    split
    · exact Nat.zero_le _
    · next h_ne =>
      have h_pos : 0 < S_tot_bar := Nat.pos_of_ne_zero h_ne
      have h_denom_pos : 0 < 10000 * S_tot_bar := Nat.mul_pos (by decide) h_pos
      have h1 : phi_dict_bps * S_st_bar ≤ 10000 * S_tot_bar :=
        Nat.le_trans (Nat.mul_le_mul_right S_st_bar h_phi_d) (Nat.mul_le_mul_left 10000 h_st_le)
      have h2 : phi_dict_bps * S_st_bar * R_rem ≤ 10000 * S_tot_bar * R_rem :=
        Nat.mul_le_mul_right R_rem h1
      have h_d := div_le_div_right (c := 10000 * S_tot_bar) h2
      rw [Nat.mul_div_cancel_left R_rem h_denom_pos] at h_d
      exact h_d
  have h_div_rem : dict_div_sum ≤ R_rem := Nat.le_trans h_div_le h_dict_rem
  show R_anchor + rbf_paid_sum + dict_div_sum + (R_x - R_anchor - rbf_paid_sum - dict_div_sum) = R_x
  omega

def safeRemEscrow (B Phi E_tr d_tr d_rem_tr : Nat) : Nat :=
  if d_tr = 0 then 0
  else Nat.min ((E_tr * d_rem_tr) / d_tr) (escrowAlloc B Phi d_rem_tr)

theorem tranche_unroll_conserves_and_bounds
    (B Phi E_init E_abs d_init d_abs d_rem_init d_rem_abs d_unroll : Nat)
    (h_rem_i : d_rem_init ≤ d_init)
    (h_rem_a : d_rem_abs  ≤ d_abs) :
    let E_total   := E_init + E_abs
    let E_rem_i   := safeRemEscrow B Phi E_init d_init d_rem_init
    let E_rem_a   := safeRemEscrow B Phi E_abs  d_abs  d_rem_abs
    let E_rem     := E_rem_i + E_rem_a
    let E_unroll  := Nat.min (E_total - E_rem) (escrowAlloc B Phi d_unroll)
    let E_dust    := E_total - E_rem - E_unroll
    E_rem_i ≤ escrowAlloc B Phi d_rem_init ∧
    E_rem_a ≤ escrowAlloc B Phi d_rem_abs ∧
    E_unroll ≤ escrowAlloc B Phi d_unroll ∧
    E_rem + E_unroll ≤ E_total ∧
    E_rem + E_unroll + E_dust = E_total := by
  intro E_total E_rem_i E_rem_a E_rem E_unroll E_dust
  have hi : E_rem_i ≤ escrowAlloc B Phi d_rem_init := by
    dsimp [E_rem_i, safeRemEscrow]; split
    · exact Nat.zero_le _
    · exact Nat.min_le_right _ _
  have ha : E_rem_a ≤ escrowAlloc B Phi d_rem_abs := by
    dsimp [E_rem_a, safeRemEscrow]; split
    · exact Nat.zero_le _
    · exact Nat.min_le_right _ _
  have hu : E_unroll ≤ escrowAlloc B Phi d_unroll := Nat.min_le_right _ _
  have h_rem_le_init : E_rem_i ≤ E_init := by
    dsimp [E_rem_i, safeRemEscrow]; split
    · exact Nat.zero_le _
    · next h_ne =>
      have h_pos : 0 < d_init := Nat.pos_of_ne_zero h_ne
      have h_mul : E_init * d_rem_init ≤ E_init * d_init := Nat.mul_le_mul_left E_init h_rem_i
      have h_d : (E_init * d_rem_init) / d_init ≤ (E_init * d_init) / d_init := div_le_div_right h_mul
      rw [Nat.mul_div_cancel E_init h_pos] at h_d
      exact Nat.le_trans (Nat.min_le_left _ _) h_d
  have h_rem_le_abs : E_rem_a ≤ E_abs := by
    dsimp [E_rem_a, safeRemEscrow]; split
    · exact Nat.zero_le _
    · next h_ne =>
      have h_pos : 0 < d_abs := Nat.pos_of_ne_zero h_ne
      have h_mul : E_abs * d_rem_abs ≤ E_abs * d_abs := Nat.mul_le_mul_left E_abs h_rem_a
      have h_d : (E_abs * d_rem_abs) / d_abs ≤ (E_abs * d_abs) / d_abs := div_le_div_right h_mul
      rw [Nat.mul_div_cancel E_abs h_pos] at h_d
      exact Nat.le_trans (Nat.min_le_left _ _) h_d
  have h_un_le : E_unroll ≤ E_total - E_rem := Nat.min_le_left _ _
  have h_rem_le : E_rem ≤ E_total := by
    show E_rem_i + E_rem_a ≤ E_init + E_abs
    exact Nat.add_le_add h_rem_le_init h_rem_le_abs
  refine ⟨hi, ha, hu, by omega, ?_⟩
  show E_rem + E_unroll + (E_total - E_rem - E_unroll) = E_total
  omega

theorem puncture_invariant_preserved
    (F Phi_local d_tot d_unsettled delta_Phi d_rem_tot : Nat)
    (h_inv_before : d_unsettled ≤ d_tot)
    (h_front_before : d_tot ≤ F - Phi_local)
    (h_rem_bound : d_rem_tot ≤ d_tot - delta_Phi) :
    let D_req     := d_tot - d_rem_tot
    let d_unroll  := Nat.min d_unsettled D_req
    let d_rem     := d_unsettled - d_unroll
    let d_tot_new := d_rem_tot
    let Phi_new   := Phi_local + delta_Phi
    d_rem ≤ d_tot_new ∧ d_tot_new ≤ F - Phi_new := by
  intro D_req d_unroll d_rem d_tot_new Phi_new
  by_cases h : d_unsettled ≤ D_req
  · have hm : d_unroll = d_unsettled := Nat.min_eq_left h
    omega
  · have hm : d_unroll = D_req := Nat.min_eq_right (by omega)
    omega

def calcAmortGen (L C_burn B Phi net_bps : Nat) : Nat :=
  Nat.min L ((10000 * C_burn * Phi) / (net_bps * B))

def calcNetRewardGen (B Phi d_saved net_bps : Nat) : Nat :=
  (net_bps * escrowAlloc B Phi d_saved) / 10000

theorem single_data_pre_embedding_unprofitable
    (L C_burn B Phi l_E net_bps : Nat)
    (h_Phi : Phi > 0) :
    let d_amort := calcAmortGen L C_burn B Phi net_bps
    let d_saved := d_amort - l_E
    let dR_net  := calcNetRewardGen B Phi d_saved net_bps
    dR_net ≤ C_burn := by
  intro d_amort d_saved dR_net
  have h_saved_le : d_saved ≤ (10000 * C_burn * Phi) / (net_bps * B) := by
    have h1 : d_saved ≤ d_amort := Nat.sub_le d_amort l_E
    have h2 : d_amort ≤ (10000 * C_burn * Phi) / (net_bps * B) := Nat.min_le_right _ _
    exact Nat.le_trans h1 h2
  have h_mul1 : d_saved * (net_bps * B) ≤ (10000 * C_burn * Phi) := by
    have h_m := Nat.mul_le_mul_right (net_bps * B) h_saved_le
    exact Nat.le_trans h_m (Nat.div_mul_le_self (10000 * C_burn * Phi) (net_bps * B))
  have h_escrow_bound : net_bps * escrowAlloc B Phi d_saved ≤ 10000 * C_burn := by
    unfold escrowAlloc
    have h_e : (B * d_saved) / Phi * Phi ≤ B * d_saved := Nat.div_mul_le_self (B * d_saved) Phi
    have h_e2 : net_bps * ((B * d_saved) / Phi) * Phi ≤ net_bps * (B * d_saved) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left net_bps h_e
    have h_comm : net_bps * (B * d_saved) = d_saved * (net_bps * B) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (net_bps * B) d_saved]
    rw [h_comm] at h_e2
    have h_e3 : net_bps * ((B * d_saved) / Phi) * Phi ≤ 10000 * C_burn * Phi :=
      Nat.le_trans h_e2 h_mul1
    have h_div := div_le_div_right (c := Phi) h_e3
    rw [Nat.mul_div_cancel _ h_Phi, Nat.mul_div_cancel _ h_Phi] at h_div
    exact h_div
  dsimp [dR_net, calcNetRewardGen]
  have h_final := div_le_div_right (c := 10000) h_escrow_bound
  rw [Nat.mul_div_cancel_left C_burn (by decide : 0 < 10000)] at h_final
  exact h_final

theorem rbf_lifetime_cap (D0 paid D R_net : Nat) (h : paid + D = D0) :
    let R_repay := Nat.min R_net D
    (paid + R_repay) + (D - R_repay) = D0 ∧ paid + R_repay ≤ D0 := by
  intro R_repay
  have h_le : R_repay ≤ D := Nat.min_le_right R_net D
  omega

theorem rbf_prorata_le_list (R_repay : Nat) (ds : List Nat) :
    sumDiv ds.sum (ds.map (fun d => R_repay * d)) ≤ R_repay := by
  by_cases h0 : ds.sum = 0
  · rw [h0]
    have h_zero : ∀ l : List Nat, sumDiv 0 l = 0 := by
      intro l; induction l with
      | nil => rfl
      | cons a t ih => simp [sumDiv, Nat.div_zero, ih]
    rw [h_zero]; exact Nat.zero_le _
  · have h_pos : 0 < ds.sum := Nat.pos_of_ne_zero h0
    have h_le := sumDiv_le ds.sum (ds.map (fun d => R_repay * d))
    have h_map_sum : ∀ l : List Nat, (l.map (fun d => R_repay * d)).sum = R_repay * l.sum := by
      intro l; induction l with
      | nil => simp
      | cons a t ih => simp [List.sum_cons, ih, Nat.mul_add]
    rw [h_map_sum, Nat.mul_div_cancel R_repay h_pos] at h_le
    exact h_le

def calcTEff (t_req N_ep : Nat) : Nat :=
  N_ep * ((t_req + 3 * N_ep - 1) / N_ep)

theorem tEff_bounds (t_req N_ep : Nat) (h_ep : N_ep > 0) :
    t_req + 2 * N_ep ≤ calcTEff t_req N_ep ∧
    calcTEff t_req N_ep < t_req + 3 * N_ep := by
  unfold calcTEff
  have h_mod : (t_req + 3 * N_ep - 1) % N_ep < N_ep := Nat.mod_lt _ h_ep
  have h_dm  : N_ep * ((t_req + 3 * N_ep - 1) / N_ep) + (t_req + 3 * N_ep - 1) % N_ep =
               t_req + 3 * N_ep - 1 := Nat.div_add_mod (t_req + 3 * N_ep - 1) N_ep
  omega

structure SupplyState where
  wallets : Nat
  locked  : Nat
  burned  : Nat
  minted  : Nat

def SupplyInv (s : SupplyState) : Prop :=
  s.wallets + s.locked + s.burned = s.minted

def applyLedgerTx (s : SupplyState) (w_out w_in l_out l_in b_add m_add : Nat) : SupplyState :=
  { wallets := s.wallets - w_out + w_in
    locked  := s.locked  - l_out + l_in
    burned  := s.burned  + b_add
    minted  := s.minted  + m_add }

theorem global_supply_invariant_preserved
    (s : SupplyState) (w_out w_in l_out l_in b_add m_add : Nat)
    (h_inv   : SupplyInv s)
    (h_w_ok  : w_out ≤ s.wallets)
    (h_l_ok  : l_out ≤ s.locked)
    (h_tx_eq : w_out + l_out + m_add = w_in + l_in + b_add) :
    SupplyInv (applyLedgerTx s w_out w_in l_out l_in b_add m_add) := by
  unfold SupplyInv applyLedgerTx at *
  dsimp
  omega

structure DataState where
  B0         : Nat
  Phi0       : Nat
  Phi_best   : Nat
  d_init     : Nat
  d_abs      : Nat
  d_hold     : Nat
  d_settled  : Nat
  e_init     : Nat
  e_abs      : Nat
  e_hold     : Nat
  e_settled  : Nat
  B_rem      : Nat

structure DataInv (s : DataState) : Prop where
  phi0_pos   : s.Phi0 > 0
  best_ge_1  : s.Phi_best ≥ 1
  front_eq   : s.Phi_best + (s.d_init + s.d_abs) + s.d_hold + s.d_settled = s.Phi0
  init_bound : s.e_init    ≤ escrowAlloc s.B0 s.Phi0 s.d_init
  abs_bound  : s.e_abs     ≤ escrowAlloc s.B0 s.Phi0 s.d_abs
  hold_bound : s.e_hold    ≤ escrowAlloc s.B0 s.Phi0 s.d_hold
  set_bound  : s.e_settled ≤ escrowAlloc s.B0 s.Phi0 s.d_settled
  pool_cons  : s.B_rem + s.e_hold + (s.e_init + s.e_abs) + s.e_settled = s.B0

theorem DataInv.pool_lower (s : DataState) (h : DataInv s) :
    s.B_rem ≥ ceilDiv (s.B0 * s.Phi_best) s.Phi0 := by
  have h_act : s.e_init + s.e_abs ≤ escrowAlloc s.B0 s.Phi0 (s.d_init + s.d_abs) :=
    Nat.le_trans (Nat.add_le_add h.init_bound h.abs_bound)
      (escrowAlloc_superadd s.B0 s.Phi0 s.d_init s.d_abs)
  have h1 := Nat.le_trans (Nat.add_le_add h_act h.hold_bound)
    (escrowAlloc_superadd s.B0 s.Phi0 (s.d_init + s.d_abs) s.d_hold)
  have h2 := Nat.le_trans (Nat.add_le_add h1 h.set_bound)
    (escrowAlloc_superadd s.B0 s.Phi0 (s.d_init + s.d_abs + s.d_hold) s.d_settled)
  exact pool_lower_bound_ceil s.B0 s.Phi0 s.Phi_best
    ((s.d_init + s.d_abs) + s.d_hold + s.d_settled)
    ((s.e_init + s.e_abs) + s.e_hold + s.e_settled) s.B_rem h.phi0_pos
    (by have := h.front_eq; omega) h2 (by have := h.pool_cons; omega)

def stepAdopt (s : DataState) (Phi_new b_new : Nat) : DataState :=
  let d_new := s.Phi_best - Phi_new
  { s with
    Phi_best := Phi_new
    d_init   := s.d_init + d_new
    e_init   := s.e_init + b_new
    B_rem    := s.B_rem - b_new }

theorem stepAdopt_preserves_inv (s : DataState) (Phi_new b_new : Nat)
    (h_inv   : DataInv s)
    (h_pos   : Phi_new ≥ 1)
    (h_imp   : Phi_new < s.Phi_best)
    (h_b_bnd : b_new ≤ escrowAlloc s.B0 s.Phi0 (s.Phi_best - Phi_new)) :
    DataInv (stepAdopt s Phi_new b_new) := by
  have hPhi0  := h_inv.phi0_pos
  have hFront := h_inv.front_eq
  have hInit  := h_inv.init_bound
  have hAbs   := h_inv.abs_bound
  have hHold  := h_inv.hold_bound
  have hSet   := h_inv.set_bound
  have hCons  := h_inv.pool_cons
  have h_init_new : s.e_init + b_new ≤ escrowAlloc s.B0 s.Phi0 (s.d_init + (s.Phi_best - Phi_new)) := by
    have h1 := Nat.add_le_add hInit h_b_bnd
    exact Nat.le_trans h1 (escrowAlloc_superadd s.B0 s.Phi0 s.d_init (s.Phi_best - Phi_new))
  have h_act_new : (s.e_init + b_new) + s.e_abs ≤
      escrowAlloc s.B0 s.Phi0 ((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) :=
    Nat.le_trans (Nat.add_le_add h_init_new hAbs)
      (escrowAlloc_superadd s.B0 s.Phi0 (s.d_init + (s.Phi_best - Phi_new)) s.d_abs)
  have h_tot_escrow :
      ((s.e_init + b_new) + s.e_abs) + s.e_hold + s.e_settled ≤
      escrowAlloc s.B0 s.Phi0 (((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) + s.d_hold + s.d_settled) := by
    have h12 := Nat.le_trans (Nat.add_le_add h_act_new hHold)
      (escrowAlloc_superadd s.B0 s.Phi0 ((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) s.d_hold)
    exact Nat.le_trans (Nat.add_le_add h12 hSet)
      (escrowAlloc_superadd s.B0 s.Phi0 (((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) + s.d_hold) s.d_settled)
  have h_used_le : ((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) + s.d_hold + s.d_settled ≤ s.Phi0 := by omega
  have h_alloc_le_B0 :
      escrowAlloc s.B0 s.Phi0 (((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) + s.d_hold + s.d_settled) ≤ s.B0 := by
    have h_m := escrowAlloc_mono s.B0 s.Phi0 _ s.Phi0 h_used_le
    unfold escrowAlloc at h_m
    rw [Nat.mul_div_cancel s.B0 hPhi0] at h_m
    exact h_m
  refine {
    phi0_pos   := hPhi0
    best_ge_1  := h_pos
    front_eq   := by show Phi_new + ((s.d_init + (s.Phi_best - Phi_new)) + s.d_abs) + s.d_hold + s.d_settled = s.Phi0; omega
    init_bound := h_init_new
    abs_bound  := hAbs
    hold_bound := hHold
    set_bound  := hSet
    pool_cons  := by
      show (s.B_rem - b_new) + s.e_hold + ((s.e_init + b_new) + s.e_abs) + s.e_settled = s.B0
      omega
  }

def stepPunctureConcrete (s : DataState) (d_unroll : Nat) : DataState :=
  let d_total    := s.d_init + s.d_abs
  let d_rem      := d_total - d_unroll
  let d_rem_init := Nat.min s.d_init d_rem
  let d_rem_abs  := d_rem - d_rem_init
  let E_total    := s.e_init + s.e_abs
  let E_rem_i    := safeRemEscrow s.B0 s.Phi0 s.e_init s.d_init d_rem_init
  let E_rem_a    := safeRemEscrow s.B0 s.Phi0 s.e_abs  s.d_abs  d_rem_abs
  let E_rem      := E_rem_i + E_rem_a
  let E_unroll   := Nat.min (E_total - E_rem) (escrowAlloc s.B0 s.Phi0 d_unroll)
  let E_dust     := E_total - E_rem - E_unroll
  { s with
    d_init   := d_rem_init
    d_abs    := d_rem_abs
    d_hold   := s.d_hold + d_unroll
    e_init   := E_rem_i
    e_abs    := E_rem_a
    e_hold   := s.e_hold + E_unroll
    B_rem    := s.B_rem + E_dust }

theorem stepPuncture_concrete_preserves_inv (s : DataState) (d_unroll : Nat)
    (h_inv : DataInv s)
    (h_unr : d_unroll ≤ s.d_init + s.d_abs) :
    DataInv (stepPunctureConcrete s d_unroll) := by
  have hFront := h_inv.front_eq
  have hHold  := h_inv.hold_bound
  have hCons  := h_inv.pool_cons
  let d_total    := s.d_init + s.d_abs
  let d_rem      := d_total - d_unroll
  let d_rem_init := Nat.min s.d_init d_rem
  let d_rem_abs  := d_rem - d_rem_init
  have h_rem_i : d_rem_init ≤ s.d_init := Nat.min_le_left s.d_init d_rem
  have h_rem_a : d_rem_abs ≤ s.d_abs := by
    by_cases h : s.d_init ≤ d_rem
    · have hm : d_rem_init = s.d_init := Nat.min_eq_left h
      omega
    · have hm : d_rem_init = d_rem := Nat.min_eq_right (by omega)
      omega
  have h_split : d_rem_init + d_rem_abs + d_unroll = s.d_init + s.d_abs := by
    have h_le : d_rem_init ≤ d_rem := Nat.min_le_right s.d_init d_rem
    omega
  have h_bridge := tranche_unroll_conserves_and_bounds
    s.B0 s.Phi0 s.e_init s.e_abs s.d_init s.d_abs d_rem_init d_rem_abs d_unroll h_rem_i h_rem_a
  have hi   := h_bridge.1
  have ha   := h_bridge.2.1
  have hu   := h_bridge.2.2.1
  have h_le := h_bridge.2.2.2.1
  have h_eq := h_bridge.2.2.2.2
  have h_hold_new :
      s.e_hold + Nat.min ((s.e_init + s.e_abs) - (safeRemEscrow s.B0 s.Phi0 s.e_init s.d_init d_rem_init +
        safeRemEscrow s.B0 s.Phi0 s.e_abs s.d_abs d_rem_abs)) (escrowAlloc s.B0 s.Phi0 d_unroll) ≤
      escrowAlloc s.B0 s.Phi0 (s.d_hold + d_unroll) := by
    have h1 := Nat.add_le_add hHold hu
    exact Nat.le_trans h1 (escrowAlloc_superadd s.B0 s.Phi0 s.d_hold d_unroll)
  refine {
    phi0_pos   := h_inv.phi0_pos
    best_ge_1  := h_inv.best_ge_1
    front_eq   := by show s.Phi_best + (d_rem_init + d_rem_abs) + (s.d_hold + d_unroll) + s.d_settled = s.Phi0; omega
    init_bound := hi
    abs_bound  := ha
    hold_bound := h_hold_new
    set_bound  := h_inv.set_bound
    pool_cons  := by
      simp only [stepPunctureConcrete]
      simp only [d_total, d_rem, d_rem_init, d_rem_abs] at h_eq ⊢
      omega
  }

def stepHoldExpire (s : DataState) (d_abs_add : Nat) : DataState :=
  let d_rewind  := s.d_hold - d_abs_add
  let e_abs_add := if s.d_hold = 0 then 0
                   else Nat.min ((s.e_hold * d_abs_add) / s.d_hold) (escrowAlloc s.B0 s.Phi0 d_abs_add)
  let e_ret     := s.e_hold - e_abs_add
  { s with
    Phi_best := s.Phi_best + d_rewind
    d_abs    := s.d_abs + d_abs_add
    d_hold   := 0
    e_abs    := s.e_abs + e_abs_add
    e_hold   := 0
    B_rem    := s.B_rem + e_ret }

theorem stepHoldExpire_concrete_preserves_inv (s : DataState) (d_abs_add : Nat)
    (h_inv : DataInv s)
    (h_le  : d_abs_add ≤ s.d_hold) :
    DataInv (stepHoldExpire s d_abs_add) := by
  have hBest1 := h_inv.best_ge_1
  have hFront := h_inv.front_eq
  have hAbs   := h_inv.abs_bound
  have hCons  := h_inv.pool_cons
  let e_abs_add := if s.d_hold = 0 then 0
                   else Nat.min ((s.e_hold * d_abs_add) / s.d_hold) (escrowAlloc s.B0 s.Phi0 d_abs_add)
  have h_ea_bnd : e_abs_add ≤ escrowAlloc s.B0 s.Phi0 d_abs_add := by
    dsimp [e_abs_add]; split
    · exact Nat.zero_le _
    · exact Nat.min_le_right _ _
  have h_ea_le_hold : e_abs_add ≤ s.e_hold := by
    dsimp [e_abs_add]; split
    · exact Nat.zero_le _
    · next h_ne =>
      have h_pos : 0 < s.d_hold := Nat.pos_of_ne_zero h_ne
      have h_mul : s.e_hold * d_abs_add ≤ s.e_hold * s.d_hold := Nat.mul_le_mul_left s.e_hold h_le
      have h_d := div_le_div_right (c := s.d_hold) h_mul
      rw [Nat.mul_div_cancel s.e_hold h_pos] at h_d
      exact Nat.le_trans (Nat.min_le_left _ _) h_d
  have h_abs_new : s.e_abs + e_abs_add ≤ escrowAlloc s.B0 s.Phi0 (s.d_abs + d_abs_add) :=
    Nat.le_trans (Nat.add_le_add hAbs h_ea_bnd)
      (escrowAlloc_superadd s.B0 s.Phi0 s.d_abs d_abs_add)
  refine {
    phi0_pos   := h_inv.phi0_pos
    best_ge_1  := by show s.Phi_best + (s.d_hold - d_abs_add) ≥ 1; omega
    front_eq   := by show (s.Phi_best + (s.d_hold - d_abs_add)) + (s.d_init + (s.d_abs + d_abs_add)) + 0 + s.d_settled = s.Phi0; omega
    init_bound := h_inv.init_bound
    abs_bound  := h_abs_new
    hold_bound := Nat.zero_le _
    set_bound  := h_inv.set_bound
    pool_cons  := by
      show (s.B_rem + (s.e_hold - e_abs_add)) + 0 + (s.e_init + (s.e_abs + e_abs_add)) + s.e_settled = s.B0
      omega
  }

def stepSettleInit (s : DataState) : DataState :=
  { s with
    d_init    := 0
    d_settled := s.d_settled + s.d_init
    e_init    := 0
    e_settled := s.e_settled + s.e_init }

theorem stepSettleInit_preserves_inv (s : DataState) (h_inv : DataInv s) :
    DataInv (stepSettleInit s) := by
  have hFront := h_inv.front_eq
  have hInit  := h_inv.init_bound
  have hSet   := h_inv.set_bound
  have hCons  := h_inv.pool_cons
  have h_set_new : s.e_settled + s.e_init ≤ escrowAlloc s.B0 s.Phi0 (s.d_settled + s.d_init) :=
    Nat.le_trans (Nat.add_le_add hSet hInit)
      (escrowAlloc_superadd s.B0 s.Phi0 s.d_settled s.d_init)
  refine {
    phi0_pos   := h_inv.phi0_pos
    best_ge_1  := h_inv.best_ge_1
    front_eq   := by show s.Phi_best + (0 + s.d_abs) + s.d_hold + (s.d_settled + s.d_init) = s.Phi0; omega
    init_bound := Nat.zero_le _
    abs_bound  := h_inv.abs_bound
    hold_bound := h_inv.hold_bound
    set_bound  := h_set_new
    pool_cons  := by show s.B_rem + s.e_hold + (0 + s.e_abs) + (s.e_settled + s.e_init) = s.B0; omega
  }

def stepSettleAbs (s : DataState) : DataState :=
  { s with
    d_abs     := 0
    d_settled := s.d_settled + s.d_abs
    e_abs     := 0
    e_settled := s.e_settled + s.e_abs }

theorem stepSettleAbs_preserves_inv (s : DataState) (h_inv : DataInv s) :
    DataInv (stepSettleAbs s) := by
  have hFront := h_inv.front_eq
  have hAbs   := h_inv.abs_bound
  have hSet   := h_inv.set_bound
  have hCons  := h_inv.pool_cons
  have h_set_new : s.e_settled + s.e_abs ≤ escrowAlloc s.B0 s.Phi0 (s.d_settled + s.d_abs) :=
    Nat.le_trans (Nat.add_le_add hSet hAbs)
      (escrowAlloc_superadd s.B0 s.Phi0 s.d_settled s.d_abs)
  refine {
    phi0_pos   := h_inv.phi0_pos
    best_ge_1  := h_inv.best_ge_1
    front_eq   := by show s.Phi_best + (s.d_init + 0) + s.d_hold + (s.d_settled + s.d_abs) = s.Phi0; omega
    init_bound := h_inv.init_bound
    abs_bound  := Nat.zero_le _
    hold_bound := h_inv.hold_bound
    set_bound  := h_set_new
    pool_cons  := by show s.B_rem + s.e_hold + (s.e_init + 0) + (s.e_settled + s.e_abs) = s.B0; omega
  }


def allocStage1Single (saved_marg sigma_marg d_tr : Nat) : Nat :=
  if sigma_marg = 0 then 0
  else (saved_marg * Nat.min sigma_marg d_tr) / sigma_marg

theorem stage1_single_bounds
    (Saved S0 sigma_marg d_tr d_amort : Nat)
    (h_saved  : Saved ≤ d_amort)
    (h_s0     : S0 ≤ d_amort) :
    let saved_marg := Saved - S0
    let a_u        := allocStage1Single saved_marg sigma_marg d_tr
    let S_new      := S0 + a_u
    a_u ≤ saved_marg ∧ S_new ≤ Nat.max S0 Saved ∧ S_new ≤ d_amort := by
  intro saved_marg a_u S_new
  have h_a_le : a_u ≤ saved_marg := by
    dsimp [a_u, allocStage1Single]
    split
    · exact Nat.zero_le _
    · next h_ne =>
      have h_pos : 0 < sigma_marg := Nat.pos_of_ne_zero h_ne
      have h_min : Nat.min sigma_marg d_tr ≤ sigma_marg := Nat.min_le_left _ _
      have h_mul : saved_marg * Nat.min sigma_marg d_tr ≤ saved_marg * sigma_marg :=
        Nat.mul_le_mul_left saved_marg h_min
      have h_d := div_le_div_right (c := sigma_marg) h_mul
      rw [Nat.mul_div_cancel saved_marg h_pos] at h_d
      exact h_d
  have h_snew_max : S_new ≤ Nat.max S0 Saved := by
    by_cases h : S0 ≤ Saved
    · have hm : Nat.max S0 Saved = Saved := Nat.max_eq_right h
      omega
    · have hm : Nat.max S0 Saved = S0 := Nat.max_eq_left (by omega)
      omega
  have h_max_amort : Nat.max S0 Saved ≤ d_amort := by
    by_cases h : S0 ≤ Saved
    · have hm : Nat.max S0 Saved = Saved := Nat.max_eq_right h
      omega
    · have hm : Nat.max S0 Saved = S0 := Nat.max_eq_left (by omega)
      omega
  exact ⟨h_a_le, h_snew_max, Nat.le_trans h_snew_max h_max_amort⟩

theorem stage1_list_sum_le_delta (margs : List Nat) (d_tr : Nat) :
    let sig := margs.sum
    let c   := Nat.min sig d_tr
    sumDiv sig (margs.map (fun m => m * c)) ≤ d_tr := by
  intro sig c
  by_cases h0 : sig = 0
  · have h_zero : ∀ l : List Nat, sumDiv 0 l = 0 := by
      intro l; induction l with
      | nil => rfl
      | cons a t ih => simp [sumDiv, Nat.div_zero, ih]
    rw [h0, h_zero]
    exact Nat.zero_le _
  · have h_pos : 0 < sig := Nat.pos_of_ne_zero h0
    have h_le := sumDiv_le sig (margs.map (fun m => m * c))
    have h_map_sum : ∀ l : List Nat, (l.map (fun m => m * c)).sum = l.sum * c := by
      intro l; induction l with
      | nil => simp
      | cons a t ih => simp [List.sum_cons, ih, Nat.add_mul]
    rw [h_map_sum] at h_le
    have h_eq : (margs.sum * c) / sig = c := by
      dsimp [sig] at h_pos ⊢
      rw [Nat.mul_comm]; exact Nat.mul_div_cancel c h_pos
    rw [h_eq] at h_le
    exact Nat.le_trans h_le (Nat.min_le_right sig d_tr)

theorem puncture_slot_scale_valid
    (xs : List Nat) (d_tr d_rem S_paid x : Nat)
    (h_d_pos : d_tr > 0)
    (h_rem   : d_rem ≤ d_tr)
    (h_sum   : xs.sum ≤ d_tr) :
    let x_new      := (x * d_rem) / d_tr
    let S_after    := S_paid - (x - x_new)
    sumDiv d_tr (xs.map (fun a => a * d_rem)) ≤ d_rem ∧
    x_new ≤ x ∧
    S_after ≤ S_paid := by
  intro x_new S_after
  have h_le1 := sumDiv_le d_tr (xs.map (fun a => a * d_rem))
  have h_map_sum : ∀ l : List Nat, (l.map (fun a => a * d_rem)).sum = l.sum * d_rem := by
    intro l; induction l with
    | nil => simp
    | cons a t ih => simp [List.sum_cons, ih, Nat.add_mul]
  rw [h_map_sum] at h_le1
  have h_mul_sum : xs.sum * d_rem ≤ d_tr * d_rem := Nat.mul_le_mul_right d_rem h_sum
  have h_div_sum := div_le_div_right (c := d_tr) h_mul_sum
  rw [Nat.mul_div_cancel_left d_rem h_d_pos] at h_div_sum
  have h_x_le : x_new ≤ x := by
    dsimp [x_new]
    have hm : x * d_rem ≤ x * d_tr := Nat.mul_le_mul_left x h_rem
    have hd := div_le_div_right (c := d_tr) hm
    rw [Nat.mul_div_cancel x h_d_pos] at hd
    exact hd
  exact ⟨Nat.le_trans h_le1 h_div_sum, h_x_le, Nat.sub_le _ _⟩

structure Tranche where
  d : Nat
  e : Nat

def sumTrancheD : List Tranche → Nat
  | [] => 0
  | tr :: tl => tr.d + sumTrancheD tl

def sumTrancheE : List Tranche → Nat
  | [] => 0
  | tr :: tl => tr.e + sumTrancheE tl

def AllTranchesBounded (B0 Phi0 : Nat) : List Tranche → Prop
  | [] => True
  | tr :: tl => tr.e ≤ escrowAlloc B0 Phi0 tr.d ∧ AllTranchesBounded B0 Phi0 tl

theorem allTranches_sum_bounded (B0 Phi0 : Nat) (trs : List Tranche)
    (h : AllTranchesBounded B0 Phi0 trs) :
    sumTrancheE trs ≤ escrowAlloc B0 Phi0 (sumTrancheD trs) := by
  induction trs with
  | nil => simp [sumTrancheE, sumTrancheD, escrowAlloc]
  | cons tr tl ih =>
    simp only [sumTrancheE, sumTrancheD]
    have h_hd := h.1
    have h_tl := ih h.2
    have h_add := Nat.add_le_add h_hd h_tl
    exact Nat.le_trans h_add (escrowAlloc_superadd B0 Phi0 tr.d (sumTrancheD tl))

structure ListDataState where
  B0         : Nat
  Phi0       : Nat
  Phi_best   : Nat
  tranches   : List Tranche
  d_hold     : Nat
  d_settled  : Nat
  e_hold     : Nat
  e_settled  : Nat
  B_rem      : Nat

structure ListDataInv (s : ListDataState) : Prop where
  phi0_pos   : s.Phi0 > 0
  best_ge_1  : s.Phi_best ≥ 1
  front_eq   : s.Phi_best + sumTrancheD s.tranches + s.d_hold + s.d_settled = s.Phi0
  tr_bounds  : AllTranchesBounded s.B0 s.Phi0 s.tranches
  hold_bound : s.e_hold    ≤ escrowAlloc s.B0 s.Phi0 s.d_hold
  set_bound  : s.e_settled ≤ escrowAlloc s.B0 s.Phi0 s.d_settled
  pool_cons  : s.B_rem + s.e_hold + sumTrancheE s.tranches + s.e_settled = s.B0

def stepAdoptList (s : ListDataState) (Phi_new b_new : Nat) : ListDataState :=
  let d_new := s.Phi_best - Phi_new
  let tr_new : Tranche := { d := d_new, e := b_new }
  { s with
    Phi_best := Phi_new
    tranches := tr_new :: s.tranches
    B_rem    := s.B_rem - b_new }

theorem stepAdoptList_preserves_inv (s : ListDataState) (Phi_new b_new : Nat)
    (h_inv   : ListDataInv s)
    (h_pos   : Phi_new ≥ 1)
    (h_imp   : Phi_new < s.Phi_best)
    (h_b_bnd : b_new ≤ escrowAlloc s.B0 s.Phi0 (s.Phi_best - Phi_new)) :
    ListDataInv (stepAdoptList s Phi_new b_new) := by
  have hPhi0  := h_inv.phi0_pos
  have hFront := h_inv.front_eq
  have hTrs   := h_inv.tr_bounds
  have hHold  := h_inv.hold_bound
  have hSet   := h_inv.set_bound
  have hCons  := h_inv.pool_cons
  have h_tr_new : AllTranchesBounded s.B0 s.Phi0 ({ d := s.Phi_best - Phi_new, e := b_new } :: s.tranches) :=
    ⟨h_b_bnd, hTrs⟩
  have h_act_sum := allTranches_sum_bounded s.B0 s.Phi0
    ({ d := s.Phi_best - Phi_new, e := b_new } :: s.tranches) h_tr_new
  have h12 := Nat.le_trans (Nat.add_le_add h_act_sum hHold)
    (escrowAlloc_superadd s.B0 s.Phi0 (sumTrancheD ({ d := s.Phi_best - Phi_new, e := b_new } :: s.tranches)) s.d_hold)
  have h123 := Nat.le_trans (Nat.add_le_add h12 hSet)
    (escrowAlloc_superadd s.B0 s.Phi0
      (sumTrancheD ({ d := s.Phi_best - Phi_new, e := b_new } :: s.tranches) + s.d_hold) s.d_settled)
  simp only [sumTrancheD, sumTrancheE] at h123
  have h_used_le : ((s.Phi_best - Phi_new) + sumTrancheD s.tranches + s.d_hold) + s.d_settled ≤ s.Phi0 := by omega
  have h_alloc_B0 :
      escrowAlloc s.B0 s.Phi0 (((s.Phi_best - Phi_new) + sumTrancheD s.tranches + s.d_hold) + s.d_settled) ≤ s.B0 := by
    have hm := escrowAlloc_mono s.B0 s.Phi0 _ s.Phi0 h_used_le
    unfold escrowAlloc at hm
    rw [Nat.mul_div_cancel s.B0 hPhi0] at hm
    exact hm
  refine {
    phi0_pos   := hPhi0
    best_ge_1  := h_pos
    front_eq   := by simp only [stepAdoptList, sumTrancheD]; omega
    tr_bounds  := h_tr_new
    hold_bound := hHold
    set_bound  := hSet
    pool_cons  := by simp only [stepAdoptList, sumTrancheE]; omega
  }

def stepSettleHead (s : ListDataState) : ListDataState :=
  match s.tranches with
  | [] => s
  | tr :: tl =>
    { s with
      tranches  := tl
      d_settled := s.d_settled + tr.d
      e_settled := s.e_settled + tr.e }

theorem stepSettleHead_preserves_inv (s : ListDataState) (h_inv : ListDataInv s) :
    ListDataInv (stepSettleHead s) := by
  unfold stepSettleHead
  cases h_eq : s.tranches with
  | nil => exact h_inv
  | cons tr tl =>
    have hFront := h_inv.front_eq
    have hTrs   := h_inv.tr_bounds
    have hSet   := h_inv.set_bound
    have hCons  := h_inv.pool_cons
    rw [h_eq] at hFront hTrs hCons
    simp only [sumTrancheD, sumTrancheE, AllTranchesBounded] at hFront hTrs hCons
    have h_set_new : s.e_settled + tr.e ≤ escrowAlloc s.B0 s.Phi0 (s.d_settled + tr.d) :=
      Nat.le_trans (Nat.add_le_add hSet hTrs.1) (escrowAlloc_superadd s.B0 s.Phi0 s.d_settled tr.d)
    refine {
      phi0_pos   := h_inv.phi0_pos
      best_ge_1  := h_inv.best_ge_1
      front_eq   := by dsimp; omega
      tr_bounds  := hTrs.2
      hold_bound := h_inv.hold_bound
      set_bound  := h_set_new
      pool_cons  := by dsimp; omega
    }

theorem branch01_T0_preserves (s : SupplyState) (B0 S_k burn_da fee : Nat)
    (h_inv : SupplyInv s) (h_w : B0 + S_k + burn_da + fee ≤ s.wallets) :
    SupplyInv (applyLedgerTx s (B0 + S_k + burn_da + fee) fee 0 (B0 + S_k) burn_da 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w (Nat.zero_le _) (by omega)

theorem branch02_commit_preserves (s : SupplyState) (S_c g_tx : Nat)
    (h_inv : SupplyInv s) (h_w : S_c + g_tx ≤ s.wallets) :
    SupplyInv (applyLedgerTx s (S_c + g_tx) g_tx 0 S_c 0 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w (Nat.zero_le _) (by omega)

theorem branch03_adopt_preserves (s : SupplyState) (S_st burn_da B_am fee : Nat)
    (h_inv : SupplyInv s) (h_w : S_st + burn_da + B_am + fee ≤ s.wallets) :
    SupplyInv (applyLedgerTx s (S_st + burn_da + B_am + fee) fee 0 S_st (burn_da + B_am) 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w (Nat.zero_le _) (by omega)

theorem branch04_reject_preserves (s : SupplyState) (S_c S_st burn_da fee : Nat)
    (h_inv : SupplyInv s) (h_w : S_st + burn_da + fee ≤ s.wallets) (h_l : S_c ≤ s.locked) :
    SupplyInv (applyLedgerTx s (S_st + burn_da + fee) (S_c + S_st + fee) S_c 0 burn_da 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w h_l (by omega)

theorem branch05_unrevealed_preserves (s : SupplyState) (S_c : Nat)
    (h_inv : SupplyInv s) (h_l : S_c ≤ s.locked) :
    let ref := (3000 * S_c) / 10000
    SupplyInv (applyLedgerTx s 0 ref S_c 0 (S_c - ref) 0) := by
  intro ref
  have h_le : ref ≤ S_c := mul_bps_div_le 3000 S_c (by decide)
  exact global_supply_invariant_preserved s _ _ _ _ _ _ h_inv (Nat.zero_le _) h_l (by omega)

theorem branch06_07_puncture_preserves (s : SupplyState) (S_cut S_pay S_burn fee : Nat)
    (h_inv : SupplyInv s) (h_w : fee ≤ s.wallets) (h_l : S_cut ≤ s.locked)
    (h_split : S_pay + S_burn = S_cut) :
    SupplyInv (applyLedgerTx s fee (S_pay + fee) S_cut 0 S_burn 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w h_l (by omega)

theorem branch08a_uw_topup_preserves (s : SupplyState) (dS_uw g_tx : Nat)
    (h_inv : SupplyInv s) (h_w : dS_uw + g_tx ≤ s.wallets) :
    SupplyInv (applyLedgerTx s (dS_uw + g_tx) g_tx 0 dS_uw 0 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w (Nat.zero_le _) (by omega)

theorem branch08b_hold_expire_preserves (s : SupplyState) (dS_excess : Nat)
    (h_inv : SupplyInv s) (h_l : dS_excess ≤ s.locked) :
    SupplyInv (applyLedgerTx s 0 dS_excess dS_excess 0 0 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv (Nat.zero_le _) h_l (by omega)

theorem branch09_settle_preserves (s : SupplyState) (E_tr S_unlock E_burn payouts : Nat)
    (h_inv : SupplyInv s) (h_l : E_tr + S_unlock ≤ s.locked)
    (h_split : E_burn + payouts = E_tr) :
    SupplyInv (applyLedgerTx s 0 (payouts + S_unlock) (E_tr + S_unlock) 0 E_burn 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv (Nat.zero_le _) h_l (by omega)

theorem branch10_close_ok_preserves (s : SupplyState) (B_rem S_k : Nat)
    (h_inv : SupplyInv s) (h_l : B_rem + S_k ≤ s.locked) :
    SupplyInv (applyLedgerTx s 0 (B_rem + S_k) (B_rem + S_k) 0 0 0) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv (Nat.zero_le _) h_l (by omega)

theorem branch11_close_pen_preserves (s : SupplyState) (B_rem S_k : Nat)
    (h_inv : SupplyInv s) (h_l : B_rem + S_k ≤ s.locked) :
    let ref := (3000 * S_k) / 10000
    SupplyInv (applyLedgerTx s 0 (B_rem + ref) (B_rem + S_k) 0 (S_k - ref) 0) := by
  intro ref
  have h_le : ref ≤ S_k := mul_bps_div_le 3000 S_k (by decide)
  exact global_supply_invariant_preserved s _ _ _ _ _ _ h_inv (Nat.zero_le _) h_l (by omega)

theorem branch12_to_15_preserves (s : SupplyState) (S_ lock_out b_burn m_mint fee : Nat)
    (h_inv : SupplyInv s) (h_w : S_ + b_burn + fee ≤ s.wallets) (h_l : lock_out ≤ s.locked) :
    SupplyInv (applyLedgerTx s (S_ + b_burn + fee) (lock_out + m_mint + fee) lock_out S_ b_burn m_mint) :=
  global_supply_invariant_preserved s _ _ _ _ _ _ h_inv h_w h_l (by omega)


/-- P1 の対称解放の算術的正しさ: 派生公理 u の S_paid = base + xs + xu から (δs+δu) を引くと
    縮小後の生存予約 base + xs' + xu' にちょうど一致し、漏れも過剰解放もない -/
theorem release_symmetric (base xs xu r d : Nat) (hd : d > 0) (hr : r ≤ d) :
    (base + xs + xu) - ((xs - (xs * r) / d) + (xu - (xu * r) / d))
      = base + (xs * r) / d + (xu * r) / d := by
  have h1 : (xs * r) / d ≤ xs := by
    have hm : xs * r ≤ xs * d := Nat.mul_le_mul_left xs hr
    have hq := div_le_div_right (c := d) hm
    rw [Nat.mul_div_cancel xs hd] at hq
    exact hq
  have h2 : (xu * r) / d ≤ xu := by
    have hm : xu * r ≤ xu * d := Nat.mul_le_mul_left xu hr
    have hq := div_le_div_right (c := d) hm
    rw [Nat.mul_div_cancel xu hd] at hq
    exact hq
  generalize (xs * r) / d = p at h1 ⊢
  generalize (xu * r) / d = q at h2 ⊢
  omega

/-- v15 の旧規則（u からは δxu のみ解放）は漏れる: xs' < xs のとき残留が生じる -/
theorem old_rule_leaks :
    let base := 0; let xs := 10; let xu := 10; let r := 1; let d := 2
    (base + xs + xu) - ((xu - (xu * r) / d)) ≠ base + (xs * r) / d + (xu * r) / d := by decide

/-! ### Part 10: M1 Debt-Following Waterfall & Class-III Game-Theoretic Equilibrium Theorems (Theorems 49–53) -/

/-- 【Theorem 49: M1 Self-Reduction RBF Protection Waterfall】
    派生公理 u から根公理 s へ振り替えられたスロット x_{u→s} のロイヤリティ R_x について、
    アンカー還流 R_anchor 控除後の R_net から、第1優先で派生公理 u の未償還 RBF 債務 D_u を返済 (paid_u) し、
    第2優先で根公理 s の RBF 債務 D_s を返済 (paid_s) し、残余から辞書配当 div_s と Owner 残余を支払うとき、
    u の RBF 支援者は自己宛て T6 還元によって1単位も希釈されず、かつ完全保存則が成立する。 -/
theorem m1_redirect_rbf_priority_conserves
    (R_x beta_D_bps D_u D_s div_s : Nat)
    (h_beta : beta_D_bps ≤ 10000)
    (h_div  : div_s ≤ (R_x - (beta_D_bps * R_x) / 10000) -
              Nat.min (R_x - (beta_D_bps * R_x) / 10000) D_u -
              Nat.min ((R_x - (beta_D_bps * R_x) / 10000) - Nat.min (R_x - (beta_D_bps * R_x) / 10000) D_u) D_s) :
    let R_anchor  := (beta_D_bps * R_x) / 10000
    let R_net     := R_x - R_anchor
    let paid_u    := Nat.min R_net D_u
    let R_after_u := R_net - paid_u
    let paid_s    := Nat.min R_after_u D_s
    let R_rem     := R_after_u - paid_s
    let R_owner   := R_rem - div_s
    paid_u = Nat.min R_net D_u ∧
    R_anchor + paid_u + paid_s + div_s + R_owner = R_x := by
  intro R_anchor R_net paid_u R_after_u paid_s R_rem R_owner
  have h_anc : R_anchor ≤ R_x := mul_bps_div_le beta_D_bps R_x h_beta
  have h_pu  : paid_u ≤ R_net := Nat.min_le_left R_net D_u
  have h_ps  : paid_s ≤ R_after_u := Nat.min_le_left R_after_u D_s
  constructor
  · rfl
  · show R_anchor + paid_u + paid_s + div_s + (R_x - R_anchor - paid_u - paid_s - div_s) = R_x
    have h_div' : div_s ≤ R_net - paid_u - paid_s := h_div
    have h_ps' : paid_s ≤ R_net - paid_u := h_ps
    have h_pu' : paid_u ≤ R_net := h_pu
    have h_rn : R_net = R_x - R_anchor := rfl
    omega

/-- 【Theorem 50: Strict Dominance of Direct Submission over Single-Dataset Pre-Embedding】
    単一データ D_k において、事前埋め込み戦略の純受取増分 ΔR_net は、
    DA登録焼却費 burn_da + ガス代 g_tx > 0 の下で総コスト C_burn + burn_da + g_tx を厳密に下回る。 -/
theorem game_pre_embedding_strictly_dominated
    (L C_burn B Phi l_E net_bps burn_da g_tx : Nat)
    (h_Phi  : Phi > 0)
    (h_cost : burn_da + g_tx > 0) :
    let d_amort := calcAmortGen L C_burn B Phi net_bps
    let d_saved := d_amort - l_E
    let dR_net  := calcNetRewardGen B Phi d_saved net_bps
    dR_net < C_burn + burn_da + g_tx := by
  intro d_amort d_saved dR_net
  have h_le := single_data_pre_embedding_unprofitable L C_burn B Phi l_E net_bps h_Phi
  dsimp [d_amort, d_saved, dR_net] at h_le ⊢
  omega

/-- 【Theorem 51: Strict Dominance Against Temporary Reservation Griefing】
    パラメータ制約 κ_bps * σ_bps * 10000 > (10000 + Λ_bps) * γ_bps * (10000 - ε_bps) の下では、
    任意の正の偽トランシェ E_tr > 0 に対し、自己穿孔時の確定焼却損の分子は最大回避ロイヤリティの分子を厳密に上回る。 -/
theorem game_griefing_strictly_dominated
    (kappa_bps sigma_bps lambda_bps gamma_bps eps_bps E_tr : Nat)
    (h_E_pos : E_tr > 0)
    (h_param : kappa_bps * sigma_bps * 10000 > (10000 + lambda_bps) * (gamma_bps * (10000 - eps_bps))) :
    let loss_scaled  := (kappa_bps * sigma_bps * 10000) * E_tr
    let evade_scaled := ((10000 + lambda_bps) * (gamma_bps * (10000 - eps_bps))) * E_tr
    evade_scaled < loss_scaled := by
  intro loss_scaled evade_scaled
  exact Nat.mul_lt_mul_of_pos_right h_param h_E_pos

/-- 【Theorem 52: Subgame-Perfect Watchtower Deterrence Equilibrium】
    コミット時自己担保 S_c が R_gross ≤ (1 + Λ) * S_c (σ_col = 10000) を満たし、
    監視者検出確率 q_bps が (10000 - q_bps) * net_bps * (1 + Λ) ≤ q_bps * κ_bps を満たすとき、
    不正提出の期待利得項はスラッシュ純損失項以下となる。 -/
theorem game_watchtower_deterrence_equilibrium
    (q_bps net_bps kappa_bps lam R_gross S_c : Nat)
    (h_col  : R_gross ≤ (1 + lam) * S_c)
    (h_cond : (10000 - q_bps) * net_bps * (1 + lam) ≤ q_bps * kappa_bps) :
    ((10000 - q_bps) * net_bps) * R_gross ≤ (q_bps * kappa_bps) * S_c := by
  have h1 : ((10000 - q_bps) * net_bps) * R_gross ≤ ((10000 - q_bps) * net_bps) * ((1 + lam) * S_c) :=
    Nat.mul_le_mul_left _ h_col
  have h2 : ((10000 - q_bps) * net_bps) * ((1 + lam) * S_c) =
            ((10000 - q_bps) * net_bps * (1 + lam)) * S_c := by
    simp only [Nat.mul_assoc]
  rw [h2] at h1
  have h3 : ((10000 - q_bps) * net_bps * (1 + lam)) * S_c ≤ (q_bps * kappa_bps) * S_c :=
    Nat.mul_le_mul_right S_c h_cond
  exact Nat.le_trans h1 h3

/-- 【Theorem 53: Honest Citation Strict Dominance over Unamortized Inlining (with Royalty Deduction)】
    償却済み先祖 v_s をポインタ引用したときの純エスクロー増分 dE_net > 0 に対し、
    先祖ロイヤリティ率 γ_bps < 10000 (基準値 2000 bps = 20%) を支払った後の提案者の純手取り増分
    dE_net - ⌊(γ_bps * dE_net) / 10000⌋ は厳密に正 (> 0) となり、未償却インライン化 (増分 0) を厳密に支配する。 -/
theorem game_honest_citation_dominates_unamortized_clone
    (E_net_base dE_net gamma_bps : Nat)
    (h_gain  : dE_net > 0)
    (h_gamma : gamma_bps < 10000) :
    let royalty_inc  := (gamma_bps * dE_net) / 10000
    let proposer_inc := dE_net - royalty_inc
    royalty_inc < dE_net ∧ E_net_base < E_net_base + proposer_inc := by
  intro royalty_inc proposer_inc
  have h_lt : royalty_inc < dE_net := by
    dsimp [royalty_inc]
    have h_mul : gamma_bps * dE_net < 10000 * dE_net :=
      (Nat.mul_lt_mul_right h_gain).mpr h_gamma
    have h_div : (gamma_bps * dE_net) / 10000 * 10000 + (gamma_bps * dE_net) % 10000 = gamma_bps * dE_net := by
      rw [Nat.mul_comm _ 10000]
      exact Nat.div_add_mod (gamma_bps * dE_net) 10000
    omega
  omega

end ESM
