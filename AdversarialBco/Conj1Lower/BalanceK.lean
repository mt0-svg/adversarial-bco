/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Balance

@[expose] public section

/-!
# The balance on a body between two balls: Theorem RIPE-K and the lower bound on a body between two balls

The strategy of Theorem RIPE run
with the Lipschitz parameter `L_K = σ/R0` on a convex body `K` with `B(0, 1/2) ⊆ K ⊆ B(0, R0)`, `1 ≤ R0 ≤ d`. What
changes from Balance.lean: the floor is `wStar d k (σ/R0) g`, so `X_K = X/R0²` (`xCount_ripe_K`); the channel constant
reads the range `L_K (R0 + 1/2) + g` of the dent at a play of `K` (`chanBK`, at most `chanB σ g σ` for `R0 ≥ 1`); and
(R2) becomes (R2-K) `g ≤ k L_K/(40 d)` (`R2_ripe_K`). The count reads `R0` through (N1) (`log_x_ripe_ge_K`, from
`5 ln R0 ≤ Γ`, `log_R0_le`) and (N2) (`log_x_ripe_le_K`, `R0 ≥ 1`). Pure arithmetic on reals.
-/

open Finset

namespace AdversarialBco.Lower

/-- The channel bound (S1) on a body inside `B(0, R0)`: at a play of the body the signal of a cell takes its values in
an interval of length `L (R0 + 1/2) + g`, so its information is at most `(L (R0 + 1/2) + g)²/(8σ²)`. -/
noncomputable def chanBK (L R0 g σ : ℝ) : ℝ := (L * (R0 + 1 / 2) + g) ^ 2 / (8 * σ ^ 2)

theorem chanBK_le_chanB (σ R0 g : ℝ) (hσ : 0 < σ) (hR : 1 ≤ R0) (hg : 0 ≤ g) :
    chanBK (σ / R0) R0 g σ ≤ chanB σ g σ := by
  unfold chanBK chanB
  have hR0 : 0 < R0 := by linarith
  have h_denom : 0 ≤ 8 * σ ^ 2 := by
    have hsq : 0 ≤ σ ^ 2 := pow_nonneg (by linarith) 2
    positivity
  have h_num : ((σ / R0) * (R0 + 1 / 2) + g) ^ 2 ≤ (3 * σ / 2 + g) ^ 2 := by
    have h_nonneg_left : 0 ≤ (σ / R0) * (R0 + 1 / 2) + g := by
      positivity
    have h_nonneg_right : 0 ≤ 3 * σ / 2 + g := by
      positivity
    have h_base : (σ / R0) * (R0 + 1 / 2) + g ≤ 3 * σ / 2 + g := by
      have h : (σ / R0) * (R0 + 1 / 2) ≤ 3 * σ / 2 := by
        field_simp [hR0.ne.symm]
        nlinarith
      linarith
    have h_abs : |(σ / R0) * (R0 + 1 / 2) + g| ≤ |3 * σ / 2 + g| := by
      rwa [abs_of_nonneg h_nonneg_left, abs_of_nonneg h_nonneg_right]
    exact (sq_le_sq.mpr h_abs)
  exact div_le_div_of_nonneg_right h_num h_denom

/-- The range of the dent at a play of `K` is at most `1/2` at the parameters of RIPE-B with `L_K = σ/R0`. -/
theorem rangeK_le (σ R0 g : ℝ) (hσ : 0 ≤ σ) (hR : 1 ≤ R0) (h : 3 * σ / 2 + g ≤ 1 / 2) :
    σ / R0 * (R0 + 1 / 2) + g ≤ 1 / 2 := by
  have hRpos : 0 < R0 := by linarith
  have hkey : σ / R0 * (R0 + 1 / 2) ≤ 3 * σ / 2 := by
    calc
      σ / R0 * (R0 + 1 / 2) = σ + σ / (2 * R0) := by
        field_simp [hRpos.ne']
      _ ≤ σ + σ / 2 := by
        have hdiv : σ / (2 * R0) ≤ σ / 2 := by
          have hpos2R0 : 0 < 2 * R0 := by nlinarith
          have hpos2 : 0 < (2 : ℝ) := by norm_num
          have hineq : (2 : ℝ) ≤ 2 * R0 := by nlinarith
          have hone_div : 1 / (2 * R0) ≤ 1 / 2 :=
            (one_div_le_one_div hpos2R0 hpos2).mpr hineq
          calc
            σ / (2 * R0) = σ * (1 / (2 * R0)) := by ring
            _ ≤ σ * (1 / 2) := mul_le_mul_of_nonneg_left hone_div hσ
            _ = σ / 2 := by ring
        nlinarith
      _ = 3 * σ / 2 := by ring
  nlinarith

/-- `R0 ≤ d ≤ e^{Γ/5}` when `n ≥ d^10`. -/
theorem log_R0_le (dd nn R0 : ℝ) (hd : 1 ≤ dd) (hR : 0 < R0) (hRd : R0 ≤ dd) (hn : dd ^ 10 ≤ nn) :
    5 * Real.log R0 ≤ gamR dd nn := by
  have hddpos : 0 < dd := by linarith
  have hdd5pos : 0 < dd ^ 5 := pow_pos hddpos 5
  have hR0le : Real.log R0 ≤ Real.log dd := Real.log_le_log hR hRd
  have h5logR0le5logdd : 5 * Real.log R0 ≤ 5 * Real.log dd := by nlinarith
  have hdd5le_nndivdd5 : dd ^ 5 ≤ nn / dd ^ 5 :=
    (le_div_iff₀ hdd5pos).mpr (by
      calc
        dd ^ 5 * dd ^ 5 = dd ^ 10 := by ring
        _ ≤ nn := hn
      )
  have hgamR : 5 * Real.log dd ≤ gamR dd nn := by
    dsimp [gamR]
    calc
      5 * Real.log dd = Real.log (dd ^ 5) := by
        rw [Real.log_pow, Nat.cast_ofNat]
      _ ≤ Real.log (nn / dd ^ 5) :=
        Real.log_le_log (by positivity) hdd5le_nndivdd5
      _ = gamR dd nn := rfl
  nlinarith

/-- `X_K = X/R0²` at the floor of `L_K = σ/R0`. -/
theorem xCount_ripe_K (dd nn σ R0 : ℝ) (hd : 0 < dd) (hk : 0 < kRipe dd) (hσ : 0 < σ) (hn : 0 < nn)
    (hΓ : 0 < gamR dd nn) (hR : 0 < R0) :
    xCount dd (wStar dd (kRipe dd) (σ / R0) (gRipe dd nn σ)) =
      kRipe dd ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) / R0 ^ 2 := by
  have h_wStar_eq : wStar dd (kRipe dd) (σ / R0) (gRipe dd nn σ) = R0 * wStar dd (kRipe dd) σ (gRipe dd nn σ) := by
    unfold wStar
    field_simp [hR.ne.symm]
  rw [h_wStar_eq]
  have h_xCount_eq : xCount dd (R0 * wStar dd (kRipe dd) σ (gRipe dd nn σ)) =
      xCount dd (wStar dd (kRipe dd) σ (gRipe dd nn σ)) / R0 ^ 2 := by
    unfold xCount
    field_simp [hR.ne.symm]
  rw [h_xCount_eq]
  rw [xCount_ripe dd nn σ hd hk hσ hn hΓ]

/-- (N1), the step that reads `R0`: `ln(X_K/2) ≥ Γ/2` when `5 ln R0 ≤ Γ`. -/
theorem log_x_ripe_ge_K (dd nn k R0 : ℝ) (hk : 1 ≤ k) (hd : 0 < dd) (hn : 0 < nn) (hΓ : 0 < gamR dd nn)
    (hR : 0 < R0) (hRΓ : 5 * Real.log R0 ≤ gamR dd nn) :
    gamR dd nn / 2 ≤ Real.log (k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) / R0 ^ 2 / 2) := by
  set Γ := gamR dd nn with hΓ_def
  have hΓpos : 0 < Γ := hΓ
  have hpos_arg : 0 < k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * Γ) / R0 ^ 2 / 2 := by
    positivity
  rw [Real.le_log_iff_exp_le hpos_arg]
  rw [div_div, div_div, ← mul_assoc]
  have hDpos : 0 < (4 / ((10 : ℝ) ^ 6) * dd ^ 5 * Γ) * R0 ^ 2 * 2 := by positivity
  apply (le_div_iff₀ hDpos).mpr
  have h_exp_Gamma : Real.exp Γ = nn / dd ^ 5 := by
    rw [hΓ_def, gamR]
    exact Real.exp_log (div_pos hn (pow_pos hd 5))
  have hn_eq : nn = dd ^ 5 * Real.exp Γ := by
    calc
      nn = (nn / dd ^ 5) * dd ^ 5 := by field_simp [hd.ne']
      _ = Real.exp Γ * dd ^ 5 := by rw [← h_exp_Gamma]
      _ = dd ^ 5 * Real.exp Γ := mul_comm _ _
  rw [hn_eq]
  have hgoal : Real.exp (Γ / 2) * ((4 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2 * 2) ≤ k ^ 4 * Real.exp Γ := by
    have hGamma_bound : 8 / ((10 : ℝ) ^ 6) * Γ ≤ Γ / 10 + 1 := by
      have hΓ_nonneg : 0 ≤ Γ := le_of_lt hΓpos
      have h : 8 * Γ ≤ ((10 : ℝ) ^ 5) * Γ + ((10 : ℝ) ^ 6) := by nlinarith
      have hpos10 : 0 < (10 : ℝ) ^ 6 := by norm_num
      calc
        8 / ((10 : ℝ) ^ 6) * Γ = (8 * Γ) / ((10 : ℝ) ^ 6) := by ring
        _ ≤ (((10 : ℝ) ^ 5) * Γ + ((10 : ℝ) ^ 6)) / ((10 : ℝ) ^ 6) := by
          exact (div_le_div_of_nonneg_right h (by positivity : 0 ≤ (10 : ℝ) ^ 6))
        _ = ((10 : ℝ) ^ 5) * Γ / ((10 : ℝ) ^ 6) + ((10 : ℝ) ^ 6) / ((10 : ℝ) ^ 6) := by ring
        _ = Γ / 10 + 1 := by field_simp [hpos10.ne']
    have hR0_le : R0 ≤ Real.exp (Γ / 5) := by
      calc
        R0 = Real.exp (Real.log R0) := by rw [Real.exp_log hR]
        _ ≤ Real.exp (Γ / 5) := Real.exp_le_exp.mpr (by linarith)
    have hR0_sq_le : R0 ^ 2 ≤ Real.exp (2 * Γ / 5) := by
      calc
        R0 ^ 2 ≤ (Real.exp (Γ / 5)) ^ 2 := by
          have hR0_nonneg : 0 ≤ R0 := hR.le
          have hexp_nonneg : 0 ≤ Real.exp (Γ / 5) := (Real.exp_pos _).le
          nlinarith
        _ = Real.exp (Γ / 5) * Real.exp (Γ / 5) := by rw [pow_two]
        _ = Real.exp (Γ / 5 + Γ / 5) := by rw [← Real.exp_add]
        _ = Real.exp (2 * Γ / 5) := by
          congr 1
          field_simp
          ring
    have h_add_one : Γ / 10 + 1 ≤ Real.exp (Γ / 10) := Real.add_one_le_exp (Γ / 10)
    have hk_pow : 1 ≤ k ^ 4 := by
      simpa using one_le_pow₀ hk (n := 4)
    calc
      Real.exp (Γ / 2) * ((4 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2 * 2)
          = Real.exp (Γ / 2) * ((8 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2) := by ring
      _ ≤ Real.exp (Γ / 2) * ((Γ / 10 + 1) * R0 ^ 2) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ Real.exp (Γ / 2))
        apply mul_le_mul_of_nonneg_right hGamma_bound (by positivity : 0 ≤ R0 ^ 2)
      _ ≤ Real.exp (Γ / 2) * (Real.exp (Γ / 10) * Real.exp (2 * Γ / 5)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ Real.exp (Γ / 2))
        apply mul_le_mul h_add_one hR0_sq_le (by positivity : 0 ≤ R0 ^ 2) (by positivity : 0 ≤ Real.exp (Γ / 10))
      _ = Real.exp (Γ / 2) * Real.exp (Γ / 10) * Real.exp (2 * Γ / 5) := by ring
      _ = Real.exp (Γ / 2 + Γ / 10) * Real.exp (2 * Γ / 5) := by rw [← Real.exp_add (Γ / 2) (Γ / 10)]
      _ = Real.exp ((Γ / 2 + Γ / 10) + 2 * Γ / 5) := by rw [← Real.exp_add]
      _ = Real.exp Γ := by
        congr 1
        field_simp
        ring
      _ ≤ k ^ 4 * Real.exp Γ := by
        have h := mul_le_mul_of_nonneg_right hk_pow (Real.exp_pos Γ).le
        simpa [one_mul] using h
  calc
    Real.exp (Γ / 2) * ((4 / ((10 : ℝ) ^ 6) * dd ^ 5 * Γ) * R0 ^ 2 * 2)
        = Real.exp (Γ / 2) * (dd ^ 5 * ((4 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2 * 2)) := by ring
    _ = (dd ^ 5) * (Real.exp (Γ / 2) * ((4 / ((10 : ℝ) ^ 6) * Γ) * R0 ^ 2 * 2)) := by ring
    _ ≤ (dd ^ 5) * (k ^ 4 * Real.exp Γ) := by
      apply mul_le_mul_of_nonneg_left hgoal
      positivity
    _ = k ^ 4 * (dd ^ 5 * Real.exp Γ) := by ring

/-- (N2): `ln(X_K/2) ≤ ln(X/2) ≤ Γ + 4 ln k + 11.8` for `R0 ≥ 1`. -/
theorem log_x_ripe_le_K (dd nn k R0 : ℝ) (hk : 1 ≤ k) (hd : 0 < dd) (hn : 0 < nn) (hΓ : 1 ≤ gamR dd nn)
    (hR : 1 ≤ R0) :
    Real.log (k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) / R0 ^ 2 / 2) ≤
      gamR dd nn + 4 * Real.log k + 118 / 10 := by
  set X := k ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) with hXdef
  have hXpos : 0 < X := by
    dsimp [X]
    positivity
  have hR0pos : 0 < R0 := by linarith
  have hR0sq_ge_one : 1 ≤ R0 ^ 2 := by
    nlinarith
  have hdiv : X / R0 ^ 2 / 2 ≤ X / 2 := by
    have h1 : X / R0 ^ 2 ≤ X := div_le_self hXpos.le hR0sq_ge_one
    nlinarith
  have hlog := Real.log_le_log (by positivity) hdiv
  have hbound := log_x_ripe_le dd nn k hk hd hn hΓ
  simpa [X] using le_trans hlog hbound

/-- (R2-K) at the rate's parameters: `g ≤ k (σ/R0)/(40 d)` for `1 ≤ R0 ≤ d` and `n ≥ d^10`. -/
theorem R2_ripe_K (dd nn σ R0 : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) (hσ : 0 < σ) (hR : 1 ≤ R0)
    (hRd : R0 ≤ dd) (hn : dd ^ 10 ≤ nn) : gRipe dd nn σ ≤ kRipe dd * (σ / R0) / (40 * dd) := by
  obtain ⟨hk, -⟩ := kRipe_ge dd hd1 hd
  have hk0 : 0 < kRipe dd := by linarith
  have hd0 : 0 < dd := by linarith
  have hR0 : 0 < R0 := by linarith
  have hn0 : 0 < nn := lt_of_lt_of_le (by positivity) hn
  have hnE := n_eq_exp dd nn hd0 hn0
  have h10 : dd ^ 5 * dd ^ 5 ≤ dd ^ 5 * Real.exp (gamR dd nn) := by
    rw [← hnE]
    calc dd ^ 5 * dd ^ 5 = dd ^ 10 := by ring
      _ ≤ nn := hn
  have hE5 : dd ^ 5 ≤ Real.exp (gamR dd nn) := le_of_mul_le_mul_left h10 (by positivity)
  have hd45 : dd ^ 2 * dd ^ 2 ≤ dd ^ 5 := by
    calc dd ^ 2 * dd ^ 2 = dd ^ 4 := by ring
      _ ≤ dd ^ 5 := pow_le_pow_right₀ hd1 (by norm_num)
  have hΓ0 : 0 ≤ gamR dd nn := Real.one_le_exp_iff.mp ((one_le_pow₀ hd1).trans hE5)
  have hEE : Real.exp (gamR dd nn) = Real.exp (gamR dd nn / 2) * Real.exp (gamR dd nn / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 := Real.exp_pos (gamR dd nn / 2)
  have hEd : dd ^ 2 ≤ Real.exp (gamR dd nn / 2) := by
    by_contra h
    replace h := not_le.mp h
    have := mul_lt_mul'' h h hE0.le hE0.le
    linarith
  have hEΓ : gamR dd nn / 2 ≤ Real.exp (gamR dd nn / 2) := by linarith [Real.add_one_le_exp (gamR dd nn / 2)]
  have hexp : dd ^ 2 * (gamR dd nn / 2) ≤ Real.exp (gamR dd nn) := by
    rw [hEE]; exact mul_le_mul hEd hEΓ (by positivity) hE0.le
  have hk1 : 1 ≤ kRipe dd ^ 4 := one_le_pow₀ (by linarith)
  have key : 64 / 10 ^ 6 * dd ^ 7 * gamR dd nn ≤ kRipe dd ^ 4 * nn := by
    have h1 : dd ^ 5 * (dd ^ 2 * (gamR dd nn / 2)) ≤ dd ^ 5 * Real.exp (gamR dd nn) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h2 : dd ^ 5 * Real.exp (gamR dd nn) ≤ kRipe dd ^ 4 * (dd ^ 5 * Real.exp (gamR dd nn)) :=
      le_mul_of_one_le_left (by positivity) hk1
    have h3 : 64 / 10 ^ 6 * dd ^ 7 * gamR dd nn ≤ dd ^ 5 * (dd ^ 2 * (gamR dd nn / 2)) := by
      have : 0 ≤ dd ^ 7 * gamR dd nn := by positivity
      nlinarith
    rw [← hnE] at h2
    linarith
  unfold gRipe
  generalize kRipe dd = k at *
  generalize gamR dd nn = Γ at *
  have hs := Real.sq_sqrt hd0.le
  have hr := Real.sq_sqrt hn0.le
  have hu := Real.sq_sqrt hΓ0
  have hs0 := Real.sqrt_pos.mpr hd0
  have hr0 := Real.sqrt_pos.mpr hn0
  have hu0 := Real.sqrt_nonneg Γ
  generalize Real.sqrt dd = s at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs hr hu
  have hsq : 8 / 10 ^ 3 * s ^ 7 * u ≤ k ^ 2 * r := by
    have : (8 / 10 ^ 3 * s ^ 7 * u) ^ 2 ≤ (k ^ 2 * r) ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  have hRs : s ^ 5 * u * R0 ≤ s ^ 7 * u := by
    have := mul_le_mul_of_nonneg_left hRd (by positivity : (0 : ℝ) ≤ s ^ 5 * u)
    nlinarith
  rw [mul_div_assoc', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hσ.le, mul_le_mul_of_nonneg_left hRs hσ.le]

/-- Theorem RIPE-K, the rate: `E R_n ≥ 2.5·10⁻⁵ σ d^{3/2} (n ln(n/d⁵))^{1/2}/(120 ln d + 68)` for the strategy with
`L_K = σ/R0`, `σ ≤ 1/4`, `1 ≤ R0 ≤ d`, `n ≥ d^10` and `d ≥ 2048 (120 ln d + 68)`. -/
theorem ripe_rate_K {dd σ R0 : ℝ} {n : ℕ} {p : ℝ} {Jm Pm am Dm lm : ℕ → ℝ} (hd1 : 1 ≤ dd) (hσ : 0 < σ)
    (hσ' : σ ≤ 1 / 4) (hR : 1 ≤ R0) (hRd : R0 ≤ dd) (hn : dd ^ 10 ≤ n) (hn4 : Real.exp 4 * dd ^ 5 ≤ n)
    (hd : 2048 * kRipe dd ≤ dd)
    (h : GameFacts dd (kRipe dd) (gRipe dd n σ) σ (chanBK (σ / R0) R0 (gRipe dd n σ) σ)
      (wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ)) n p Jm Pm am Dm lm) :
    25 / 10 ^ 6 * σ * (dd * Real.sqrt dd) * Real.sqrt (n * gamR dd n) / kRipe dd ≤ ∑ t ∈ range n, Dm t := by
  obtain ⟨hk240, hd491⟩ := kRipe_ge dd hd1 hd
  have hd0 : 0 < dd := by linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn4
  have hR0 : 0 < R0 := by linarith
  have hΓ : 4 ≤ gamR dd n := gamR_ge dd n hd0 hn4
  have hg : 0 < gRipe dd n σ := gRipe_pos dd n σ hd1 hd hσ hn4
  have hgle : gRipe dd n σ ≤ σ / 81920 := gRipe_le dd n σ hd1 hd hσ hn4
  have hB := (chanBK_le_chanB σ R0 (gRipe dd n σ) hσ hR hg.le).trans (chanB_ripe σ (gRipe dd n σ) hσ hg.le hgle)
  have hB0 : 0 ≤ chanBK (σ / R0) R0 (gRipe dd n σ) σ := by unfold chanBK; positivity
  obtain ⟨hhi, hlo⟩ := ripe_balance (by linarith) hg hσ (div_pos hσ hR0) hB0 (R1_ripe dd _ hB) hd
    (R2_ripe_K dd n σ R0 hd1 hd hσ hR hRd hn) h
  set w := wStar dd (kRipe dd) (σ / R0) (gRipe dd n σ) with hw
  have hX : xCount dd w = kRipe dd ^ 4 * n / (4 / 10 ^ 6 * dd ^ 5 * gamR dd n) / R0 ^ 2 :=
    xCount_ripe_K dd n σ R0 hd0 (by linarith) hσ hn0 (by linarith) hR0
  have hd12 : 12288 ≤ dd := by linarith
  have hNge : 1248 / 10000 * dd * gamR dd n ≤ nStar dd w := by
    apply nStar_ripe_ge dd _ _ hd0 hΓ
    have h1 := nStar_ge_x dd w hd12
    have h2 := log_x_ripe_ge_K dd n (kRipe dd) R0 (by linarith) hd0 hn0 (by linarith) hR0
      (log_R0_le dd n R0 hd1 hR0 hRd hn)
    rw [hX] at h1
    nlinarith
  have hNle : nStar dd w ≤ dd / 4 * (gamR dd n + 4 * Real.log (kRipe dd) + 118 / 10) := by
    have h1 := nStar_le_x dd w hd1
    have h2 := log_x_ripe_le_K dd n (kRipe dd) R0 (by linarith) hd0 hn0 (by linarith) hR
    rw [hX] at h1
    nlinarith
  by_cases hp : 1 / 2 ≤ p
  · exact (rate_hi dd n (kRipe dd) σ (gamR dd n) (gRipe dd n σ) (nStar dd w) p hd0 (by linarith) hσ hn0
      (by linarith) rfl hNge hp).trans hhi
  · rw [not_le] at hp
    have hsmall := nStar_ripe_small dd n (kRipe dd) (gamR dd n) (nStar dd w) hk240 (by linarith) hd491 hΓ
      (n_eq_exp dd n hd0 hn0) hNle
    exact (rate_lo dd n (kRipe dd) σ (gamR dd n) (gRipe dd n σ) (nStar dd w) p hd0 (by linarith) hσ hn0
      (by linarith) rfl hsmall hp).trans hlo

/-- The parameters of the lower bound on a body between two balls: `L_K = σ/R0 ∈ (0, 1/4]`, the range
`L_K (R0 + 1/2) + g ≤ 1/2` (Lemma
LEGAL-K), `X_K ≥ 16` at the floor (Lemma COUNT). -/
theorem ripeK_params {d n : ℕ} {R0 : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0) (hRd : R0 ≤ d) :
    0 < sigB n / R0 ∧ sigB n / R0 ≤ 1 / 4 ∧ sigB n / R0 * (R0 + 1 / 2) + gRipe d n (sigB n) ≤ 1 / 2 ∧
      16 ≤ xCount d (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) := by
  have h := ripeB_params hd hn
  rcases h with ⟨hσpos, hσle, hgpos, hgle, hsum, hkge, hkd, hxcount, hchan, hkbound, hexp⟩
  have hR0pos : 0 < R0 := by linarith
  have hdpos : 0 < (d : ℝ) := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : (1 : ℕ) ≤ d := by omega
    exact_mod_cast this
  have h1 : 0 < sigB n / R0 := div_pos hσpos hR0pos
  have h2 : sigB n / R0 ≤ 1 / 4 := by
    calc
      sigB n / R0 ≤ sigB n := div_le_self hσpos.le hR
      _ ≤ 1 / 4 := hσle
  have h3 : sigB n / R0 * (R0 + 1 / 2) + gRipe d n (sigB n) ≤ 1 / 2 := by
    apply rangeK_le (sigB n) R0 (gRipe d n (sigB n)) hσpos.le hR hsum
  have hR2 : gRipe (d : ℝ) (n : ℝ) (sigB n) ≤ kRipe (d : ℝ) * (sigB n / R0) / (40 * (d : ℝ)) := by
    apply R2_ripe_K (d : ℝ) (n : ℝ) (sigB n) R0 hd1 hkd hσpos hR hRd
    exact_mod_cast hn
  have hkRipe_pos : 0 < kRipe (d : ℝ) := by
    have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
    nlinarith
  have h4 : 16 ≤ xCount d (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) := by
    apply xCount_wStar_ge (d : ℝ) (kRipe (d : ℝ)) (sigB n / R0) (gRipe (d : ℝ) (n : ℝ) (sigB n))
    · exact hdpos
    · exact hkRipe_pos
    · exact div_pos hσpos hR0pos
    · exact hgpos
    · simpa using hR2
  exact ⟨h1, h2, h3, h4⟩

/-- The lower bound on a body between two balls, the arithmetic, in the form of `TheoremConj1LowerPoly`: the
expectations of the Gaussian game
with `L_K = σ/R0` satisfy `GameFacts`, and the bounded game's mean regret `ER` is at least the Gaussian one minus
`1/n`; then `ER ≥ 7·10⁻⁹ d^{3/2} n^{1/2}/ln d`. -/
theorem ripeK_balance {d n : ℕ} {R0 : ℝ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) (hR : 1 ≤ R0) (hRd : R0 ≤ d)
    {p : ℝ} {Jm Pm am Dm lm : ℕ → ℝ}
    (h : GameFacts d (kRipe d) (gRipe d n (sigB n)) (sigB n)
      (chanBK (sigB n / R0) R0 (gRipe d n (sigB n)) (sigB n))
      (wStar d (kRipe d) (sigB n / R0) (gRipe d n (sigB n))) n p Jm Pm am Dm lm)
    {ER : ℝ} (hER : ∑ t ∈ range n, Dm t - 1 / n ≤ ER) :
    7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ ER := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  obtain ⟨hs0, hs4⟩ := ripeB_sig d n hdR hnR
  have hdim := ripeB_dim d hdR
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hn4 := ripeB_n d n hdR hnR
  have hrate := ripe_rate_K hd1 hs0 hs4 hR hRd hnR hn4 hdim h
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hn1 : (1 : ℝ) < n := by
    have : (1 : ℝ) < (d : ℝ) ^ 10 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  have hcoef := ripeB_coef n (gamR d n) hn1 (ripeB_gam d n hd1 hnR)
  have hfin := ripeB_final d n hdR hnR
  rw [rpow_three_halves d (by linarith)]
  have hdd : 0 ≤ (d : ℝ) * Real.sqrt d := by positivity
  have h1 : 9 / 10 ^ 7 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / kRipe d ≤ ∑ t ∈ range n, Dm t := by
    refine le_trans ?_ hrate
    rw [div_le_div_iff_of_pos_right (by linarith)]
    have h2 : 9 / 10 ^ 7 * Real.sqrt n ≤ 25 / 10 ^ 6 * sigB n * Real.sqrt (n * gamR d n) :=
      le_trans (by nlinarith [Real.sqrt_nonneg (n : ℝ)]) hcoef
    nlinarith [mul_le_mul_of_nonneg_left h2 hdd]
  linarith

end AdversarialBco.Lower
