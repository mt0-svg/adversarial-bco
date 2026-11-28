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
reads the range `L_K (R0 + 1/2) + g` of the dent at a play of `K` (`chanBK`, at most `chanB σ g σ` for `R0 ≥ 1`, by
`chanBK_le_chanB`; the range is at most `1/2`, `rangeK_le`); and the count reads `R0` through `R0 ≤ d ≤ e^{Γ/5}`
(`log_R0_le`). Pure arithmetic on reals.
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

end AdversarialBco.Lower
