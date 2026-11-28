/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetW
public import AdversarialBco.UW.DetPar
public import AdversarialBco.UW.RowsUW

@[expose] public section

/-!
# DET at T4U with sure ranges

`detOf : RowsUW → SIFactsUW → DetUW`. On the regime, the weighted epoch at `ctxW` is an epoch of Theorem U's learner
on the path `pathW` (UW/Defs.lean, `mode_pathW`, `Y_pathW`). Its hypotheses `DetHypW` (UW/DetRound.lean) come from:
`DetBase` at T4U (`detBaseW`, with the base rows of `RowsW` and the facts of SI at T4U); the rows of the levels with
`u` and the closure of `RowsW`; the sure ranges of the observation on the rounds that run (Lemma WR, `obsW_sure`); the
four bounds of the guards, from the regime (`N_0 = 15 · 2^17 d³ n⁴`, `14 y0² ≤ y0² log(7/δc) ≤ n`); and the events
(b) to (e) of `EvDetW`. Then `DetHypW.epoch_ok` (UW/DetW.lean), Theorem U's induction on the rounds at these levels.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The arithmetic of the guards, on variables -/

/-- The gradient: `n η κ M₁ ≤ 1/(4 δ_e²)` with `δ_e = 1/N`, from `η κ λ κ₀ y0 (b0 + 2) ≤ 7/4` and `7 n ≤ N`. -/
theorem gM_arith (n N A η κ l k y b : ℝ) (hN : 0 < N) (hn : 0 ≤ n) (h7 : 7 * n ≤ N) (hA0 : 0 ≤ A) (hA : A ≤ 7 / 4)
    (hAdef : η * κ * l * k * y * (b + 2) = A) :
    n * (η * κ * (l * k * y * (b + 2) / (1 / N))) ≤ 1 / (4 * (1 / N) ^ 2) := by
  have hN' : N ≠ 0 := hN.ne'
  have e : n * (η * κ * (l * k * y * (b + 2) / (1 / N))) = n * N * A := by
    rw [← hAdef, div_div_eq_mul_div, div_one]; ring
  have e2 : 1 / (4 * (1 / N) ^ 2) = N ^ 2 / 4 := by field_simp
  rw [e, e2]
  have h1 : n * A ≤ N / 4 := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 hN.le
  nlinarith

/-- The gradient: `1/σ² = 8 L ≤ 1/(2 δ_e²)` with `L = 36 log N`, `N ≥ 576`. -/
theorem gS_arith (N L : ℝ) (hN : 576 ≤ N) (hL : L = 36 * Real.log N) :
    (1 / (8 * L))⁻¹ ≤ 1 / (2 * (1 / N) ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have e1 : (1 / (8 * L))⁻¹ = 8 * L := by rw [one_div, inv_inv]
  have e2 : 1 / (2 * (1 / N) ^ 2) = N ^ 2 / 2 := by field_simp
  rw [e1, e2, hL]
  nlinarith

/-- The guard Z: `(η/2) n y0 κ₀^{1/2} X^{1/2} ≤ (3/4) R/δ_e²` with `δ_e = 1/N`, `X = (b0 + 1)/δ_e ≤ 108 d N²`,
`14 y0² ≤ n` and `15 · 2^17 d n³ ≤ N`. -/
theorem gZ_arith (η k0 R N n d y0 X : ℝ) (hη0 : 0 < η) (hη : η ≤ 1) (hk0 : 0 ≤ k0) (hk1 : k0 ≤ 21 / 20)
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hn : 0 ≤ n) (hd : 0 ≤ d) (hy0 : 0 ≤ y0) (hy : 14 * y0 ^ 2 ≤ n) (hX0 : 0 ≤ X)
    (hX : X ≤ 108 * d * N ^ 2) (hdn : 15 * 2 ^ 17 * (d * n ^ 3) ≤ N) :
    η / 2 * (n * (y0 * Real.sqrt k0 * Real.sqrt X)) ≤ 3 / 4 * R / (1 / N) ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hsk : Real.sqrt k0 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsX := Real.sqrt_nonneg X
  have hsk0 := Real.sqrt_nonneg k0
  have key : (n * y0) ^ 2 * X ≤ (3 / 4 * N ^ 2) ^ 2 := by
    have hy2 : y0 ^ 2 ≤ n / 14 := by linarith
    have h1 : y0 ^ 2 * X ≤ n / 14 * (108 * d * N ^ 2) :=
      mul_le_mul hy2 hX hX0 (by positivity)
    calc (n * y0) ^ 2 * X = n ^ 2 * (y0 ^ 2 * X) := by ring
      _ ≤ n ^ 2 * (n / 14 * (108 * d * N ^ 2)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg n)
      _ = 108 / 14 * (d * n ^ 3) * N ^ 2 := by ring
      _ ≤ 108 / 14 * (N / (15 * 2 ^ 17)) * N ^ 2 := by
          gcongr
          rw [le_div_iff₀ (by norm_num)]; linarith
      _ ≤ (3 / 4 * N ^ 2) ^ 2 := by
          have hN2 : N ≤ N ^ 2 := by nlinarith
          have hN3 : N ^ 3 ≤ N ^ 4 := by nlinarith [pow_pos hN0 3]
          nlinarith [pow_pos hN0 3]
  have h := Real.sqrt_le_sqrt key
  rw [Real.sqrt_mul' _ hX0, Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
  have e : 3 / 4 * R / (1 / N) ^ 2 = 3 / 4 * R * N ^ 2 := by field_simp
  rw [e]
  have h2 : η / 2 * (n * (y0 * Real.sqrt k0 * Real.sqrt X)) ≤ 1 / 2 * (n * (y0 * 2 * Real.sqrt X)) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
    apply mul_le_mul_of_nonneg_left _ hn
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsk hy0) hsX
  have h3 : 1 / 2 * (n * (y0 * 2 * Real.sqrt X)) = n * y0 * Real.sqrt X := by ring
  have h4 : 3 / 4 * N ^ 2 ≤ 3 / 4 * R * N ^ 2 := by nlinarith [sq_nonneg N]
  linarith

/-- The guard W: `4 κ₀ y0² (b0 + 1) ≤ 16 d n L`, from `14 y0² ≤ n` and `b0 + 1 ≤ 3 d L`. -/
theorem gW_arith (k0 y0 b0 n d L : ℝ) (hk0 : 0 ≤ k0) (hk1 : k0 ≤ 21 / 20) (hy : 14 * y0 ^ 2 ≤ n) (hb0 : 0 ≤ b0)
    (hb : b0 + 1 ≤ 3 * d * L) (hn : 0 ≤ n) :
    4 * k0 * y0 ^ 2 * (b0 + 1) ≤ 16 * d * n * L := by
  have hy2 : y0 ^ 2 ≤ n / 14 := by linarith
  have h1 : y0 ^ 2 * (b0 + 1) ≤ n / 14 * (3 * d * L) := mul_le_mul hy2 hb (by linarith) (by positivity)
  have h2 : 0 ≤ y0 ^ 2 * (b0 + 1) := by positivity
  have hdL : 0 ≤ d * L := by nlinarith
  calc 4 * k0 * y0 ^ 2 * (b0 + 1) = 4 * k0 * (y0 ^ 2 * (b0 + 1)) := by ring
    _ ≤ 4 * (21 / 20) * (y0 ^ 2 * (b0 + 1)) := by nlinarith
    _ ≤ 4 * (21 / 20) * (n / 14 * (3 * d * L)) := by nlinarith
    _ ≤ 16 * d * n * L := by nlinarith [mul_nonneg hn hdL]

/-! ## The regime -/

section Regime

variable {n : ℕ} {ρ : RefW}

/-- `N_0 ≥ 15 · 2^17 d n³`. -/
theorem n0W_ge_dn3 (hd : 1 ≤ d) (hn : 1 ≤ n) : 15 * 2 ^ 17 * ((d : ℝ) * (n : ℝ) ^ 3) ≤ n0W d n := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [n0W_cast]
  have h1 : (d : ℝ) ≤ (d : ℝ) ^ 3 := le_self_pow₀ hd1 (by norm_num)
  have h2 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : (d : ℝ) * (n : ℝ) ^ 3 ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith

theorem RegimeW.Le_logN (R : RegimeW d n ρ) : (parW d n ρ.u).Le = 36 * Real.log (n0W d n : ℝ) := by
  show df2C0 * Real.log (1 / (1 / (n0W d n : ℝ))) = _
  rw [df2C0, one_div_one_div]

/-- `log(7/δc) ≥ 14`: `7/δc ≥ N_0 ≥ e^14`. -/
theorem RegimeW.log7_ge (R : RegimeW d n ρ) : 14 ≤ Real.log (7 / ρ.δc) := by
  obtain ⟨-, -, -, heN⟩ := n0W_bounds R.hd R.hn
  have hN0 : 0 < (n0W d n : ℝ) := lt_of_lt_of_le (Real.exp_pos 14) heN
  have hdc := R.dc_pos
  have h1 : (n0W d n : ℝ) ≤ 7 / ρ.δc := by
    rw [le_div_iff₀ hdc]
    have h := mul_le_mul_of_nonneg_left R.dc_le hN0.le
    rw [mul_one_div_cancel hN0.ne'] at h
    linarith
  rw [Real.le_log_iff_exp_le (by positivity)]
  exact heN.trans h1

/-- `14 y0² ≤ n` (event (b) under the clip, `y0² log(7/δc) ≤ n`). -/
theorem RegimeW.y0_sq_le (R : RegimeW d n ρ) : 14 * ρ.y0 ^ 2 ≤ n := by
  have h := R.y0_sq.2
  have hl := R.log7_ge
  nlinarith [mul_nonneg (sq_nonneg ρ.y0) (sub_nonneg.2 hl)]

theorem RegimeW.b0_ge (R : RegimeW d n ρ) : 1 ≤ ρ.b0 := by
  have h := R.b0_lo
  have := R.lam0_nonneg
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem k0_parW_nonneg (d n : ℕ) (u : ℝ) : 0 ≤ (parW d n u).k0 := by
  rw [(df2ParFix_parW d n u).k0]; positivity

theorem RegimeW.gM (R : RegimeW d n ρ) (RW : RowsW d n ρ) :
    (n : ℝ) * ((parW d n ρ.u).eta * (parW d n ρ.u).kap *
      ((parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 * (ρ.b0 + 2) / (parW d n ρ.u).δe)) ≤
      1 / (4 * (parW d n ρ.u).δe ^ 2) := by
  have hb := R.b0_ge
  have hy := R.y0_pos
  have hk := k0_parW_nonneg d n ρ.u
  have hη := RW.base.pos_eta
  have hl := RW.base.pos_lam
  have hκ : (parW d n ρ.u).kap = 1 / 4 := (df2ParFix_parW d n ρ.u).kap
  have hA0 : 0 ≤ (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 * ρ.y0 := by
    rw [hκ]; positivity
  have ha := RW.clo_a
  have hq := RW.clo_q
  have hNge := n0W_ge_dn3 R.hd R.hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast R.hn
  have hdn : (n : ℝ) ≤ (d : ℝ) * (n : ℝ) ^ 3 := by
    have : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn1 (by norm_num)
    nlinarith
  have hNn : 7 * (n : ℝ) ≤ n0W d n := by linarith
  exact gM_arith n (n0W d n) _ _ _ _ _ ρ.y0 ρ.b0 (by linarith) (by linarith) hNn
    (mul_nonneg hA0 (by linarith)) (by nlinarith) rfl

theorem RegimeW.gS (R : RegimeW d n ρ) : (parW d n ρ.u).sig2⁻¹ ≤ 1 / (2 * (parW d n ρ.u).δe ^ 2) := by
  obtain ⟨hN, -, -, -⟩ := n0W_bounds R.hd R.hn
  rw [(df2ParFix_parW d n ρ.u).sig2]
  exact gS_arith _ _ (by linarith) R.Le_logN

theorem RegimeW.gZ (R : RegimeW d n ρ) (RW : RowsW d n ρ) :
    (parW d n ρ.u).eta / 2 * (n * (ρ.y0 * Real.sqrt (parW d n ρ.u).k0 *
      Real.sqrt ((ρ.b0 + 1) / (parW d n ρ.u).δe))) ≤ 3 / 4 * (parW d n ρ.u).R / (parW d n ρ.u).δe ^ 2 := by
  obtain ⟨hN, -, -, -⟩ := n0W_bounds R.hd R.hn
  have hN0 : 0 < (n0W d n : ℝ) := by linarith
  have hb := R.b0_ge
  have hbL := R.b0_le
  have hlog : Real.log (n0W d n : ℝ) ≤ n0W d n := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hL := R.Le_logN
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hX : (ρ.b0 + 1) / (1 / (n0W d n : ℝ)) ≤ 108 * d * (n0W d n : ℝ) ^ 2 := by
    rw [div_div_eq_mul_div, div_one]
    have h1 : (parW d n ρ.u).Le ≤ 36 * (n0W d n : ℝ) := by rw [hL]; linarith
    have h2 : ρ.b0 + 1 ≤ 3 * d * (36 * (n0W d n : ℝ)) := hbL.trans (by nlinarith)
    nlinarith
  exact gZ_arith _ _ _ _ _ _ _ _ RW.base.pos_eta RW.base.eta_le (k0_parW_nonneg d n ρ.u) RW.base.k0_le
    RW.base.one_le_R (by linarith) (Nat.cast_nonneg n) hd0 R.y0_pos.le R.y0_sq_le
    (div_nonneg (by linarith [R.b0_pos]) RW.base.pos_de.le) hX (n0W_ge_dn3 R.hd R.hn)

theorem RegimeW.gW (R : RegimeW d n ρ) (RW : RowsW d n ρ) :
    4 * (parW d n ρ.u).k0 * ρ.y0 ^ 2 * (ρ.b0 + 1) ≤ 16 * d * n * (parW d n ρ.u).Le :=
  gW_arith _ _ _ _ _ _ (k0_parW_nonneg d n ρ.u) RW.base.k0_le R.y0_sq_le R.b0_pos.le R.b0_le (Nat.cast_nonneg n)

end Regime

/-! ## The sure ranges on the weighted path -/

/-- On a round of the weighted epoch whose mode runs, `|Y_s| ≤ y0`, and `|ξ_s|² ≤ b0 + 1` where `Y_s ≠ 0`. -/
theorem Y_pathW_sure (c : Df2Ctx d) (b0 y0 : ℝ) (π : Df2Path d) (s : ℕ) (hy0 : 0 ≤ y0)
    (h : c.mode (pathW c b0 y0 π) s = .run (c.st (pathW c b0 y0 π) s)) :
    |c.Y (pathW c b0 y0 π) s| ≤ y0 ∧ (c.Y (pathW c b0 y0 π) s ≠ 0 → π.xi s ⬝ᵥ π.xi s ≤ b0 + 1) := by
  rw [mode_pathW] at h
  rw [Y_pathW c b0 y0 π s _ h]
  obtain ⟨h1, -, h3, -⟩ := obsW_sure hy0 b0 (π.xi s)
    (c.pip (pathW c b0 y0 π) s * (π.g s (WithLp.toLp 2 (c.play (pathW c b0 y0 π) s)) + π.e s) +
      2 * (c.pip (pathW c b0 y0 π) s - 1) / c.p.eps)
  refine ⟨h1, fun hne => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hne (h3 hlt.le)

/-! ## DET at T4U -/

/-- **The hypotheses of DET at T4U with sure ranges** on the weighted path of an epoch, from the rows, the facts of
SI at T4U and the four events. -/
theorem detHypW_of (hR : RowsUW) (hS : SIFactsUW) {d n : ℕ} {ρ : RefW} {Kt : Set (E d)} {ap : ℕ → ApFun d}
    {π : Df2Path d} {m : ℕ} (R : RegimeW d n ρ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (hbody : Df2Body d (parW d n ρ.u).R Kt)
    (hap : ∀ s, ApSpec (ap s)) (hadm : ∀ s < m, AdmLoss Kt (π.g s))
    (hev : EvDetW n ρ (ctxW d n ρ Kt ap) (pathW (ctxW d n ρ Kt ap) ρ.b0 ρ.y0 π) m) :
    DetHypW (ctxW d n ρ Kt ap) (pathW (ctxW d n ρ Kt ap) ρ.b0 ρ.y0 π) m ρ := by
  have RW := hR d n ρ R
  have heps : (parW d n ρ.u).eps ≤ 1 / 2 := by linarith [R.heps]
  have B : DetBase (ctxW d n ρ Kt ap) (1 / 2) (pathW (ctxW d n ρ Kt ap) ρ.b0 ρ.y0 π) m :=
    detBaseW (u := ρ.u) rfl R.hd R.hn heps RW.base
      (fun g hg => hS d n ρ.u Kt g R.hd R.hn R.hu heps hbody hg) hm1 hmn hbody hap hadm
  have hy0 := R.y0_pos.le
  obtain ⟨evY, evLQ, evSDF, evDQ⟩ := hev
  exact
    { B with
      u_ge := R.hu
      b0_ge := R.b0_ge
      y0_nonneg := hy0
      r12w := RW.r12w
      r19ow := RW.r19ow
      r20w := RW.r20w
      r21w := RW.r21w
      r22w := RW.r22w
      r24ow := RW.r24ow
      r24bw := RW.r24bw
      clo_a := RW.clo_a
      clo_q := RW.clo_q
      gM := R.gM RW
      gS := R.gS
      gZ := R.gZ RW
      gW := R.gW RW
      Ybd := fun s hs => (Y_pathW_sure _ ρ.b0 ρ.y0 π s hy0 (B.stInv_le_tau s hs).run).1
      Ywt := fun s hs => (Y_pathW_sure _ ρ.b0 ρ.y0 π s hy0 (B.stInv_le_tau s hs).run).2
      evY := evY
      evLQ := evLQ
      evSDF := evSDF
      evDQ := evDQ }

/-- **DET at T4U with sure ranges**, from the rows and the facts of SI at T4U. -/
theorem detOf : RowsUW → SIFactsUW → DetUW := fun hR hS _ _ _ _ _ _ _ R hm1 hmn hbody hap hadm hev =>
  (detHypW_of hR hS R hm1 hmn hbody hap hadm hev).epoch_ok

end AdversarialBco.UW
