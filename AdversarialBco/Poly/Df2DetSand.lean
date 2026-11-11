/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetRegion

@[expose] public section

/-!
# DET, the sandwich and the deviations

Appendix D.6 of the paper (part 1 of Q at `κ`) on the run, for a round `t ≤ τ` and a point `y` of the past
ellipsoids `S_t` (and of `B_R` for the deviations); the sums run over the rounds `u ≤ t`, index `t + 1`:

* (i) `sReg ≤ T + ν` (prop:ons:q-lower, X5), `ν = n δ_e/λ²`;
* (ii) `T ≤ sReg + (3/4) W + ν` (Taylor and prop:s-sc, X4);
* (iv) `|T̂ - T| ≤ dev` (events LQ and DQ);
* part 1 of Q: `η T ≤ η ĥqReg^κ + η dev_κ - Ω` (events LQ and DQ, with `Ω = (η κ/2) W`, `κ = 1/4`).
-/

open Matrix MeasureTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem si_at (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) : c.SIat π u :=
  H.si (H.le_tau_lt hu) (H.stOK_of_stInv (H.stInv_le_tau u hu))

theorem AAinv (H : DetBase c δ π m) {u : ℕ} (hu : u ≤ c.tau π m) :
    ((c.st π u).A * (c.st π u).Aᵀ)⁻¹ = (c.st π u).P := by
  have hI := H.stInv_le_tau u hu; rw [hI.AA]; exact Matrix.inv_eq_right_inv hI.SP

end DetBase

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem Le_pos (H : DetHyp c δ π m) : 0 < c.p.Le := by linarith [H.one_le_Le]

theorem n_ge (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
  have := (H.le_tau_lt ht).trans_le H.hmn; exact_mod_cast this

/-- A point of `S_t` is within `1/L` of `μ_u` in `λ² P_u`, `u ≤ t`. -/
theorem ss_le (H : DetHyp c δ π m) {t u : ℕ} (hu : u ≤ t) {y : Fin d → ℝ} (hy : y ∈ c.SS π t) :
    c.p.lam ^ 2 * df2Sq (c.st π u).P (y - (c.st π u).mu) ≤ 1 / c.p.Le := by
  have := hy u hu; have hL := H.Le_pos
  calc _ ≤ 1 / (2 * c.p.Le) := this
    _ ≤ 1 / c.p.Le := by gcongr; linarith

theorem Wt_nonneg (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) (y : Fin d → ℝ) : 0 ≤ c.Wt π (t + 1) y :=
  Finset.sum_nonneg fun u hu => sq_nonneg_of_psd (H.sHess_psd (by have := Finset.mem_range.1 hu; omega)) _

theorem OmT_eq (H : DetHyp c δ π m) (t : ℕ) (y : Fin d → ℝ) : c.OmT π t y = c.p.eta / 8 * c.Wt π t y := by
  unfold Df2Ctx.OmT Df2Ctx.Wt; rw [H.kap]; ring

/-- (i). -/
theorem sand_i (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.SS π t) :
    c.sReg π (t + 1) y ≤ c.TT π (t + 1) y + c.n * c.p.δe / c.p.lam ^ 2 := by
  have hterm : ∀ u ∈ Finset.range (t + 1),
      c.surr π u (WithLp.toLp 2 (c.st π u).mu) - c.surr π u (WithLp.toLp 2 y) ≤
        (c.sGrad π u ⬝ᵥ ((c.st π u).mu - y) - 1 / 4 * df2Sq (c.sHess π u) (y - (c.st π u).mu)) +
          c.p.δe / c.p.lam ^ 2 := by
    intro u hu
    have hut : u ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    refine (H.si_at (hut.trans ht)).qlower y ?_
    rw [H.AAinv (hut.trans ht)]; exact H.ss_le hut hy
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hn := H.n_ge ht
  have hδl : 0 ≤ c.p.δe / c.p.lam ^ 2 := by have := H.rows.pos_de; positivity
  have h2 : ((t + 1 : ℕ) : ℝ) * (c.p.δe / c.p.lam ^ 2) ≤ c.n * (c.p.δe / c.p.lam ^ 2) :=
    mul_le_mul_of_nonneg_right hn hδl
  have e : c.TT π (t + 1) y = ∑ u ∈ Finset.range (t + 1),
      (c.sGrad π u ⬝ᵥ ((c.st π u).mu - y) - 1 / 4 * df2Sq (c.sHess π u) (y - (c.st π u).mu)) := by
    unfold Df2Ctx.TT Df2Ctx.Lin Df2Ctx.Wt; rw [Finset.sum_sub_distrib, Finset.mul_sum]
  unfold Df2Ctx.sReg
  rw [e, mul_div_assoc]
  push_cast at h2 hsum
  linarith

/-- (ii). -/
theorem sand_ii (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.SS π t) :
    c.TT π (t + 1) y ≤ c.sReg π (t + 1) y + 3 / 4 * c.Wt π (t + 1) y + c.n * c.p.δe / c.p.lam ^ 2 := by
  have hde := H.rows.pos_de
  have hl := H.rows.pos_lam
  have hL := H.one_le_Le
  have hterm : ∀ u ∈ Finset.range (t + 1),
      c.sGrad π u ⬝ᵥ ((c.st π u).mu - y) - 1 / 4 * df2Sq (c.sHess π u) (y - (c.st π u).mu) ≤
        (c.surr π u (WithLp.toLp 2 (c.st π u).mu) - c.surr π u (WithLp.toLp 2 y)) +
          3 / 4 * df2Sq (c.sHess π u) (y - (c.st π u).mu) + c.p.δe / (4 * c.p.lam ^ 2) := by
    intro u hu
    have hut : u ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    have hsi := H.si_at (hut.trans ht)
    have hP := H.AAinv (hut.trans ht)
    have hsc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ((2 : ℝ) • df2HessM (c.surr π u) (WithLp.toLp 2 (c.st π u).mu) + c.p.δe • (c.st π u).P -
          df2HessM (c.surr π u) (WithLp.toLp 2 ((c.st π u).mu + s • (y - (c.st π u).mu)))).PosSemidef := by
      intro s hs
      have := hsi.sc ((c.st π u).mu + s • (y - (c.st π u).mu)) (c.st π u).mu ?_
      · rwa [hP] at this
      rw [hP, add_sub_cancel_left, sq_smul_arg]
      have h0 : 0 ≤ df2Sq (c.st π u).P (y - (c.st π u).mu) :=
        sq_nonneg_of_psd (H.stInv_le_tau u (hut.trans ht)).pd.posSemidef _
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      calc c.p.lam ^ 2 * (s ^ 2 * df2Sq (c.st π u).P (y - (c.st π u).mu))
          ≤ c.p.lam ^ 2 * (1 * df2Sq (c.st π u).P (y - (c.st π u).mu)) := by gcongr
        _ ≤ 1 / c.p.Le := by rw [one_mul]; exact H.ss_le hut hy
    have hlow := sandwich_lower (c.surr π u) hsi.c2 (c.st π u).mu y (c.st π u).P c.p.δe hsc
    have hrs := (H.le_rS_iff _).2 (hy u hut)
    have hrs' : c.p.δe / 2 * df2Sq (c.st π u).P (y - (c.st π u).mu) ≤ c.p.δe / (4 * c.p.lam ^ 2) := by
      calc c.p.δe / 2 * df2Sq (c.st π u).P (y - (c.st π u).mu) ≤ c.p.δe / 2 * c.rS :=
            mul_le_mul_of_nonneg_left hrs (by positivity)
        _ = c.p.δe / (4 * c.p.lam ^ 2) / c.p.Le := by unfold Df2Ctx.rS; field_simp; ring
        _ ≤ c.p.δe / (4 * c.p.lam ^ 2) := div_le_self (by positivity) hL
    change _ ≥ df2GradM (c.surr π u) (WithLp.toLp 2 (c.st π u).mu) ⬝ᵥ ((c.st π u).mu - y) -
      df2Sq (c.sHess π u) (y - (c.st π u).mu) - c.p.δe / 2 * df2Sq (c.st π u).P (y - (c.st π u).mu) at hlow
    have hg : c.sGrad π u = df2GradM (c.surr π u) (WithLp.toLp 2 (c.st π u).mu) := rfl
    rw [hg]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hn := H.n_ge ht
  have h2 : ((t + 1 : ℕ) : ℝ) * (c.p.δe / (4 * c.p.lam ^ 2)) ≤ c.n * c.p.δe / c.p.lam ^ 2 := by
    have : ((t + 1 : ℕ) : ℝ) * (c.p.δe / (4 * c.p.lam ^ 2)) ≤ c.n * (c.p.δe / (4 * c.p.lam ^ 2)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    have h3 : c.n * (c.p.δe / (4 * c.p.lam ^ 2)) ≤ c.n * c.p.δe / c.p.lam ^ 2 := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have e : c.TT π (t + 1) y = ∑ u ∈ Finset.range (t + 1),
      (c.sGrad π u ⬝ᵥ ((c.st π u).mu - y) - 1 / 4 * df2Sq (c.sHess π u) (y - (c.st π u).mu)) := by
    unfold Df2Ctx.TT Df2Ctx.Lin Df2Ctx.Wt; rw [Finset.sum_sub_distrib, Finset.mul_sum]
  unfold Df2Ctx.sReg Df2Ctx.Wt
  rw [e]
  linarith

/-- The two deviations: `T̂ - T = -X - G/4` and `ĥqReg^κ - qReg^κ = -X - (κ/2) G`, with `X` the sum of LQ and `G` that
of DQ. -/
theorem dev_split (c : Df2Ctx d) (π : Df2Path d) (t : ℕ) (y : Fin d → ℝ) :
    c.ThT π (t + 1) y - c.TT π (t + 1) y =
      -(∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu)) - 1 / 4 * c.GG π t y ∧
    c.hqReg π (t + 1) y - (c.Lin π (t + 1) y - c.p.kap / 2 * c.Wt π (t + 1) y) =
      -(∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu)) - c.p.kap / 2 * c.GG π t y := by
  have hx : ∀ u, (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu) =
      -(c.ghat π u ⬝ᵥ ((c.st π u).mu - y) - c.sGrad π u ⬝ᵥ ((c.st π u).mu - y)) := by
    intro u; simp only [sub_dotProduct, dotProduct_sub]; ring
  have hg : c.GG π t y = ∑ u ∈ Finset.range (t + 1),
      (df2Sq (c.shh π u) (y - (c.st π u).mu) - df2Sq (c.sHess π u) (y - (c.st π u).mu)) := by
    unfold Df2Ctx.GG; exact Finset.sum_congr rfl fun u _ => sq_sub _ _ _
  have hA : c.hLin π (t + 1) y - c.Lin π (t + 1) y =
      -(∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu)) := by
    unfold Df2Ctx.hLin Df2Ctx.Lin
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [hx u]; ring
  have hB : ∑ u ∈ Finset.range (t + 1), df2Sq (c.shh π u) (y - (c.st π u).mu) - c.Wt π (t + 1) y = c.GG π t y := by
    rw [hg, Finset.sum_sub_distrib]; rfl
  have hq : c.hqReg π (t + 1) y = c.hLin π (t + 1) y -
      c.p.kap / 2 * ∑ u ∈ Finset.range (t + 1), df2Sq (c.shh π u) (y - (c.st π u).mu) := by
    unfold Df2Ctx.hqReg Df2Ctx.hLin; rw [Finset.sum_sub_distrib, Finset.mul_sum]
  constructor
  · unfold Df2Ctx.ThT Df2Ctx.TT
    linear_combination hA - (1 / 4) * hB
  · linear_combination hq + hA - (c.p.kap / 2) * hB

/-- (iv): `|T̂ - T| ≤ dev`. -/
theorem sand_iv (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.SS π t)
    (hR : oNorm y ≤ c.p.R) : |c.ThT π (t + 1) y - c.TT π (t + 1) y| ≤ df2Dev c.p d c.n := by
  rw [(dev_split c π t y).1]
  have h1 := H.evLQ t ht y hR hy
  have h2 := H.evDQ t ht y hR hy
  have hl := H.rows.pos_lam; have hL := H.Le_pos
  unfold df2Dev
  have e : df2Bn c.p d c.n / (4 * c.p.Le * c.p.lam ^ 2) = 1 / 4 * (df2Bn c.p d c.n / (c.p.Le * c.p.lam ^ 2)) := by
    field_simp
  rw [e]
  calc _ ≤ |-(∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu))| +
        |1 / 4 * c.GG π t y| := abs_sub _ _
    _ ≤ _ := by rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; gcongr

/-- Part 1 of Q at `κ` with the identity (iii): `η T ≤ η ĥqReg^κ + η dev_κ - Ω`. -/
theorem q_part1 (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.SS π t)
    (hR : oNorm y ≤ c.p.R) :
    c.p.eta * c.TT π (t + 1) y ≤
      c.p.eta * c.hqReg π (t + 1) y + c.p.eta * df2DevK c.p d c.n - c.OmT π (t + 1) y := by
  have hs := (dev_split c π t y).2
  have h1 := H.evLQ t ht y hR hy
  have h2 := H.evDQ t ht y hR hy
  have hl := H.rows.pos_lam; have hL := H.Le_pos; have hη := H.rows.pos_eta
  rw [H.kap] at hs
  have hdev : c.Lin π (t + 1) y - 1 / 4 / 2 * c.Wt π (t + 1) y - c.hqReg π (t + 1) y ≤ df2DevK c.p d c.n := by
    have e : c.Lin π (t + 1) y - 1 / 4 / 2 * c.Wt π (t + 1) y - c.hqReg π (t + 1) y =
        (∑ u ∈ Finset.range (t + 1), (c.ghat π u - c.sGrad π u) ⬝ᵥ (y - (c.st π u).mu)) + 1 / 8 * c.GG π t y := by
      linarith
    rw [e]
    unfold df2DevK
    have e2 : df2Bn c.p d c.n / (8 * c.p.Le * c.p.lam ^ 2) = 1 / 8 * (df2Bn c.p d c.n / (c.p.Le * c.p.lam ^ 2)) := by
      field_simp
    rw [e2]
    have := abs_le.1 h1; have := abs_le.1 h2
    linarith
  rw [H.OmT_eq]
  unfold Df2Ctx.TT
  nlinarith

end DetHyp

end AdversarialBco.Poly
