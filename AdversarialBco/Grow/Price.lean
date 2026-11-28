/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Tip

@[expose] public section

/-!
# The static dent of Route G and its price at the vertex law

Lemma PRICE-U at the vertex law `tipLaw d` (Grow/Tip.lean), the frame `A = c I`
(`frameG`), the centre `0`, `κ = g/k`, `ε = k`, `r₁ = 5 √d`, `D_M = d`:

* `dentG`, `bowlG`: the dent and the bowl;
* `price_floor`: `(1 - 3k²/d²) q(x)/2 ≤ E D(x; ·)` (`rest_floor`, `cells_reg` with rest everything);
* `price_gap`: `E (q(x) - D(x; ·))² ≤ (2^20 + 17) g (k²/d²) q(x)` (`rest_second_moment`);
* `gap_le_sphere`: `0 ≤ q(x) - D(x; θ) ≤ (g/k)((d + 2)/2 + k)` for `‖θ‖ ≤ 1/2` and every play (`dent_tangent`);
* `bowlG_le`, `dentG_lipschitz`, `dentG_convexOn`, `dentG_self`: the facts of Lemma LEGAL-S.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace AdversarialBco.Grow

open AdversarialBco.Lower

variable {d : ℕ}

/-- The static dent of tip `θ`, read at `x`. -/
noncomputable def dentG (d : ℕ) (g k : ℝ) (θ x : E d) : ℝ :=
  dent (frameG d) 0 (g / k) k (5 * Real.sqrt d) θ x

/-- The bowl `q(x) = κ φ(|x|_M)`. -/
noncomputable def bowlG (d : ℕ) (g k : ℝ) (x : E d) : ℝ :=
  bowl (frameG d) 0 (g / k) k (5 * Real.sqrt d) x

/-- The hypotheses of U-CELLS at the order `k` (the two tail inequalities and `t ≥ v`). -/
structure CellsOK (d : ℕ) (k : ℝ) : Prop where
  one_le_d : 1 ≤ d
  one_le_k : 1 ≤ k
  dk : 2048 * k ≤ d
  hv : ((d : ℝ) + 2) / d ≤ Real.sqrt (2 * k)
  h1 : Real.exp (-(k * d / (d + 2))) < k ^ 3 / (d : ℝ) ^ 3
  h2 : 2 * Real.exp (Real.sqrt (2 * k) - k * d / (d + 2)) < k ^ 3 / (d : ℝ) ^ 2

theorem CellsOK.restSet {k : ℝ} (hc : CellsOK d k) (x : E d) :
    AdversarialBco.Lower.restSet (tipLaw d) (frameG d) 0 k d d x = Set.univ :=
  restSet_tipLaw hc.one_le_d (by linarith [hc.one_le_k]) x hc.hv hc.h1 hc.h2

/-- **PRICE-U (i)**: `(1 - 3k²/d²) q(x)/2 ≤ E D(x; ·)`. -/
theorem price_floor {g k : ℝ} (hc : CellsOK d k) (hg : 0 < g) (x : E d) :
    (1 - 3 * k ^ 2 / (d : ℝ) ^ 2) * (bowlG d g k x / 2) ≤ ∫ θ, dentG d g k θ x ∂tipLaw d := by
  have hk0 : 0 < k := by linarith [hc.one_le_k]
  have h1 := rest_floor (tipLaw d) (frameG d) 0 (g / k) k d d (div_pos hg hk0) hk0 hc.dk (by linarith) x
  have h2 := cells_reg (tipLaw d) (frameG d) 0 k d d hc.one_le_k hc.dk x
  rw [hc.restSet x, setIntegral_univ] at h1
  have hrest : massRest (tipLaw d) (frameG d) 0 k d d x = 1 := by
    unfold massRest
    rw [hc.restSet x]
    simp [measureReal_def]
  rw [hrest] at h2
  unfold massReg at h2
  have hq : 0 ≤ bowlG d g k x / 2 := by
    have := bowl_ge (frameG d) 0 (g / k) k (5 * Real.sqrt d) (div_pos hg hk0).le (by positivity) x
    unfold bowlG
    have : 0 ≤ g / k * k := by positivity
    linarith
  calc (1 - 3 * k ^ 2 / (d : ℝ) ^ 2) * (bowlG d g k x / 2)
      ≤ (tipLaw d).real (cellSet (frameG d) 0 k d d x Cell.regular) * (bowlG d g k x / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hq
    _ ≤ ∫ θ, dentG d g k θ x ∂tipLaw d := h1

theorem bowlG_eq (g k : ℝ) (x : E d) : bowlG d g k x = g / k * huber (5 * Real.sqrt d) k ‖frameG d (x - 0)‖ := rfl

/-- **PRICE-U (ii)**: `E (q(x) - D(x; ·))² ≤ (2^20 + 17) g (k²/d²) q(x)`. -/
theorem price_gap {g k : ℝ} (hc : CellsOK d k) (hg : 0 < g) (x : E d) :
    ∫ θ, (bowlG d g k x - dentG d g k θ x) ^ 2 ∂tipLaw d ≤
      (2 ^ 20 + 17) * g * (k ^ 2 / (d : ℝ) ^ 2) * bowlG d g k x := by
  have hk0 : 0 < k := by linarith [hc.one_le_k]
  have hT2 : IntegrableOn (fun θ => readT (frameG d) 0 θ x ^ 2) (cellSet (frameG d) 0 k d d x Cell.tail)
      (tipLaw d) :=
    (integrable_tipLaw ((continuous_readT_tip (frameG d) 0 x).measurable.pow_const 2)).integrableOn
  have h := rest_second_moment (tipLaw d) (frameG d) 0 (g / k) k d d (div_pos hg hk0) hc.one_le_k hc.dk
    (by linarith) x hT2
  rw [hc.restSet x, setIntegral_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [bowlG_eq]
  field_simp

/-! ## The facts of Lemma LEGAL-S -/

theorem dentG_nonneg {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (θ x : E d) : 0 ≤ dentG d g k θ x :=
  dent_nonneg _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) θ x

theorem dentG_le_bowlG {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (θ x : E d) : dentG d g k θ x ≤ bowlG d g k x :=
  dent_le_bowl _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) θ x

theorem dentG_self {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (θ : E d) : dentG d g k θ θ = 0 :=
  dent_self _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) θ

theorem dentG_convexOn {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (θ : E d) : ConvexOn ℝ Set.univ (dentG d g k θ) :=
  dent_convexOn _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) θ

/-- The slope of the dent: `L_D = κ r₁ c`. -/
theorem dentG_lipschitz {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (θ x y : E d) :
    |dentG d g k θ x - dentG d g k θ y| ≤ g / k * (5 * Real.sqrt d) * frameC d * ‖x - y‖ := by
  refine (dent_lipschitz _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) θ x y).trans ?_
  have := norm_frameG_le (d := d)
  have h0 : 0 ≤ g / k * (5 * Real.sqrt d) := by positivity
  gcongr

/-- `q(x) ≤ κ (r₁ c ‖x‖ + k)`. -/
theorem bowlG_le {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (x : E d) :
    bowlG d g k x ≤ g / k * (5 * Real.sqrt d) * frameC d * ‖x‖ + g / k * k := by
  rw [bowlG_eq]
  have h := huber_le_lin (5 * Real.sqrt d) k ‖frameG d (x - 0)‖ (norm_nonneg _)
  rw [sub_zero, norm_frameG_apply] at h
  have hκ : 0 ≤ g / k := div_nonneg hg hk
  calc g / k * huber (5 * Real.sqrt d) k ‖frameG d (x - 0)‖
      ≤ g / k * (5 * Real.sqrt d * (frameC d * ‖x‖) + k) := by
        rw [sub_zero, norm_frameG_apply]
        exact mul_le_mul_of_nonneg_left h hκ
    _ = g / k * (5 * Real.sqrt d) * frameC d * ‖x‖ + g / k * k := by ring

/-- `hgen ≤ |θ|_M²/2 + k` at every play. -/
theorem hgen_le_sq (A : E d →L[ℝ] E d) (k r₁ : ℝ) (θ x : E d) :
    hgen A 0 k r₁ θ x ≤ ‖A (θ - 0)‖ ^ 2 / 2 + k := by
  have hT : readT A 0 θ x ≤ ‖A (θ - 0)‖ := by
    unfold readT
    by_cases h : ‖A (x - 0)‖ = 0
    · rw [h, div_zero]; exact norm_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)), mul_comm]
      exact real_inner_le_norm _ _
  have hT' : |readT A 0 θ x| ≤ ‖A (θ - 0)‖ := by
    unfold readT
    rw [abs_div, abs_norm]
    by_cases h : ‖A (x - 0)‖ = 0
    · rw [h, div_zero]; exact norm_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)), mul_comm]
      exact abs_real_inner_le_norm _ _
  have hT2 : readT A 0 θ x ^ 2 ≤ ‖A (θ - 0)‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hT' 2
  unfold hgen hq
  rw [inner_eq_norm_mul_readT A 0 θ x]
  split_ifs
  · nlinarith [sq_nonneg (‖A (x - 0)‖ - readT A 0 θ x)]
  · nlinarith [sq_nonneg (r₁ - readT A 0 θ x)]

/-- The uniform bound on the gap: `0 ≤ q(x) - D(x; θ) ≤ (g/k)((d + 2)/2 + k)` for `‖θ‖ ≤ 1/2`. -/
theorem gap_le_sphere (hd : 1 ≤ d) {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) {θ : E d} (hθ : ‖θ‖ ≤ 1 / 2) (x : E d) :
    bowlG d g k x - dentG d g k θ x ≤ g / k * (((d : ℝ) + 2) / 2 + k) := by
  have hκ : 0 ≤ g / k := div_nonneg hg hk
  have h1 := dent_tangent (frameG d) 0 (g / k) k (5 * Real.sqrt d) hκ hk
    (by have : (0 : ℝ) < d := by exact_mod_cast hd
        positivity) θ x
  have h2 := hgen_le_sq (frameG d) k (5 * Real.sqrt d) θ x
  have h3 : ‖frameG d (θ - 0)‖ ^ 2 ≤ (d : ℝ) + 2 := by
    rw [sub_zero, norm_frameG_apply, mul_pow, frameC_sq]
    have : ‖θ‖ ^ 2 ≤ 1 / 4 := by
      have := norm_nonneg θ
      nlinarith
    nlinarith
  have h4 : max (hgen (frameG d) 0 k (5 * Real.sqrt d) θ x) 0 ≤ ((d : ℝ) + 2) / 2 + k :=
    max_le (by linarith) (by positivity)
  unfold bowlG dentG
  nlinarith [mul_le_mul_of_nonneg_left h4 hκ]

end AdversarialBco.Grow
