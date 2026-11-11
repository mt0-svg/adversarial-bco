/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.APMath

@[expose] public section

/-!
# The subroutine AP: bounds on the constants of ELL-cap and on the bisection count of ELL-1

Under `0 < r̲ ≤ r ≤ R ≤ R̄`, `0 < e̲ ≤ e`, `0 ≤ tr P ≤ T` and `|w| ≤ W`, the constants `N`, `J`, `B` of `ellConsts` are
at most `nBar`, `jBar`, `bBar`, and the bisection count of ELL-1 at most `cntBar`; these bounds read only
`(d, r̲, R̄, T, W, e̲)`. Their key is `theta_cases`: `θ = min 1 (e/(3 L_F R))` is `0` (when `L_F = 0`) or lies in
`[thetaLo, 1]`.
-/

open Matrix

namespace AdversarialBco.Poly.AP

variable {d : ℕ}

/-- A lower bound on `θ = min 1 (e/(3 L_F R))` when it is positive. -/
noncomputable def thetaLo (Rb T W eb : ℝ) : ℝ := min 1 (eb / (3 * (max T 1 * (Rb + W)) * Rb))

/-- The bound on `N`. -/
noncomputable def nBar (d : ℕ) (rb Rb T W eb : ℝ) : ℕ :=
  ⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * Rb / (thetaLo Rb T W eb * rb))⌉₊ + 1

/-- The bound on `J`. -/
noncomputable def jBar (d : ℕ) (rb Rb T W eb : ℝ) : ℕ :=
  ⌈Real.logb 2 (576 * Rb ^ 2 * Real.sqrt d / (thetaLo Rb T W eb * rb ^ 2))⌉₊

/-- The bound on `B`. -/
noncomputable def bBar (d : ℕ) (rb Rb T W eb : ℝ) : ℕ :=
  ⌈Real.logb 2 (16588800 * Rb ^ 4 * Real.sqrt d / (thetaLo Rb T W eb ^ 2 * rb ^ 4)) +
    3 * d * ((jBar d rb Rb T W eb : ℝ) + 1)⌉₊

/-- The bound on the bisection count of ELL-1. -/
noncomputable def cntBar (Rb T W eb : ℝ) : ℕ := ⌈Real.logb 2 (2 * Rb * T * (Rb + W) / eb)⌉₊

theorem thetaLo_pos {Rb T W eb : ℝ} (hRb : 0 < Rb) (hW : 0 ≤ W) (heb : 0 < eb) : 0 < thetaLo Rb T W eb := by
  unfold thetaLo
  have : 0 < max T 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact lt_min zero_lt_one (by positivity)

theorem theta_cases {r R e rb Rb T W eb : ℝ} {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} (hrb : 0 < rb)
    (hr : rb ≤ r) (hrR : r ≤ R) (hR : R ≤ Rb) (heb : 0 < eb) (he : eb ≤ e) (hT0 : 0 ≤ P.trace) (hT : P.trace ≤ T)
    (hW : oNorm w ≤ W) :
    min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) = 0 ∨
      (thetaLo Rb T W eb ≤ min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) ∧
        min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) ≤ 1) := by
  have hR0 : 0 < R := by linarith
  have hN0 : 0 ≤ oNorm w := Real.sqrt_nonneg _
  have hW0 : 0 ≤ W := le_trans hN0 hW
  have hL0 : 0 ≤ P.trace * (R + oNorm w) := mul_nonneg hT0 (by linarith)
  rcases hL0.eq_or_lt with hL | hL
  · left; rw [← hL]; simp
  · right
    refine ⟨?_, min_le_left _ _⟩
    unfold thetaLo
    apply min_le_min_left
    have h1 : P.trace * (R + oNorm w) ≤ max T 1 * (Rb + W) :=
      mul_le_mul (le_trans hT (le_max_left _ _)) (by linarith) (by linarith)
        (le_trans zero_le_one (le_max_right _ _))
    have hpos : 0 < 3 * (P.trace * (R + oNorm w)) * R := by positivity
    calc eb / (3 * (max T 1 * (Rb + W)) * Rb) ≤ e / (3 * (max T 1 * (Rb + W)) * Rb) := by
          gcongr
          have : 0 < max T 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
          have : 0 < Rb := by linarith
          positivity
      _ ≤ e / (3 * (P.trace * (R + oNorm w)) * R) := by
          apply div_le_div_of_nonneg_left (by linarith) hpos
          gcongr
          exact mul_nonneg (by norm_num) (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (by linarith))

theorem ellConsts_N_le {r R e rb Rb T W eb : ℝ} {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} (hrb : 0 < rb)
    (hr : rb ≤ r) (hrR : r ≤ R) (hR : R ≤ Rb) (heb : 0 < eb) (he : eb ≤ e) (hT0 : 0 ≤ P.trace) (hT : P.trace ≤ T)
    (hW : oNorm w ≤ W) : (ellConsts r R P w e).N ≤ nBar d rb Rb T W eb := by
  have hth := theta_cases (P := P) (w := w) hrb hr hrR hR heb he hT0 hT hW
  have hlo0 : 0 < thetaLo Rb T W eb := thetaLo_pos (by linarith) (le_trans (Real.sqrt_nonneg _) hW) heb
  simp only [ellConsts, nBar]
  apply Nat.add_le_add_right
  set θ := min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) with hθ
  rcases hth with h0 | ⟨hlo, -⟩
  · rw [h0, zero_mul, div_zero, Real.log_zero, mul_zero, Nat.ceil_zero]; exact Nat.zero_le _
  · apply Nat.ceil_mono
    have hθ0 : 0 < θ := lt_of_lt_of_le hlo0 hlo
    have hr0 : 0 < r := by linarith
    have hR0 : 0 < R := by linarith
    have hRb0 : 0 < Rb := by linarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by positivity)
    gcongr

theorem j_core {R r θ θlo Rb rb s : ℝ} (hr0 : 0 < r) (hR0 : 0 < R) (hRb : R ≤ Rb) (hrb0 : 0 < rb) (hrb : rb ≤ r)
    (hs : 0 ≤ s) (hlo0 : 0 < θlo) (hθ : θ = 0 ∨ θlo ≤ θ) :
    ⌈Real.logb 2 (8 / (r * (θ * r / 2 / (36 * R ^ 2 * s))))⌉₊ ≤
      ⌈Real.logb 2 (576 * Rb ^ 2 * s / (θlo * rb ^ 2))⌉₊ := by
  rcases hs.eq_or_lt with hs0 | hs0
  · rw [← hs0]; simp
  rcases hθ with h0 | hlo
  · rw [h0]; simp
  have hθ0 : 0 < θ := lt_of_lt_of_le hlo0 hlo
  have heq : 8 / (r * (θ * r / 2 / (36 * R ^ 2 * s))) = 576 * R ^ 2 * s / (θ * r ^ 2) := by
    field_simp; ring
  rw [heq]
  apply Nat.ceil_mono
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  gcongr

theorem b_core {R r θ θlo Rb rb s K : ℝ} (hr0 : 0 < r) (hR0 : 0 < R) (hRb : R ≤ Rb) (hrb0 : 0 < rb)
    (hrb : rb ≤ r) (hs : 0 ≤ s) (hlo0 : 0 < θlo) (hθ : θ = 0 ∨ θlo ≤ θ) :
    ⌈Real.logb 2 (3 * R / (r * (θ * r / 2 / (36 * R ^ 2 * s) * (r * (θ * r / 2) / (24 * R)) / 1600 *
      (2 : ℝ) ^ (-K))))⌉₊ ≤ ⌈Real.logb 2 (16588800 * Rb ^ 4 * s / (θlo ^ 2 * rb ^ 4)) + K⌉₊ := by
  rcases hs.eq_or_lt with hs0 | hs0
  · rw [← hs0]; simp
  rcases hθ with h0 | hlo
  · rw [h0]; simp
  have hθ0 : 0 < θ := lt_of_lt_of_le hlo0 hlo
  have hpK : 0 < (2 : ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
  have heq : 3 * R / (r * (θ * r / 2 / (36 * R ^ 2 * s) * (r * (θ * r / 2) / (24 * R)) / 1600 * (2 : ℝ) ^ (-K))) =
      16588800 * R ^ 4 * s / (θ ^ 2 * r ^ 4) * (2 : ℝ) ^ K := by
    rw [Real.rpow_neg (by norm_num)]
    field_simp; ring
  rw [heq, Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  apply Nat.ceil_mono
  refine add_le_add ?_ le_rfl
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  gcongr

theorem ellConsts_J_le {r R e rb Rb T W eb : ℝ} {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} (hrb : 0 < rb)
    (hr : rb ≤ r) (hrR : r ≤ R) (hR : R ≤ Rb) (heb : 0 < eb) (he : eb ≤ e) (hT0 : 0 ≤ P.trace) (hT : P.trace ≤ T)
    (hW : oNorm w ≤ W) : (ellConsts r R P w e).J ≤ jBar d rb Rb T W eb := by
  have hth := theta_cases (P := P) (w := w) hrb hr hrR hR heb he hT0 hT hW
  have hlo0 : 0 < thetaLo Rb T W eb := thetaLo_pos (by linarith) (le_trans (Real.sqrt_nonneg _) hW) heb
  simp only [ellConsts, jBar]
  exact j_core (by linarith) (by linarith) hR hrb hr (Real.sqrt_nonneg _) hlo0 (hth.imp id (fun h => h.1))

theorem ellConsts_B_le_J {r R e rb Rb T W eb : ℝ} {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} (hrb : 0 < rb)
    (hr : rb ≤ r) (hrR : r ≤ R) (hR : R ≤ Rb) (heb : 0 < eb) (he : eb ≤ e) (hT0 : 0 ≤ P.trace) (hT : P.trace ≤ T)
    (hW : oNorm w ≤ W) :
    (ellConsts r R P w e).B ≤ ⌈Real.logb 2 (16588800 * Rb ^ 4 * Real.sqrt d / (thetaLo Rb T W eb ^ 2 * rb ^ 4)) +
      3 * d * (((ellConsts r R P w e).J : ℝ) + 1)⌉₊ := by
  have hth := theta_cases (P := P) (w := w) hrb hr hrR hR heb he hT0 hT hW
  have hlo0 : 0 < thetaLo Rb T W eb := thetaLo_pos (by linarith) (le_trans (Real.sqrt_nonneg _) hW) heb
  simp only [ellConsts]
  exact b_core (by linarith) (by linarith) hR hrb hr (Real.sqrt_nonneg _) hlo0 (hth.imp id (fun h => h.1))

theorem bBar_of_J {rb Rb T W eb : ℝ} {J B : ℕ} (hJ : J ≤ jBar d rb Rb T W eb)
    (hB : B ≤ ⌈Real.logb 2 (16588800 * Rb ^ 4 * Real.sqrt d / (thetaLo Rb T W eb ^ 2 * rb ^ 4)) +
      3 * d * ((J : ℝ) + 1)⌉₊) : B ≤ bBar d rb Rb T W eb := by
  unfold bBar
  refine le_trans hB ?_
  have hJ' : (J : ℝ) ≤ (jBar d rb Rb T W eb : ℝ) := by exact mod_cast hJ
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have h_add : (J : ℝ) + 1 ≤ (jBar d rb Rb T W eb : ℝ) + 1 := by linarith
  have h_mul : 3 * (d : ℝ) * ((J : ℝ) + 1) ≤ 3 * (d : ℝ) * ((jBar d rb Rb T W eb : ℝ) + 1) := by
    nlinarith
  have hsum : Real.logb 2 (16588800 * Rb ^ 4 * Real.sqrt d / (thetaLo Rb T W eb ^ 2 * rb ^ 4)) +
      3 * (d : ℝ) * ((J : ℝ) + 1) ≤
      Real.logb 2 (16588800 * Rb ^ 4 * Real.sqrt d / (thetaLo Rb T W eb ^ 2 * rb ^ 4)) +
      3 * (d : ℝ) * ((jBar d rb Rb T W eb : ℝ) + 1) := by
    nlinarith
  exact Nat.ceil_mono hsum

theorem ceil_logb_abs_le (x ξ R : ℝ) (_hR : 0 ≤ R) (hx : |x| ≤ 2 * R) :
    ⌈Real.logb 2 (|x| / ξ)⌉₊ ≤ ⌈Real.logb 2 (2 * R / |ξ|)⌉₊ := by
  have e : Real.logb 2 (|x| / ξ) = Real.logb 2 (|x| / |ξ|) := by
    rw [← Real.logb_abs, abs_div, abs_abs]
  rw [e]
  rcases (div_nonneg (abs_nonneg x) (abs_nonneg ξ)).eq_or_lt with h | h
  · rw [← h, Real.logb_zero, Nat.ceil_zero]; exact Nat.zero_le _
  · apply Nat.ceil_mono
    apply Real.logb_le_logb_of_le (by norm_num) h
    gcongr

theorem one_cnt_le {R p wv e Rb T W eb : ℝ} (hR : 0 ≤ R) (hRb : R ≤ Rb) (hp0 : 0 ≤ p) (hp : p ≤ T)
    (hw : |wv| ≤ W) (heb : 0 < eb) (he : eb ≤ e) :
    ⌈Real.logb 2 (2 * R / |e / (p * (R + |wv|))|)⌉₊ ≤ cntBar Rb T W eb := by
  have he0 : 0 < e := lt_of_lt_of_le heb he
  have hq : 0 ≤ p * (R + |wv|) := mul_nonneg hp0 (by positivity)
  have hRb0 : 0 ≤ Rb := le_trans hR hRb
  have hT0 : 0 ≤ T := le_trans hp0 hp
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) hw
  rw [abs_of_nonneg (div_nonneg he0.le hq), div_div_eq_mul_div]
  have h1 : 2 * R * (p * (R + |wv|)) = 2 * R * p * (R + |wv|) := by ring
  rw [h1]
  rcases (show 0 ≤ 2 * R * p * (R + |wv|) / e by positivity).eq_or_lt with h0 | h0
  · rw [← h0, Real.logb_zero, Nat.ceil_zero]; exact Nat.zero_le _
  · apply Nat.ceil_mono
    apply Real.logb_le_logb_of_le (by norm_num) h0
    gcongr

theorem abs_clamp_le (R w : ℝ) (hR : 0 ≤ R) : |max (0 - R) (min R w)| ≤ R := by
  rw [zero_sub, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_sub_le_two_mul {x y R : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) : |x - y| ≤ 2 * R := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  obtain ⟨h3, h4⟩ := abs_le.1 hy
  rw [abs_le]; constructor <;> linarith

theorem max_zero_sub (x : ℝ) : max x (0 - x) = |x| := by
  rw [zero_sub]; exact (abs_eq_max_neg).symm

theorem mul_half_rat (x : ℝ) : x * (((1 / 2 : ℚ)) : ℝ) = x / 2 := by
  push_cast; ring

end AdversarialBco.Poly.AP
