/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Poly.GaussConc
public import AdversarialBco.Gauss.Concentration
public import AdversarialBco.Body.Basic

@[expose] public section

/-!
# Gaussian concentration for Lipschitz functions at the sharp constant

Proves `AdversarialBco.Poly.GaussConcSharp` of `AdversarialBco/Poly/GaussConc.lean`: `GaussConcLip (1/2)` and
`GaussConcMatrix (1/2)`, the source's thm:orlicz-lip; and, through v1.0's Maurey and
Pisier theorem `AdversarialBco.Gauss.gaussConcAt`, both forms at `2/π^2` (`gaussConcLip_two_div_pi_sq`,
`gaussConcMatrix_two_div_pi_sq`).

Route: the covariance identity along a rotation. For `F` of class `C^1` with `‖F'‖ ≤ L` on `ℝ^k`, `γ` the standard
Gaussian and `ν = γ ⊗ γ`, put `ψ(θ) = ∫ F(x) exp(l F(cos θ x + sin θ y)) dν`. Then `ψ(0) = E[F e^{lF}]`,
`ψ(π/2) = E F E e^{lF}` (`psi_zero`, `psi_pi_div_two`), and `ψ'(θ) = l ∫ F(x) e^{lF(z)} F'(z)(w) dν`
(`hasDerivAt_psi`, differentiation under the integral) with `(z, w)` the rotation of `(x, y)`. Rotation invariance of
`ν` and Fubini (`psi_deriv_eq`), then Stein's identity in `w` (`stein_shift`, from `AdversarialBco.Body.stein_dir`),
give `ψ'(θ) = -l sin θ ∫∫ e^{lF(z)} F'(cos θ z - sin θ w)(∇F(z))`, which is `≥ -l L^2 sin θ E e^{lF}` for `l ≥ 0`;
so `E[F e^{lF}] - E F E e^{lF} ≤ l L^2 E e^{lF}` (`herbst_cov`). Herbst's argument (`le_exp_of_hasDerivAt_le`,
`hasSubgaussianMGF_of_herbst`) makes `F - E F` sub-Gaussian with variance proxy `L^2`
(`hasSubgaussianMGF_sub_integral_sharp`); smoothing passes to Lipschitz functions
(`hasSubgaussianMGF_sub_integral_of_lipschitz_sharp`, the smoothing and limit lemmas of
`AdversarialBco/Gauss/Concentration.lean` with the constant changed); Chernoff and the affine image give the upper tail under
every cloud (`gaussConcAt_half`); the lower tail is the upper tail of `-F` and the matrix form is the cloud of
`√A`, with `‖√A‖^2 = ‖A‖` (`gaussConcLip_of_gaussConcAt`, `gaussConcMatrix_of_gaussConcLip`).
-/


open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped RealInnerProductSpace NNReal MatrixOrder

section
open MeasureTheory ProbabilityTheory

theorem AdversarialBco.Poly.GConc.integral_comp_rotation {k : ℕ} (θ : ℝ)
    (Φ : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → ℝ) (hΦ : Continuous Φ) :
    ∫ p, Φ (ContinuousLinearMap.rotation θ p)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) =
      ∫ p, Φ p ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  have hμ_zero : ∀ L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)), μ[L] = 0 := by
    intro L
    rw [integral_strongDual_stdGaussian]
  have h_inv := IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero (μ := μ) hμ_zero θ
  calc
    ∫ p, Φ (ContinuousLinearMap.rotation θ p) ∂(μ.prod μ)
        = ∫ r, Φ r ∂((μ.prod μ).map (ContinuousLinearMap.rotation θ)) :=
      (integral_map (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable
        hΦ.aestronglyMeasurable).symm
    _ = ∫ r, Φ r ∂(μ.prod μ) := by rw [h_inv]

end

section

theorem AdversarialBco.Poly.GConc.le_exp_of_hasDerivAt_le (M M' : ℝ → ℝ) (c : ℝ)
    (hM : ∀ x, HasDerivAt M (M' x) x) (_hpos : ∀ x, 0 < M x) (h0 : M 0 = 1)
    (hle : ∀ x, 0 ≤ x → M' x ≤ c * x * M x) :
    ∀ x, 0 ≤ x → M x ≤ Real.exp (c * x ^ 2 / 2) := by
  intro x hx
  set g := fun x => M x * Real.exp (-(c * x ^ 2 / 2)) with hg_def
  have hg_deriv : ∀ x, HasDerivAt g ((M' x - c * x * M x) * Real.exp (-(c * x ^ 2 / 2))) x := by
    intro x
    have h_exp_arg : HasDerivAt (fun x : ℝ => -(c * x ^ 2 / 2)) (-(c * x)) x := by
      have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h_mul : HasDerivAt (fun x : ℝ => (-(c / 2)) * x ^ 2) ((-(c / 2)) * (2 * x)) x :=
        HasDerivAt.const_mul (-(c / 2)) h_sq
      have h_simp : (-(c / 2)) * (2 * x) = -(c * x) := by ring
      rw [h_simp] at h_mul
      have h_eq : (fun x : ℝ => (-(c / 2)) * x ^ 2) = (fun x : ℝ => -(c * x ^ 2 / 2)) := by
        ext y; ring
      rw [h_eq] at h_mul
      exact h_mul
    have h_exp : HasDerivAt (fun x : ℝ => Real.exp (-(c * x ^ 2 / 2))) (Real.exp (-(c * x ^ 2 / 2)) * (-(c * x))) x :=
      HasDerivAt.exp h_exp_arg
    have h_prod : HasDerivAt g (M' x * Real.exp (-(c * x ^ 2 / 2)) + M x * (Real.exp (-(c * x ^ 2 / 2)) * (-(c * x)))) x :=
      HasDerivAt.mul (hM x) h_exp
    have h_simp : M' x * Real.exp (-(c * x ^ 2 / 2)) + M x * (Real.exp (-(c * x ^ 2 / 2)) * (-(c * x))) = (M' x - c * x * M x) * Real.exp (-(c * x ^ 2 / 2)) := by ring
    rw [h_simp] at h_prod
    exact h_prod
  have hg_deriv_nonpos : ∀ x, 0 < x → (M' x - c * x * M x) * Real.exp (-(c * x ^ 2 / 2)) ≤ 0 := by
    intro x hxpos
    have hle' := hle x (by linarith)
    have h_exp_pos : 0 ≤ Real.exp (-(c * x ^ 2 / 2)) := (Real.exp_pos _).le
    nlinarith
  have h_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    intro x hx
    exact (hg_deriv x).continuousAt.continuousWithinAt
  have h_deriv_on : ∀ x ∈ interior (Set.Ici (0 : ℝ)), HasDerivWithinAt g ((M' x - c * x * M x) * Real.exp (-(c * x ^ 2 / 2))) (interior (Set.Ici (0 : ℝ))) x := by
    intro x hx
    apply (hg_deriv x).hasDerivWithinAt.mono interior_subset
  have h_nonpos_on : ∀ x ∈ interior (Set.Ici (0 : ℝ)), (M' x - c * x * M x) * Real.exp (-(c * x ^ 2 / 2)) ≤ 0 := by
    intro x hx
    rw [interior_Ici] at hx
    have hxpos : 0 < x := hx
    exact hg_deriv_nonpos x hxpos
  have h_antitone : AntitoneOn g (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) h_cont h_deriv_on h_nonpos_on
  have hx_mem : x ∈ Set.Ici (0 : ℝ) := hx
  have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have h_gx_le_g0 : g x ≤ g 0 := h_antitone h0_mem hx_mem hx
  have hg0 : g 0 = 1 := by
    dsimp [g]
    rw [h0]
    simp
  rw [hg0] at h_gx_le_g0
  have h_exp_pos : 0 < Real.exp (c * x ^ 2 / 2) := Real.exp_pos _
  have h_mul := mul_le_mul_of_nonneg_right h_gx_le_g0 h_exp_pos.le
  have h_exp_mul : Real.exp (-(c * x ^ 2 / 2)) * Real.exp (c * x ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [mul_assoc, h_exp_mul, mul_one] at h_mul
  simpa [mul_comm] using h_mul

end

section
open Real

theorem AdversarialBco.Poly.GConc.sub_le_of_hasDerivAt_ge (ψ ψ' : ℝ → ℝ) (K : ℝ)
    (hψ : ∀ θ, HasDerivAt ψ (ψ' θ) θ)
    (hle : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), -(K * Real.sin θ) ≤ ψ' θ) :
    ψ 0 - ψ (π / 2) ≤ K := by
  set χ := fun θ : ℝ => ψ θ - K * Real.cos θ with hχ
  have hχ_deriv : ∀ θ, HasDerivAt χ (ψ' θ + K * Real.sin θ) θ := by
    intro θ
    have hψ_deriv := hψ θ
    have hcos_deriv := Real.hasDerivAt_cos θ
    have hKcos_deriv : HasDerivAt (fun x : ℝ => K * Real.cos x) (K * (-Real.sin θ)) θ :=
      HasDerivAt.const_mul K hcos_deriv
    have hsub : HasDerivAt (fun x : ℝ => ψ x - K * Real.cos x) (ψ' θ - (K * (-Real.sin θ))) θ :=
      HasDerivAt.sub hψ_deriv hKcos_deriv
    simpa [χ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hsub
  have hχ_deriv_nonneg : ∀ θ ∈ interior (Set.Icc (0 : ℝ) (π / 2)), 0 ≤ deriv χ θ := by
    intro θ hθ
    rw [interior_Icc] at hθ
    rcases hθ with ⟨hθl, hθr⟩
    have hle' := hle θ ⟨by linarith, by linarith⟩
    have hderiv : deriv χ θ = ψ' θ + K * Real.sin θ := by
      have h := hχ_deriv θ
      exact h.deriv
    rw [hderiv]
    linarith
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (π / 2)) := convex_Icc _ _
  have hcont : ContinuousOn χ (Set.Icc (0 : ℝ) (π / 2)) := by
    have hdiff : DifferentiableOn ℝ χ (Set.Icc (0 : ℝ) (π / 2)) := by
      intro θ hθ
      have h := hχ_deriv θ
      exact h.differentiableAt.differentiableWithinAt
    exact hdiff.continuousOn
  have hdiff_on : DifferentiableOn ℝ χ (interior (Set.Icc (0 : ℝ) (π / 2))) := by
    intro θ hθ
    have h := hχ_deriv θ
    exact h.differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn χ (Set.Icc (0 : ℝ) (π / 2)) :=
    monotoneOn_of_deriv_nonneg hconv hcont hdiff_on hχ_deriv_nonneg
  have hpi_pos : (0 : ℝ) ≤ π / 2 := by
    have h := Real.pi_pos
    linarith
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨by norm_num, hpi_pos⟩
  have hpi_mem : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨hpi_pos, by rfl⟩
  have hχ_le : χ 0 ≤ χ (π / 2) := hmono h0_mem hpi_mem (by linarith)
  have hcos0 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  have hcos_pi_div_two : Real.cos (π / 2) = 0 := Real.cos_pi_div_two
  dsimp [χ] at hχ_le
  rw [hcos0, hcos_pi_div_two] at hχ_le
  linarith

end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem AdversarialBco.Poly.GConc.stein_shift {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (L : ℝ)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (z v : EuclideanSpace ℝ (Fin k)) (θ : ℝ) :
    ∫ w, ⟪v, w⟫ * F (Real.cos θ • z - Real.sin θ • w) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) =
      -Real.sin θ * ∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) v
        ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hlin : ∀ w : EuclideanSpace ℝ (Fin k), HasFDerivAt (fun w : EuclideanSpace ℝ (Fin k) =>
      Real.cos θ • z - Real.sin θ • w) (-Real.sin θ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) w := by
    intro w
    have h := ((hasFDerivAt_id (𝕜 := ℝ) w).const_smul (Real.sin θ)).const_sub (Real.cos θ • z)
    exact h.congr_fderiv (neg_smul _ _).symm
  have hΦ : ∀ w, HasFDerivAt (fun w => F (Real.cos θ • z - Real.sin θ • w))
      (-Real.sin θ • fderiv ℝ F (Real.cos θ • z - Real.sin θ • w)) w := by
    intro w
    have h := (hdiff (Real.cos θ • z - Real.sin θ • w)).hasFDerivAt.comp w (hlin w)
    refine HasFDerivAt.congr_fderiv h ?_
    ext u
    simp
  have hgrowth : ∀ u, |F u| ≤ |F 0| + L * ‖u‖ := by
    intro u
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hL x) convex_univ
      (Set.mem_univ 0) (Set.mem_univ u)
    rw [sub_zero, Real.norm_eq_abs] at h
    have := abs_sub_abs_le_abs_sub (F u) (F 0)
    linarith
  set A := |F 0| + L * ‖z‖ + L + 1 with hA
  have hb : ∀ w, |F (Real.cos θ • z - Real.sin θ • w)| ≤ A * Real.exp (1 * ‖w‖) := by
    intro w
    have hn : ‖Real.cos θ • z - Real.sin θ • w‖ ≤ ‖z‖ + ‖w‖ := by
      calc ‖Real.cos θ • z - Real.sin θ • w‖ ≤ ‖Real.cos θ • z‖ + ‖Real.sin θ • w‖ := norm_sub_le _ _
        _ = |Real.cos θ| * ‖z‖ + |Real.sin θ| * ‖w‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * ‖z‖ + 1 * ‖w‖ := by
            gcongr
            exacts [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
        _ = ‖z‖ + ‖w‖ := by ring
    have h1 := hgrowth (Real.cos θ • z - Real.sin θ • w)
    have hex : ‖w‖ ≤ Real.exp ‖w‖ := by linarith [Real.add_one_le_exp ‖w‖]
    have he1 : 1 ≤ Real.exp ‖w‖ := Real.one_le_exp (norm_nonneg w)
    have hz0 : 0 ≤ |F 0| + L * ‖z‖ + 1 := by positivity
    rw [one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hn hL0, mul_le_mul_of_nonneg_left hex hL0,
      mul_le_mul_of_nonneg_left he1 hz0]
  have hb' : ∀ w, ‖-Real.sin θ • fderiv ℝ F (Real.cos θ • z - Real.sin θ • w)‖ ≤ A * Real.exp (1 * ‖w‖) := by
    intro w
    rw [norm_smul, Real.norm_eq_abs, abs_neg, one_mul]
    have he1 : 1 ≤ Real.exp ‖w‖ := Real.one_le_exp (norm_nonneg w)
    have hA1 : L ≤ A := by
      have : 0 ≤ |F 0| + L * ‖z‖ := by positivity
      linarith
    calc |Real.sin θ| * ‖fderiv ℝ F (Real.cos θ • z - Real.sin θ • w)‖ ≤ 1 * L :=
          mul_le_mul (Real.abs_sin_le_one θ) (hL _) (norm_nonneg _) zero_le_one
      _ = L * 1 := by ring
      _ ≤ A * Real.exp ‖w‖ := mul_le_mul hA1 he1 zero_le_one (by linarith)
  rw [AdversarialBco.Body.stein_dir (fun w => F (Real.cos θ • z - Real.sin θ • w))
    (fun w => -Real.sin θ • fderiv ℝ F (Real.cos θ • z - Real.sin θ • w)) hΦ A 1 hb hb' v]
  rw [← integral_const_mul]
  congr 1
end

section

open MeasureTheory ProbabilityTheory Real

theorem AdversarialBco.Poly.GConc.abs_le_of_norm_fderiv_le {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (L : ℝ) (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (u : EuclideanSpace ℝ (Fin k)) :
    |F u| ≤ |F 0| + L * ‖u‖ := by
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hL x) convex_univ
    (Set.mem_univ 0) (Set.mem_univ u)
  rw [sub_zero, Real.norm_eq_abs] at h
  have := abs_sub_abs_le_abs_sub (F u) (F 0)
  linarith

theorem AdversarialBco.Poly.GConc.norm_rot_le {k : ℕ} (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (x y : EuclideanSpace ℝ (Fin k)) : ‖a • x + b • y‖ ≤ ‖x‖ + ‖y‖ := by
  calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = |a| * ‖x‖ + |b| * ‖y‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖x‖ + 1 * ‖y‖ := by gcongr
    _ = ‖x‖ + ‖y‖ := by ring

theorem AdversarialBco.Poly.GConc.le_exp_self (t : ℝ) : t ≤ Real.exp t := by
  linarith [Real.add_one_le_exp t]

/-- The domination of the integrand of `ψ` and of its derivative. -/
theorem AdversarialBco.Poly.GConc.psi_bound {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (L : ℝ)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (l θ : ℝ)
    (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :
    |F p.1| * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) * (|l| * (L * (‖p.1‖ + ‖p.2‖)) + 1) ≤
      (|F 0| + L) * Real.exp (|l| * |F 0|) * (|l| * L + 1) *
        (Real.exp ((|l| * L + 2) * ‖p.1‖) * Real.exp ((|l| * L + 2) * ‖p.2‖)) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set a := |F 0| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set x := ‖p.1‖ with hx
  set y := ‖p.2‖ with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have hz : ‖Real.cos θ • p.1 + Real.sin θ • p.2‖ ≤ x + y :=
    AdversarialBco.Poly.GConc.norm_rot_le _ _ (abs_cos_le_one θ) (abs_sin_le_one θ) _ _
  have h1 : |F p.1| ≤ (a + L) * Real.exp x := by
    have := AdversarialBco.Poly.GConc.abs_le_of_norm_fderiv_le F L hF hL p.1
    have hex := AdversarialBco.Poly.GConc.le_exp_self x
    have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx0
    nlinarith
  have h2 : Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) ≤
      Real.exp (|l| * a) * (Real.exp (|l| * L * x) * Real.exp (|l| * L * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hF' := AdversarialBco.Poly.GConc.abs_le_of_norm_fderiv_le F L hF hL (Real.cos θ • p.1 + Real.sin θ • p.2)
    have : |F (Real.cos θ • p.1 + Real.sin θ • p.2)| ≤ a + L * (x + y) :=
      hF'.trans (by gcongr)
    calc l * F (Real.cos θ • p.1 + Real.sin θ • p.2) ≤ |l * F (Real.cos θ • p.1 + Real.sin θ • p.2)| :=
          le_abs_self _
      _ = |l| * |F (Real.cos θ • p.1 + Real.sin θ • p.2)| := abs_mul _ _
      _ ≤ |l| * (a + L * (x + y)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |l| * a + (|l| * L * x + |l| * L * y) := by ring
  have h3 : |l| * (L * (x + y)) + 1 ≤ (|l| * L + 1) * (Real.exp x * Real.exp y) := by
    rw [← Real.exp_add]
    have hex := AdversarialBco.Poly.GConc.le_exp_self (x + y)
    have he1 : 1 ≤ Real.exp (x + y) := Real.one_le_exp (by linarith)
    have hlL : 0 ≤ |l| * L := mul_nonneg (abs_nonneg _) hL0
    nlinarith
  have hA0 : 0 ≤ |F p.1| := abs_nonneg _
  have hE0 : 0 ≤ Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) := (Real.exp_pos _).le
  have hC0 : 0 ≤ |l| * (L * (x + y)) + 1 := by positivity
  calc |F p.1| * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) * (|l| * (L * (x + y)) + 1)
      ≤ ((a + L) * Real.exp x) * (Real.exp (|l| * a) * (Real.exp (|l| * L * x) * Real.exp (|l| * L * y))) *
          ((|l| * L + 1) * (Real.exp x * Real.exp y)) := by
        gcongr
    _ = (a + L) * (|l| * L + 1) *
          Real.exp (x + (|l| * a + (|l| * L * x + |l| * L * y)) + (x + y)) := by
        simp only [Real.exp_add]; ring
    _ ≤ (a + L) * (|l| * L + 1) * Real.exp (|l| * a + ((|l| * L + 2) * x + (|l| * L + 2) * y)) := by
        have hlL : 0 ≤ |l| * L + 1 := by positivity
        have haL : 0 ≤ a + L := by linarith
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (mul_nonneg haL hlL)
        nlinarith
    _ = (a + L) * Real.exp (|l| * a) * (|l| * L + 1) *
          (Real.exp ((|l| * L + 2) * x) * Real.exp ((|l| * L + 2) * y)) := by
        simp only [Real.exp_add]; ring

theorem AdversarialBco.Poly.GConc.psi_integrable_hasDerivAt {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (L : ℝ) (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (l θ : ℝ) :
    Integrable (fun p => F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
          (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2))))
        ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) ∧
    HasDerivAt (fun θ => ∫ p, F p.1 * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))))
      (∫ p, F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
          (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k))))) θ := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hcd : Continuous (fun x => fderiv ℝ F x) := hF.continuous_fderiv one_ne_zero
  set B := |l| * L + 2 with hB
  set K := (|F 0| + L) * Real.exp (|l| * |F 0|) * (|l| * L + 1) with hK
  set bound : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → ℝ :=
    fun p => K * (Real.exp (B * ‖p.1‖) * Real.exp (B * ‖p.2‖)) with hbound
  have hbi : Integrable bound (γ.prod γ) :=
    ((AdversarialBco.Gauss.integrable_exp_mul_norm (μ := γ) B).mul_prod
      (AdversarialBco.Gauss.integrable_exp_mul_norm (μ := γ) B)).const_mul K
  have hzc : ∀ θ : ℝ, Continuous fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      Real.cos θ • p.1 + Real.sin θ • p.2 := fun θ => by fun_prop
  have hwc : ∀ θ : ℝ, Continuous fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      -Real.sin θ • p.1 + Real.cos θ • p.2 := fun θ => by fun_prop
  have hFc : Continuous F := hF.continuous
  have hfun_c : ∀ θ : ℝ, Continuous fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      F p.1 * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) := fun θ =>
    (hFc.comp continuous_fst).mul ((continuous_const.mul (hFc.comp (hzc θ))).rexp)
  have hder_c : ∀ θ : ℝ, Continuous fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
        (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2))) :=
    fun θ => (hFc.comp continuous_fst).mul
      (((continuous_const.mul (hFc.comp (hzc θ))).rexp).mul
        (continuous_const.mul ((hcd.comp (hzc θ)).clm_apply (hwc θ))))
  have hpt : ∀ (θ : ℝ) (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)),
      |F p.1 * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2))| ≤ bound p ∧
      ‖F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
        (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)))‖ ≤
        bound p := by
    intro θ p
    have hb := AdversarialBco.Poly.GConc.psi_bound F L hF hL l θ p
    have hE0 : 0 ≤ Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) := (Real.exp_pos _).le
    have hw : ‖-Real.sin θ • p.1 + Real.cos θ • p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
      have := AdversarialBco.Poly.GConc.norm_rot_le (-Real.sin θ) (Real.cos θ)
        (by rw [abs_neg]; exact abs_sin_le_one θ) (abs_cos_le_one θ) p.1 p.2
      exact this
    have hD : |fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)| ≤
        L * (‖p.1‖ + ‖p.2‖) := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ F _).le_opNorm _).trans (mul_le_mul (hL _) hw (norm_nonneg _) hL0)
    have hP : 0 ≤ |F p.1| * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) :=
      mul_nonneg (abs_nonneg _) hE0
    constructor
    · rw [abs_mul, abs_of_nonneg hE0]
      refine le_trans ?_ hb
      have : 0 ≤ |l| * (L * (‖p.1‖ + ‖p.2‖)) := by positivity
      nlinarith
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hE0, abs_mul]
      refine le_trans ?_ hb
      have h4 : |l| * |fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)| ≤
          |l| * (L * (‖p.1‖ + ‖p.2‖)) + 1 := by
        have := mul_le_mul_of_nonneg_left hD (abs_nonneg l)
        linarith
      calc |F p.1| * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
            (|l| * |fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)|))
          = |F p.1| * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
            (|l| * |fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)|) := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 hP
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ.prod γ) (x₀ := θ) (bound := bound)
    (F := fun θ p => F p.1 * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)))
    (F' := fun θ p => F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
        (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2))))
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ => (hfun_c θ).aestronglyMeasurable)
    (hbi.mono' (hfun_c θ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact (hpt θ p).1))
    (hder_c θ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p θ' _ => (hpt θ' p).2) hbi
    (Filter.Eventually.of_forall fun p θ' _ => by
      have hzd : HasDerivAt (fun θ => Real.cos θ • p.1 + Real.sin θ • p.2)
          (-Real.sin θ' • p.1 + Real.cos θ' • p.2) θ' :=
        ((Real.hasDerivAt_cos θ').smul_const p.1).add ((Real.hasDerivAt_sin θ').smul_const p.2)
      have hFz := (hdiff _).hasFDerivAt.comp_hasDerivAt θ' hzd
      exact ((hFz.const_mul l).exp).const_mul (F p.1))
  exact h

theorem AdversarialBco.Poly.GConc.hasDerivAt_psi {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (L : ℝ)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (l θ : ℝ) :
    HasDerivAt (fun θ => ∫ p, F p.1 * Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))))
      (∫ p, F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
          (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k))))) θ :=
  (AdversarialBco.Poly.GConc.psi_integrable_hasDerivAt F L hF hL l θ).2

end

section
open scoped RealInnerProductSpace in
theorem AdversarialBco.Poly.GConc.psi_deriv_eq {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (L : ℝ)
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (l θ : ℝ) :
    ∫ p, F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
        (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)))
      ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) =
    l * ∫ z, Real.exp (l * F z) *
        ∫ w, ⟪gradient F z, w⟫ * F (Real.cos θ • z - Real.sin θ • w) ∂stdGaussian (EuclideanSpace ℝ (Fin k))
      ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  have hFc : Continuous F := hF.continuous
  have hcd : Continuous (fun x => fderiv ℝ F x) := hF.continuous_fderiv one_ne_zero
  have hgc : Continuous (gradient F) := by
    change Continuous fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ F x)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm.continuous.comp hcd
  set Φ : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) → ℝ := fun q =>
    F (Real.cos θ • q.1 - Real.sin θ • q.2) * (Real.exp (l * F q.1) * (l * ⟪gradient F q.1, q.2⟫)) with hΦ
  have hΦc : Continuous Φ :=
    (hFc.comp (by fun_prop)).mul (((continuous_const.mul (hFc.comp continuous_fst)).rexp).mul
      (continuous_const.mul ((hgc.comp continuous_fst).inner continuous_snd)))
  have hrot : (fun p => Φ (ContinuousLinearMap.rotation θ p)) = fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
      F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
        (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2))) := by
    funext p
    have e : Real.cos θ • (Real.cos θ • p.1 + Real.sin θ • p.2) -
        Real.sin θ • (-Real.sin θ • p.1 + Real.cos θ • p.2) = p.1 := by
      linear_combination (norm := module) (Real.cos_sq_add_sin_sq θ) • p.1
    simp only [Φ, ContinuousLinearMap.rotation_apply, e, gradient, InnerProductSpace.toDual_symm_apply]
  have hint : Integrable (fun p => Φ (ContinuousLinearMap.rotation θ p)) (γ.prod γ) := by
    rw [hrot]; exact (AdversarialBco.Poly.GConc.psi_integrable_hasDerivAt F L hF hL l θ).1
  have hinv := IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero (μ := γ)
    (fun L => integral_strongDual_stdGaussian L) θ
  have hΦi : Integrable Φ (γ.prod γ) := by
    rw [← hinv, integrable_map_measure (by rw [hinv]; exact hΦc.aestronglyMeasurable)
      (ContinuousLinearMap.rotation θ).continuous.measurable.aemeasurable]
    exact hint
  rw [← hrot, AdversarialBco.Poly.GConc.integral_comp_rotation θ Φ hΦc, integral_prod Φ hΦi]
  have hin : ∀ z, ∫ w, Φ (z, w) ∂γ =
      l * (Real.exp (l * F z) * ∫ w, ⟪gradient F z, w⟫ * F (Real.cos θ • z - Real.sin θ • w) ∂γ) := by
    intro z
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    funext w
    simp only [Φ]
    ring
  simp_rw [hin]
  rw [integral_const_mul]
end

section
open MeasureTheory ProbabilityTheory

theorem AdversarialBco.Poly.GConc.psi_zero {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (l : ℝ) :
    ∫ p, F p.1 * Real.exp (l * F (Real.cos 0 • p.1 + Real.sin 0 • p.2))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) =
      ∫ x, F x * Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have hcos : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  have hsin : Real.sin (0 : ℝ) = 0 := Real.sin_zero
  calc
    ∫ p, F p.1 * Real.exp (l * F (Real.cos (0 : ℝ) • p.1 + Real.sin (0 : ℝ) • p.2))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ p, F p.1 * Real.exp (l * F ((1 : ℝ) • p.1 + (0 : ℝ) • p.2))
          ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
      simp [hcos, hsin]
    _ = ∫ p, F p.1 * Real.exp (l * F p.1)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
      simp
    _ = (stdGaussian (EuclideanSpace ℝ (Fin k))).real Set.univ •
        ∫ x, F x * Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
      rw [MeasureTheory.integral_fun_fst (f := fun x => F x * Real.exp (l * F x))]
    _ = (1 : ℝ) • ∫ x, F x * Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
      rw [MeasureTheory.probReal_univ]
    _ = ∫ x, F x * Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
      simp

end

section
open MeasureTheory ProbabilityTheory Real

theorem AdversarialBco.Poly.GConc.psi_pi_div_two {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (l : ℝ) :
    ∫ p, F p.1 * Real.exp (l * F (Real.cos (π / 2) • p.1 + Real.sin (π / 2) • p.2))
        ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (stdGaussian (EuclideanSpace ℝ (Fin k)))) =
      (∫ x, F x ∂stdGaussian (EuclideanSpace ℝ (Fin k))) *
        ∫ x, Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  have h_inner : (fun (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) =>
      F p.1 * Real.exp (l * F (Real.cos (π / 2) • p.1 + Real.sin (π / 2) • p.2))) =
      (fun p => F p.1 * Real.exp (l * F p.2)) := by
    ext p
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [h_inner]
  exact MeasureTheory.integral_prod_mul F (fun x => Real.exp (l * F x))

end

section
open scoped MatrixOrder

theorem AdversarialBco.Poly.GConc.norm_toEuclideanCLM_sqrt_sq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A)‖ ^ 2 = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.2 hA
  have hR : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hRR : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA0
  rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, hR.star_eq, ← map_mul, hRR]
end

section
open MeasureTheory

theorem AdversarialBco.Poly.GConc.measureReal_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : Ω → ℝ) (t a : ℝ) (h1 : μ.real {ω | t ≤ X ω} ≤ a)
    (h2 : μ.real {ω | t ≤ -X ω} ≤ a) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * a := by
  have h_subset : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_ofPred, Set.mem_union] at hω ⊢
    rcases (le_abs.mp hω) with (h | h)
    · exact Or.inl h
    · exact Or.inr h
  have h_meas_mono : μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) :=
    measureReal_mono (μ := μ) h_subset
  have h_union_le : μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} :=
    measureReal_union_le (μ := μ) {ω | t ≤ X ω} {ω | t ≤ -X ω}
  have h_sum : μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} ≤ a + a := by
    nlinarith
  have h_a_add_a : a + a = 2 * a := by ring
  calc
    μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := h_meas_mono
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} := h_union_le
    _ ≤ a + a := h_sum
    _ = 2 * a := h_a_add_a

end

section
open MeasureTheory ProbabilityTheory

theorem AdversarialBco.Poly.GConc.hasSubgaussianMGF_of_herbst {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : NNReal)
    (hint : ∀ t, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hpos : ∀ l, 0 ≤ l → ∫ ω, X ω * Real.exp (l * X ω) ∂μ ≤ l * c * ∫ ω, Real.exp (l * X ω) ∂μ)
    (hneg : ∀ l, 0 ≤ l → ∫ ω, -X ω * Real.exp (l * -X ω) ∂μ ≤ l * c * ∫ ω, Real.exp (l * -X ω) ∂μ) :
    HasSubgaussianMGF X c μ := by
  have side : ∀ Y : Ω → ℝ, (∀ t, Integrable (fun ω => Real.exp (t * Y ω)) μ) →
      (∀ l, 0 ≤ l → ∫ ω, Y ω * Real.exp (l * Y ω) ∂μ ≤ l * c * ∫ ω, Real.exp (l * Y ω) ∂μ) →
      ∀ t, 0 ≤ t → mgf Y μ t ≤ Real.exp (c * t ^ 2 / 2) := by
    intro Y hY hle t ht
    have hset : integrableExpSet Y μ = Set.univ := Set.eq_univ_of_forall hY
    have hd : ∀ x, HasDerivAt (mgf Y μ) (∫ ω, Y ω * Real.exp (x * Y ω) ∂μ) x := fun x =>
      hasDerivAt_mgf (by rw [hset, interior_univ]; trivial)
    refine AdversarialBco.Poly.GConc.le_exp_of_hasDerivAt_le (mgf Y μ) _ c hd (fun x => mgf_pos (hY x))
      mgf_zero (fun x hx => ?_) t ht
    have h := hle x hx
    rw [mgf]
    linarith
  refine ⟨hint, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact side X hint hpos t ht
  · have hint' : ∀ s, Integrable (fun ω => Real.exp (s * -X ω)) μ := fun s => by
      have := hint (-s)
      simpa only [mul_neg, neg_mul] using this
    have h := side (fun ω => -X ω) hint' hneg (-t) (by linarith)
    have e : mgf (fun ω => -X ω) μ (-t) = mgf X μ t := by
      simp only [mgf, mul_neg, neg_mul, neg_neg]
    rw [e, neg_sq] at h
    exact h
end

namespace AdversarialBco.Poly.GConc

section fallback

/-- Both tails from the upper tail of every Lipschitz function. -/
theorem gaussConcLip_of_gaussConcAt (c : ℝ) (h : AdversarialBco.Gauss.GaussConcAt c) : GaussConcLip c := by
  intro k d b S F L hF
  obtain ⟨hint, htail⟩ := h k d b S F L hF
  obtain ⟨-, htail'⟩ := h k d b S (fun x => -F x) L hF.neg
  unfold AdversarialBco.Gauss.cloud at hint htail htail'
  refine ⟨hint, fun t ht => ?_⟩
  have h1 : ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g).real
      {x | t ≤ F x - ∫ y, F y ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g)} ≤
      Real.exp (-(c * t ^ 2) / ((L : ℝ) * ‖S‖) ^ 2) := by
    refine le_of_eq_of_le ?_ (htail t ht)
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  have h2 : ((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g).real
      {x | t ≤ -(F x - ∫ y, F y ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map fun g => b + S g))} ≤
      Real.exp (-(c * t ^ 2) / ((L : ℝ) * ‖S‖) ^ 2) := by
    refine le_of_eq_of_le ?_ (htail' t ht)
    rw [integral_neg]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  exact ⟨h1, measureReal_abs_ge_le _ _ _ _ h1 h2⟩

/-- The matrix form from the linear-map form: `multivariateGaussian m A` is the law of `m + √A g`. -/
theorem gaussConcMatrix_of_gaussConcLip (c : ℝ) (h : GaussConcLip c) : GaussConcMatrix c := by
  intro d m A hA F L hF
  obtain ⟨hint, htail⟩ := h d d m (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A)) F L hF
  refine ⟨hint, fun t ht => ?_⟩
  have h2 := (htail t ht).2
  rw [mul_pow, norm_toEuclideanCLM_sqrt_sq A hA] at h2
  exact h2

/-- Route (b), Maurey and Pisier: both forms at the constant `2/π^2`. -/
theorem gaussConcLip_two_div_pi_sq : GaussConcLip (2 / π ^ 2) :=
  gaussConcLip_of_gaussConcAt _ AdversarialBco.Gauss.gaussConcAt

theorem gaussConcMatrix_two_div_pi_sq : GaussConcMatrix (2 / π ^ 2) :=
  gaussConcMatrix_of_gaussConcLip _ gaussConcLip_two_div_pi_sq

end fallback

section sharp

/-- The Herbst inequality from the covariance identity along the rotation:
`E[F e^{lF}] - E F E e^{lF} ≤ l L^2 E e^{lF}` for `l ≥ 0`. -/
theorem herbst_cov {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (L : ℝ) (hF : ContDiff ℝ 1 F)
    (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (l : ℝ) (hl : 0 ≤ l) :
    ∫ x, F x * Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) -
        (∫ x, F x ∂stdGaussian (EuclideanSpace ℝ (Fin k))) *
          ∫ x, Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) ≤
      l * L ^ 2 * ∫ x, Real.exp (l * F x) ∂stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set H := ∫ x, Real.exp (l * F x) ∂γ with hH
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hH0 : 0 ≤ H := integral_nonneg fun x => (Real.exp_pos _).le
  have hgrad : ∀ z, ‖gradient F z‖ ≤ L := fun z => by
    rw [gradient, LinearIsometryEquiv.norm_map]; exact hL z
  -- the inner integral after Stein's identity is bounded by `L^2`
  have hI : ∀ θ z, |∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z) ∂γ| ≤ L ^ 2 := by
    intro θ z
    have h := norm_integral_le_of_norm_le_const (μ := γ)
      (f := fun w => fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z)) (C := L ^ 2)
      (Filter.Eventually.of_forall fun w => by
        calc ‖fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z)‖
            ≤ ‖fderiv ℝ F (Real.cos θ • z - Real.sin θ • w)‖ * ‖gradient F z‖ := (fderiv ℝ F _).le_opNorm _
          _ ≤ L * L := mul_le_mul (hL _) (hgrad z) (norm_nonneg _) hL0
          _ = L ^ 2 := by ring)
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
    exact h
  have hderiv : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2),
      -(l * L ^ 2 * H * Real.sin θ) ≤
        ∫ p, F p.1 * (Real.exp (l * F (Real.cos θ • p.1 + Real.sin θ • p.2)) *
          (l * fderiv ℝ F (Real.cos θ • p.1 + Real.sin θ • p.2) (-Real.sin θ • p.1 + Real.cos θ • p.2)))
          ∂(γ.prod γ) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    rw [psi_deriv_eq F L hF hL l θ]
    simp_rw [stein_shift F L hF hL _ _ θ]
    -- `J = ∫ z, e^{lF z} (-sin θ I z) ≥ -(sin θ L^2 H)`
    have hJ : -(Real.sin θ * L ^ 2 * H) ≤
        ∫ z, Real.exp (l * F z) *
          (-Real.sin θ * ∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z) ∂γ) ∂γ := by
      by_cases hint : Integrable (fun z => Real.exp (l * F z) *
          (-Real.sin θ * ∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z) ∂γ)) γ
      · have hexp : Integrable (fun z => Real.exp (l * F z)) γ :=
          AdversarialBco.Gauss.integrable_exp_of_abs_le_add_mul_norm hF.continuous.aestronglyMeasurable
            (AdversarialBco.Gauss.abs_le_of_norm_gradient_le (L := ⟨L, hL0⟩) (hF.differentiable one_ne_zero)
              hgrad) l
        have hrhs : -(Real.sin θ * L ^ 2 * H) = ∫ z, -(Real.sin θ * L ^ 2) * Real.exp (l * F z) ∂γ := by
          rw [integral_const_mul, hH]; ring
        rw [hrhs]
        refine integral_mono (hexp.const_mul _) hint fun z => ?_
        have h1 := hI θ z
        have h2 : -(L ^ 2) ≤ ∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z) ∂γ :=
          (abs_le.1 h1).1
        have h3 : ∫ w, fderiv ℝ F (Real.cos θ • z - Real.sin θ • w) (gradient F z) ∂γ ≤ L ^ 2 :=
          (abs_le.1 h1).2
        have he := (Real.exp_pos (l * F z)).le
        dsimp only
        nlinarith [mul_le_mul_of_nonneg_left h3 hs, mul_nonneg he hs]
      · rw [integral_undef hint]
        have : 0 ≤ Real.sin θ * L ^ 2 * H := by positivity
        linarith
    nlinarith [mul_le_mul_of_nonneg_left hJ hl]
  have key := sub_le_of_hasDerivAt_ge _ _ (l * L ^ 2 * H) (fun θ => hasDerivAt_psi F L hF hL l θ) hderiv
  rw [psi_zero, psi_pi_div_two] at key
  exact key

end sharp
section sharp2

/-- The sharp sub-Gaussian bound for `C^1` functions: `F - E F` has variance proxy `L^2` under the standard
Gaussian when `‖∇F‖ ≤ L`. -/
theorem hasSubgaussianMGF_sub_integral_sharp {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ} {L : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hL : ∀ x, ‖gradient F x‖ ≤ L) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin k))) (L ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hγ
  set m := ∫ y, F y ∂γ with hm
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun x => F x - m with hG
  have hfd : ∀ x, ‖fderiv ℝ F x‖ ≤ (L : ℝ) := fun x => by
    rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ _).symm]; exact hL x
  have hGc : ContDiff ℝ 1 G := hF.sub contDiff_const
  have hGd : ∀ x, ‖fderiv ℝ G x‖ ≤ (L : ℝ) := fun x => by
    rw [hG, fderiv_sub_const]; exact hfd x
  have hNc : ContDiff ℝ 1 (fun x => -G x) := hGc.neg
  have hNd : ∀ x, ‖fderiv ℝ (fun x => -G x) x‖ ≤ (L : ℝ) := fun x => by
    rw [fderiv_fun_neg, norm_neg]; exact hGd x
  have hFi : Integrable F γ :=
    AdversarialBco.Gauss.integrable_of_norm_gradient_le hF hL
  have hG0 : ∫ x, G x ∂γ = 0 := by
    rw [hG, integral_sub hFi (integrable_const m), integral_const, probReal_univ, one_smul, hm, sub_self]
  have hgrowth : ∀ x, |G x| ≤ (|F 0| + |m|) + L * ‖x‖ := fun x => by
    have h1 := AdversarialBco.Gauss.abs_le_of_norm_gradient_le (hF.differentiable one_ne_zero) hL x
    have h2 := abs_sub (F x) m
    simp only [hG]
    linarith
  have hint : ∀ t, Integrable (fun x => Real.exp (t * G x)) γ := fun t =>
    AdversarialBco.Gauss.integrable_exp_of_abs_le_add_mul_norm hGc.continuous.aestronglyMeasurable hgrowth t
  refine hasSubgaussianMGF_of_herbst γ G (L ^ 2) hint (fun l hl => ?_) (fun l hl => ?_)
  · have h := herbst_cov G L hGc hGd l hl
    rw [hG0, zero_mul, sub_zero] at h
    refine h.trans_eq ?_
    push_cast
    ring
  · have h := herbst_cov (fun x => -G x) L hNc hNd l hl
    rw [integral_neg, hG0, neg_zero, zero_mul, sub_zero] at h
    refine h.trans_eq ?_
    push_cast
    ring

/-- The sharp sub-Gaussian bound for Lipschitz functions, by smoothing (v1.0's argument with the constant changed). -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitz_sharp {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) :
    HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin k))) (L ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  set m := ∫ y, F y ∂μ with hm
  have hgrowth : ∀ x, |F x - m| ≤ (|F 0| + |m|) + L * ‖x‖ := fun x => by
    have h1 := AdversarialBco.Gauss.abs_le_of_lipschitz hF x
    have h2 := abs_sub (F x) m
    linarith
  have hmeas : AEStronglyMeasurable (fun x => F x - m) μ :=
    (hF.continuous.sub continuous_const).aestronglyMeasurable
  have hint : ∀ t, Integrable (fun x => Real.exp (t * (F x - m))) μ := fun t =>
    AdversarialBco.Gauss.integrable_exp_of_abs_le_add_mul_norm hmeas hgrowth t
  refine ⟨hint, fun t => ?_⟩
  change ∫ x, Real.exp (t * (F x - m)) ∂μ ≤ Real.exp (↑(L ^ 2) * t ^ 2 / 2)
  have hFi : Integrable F μ :=
    AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm hF.continuous.aestronglyMeasurable
      (AdversarialBco.Gauss.abs_le_of_lipschitz hF)
  refine AdversarialBco.Gauss.le_of_forall_exp_mul _ _ (2 * |t| * L) (by positivity) (Real.exp_pos _).le
    fun ε hε => ?_
  obtain ⟨G, hGc, hGL, hGF⟩ := AdversarialBco.Gauss.exists_contDiff_lipschitz_approx F L hF ε hε
  have hMP := hasSubgaussianMGF_sub_integral_sharp hGc (AdversarialBco.Gauss.norm_gradient_le_of_lipschitz hGL)
  have hGi : Integrable G μ :=
    AdversarialBco.Gauss.integrable_of_norm_gradient_le hGc (AdversarialBco.Gauss.norm_gradient_le_of_lipschitz hGL)
  have hclose := AdversarialBco.Gauss.mgf_centered_le_of_close μ F G (L * ε) t
    (fun x => by rw [abs_sub_comm]; exact hGF x) hFi hGi (hMP.integrable_exp_mul t)
  calc ∫ x, Real.exp (t * (F x - m)) ∂μ
      ≤ Real.exp (2 * |t| * (L * ε)) * ∫ x, Real.exp (t * (G x - ∫ y, G y ∂μ)) ∂μ := hclose
    _ ≤ Real.exp (2 * |t| * (L * ε)) * Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
        gcongr
        exact hMP.mgf_le t
    _ = Real.exp (2 * |t| * L * ε) * Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
        rw [← mul_assoc]

/-- The upper tail of a Lipschitz function under the standard Gaussian, sharp constant. -/
theorem tail_stdGaussian_of_lipschitz_sharp {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {r : ℝ} (hr : 0 ≤ r) :
    (stdGaussian (EuclideanSpace ℝ (Fin k))).real
        {x | (∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin k))) + r ≤ F x} ≤
      Real.exp (-(1 / 2 * r ^ 2) / (L : ℝ) ^ 2) := by
  have h := (hasSubgaussianMGF_sub_integral_of_lipschitz_sharp hF).measure_ge_le hr
  have hset : {x | (∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin k))) + r ≤ F x} =
      {x | r ≤ F x - ∫ y, F y ∂stdGaussian (EuclideanSpace ℝ (Fin k))} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  push_cast
  ring

/-- Gaussian concentration for Lipschitz functions under every cloud, upper tail, sharp constant `1/2`. -/
theorem gaussConcAt_half : AdversarialBco.Gauss.GaussConcAt (1 / 2) := by
  intro k d b S F L hF
  set μ := stdGaussian (EuclideanSpace ℝ (Fin k)) with hμ
  have hmap : Measurable (fun g => b + S g) := by fun_prop
  have hFm : AEStronglyMeasurable F (AdversarialBco.Gauss.cloud b S) := hF.continuous.aestronglyMeasurable
  have h1 : LipschitzWith ‖S‖₊ (fun g => b + S g) := by
    have := ((isometry_add_left b).lipschitzWith).comp S.lipschitzWith
    simpa [Function.comp_def] using this
  have hG : LipschitzWith (L * ‖S‖₊) (fun g => F (b + S g)) := hF.comp h1
  have hGi : Integrable (fun g => F (b + S g)) μ :=
    AdversarialBco.Gauss.integrable_of_abs_le_add_mul_norm hG.continuous.aestronglyMeasurable
      (AdversarialBco.Gauss.abs_le_of_lipschitz hG)
  have hint_eq : ∫ y, F y ∂AdversarialBco.Gauss.cloud b S = ∫ g, F (b + S g) ∂μ :=
    integral_map hmap.aemeasurable hFm
  refine ⟨(integrable_map_measure hFm hmap.aemeasurable).2 hGi, fun r hr => ?_⟩
  have hs : MeasurableSet {x | (∫ g, F (b + S g) ∂μ) + r ≤ F x} :=
    measurableSet_le measurable_const hF.continuous.measurable
  have hreal : (AdversarialBco.Gauss.cloud b S).real {x | (∫ y, F y ∂AdversarialBco.Gauss.cloud b S) + r ≤ F x} =
      μ.real {g | (∫ g', F (b + S g') ∂μ) + r ≤ F (b + S g)} := by
    rw [hint_eq]
    unfold AdversarialBco.Gauss.cloud
    rw [map_measureReal_apply hmap hs]
    rfl
  rw [hreal]
  refine (tail_stdGaussian_of_lipschitz_sharp hG hr).trans_eq ?_
  rw [NNReal.coe_mul, coe_nnnorm]

/-- The source's thm:orlicz-lip, both forms at the constant `1/2`. -/
theorem gaussConcSharp : GaussConcSharp :=
  ⟨gaussConcLip_of_gaussConcAt _ gaussConcAt_half,
    gaussConcMatrix_of_gaussConcLip _ (gaussConcLip_of_gaussConcAt _ gaussConcAt_half)⟩

end sharp2
end AdversarialBco.Poly.GConc
