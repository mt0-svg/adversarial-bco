/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2SIFactsCore
public import AdversarialBco.Poly.Df2SIFactsExt
public import AdversarialBco.Poly.Df2SIFactsBridge
public import AdversarialBco.Poly.Df2ParBounds
public import AdversarialBco.Poly.Df2SIAt

@[expose] public section

/-!
# `Df2SIFacts`

The analytic facts of SI on the extension and the surrogate at the parameters of the learner
(`Df2Layer2.lean`, `Df2SIFacts`): X1 from the extension lemmas, X7, X2, X6, X8 from the generic surrogate
(`Df2SIFactsSurr.lean`), X4 and X3 from `Df2SIFactsCore.lean`, X5 by Taylor from below with X4 along the segment.
The state enters through `S = A⁻¹` (`Df2SIFactsBridge.lean`).
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal Matrix

namespace AdversarialBco.Poly.SIF

open AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## The parameters -/

/-- The facts of the parameter record `p` that the items read: those of `df2oPar d n δ` (`parOK`) and of the table
T4U of Theorem UW alike. -/
structure ParOK (p : Df2OPar) (d n : ℕ) : Prop where
  de0 : 0 < p.δe
  de1 : p.δe ≤ 1
  nde : (n : ℝ) * p.δe ≤ 1
  de128 : 128 * p.δe ≤ 1
  Le : 504 ≤ p.Le
  Lede : p.Le = 36 * Real.log (1 / p.δe)
  lam : p.lam = 1 / (725 * d * p.Le ^ 2)
  sig : p.sig2 = 1 / (8 * p.Le)
  eps0 : 0 < p.eps
  epsn : 1 / p.eps ≤ n
  R : p.R = 134 * d * Real.sqrt (Real.log (2 * d + 2))
  log2d : Real.log (2 * d + 2) ≤ p.Le / 36

theorem parOK {n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1) : ParOK (df2oPar d n δ) d n := by
  obtain ⟨hde0, hde1, -⟩ := df2oPar_δe_bounds d n hd hn δ hδ hδ1
  obtain ⟨hδ10, -, -⟩ := df2oPar_δ1_bounds d n hd hn δ hδ
  have he : (df2oPar d n δ).δe = 4 * (df2oPar d n δ).δ1 / (5 * n) := rfl
  have hδ1le : (df2oPar d n δ).δ1 ≤ Real.exp (-14) / ((d : ℝ) * n) ^ 3 := min_le_right _ _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨a1, a2, a3⟩ := de_arith d n _ hd1 hn1 hδ10 hδ1le
  rw [← he] at a1 a2 a3
  have hLede : (df2oPar d n δ).Le = 36 * Real.log (1 / (df2oPar d n δ).δe) := by
    show df2C0 * _ = _
    rw [df2C0]
    rfl
  have heps := df2oPar_eps_ge d n hd hn δ hδ
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have heps0 : 0 < (df2oPar d n δ).eps := lt_of_lt_of_le (by positivity) heps
  refine ⟨hde0, hde1, a3, a2, df2oPar_Le_ge d n hd hn δ hδ, hLede, ?_, rfl, heps0, ?_, rfl, ?_⟩
  · show 1 / (df2oClam * d * _ ^ 2) = _
    rw [df2oClam]
    rfl
  · calc 1 / (df2oPar d n δ).eps ≤ 1 / (1 / Real.sqrt n) := one_div_le_one_div_of_le (by positivity) heps
      _ = Real.sqrt n := one_div_one_div _
      _ ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  · rw [hLede, mul_div_cancel_left₀ _ (by norm_num : (36 : ℝ) ≠ 0)]
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ hde0]
    exact a1

/-! ## X1 -/

theorem df2Ext_eq_extOf (p : Df2OPar) (Kt : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    df2Ext p Kt g = extOf Kt p.eps (2 / p.eps) g := by
  funext x
  simp only [df2Ext, extOf, df2Pip, pipOf]
  ring

/-- X1 for `ε ∈ (0, 1/2]`. -/
theorem x1_holds (p : Df2OPar) (Kt : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hε0 : 0 < p.eps) (hε : p.eps ≤ 1 / 2) (hK : Convex ℝ Kt) (hKc : IsClosed Kt)
    (hball : Metric.closedBall 0 1 ⊆ Kt) (hg : ConvexOn ℝ Kt g) (hg01 : ∀ x ∈ Kt, g x ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ Set.univ (df2Ext p Kt g) ∧ (∀ x, 0 ≤ df2Ext p Kt g x) ∧
      (∀ x y, |df2Ext p Kt g x - df2Ext p Kt g y| ≤ 8 / p.eps * ‖x - y‖) ∧
      ∀ y ∈ df2KepsOf Kt p.eps, df2Ext p Kt g (WithLp.toLp 2 y) = g (WithLp.toLp 2 y) := by
  have hε1 : p.eps < 1 := by linarith
  have hc : (1 - p.eps) / p.eps ≤ 2 / p.eps := div_le_div_of_nonneg_right (by linarith) hε0.le
  rw [df2Ext_eq_extOf]
  refine ⟨extOf_convex Kt hK hKc hball g hg hg01 p.eps hε0 hε1 _ hc,
    fun x => extOf_nonneg Kt hK hKc hball g hg01 p.eps hε0 hε1 _ (by positivity) x, fun x y => ?_,
    fun y hy => extOf_eq_of_mem Kt hball g p.eps hε1 _ _ ?_⟩
  · calc _ ≤ (1 / p.eps + (2 + 2 / p.eps) / (1 - p.eps)) * ‖x - y‖ :=
          extOf_lip Kt hK hKc hball g hg hg01 p.eps hε0 hε1 _ hc x y
      _ ≤ 8 / p.eps * ‖x - y‖ := mul_le_mul_of_nonneg_right (ext_lip_arith _ hε0 hε) (norm_nonneg _)
  · simpa only [df2KepsOf, Set.mem_ofPred_eq, WithLp.toLp_smul] using hy

/-! ## At a state -/

/-- The hypotheses of `Df2SIAt` at a state, at the parameter record `p`. -/
structure Ctx (p : Df2OPar) (d n : ℕ) (Kt : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (mu : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hpar : ParOK p d n
  heps : p.eps ≤ 1 / 2
  hbody : Df2Body d p.R Kt
  hadm : AdmLoss Kt g
  hst : Df2StateOK p Kt mu A

namespace Ctx

variable {p : Df2OPar} {n : ℕ} {Kt : Set (EuclideanSpace ℝ (Fin d))} {g : EuclideanSpace ℝ (Fin d) → ℝ}
  {mu : Fin d → ℝ} {A : Matrix (Fin d) (Fin d) ℝ}

theorem par (h : Ctx p d n Kt g mu A) : ParOK p d n := h.hpar

theorem x1 (h : Ctx p d n Kt g mu A) :
    ConvexOn ℝ Set.univ (df2Ext p Kt g) ∧ (∀ x, 0 ≤ df2Ext p Kt g x) ∧
      (∀ x y, |df2Ext p Kt g x - df2Ext p Kt g y| ≤ 8 / p.eps * ‖x - y‖) ∧
      ∀ y ∈ df2KepsOf Kt p.eps,
        df2Ext p Kt g (WithLp.toLp 2 y) = g (WithLp.toLp 2 y) :=
  x1_holds _ Kt g h.par.eps0 h.heps h.hbody.1 h.hbody.2.1 h.hbody.2.2.1 h.hadm.1 h.hadm.2

theorem coeK (h : Ctx p d n Kt g mu A) :
    ((Real.toNNReal (8 / p.eps) : ℝ≥0) : ℝ) = 8 / p.eps :=
  Real.coe_toNNReal _ (by have := h.par.eps0; positivity)

theorem lip (h : Ctx p d n Kt g mu A) :
    LipschitzWith (Real.toNNReal (8 / p.eps)) (df2Ext p Kt g) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, dist_eq_norm, h.coeK]
    exact h.x1.2.2.1 x y

theorem lam0 (h : Ctx p d n Kt g mu A) : 0 < p.lam := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
  have := h.par.Le
  rw [h.par.lam]; positivity

theorem lam1 (h : Ctx p d n Kt g mu A) : p.lam ≤ 1 / 100 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
  have := h.par.Le
  rw [h.par.lam, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem sig0 (h : Ctx p d n Kt g mu A) : 0 ≤ p.sig2 := by
  have := h.par.Le
  rw [h.par.sig]; positivity

theorem sig4 (h : Ctx p d n Kt g mu A) : p.sig2 ≤ 1 / 4 := by
  have := h.par.Le
  rw [h.par.sig, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem AS (h : Ctx p d n Kt g mu A) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ x) = x := clm_mul_inv A h.hst.2.1 x

theorem SA (h : Ctx p d n Kt g mu A) (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (Matrix.toEuclideanCLM (𝕜 := ℝ) A x) = x := clm_inv_mul A h.hst.2.1 x

theorem normS (h : Ctx p d n Kt g mu A) (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ Real.sqrt (2 * p.sig2) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ v‖ :=
  clm_norm_le_inv A h.hst.2.1 _ (by have := h.sig0; positivity) h.hst.2.2.1 v

theorem c2 (h : Ctx p d n Kt g mu A) : ContDiff ℝ 2 (df2SurrOf p Kt g mu A) :=
  surr_contDiff _ _ h.lip _ _ _ h.AS h.SA _ h.lam0 (by linarith [h.lam1])

theorem convex (h : Ctx p d n Kt g mu A) : ConvexOn ℝ Set.univ (df2SurrOf p Kt g mu A) :=
  surr_convex _ _ h.lip h.x1.1 _ _ _ h.lam0

/-- X7. -/
theorem x7 (h : Ctx p d n Kt g mu A) :
    ContDiff ℝ 2 (df2SurrOf p Kt g mu A) ∧
      ConvexOn ℝ Set.univ (df2SurrOf p Kt g mu A) ∧
      ∀ z, df2SurrOf p Kt g mu A z ≤ df2Ext p Kt g z :=
  ⟨h.c2, h.convex, fun z => surr_le _ _ h.lip h.x1.1 _ _ _ h.lam0 (by linarith [h.lam1]) z⟩

/-- `E |A g| ≤ d`. -/
theorem int_norm_A (h : Ctx p d n Kt g mu A) :
    ∫ z, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
  have hs1 : Real.sqrt (2 * p.sig2) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith [h.sig4]
  have hb : ∀ z : EuclideanSpace ℝ (Fin d), ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ≤ (1 + ‖z‖ ^ 2) / 2 := by
    intro z
    have h1 := clm_norm_apply_le A _ (by have := h.sig0; positivity) h.hst.2.2.1 z
    have h2 : Real.sqrt (2 * p.sig2) * ‖z‖ ≤ ‖z‖ := by
      have := norm_nonneg z; nlinarith [Real.sqrt_nonneg (2 * p.sig2)]
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hI : Integrable (fun z : EuclideanSpace ℝ (Fin d) => (1 + ‖z‖ ^ 2) / 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := ((integrable_const 1).add integrable_norm_sq).div_const 2
  calc _ ≤ ∫ z, (1 + ‖z‖ ^ 2) / 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono (integrable_norm_clm _) hI hb
    _ = (1 + d) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) integrable_norm_sq, integral_const, integral_norm_sq]
        simp only [probReal_univ, smul_eq_mul, one_mul]
    _ ≤ d := by linarith

/-- X2. -/
theorem x2 (h : Ctx p d n Kt g mu A) (z : Fin d → ℝ) (hz : z ∈ df2KepsOf Kt p.eps) :
    -(10 / (p.lam * p.eps)) ≤
        df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ∧
      df2SurrOf p Kt g mu A (WithLp.toLp 2 z) ≤ 1 := by
  have hε0 := h.par.eps0
  have hε1 : p.eps < 1 := by linarith [h.heps]
  have hmem : ∀ y ∈ df2KepsOf Kt p.eps, WithLp.toLp 2 y ∈ Kt := by
    intro y hy
    have hy' : (1 - p.eps)⁻¹ • WithLp.toLp 2 y ∈ Kt := by
      simpa only [df2KepsOf, Set.mem_ofPred_eq, WithLp.toLp_smul] using hy
    have := h.hbody.1.smul_mem_of_zero_mem (h.hbody.2.2.1 (Metric.mem_closedBall_self zero_le_one)) hy'
      ⟨(by linarith : (0 : ℝ) ≤ 1 - p.eps), (by linarith : 1 - p.eps ≤ 1)⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith), one_smul] at this
  have hzK := hmem z hz
  have hmuK := hmem mu h.hst.1
  refine ⟨?_, ?_⟩
  · have hlow := surr_lower _ _ h.lip h.x1.2.1 (WithLp.toLp 2 mu) (Matrix.toEuclideanCLM (𝕜 := ℝ) A) _ h.lam0
      (WithLp.toLp 2 z)
    rw [h.coeK] at hlow
    have hR : ‖WithLp.toLp 2 z - WithLp.toLp 2 mu‖ ≤ 2 * p.R := by
      have h1 := mem_closedBall_zero_iff.mp (h.hbody.2.2.2.1 hzK)
      have h2 := mem_closedBall_zero_iff.mp (h.hbody.2.2.2.1 hmuK)
      linarith [norm_sub_le (WithLp.toLp 2 z) (WithLp.toLp 2 mu)]
    have hI := h.int_norm_A
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
    have harith := x2_arith d p.Le p.R p.eps p.lam
      (∫ z, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) hd1 h.par.Le
      h.par.lam h.par.R h.par.log2d hε0 hI
    have hK0 : 0 ≤ 8 / p.eps := by positivity
    have : 8 / p.eps * (‖WithLp.toLp 2 z - WithLp.toLp 2 mu‖ +
        ∫ z, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤
        8 / p.eps * (2 * p.R +
          ∫ z, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    show _ ≤ df2Surr _ _ _ _ _
    linarith
  · calc _ ≤ df2Ext p Kt g (WithLp.toLp 2 z) := h.x7.2.2 _
      _ = g (WithLp.toLp 2 z) := h.x1.2.2.2 z hz
      _ ≤ 1 := (h.hadm.2 _ hzK).2

/-- `|S v|² = |v|²_P`. -/
theorem normS_sq (h : Ctx p d n Kt g mu A) (v : Fin d → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (WithLp.toLp 2 v)‖ ^ 2 = df2Sq (A * Aᵀ)⁻¹ v :=
  clm_inv_norm_sq A h.hst.2.1 v

/-- The Hessian in the matrix form. -/
theorem sq_hess (f : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    df2Sq (df2HessM f z) v = fderiv ℝ (fderiv ℝ f) z (WithLp.toLp 2 v) (WithLp.toLp 2 v) :=
  (Layer2.gradM_hessM f z v).2

/-- X6. -/
theorem x6 (h : Ctx p d n Kt g mu A) (z : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) *
        Real.sqrt (2 * d * p.sig2) * df2Sq (A * Aᵀ)⁻¹ v := by
  have hb := surr_hess_bound _ _ h.lip h.x1.1 (WithLp.toLp 2 mu) _ _ h.AS h.SA _ h.lam0 (by linarith [h.lam1]) z
    (WithLp.toLp 2 v) (WithLp.toLp 2 v)
  rw [h.coeK] at hb
  rw [sq_hess]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
  have hs : Real.sqrt (2 * p.sig2) ≤ Real.sqrt (2 * d * p.sig2) :=
    Real.sqrt_le_sqrt (by nlinarith [h.sig0])
  have hc0 : 0 ≤ p.lam * (8 / p.eps) / (1 - p.lam) := by
    have := h.par.eps0; have := h.lam0; have := h.lam1
    exact div_nonneg (by positivity) (by linarith)
  have hn := h.normS (WithLp.toLp 2 v)
  set a := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (WithLp.toLp 2 v)‖
  calc _ ≤ _ := hb
    _ ≤ p.lam * (8 / p.eps) / (1 - p.lam) *
          (Real.sqrt (2 * d * p.sig2) * a * a) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact mul_le_mul_of_nonneg_right (hn.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [← h.normS_sq v]; ring

/-- X8. -/
theorem x8 (h : Ctx p d n Kt g mu A) (z : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    |df2Sq (df2HessM (df2SurrOf p Kt g mu A) z) v| ≤
      p.lam * (8 / p.eps) / (1 - p.lam) *
        Real.sqrt (d / p.δe) * (v ⬝ᵥ v) := by
  have hb := surr_hess_bound _ _ h.lip h.x1.1 (WithLp.toLp 2 mu) _ _ h.AS h.SA _ h.lam0 (by linarith [h.lam1]) z
    (WithLp.toLp 2 v) (WithLp.toLp 2 v)
  rw [h.coeK] at hb
  rw [sq_hess]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h.hd
  have hde0 := h.par.de0
  have hc0 : 0 ≤ p.lam * (8 / p.eps) / (1 - p.lam) := by
    have := h.par.eps0; have := h.lam0; have := h.lam1
    exact div_nonneg (by positivity) (by linarith)
  -- `|S v|² ≤ |v|²/δ`
  have hP : df2Sq (A * Aᵀ)⁻¹ v ≤ p.δe⁻¹ * (v ⬝ᵥ v) := by
    have := Layer2.sq_le_of_psd h.hst.2.2.2.2 v
    rwa [Layer2.sq_smul, Layer2.sq_one] at this
  have hv := norm_toLp_sq v
  set a := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (WithLp.toLp 2 v)‖ with ha
  set b := ‖WithLp.toLp 2 v‖ with hbdef
  have ha2 : a ^ 2 ≤ (Real.sqrt (d / p.δe) * b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hv, h.normS_sq v]
    calc df2Sq (A * Aᵀ)⁻¹ v ≤ p.δe⁻¹ * (v ⬝ᵥ v) := hP
      _ ≤ d / p.δe * (v ⬝ᵥ v) := by
        rw [div_eq_mul_inv, mul_comm (d : ℝ)]
        refine mul_le_mul_of_nonneg_right ?_ (by rw [← hv]; positivity)
        exact le_mul_of_one_le_right (by positivity) hd1
  have ha' : a ≤ Real.sqrt (d / p.δe) * b :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ha2
  calc _ ≤ _ := hb
    _ ≤ p.lam * (8 / p.eps) / (1 - p.lam) *
          (b * (Real.sqrt (d / p.δe) * b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha' (norm_nonneg _)) hc0
    _ = _ := by rw [← hv]; ring

/-- X4 in the quadratic form, at the state. -/
theorem x4q (h : Ctx p d n Kt g mu A) (x y v : EuclideanSpace ℝ (Fin d))
    (hxy : p.lam ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - y)‖ ^ 2 ≤ 1 / p.Le) :
    fderiv ℝ (fderiv ℝ (df2SurrOf p Kt g mu A)) x v v ≤
      2 * fderiv ℝ (fderiv ℝ (df2SurrOf p Kt g mu A)) y v v +
        p.δe * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ v‖ ^ 2 :=
  core_x4 (df2Ext p Kt g) _ h.lip h.x1.1 (WithLp.toLp 2 mu) _ _ h.AS p.lam
    p.sig2 p.Le p.δe n p.eps h.coeK h.lam0 h.lam1 h.sig0
    h.sig4 h.normS h.par.Le h.par.Lede h.par.de0 (by linarith [h.par.de128]) h.par.eps0 h.par.epsn h.par.nde x y hxy
    v

/-- X4. -/
theorem x4 (h : Ctx p d n Kt g mu A) (x y : Fin d → ℝ)
    (hxy : p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (x - y) ≤ 1 / p.Le) :
    ((2 : ℝ) • df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 y) + p.δe • (A * Aᵀ)⁻¹ -
      df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 x)).PosSemidef := by
  have hHx := (Layer2.hess_psd _ h.c2 h.convex (WithLp.toLp 2 x)).isHermitian
  have hHy := (Layer2.hess_psd _ h.c2 h.convex (WithLp.toLp 2 y)).isHermitian
  have hP : ((A * Aᵀ)⁻¹).IsHermitian := by
    have := h.hst.2.2.2.1.isHermitian.add (Layer2.psd_smul_one h.par.de0.le).isHermitian
    rwa [sub_add_cancel] at this
  have h2 : ((2 : ℝ) • df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 y) +
      p.δe • (A * Aᵀ)⁻¹).IsHermitian :=
    (hHy.smul (IsSelfAdjoint.all _)).add (hP.smul (IsSelfAdjoint.all _))
  refine Layer2.psd_of_sq_le _ _ h2 hHx fun v => ?_
  show df2Sq _ v ≤ df2Sq _ v
  rw [Layer2.sq_add, Layer2.sq_smul, Layer2.sq_smul, sq_hess, sq_hess, ← h.normS_sq v]
  have hxy' : p.lam ^ 2 *
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (WithLp.toLp 2 x - WithLp.toLp 2 y)‖ ^ 2 ≤ 1 / p.Le := by
    rw [← WithLp.toLp_sub, h.normS_sq]; exact hxy
  exact h.x4q _ _ _ hxy'

/-- X5. -/
theorem x5 (h : Ctx p d n Kt g mu A) (y : Fin d → ℝ)
    (hy : p.lam ^ 2 * df2Sq (A * Aᵀ)⁻¹ (y - mu) ≤ 1 / p.Le) :
    df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) - df2SurrOf p Kt g mu A (WithLp.toLp 2 y) ≤
      df2GradM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) ⬝ᵥ (mu - y) -
        1 / 4 * df2Sq (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu)) (y - mu) +
        p.δe / p.lam ^ 2 := by
  set s := df2SurrOf p Kt g mu A with hs
  set v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (y - mu) with hv
  set S := Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ with hS
  have hSv : ‖S v‖ ^ 2 = df2Sq (A * Aᵀ)⁻¹ (y - mu) := h.normS_sq _
  have hL0 : 0 < p.Le := by linarith [h.par.Le]
  have hl0 := h.lam0
  have hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 2 * (fderiv ℝ (fderiv ℝ s) (WithLp.toLp 2 mu) v v -
      p.δe * ‖S v‖ ^ 2) ≤ fderiv ℝ (fderiv ℝ s) (WithLp.toLp 2 mu + t • v) v v := by
    intro t ht
    have hxy : p.lam ^ 2 * ‖S (WithLp.toLp 2 mu - (WithLp.toLp 2 mu + t • v))‖ ^ 2 ≤
        1 / p.Le := by
      rw [sub_add_cancel_left, map_neg, norm_neg, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hSv]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have hQ : 0 ≤ df2Sq (A * Aᵀ)⁻¹ (y - mu) := by rw [← hSv]; positivity
      calc p.lam ^ 2 * (t ^ 2 * df2Sq (A * Aᵀ)⁻¹ (y - mu)) ≤
          p.lam ^ 2 * (1 * df2Sq (A * Aᵀ)⁻¹ (y - mu)) := by gcongr
        _ ≤ 1 / p.Le := by rw [one_mul]; exact hy
    have := h.x4q (WithLp.toLp 2 mu) (WithLp.toLp 2 mu + t • v) v hxy
    linarith
  have ht := taylor_lower s h.c2 (WithLp.toLp 2 mu) v _ hm
  have hmv : WithLp.toLp 2 mu + v = WithLp.toLp 2 y := by
    rw [hv, ← WithLp.toLp_add]; congr 1; abel
  rw [hmv] at ht
  have hg : df2GradM s (WithLp.toLp 2 mu) ⬝ᵥ (mu - y) = -(fderiv ℝ s (WithLp.toLp 2 mu) v) := by
    rw [(Layer2.gradM_hessM s _ (mu - y)).1]
    have : WithLp.toLp 2 (mu - y) = -v := by rw [hv, ← WithLp.toLp_neg]; congr 1; abel
    rw [this, map_neg]
  rw [hg, sq_hess]
  have hQ : p.δe * ‖S v‖ ^ 2 / 4 ≤ p.δe / p.lam ^ 2 := by
    have hde0 := h.par.de0
    have hQ0 : 0 ≤ ‖S v‖ ^ 2 := by positivity
    have hQ1 : ‖S v‖ ^ 2 ≤ 1 / p.lam ^ 2 := by
      rw [le_div_iff₀ (by positivity), hSv]
      calc df2Sq (A * Aᵀ)⁻¹ (y - mu) * p.lam ^ 2 ≤ 1 / p.Le := by linarith
        _ ≤ 1 := by rw [div_le_one hL0]; linarith [h.par.Le]
    calc p.δe * ‖S v‖ ^ 2 / 4 ≤ p.δe * ‖S v‖ ^ 2 := by linarith [mul_nonneg hde0.le hQ0]
      _ ≤ p.δe * (1 / p.lam ^ 2) := mul_le_mul_of_nonneg_left hQ1 hde0.le
      _ = _ := by ring
  linarith

/-- X3. -/
theorem x3 (h : Ctx p d n Kt g mu A) :
    (∫ z, df2Ext p Kt g (WithLp.toLp 2 mu + Matrix.toEuclideanCLM (𝕜 := ℝ) A z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) -
        df2SurrOf p Kt g mu A (WithLp.toLp 2 mu) ≤
      2 / p.lam *
          (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) * (A * Aᵀ)).trace +
        2 * p.δe * d / p.lam := by
  have hc := core_x3 h.hd (df2Ext p Kt g) _ h.lip h.x1.1 (WithLp.toLp 2 mu) _ _ h.AS h.SA
    p.lam p.sig2 p.Le p.δe n p.eps h.coeK
    h.par.lam h.par.sig h.normS h.par.Le h.par.Lede h.par.de0 h.par.de128 h.par.eps0 h.par.epsn h.par.nde
  have htr : ∫ z, fderiv ℝ (fderiv ℝ (df2SurrOf p Kt g mu A)) (WithLp.toLp 2 mu)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A z) (Matrix.toEuclideanCLM (𝕜 := ℝ) A z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (df2HessM (df2SurrOf p Kt g mu A) (WithLp.toLp 2 mu) * (A * Aᵀ)).trace := by
    rw [← integral_sq_mulVec]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show _ = df2Sq _ _
    rw [sq_hess, ← Matrix.toEuclideanCLM_toLp, WithLp.toLp_ofLp]
  rw [← htr]
  exact hc

end Ctx

/-- The analytic facts of SI at every parameter record `p` with `ParOK p d n` and `ε ≤ 1/2`, on a body of the
analysis and an admissible loss. -/
theorem df2SIAt_holds (p : Df2OPar) {n : ℕ} (Kt : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hpar : ParOK p d n) (heps : p.eps ≤ 1 / 2)
    (hbody : Df2Body d p.R Kt) (hadm : AdmLoss Kt g) : Df2SIAt p Kt g := by
  refine ⟨x1_holds _ Kt g hpar.eps0 heps hbody.1 hbody.2.1 hbody.2.2.1 hadm.1 hadm.2, fun mu A hst => ?_⟩
  have h : Ctx p d n Kt g mu A := ⟨hd, hn, hpar, heps, hbody, hadm, hst⟩
  exact ⟨h.x7, h.x2, h.x3, h.x6, h.x8, h.x4, h.x5⟩

/-- `Df2SIFacts`, the analytic facts of SI at the parameters of the learner: `df2SIAt_holds` at `df2oPar d n δ`. -/
theorem df2SIFacts_holds : Df2SIFacts := fun d n δ Kt g hd hn hδ hδ1 heps hbody hadm =>
  df2SIAt_holds (df2oPar d n δ) Kt g hd hn (parOK hd hn hδ hδ1) heps hbody hadm

end AdversarialBco.Poly.SIF
