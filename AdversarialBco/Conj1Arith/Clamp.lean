/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLin

@[expose] public section

/-!
# The clamp routine of Procedure PG without the spectral instruction: its interface (Lemma N)

The projection of each descent step clips `μ` to the ball of radius `κ ρ` as now (`ballClip`) and replaces the exact
clamp of the matrix part by a routine. `ClampRoutine` is what Procedure PG reads of that routine (Lemma N): from the
bounds `a < b`, a tolerance `e` with `0 < e < (b - a)/2` and a square matrix `Y`, a symmetric matrix between `a I`
and `b I` (`bounds`), at Frobenius distance at most `|Y - Z|_F + 2 e d^{1/2}` from every symmetric `Z` between `a I`
and `b I` (`near`), and measurable in `Y` (`meas`). Two routines fill it: CLAMP-N (Conj1Arith/ClampN.lean, Newton
iterations with Gauss-Jordan inverses) and CLAMP-NS (Conj1Arith/ClampNS.lean, Newton-Schulz
sign iterations). CLAMP-NS is the filler the final theorems use (Lemma N-S);
nothing outside the two filler files depends on the choice.

`pgProjR C d ρ` is the projection with the routine `C`, at the bounds `t_min`, `t_max` (`pgLD ρ`, as in `pgDom`) and
the tolerance `e' = e_P/(2 d^{1/2})`, `e_P = e_h/(10⁶ G N^{1/2})`. From the interface: it maps into `D` and
`|pgProjR C d ρ y - z| ≤ |y - z| + e_P` for `z ∈ D` (`pgProjR_mem`, `pgProjR_near`, A5d), the hypothesis of
Lemma SGD-e (Conj1Arith/SgdE.lean), and it is measurable for every `d` and `ρ` (`pgProjR_measurable`, A6), which is
what `PgMeas` reads. Lemma N (iv), continuity, is not needed: Lemma SGD-e asks for a measurable projection.

Also here, for both fillers: the Frobenius clip of step 2 (`frobClip`, `clipSym`: `S' = m I + clip_{R₀}(sym Y - m I)`,
`m = (a + b)/2`, `w = (b - a)/2`, `R₀ = d^{1/2} w`, `c₀ = R₀ + w`) and its lemmas (A4), the exact clamp of `S'` as
a map that does not increase the distance to the matrices between `a I` and `b I` (A5c), the functional calculus
of a real symmetric matrix (A2a to A2c, A2f, A2g), and the count `k` with `c₀ 2^{-k} ≤ 2 e` (`cnK`, `cnK_spec`).


Junk values. `frobClip` divides by the Frobenius norm only when it exceeds `R ≥ 0`. `pgEP`, `pgEpr` divide by `G`,
`N^{1/2}`, `d^{1/2}`, positive for `d, ρ ≥ 1`. The interface asks nothing outside `a < b`, `0 < e < (b - a)/2`.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.PG Matrix
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

variable {d : ℕ}

/-! ## Step 2: the Frobenius clip -/

/-- The Frobenius norm. -/
noncomputable def frobNorm (W : Matrix (Fin d) (Fin d) ℝ) : ℝ := Real.sqrt (∑ i, ∑ j, W i j ^ 2)

/-- The radial clip of `W` to the Frobenius ball of radius `R`. -/
noncomputable def frobClip (R : ℝ) (W : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if R < frobNorm W then (R / frobNorm W) • W else W

/-- `m = (a + b)/2`. -/
noncomputable def cnMid (a b : ℝ) : ℝ := (a + b) / 2

/-- `w = (b - a)/2`. -/
noncomputable def cnHalf (a b : ℝ) : ℝ := (b - a) / 2

/-- `R₀ = d^{1/2} w`. -/
noncomputable def cnR0 (d : ℕ) (a b : ℝ) : ℝ := Real.sqrt d * cnHalf a b

/-- `c₀ = R₀ + w`, a bound on `|l - c|` over the spectrum of `S'` and the shifts `c ∈ [a, b]`. -/
noncomputable def cnC0 (d : ℕ) (a b : ℝ) : ℝ := cnR0 d a b + cnHalf a b

/-- `S' = m I + clip_{R₀}(sym Y - m I)`. -/
noncomputable def clipSym (a b : ℝ) (Y : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cnMid a b • 1 + frobClip (cnR0 d a b) (symPart Y - cnMid a b • 1)

/-! ## The count `k` of the Newton bound, read by both fillers -/

/-- `k`, the least integer with `c₀ 2^{-k} ≤ 2 e`. -/
noncomputable def cnK (d : ℕ) (a b e : ℝ) : ℕ := ⌈Real.logb 2 (cnC0 d a b / (2 * e))⌉₊

/-- The count: `c₀ 2^{-k} ≤ 2 e`. -/
theorem cnK_spec (a b e : ℝ) (hab : a < b) (he : 0 < e) : cnC0 d a b / 2 ^ cnK d a b e ≤ 2 * e := by
  have hcnHalf_pos : 0 < cnHalf a b := by
    rw [AdversarialBco.Conj1Arith.cnHalf]
    have hpos : 0 < b - a := sub_pos.mpr hab
    positivity
  have hcnR0_nonneg : 0 ≤ cnR0 d a b := by
    rw [AdversarialBco.Conj1Arith.cnR0]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hhalf_nonneg : 0 ≤ cnHalf a b := le_of_lt hcnHalf_pos
    nlinarith
  have hcnC0_pos : 0 < cnC0 d a b := by
    rw [AdversarialBco.Conj1Arith.cnC0]
    nlinarith
  have hq_pos : 0 < cnC0 d a b / (2 * e) := by
    refine div_pos hcnC0_pos (by nlinarith)
  have h_two_gt_one : 1 < (2 : ℝ) := by norm_num
  have hk_le : Real.logb (2 : ℝ) (cnC0 d a b / (2 * e)) ≤ (cnK d a b e : ℝ) := by
    rw [AdversarialBco.Conj1Arith.cnK]
    exact Nat.le_ceil _
  have hq_le_two_pow_k : cnC0 d a b / (2 * e) ≤ (2 : ℝ) ^ (cnK d a b e : ℝ) := by
    rw [← Real.logb_le_iff_le_rpow h_two_gt_one hq_pos]
    exact hk_le
  have h_two_pow_eq : (2 : ℝ) ^ (cnK d a b e : ℝ) = (2 : ℝ) ^ cnK d a b e := by
    rw [Real.rpow_natCast]
  rw [h_two_pow_eq] at hq_le_two_pow_k
  have hpos_two_pow : 0 < (2 : ℝ) ^ cnK d a b e := by
    apply pow_pos (by norm_num) _
  rw [div_le_iff₀ hpos_two_pow]
  calc
    cnC0 d a b ≤ (2 * e) * ((2 : ℝ) ^ cnK d a b e) := by
      -- from hq_le_two_pow_k: cnC0 / (2*e) ≤ 2^k
      -- multiply both sides by (2*e) > 0
      have hpos_2e : 0 < 2 * e := by nlinarith
      rw [div_le_iff₀ hpos_2e] at hq_le_two_pow_k
      nlinarith
    _ = (2 * e) * ((2 : ℝ) ^ cnK d a b e) := rfl

/-! ## The interface -/

/-- A symmetric matrix between `a I` and `b I`. -/
def InBand (a b : ℝ) (Z : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Z.IsHermitian ∧ ∀ v : Fin d → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Z *ᵥ v) ∧ v ⬝ᵥ (Z *ᵥ v) ≤ b * (v ⬝ᵥ v)

/-- What Procedure PG reads of its clamp routine (Lemma N (i) to (iii), and measurability in place of (iv)). -/
structure ClampRoutine where
  /-- The routine, at the dimension, the bounds `a`, `b` and the tolerance `e`. -/
  run : (d : ℕ) → ℝ → ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ
  /-- Lemma N (i). -/
  bounds : ∀ (d : ℕ) (a b e : ℝ) (Y : Matrix (Fin d) (Fin d) ℝ), a < b → 0 < e → e < cnHalf a b →
    InBand a b (run d a b e Y)
  /-- Lemma N (ii) and (iii). -/
  near : ∀ (d : ℕ) (a b e : ℝ) (Y Z : Matrix (Fin d) (Fin d) ℝ), a < b → 0 < e → e < cnHalf a b → InBand a b Z →
    frobNorm (run d a b e Y - Z) ≤ frobNorm (Y - Z) + 2 * e * Real.sqrt d
  /-- Measurability in the matrix. -/
  meas : ∀ (d : ℕ) (a b e : ℝ),
    Measurable fun Y : Fin d → Fin d → ℝ => (run d a b e (Matrix.of Y) : Fin d → Fin d → ℝ)

/-- `e_P = e_h/(10⁶ G N^{1/2})`. -/
noncomputable def pgEP (d : ℕ) (ρ : ℝ) : ℝ :=
  pgEh d ρ / (10 ^ 6 * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ))

/-- `e' = e_P/(2 d^{1/2})`. -/
noncomputable def pgEpr (d : ℕ) (ρ : ℝ) : ℝ := pgEP d ρ / (2 * Real.sqrt d)

/-- The projection of a descent step with the clamp routine `C`. -/
noncomputable def pgProjR (C : ClampRoutine) (d : ℕ) (ρ : ℝ) (y : PgSp d) : PgSp d :=
  pgPack (ballClip (pgKappa * ρ) (pgMu y)) (C.run d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) (pgMat y))

/-! ## A2: the functional calculus of a real symmetric matrix -/

/-- A2a. -/
theorem cfc_mul_of_isHermitian (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    cfc (fun x => f x * g x) S = cfc f S * cfc g S := by
  have h_cont_f : ContinuousOn f (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn f
  have h_cont_g : ContinuousOn g (spectrum ℝ S) :=
    (Matrix.finite_real_spectrum (A := S)).continuousOn g
  exact cfc_mul f g S h_cont_f h_cont_g

/-- A2b. -/
theorem cfc_lin_of_isHermitian (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (f g : ℝ → ℝ) (α β : ℝ) :
    cfc (fun x => α * f x + β * g x) S = α • cfc f S + β • cfc g S := by
  have hspec : (spectrum ℝ S).Finite := Matrix.finite_real_spectrum
  have hcont_f : ContinuousOn f (spectrum ℝ S) := hspec.continuousOn _
  have hcont_g : ContinuousOn g (spectrum ℝ S) := hspec.continuousOn _
  calc
    cfc (fun x => α * f x + β * g x) S = cfc (fun x => α * f x) S + cfc (fun x => β * g x) S := by
      refine cfc_add S (fun x => α * f x) (fun x => β * g x) (hspec.continuousOn _) (hspec.continuousOn _)
    _ = (α • cfc f S) + (β • cfc g S) := by
      rw [cfc_const_mul α f S hcont_f, cfc_const_mul β g S hcont_g]
    _ = α • cfc f S + β • cfc g S := rfl

/-- A2c. -/
theorem cfc_affine_of_isHermitian (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (α β : ℝ) :
    cfc (fun x => α * x + β) S = α • S + β • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hS_selfadjoint : IsSelfAdjoint S := hS.isSelfAdjoint
  calc
    cfc (fun x => α * x + β) S = cfc (fun x => α * x) S + cfc (fun _ => β) S := by
      rw [cfc_add S (fun x => α * x) (fun _ => β)]
    _ = α • cfc (fun x => x) S + cfc (fun _ => β) S := by
      simpa using cfc_const_mul α (fun x => x) S
    _ = α • S + cfc (fun _ => β) S := by
      rw [cfc_id' ℝ S]
    _ = α • S + (algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ)) β := by
      simpa using cfc_const β S
    _ = α • S + β • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [Algebra.algebraMap_eq_smul_one]

/-- A2f: a function of `S` with values in `[a, b]` on the spectrum is in the band. -/
theorem cfc_inBand_of_isHermitian (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, a ≤ f (hS.eigenvalues i) ∧ f (hS.eigenvalues i) ≤ b) : InBand a b (cfc f S) := by
  have h_sa : IsSelfAdjoint S := hS.isSelfAdjoint
  have h_cfc_sa : IsSelfAdjoint (cfc f S) := IsSelfAdjoint.cfc (f := f) (a := S)
  refine ⟨h_cfc_sa.isHermitian, fun v => ?_⟩
  have h_dot : v ⬝ᵥ (cfc f S *ᵥ v) = ∑ i, f (hS.eigenvalues i) *
      ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) :=
    dot_cfc_mulVec_eq_sum S hS f v v
  have h_sq_sum : ∑ i, ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) = v ⬝ᵥ v := by
    rw [sum_eigen_dot_mul S hS v v]
  have h_lower : a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (cfc f S *ᵥ v) := by
    calc
      a * (v ⬝ᵥ v) = a * (∑ i, ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v))) := by rw [h_sq_sum]
      _ = ∑ i, a * ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, f (hS.eigenvalues i) * ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h_sq_nonneg : 0 ≤ (⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v) := by
          have h := sq_nonneg (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)
          nlinarith
        exact mul_le_mul_of_nonneg_right (hf i).1 h_sq_nonneg
      _ = v ⬝ᵥ (cfc f S *ᵥ v) := by rw [h_dot]
  have h_upper : v ⬝ᵥ (cfc f S *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
    calc
      v ⬝ᵥ (cfc f S *ᵥ v) = ∑ i, f (hS.eigenvalues i) *
          ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) := by rw [h_dot]
      _ ≤ ∑ i, b * ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h_sq_nonneg : 0 ≤ (⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v) := by
          have h := sq_nonneg (⇑(hS.eigenvectorBasis i) ⬝ᵥ v)
          nlinarith
        exact mul_le_mul_of_nonneg_right (hf i).2 h_sq_nonneg
      _ = b * (∑ i, ((⇑(hS.eigenvectorBasis i) ⬝ᵥ v) * (⇑(hS.eigenvectorBasis i) ⬝ᵥ v))) := by rw [Finset.mul_sum]
      _ = b * (v ⬝ᵥ v) := by rw [h_sq_sum]
  exact ⟨h_lower, h_upper⟩

/-- A2g: two functions of `S` within `ε` of each other on the spectrum are within `ε d^{1/2}` in the Frobenius
norm. -/
theorem frobNorm_cfc_sub_le (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (f g : ℝ → ℝ) (ε : ℝ)
    (hfg : ∀ i, |f (hS.eigenvalues i) - g (hS.eigenvalues i)| ≤ ε) :
    frobNorm (cfc f S - cfc g S) ≤ ε * Real.sqrt d := by
  let h : ℝ → ℝ := fun x => f x - g x
  have hsub : cfc f S - cfc g S = cfc h S := by
    have hcont_f : ContinuousOn f (spectrum ℝ S) :=
      (Matrix.finite_real_spectrum (A := S)).continuousOn f
    have hcont_g : ContinuousOn g (spectrum ℝ S) :=
      (Matrix.finite_real_spectrum (A := S)).continuousOn g
    simpa [h] using (cfc_sub f g S hcont_f hcont_g).symm
  rw [hsub]
  have h_ortho_dot : ∀ (i j : Fin d), ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h_inner := (orthonormal_iff_ite.mp hS.eigenvectorBasis.orthonormal) i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
    simpa [starRingEnd_apply, dotProduct_comm] using h_inner
  by_cases hd : Nonempty (Fin d)
  · obtain ⟨i₀⟩ := hd
    have hε_nonneg : 0 ≤ ε := by
      have h_abs_nonneg : 0 ≤ |f (hS.eigenvalues i₀) - g (hS.eigenvalues i₀)| := abs_nonneg _
      linarith [hfg i₀, h_abs_nonneg]
    have hsum_sq_eq : (∑ i : Fin d, ∑ j : Fin d, (cfc h S) i j ^ 2) =
        ∑ i : Fin d, (h (hS.eigenvalues i)) ^ 2 := by
      calc
        (∑ i : Fin d, ∑ j : Fin d, (cfc h S) i j ^ 2) =
            (∑ i : Fin d, ∑ j : Fin d, (cfc h S) i j * (cfc h S) i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        _ = ∑ i : Fin d, h (hS.eigenvalues i) *
            (⇑(hS.eigenvectorBasis i) ⬝ᵥ (cfc h S *ᵥ ⇑(hS.eigenvectorBasis i))) := by
          rw [frob_cfc_eq_sum S hS h]
        _ = ∑ i : Fin d, (h (hS.eigenvalues i)) ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have h_inner : ⇑(hS.eigenvectorBasis i) ⬝ᵥ (cfc h S *ᵥ ⇑(hS.eigenvectorBasis i)) =
              h (hS.eigenvalues i) := by
            rw [dot_cfc_mulVec_eq_sum S hS h (⇑(hS.eigenvectorBasis i)) (⇑(hS.eigenvectorBasis i))]
            calc
              (∑ j : Fin d, h (hS.eigenvalues j) *
                ((⇑(hS.eigenvectorBasis j) ⬝ᵥ ⇑(hS.eigenvectorBasis i)) *
                 (⇑(hS.eigenvectorBasis j) ⬝ᵥ ⇑(hS.eigenvectorBasis i)))) =
                  (∑ j : Fin d, h (hS.eigenvalues j) * ((if j = i then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0))) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                simp [h_ortho_dot j i]
              _ = (∑ j : Fin d, h (hS.eigenvalues j) * (if j = i then (1 : ℝ) else 0)) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                by_cases hji : j = i
                · simp [hji]
                · simp [hji]
              _ = h (hS.eigenvalues i) := by
                simp
          rw [h_inner]
          ring
    have hsum_le : (∑ i : Fin d, (h (hS.eigenvalues i)) ^ 2) ≤ (d : ℝ) * ε ^ 2 := by
      calc
        (∑ i : Fin d, (h (hS.eigenvalues i)) ^ 2) ≤ (∑ i : Fin d, ε ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hi_abs : |h (hS.eigenvalues i)| ≤ ε := by
            simpa [h] using hfg i
          have h_sq : (h (hS.eigenvalues i)) ^ 2 ≤ ε ^ 2 := by
            have h_abs := (abs_le.mp hi_abs)
            have h_left : -ε ≤ h (hS.eigenvalues i) := h_abs.1
            have h_right : h (hS.eigenvalues i) ≤ ε := h_abs.2
            nlinarith
          exact h_sq
        _ = (d : ℝ) * ε ^ 2 := by simp
    calc
      frobNorm (cfc h S) = Real.sqrt (∑ i : Fin d, ∑ j : Fin d, (cfc h S) i j ^ 2) := rfl
      _ = Real.sqrt (∑ i : Fin d, (h (hS.eigenvalues i)) ^ 2) := by rw [hsum_sq_eq]
      _ ≤ Real.sqrt ((d : ℝ) * ε ^ 2) := Real.sqrt_le_sqrt hsum_le
      _ = Real.sqrt (d : ℝ) * Real.sqrt (ε ^ 2) := by rw [Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (d : ℝ) * |ε| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (d : ℝ) * ε := by rw [abs_of_nonneg hε_nonneg]
      _ = ε * Real.sqrt d := mul_comm _ _
  · -- d = 0 case: Fin d is empty
    have hd0 : d = 0 := by
      simpa using not_nonempty_iff.mp hd
    subst hd0
    simp [frobNorm]

/-! ## A4: the Frobenius clip -/

/-- A4a. -/
theorem frobNorm_frobClip_le (R : ℝ) (hR : 0 ≤ R) (W : Matrix (Fin d) (Fin d) ℝ) : frobNorm (frobClip R W) ≤ R := by
  unfold frobClip
  split
  · case isTrue h =>
    have hfrobpos : 0 < frobNorm W := by linarith
    have hsum_nonneg : 0 ≤ ∑ i, ∑ j, W i j ^ 2 := by positivity
    have hinner : (R / frobNorm W)^2 * (frobNorm W)^2 = R^2 := by
      field_simp [hfrobpos.ne']
    have hcalc : frobNorm ((R / frobNorm W) • W) = R := by
      rw [frobNorm]
      calc
        Real.sqrt (∑ i, ∑ j, (((R / frobNorm W) • W) i j)^2) = Real.sqrt (∑ i, ∑ j, ((R / frobNorm W) * W i j)^2) := by
          simp
        _ = Real.sqrt (∑ i, ∑ j, ((R / frobNorm W)^2 * (W i j)^2)) := by
          simp [mul_pow]
        _ = Real.sqrt ((R / frobNorm W)^2 * ∑ i, ∑ j, (W i j)^2) := by
          simp [Finset.mul_sum]
        _ = Real.sqrt ((R / frobNorm W)^2 * (frobNorm W)^2) := by
          rw [frobNorm, Real.sq_sqrt hsum_nonneg]
        _ = Real.sqrt (R^2) := by rw [hinner]
        _ = R := Real.sqrt_sq hR
    exact le_of_eq hcalc
  · case isFalse h =>
    exact le_of_not_gt h

/-- A4c, the variational inequality of the clip (the pattern of `ballClip_varineq`). -/
theorem frobClip_varineq (R : ℝ) (hR : 0 ≤ R) (W Z : Matrix (Fin d) (Fin d) ℝ) (hZ : frobNorm Z ≤ R) :
    ∑ i, ∑ j, (W - frobClip R W) i j * (Z - frobClip R W) i j ≤ 0 := by
  by_cases h : R < frobNorm W
  · have hpos : 0 < frobNorm W := by
      have : 0 ≤ frobNorm W := Real.sqrt_nonneg _
      linarith
    let n := frobNorm W
    have hn_def : n = frobNorm W := rfl
    have hclip : frobClip R W = (R / n) • W := by
      rw [frobClip, hn_def, ite_eq_left h]
    rw [hclip]
    have hsub : W - (R / n) • W = (1 - R / n) • W := by
      simp [sub_smul]
    rw [hsub]
    set c := R / n with hc_def
    have hn_nonneg : 0 ≤ n := by
      rw [hn_def]
      exact Real.sqrt_nonneg _
    have h_cauchy : (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) ≤ n * frobNorm Z := by
      have h_raw := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d × Fin d))
        (λ p => W p.1 p.2) (λ p => Z p.1 p.2)
      have h_left : (∑ p : Fin d × Fin d, W p.1 p.2 * Z p.1 p.2) = (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) := by
        simpa using Finset.sum_product (Finset.univ : Finset (Fin d)) (Finset.univ : Finset (Fin d))
          (λ p : Fin d × Fin d => W p.1 p.2 * Z p.1 p.2)
      have h_right : Real.sqrt (∑ p : Fin d × Fin d, (W p.1 p.2) ^ 2) * Real.sqrt (∑ p : Fin d × Fin d, (Z p.1 p.2) ^ 2) = n * frobNorm Z := by
        rw [hn_def]
        dsimp [frobNorm]
        have h1 : (∑ p : Fin d × Fin d, (W p.1 p.2) ^ 2) = (∑ i : Fin d, ∑ j : Fin d, W i j ^ 2) := by
          simpa using Finset.sum_product (Finset.univ : Finset (Fin d)) (Finset.univ : Finset (Fin d))
            (λ p : Fin d × Fin d => (W p.1 p.2) ^ 2)
        have h2 : (∑ p : Fin d × Fin d, (Z p.1 p.2) ^ 2) = (∑ i : Fin d, ∑ j : Fin d, Z i j ^ 2) := by
          simpa using Finset.sum_product (Finset.univ : Finset (Fin d)) (Finset.univ : Finset (Fin d))
            (λ p : Fin d × Fin d => (Z p.1 p.2) ^ 2)
        rw [h1, h2]
      rw [h_left, h_right] at h_raw
      exact h_raw
    have hsum_sq_eq : (∑ i : Fin d, ∑ j : Fin d, W i j ^ 2) = n ^ 2 := by
      have hsumsq_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, W i j ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => pow_two_nonneg _
      dsimp [frobNorm] at hn_def
      rw [hn_def]
      rw [Real.sq_sqrt hsumsq_nonneg]
    have h_inner_eq : ∀ i, (∑ j : Fin d, ((1 - c) • W) i j * (Z - c • W) i j) =
        (1 - c) * (∑ j : Fin d, W i j * Z i j) - c * (1 - c) * (∑ j : Fin d, W i j ^ 2) := by
      intro i
      calc
        (∑ j : Fin d, ((1 - c) • W) i j * (Z - c • W) i j) =
            (∑ j : Fin d, ((1 - c) * W i j) * (Z i j - c * W i j)) := by
          simp [Matrix.smul_apply, Matrix.sub_apply]
        _ = (∑ j : Fin d, ((1 - c) * (W i j * Z i j) - c * (1 - c) * (W i j ^ 2))) := by
          refine Finset.sum_congr rfl (λ j _ => ?_)
          ring
        _ = (∑ j : Fin d, (1 - c) * (W i j * Z i j)) - (∑ j : Fin d, c * (1 - c) * (W i j ^ 2)) := by
          rw [Finset.sum_sub_distrib]
        _ = (1 - c) * (∑ j : Fin d, W i j * Z i j) - c * (1 - c) * (∑ j : Fin d, W i j ^ 2) := by
          simp [Finset.mul_sum]
    have h_total : (∑ i : Fin d, ∑ j : Fin d, ((1 - c) • W) i j * (Z - c • W) i j) =
        (1 - c) * ((∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) - R * n) := by
      calc
        (∑ i : Fin d, ∑ j : Fin d, ((1 - c) • W) i j * (Z - c • W) i j) =
            (∑ i : Fin d, ((1 - c) * (∑ j : Fin d, W i j * Z i j) - c * (1 - c) * (∑ j : Fin d, W i j ^ 2))) := by
          refine Finset.sum_congr rfl (λ i _ => ?_)
          rw [h_inner_eq i]
        _ = (∑ i : Fin d, (1 - c) * (∑ j : Fin d, W i j * Z i j)) -
            (∑ i : Fin d, c * (1 - c) * (∑ j : Fin d, W i j ^ 2)) := by
          rw [Finset.sum_sub_distrib]
        _ = (1 - c) * (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) -
            c * (1 - c) * (∑ i : Fin d, ∑ j : Fin d, W i j ^ 2) := by
          simp [Finset.mul_sum]
        _ = (1 - c) * (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) -
            c * (1 - c) * (n ^ 2) := by rw [hsum_sq_eq]
        _ = (1 - c) * (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) -
            (1 - c) * (c * n ^ 2) := by ring
        _ = (1 - c) * ((∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) - c * n ^ 2) := by ring
        _ = (1 - c) * ((∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) - R * n) := by
          rw [hc_def]
          field_simp [show n ≠ 0 from by linarith]
    rw [h_total]
    have h_factor_nonneg : 0 ≤ 1 - c := by
      rw [hc_def]
      have : R / n ≤ 1 := (div_le_one hpos).mpr (by linarith)
      linarith
    have h_inner_nonpos : (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) - R * n ≤ 0 := by
      have h_inner_le_nR : (∑ i : Fin d, ∑ j : Fin d, W i j * Z i j) ≤ n * R := by
        nlinarith
      linarith
    nlinarith
  · have hle : frobNorm W ≤ R := by linarith
    have hclip : frobClip R W = W := by
      rw [frobClip, ite_eq_right (not_lt.mpr hle)]
    rw [hclip, sub_self]
    simp

/-- A4d: a matrix of the band is in the Frobenius ball of radius `R₀` about `m I`. -/
theorem frobNorm_sub_mid_le (a b : ℝ) (hab : a ≤ b) (Z : Matrix (Fin d) (Fin d) ℝ) (hZ : InBand a b Z) :
    frobNorm (Z - cnMid a b • 1) ≤ cnR0 d a b := by
  set m := cnMid a b
  set w := cnHalf a b
  set W := Z - m • (1 : Matrix (Fin d) (Fin d) ℝ)
  have hw_nonneg : 0 ≤ w := by
    dsimp [w, cnHalf]
    nlinarith
  have hW : W.IsHermitian :=
    hZ.1.sub ((Matrix.isHermitian_one (n := Fin d)).smul (IsSelfAdjoint.all m))
  -- Helper lemma: for any eigenvector u i, u i ⬝ᵥ u i = 1
  have h_norm_sq_eigen (i : Fin d) : ⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i) = 1 := by
    have h_orthonorm := hW.eigenvectorBasis.orthonormal
    have h_norm : ‖hW.eigenvectorBasis i‖ = 1 := h_orthonorm.1 i
    have h_inner_eq : inner ℝ (hW.eigenvectorBasis i) (hW.eigenvectorBasis i) = ‖hW.eigenvectorBasis i‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (hW.eigenvectorBasis i)
    have h_dot_eq : inner ℝ (hW.eigenvectorBasis i) (hW.eigenvectorBasis i) = ⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i) := by
      simpa using EuclideanSpace.inner_eq_star_dotProduct (hW.eigenvectorBasis i) (hW.eigenvectorBasis i)
    rw [← h_dot_eq, h_inner_eq, h_norm]
    norm_num
  -- Use frob_cfc_eq_sum to express (frobNorm W)^2 as sum of eigenvalues squared
  have h_frob_sq_eq : (frobNorm W) ^ 2 = ∑ i : Fin d, (hW.eigenvalues i) ^ 2 := by
    calc
      (frobNorm W) ^ 2 = (Real.sqrt (∑ i, ∑ j, W i j ^ 2)) ^ 2 := rfl
      _ = ∑ i, ∑ j, W i j ^ 2 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ ∑ i, ∑ j, W i j ^ 2)]
      _ = ∑ j, ∑ k, W j k * W j k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = ∑ j, ∑ k, (cfc id W) j k * W j k := by
        simpa using (congrArg (fun M => ∑ j, ∑ k, M j k * W j k) (cfc_id ℝ W hW)).symm
      _ = ∑ i : Fin d, id (hW.eigenvalues i) * (⇑(hW.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hW.eigenvectorBasis i))) := by
        rw [frob_cfc_eq_sum W hW id W]
      _ = ∑ i : Fin d, (hW.eigenvalues i) * (⇑(hW.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hW.eigenvectorBasis i))) := by simp
      _ = ∑ i : Fin d, (hW.eigenvalues i) * ((hW.eigenvalues i) * (⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hW.mulVec_eigenvectorBasis i]
        simp [dotProduct_smul, smul_eq_mul]
      _ = ∑ i : Fin d, (hW.eigenvalues i) * ((hW.eigenvalues i) * 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h_norm_sq_eigen i]
      _ = ∑ i : Fin d, (hW.eigenvalues i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  -- Bound each eigenvalue using InBand
  have h_eigen_bound (i : Fin d) : (hW.eigenvalues i) ^ 2 ≤ w ^ 2 := by
    have hZbounds := hZ.2 (⇑(hW.eigenvectorBasis i))
    rcases hZbounds with ⟨h_low, h_high⟩
    rw [h_norm_sq_eigen i] at h_low h_high
    simp at h_low h_high
    -- a ≤ v ⬝ᵥ (Z *ᵥ v) ≤ b where v = u i
    have hZv : ⇑(hW.eigenvectorBasis i) ⬝ᵥ (Z *ᵥ ⇑(hW.eigenvectorBasis i)) = (hW.eigenvalues i) + m := by
      calc
        ⇑(hW.eigenvectorBasis i) ⬝ᵥ (Z *ᵥ ⇑(hW.eigenvectorBasis i)) =
            ⇑(hW.eigenvectorBasis i) ⬝ᵥ ((W + m • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ⇑(hW.eigenvectorBasis i)) := by
          dsimp [W]
          rw [sub_add_cancel]
        _ = ⇑(hW.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hW.eigenvectorBasis i) + (m • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ⇑(hW.eigenvectorBasis i)) := by
          rw [add_mulVec]
        _ = ⇑(hW.eigenvectorBasis i) ⬝ᵥ (W *ᵥ ⇑(hW.eigenvectorBasis i)) + ⇑(hW.eigenvectorBasis i) ⬝ᵥ ((m • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ⇑(hW.eigenvectorBasis i)) := by
          rw [dotProduct_add]
        _ = ⇑(hW.eigenvectorBasis i) ⬝ᵥ ((hW.eigenvalues i) • ⇑(hW.eigenvectorBasis i)) + ⇑(hW.eigenvectorBasis i) ⬝ᵥ (m • ⇑(hW.eigenvectorBasis i)) := by
          rw [hW.mulVec_eigenvectorBasis i, Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = (hW.eigenvalues i) * (⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i)) + m * (⇑(hW.eigenvectorBasis i) ⬝ᵥ ⇑(hW.eigenvectorBasis i)) := by
          simp [dotProduct_smul, smul_eq_mul]
        _ = (hW.eigenvalues i) * 1 + m * 1 := by rw [h_norm_sq_eigen i]
        _ = (hW.eigenvalues i) + m := by ring
    rw [hZv] at h_low h_high
    -- a ≤ λ + m ≤ b → -w ≤ λ ≤ w
    have h_low' : -w ≤ hW.eigenvalues i := by
      dsimp [w, cnHalf, m, cnMid] at *
      linarith
    have h_high' : hW.eigenvalues i ≤ w := by
      dsimp [w, cnHalf, m, cnMid] at *
      linarith
    nlinarith [hw_nonneg, h_low', h_high']
  -- Sum the bounds: (frobNorm W)^2 ≤ d * w^2
  have h_sum_sq : (frobNorm W) ^ 2 ≤ (d : ℝ) * w ^ 2 := by
    rw [h_frob_sq_eq]
    calc
      ∑ i : Fin d, (hW.eigenvalues i) ^ 2 ≤ ∑ i : Fin d, w ^ 2 :=
        Finset.sum_le_sum fun i _ => h_eigen_bound i
      _ = (Finset.card (Finset.univ : Finset (Fin d))) • (w ^ 2) := by
        simp [Finset.sum_const]
      _ = (d : ℝ) • (w ^ 2) := by simp
      _ = (d : ℝ) * (w ^ 2) := by simp
  -- Take square roots
  have h_nonneg_frob : 0 ≤ frobNorm W := Real.sqrt_nonneg _
  have h_nonneg_rhs : 0 ≤ Real.sqrt (d : ℝ) * w := by
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    nlinarith
  rw [show cnR0 d a b = Real.sqrt (d : ℝ) * w from rfl]
  have h_sq_le : (frobNorm W) ^ 2 ≤ (Real.sqrt (d : ℝ) * w) ^ 2 := by
    calc
      (frobNorm W) ^ 2 ≤ (d : ℝ) * w ^ 2 := h_sum_sq
      _ = (Real.sqrt (d : ℝ)) ^ 2 * w ^ 2 := by
        rw [Real.sq_sqrt (show 0 ≤ (d : ℝ) from by exact mod_cast Nat.zero_le d)]
      _ = (Real.sqrt (d : ℝ) * w) ^ 2 := by ring
  nlinarith

/-- A4e: every eigenvalue of a symmetric matrix is at most its Frobenius norm in absolute value. -/
theorem abs_eigenvalues_le_frobNorm (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (i : Fin d) :
    |hS.eigenvalues i| ≤ frobNorm S := by
  have hS_eq : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S
  have h_sum_eq : (∑ j : Fin d, ∑ k : Fin d, S j k ^ 2) = ∑ i' : Fin d, (hS.eigenvalues i') ^ 2 := by
    calc
      (∑ j : Fin d, ∑ k : Fin d, S j k ^ 2) = (∑ j : Fin d, ∑ k : Fin d, cfc (id : ℝ → ℝ) S j k * S j k) := by
        simp_rw [sq, hS_eq]
      _ = ∑ i' : Fin d, (id (hS.eigenvalues i')) * (⇑(hS.eigenvectorBasis i') ⬝ᵥ (S *ᵥ ⇑(hS.eigenvectorBasis i'))) := by
        simpa using frob_cfc_eq_sum S hS (id : ℝ → ℝ) S
      _ = ∑ i' : Fin d, (hS.eigenvalues i') * (⇑(hS.eigenvectorBasis i') ⬝ᵥ (S *ᵥ ⇑(hS.eigenvectorBasis i'))) := by simp
      _ = ∑ i' : Fin d, (hS.eigenvalues i') * (⇑(hS.eigenvectorBasis i') ⬝ᵥ ((hS.eigenvalues i') • ⇑(hS.eigenvectorBasis i'))) := by
        simp_rw [hS.mulVec_eigenvectorBasis]
      _ = ∑ i' : Fin d, (hS.eigenvalues i') * ((hS.eigenvalues i') * (⇑(hS.eigenvectorBasis i') ⬝ᵥ ⇑(hS.eigenvectorBasis i'))) := by
        simp_rw [dotProduct_smul, smul_eq_mul]
      _ = ∑ i' : Fin d, (hS.eigenvalues i') * ((hS.eigenvalues i') * 1) := by
        have h_inner : ∀ i', ⇑(hS.eigenvectorBasis i') ⬝ᵥ ⇑(hS.eigenvectorBasis i') = 1 := by
          intro i'
          have h_ortho := hS.eigenvectorBasis.orthonormal
          have h_norm_sq : ‖hS.eigenvectorBasis i'‖ ^ 2 = 1 := by
            simp [h_ortho.1 i']
          have h_dot_eq_norm_sq : ⇑(hS.eigenvectorBasis i') ⬝ᵥ ⇑(hS.eigenvectorBasis i') = ‖hS.eigenvectorBasis i'‖ ^ 2 := by
            simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq (hS.eigenvectorBasis i')).symm
          rw [h_dot_eq_norm_sq, h_norm_sq]
        simp_rw [h_inner]
      _ = ∑ i' : Fin d, (hS.eigenvalues i') ^ 2 := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        ring
  have h_sq_nonneg : ∀ i' : Fin d, 0 ≤ (hS.eigenvalues i') ^ 2 := by
    intro i'
    apply sq_nonneg
  have h_sq_le : (hS.eigenvalues i) ^ 2 ≤ ∑ j : Fin d, ∑ k : Fin d, S j k ^ 2 := by
    rw [h_sum_eq]
    have h_mem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
    exact Finset.single_le_sum (fun i' _ => h_sq_nonneg i') h_mem
  calc
    |hS.eigenvalues i| = Real.sqrt ((hS.eigenvalues i) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (∑ j : Fin d, ∑ k : Fin d, S j k ^ 2) := Real.sqrt_le_sqrt h_sq_le
    _ = frobNorm S := rfl

/-- A4f: `S'` is symmetric with its spectrum within `c₀` of every shift `c ∈ [a, b]`. -/
theorem clipSym_spec (a b c : ℝ) (hab : a ≤ b) (hca : a ≤ c) (hcb : c ≤ b) (Y : Matrix (Fin d) (Fin d) ℝ) :
    ∃ hS : (clipSym a b Y).IsHermitian, ∀ i, |hS.eigenvalues i - c| ≤ cnC0 d a b := by
  set m := cnMid a b with hm
  set R₀ := cnR0 d a b with hR₀
  set W := symPart Y - m • 1 with hW
  set S' := clipSym a b Y with hS'
  have hm_def : m = (a + b) / 2 := rfl
  have hR₀_nonneg : 0 ≤ R₀ := by
    rw [hR₀, cnR0, cnHalf]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have h_half_nonneg : 0 ≤ (b - a) / 2 := by linarith
    nlinarith
  have hsymPartY : (symPart Y).IsHermitian := by
    rw [symPart]
    have : (Y + Y.transpose).IsHermitian :=
      isHermitian_add_transpose_self Y
    have hhalf : IsSelfAdjoint ((1 : ℝ) / 2) := IsSelfAdjoint.all _
    simpa [conjTranspose_smul, smul_add] using IsHermitian.smul this hhalf
  have hm_one : (m • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian := by
    have hm_selfadj : IsSelfAdjoint (m : ℝ) := IsSelfAdjoint.all _
    simpa using IsHermitian.smul isHermitian_one hm_selfadj
  have hW_herm : W.IsHermitian := by
    rw [hW]
    exact IsHermitian.sub hsymPartY hm_one
  have hfrobClip_herm : (frobClip R₀ W).IsHermitian := by
    rw [frobClip]
    split_ifs with hlt
    · have hdiv : IsSelfAdjoint (R₀ / frobNorm W : ℝ) := IsSelfAdjoint.all _
      exact IsHermitian.smul hW_herm hdiv
    · exact hW_herm
  have hS : S'.IsHermitian := by
    rw [hS', clipSym]
    exact IsHermitian.add hm_one hfrobClip_herm
  refine ⟨hS, ?_⟩
  intro i
  set u := hS.eigenvectorBasis i with hu
  have hu_inner_self : u ⬝ᵥ u = 1 := by
    have h_norm : ‖u‖ = 1 := hS.eigenvectorBasis.orthonormal.1 i
    calc
      u ⬝ᵥ u = RCLike.re (inner (𝕜 := ℝ) u u) := rfl
      _ = ‖u‖ ^ 2 := by rw [inner_self_eq_norm_sq (𝕜 := ℝ) u]
      _ = 1 ^ 2 := by rw [h_norm]
      _ = 1 := by norm_num
  have h_mulVec : S' *ᵥ u = (hS.eigenvalues i) • u :=
    hS.mulVec_eigenvectorBasis i
  set W' := frobClip R₀ W with hW'
  have hS'_eq : S' = m • 1 + W' := by
    rw [hS', clipSym, hW']
  have h_mulVec_expand : (hS.eigenvalues i) • u = m • u + W' *ᵥ u := by
    calc
      (hS.eigenvalues i) • u = S' *ᵥ u := by rw [h_mulVec]
      _ = (m • 1 + W') *ᵥ u := by rw [hS'_eq]
      _ = (m • 1) *ᵥ u + W' *ᵥ u := by rw [add_mulVec]
      _ = m • (1 *ᵥ u) + W' *ᵥ u := by rw [Matrix.smul_mulVec]
      _ = m • u + W' *ᵥ u := by rw [one_mulVec]
  have h_eigenvalue_eq : hS.eigenvalues i = m + u ⬝ᵥ (W' *ᵥ u) := by
    have h_dot : hS.eigenvalues i * (u ⬝ᵥ u) = m * (u ⬝ᵥ u) + u ⬝ᵥ (W' *ᵥ u) := by
      calc
        hS.eigenvalues i * (u ⬝ᵥ u) = u ⬝ᵥ ((hS.eigenvalues i) • u) := by
          simp [dotProduct_smul, smul_dotProduct]
        _ = u ⬝ᵥ (m • u + W' *ᵥ u) := by rw [h_mulVec_expand]
        _ = u ⬝ᵥ (m • u) + u ⬝ᵥ (W' *ᵥ u) := by rw [dotProduct_add]
        _ = m * (u ⬝ᵥ u) + u ⬝ᵥ (W' *ᵥ u) := by simp [dotProduct_smul]
    rw [hu_inner_self] at h_dot
    linarith
  rw [h_eigenvalue_eq]
  have h_bound_m : |m - c| ≤ cnHalf a b := by
    rw [hm_def, cnHalf]
    have h1 : c - (a + b) / 2 ≤ (b - a) / 2 := by linarith
    have h2 : (a + b) / 2 - c ≤ (b - a) / 2 := by linarith
    rw [abs_le]
    constructor <;> linarith
  have h_bound_W' : |u ⬝ᵥ (W' *ᵥ u)| ≤ R₀ := by
    have hW'_herm : W'.IsHermitian := hfrobClip_herm
    have h_cfc_id : cfc (id : ℝ → ℝ) W' = W' := by
      rw [Matrix.IsHermitian.cfc_eq hW'_herm (id : ℝ → ℝ)]
      have h := hW'_herm.spectral_theorem
      calc
        hW'_herm.cfc id = (Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) hW'_herm.eigenvectorUnitary
            (diagonal (RCLike.ofReal ∘ id ∘ hW'_herm.eigenvalues)) := rfl
        _ = (Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ)) hW'_herm.eigenvectorUnitary
            (diagonal (RCLike.ofReal ∘ hW'_herm.eigenvalues)) := by simp
        _ = W' := by rw [← h]
    have h_expand : u ⬝ᵥ (W' *ᵥ u) = ∑ j : Fin d, hW'_herm.eigenvalues j * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := by
      calc
        u ⬝ᵥ (W' *ᵥ u) = u ⬝ᵥ ((cfc (id : ℝ → ℝ) W') *ᵥ u) := by rw [h_cfc_id]
        _ = ∑ j : Fin d, (id : ℝ → ℝ) (hW'_herm.eigenvalues j) *
            ((⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u) * (⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u)) := by
          rw [dot_cfc_mulVec_eq_sum W' hW'_herm (id : ℝ → ℝ) u u]
        _ = ∑ j : Fin d, hW'_herm.eigenvalues j * ((⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u) * (⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u)) := by
          simp
        _ = ∑ j : Fin d, hW'_herm.eigenvalues j * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := by
          simp [sq]
    have h_sum_sq : ∑ j : Fin d, ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 = 1 := by
      calc
        ∑ j : Fin d, ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 =
            ∑ j : Fin d, ((⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u) * (⇑(hW'_herm.eigenvectorBasis j) ⬝ᵥ u)) := by
          simp [sq]
        _ = u ⬝ᵥ u := by rw [sum_eigen_dot_mul W' hW'_herm u u]
        _ = 1 := hu_inner_self
    have h_abs_eigen : ∀ j, |hW'_herm.eigenvalues j| ≤ frobNorm W' := by
      intro j
      exact abs_eigenvalues_le_frobNorm W' hW'_herm j
    have h_bound_sum : |∑ j : Fin d, hW'_herm.eigenvalues j * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2| ≤
        frobNorm W' := by
      calc
        |∑ j : Fin d, hW'_herm.eigenvalues j * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2| ≤
            ∑ j : Fin d, |hW'_herm.eigenvalues j * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin d, |hW'_herm.eigenvalues j| * |((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2| := by
          simp [abs_mul]
        _ = ∑ j : Fin d, |hW'_herm.eigenvalues j| * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have h_sq_nonneg : 0 ≤ ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := sq_nonneg _
          rw [abs_of_nonneg h_sq_nonneg]
        _ ≤ ∑ j : Fin d, frobNorm W' * ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h_sq_nonneg : 0 ≤ ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := sq_nonneg _
          nlinarith [h_abs_eigen j]
        _ = frobNorm W' * ∑ j : Fin d, ((hW'_herm.eigenvectorBasis j) ⬝ᵥ u) ^ 2 := by
          rw [Finset.mul_sum]
        _ = frobNorm W' * 1 := by rw [h_sum_sq]
        _ = frobNorm W' := by simp
    rw [h_expand]
    have h_frobNorm_le : frobNorm W' ≤ R₀ := by
      rw [hW']
      exact frobNorm_frobClip_le R₀ hR₀_nonneg W
    linarith
  have h_cnC0 : cnC0 d a b = R₀ + cnHalf a b := by
    rw [cnC0, hR₀]
  rw [h_cnC0]
  have h_triangle : |(m + u ⬝ᵥ (W' *ᵥ u)) - c| ≤ |m - c| + |u ⬝ᵥ (W' *ᵥ u)| := by
    calc
      |(m + u ⬝ᵥ (W' *ᵥ u)) - c| = |(m - c) + (u ⬝ᵥ (W' *ᵥ u))| := by ring
      _ ≤ |m - c| + |u ⬝ᵥ (W' *ᵥ u)| := abs_add_le _ _
  linarith

/-! ## A5c: the exact clamp of `S'` -/

/-- A5c, Lemma N (iii): the exact clamp of `S'` does not increase the distance to a matrix of the band. -/
theorem clampExact_nonexp (a b : ℝ) (hab : a < b) (Y Z : Matrix (Fin d) (Fin d) ℝ) (hZ : InBand a b Z) :
    frobNorm (cfc (fun x : ℝ => max a (min b x)) (clipSym a b Y) - Z) ≤ frobNorm (Y - Z) := by
  have hab_le : a ≤ b := le_of_lt hab
  -- Define the clamp function
  set clamp := fun x : ℝ => max a (min b x) with hclamp
  set C := cfc clamp (clipSym a b Y) with hC
  set S' := clipSym a b Y with hS'
  have hS'_herm : S'.IsHermitian := by
    -- from clipSym_spec with c = a
    have hspec := clipSym_spec a b a hab_le (le_refl a) (le_of_lt hab) Y
    exact hspec.1
  -- Step 1: frobNorm (C - Z) ≤ frobNorm (S' - Z)
  have h_step1 : frobNorm (C - Z) ≤ frobNorm (S' - Z) := by
    -- Key identity: frobNorm M ^ 2 = ∑ i, ∑ j, M i j ^ 2
    have h_frob_sq (M : Matrix (Fin d) (Fin d) ℝ) : (frobNorm M)^2 = ∑ i, ∑ j, M i j ^ 2 := by
      dsimp [frobNorm]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by nlinarith [sq_nonneg (M i j)])))]
    have h_nonneg_frob (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ frobNorm M := by
      dsimp [frobNorm]
      exact Real.sqrt_nonneg _
    -- Using the expansion identity
    have h_expand (X Y : Matrix (Fin d) (Fin d) ℝ) : (∑ i, ∑ j, (X i j + Y i j)^2) =
      (∑ i, ∑ j, (X i j)^2) + (∑ i, ∑ j, (Y i j)^2) + 2 * (∑ i, ∑ j, X i j * Y i j) := by
      have h_sq (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring
      simp_rw [h_sq]
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      ring
    -- The cross term inequality from clamp_frob_le
    have h_cross_nonneg : 0 ≤ ∑ i, ∑ j, (S' - C) i j * (C - Z) i j := by
      have h_le := clamp_frob_le S' Z hS'_herm a b (fun v => (hZ.2 v).1) (fun v => (hZ.2 v).2)
      have h_neg : (C - Z) = -(Z - C) := by
        ext i j; dsimp; ring
      rw [h_neg]
      have : (∑ i, ∑ j, (S' - C) i j * ((-(Z - C)) i j)) = (∑ i, ∑ j, -((S' - C) i j * (Z - C) i j)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        dsimp
        ring
      rw [this]
      simp only [Finset.sum_neg_distrib, mul_neg]
      linarith
    -- Now use the expansion
    have h_sq_eq : (frobNorm (S' - Z))^2 - (frobNorm (C - Z))^2 =
      2 * (∑ i, ∑ j, (S' - C) i j * (C - Z) i j) + (∑ i, ∑ j, (S' - C) i j ^ 2) := by
      rw [h_frob_sq (S' - Z), h_frob_sq (C - Z)]
      have h_eq : S' - Z = (S' - C) + (C - Z) := by ext i j; simp
      rw [h_eq]
      simp only [Matrix.add_apply, Matrix.sub_apply]
      -- Now the goal has (S' i j - C i j + (C i j - Z i j))^2
      -- Rewrite using the expansion lemma
      have h := h_expand (S' - C) (C - Z)
      simp only [Matrix.add_apply, Matrix.sub_apply] at h
      rw [h]
      ring
    -- Since h_cross_nonneg gives the cross term ≥ 0, and the S' - C squared sum is ≥ 0
    have h_nonneg_sq : 0 ≤ (∑ i, ∑ j, (S' - C) i j ^ 2) := by
      refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
      exact sq_nonneg _
    have h_nonneg_diff : 0 ≤ (frobNorm (S' - Z))^2 - (frobNorm (C - Z))^2 := by
      rw [h_sq_eq]
      nlinarith
    -- Therefore frobNorm (C - Z) ≤ frobNorm (S' - Z)
    have h_sq_le : (frobNorm (C - Z))^2 ≤ (frobNorm (S' - Z))^2 := by linarith
    nlinarith [h_nonneg_frob (C - Z), h_nonneg_frob (S' - Z)]
  -- Step 2: frobNorm (S' - Z) ≤ frobNorm (symPart Y - Z)
  have h_step2 : frobNorm (S' - Z) ≤ frobNorm (symPart Y - Z) := by
    set m := cnMid a b with hm
    set R₀ := cnR0 d a b with hR₀
    set X := symPart Y - m • 1 with hX
    set Z₀ := Z - m • 1 with hZ₀
    have hZ₀_norm : frobNorm Z₀ ≤ R₀ := frobNorm_sub_mid_le a b hab_le Z hZ
    have hR₀_nonneg : 0 ≤ R₀ := by
      dsimp [R₀, cnR0, cnHalf]
      have hsqrt_d_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have hhalf_nonneg : 0 ≤ (b - a) / 2 := by nlinarith
      exact mul_nonneg hsqrt_d_nonneg hhalf_nonneg
    have h_frobClip_varineq : ∑ i, ∑ j, (X - frobClip R₀ X) i j * (Z₀ - frobClip R₀ X) i j ≤ 0 :=
      frobClip_varineq R₀ hR₀_nonneg X Z₀ hZ₀_norm
    -- Same expansion as in step 1
    have h_expand (X' Y' : Matrix (Fin d) (Fin d) ℝ) : (∑ i, ∑ j, (X' i j + Y' i j)^2) =
      (∑ i, ∑ j, (X' i j)^2) + (∑ i, ∑ j, (Y' i j)^2) + 2 * (∑ i, ∑ j, X' i j * Y' i j) := by
      have h_sq (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring
      simp_rw [h_sq]
      simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      ring
    have h_frob_sq (M : Matrix (Fin d) (Fin d) ℝ) : (frobNorm M)^2 = ∑ i, ∑ j, M i j ^ 2 := by
      dsimp [frobNorm]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by nlinarith [sq_nonneg (M i j)])))]
    have h_nonneg_frob (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ frobNorm M := by
      dsimp [frobNorm]
      exact Real.sqrt_nonneg _
    -- The cross term inequality from frobClip_varineq
    have h_cross_nonneg : 0 ≤ ∑ i, ∑ j, (X - frobClip R₀ X) i j * (frobClip R₀ X - Z₀) i j := by
      have h_le := h_frobClip_varineq
      -- h_le: ∑ (X - frobClip R₀ X) i j * (Z₀ - frobClip R₀ X) i j ≤ 0
      -- We need ∑ (X - frobClip R₀ X) i j * (frobClip R₀ X - Z₀) i j ≥ 0
      -- Note (frobClip R₀ X - Z₀) = -(Z₀ - frobClip R₀ X)
      have : (frobClip R₀ X - Z₀) = -(Z₀ - frobClip R₀ X) := by
        ext i j; dsimp; ring
      rw [this]
      have : (∑ i, ∑ j, (X - frobClip R₀ X) i j * ((-(Z₀ - frobClip R₀ X)) i j)) =
             (∑ i, ∑ j, -((X - frobClip R₀ X) i j * (Z₀ - frobClip R₀ X) i j)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        dsimp
        ring
      rw [this]
      simp only [Finset.sum_neg_distrib, mul_neg]
      linarith
    -- Express S' - Z in terms of X, Z₀, frobClip
    have h_S'_sub_Z : S' - Z = frobClip R₀ X - Z₀ := by
      dsimp [S', clipSym, X, Z₀, m, R₀]
      ext i j; simp; ring
    have h_X_sub_Z₀ : X - Z₀ = symPart Y - Z := by
      dsimp [X, Z₀, m]
      ext i; simp
    -- Now use the same expansion as in step 1
    have h_nonneg_sq2 : 0 ≤ (∑ i, ∑ j, (X - frobClip R₀ X) i j ^ 2) := by
      refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
      exact sq_nonneg _
    have h_sq_eq : (frobNorm (X - Z₀))^2 - (frobNorm (frobClip R₀ X - Z₀))^2 =
      2 * (∑ i, ∑ j, (X - frobClip R₀ X) i j * (frobClip R₀ X - Z₀) i j) + (∑ i, ∑ j, (X - frobClip R₀ X) i j ^ 2) := by
      rw [h_frob_sq (X - Z₀), h_frob_sq (frobClip R₀ X - Z₀)]
      have h_eq : X - Z₀ = (X - frobClip R₀ X) + (frobClip R₀ X - Z₀) := by ext i j; simp
      rw [h_eq]
      simp only [Matrix.add_apply, Matrix.sub_apply]
      have h := h_expand (X - frobClip R₀ X) (frobClip R₀ X - Z₀)
      simp only [Matrix.add_apply, Matrix.sub_apply] at h
      rw [h]
      ring
    have h_nonneg_diff : 0 ≤ (frobNorm (X - Z₀))^2 - (frobNorm (frobClip R₀ X - Z₀))^2 := by
      rw [h_sq_eq]
      nlinarith
    have h_sq_le' : (frobNorm (frobClip R₀ X - Z₀))^2 ≤ (frobNorm (X - Z₀))^2 := by linarith
    -- Now combine with the expressions for S' - Z and symPart Y - Z
    have h_sq_le'' : (frobNorm (S' - Z))^2 ≤ (frobNorm (symPart Y - Z))^2 := by
      calc
        (frobNorm (S' - Z))^2 = (frobNorm (frobClip R₀ X - Z₀))^2 := by rw [h_S'_sub_Z]
        _ ≤ (frobNorm (X - Z₀))^2 := h_sq_le'
        _ = (frobNorm (symPart Y - Z))^2 := by rw [h_X_sub_Z₀]
    nlinarith [h_nonneg_frob (S' - Z), h_nonneg_frob (symPart Y - Z)]
  -- Step 3: frobNorm (symPart Y - Z) ≤ frobNorm (Y - Z)
  have h_step3 : frobNorm (symPart Y - Z) ≤ frobNorm (Y - Z) := by
    have h_frob_sq (M : Matrix (Fin d) (Fin d) ℝ) : (frobNorm M)^2 = ∑ i, ∑ j, M i j ^ 2 := by
      dsimp [frobNorm]
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by nlinarith [sq_nonneg (M i j)])))]
    have h_nonneg_frob (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ frobNorm M := by
      dsimp [frobNorm]
      exact Real.sqrt_nonneg _
    -- Key entrywise inequality: ((p+q)/2)^2 ≤ (p^2 + q^2)/2
    have h_entry (p q : ℝ) : ((p + q)/2)^2 ≤ (p^2 + q^2)/2 := by
      nlinarith [sq_nonneg (p - q)]
    -- (symPart Y - Z) i j = ((Y - Z) i j + (Y - Z) j i) / 2
    have h_entry_val (i j : Fin d) : (symPart Y - Z) i j = ((Y - Z) i j + (Y - Z) j i) / 2 := by
      dsimp [symPart, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply]
      have hZ_sym : Z i j = Z j i := by
        have h_herm := hZ.1
        -- h_herm : Z.IsHermitian, i.e., Zᴴ = Z
        -- For real matrices, (Zᴴ) i j = Z j i
        simpa [Matrix.conjTranspose_apply] using (congr_fun (congr_fun h_herm i) j).symm
      rw [hZ_sym]
      ring
    -- Now compare the squared sums
    have h_sq_le : (∑ i, ∑ j, (symPart Y - Z) i j ^ 2) ≤ (∑ i, ∑ j, (Y - Z) i j ^ 2) := by
      calc
        (∑ i, ∑ j, (symPart Y - Z) i j ^ 2) = (∑ i, ∑ j, (((Y - Z) i j + (Y - Z) j i) / 2)^2) := by
          simp_rw [h_entry_val]
        _ ≤ (∑ i, ∑ j, (((Y - Z) i j)^2 + ((Y - Z) j i)^2) / 2) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          exact h_entry ((Y - Z) i j) ((Y - Z) j i)
        _ = (∑ i, (∑ j, (((Y - Z) i j)^2 + ((Y - Z) j i)^2) / 2)) := rfl
        _ = (∑ i, (∑ j, (((Y - Z) i j)^2 + ((Y - Z) j i)^2)) / 2) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_div]
        _ = (∑ i, ∑ j, (((Y - Z) i j)^2 + ((Y - Z) j i)^2)) / 2 := by
          rw [Finset.sum_div]
        _ = ((∑ i, ∑ j, ((Y - Z) i j)^2) + (∑ i, ∑ j, ((Y - Z) j i)^2)) / 2 := by
          simp [Finset.sum_add_distrib]
        _ = ((∑ i, ∑ j, ((Y - Z) i j)^2) + (∑ i, ∑ j, ((Y - Z) i j)^2)) / 2 := by
          rw [Finset.sum_comm]
        _ = (∑ i, ∑ j, ((Y - Z) i j)^2) := by ring
    -- Now use the relationship between frobNorm squared and the sum
    have h_frob_sq_diff : (frobNorm (Y - Z))^2 - (frobNorm (symPart Y - Z))^2 =
      (∑ i, ∑ j, (Y - Z) i j ^ 2) - (∑ i, ∑ j, (symPart Y - Z) i j ^ 2) := by
      simp [h_frob_sq]
    have h_nonneg_diff : 0 ≤ (frobNorm (Y - Z))^2 - (frobNorm (symPart Y - Z))^2 := by
      rw [h_frob_sq_diff]
      linarith
    have h_sq_le' : (frobNorm (symPart Y - Z))^2 ≤ (frobNorm (Y - Z))^2 := by linarith
    nlinarith [h_nonneg_frob (symPart Y - Z), h_nonneg_frob (Y - Z)]
  -- Combine the three steps
  calc
    frobNorm (cfc (fun x : ℝ => max a (min b x)) (clipSym a b Y) - Z) = frobNorm (C - Z) := by rfl
    _ ≤ frobNorm (S' - Z) := h_step1
    _ ≤ frobNorm (symPart Y - Z) := h_step2
    _ ≤ frobNorm (Y - Z) := h_step3

/-! ## C2a: the tolerance -/

/-- C2a: `t_min < t_max` and `0 < e' < w`. -/
theorem pgEpr_bounds {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    pgTmin d ρ < pgLD ρ ∧ 0 < pgEpr d ρ ∧ pgEpr d ρ < cnHalf (pgTmin d ρ) (pgLD ρ) := by
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hρpos : 0 < ρ := by linarith
  -- pgLam ρ > 1
  have hLam_gt_one : 1 < pgLam ρ := by
    have hlog2_gt_half : (1/2 : ℝ) < Real.log 2 := by
      have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have hlog_gt_half : (1/2 : ℝ) < Real.log (1 + ρ) := by
      have hlog2_le : Real.log 2 ≤ Real.log (1 + ρ) :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
      linarith
    have h2log_gt_one : 1 < 2 * Real.log (1 + ρ) := by linarith
    have hsqrt : 1 < Real.sqrt (2 * Real.log (1 + ρ)) := by
      calc
        1 = Real.sqrt ((1 : ℝ)^2) := by norm_num
        _ < Real.sqrt (2 * Real.log (1 + ρ)) :=
          Real.sqrt_lt_sqrt (by norm_num) (by simpa using h2log_gt_one)
    simpa [pgLam] using hsqrt
  have hLam_pos : 0 < pgLam ρ := by linarith
  have hLam_ge_one : (1 : ℝ) ≤ pgLam ρ := by linarith
  -- pgTmin d ρ ≤ 1/9
  have hTmin_le : pgTmin d ρ ≤ 1/9 := by
    dsimp [pgTmin]
    have hden : (9 : ℝ) ≤ 9 * (d : ℝ) * pgLam ρ := by nlinarith
    have hpos : 0 < 9 * (d : ℝ) * pgLam ρ := by positivity
    have hpos9 : 0 < (9 : ℝ) := by norm_num
    apply (one_div_le_one_div hpos hpos9).mpr
    nlinarith
  -- pgLD ρ ≥ 1254/8000
  have hLD_ge : (1254/8000 : ℝ) ≤ pgLD ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    nlinarith
  -- First conjunct
  have h_first : pgTmin d ρ < pgLD ρ := by
    have h_lt : (1/9 : ℝ) < (1254/8000 : ℝ) := by norm_num
    linarith
  -- Second conjunct
  have h_second : 0 < pgEpr d ρ := by
    dsimp [pgEpr, pgEP]
    have hEh_pos : 0 < pgEh d ρ := pgEh_pos d ρ hd hρ
    have hG2_pos : 0 < pgG2 d ρ := by
      dsimp [pgG2, pgLD, pgKappa, pgPB, pgTmin]
      positivity
    have hNs_pos : 0 < (pgNs d ρ : ℝ) := by
      have hNs_ge_one : 1 ≤ pgNs d ρ := pgNs_pos d ρ hd hρ
      exact_mod_cast hNs_ge_one
    have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
    have hsqrt_Ns_pos : 0 < Real.sqrt (pgNs d ρ : ℝ) := Real.sqrt_pos.mpr hNs_pos
    positivity
  -- pgG2 ≥ 1
  have hG2_ge_one : 1 ≤ pgG2 d ρ := by
    unfold pgG2 pgLD pgKappa pgPB pgTmin
    have hN_lower : (90 : ℝ) * ((1254/8000 : ℝ)^2) ≤
        5 * ((1/8)*(1254/1000)*ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := by
      have hLD : (1254/8000 : ℝ) ≤ (1/8)*(1254/1000)*ρ := by
        nlinarith
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := hd_real
      have hd3 : (3 : ℝ) ≤ (d : ℝ) + 2 := by nlinarith
      have hd6 : (6 : ℝ) ≤ (d : ℝ) + 5 := by nlinarith
      have h_sq : ((1254/8000 : ℝ)^2) ≤ (((1/8)*(1254/1000)*ρ)^2) := by nlinarith
      have h_nonneg_sq : 0 ≤ ((1/8)*(1254/1000)*ρ)^2 := by positivity
      have h_nonneg_d : 0 ≤ (d : ℝ) := by linarith
      have h_nonneg_d3 : 0 ≤ (d : ℝ) + 2 := by linarith
      have h_nonneg_d6 : 0 ≤ (d : ℝ) + 5 := by linarith
      have h_inner : ((1254/8000 : ℝ)^2) * 1 * 3 * 6 ≤ (((1/8)*(1254/1000)*ρ)^2) * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := by
        have h1 : ((1254/8000 : ℝ)^2) * 1 ≤ ((1/8)*(1254/1000)*ρ)^2 * (d : ℝ) :=
          mul_le_mul h_sq hd1 (by positivity) (by nlinarith)
        have h2 : (((1254/8000 : ℝ)^2) * 1) * 3 ≤ (((1/8)*(1254/1000)*ρ)^2 * (d : ℝ)) * ((d : ℝ) + 2) :=
          mul_le_mul h1 hd3 (by positivity) (by nlinarith)
        have h3 : ((((1254/8000 : ℝ)^2) * 1) * 3) * 6 ≤ ((((1/8)*(1254/1000)*ρ)^2 * (d : ℝ)) * ((d : ℝ) + 2)) * ((d : ℝ) + 5) :=
          mul_le_mul h2 hd6 (by positivity) (by nlinarith)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h3
      calc
        (90 : ℝ) * ((1254/8000 : ℝ)^2) = 5 * (((1254/8000 : ℝ)^2) * 1 * 3 * 6) := by ring
        _ ≤ 5 * ((((1/8)*(1254/1000)*ρ)^2) * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5)) := by
          gcongr
        _ = 5 * ((1/8)*(1254/1000)*ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := by ring
    have hD_upper : (1 / (9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)))) ^ 2 ≤ (1/81 : ℝ) := by
      have h_inner : 9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) ≥ (9 : ℝ) := by
        have h_sqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.log (1 + ρ)) := by
          have harg : 1 ≤ 2 * Real.log (1 + ρ) := by
            have hhalf : (1/2 : ℝ) ≤ Real.log (1 + ρ) := by
              have hlog2_gt_half : (1/2 : ℝ) < Real.log 2 := by
                have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
                linarith
              have hlog2_le : Real.log 2 ≤ Real.log (1 + ρ) :=
                Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
              exact le_trans hlog2_gt_half.le hlog2_le
            linarith
          calc
            (1 : ℝ) = Real.sqrt ((1 : ℝ)^2) := by norm_num
            _ ≤ Real.sqrt (2 * Real.log (1 + ρ)) :=
              Real.sqrt_le_sqrt (by simpa using harg)
        nlinarith
      have hpos : 0 < 9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)) := by positivity
      have hpos9 : 0 < (9 : ℝ) := by norm_num
      have h_inv : 1 / (9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ))) ≤ 1/9 :=
        (one_div_le_one_div hpos hpos9).mpr h_inner
      have h_nonneg : 0 ≤ 1 / (9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ))) := by positivity
      nlinarith
    have h_key : (1/81 : ℝ) ≤ (90 : ℝ) * ((1254/8000 : ℝ)^2) := by norm_num
    have hpos_num : 0 < 5 * ((1/8)*(1254/1000)*ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) +
      2 * ((1/8)^2) / (d : ℝ) := by positivity
    have hpos_den : 0 < (1 / (9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)))) ^ 2 := by positivity
    apply (one_le_div hpos_den).mpr
    calc
      (1 / (9 * (d : ℝ) * Real.sqrt (2 * Real.log (1 + ρ)))) ^ 2 ≤ (1/81 : ℝ) := hD_upper
      _ ≤ (90 : ℝ) * ((1254/8000 : ℝ)^2) := h_key
      _ ≤ 5 * ((1/8)*(1254/1000)*ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) := hN_lower
      _ ≤ 5 * ((1/8)*(1254/1000)*ρ) ^ 2 * (d : ℝ) * ((d : ℝ) + 2) * ((d : ℝ) + 5) +
        2 * ((1/8)^2) / (d : ℝ) := by
        have h_nonneg : 0 ≤ 2 * ((1/8)^2) / (d : ℝ) := by positivity
        linarith
  -- Third conjunct
  have h_third : pgEpr d ρ < cnHalf (pgTmin d ρ) (pgLD ρ) := by
    dsimp [cnHalf]
    have h_main : 2 * pgEpr d ρ < pgLD ρ - pgTmin d ρ := by
      have h_eq : 2 * pgEpr d ρ = pgEP d ρ / Real.sqrt (d : ℝ) := by
        dsimp [pgEpr]
        ring
      rw [h_eq]
      -- Upper bound LHS
      have hLHS_le : pgEP d ρ / Real.sqrt (d : ℝ) ≤ ((1/64 : ℝ) / (922 * (1254/8000 : ℝ) * (10^6 : ℝ))) := by
        dsimp [pgEP, pgEh]
        have hKappa_sq : pgKappa^2 = (1/64 : ℝ) := by norm_num [pgKappa]
        rw [hKappa_sq]
        have hG2_pos : 0 < pgG2 d ρ := by
          dsimp [pgG2, pgLD, pgKappa, pgPB, pgTmin]
          positivity
        have hNs_pos' : 0 < (pgNs d ρ : ℝ) := by
          have hNs_ge_one : 1 ≤ pgNs d ρ := pgNs_pos d ρ hd hρ
          exact_mod_cast hNs_ge_one
        have h_sqrt_G2_pos : 0 < Real.sqrt (pgG2 d ρ) := Real.sqrt_pos.mpr hG2_pos
        have h_sqrt_Ns_pos : 0 < Real.sqrt (pgNs d ρ : ℝ) := Real.sqrt_pos.mpr hNs_pos'
        have h_sqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
        have h_denom_pos : 0 < 922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
            (10^6 : ℝ) * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ) := by
          positivity
        have h_denom_ge : (0 : ℝ) < 922 * (1254/8000 : ℝ) * (10^6 : ℝ) := by norm_num
        have h_denom_ge' : 922 * (1254/8000 : ℝ) * (10^6 : ℝ) ≤
            922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ * (10^6 : ℝ) *
            Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ) := by
          -- Need: (1254/8000) ≤ d^2 * pgLam^2 * pgLD * sqrt(G2) * sqrt(Ns) * sqrt(d)
          -- Each factor on RHS ≥ 1 except pgLD ≥ 1254/8000
          have h_factor_ge : (1254/8000 : ℝ) ≤ (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
              Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ) := by
            have hd_sq_ge_one : (1 : ℝ) ≤ (d : ℝ)^2 := by nlinarith
            have hLam_sq_ge_one : (1 : ℝ) ≤ (pgLam ρ)^2 := by nlinarith
            have h_sqrt_G2_ge_one : (1 : ℝ) ≤ Real.sqrt (pgG2 d ρ) := by
              calc
                (1 : ℝ) = Real.sqrt ((1 : ℝ)^2) := by norm_num
                _ ≤ Real.sqrt (pgG2 d ρ) := Real.sqrt_le_sqrt (by simpa using hG2_ge_one)
            have h_sqrt_Ns_ge_one : (1 : ℝ) ≤ Real.sqrt (pgNs d ρ : ℝ) := by
              have hNs_ge_one : (1 : ℝ) ≤ (pgNs d ρ : ℝ) := by
                have h : 1 ≤ pgNs d ρ := pgNs_pos d ρ hd hρ
                exact_mod_cast h
              calc
                (1 : ℝ) = Real.sqrt ((1 : ℝ)^2) := by norm_num
                _ ≤ Real.sqrt (pgNs d ρ : ℝ) := Real.sqrt_le_sqrt (by simpa using hNs_ge_one)
            have h_sqrt_d_ge_one : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
              calc
                (1 : ℝ) = Real.sqrt ((1 : ℝ)^2) := by norm_num
                _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt (by simpa using hd_real)
            -- Now chain: 1*1*(1254/8000)*1*1*1 ≤ d^2*pgLam^2*pgLD*sqrt(G2)*sqrt(Ns)*sqrt(d)
            have h1 : (1 : ℝ) * 1 ≤ (d : ℝ)^2 * (pgLam ρ)^2 :=
              mul_le_mul hd_sq_ge_one hLam_sq_ge_one (by positivity) (by nlinarith)
            have h2 : ((1 : ℝ) * 1) * (1254/8000 : ℝ) ≤ ((d : ℝ)^2 * (pgLam ρ)^2) * pgLD ρ :=
              mul_le_mul h1 hLD_ge (by positivity) (by positivity)
            have h3 : (((1 : ℝ) * 1) * (1254/8000 : ℝ)) * 1 ≤ (((d : ℝ)^2 * (pgLam ρ)^2) * pgLD ρ) * Real.sqrt (pgG2 d ρ) :=
              mul_le_mul h2 h_sqrt_G2_ge_one (by positivity) (by positivity)
            have h4 : ((((1 : ℝ) * 1) * (1254/8000 : ℝ)) * 1) * 1 ≤ ((((d : ℝ)^2 * (pgLam ρ)^2) * pgLD ρ) * Real.sqrt (pgG2 d ρ)) * Real.sqrt (pgNs d ρ : ℝ) :=
              mul_le_mul h3 h_sqrt_Ns_ge_one (by positivity) (by positivity)
            have h5 : (((((1 : ℝ) * 1) * (1254/8000 : ℝ)) * 1) * 1) * 1 ≤ (((((d : ℝ)^2 * (pgLam ρ)^2) * pgLD ρ) * Real.sqrt (pgG2 d ρ)) * Real.sqrt (pgNs d ρ : ℝ)) * Real.sqrt (d : ℝ) :=
              mul_le_mul h4 h_sqrt_d_ge_one (by positivity) (by positivity)
            -- Simplify both sides
            simpa [mul_comm, mul_left_comm, mul_assoc] using h5
          calc
            922 * (1254/8000 : ℝ) * (10^6 : ℝ) = (922 * (10^6 : ℝ)) * (1254/8000 : ℝ) := by ring
            _ ≤ (922 * (10^6 : ℝ)) * ((d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
              Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ)) := by
              refine mul_le_mul_of_nonneg_left h_factor_ge (by norm_num)
            _ = 922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ * (10^6 : ℝ) *
              Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ) := by ring
        have h_one_div_le : (1 : ℝ) / (922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
            (10^6 : ℝ) * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ)) ≤
            (1 : ℝ) / (922 * (1254/8000 : ℝ) * (10^6 : ℝ)) :=
          (one_div_le_one_div h_denom_pos h_denom_ge).mpr h_denom_ge'
        calc
          (1/64 : ℝ) / (922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ) / ((10^6 : ℝ) * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ)) / Real.sqrt (d : ℝ) =
            ((1/64 : ℝ) / (922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
            (10^6 : ℝ) * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ))) := by
            ring
          _ = (1/64 : ℝ) * ((1 : ℝ) / (922 * (d : ℝ)^2 * (pgLam ρ)^2 * pgLD ρ *
            (10^6 : ℝ) * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ : ℝ) * Real.sqrt (d : ℝ))) := by ring
          _ ≤ (1/64 : ℝ) * ((1 : ℝ) / (922 * (1254/8000 : ℝ) * (10^6 : ℝ))) := by
            gcongr
          _ = ((1/64 : ℝ) / (922 * (1254/8000 : ℝ) * (10^6 : ℝ))) := by ring
      -- Lower bound RHS
      have hRHS_ge : (1254/8000 : ℝ) - 1/9 ≤ pgLD ρ - pgTmin d ρ := by
        linarith
      -- Numeric inequality
      have h_num : ((1/64 : ℝ) / (922 * (1254/8000 : ℝ) * (10^6 : ℝ))) < (1254/8000 : ℝ) - 1/9 := by
        norm_num
      linarith
    linarith
  exact ⟨h_first, h_second, h_third⟩

/-! ## A5d and A6: the projection on `D` -/

/-- The radial clip is nonexpansive toward a point of the ball. -/
theorem ballClip_dist_le (R : ℝ) (hR : 0 ≤ R) (μ ν : EuclideanSpace ℝ (Fin d)) (hν : ‖ν‖ ≤ R) :
    ‖ballClip R μ - ν‖ ≤ ‖μ - ν‖ := by
  set c := ballClip R μ with hc
  have hvar := ballClip_varineq R hR μ ν hν
  -- hvar : ⟪μ - c, ν - c⟫ ≤ 0
  have h_inner_nonneg : 0 ≤ ⟪μ - c, c - ν⟫ := by
    have : c - ν = -(ν - c) := by simp
    rw [this, inner_neg_right]
    linarith
  have h_sq_ineq : ‖c - ν‖ ^ 2 ≤ ‖μ - ν‖ ^ 2 := by
    calc
      ‖c - ν‖ ^ 2 ≤ ‖μ - c‖ ^ 2 + 2 * ⟪μ - c, c - ν⟫ + ‖c - ν‖ ^ 2 := by nlinarith
      _ = ‖(μ - c) + (c - ν)‖ ^ 2 := by rw [norm_add_sq_real]
      _ = ‖μ - ν‖ ^ 2 := by
        simp [sub_add_sub_cancel]
  have h_norm_nonneg₁ : 0 ≤ ‖c - ν‖ := norm_nonneg _
  have h_norm_nonneg₂ : 0 ≤ ‖μ - ν‖ := norm_nonneg _
  nlinarith

/-- The triangle inequality of the Frobenius norm. -/
theorem frobNorm_sub_le_add (A B Z : Matrix (Fin d) (Fin d) ℝ) :
    frobNorm (A - Z) ≤ frobNorm (A - B) + frobNorm (B - Z) := by
  have key : ∀ W : Matrix (Fin d) (Fin d) ℝ, frobNorm W =
      ‖(WithLp.toLp 2 (fun p : Fin d × Fin d => W p.1 p.2) : EuclideanSpace ℝ (Fin d × Fin d))‖ := by
    intro W
    rw [EuclideanSpace.norm_eq, frobNorm, Fintype.sum_prod_type]
    simp [Real.norm_eq_abs, sq_abs]
  rw [key, key, key]
  have h : (WithLp.toLp 2 (fun p : Fin d × Fin d => (A - Z) p.1 p.2) : EuclideanSpace ℝ (Fin d × Fin d)) =
      WithLp.toLp 2 (fun p : Fin d × Fin d => (A - B) p.1 p.2) +
        WithLp.toLp 2 (fun p : Fin d × Fin d => (B - Z) p.1 p.2) := by
    ext p; simp
  rw [h]
  exact norm_add_le _ _

/-- `(a² + b²)^{1/2} ≤ (a'² + b'²)^{1/2} + e` for `0 ≤ a ≤ a'` and `0 ≤ b ≤ b' + e`. -/
theorem sqrt_pair_le (a a' b b' e : ℝ) (ha : 0 ≤ a) (haa : a ≤ a') (hb : 0 ≤ b) (hbb : b ≤ b' + e) (hb' : 0 ≤ b')
    (he : 0 ≤ e) : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (a' ^ 2 + b' ^ 2) + e := by
  have ha' : 0 ≤ a' := by nlinarith
  have hbe : 0 ≤ b' + e := by nlinarith
  have h1 : a ^ 2 + b ^ 2 ≤ a' ^ 2 + (b' + e) ^ 2 := by
    nlinarith
  have h2 : Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (a' ^ 2 + (b' + e) ^ 2) :=
    Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (a' ^ 2 + (b' + e) ^ 2) ≤ Real.sqrt (a' ^ 2 + b' ^ 2) + e := by
    have h_sq_nonneg : 0 ≤ a' ^ 2 + (b' + e) ^ 2 := by nlinarith
    have h_sq_nonneg2 : 0 ≤ a' ^ 2 + b' ^ 2 := by nlinarith
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := Real.sqrt_nonneg _
    have h_sum_nonneg : 0 ≤ Real.sqrt (a' ^ 2 + b' ^ 2) + e := by nlinarith
    have h_sq_ineq : (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) ^ 2 ≤ (Real.sqrt (a' ^ 2 + b' ^ 2) + e) ^ 2 := by
      calc
        (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) ^ 2 = a' ^ 2 + (b' + e) ^ 2 := Real.sq_sqrt h_sq_nonneg
        _ = a' ^ 2 + (b' ^ 2 + 2 * b' * e + e ^ 2) := by ring
        _ = (a' ^ 2 + b' ^ 2) + 2 * b' * e + e ^ 2 := by ring
        _ ≤ (a' ^ 2 + b' ^ 2) + 2 * (Real.sqrt (a' ^ 2 + b' ^ 2)) * e + e ^ 2 := by
          have hb'_sq : b' ^ 2 ≤ a' ^ 2 + b' ^ 2 := by nlinarith
          have hb'_le_sqrt : b' ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := by
            calc
              b' = Real.sqrt (b' ^ 2) := by rw [Real.sqrt_sq hb']
              _ ≤ Real.sqrt (a' ^ 2 + b' ^ 2) := Real.sqrt_le_sqrt hb'_sq
          nlinarith
        _ = (Real.sqrt (a' ^ 2 + b' ^ 2)) ^ 2 + 2 * (Real.sqrt (a' ^ 2 + b' ^ 2)) * e + e ^ 2 := by
          rw [Real.sq_sqrt h_sq_nonneg2]
        _ = (Real.sqrt (a' ^ 2 + b' ^ 2) + e) ^ 2 := by ring
    have hpos1 : 0 ≤ Real.sqrt (a' ^ 2 + (b' + e) ^ 2) := Real.sqrt_nonneg _
    have h_mul_self_ineq : (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) * (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) ≤
        (Real.sqrt (a' ^ 2 + b' ^ 2) + e) * (Real.sqrt (a' ^ 2 + b' ^ 2) + e) := by
      calc
        (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) * (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) =
            (Real.sqrt (a' ^ 2 + (b' + e) ^ 2)) ^ 2 := by ring
        _ ≤ (Real.sqrt (a' ^ 2 + b' ^ 2) + e) ^ 2 := h_sq_ineq
        _ = (Real.sqrt (a' ^ 2 + b' ^ 2) + e) * (Real.sqrt (a' ^ 2 + b' ^ 2) + e) := by ring
    exact ((mul_self_le_mul_self_iff hpos1 h_sum_nonneg).mpr h_mul_self_ineq)
  nlinarith

/-- The norm of `PgSp d` from the norms of its two parts. -/
theorem pgSp_norm_eq (x : PgSp d) : ‖x‖ = Real.sqrt (‖pgMu x‖ ^ 2 + frobNorm (pgMat x) ^ 2) := by
  rw [frobNorm, Real.sq_sqrt (by positivity), ← pgSp_norm_sq, Real.sqrt_sq (norm_nonneg x)]

/-- A5d: the projection maps into `D`. -/
theorem pgProjR_mem (C : ClampRoutine) {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (y : PgSp d) :
    pgProjR C d ρ y ∈ pgDom d ρ := by
  obtain ⟨hab, he0, he1⟩ := pgEpr_bounds hd hρ
  have hR : 0 ≤ pgKappa * ρ := by unfold pgKappa; linarith
  have hb := C.bounds d _ _ _ (pgMat y) hab he0 he1
  exact mem_pgDom_of _ _ hb.1 (ballClip_norm_le _ hR _) hb.2

/-- A5d: the projection is a projection on `D` up to `e_P`, the hypothesis of Lemma SGD-e. -/
theorem pgProjR_near (C : ClampRoutine) {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (y z : PgSp d) (hz : z ∈ pgDom d ρ) :
    ‖pgProjR C d ρ y - z‖ ≤ ‖y - z‖ + pgEP d ρ := by
  obtain ⟨hab, he0, he1⟩ := pgEpr_bounds hd hρ
  obtain ⟨hzh, hzmu, hzq⟩ := pgDom_mat hz
  have hR : 0 ≤ pgKappa * ρ := by unfold pgKappa; linarith
  have h1 := ballClip_dist_le _ hR (pgMu y) (pgMu z) hzmu
  have h2 := C.near d _ _ _ (pgMat y) (pgMat z) hab he0 he1 ⟨hzh, hzq⟩
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have he2 : 2 * pgEpr d ρ * Real.sqrt d = pgEP d ρ := by unfold pgEpr; field_simp
  have hEP : 0 ≤ pgEP d ρ := by rw [← he2]; positivity
  rw [pgSp_norm_eq (pgProjR C d ρ y - z), pgSp_norm_eq (y - z), pgMu_sub, pgMu_sub, pgMat_sub, pgMat_sub]
  unfold pgProjR
  rw [pgMu_pgPack, pgMat_pgPack]
  exact sqrt_pair_le _ _ _ _ _ (norm_nonneg _) h1 (Real.sqrt_nonneg _) (by linarith) (Real.sqrt_nonneg _) hEP

/-- A6: the projection is measurable, for every `d` and `ρ`. -/
theorem pgProjR_measurable (C : ClampRoutine) (d : ℕ) (ρ : ℝ) : Measurable (pgProjR C d ρ) := by
  have hm : Measurable fun y : PgSp d => pgMu y := (pg_continuous d).1.measurable
  have hmu : Measurable fun y : PgSp d => ballClip (pgKappa * ρ) (pgMu y) := by
    unfold ballClip
    exact Measurable.ite (measurableSet_lt measurable_const hm.norm) ((measurable_const.div hm.norm).smul hm) hm
  have hM : Measurable fun y : PgSp d => C.run d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) (pgMat y) :=
    (C.meas d _ _ _).comp (pg_continuous d).2.1.measurable
  exact (pgPack_continuous d).measurable.comp (hmu.prodMk hM)

end AdversarialBco.Conj1Arith
