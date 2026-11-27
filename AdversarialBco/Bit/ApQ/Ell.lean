/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ApQ.Step
public import AdversarialBco.Bit.ApQ.Clear
public import AdversarialBco.Poly.Df2OracleProof

@[expose] public section

/-!
# The projection theorem, part (b): the lemmas of the proof

The facts on the integer problem `EllI d` behind the correctness of the projection routine (ELL-R for `d ≥ 2`, BIS-R
for `d = 1`): the gradients and the values of step 4 (`gG`, `PsiI`, `gPsi`, `ghI`, `VI`, `updK`), the convexity and the
compactness of the region (`region_convex`, `region_compact`) and the Lipschitz bound of the gradient (`grad_lip`),
the constants of the ball `B̄(p_θ, ρ)`, `p_θ = (1 - θ)p* + θ a₀`, `ρ = 2^{-j}` (`theta_spec`, `rho_le`, `Rb_spec`,
`Rb_rho`) and of the precisions (`p_prec`, `q_prec`, `two_j_le_p`, `cap_gam`), the cuts of one test (`cut_out`,
`cut_psi`, `test_in`), and the bisection on intervals (`bis_mid`, `bis_contra`).
-/

namespace AdversarialBco.Bit.ApQ

open AdversarialBco.Bit.RQ
open AdversarialBco.Poly (oNorm oBall)
open Matrix

variable {d : ℕ}

/-- `∇G(y) = P y - f̂/D_f`. -/
noncomputable def gG (I : EllI d) (y : Fin d → ℝ) : Fin d → ℝ :=
  I.P.map ((↑) : ℤ → ℝ) *ᵥ y - fun j => (I.f j : ℝ) / I.Df

/-- `Ψ(y) = yᵀHy/2 - g·y`. -/
noncomputable def PsiI (I : EllI d) (y : Fin d → ℝ) : ℝ :=
  y ⬝ᵥ (I.H.map ((↑) : ℤ → ℝ) *ᵥ y) / 2 - (fun j => (I.g j : ℝ)) ⬝ᵥ y

/-- `∇Ψ(y) = H y - g`. -/
noncomputable def gPsi (I : EllI d) (y : Fin d → ℝ) : Fin d → ℝ :=
  I.H.map ((↑) : ℤ → ℝ) *ᵥ y - fun j => (I.g j : ℝ)

/-- `ĝ = P(D_f â) - 2^s f̂` of step 4. -/
def ghI (I : EllI d) (s : ℕ) (a : Fin d → ℤ) : Fin d → ℤ := I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f

/-- `V = D_f âᵀPâ - 2^{s+1} f̂·â` of step 4. -/
def VI (I : EllI d) (s : ℕ) (a : Fin d → ℤ) : ℤ := (I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)

/-- The kept point after recording `(a, V)`. -/
def updK (a : Fin d → ℤ) (V : ℤ) (kept : Option ((Fin d → ℤ) × ℤ)) : Option ((Fin d → ℤ) × ℤ) :=
  match kept with
  | none => some (a, V)
  | some (b, W) => if V < W then some (a, V) else some (b, W)

/-! ## The scaled point `x/2^s` and integer casts -/

theorem vR_eq (s : ℕ) (a : Fin d → ℤ) : vR s a = (1 / 2 ^ s : ℝ) • vZ a := by
  funext j
  simp only [vR, vZ, Pi.smul_apply, smul_eq_mul]
  ring

theorem dotZ_cast (c a : Fin d → ℤ) : ((c ⬝ᵥ a : ℤ) : ℝ) = vZ c ⬝ᵥ vZ a := by
  simp [dotProduct, vZ]

theorem mulVecZ_cast (M : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ) :
    vZ (M *ᵥ a) = M.map ((↑) : ℤ → ℝ) *ᵥ vZ a := by
  funext i
  simp [vZ, Matrix.mulVec, dotProduct]

theorem lin_vR (c a : Fin d → ℤ) (s : ℕ) : vZ c ⬝ᵥ vR s a = ((c ⬝ᵥ a : ℤ) : ℝ) / 2 ^ s := by
  rw [vR_eq, dotProduct_smul, smul_eq_mul, dotZ_cast]
  ring

theorem quad_vR (M : Matrix (Fin d) (Fin d) ℤ) (s : ℕ) (a : Fin d → ℤ) :
    vR s a ⬝ᵥ (M.map ((↑) : ℤ → ℝ) *ᵥ vR s a) = ((a ⬝ᵥ (M *ᵥ a) : ℤ) : ℝ) / 2 ^ (2 * s) := by
  rw [vR_eq, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dotZ_cast, mulVecZ_cast]
  simp only [smul_eq_mul]
  have : (2 : ℝ) ^ (2 * s) = (2 ^ s) ^ 2 := by ring
  rw [this]
  field_simp

theorem Psi_vR (I : EllI d) (s : ℕ) (a : Fin d → ℤ) :
    PsiI I (vR s a) = ((a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) : ℤ) : ℝ) / 2 ^ (2 * s + 1) := by
  unfold PsiI
  rw [quad_vR, show (fun j => (I.g j : ℝ)) = vZ I.g from rfl, lin_vR]
  push_cast
  field_simp
  ring

/-! ## Leaves: the region and the objective -/

theorem GI_conv (I : EllI d) (hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef) (x y : Fin d → ℝ) :
    GI I x + gG I x ⬝ᵥ (y - x) ≤ GI I y := by
  set M := I.P.map ((↑) : ℤ → ℝ) with hM
  have hT : Mᵀ = M := by
    have h := hP.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hsym : ∀ u v : Fin d → ℝ, u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← hT, Matrix.vecMul_transpose, dotProduct_comm, hT]
  have hq := hP.dotProduct_mulVec_nonneg (y - x)
  simp only [star_trivial] at hq
  have e1 : (y - x) ⬝ᵥ (M *ᵥ (y - x)) = y ⬝ᵥ (M *ᵥ y) - 2 * (x ⬝ᵥ (M *ᵥ y)) + x ⬝ᵥ (M *ᵥ x) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym y x]
    ring
  unfold GI gG
  rw [← hM]
  set b : Fin d → ℝ := fun j => (I.f j : ℝ) / I.Df with hb
  have e2 : (M *ᵥ x - b) ⬝ᵥ (y - x) = x ⬝ᵥ (M *ᵥ y) - x ⬝ᵥ (M *ᵥ x) - b ⬝ᵥ y + b ⬝ᵥ x := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (M *ᵥ x) y, dotProduct_comm (M *ᵥ x) x,
      hsym y x]
    ring
  rw [e2]
  linarith

theorem Psi_conv (I : EllI d) (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef) (x y : Fin d → ℝ) :
    PsiI I x + gPsi I x ⬝ᵥ (y - x) ≤ PsiI I y := by
  set M := I.H.map ((↑) : ℤ → ℝ) with hM
  have hT : Mᵀ = M := by
    have h := hH.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hsym : ∀ u v : Fin d → ℝ, u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← hT, Matrix.vecMul_transpose, dotProduct_comm, hT]
  have hq := hH.dotProduct_mulVec_nonneg (y - x)
  simp only [star_trivial] at hq
  have e1 : (y - x) ⬝ᵥ (M *ᵥ (y - x)) = y ⬝ᵥ (M *ᵥ y) - 2 * (x ⬝ᵥ (M *ᵥ y)) + x ⬝ᵥ (M *ᵥ x) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym y x]
    ring
  unfold PsiI gPsi
  rw [← hM]
  set b : Fin d → ℝ := fun j => (I.g j : ℝ) with hb
  have e2 : (M *ᵥ x - b) ⬝ᵥ (y - x) = x ⬝ᵥ (M *ᵥ y) - x ⬝ᵥ (M *ᵥ x) - b ⬝ᵥ y + b ⬝ᵥ x := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (M *ᵥ x) y, dotProduct_comm (M *ᵥ x) x,
      hsym y x]
    ring
  rw [e2]
  linarith

theorem region_convex (I : EllI d) (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef) : Convex ℝ (regionI I) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx1 i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy1 i) hb
    have h3 : (I.β i : ℝ) = a * I.β i + b * I.β i := by rw [← add_mul, hab, one_mul]
    linarith
  · set z := a • x + b • y with hzdef
    have hx2' : PsiI I x ≤ I.ℓ := hx2
    have hy2' : PsiI I y ≤ I.ℓ := hy2
    show PsiI I z ≤ I.ℓ
    have c1 := mul_le_mul_of_nonneg_left (Psi_conv I hH z x) ha
    have c2 := mul_le_mul_of_nonneg_left (Psi_conv I hH z y) hb
    have hz0 : a • (x - z) + b • (y - z) = 0 := by
      funext j
      simp only [hzdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination (-(a * x j + b * y j)) * hab
    have key : a * (gPsi I z ⬝ᵥ (x - z)) + b * (gPsi I z ⬝ᵥ (y - z)) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← dotProduct_smul, ← dotProduct_smul, ← dotProduct_add, hz0,
        dotProduct_zero]
    have e1 : PsiI I z = a * PsiI I z + b * PsiI I z := by rw [← add_mul, hab, one_mul]
    have e2 : (I.ℓ : ℝ) = a * I.ℓ + b * I.ℓ := by rw [← add_mul, hab, one_mul]
    have f1 := mul_le_mul_of_nonneg_left hx2' ha
    have f2 := mul_le_mul_of_nonneg_left hy2' hb
    nlinarith
  · calc oNorm (a • x + b • y) ≤ oNorm (a • x) + oNorm (b • y) := AdversarialBco.Poly.LeanAp.oNorm_add_le _ _
      _ = a * oNorm x + b * oNorm y := by
          rw [AdversarialBco.Poly.LeanAp.oNorm_smul, AdversarialBco.Poly.LeanAp.oNorm_smul, abs_of_nonneg ha,
            abs_of_nonneg hb]
      _ ≤ a * I.R + b * I.R := by gcongr
      _ = I.R := by rw [← add_mul, hab, one_mul]

theorem region_compact (I : EllI d) : IsCompact (regionI I) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · unfold regionI
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const)
      (IsClosed.inter (isClosed_le (by fun_prop) continuous_const) (isClosed_le ?_ continuous_const))
    unfold AdversarialBco.Poly.oNorm
    fun_prop
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨I.R, fun y hy => ?_⟩
    have h3 : oNorm y ≤ I.R := hy.2.2
    have hR0 : (0 : ℝ) ≤ I.R := (AdversarialBco.Poly.LeanAp.oNorm_nonneg y).trans h3
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    intro i
    rw [Real.norm_eq_abs]
    exact (AdversarialBco.Poly.LeanAp.abs_apply_le_oNorm y i).trans h3

theorem psd_entry_sq (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) (i k : Fin d) :
    M i k ^ 2 ≤ M i i * M k k := by
  have hs : M k i = M i k := by
    have := hM.isHermitian.apply i k
    simpa [star_trivial] using this
  have Q : ∀ a b : ℝ, 0 ≤ a ^ 2 * M i i + 2 * a * b * M i k + b ^ 2 * M k k := by
    intro a b
    have h := hM.dotProduct_mulVec_nonneg (Pi.single i a + Pi.single k b)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single,
      single_dotProduct, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply] at h
    rw [hs] at h
    nlinarith [h]
  have hii : 0 ≤ M i i := by simpa using Q 1 0
  have hkk : 0 ≤ M k k := by simpa using Q 0 1
  have Q1 := Q (M i k) (-M i i)
  have Q2 := Q (M k k) (-M i k)
  have Q3 := Q 1 (-M i k)
  rcases hii.lt_or_eq with hi | hi
  · by_contra hc
    rw [not_le] at hc
    have : M i i * (M i i * M k k - M i k ^ 2) < 0 := mul_neg_of_pos_of_neg hi (by linarith)
    nlinarith
  rcases hkk.lt_or_eq with hk | hk
  · by_contra hc
    rw [not_le] at hc
    have : M k k * (M i i * M k k - M i k ^ 2) < 0 := mul_neg_of_pos_of_neg hk (by linarith)
    nlinarith
  rw [← hi, ← hk] at Q3 ⊢
  nlinarith

theorem mulVec_le_trace (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosSemidef) (z : Fin d → ℝ) :
    oNorm (M *ᵥ z) ≤ M.trace * oNorm z := by
  have hsq : oNorm (M *ᵥ z) ^ 2 ≤ (M.trace * oNorm z) ^ 2 := by
    rw [mul_pow, AdversarialBco.Poly.LeanAp.oNorm_sq, AdversarialBco.Poly.LeanAp.oNorm_sq]
    have hCS : ∀ i, (M *ᵥ z) i ^ 2 ≤ (∑ k, M i k ^ 2) * (z ⬝ᵥ z) := by
      intro i
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => M i k) z
      simpa [Matrix.mulVec, dotProduct, sq] using this
    have hF : ∑ i, ∑ k, M i k ^ 2 ≤ M.trace ^ 2 := by
      calc ∑ i, ∑ k, M i k ^ 2 ≤ ∑ i, ∑ k, M i i * M k k :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => psd_entry_sq M hM i k
        _ = M.trace ^ 2 := by simp [Matrix.trace, Matrix.diag, sq, Finset.sum_mul_sum]
    have hz : 0 ≤ z ⬝ᵥ z := by rw [← AdversarialBco.Poly.LeanAp.oNorm_sq]; positivity
    calc (M *ᵥ z) ⬝ᵥ (M *ᵥ z) = ∑ i, (M *ᵥ z) i ^ 2 := by simp [dotProduct, sq]
      _ ≤ ∑ i, (∑ k, M i k ^ 2) * (z ⬝ᵥ z) := Finset.sum_le_sum fun i _ => hCS i
      _ = (∑ i, ∑ k, M i k ^ 2) * (z ⬝ᵥ z) := by rw [Finset.sum_mul]
      _ ≤ M.trace ^ 2 * (z ⬝ᵥ z) := mul_le_mul_of_nonneg_right hF hz
  exact (pow_le_pow_iff_left₀ (AdversarialBco.Poly.LeanAp.oNorm_nonneg _)
    (mul_nonneg hM.trace_nonneg (AdversarialBco.Poly.LeanAp.oNorm_nonneg _)) two_ne_zero).1 hsq

theorem grad_lip (I : EllI d) (hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef) (hDf : 0 < I.Df) (z w : Fin d → ℝ)
    (hz : oNorm z ≤ I.Rb) : gG I z ⬝ᵥ w ≤ (I.LG : ℝ) * oNorm w := by
  have hD : (0 : ℝ) < I.Df := by exact_mod_cast hDf
  set M := I.P.map ((↑) : ℤ → ℝ) with hM
  have htr : M.trace = ((I.P.trace : ℤ) : ℝ) := by
    simp only [hM, Matrix.trace, Matrix.diag, Matrix.map_apply]
    push_cast
    rfl
  have hw := AdversarialBco.Poly.LeanAp.oNorm_nonneg w
  have e1 : (M *ᵥ z) ⬝ᵥ w ≤ M.trace * I.Rb * oNorm w := by
    calc (M *ᵥ z) ⬝ᵥ w ≤ oNorm (M *ᵥ z) * oNorm w := AdversarialBco.Poly.LeanAp.dot_le _ _
      _ ≤ (M.trace * oNorm z) * oNorm w := mul_le_mul_of_nonneg_right (mulVec_le_trace M hP z) hw
      _ ≤ M.trace * I.Rb * oNorm w := by
          apply mul_le_mul_of_nonneg_right _ hw
          exact mul_le_mul_of_nonneg_left hz hP.trace_nonneg
  have e2 : -((fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ w) ≤ (∑ j, |(I.f j : ℝ)|) / I.Df * oNorm w := by
    calc -((fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ w) ≤ |(fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ w| := neg_le_abs _
      _ ≤ ∑ j, |(I.f j : ℝ) / I.Df * w j| := by unfold dotProduct; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(I.f j : ℝ)| / I.Df * oNorm w := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_div, abs_of_pos hD]
          exact mul_le_mul_of_nonneg_left (AdversarialBco.Poly.LeanAp.abs_apply_le_oNorm w j) (by positivity)
      _ = (∑ j, |(I.f j : ℝ)|) / I.Df * oNorm w := by rw [← Finset.sum_mul, ← Finset.sum_div]
  have hLG : (I.LG : ℝ) = M.trace * I.Rb + (∑ j, |(I.f j : ℝ)|) / I.Df := by
    unfold EllI.LG
    rw [htr]
    push_cast
    ring
  unfold gG
  rw [← hM, sub_dotProduct, hLG, add_mul]
  linarith

theorem LG_nonneg (I : EllI d) (hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef) : 0 ≤ I.LG := by
  unfold EllI.LG
  have htr : (0 : ℝ) ≤ (I.P.map ((↑) : ℤ → ℝ)).trace := hP.trace_nonneg
  have htrZ : (0 : ℤ) ≤ I.P.trace := by
    have h : (I.P.map ((↑) : ℤ → ℝ)).trace = ((I.P.trace : ℤ) : ℝ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
      push_cast
      rfl
    rw [h] at htr
    exact_mod_cast htr
  have h1 : (0 : ℚ) ≤ (I.P.trace : ℚ) * I.Rb := mul_nonneg (by exact_mod_cast htrZ) (Nat.cast_nonneg _)
  have h2 : (0 : ℚ) ≤ (∑ i, |(I.f i : ℚ)|) / I.Df :=
    div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Nat.cast_nonneg _)
  linarith

/-! ## Leaves: the parameters -/

theorem theta_spec (I : EllI d) (he : 0 < I.e) : 0 < I.θ ∧ I.θ ≤ 1 ∧ 3 * I.θ * I.LG * I.Rb ≤ I.e := by
  unfold EllI.θ
  split_ifs with h
  · exact ⟨one_pos, le_rfl, by linarith⟩
  · have hlt := lt_of_not_ge h
    have hpos : 0 < 3 * I.LG * I.Rb := lt_trans he hlt
    have hne : I.LG * I.Rb ≠ 0 := by
      intro h0
      rw [mul_assoc, h0, mul_zero] at hpos
      exact lt_irrefl _ hpos
    refine ⟨div_pos he hpos, (div_le_one hpos).mpr hlt.le, le_of_eq ?_⟩
    field_simp
    exact div_self hne

theorem rho_le (I : EllI d) (he : 0 < I.e) (hr : 0 < I.r) : (1 : ℚ) / 2 ^ I.j ≤ I.θ * min I.r 1 := by
  obtain ⟨hθ0, -, -⟩ := theta_spec I he
  have hm : 0 < min I.r 1 := lt_min hr one_pos
  have hx : 0 < 1 / (I.θ * min I.r 1) := by positivity
  unfold EllI.j lgQ
  have h1 : 1 / (I.θ * min I.r 1) ≤ (2 : ℚ) ^ Nat.clog 2 ⌈1 / (I.θ * min I.r 1)⌉₊ := by
    calc 1 / (I.θ * min I.r 1) ≤ (⌈1 / (I.θ * min I.r 1)⌉₊ : ℚ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
  calc (1 : ℚ) / 2 ^ Nat.clog 2 ⌈1 / (I.θ * min I.r 1)⌉₊ ≤ 1 / (1 / (I.θ * min I.r 1)) :=
        one_div_le_one_div_of_le hx h1
    _ = I.θ * min I.r 1 := one_div_one_div _

theorem Rb_spec (I : EllI d) (hR : 1 ≤ I.R) : 1 ≤ I.Rb ∧ I.R ≤ I.Rb := by
  refine ⟨Nat.succ_le_of_lt (Nat.ceil_pos.mpr (by linarith)), Nat.le_ceil _⟩

theorem Rb_rho (I : EllI d) : (I.Rb : ℝ) ≤ 2 ^ I.lam * (1 / 2 ^ I.j) := by
  unfold EllI.lam
  rw [pow_add, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
  exact_mod_cast Nat.le_pow_clog (by norm_num) I.Rb

theorem p_prec (I : EllI d) (hd : 1 ≤ d) :
    (1 : ℝ) / 2 ^ I.p ≤ (1 / 2 ^ I.j) ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)) := by
  unfold EllI.p
  have hc' : ((d : ℝ) ^ 2 * (d + 1)) ≤ 2 ^ Nat.clog 2 (d ^ 2 * (d + 1)) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (d ^ 2 * (d + 1))
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2p : (2 : ℝ) ^ (6 + Nat.clog 2 (d ^ 2 * (d + 1)) + 2 * I.j) =
      64 * (2 ^ I.j) ^ 2 * 2 ^ Nat.clog 2 (d ^ 2 * (d + 1)) := by
    rw [pow_add, pow_add, pow_mul']
    ring
  rw [h2p, div_pow, one_pow, div_div, one_div_le_one_div (by positivity) (by positivity)]
  rw [show (2 ^ I.j : ℝ) ^ 2 * (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)) = 64 * (2 ^ I.j) ^ 2 * ((d : ℝ) ^ 2 * (d + 1)) by ring]
  exact mul_le_mul_of_nonneg_left hc' (by positivity)

theorem sqrt_Lam (I : EllI d) : Real.sqrt (I.Lam : ℝ) = I.LamH := by
  unfold EllI.Lam EllI.LamH
  push_cast
  rw [show (I.Rb : ℝ) ^ 2 * 2 ^ (6 * I.lam + 2) = ((I.Rb : ℝ) * 2 ^ (3 * I.lam + 1)) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem q_prec (I : EllI d) (hd : 1 ≤ d) (hR : 1 ≤ I.Rb) :
    4 / (1 / 2 ^ I.j : ℝ) ≤ 2 ^ I.q ∧
      4 * Real.sqrt (I.Lam : ℝ) / (1 / 2 ^ I.j * 2 ^ I.q) ≤ 1 / 2 ^ I.j / (64 * d) := by
  have hq : (2 : ℝ) ^ I.q = 2 ^ 9 * 2 ^ (Nat.clog 2 d) * 2 ^ (Nat.clog 2 I.Rb) * 2 ^ (3 * I.lam) * (2 ^ I.j) ^ 2 := by
    unfold EllI.q
    ring
  have hdc : (d : ℝ) ≤ 2 ^ Nat.clog 2 d := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) d
  have hRc : (I.Rb : ℝ) ≤ 2 ^ Nat.clog 2 I.Rb := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) I.Rb
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hj : (1 : ℝ) ≤ 2 ^ I.j := one_le_pow₀ (by norm_num)
  constructor
  · rw [hq, show 4 / (1 / 2 ^ I.j : ℝ) = 4 * 2 ^ I.j by field_simp]
    calc (4 : ℝ) * 2 ^ I.j ≤ 2 ^ 9 * (2 ^ I.j) ^ 2 := by nlinarith
      _ = 2 ^ 9 * 1 * 1 * 1 * (2 ^ I.j) ^ 2 := by ring
      _ ≤ 2 ^ 9 * 2 ^ (Nat.clog 2 d) * 2 ^ (Nat.clog 2 I.Rb) * 2 ^ (3 * I.lam) * (2 ^ I.j) ^ 2 := by
          gcongr <;> exact one_le_pow₀ (by norm_num)
  · rw [sqrt_Lam, hq, div_le_div_iff₀ (by positivity) (by positivity)]
    unfold EllI.LamH
    push_cast
    calc 4 * ((I.Rb : ℝ) * 2 ^ (3 * I.lam + 1)) * (64 * d) = 2 ^ 9 * d * I.Rb * 2 ^ (3 * I.lam) := by ring
      _ ≤ 2 ^ 9 * 2 ^ (Nat.clog 2 d) * 2 ^ (Nat.clog 2 I.Rb) * 2 ^ (3 * I.lam) := by gcongr
      _ = _ := by field_simp

theorem two_j_le_p (I : EllI d) : 2 * I.j ≤ I.p := by
  unfold EllI.p
  omega

theorem cap_gam (I : EllI d) (hd : 2 ≤ d) (k : ℕ) (hk : k ≤ I.N) : (I.Rb : ℝ) ^ 2 * gam d ^ k ≤ I.Lam := by
  have h := pb_cap_general d I.lam k hd (by simpa [EllI.N] using hk)
  have hL : (I.Lam : ℝ) = (I.Rb : ℝ) ^ 2 * 2 ^ (6 * I.lam + 2) := by simp [EllI.Lam]
  rw [hL]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem N_cast (I : EllI d) : (I.N : ℝ) = 2 * d * ((d : ℝ) + 1) * I.lam + 1 := by
  unfold EllI.N
  push_cast
  ring

/-! ## Leaves: the tests of steps 1 to 4 -/

theorem cut_out (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (hR : 0 < I.R)
    (h : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2) (y : Fin d → ℝ) (hy : y ∈ regionI I) :
    vZ a ⬝ᵥ (y - vR s a) < 0 := by
  have hRr : (0 : ℝ) < I.R := by exact_mod_cast hR
  have hy3 : oNorm y ≤ I.R := hy.2.2
  have hden : (0 : ℝ) < I.R.den := by exact_mod_cast I.R.den_pos
  have hcast : (2 : ℝ) ^ (2 * s) * (I.R.num : ℝ) ^ 2 < ((a ⬝ᵥ a : ℤ) : ℝ) * (I.R.den : ℝ) ^ 2 := by
    exact_mod_cast h
  have hsq : ((2 : ℝ) ^ s * I.R) ^ 2 < oNorm (vZ a) ^ 2 := by
    rw [AdversarialBco.Poly.LeanAp.oNorm_sq, ← dotZ_cast, Rat.cast_def]
    have : ((2 : ℝ) ^ s * ((I.R.num : ℝ) / (I.R.den : ℝ))) ^ 2 =
        (2 : ℝ) ^ (2 * s) * (I.R.num : ℝ) ^ 2 / (I.R.den : ℝ) ^ 2 := by
      field_simp
      ring
    rw [this, div_lt_iff₀ (by positivity)]
    exact hcast
  have hlt : (2 : ℝ) ^ s * I.R < oNorm (vZ a) :=
    lt_of_pow_lt_pow_left₀ 2 (AdversarialBco.Poly.LeanAp.oNorm_nonneg _) hsq
  have hpos : 0 < oNorm (vZ a) := lt_of_le_of_lt (by positivity) hlt
  have e1 : vZ a ⬝ᵥ y ≤ oNorm (vZ a) * I.R :=
    (AdversarialBco.Poly.LeanAp.dot_le _ _).trans
      (mul_le_mul_of_nonneg_left hy3 (AdversarialBco.Poly.LeanAp.oNorm_nonneg _))
  have e2 : vZ a ⬝ᵥ vR s a = oNorm (vZ a) ^ 2 / 2 ^ s := by
    rw [vR_eq, dotProduct_smul, smul_eq_mul, ← AdversarialBco.Poly.LeanAp.oNorm_sq]
    ring
  rw [dotProduct_sub, e2]
  have : oNorm (vZ a) * I.R < oNorm (vZ a) ^ 2 / 2 ^ s := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem cut_psi (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef)
    (h : 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)) (y : Fin d → ℝ)
    (hy : y ∈ regionI I) : vZ (I.H *ᵥ a - (2 ^ s : ℤ) • I.g) ⬝ᵥ (y - vR s a) < 0 := by
  have hy2 : PsiI I y ≤ I.ℓ := hy.2.1
  have hc := Psi_conv I hH (vR s a) y
  have hψ : (I.ℓ : ℝ) < PsiI I (vR s a) := by
    rw [Psi_vR, lt_div_iff₀ (by positivity)]
    have : (2 : ℝ) ^ (2 * s + 1) * I.ℓ < ((a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) : ℤ) : ℝ) := by
      exact_mod_cast h
    linarith
  have hg : vZ (I.H *ᵥ a - (2 ^ s : ℤ) • I.g) = (2 : ℝ) ^ s • gPsi I (vR s a) := by
    funext i
    have h1 := congrFun (mulVecZ_cast I.H a) i
    have h2 : (I.H.map ((↑) : ℤ → ℝ) *ᵥ vR s a) i = 1 / 2 ^ s * (I.H.map ((↑) : ℤ → ℝ) *ᵥ vZ a) i := by
      rw [vR_eq, Matrix.mulVec_smul]
      rfl
    rw [Pi.smul_apply, smul_eq_mul]
    unfold gPsi
    rw [Pi.sub_apply, h2, ← h1]
    simp only [vZ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  rw [hg, smul_dotProduct, smul_eq_mul]
  have : gPsi I (vR s a) ⬝ᵥ (y - vR s a) < 0 := by linarith
  exact mul_neg_of_pos_of_neg (by positivity) this

theorem test_in (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (hR : 0 < I.R)
    (h1 : ¬ 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2)
    (h2 : ∀ i, I.α i ⬝ᵥ a ≤ 2 ^ s * I.β i)
    (h3 : ¬ 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)) :
    vR s a ∈ regionI I := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have h2i : ((I.α i ⬝ᵥ a : ℤ) : ℝ) ≤ 2 ^ s * I.β i := by exact_mod_cast h2 i
    show vZ (I.α i) ⬝ᵥ vR s a ≤ I.β i
    rw [lin_vR, div_le_iff₀ (by positivity)]
    linarith
  · replace h3 := not_lt.mp h3
    have h3' : ((a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) : ℤ) : ℝ) ≤ 2 ^ (2 * s + 1) * I.ℓ := by
      exact_mod_cast h3
    show PsiI I (vR s a) ≤ I.ℓ
    rw [Psi_vR, div_le_iff₀ (by positivity)]
    linarith
  · replace h1 := not_lt.mp h1
    have hc : ((a ⬝ᵥ a : ℤ) : ℝ) * (I.R.den : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * s) * (I.R.num : ℝ) ^ 2 := by
      exact_mod_cast h1
    have hRr : (0 : ℝ) < I.R := by exact_mod_cast hR
    have hden : (0 : ℝ) < I.R.den := by exact_mod_cast I.R.den_pos
    have hsq : oNorm (vR s a) ^ 2 ≤ (I.R : ℝ) ^ 2 := by
      rw [AdversarialBco.Poly.LeanAp.oNorm_sq, vR_eq, dotProduct_smul, smul_dotProduct, ← dotZ_cast, Rat.cast_def]
      simp only [smul_eq_mul]
      have : (1 / 2 ^ s : ℝ) * (1 / 2 ^ s * ((a ⬝ᵥ a : ℤ) : ℝ)) = ((a ⬝ᵥ a : ℤ) : ℝ) / 2 ^ (2 * s) := by
        field_simp
        ring
      rw [this, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    exact (pow_le_pow_iff_left₀ (AdversarialBco.Poly.LeanAp.oNorm_nonneg _) hRr.le two_ne_zero).1 hsq

theorem gh_eq (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (hDf : 0 < I.Df) :
    vZ (ghI I s a) = ((2 : ℝ) ^ s * I.Df) • gG I (vR s a) := by
  have hD : (I.Df : ℝ) ≠ 0 := by positivity
  funext i
  have h1 := congrFun (mulVecZ_cast I.P a) i
  have h2 : (I.P.map ((↑) : ℤ → ℝ) *ᵥ vR s a) i = 1 / 2 ^ s * (I.P.map ((↑) : ℤ → ℝ) *ᵥ vZ a) i := by
    rw [vR_eq, Matrix.mulVec_smul]
    rfl
  rw [Pi.smul_apply, smul_eq_mul]
  unfold gG ghI
  rw [Pi.sub_apply, h2, ← h1, Matrix.mulVec_smul]
  simp only [vZ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp

theorem V_eq (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (hDf : 0 < I.Df) :
    ((VI I s a : ℤ) : ℝ) = 2 ^ (2 * s + 1) * I.Df * GI I (vR s a) := by
  have hD : (I.Df : ℝ) ≠ 0 := by positivity
  have hl : (fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ vR s a = ((I.f ⬝ᵥ a : ℤ) : ℝ) / 2 ^ s / I.Df := by
    rw [← lin_vR]
    simp only [vZ, dotProduct, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold VI GI
  rw [quad_vR, hl]
  push_cast
  field_simp
  ring

/-! ## Leaves: the start of ELL-R and the intervals of BIS-R -/

theorem start_mR (p Rb : ℕ) :
    mR p (((2 : ℤ) ^ p * (Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)) = ((Rb : ℝ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i k
  by_cases h : i = k
  · subst h
    simp only [mR, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    push_cast
    field_simp
  · simp only [mR, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_ne h, smul_eq_mul, mul_zero, Int.cast_zero]

theorem inE_scalar (c : ℝ) (hc : 0 < c) (a x : Fin d → ℝ) :
    InE (c • (1 : Matrix (Fin d) (Fin d) ℝ)) a x ↔ (x - a) ⬝ᵥ (x - a) ≤ c := by
  unfold InE
  have hinv : (c • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = c⁻¹ • 1 :=
    Matrix.inv_eq_left_inv (by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul])
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hc, mul_one]

theorem bis_mid (lo hi : ℤ) (Rb n : ℕ) (h : hi - lo = 2 * Rb * 2 ^ (n + 1)) :
    (lo + hi) / 2 - lo = 2 * Rb * 2 ^ n ∧ hi - (lo + hi) / 2 = 2 * Rb * 2 ^ n := by
  have h' : hi - lo = 2 * (2 * (Rb : ℤ) * 2 ^ n) := by rw [h, pow_succ]; ring
  generalize (2 : ℤ) * Rb * 2 ^ n = s at *
  omega

theorem dot_fin_one (c : Fin 1 → ℤ) (z : Fin 1 → ℝ) (s : ℕ) (a : ℤ) :
    vZ c ⬝ᵥ (z - vR s (fun _ => a)) = (c 0 : ℝ) * (z 0 - a / 2 ^ s) := by
  simp [dotProduct, Fin.sum_univ_one, vZ, vR]

theorem bis_contra (z0 : Fin 1 → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (lo hi : ℤ) (s Rb : ℕ) (hw : hi - lo = 2 * Rb)
    (hRb : (Rb : ℝ) ≤ 2 ^ (s - 1) * ρ) (hs : 1 ≤ s)
    (hB : ∀ x, InB z0 ρ x → (lo : ℝ) / 2 ^ s ≤ x 0 ∧ x 0 ≤ (hi : ℝ) / 2 ^ s) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hRb
  have hw' : (hi : ℝ) - lo = 2 * Rb := by exact_mod_cast hw
  have hin : ∀ c : ℝ, c ^ 2 ≤ ρ ^ 2 → InB z0 ρ (z0 + fun _ => c) := by
    intro c hc
    unfold InB
    rw [add_sub_cancel_left]
    simpa [dotProduct, sq] using hc
  have e1 := (hB _ (hin ρ le_rfl)).2
  have e2 := (hB _ (hin (-ρ) (by rw [neg_sq]))).1
  simp only [Pi.add_apply] at e1 e2
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have e3 : (hi : ℝ) / 2 ^ (t + 1) - lo / 2 ^ (t + 1) = Rb / 2 ^ t := by
    rw [← sub_div, hw', pow_succ]
    field_simp
  have h3 : (Rb : ℝ) / 2 ^ t ≤ ρ := by
    rw [div_le_iff₀ h2t]
    linarith
  linarith

/-! ## One test (steps 1 to 4) -/

theorem vZ_zero : vZ (0 : Fin d → ℤ) = 0 := by
  funext i; simp [vZ]

/-! ## The ball `B'` -/

theorem mem_region_norm (I : EllI d) (hR : 1 ≤ I.R) {x : Fin d → ℝ} (hx : x ∈ regionI I) : oNorm x ≤ I.Rb := by
  have h1 : oNorm x ≤ (I.R : ℝ) := hx.2.2
  have h2 : (I.R : ℝ) ≤ (I.Rb : ℝ) := by exact_mod_cast (Rb_spec I hR).2
  linarith

/-! ## ELL-R: the iterations (the claim `I_k`) -/

theorem inB_self (z0 : Fin d → ℝ) (ρ : ℝ) : InB z0 ρ z0 := by
  unfold InB
  rw [sub_self, dotProduct_zero]
  positivity

theorem exp_step (ω R : ℝ) (k : ℕ) :
    Real.exp (-ω) * (R * Real.exp (-ω * k)) = R * Real.exp (-ω * ((k + 1 : ℕ) : ℝ)) := by
  push_cast
  rw [show -ω * ((k : ℝ) + 1) = -ω * k + -ω by ring, Real.exp_add]
  ring

end AdversarialBco.Bit.ApQ
