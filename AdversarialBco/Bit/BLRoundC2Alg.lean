/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundBasic

@[expose] public section

/-!
# Piece C, C2: the generic lemmas of the test call and line μ

The selection lemma on the selection `selT` (`selT_spec`), the Hausdorff gap maps (`gap_map`,
`gap_ball`, `gap_disp`), the quadratics `ellF` and `df2Phi` (differences, Lipschitz bounds, convexity, the expansion
of the test statistic), the errors of E13 (`xi_err`) and E16 (`s5_err`, `dw_err`, `ellF_err`), the positive
definiteness of BL's `P' = B' B'ᵀ`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open Matrix

theorem selT_root (α0 α1 α2 : ℝ) (h0 : 0 < α0) (h2 : 0 ≤ α2) (h1 : α0 + α1 - α2 ≤ 0) :
    0 < Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1 ∧
      0 < 2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1) ∧
      2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1) ≤ 1 ∧
      α0 + α1 * (2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1)) -
        α2 * (2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1)) ^ 2 = 0 := by
  set D := α1 ^ 2 + 4 * α0 * α2 with hD
  set s := Real.sqrt D with hs
  have hD_nonneg : 0 ≤ D := by
    rw [hD]
    nlinarith
  have hs_sq : s ^ 2 = D := Real.sq_sqrt hD_nonneg
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_ge_α1 : α1 ≤ s := by
    have h_sq : α1 ^ 2 ≤ s ^ 2 := by
      rw [hs_sq, hD]
      nlinarith
    nlinarith
  have hs_ge_neg_α1 : -α1 ≤ s := by
    have h_sq : (-α1) ^ 2 ≤ s ^ 2 := by
      rw [hs_sq, hD, neg_sq]
      nlinarith
    nlinarith
  have h_pos_denom : 0 < s - α1 := by
    by_contra! hle
    have h_eq : s = α1 := by linarith
    have h_alpha2_zero : α2 = 0 := by
      have h_sq_eq : s ^ 2 = α1 ^ 2 := by rw [h_eq]
      rw [hs_sq, hD] at h_sq_eq
      nlinarith
    have h_sum : α0 + α1 ≤ 0 := by linarith
    have h_α1_nonneg : 0 ≤ α1 := by linarith
    nlinarith
  have h_t_pos : 0 < 2 * α0 / (s - α1) := by
    refine div_pos (by nlinarith) h_pos_denom
  have h_t_le_one : 2 * α0 / (s - α1) ≤ 1 := by
    have h_num : 2 * α0 ≤ s - α1 := by
      by_cases h : 2 * α0 + α1 ≤ 0
      · linarith
      · have h_sq : (2 * α0 + α1) ^ 2 ≤ s ^ 2 := by
          rw [hs_sq, hD]
          nlinarith
        have h_nonneg_sum : 0 ≤ 2 * α0 + α1 := by linarith
        nlinarith
    exact (div_le_one (by linarith)).mpr h_num
  have h_eq : α0 + α1 * (2 * α0 / (s - α1)) - α2 * (2 * α0 / (s - α1)) ^ 2 = 0 := by
    set t := 2 * α0 / (s - α1) with ht
    have ht_mul : t * (s - α1) = 2 * α0 := by
      dsimp [t]
      field_simp [h_pos_denom.ne']
    have h_4α0α2_eq : 4 * α0 * α2 = (s - α1) * (s + α1) := by
      have h : (s - α1) * (s + α1) = s ^ 2 - α1 ^ 2 := by ring
      rw [h, hs_sq, hD]
      nlinarith
    have h_2α2_t_mul : 2 * α2 * t * (s - α1) = (s - α1) * (s + α1) := by
      calc
        2 * α2 * t * (s - α1) = 2 * α2 * (t * (s - α1)) := by ring
        _ = 2 * α2 * (2 * α0) := by rw [ht_mul]
        _ = 4 * α0 * α2 := by ring
        _ = (s - α1) * (s + α1) := by rw [h_4α0α2_eq]
    have h_2α2_t : 2 * α2 * t = s + α1 := by
      have h_factor : (s - α1) * (2 * α2 * t - (s + α1)) = 0 := by
        nlinarith
      have h_ne_zero : s - α1 ≠ 0 := by linarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h | h
      · exact (h_ne_zero h).elim
      · nlinarith
    have h_mul : (α0 + α1 * t - α2 * t ^ 2) * (s - α1) = 0 := by
      calc
        (α0 + α1 * t - α2 * t ^ 2) * (s - α1) =
            α0 * (s - α1) + α1 * t * (s - α1) - α2 * t ^ 2 * (s - α1) := by ring
        _ = α0 * (s - α1) + α1 * (t * (s - α1)) - α2 * t * (t * (s - α1)) := by ring
        _ = α0 * (s - α1) + α1 * (2 * α0) - α2 * t * (2 * α0) := by
          simp [ht_mul]
        _ = α0 * (s - α1 + 2 * α1) - 2 * α0 * (α2 * t) := by ring
        _ = α0 * (s + α1) - 2 * α0 * (α2 * t) := by ring
        _ = α0 * (s + α1 - 2 * α2 * t) := by ring
        _ = α0 * (s + α1 - (s + α1)) := by rw [h_2α2_t]
        _ = 0 := by ring
    have h_result : α0 + α1 * t - α2 * t ^ 2 = 0 := by
      have h_ne_zero : s - α1 ≠ 0 := by linarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h_mul with h | h
      · exact h
      · exact (h_ne_zero h).elim
    dsimp [t] at h_result
    exact h_result
  exact ⟨h_pos_denom, h_t_pos, h_t_le_one, h_eq⟩

theorem selT_spec {d : ℕ} (hd : 1 ≤ d) (κ : ℝ) (h : Fin d → ℝ)
    (P : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) (c0 : Fin d → ℝ) (r : ℝ) (p : Fin d → ℝ) (fire : Bool)
    (Q : Set (Fin d → ℝ)) (μ ηT eT : ℝ) (hQ : Convex ℝ Q) (hball : oBall c0 r ⊆ Q) (hr : 0 < r)
    (hP : ∀ v, μ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) (hp : p ∈ Q)
    (hH1 : ∀ y ∈ Q, κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y) ≤ κ + h ⬝ᵥ p - p ⬝ᵥ (P *ᵥ p) + ηT)
    (hH2c : fire = false → T < κ + h ⬝ᵥ p - p ⬝ᵥ (P *ᵥ p))
    (hH2f : fire = true → κ + h ⬝ᵥ p - p ⬝ᵥ (P *ᵥ p) ≤ T + eT)
    (hH3 : ηT + eT ≤ μ * r ^ 2) (hη : 0 ≤ ηT) (he : 0 ≤ eT) :
    selT κ h P T c0 r p fire ∈ Q ∧
      (∀ y ∈ Q, κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y) ≤
        κ + h ⬝ᵥ selT κ h P T c0 r p fire - selT κ h P T c0 r p fire ⬝ᵥ (P *ᵥ selT κ h P T c0 r p fire) +
          (ηT + eT)) ∧
      (κ + h ⬝ᵥ selT κ h P T c0 r p fire - selT κ h P T c0 r p fire ⬝ᵥ (P *ᵥ selT κ h P T c0 r p fire) ≤ T ↔
        fire = true) ∧
      (fire = false → selT κ h P T c0 r p fire = p) := by
  set F : (Fin d → ℝ) → ℝ := fun y => κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y) with hF
  set gr := h - (P + Pᵀ) *ᵥ c0 with hgr
  set v : Fin d → ℝ := if gr = 0 then (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)
    else (oNorm gr)⁻¹ • (-gr) with hv
  set q := c0 + r • v with hq
  set dv := q - p with hdv
  set α0 := F p - T with hα0
  set α1 := (h - (P + Pᵀ) *ᵥ p) ⬝ᵥ dv with hα1
  set α2 := dv ⬝ᵥ (P *ᵥ dv) with hα2
  set t := 2 * α0 / (Real.sqrt (α1 ^ 2 + 4 * α0 * α2) - α1) with ht
  have hsel : selT κ h P T c0 r p fire = if fire = true ∧ T < F p then p + t • dv else p := rfl
  have hH1' : ∀ y ∈ Q, F y ≤ F p + ηT := hH1
  have hH2c' : fire = false → T < F p := hH2c
  have hH2f' : fire = true → F p ≤ T + eT := hH2f
  suffices H : selT κ h P T c0 r p fire ∈ Q ∧ (∀ y ∈ Q, F y ≤ F (selT κ h P T c0 r p fire) + (ηT + eT)) ∧
      (F (selT κ h P T c0 r p fire) ≤ T ↔ fire = true) ∧ (fire = false → selT κ h P T c0 r p fire = p) from H
  rw [hsel]
  by_cases hc : fire = true ∧ T < F p
  swap
  · rw [ite_eq_right hc]
    refine ⟨hp, fun y hy => by linarith [hH1' y hy], ?_, fun _ => rfl⟩
    cases fire
    · simp only [Bool.false_eq_true, iff_false, not_le]
      exact hH2c' rfl
    · simp only [true_and, not_lt] at hc
      simp only [iff_true]
      exact hc
  rw [ite_eq_left hc]
  obtain ⟨hfire, hTp⟩ := hc
  have hμ : 0 ≤ μ := by
    by_contra hneg
    push Not at hneg
    nlinarith [pow_pos hr 2]
  have hdd : ∀ w : Fin d → ℝ, 0 ≤ w ⬝ᵥ w := fun w => by rw [← oNorm_sq]; positivity
  have hpsd : ∀ w : Fin d → ℝ, 0 ≤ w ⬝ᵥ (P *ᵥ w) := fun w =>
    le_trans (mul_nonneg hμ (hdd w)) (hP w)
  have hexp : ∀ (x w : Fin d → ℝ) (s : ℝ),
      F (x + s • w) = F x + s * ((h - (P + Pᵀ) *ᵥ x) ⬝ᵥ w) - s ^ 2 * (w ⬝ᵥ (P *ᵥ w)) := by
    intro x w s
    have e1 : (Pᵀ *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (P *ᵥ w) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    have e2 : (P *ᵥ x) ⬝ᵥ w = w ⬝ᵥ (P *ᵥ x) := dotProduct_comm _ _
    simp only [hF, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.add_mulVec, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, sub_dotProduct, e1, e2]
    ring
  -- the unit vector `v`
  have hvv : v ⬝ᵥ v = 1 := by
    by_cases hg : gr = 0
    · have : v = fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0 := by rw [hv, ite_eq_left hg]
      rw [this, dotProduct, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
      · simp
      · intro i _ hi
        have : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
        simp [this]
      · simp
    · have : v = (oNorm gr)⁻¹ • (-gr) := by rw [hv, ite_eq_right hg]
      have hn : oNorm gr ≠ 0 := fun h0 => hg ((AdversarialBco.Poly.AP.oNorm_eq_zero_iff).1 h0)
      rw [this, dotProduct_smul, smul_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg,
        ← oNorm_sq, smul_eq_mul, smul_eq_mul]
      field_simp
  have hgv : gr ⬝ᵥ v ≤ 0 := by
    by_cases hg : gr = 0
    · rw [hg, zero_dotProduct]
    · have : v = (oNorm gr)⁻¹ • (-gr) := by rw [hv, ite_eq_right hg]
      rw [this, dotProduct_smul, dotProduct_neg, ← oNorm_sq, smul_eq_mul]
      have := oNorm_nonneg gr
      have : 0 ≤ (oNorm gr)⁻¹ := inv_nonneg.2 this
      nlinarith [sq_nonneg (oNorm gr)]
  have hc0 : c0 ∈ Q := hball (by
    show oNorm (c0 - c0) ≤ r
    rw [sub_self, ← sq_le_sq₀ (oNorm_nonneg _) hr.le, oNorm_sq, zero_dotProduct]
    positivity)
  have hqQ : q ∈ Q := hball (by
    show oNorm (q - c0) ≤ r
    have : q - c0 = r • v := by rw [hq]; abel
    rw [this, oNorm_smul, abs_of_pos hr]
    have : oNorm v = 1 := by
      rw [← sq_eq_sq₀ (oNorm_nonneg _) zero_le_one, oNorm_sq, hvv, one_pow]
    rw [this, mul_one])
  have hFq : F q ≤ T := by
    have e := hexp c0 v r
    have hvP : μ ≤ v ⬝ᵥ (P *ᵥ v) := by have := hP v; rwa [hvv, mul_one] at this
    have h1 := hH1' c0 hc0
    have h2 := hH2f' hfire
    have h3 : r * (gr ⬝ᵥ v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hgv
    have h4 : μ * r ^ 2 ≤ r ^ 2 * (v ⬝ᵥ (P *ᵥ v)) := by nlinarith [pow_pos hr 2]
    have : F q = F c0 + r * (gr ⬝ᵥ v) - r ^ 2 * (v ⬝ᵥ (P *ᵥ v)) := e
    linarith
  have h0 : 0 < α0 := by rw [hα0]; linarith
  have h2 : 0 ≤ α2 := hpsd dv
  have hpq : p + (1 : ℝ) • dv = q := by rw [one_smul, hdv]; abel
  have h1 : α0 + α1 - α2 ≤ 0 := by
    have e := hexp p dv 1
    rw [hpq] at e
    have : F q = F p + α1 - α2 := by rw [e]; ring
    rw [hα0]; linarith
  obtain ⟨-, ht0, ht1, hroot⟩ := selT_root α0 α1 α2 h0 h2 h1
  have hroot' : α0 + α1 * t - α2 * t ^ 2 = 0 := hroot
  have ht0' : 0 < t := ht0
  have ht1' : t ≤ 1 := ht1
  have hFs : F (p + t • dv) = T := by
    have e := hexp p dv t
    have : F (p + t • dv) = F p + t * α1 - t ^ 2 * α2 := e
    rw [this]; rw [hα0] at hroot'; linarith
  have hsQ : p + t • dv ∈ Q := by
    have e : p + t • dv = (1 - t) • p + t • q := by
      rw [hdv, smul_sub, sub_smul, one_smul]; abel
    rw [e]
    exact hQ hp hqQ (by linarith) ht0'.le (by ring)
  refine ⟨hsQ, fun y hy => ?_, ⟨fun _ => hfire, fun _ => hFs.le⟩, fun hf => ?_⟩
  · have := hH1' y hy
    have := hH2f' hfire
    rw [hFs]; linarith
  · rw [hfire] at hf; exact absurd hf (by decide)

theorem gap_map {d : ℕ} (Ke Ke' Q' : Set (Fin d → ℝ)) (Φ : (Fin d → ℝ) → ℝ)
    (R κ s L m0 D E1 : ℝ) (y0 : Fin d → ℝ) (hKe : Convex ℝ Ke) (hR : ∀ y ∈ Ke, oNorm y ≤ R)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hK' : ∀ y ∈ Ke, κ • y ∈ Ke')
    (hΦ : ConvexOn ℝ Ke Φ) (hy0 : y0 ∈ Ke) (hΦ0 : Φ y0 ≤ L - m0)
    (hE1 : ∀ y ∈ Ke, Φ (κ • y) ≤ Φ y + E1) (hsm : D + E1 ≤ s * m0)
    (hQ' : ∀ y ∈ Ke', Φ y ≤ L - D → y ∈ Q') :
    ∀ y ∈ Ke, Φ y ≤ L → κ • ((1 - s) • y + s • y0) ∈ Q' ∧
      oNorm (y - κ • ((1 - s) • y + s • y0)) ≤ 2 * R * s + (1 - κ) * R := by
  intro y hy hΦyL
  set z := (1 - s) • y + s • y0 with hz
  have hz_mem : z ∈ Ke := by
    dsimp [z]
    exact hKe hy hy0 (by linarith) hs0 (by ring)
  have hΦz_le : Φ z ≤ (1 - s) • Φ y + s • Φ y0 := by
    dsimp [z]
    exact hΦ.2 hy hy0 (by linarith) hs0 (by ring)
  have hΦz : Φ z ≤ L - s * m0 := by
    have h1 : (1 - s) • Φ y ≤ (1 - s) • L := by
      simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hΦyL (by linarith)
    have h2 : s • Φ y0 ≤ s • (L - m0) := by
      simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hΦ0 hs0
    calc
      Φ z ≤ (1 - s) • Φ y + s • Φ y0 := hΦz_le
      _ ≤ (1 - s) • L + s • (L - m0) := by linarith
      _ = L - s * m0 := by ring
  have hκz_mem : κ • z ∈ Ke' := hK' z hz_mem
  have hΦκz_le : Φ (κ • z) ≤ Φ z + E1 := hE1 z hz_mem
  have hΦκz : Φ (κ • z) ≤ L - D := by
    calc
      Φ (κ • z) ≤ Φ z + E1 := hΦκz_le
      _ ≤ (L - s * m0) + E1 := by linarith
      _ = L - (s * m0 - E1) := by ring
      _ ≤ L - D := by
        have h : D ≤ s * m0 - E1 := by linarith
        linarith
  have hQ'κz : κ • z ∈ Q' := hQ' (κ • z) hκz_mem hΦκz
  have h_distrib : y - κ • z = s • (y - y0) + (1 - κ) • z := by
    have hL : y - κ • ((1 - s) • y + s • y0) = (1 - κ * (1 - s)) • y + (-(κ * s)) • y0 := by
      calc
        y - κ • ((1 - s) • y + s • y0)
            = y - (κ • ((1 - s) • y) + κ • (s • y0)) := by rw [smul_add]
        _ = y - ((κ * (1 - s)) • y + (κ * s) • y0) := by simp [smul_smul]
        _ = y - (κ * (1 - s)) • y - (κ * s) • y0 := by abel
        _ = ((1 : ℝ) • y - (κ * (1 - s)) • y) - (κ * s) • y0 := by simp
        _ = (1 - κ * (1 - s)) • y - (κ * s) • y0 := by
          simp [sub_smul]
        _ = (1 - κ * (1 - s)) • y + (-(κ * s)) • y0 := by rw [sub_eq_add_neg, neg_smul]
    have hR : s • (y - y0) + (1 - κ) • ((1 - s) • y + s • y0) = (1 - κ * (1 - s)) • y + (-(κ * s)) • y0 := by
      calc
        s • (y - y0) + (1 - κ) • ((1 - s) • y + s • y0)
            = (s • y - s • y0) + ((1 - κ) • ((1 - s) • y) + (1 - κ) • (s • y0)) := by rw [smul_sub, smul_add]
        _ = (s • y - s • y0) + (((1 - κ) * (1 - s)) • y + ((1 - κ) * s) • y0) := by simp [smul_smul]
        _ = (s • y + ((1 - κ) * (1 - s)) • y) + ((-s) • y0 + ((1 - κ) * s) • y0) := by
          simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
        _ = (s + (1 - κ) * (1 - s)) • y + ((-s) + (1 - κ) * s) • y0 := by rw [add_smul, add_smul]
        _ = (1 - κ * (1 - s)) • y + (-(κ * s)) • y0 := by
          have h1 : s + (1 - κ) * (1 - s) = 1 - κ * (1 - s) := by ring
          have h2 : (-s) + (1 - κ) * s = -(κ * s) := by ring
          simp [h1, h2]
    rw [hz, hL, hR]
  have h_norm_bound : oNorm (y - κ • z) ≤ 2 * R * s + (1 - κ) * R := by
    rw [h_distrib]
    have h_triangle : oNorm (s • (y - y0) + (1 - κ) • z) ≤ oNorm (s • (y - y0)) + oNorm ((1 - κ) • z) := by
      rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
      exact norm_add_le _ _
    have h_smul1 : oNorm (s • (y - y0)) = s * oNorm (y - y0) := by
      rw [oNorm_eq_norm, oNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    have h_smul2 : oNorm ((1 - κ) • z) = (1 - κ) * oNorm z := by
      rw [oNorm_eq_norm, oNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h_sub : oNorm (y - y0) ≤ oNorm y + oNorm y0 := by
      rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm, WithLp.toLp_sub]
      exact norm_sub_le _ _
    have h_z : oNorm z ≤ R := hR z hz_mem
    have h_y : oNorm y ≤ R := hR y hy
    have h_y0 : oNorm y0 ≤ R := hR y0 hy0
    calc
      oNorm (s • (y - y0) + (1 - κ) • z) ≤ oNorm (s • (y - y0)) + oNorm ((1 - κ) • z) := h_triangle
      _ = s * oNorm (y - y0) + (1 - κ) * oNorm z := by rw [h_smul1, h_smul2]
      _ ≤ s * (oNorm y + oNorm y0) + (1 - κ) * oNorm z := by
        have hterm : s * oNorm (y - y0) ≤ s * (oNorm y + oNorm y0) :=
          mul_le_mul_of_nonneg_left h_sub hs0
        linarith
      _ ≤ s * (R + R) + (1 - κ) * R := by
        have h1 : s * (oNorm y + oNorm y0) ≤ s * (R + R) :=
          mul_le_mul_of_nonneg_left (by linarith) hs0
        have h2 : (1 - κ) * oNorm z ≤ (1 - κ) * R :=
          mul_le_mul_of_nonneg_left h_z (by linarith)
        linarith
      _ = 2 * R * s + (1 - κ) * R := by ring
  exact And.intro hQ'κz h_norm_bound

theorem gap_ball {d : ℕ} (Q Q' : Set (Fin d → ℝ)) (κ s r : ℝ)
    (c y0 : Fin d → ℝ) (hκ : 0 < κ) (hs1 : s < 1) (hr : 0 ≤ r)
    (hT : ∀ y ∈ Q, κ • ((1 - s) • y + s • y0) ∈ Q') (hball : oBall c r ⊆ Q) :
    oBall (κ • ((1 - s) • c + s • y0)) (κ * (1 - s) * r) ⊆ Q' := by
  have h1s_pos : 0 < 1 - s := by linarith
  have ht_pos : 0 < κ * (1 - s) := by positivity
  set t := κ * (1 - s) with ht_def
  have ht_pos' : 0 < t := ht_pos
  have ht_ne_zero : t ≠ 0 := by linarith
  have ht_inv_pos : 0 < t⁻¹ := by exact inv_pos_of_pos ht_pos'
  have habs_inv_t : |t⁻¹| = t⁻¹ := abs_of_pos ht_inv_pos
  intro x hx
  rw [oBall, Set.mem_setOf_eq] at hx
  set y := c + (t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))) with hy_def
  have hy_sub : y - c = (t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))) := by
    dsimp [y]
    abel
  have hy_in_ball : y ∈ oBall c r := by
    rw [oBall, Set.mem_setOf_eq, hy_sub]
    have h_norm_smul : oNorm ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0)))) = t⁻¹ * oNorm (x - (κ • ((1 - s) • c + s • y0))) := by
      rw [oNorm_eq_norm, oNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, habs_inv_t]
    rw [h_norm_smul]
    have hx_bound : oNorm (x - (κ • ((1 - s) • c + s • y0))) ≤ t * r := hx
    calc
      t⁻¹ * oNorm (x - (κ • ((1 - s) • c + s • y0))) ≤ t⁻¹ * (t * r) := by gcongr
      _ = (t⁻¹ * t) * r := by ring
      _ = 1 * r := by field_simp [ht_ne_zero]
      _ = r := by simp
  have hy_in_Q : y ∈ Q := hball hy_in_ball
  have hTy_eq_x : κ • ((1 - s) • y + s • y0) = x := by
    calc
      κ • ((1 - s) • y + s • y0) = κ • ((1 - s) • (c + (t⁻¹) • (x - (κ • ((1 - s) • c + s • y0)))) + s • y0) := by rfl
      _ = κ • (((1 - s) • c + (1 - s) • ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))))) + s • y0) := by
        simp [smul_add]
      _ = κ • (((1 - s) • c + s • y0) + (1 - s) • ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))))) := by
        abel
      _ = κ • ((1 - s) • c + s • y0) + κ • ((1 - s) • ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))))) := by
        rw [smul_add]
      _ = (κ • ((1 - s) • c + s • y0)) + (κ * (1 - s)) • ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0)))) := by
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = (κ • ((1 - s) • c + s • y0)) + t • ((t⁻¹) • (x - (κ • ((1 - s) • c + s • y0)))) := by rfl
      _ = (κ • ((1 - s) • c + s • y0)) + (t * t⁻¹) • (x - (κ • ((1 - s) • c + s • y0))) := by
        rw [smul_smul]
      _ = (κ • ((1 - s) • c + s • y0)) + 1 • (x - (κ • ((1 - s) • c + s • y0))) := by
        simp [ht_ne_zero]
      _ = (κ • ((1 - s) • c + s • y0)) + (x - (κ • ((1 - s) • c + s • y0))) := by simp [one_smul]
      _ = x := by abel
  have hTx_in_Q' : κ • ((1 - s) • y + s • y0) ∈ Q' := hT y hy_in_Q
  rw [hTy_eq_x] at hTx_in_Q'
  exact hTx_in_Q'

theorem ellF_diff {d : ℕ} (P P' : Matrix (Fin d) (Fin d) ℝ) (w w' y : Fin d → ℝ) :
    |ellF P' w' y - ellF P w y| ≤
      oNorm (y - w') ^ 2 / 2 * opN (P' - P) +
        oNorm (w - w') * opN P * (oNorm (y - w') + oNorm (y - w)) / 2 := by
  set a := y - w' with ha
  set b := y - w with hb
  have hab : a - b = w - w' := by
    dsimp [a, b]
    abel
  have hdiff : ellF P' w' y - ellF P w y = (1/2 : ℝ) * (a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b))) := by
    dsimp [ellF, a, b]
    have hkey : (y - w') ⬝ᵥ (P' *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w)) =
        (y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) + ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w))) := by
      have h1 : (y - w') ⬝ᵥ (P' *ᵥ (y - w')) - (y - w') ⬝ᵥ (P *ᵥ (y - w')) = (y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) := by
        calc
          (y - w') ⬝ᵥ (P' *ᵥ (y - w')) - (y - w') ⬝ᵥ (P *ᵥ (y - w'))
              = (y - w') ⬝ᵥ (P' *ᵥ (y - w') - P *ᵥ (y - w')) := by rw [dotProduct_sub]
          _ = (y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) := by rw [Matrix.sub_mulVec]
      have h2 : (y - w') ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w)) =
          ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w))) := by
        have hh1 : (y - w') ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w')) = ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) := by
          rw [← sub_dotProduct]
        have hh2 : (y - w) ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w)) = (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w))) := by
          rw [← dotProduct_sub, Matrix.mulVec_sub]
          simp [Matrix.mulVec_sub]
        calc
          (y - w') ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w))
              = ((y - w') ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w'))) +
                ((y - w) ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w))) := by ring
          _ = ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w))) := by rw [hh1, hh2]
      calc
        (y - w') ⬝ᵥ (P' *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w))
            = ((y - w') ⬝ᵥ (P' *ᵥ (y - w')) - (y - w') ⬝ᵥ (P *ᵥ (y - w'))) +
              ((y - w') ⬝ᵥ (P *ᵥ (y - w')) - (y - w) ⬝ᵥ (P *ᵥ (y - w))) := by ring
        _ = (y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) + (((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w)))) := by rw [h1, h2]
        _ = (y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) + ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w))) := by ring
    calc
      ellF P' w' y - ellF P w y
          = (1/2 : ℝ) * ((y - w') ⬝ᵥ (P' *ᵥ (y - w'))) - (1/2 : ℝ) * ((y - w) ⬝ᵥ (P *ᵥ (y - w))) := by rfl
      _ = (1/2 : ℝ) * (((y - w') ⬝ᵥ (P' *ᵥ (y - w'))) - ((y - w) ⬝ᵥ (P *ᵥ (y - w)))) := by ring
      _ = (1/2 : ℝ) * ((y - w') ⬝ᵥ ((P' - P) *ᵥ (y - w')) + ((y - w') - (y - w)) ⬝ᵥ (P *ᵥ (y - w')) + (y - w) ⬝ᵥ (P *ᵥ ((y - w') - (y - w)))) := by rw [hkey]
      _ = (1/2 : ℝ) * (a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b))) := by
        simp [a, b]
  have hbound1 : |a ⬝ᵥ ((P' - P) *ᵥ a)| ≤ oNorm a ^ 2 * opN (P' - P) := by
    have h1 : |a ⬝ᵥ ((P' - P) *ᵥ a)| ≤ oNorm a * oNorm ((P' - P) *ᵥ a) := abs_dot_le _ _
    have h2 : oNorm ((P' - P) *ᵥ a) ≤ opN (P' - P) * oNorm a := oNorm_mulVec_le (P' - P) a
    have ha : 0 ≤ oNorm a := oNorm_nonneg _
    have hP : 0 ≤ opN (P' - P) := opN_nonneg _
    apply le_trans h1
    nlinarith
  have hbound2 : |(a - b) ⬝ᵥ (P *ᵥ a)| ≤ oNorm (a - b) * opN P * oNorm a := by
    have h1 : |(a - b) ⬝ᵥ (P *ᵥ a)| ≤ oNorm (a - b) * oNorm (P *ᵥ a) := abs_dot_le _ _
    have h2 : oNorm (P *ᵥ a) ≤ opN P * oNorm a := oNorm_mulVec_le P a
    have ha : 0 ≤ oNorm (a - b) := oNorm_nonneg _
    have hb : 0 ≤ oNorm a := oNorm_nonneg _
    have hP : 0 ≤ opN P := opN_nonneg _
    apply le_trans h1
    nlinarith
  have hbound3 : |b ⬝ᵥ (P *ᵥ (a - b))| ≤ oNorm b * opN P * oNorm (a - b) := by
    have h1 : |b ⬝ᵥ (P *ᵥ (a - b))| ≤ oNorm b * oNorm (P *ᵥ (a - b)) := abs_dot_le _ _
    have h2 : oNorm (P *ᵥ (a - b)) ≤ opN P * oNorm (a - b) := oNorm_mulVec_le P (a - b)
    have ha : 0 ≤ oNorm b := oNorm_nonneg _
    have hb : 0 ≤ oNorm (a - b) := oNorm_nonneg _
    have hP : 0 ≤ opN P := opN_nonneg _
    apply le_trans h1
    nlinarith
  rw [hdiff]
  have hsum : |(1/2 : ℝ) * (a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b)))| ≤
      oNorm a ^ 2 / 2 * opN (P' - P) + oNorm (a - b) * opN P * (oNorm a + oNorm b) / 2 := by
    calc
      |(1/2 : ℝ) * (a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b)))|
          = |(1/2 : ℝ)| * |a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b))| := by rw [abs_mul]
      _ = (1/2 : ℝ) * |a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b))| := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      _ ≤ (1/2 : ℝ) * (|a ⬝ᵥ ((P' - P) *ᵥ a)| + |(a - b) ⬝ᵥ (P *ᵥ a)| + |b ⬝ᵥ (P *ᵥ (a - b))|) := by
        gcongr
        calc
          |a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a) + b ⬝ᵥ (P *ᵥ (a - b))|
              ≤ |a ⬝ᵥ ((P' - P) *ᵥ a) + (a - b) ⬝ᵥ (P *ᵥ a)| + |b ⬝ᵥ (P *ᵥ (a - b))| := abs_add_le _ _
          _ ≤ (|a ⬝ᵥ ((P' - P) *ᵥ a)| + |(a - b) ⬝ᵥ (P *ᵥ a)|) + |b ⬝ᵥ (P *ᵥ (a - b))| := by
            gcongr; exact abs_add_le _ _
          _ = |a ⬝ᵥ ((P' - P) *ᵥ a)| + |(a - b) ⬝ᵥ (P *ᵥ a)| + |b ⬝ᵥ (P *ᵥ (a - b))| := by ring
      _ ≤ (1/2 : ℝ) * ((oNorm a ^ 2 * opN (P' - P)) + (oNorm (a - b) * opN P * oNorm a) + (oNorm b * opN P * oNorm (a - b))) := by
        have hpos : 0 ≤ (1/2 : ℝ) := by norm_num
        refine mul_le_mul_of_nonneg_left ?_ hpos
        nlinarith [hbound1, hbound2, hbound3]
      _ = oNorm a ^ 2 / 2 * opN (P' - P) + oNorm (a - b) * opN P * oNorm a / 2 + oNorm b * opN P * oNorm (a - b) / 2 := by ring
      _ = oNorm a ^ 2 / 2 * opN (P' - P) + oNorm (a - b) * opN P * (oNorm a + oNorm b) / 2 := by ring
  -- Now rewrite the RHS using hab
  simpa [hab, a, b] using hsum

theorem phi_diff {d : ℕ} (P P' : Matrix (Fin d) (Fin d) ℝ) (b b' : Fin d → ℝ)
    (k k' R : ℝ) (y : Fin d → ℝ) (hy : oNorm y ≤ R) :
    |df2Phi P' b' k' y - df2Phi P b k y| ≤
      R ^ 2 / 2 * opN (P' - P) + R * oNorm (b' - b) + |k' - k| := by
  have hR : 0 ≤ R := le_trans (oNorm_nonneg y) hy
  have hdiff : df2Phi P' b' k' y - df2Phi P b k y =
      (1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y)) - (b' - b) ⬝ᵥ y + (k' - k) := by
    dsimp [df2Phi]
    have hsub : y ⬝ᵥ (P' *ᵥ y) - y ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ ((P' - P) *ᵥ y) := by
      calc
        y ⬝ᵥ (P' *ᵥ y) - y ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P' *ᵥ y - P *ᵥ y) := by
          rw [dotProduct_sub]
        _ = y ⬝ᵥ ((P' - P) *ᵥ y) := by rw [sub_mulVec]
    calc
      (1 / 2 * (y ⬝ᵥ (P' *ᵥ y)) - b' ⬝ᵥ y + k') - (1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k)
          = (1/2 : ℝ) * (y ⬝ᵥ (P' *ᵥ y) - y ⬝ᵥ (P *ᵥ y)) - (b' - b) ⬝ᵥ y + (k' - k) := by
        ring_nf; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y)) - (b' - b) ⬝ᵥ y + (k' - k) := by rw [hsub]
  rw [hdiff]
  have h_abs_triangle : ∀ (a b c : ℝ), |a + b + c| ≤ |a| + |b| + |c| := by
    intro a b c; calc
      |a + b + c| = |(a + b) + c| := by ring
      _ ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ |a| + |b| + |c| := by nlinarith [abs_add_le a b]
  calc
    |(1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y)) - (b' - b) ⬝ᵥ y + (k' - k)|
        = |(1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y)) + (-(b' - b) ⬝ᵥ y) + (k' - k)| := by
      ring_nf; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ |(1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y))| + |-(b' - b) ⬝ᵥ y| + |k' - k| :=
      h_abs_triangle _ _ _
    _ = |(1/2 : ℝ) * (y ⬝ᵥ ((P' - P) *ᵥ y))| + |(b' - b) ⬝ᵥ y| + |k' - k| := by
      simp [abs_sub_comm]
    _ = |(1/2 : ℝ)| * |y ⬝ᵥ ((P' - P) *ᵥ y)| + |(b' - b) ⬝ᵥ y| + |k' - k| := by rw [abs_mul]
    _ = (1/2 : ℝ) * |y ⬝ᵥ ((P' - P) *ᵥ y)| + |(b' - b) ⬝ᵥ y| + |k' - k| := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    _ ≤ (1/2 : ℝ) * (oNorm y * (opN (P' - P) * oNorm y)) + oNorm (b' - b) * oNorm y + |k' - k| := by
      have h1 : |y ⬝ᵥ ((P' - P) *ᵥ y)| ≤ oNorm y * (opN (P' - P) * oNorm y) := by
        calc
          |y ⬝ᵥ ((P' - P) *ᵥ y)| ≤ oNorm y * oNorm ((P' - P) *ᵥ y) := abs_dot_le _ _
          _ ≤ oNorm y * (opN (P' - P) * oNorm y) := by
            have h := oNorm_mulVec_le (P' - P) y
            have hy_nonneg : 0 ≤ oNorm y := oNorm_nonneg _
            nlinarith
      have h2 : |(b' - b) ⬝ᵥ y| ≤ oNorm (b' - b) * oNorm y := abs_dot_le _ _
      gcongr
    _ = (1/2 : ℝ) * (oNorm y * opN (P' - P) * oNorm y) + oNorm (b' - b) * oNorm y + |k' - k| := by ring
    _ ≤ (1/2 : ℝ) * (R * opN (P' - P) * R) + R * oNorm (b' - b) + |k' - k| := by
      have hy_nonneg : 0 ≤ oNorm y := oNorm_nonneg _
      have hb_nonneg : 0 ≤ oNorm (b' - b) := oNorm_nonneg _
      have hopN_nonneg : 0 ≤ opN (P' - P) := opN_nonneg _
      have hy_le_R : oNorm y ≤ R := hy
      have hsq : oNorm y * oNorm y ≤ R * R := by
        nlinarith
      have hterm1 : oNorm y * opN (P' - P) * oNorm y ≤ R * opN (P' - P) * R := by
        calc
          oNorm y * opN (P' - P) * oNorm y = opN (P' - P) * (oNorm y * oNorm y) := by ring
          _ ≤ opN (P' - P) * (R * R) := mul_le_mul_of_nonneg_left hsq hopN_nonneg
          _ = R * opN (P' - P) * R := by ring
      have hterm2 : oNorm (b' - b) * oNorm y ≤ R * oNorm (b' - b) := by
        calc
          oNorm (b' - b) * oNorm y ≤ oNorm (b' - b) * R := mul_le_mul_of_nonneg_left hy_le_R hb_nonneg
          _ = R * oNorm (b' - b) := mul_comm _ _
      nlinarith
    _ = R ^ 2 / 2 * opN (P' - P) + R * oNorm (b' - b) + |k' - k| := by ring

theorem quad_concave_le {d : ℕ} (κ : ℝ) (h : Fin d → ℝ)
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : ∀ v, 0 ≤ v ⬝ᵥ (P *ᵥ v)) (y z : Fin d → ℝ) :
    κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y) ≤
      κ + h ⬝ᵥ z - z ⬝ᵥ (P *ᵥ z) + oNorm (h - (P + Pᵀ) *ᵥ z) * oNorm (y - z) := by
  set v := y - z with hv
  have hy_eq : y = z + v := by
    dsimp [v]
    abel
  have hkey : z ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ z) = ((P + Pᵀ) *ᵥ z) ⬝ᵥ v := by
    have h1 : z ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (Pᵀ *ᵥ z) := by
      simpa [Matrix.transpose_transpose] using dotProduct_transpose_mulVec Pᵀ z v
    calc
      z ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ z)
          = v ⬝ᵥ (Pᵀ *ᵥ z) + v ⬝ᵥ (P *ᵥ z) := by rw [h1]
      _ = v ⬝ᵥ ((Pᵀ + P) *ᵥ z) := by rw [add_mulVec, dotProduct_add]
      _ = ((Pᵀ + P) *ᵥ z) ⬝ᵥ v := by rw [dotProduct_comm]
      _ = ((P + Pᵀ) *ᵥ z) ⬝ᵥ v := by rw [add_comm]
  have hFdiff : (κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y)) - (κ + h ⬝ᵥ z - z ⬝ᵥ (P *ᵥ z)) =
      (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v - v ⬝ᵥ (P *ᵥ v) := by
    calc
      (κ + h ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y)) - (κ + h ⬝ᵥ z - z ⬝ᵥ (P *ᵥ z))
          = h ⬝ᵥ (y - z) - (y ⬝ᵥ (P *ᵥ y) - z ⬝ᵥ (P *ᵥ z)) := by
            simp [dotProduct_sub]
            ring
      _ = h ⬝ᵥ v - ((z + v) ⬝ᵥ (P *ᵥ (z + v)) - z ⬝ᵥ (P *ᵥ z)) := by
        rw [← hv, ← hy_eq]
      _ = h ⬝ᵥ v - (((z + v) ⬝ᵥ (P *ᵥ z) + (z + v) ⬝ᵥ (P *ᵥ v)) - z ⬝ᵥ (P *ᵥ z)) := by
        rw [mulVec_add, dotProduct_add]
      _ = h ⬝ᵥ v - (((z ⬝ᵥ (P *ᵥ z) + v ⬝ᵥ (P *ᵥ z)) + (z ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ v))) - z ⬝ᵥ (P *ᵥ z)) := by
        simp
      _ = h ⬝ᵥ v - (z ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ z) + v ⬝ᵥ (P *ᵥ v)) := by ring
      _ = (h ⬝ᵥ v - (z ⬝ᵥ (P *ᵥ v) + v ⬝ᵥ (P *ᵥ z))) - v ⬝ᵥ (P *ᵥ v) := by ring
      _ = (h ⬝ᵥ v - ((P + Pᵀ) *ᵥ z) ⬝ᵥ v) - v ⬝ᵥ (P *ᵥ v) := by rw [hkey]
      _ = (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v - v ⬝ᵥ (P *ᵥ v) := by
        rw [← sub_dotProduct]
  have h_nonneg : 0 ≤ v ⬝ᵥ (P *ᵥ v) := hP v
  have h_bound : (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v - v ⬝ᵥ (P *ᵥ v) ≤
      oNorm (h - (P + Pᵀ) *ᵥ z) * oNorm v := by
    have h1 : (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v - v ⬝ᵥ (P *ᵥ v) ≤ (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v := by
      nlinarith
    have h2 : (h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v ≤ |(h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v| := le_abs_self _
    have h3 : |(h - (P + Pᵀ) *ᵥ z) ⬝ᵥ v| ≤ oNorm (h - (P + Pᵀ) *ᵥ z) * oNorm v := abs_dot_le _ _
    nlinarith
  nlinarith

theorem ellF_lip {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (P *ᵥ v)) (w x x' : Fin d → ℝ) :
    ellF P w x' ≤ ellF P w x + oNorm (P *ᵥ (x' - w)) * oNorm (x' - x) := by
  have h_symm (u v : Fin d → ℝ) : u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := by
    calc
      u ⬝ᵥ (P *ᵥ v) = (Matrix.vecMul u P) ⬝ᵥ v := by rw [Matrix.dotProduct_mulVec]
      _ = v ⬝ᵥ (Matrix.vecMul u P) := by rw [dotProduct_comm]
      _ = v ⬝ᵥ (Pᵀ.mulVec u) := by
        have h_temp : Matrix.vecMul u P = Pᵀ.mulVec u := by
          rw [← Matrix.transpose_transpose P]
          exact Matrix.vecMul_transpose (A := Pᵀ) (x := u)
        rw [h_temp]
      _ = v ⬝ᵥ (P *ᵥ u) := by rw [hP]
  have h_expand : ((x' - w) ⬝ᵥ (P *ᵥ (x' - w))) - (((x' - w) - (x' - x)) ⬝ᵥ (P *ᵥ ((x' - w) - (x' - x)))) = 2 * ((x' - x) ⬝ᵥ (P *ᵥ (x' - w))) - ((x' - x) ⬝ᵥ (P *ᵥ (x' - x))) := by
    apply sub_eq_zero.mp
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    ring_nf
    -- Goal: -(w ⬝ᵥ P *ᵥ x') + x' ⬝ᵥ P *ᵥ w + x ⬝ᵥ P *ᵥ x' - x ⬝ᵥ P *ᵥ w - x' ⬝ᵥ P *ᵥ x + w ⬝ᵥ P *ᵥ x = 0
    -- Using h_symm to cancel pairs
    rw [h_symm x x', h_symm x w, h_symm x' w]
    ring
  have h_diff : ellF P w x' - ellF P w x = (x' - x) ⬝ᵥ (P *ᵥ (x' - w)) - (1/2 : ℝ) * ((x' - x) ⬝ᵥ (P *ᵥ (x' - x))) := by
    dsimp [ellF]
    have hx_sub_w : x - w = (x' - w) - (x' - x) := by abel
    rw [hx_sub_w]
    calc
      (1/2 : ℝ) * ((x' - w) ⬝ᵥ (P *ᵥ (x' - w))) - (1/2 : ℝ) * (((x' - w) - (x' - x)) ⬝ᵥ (P *ᵥ ((x' - w) - (x' - x))))
          = (1/2 : ℝ) * (((x' - w) ⬝ᵥ (P *ᵥ (x' - w))) - (((x' - w) - (x' - x)) ⬝ᵥ (P *ᵥ ((x' - w) - (x' - x))))) := by ring
      _ = (1/2 : ℝ) * (2 * ((x' - x) ⬝ᵥ (P *ᵥ (x' - w))) - ((x' - x) ⬝ᵥ (P *ᵥ (x' - x)))) := by rw [h_expand]
      _ = (x' - x) ⬝ᵥ (P *ᵥ (x' - w)) - (1/2 : ℝ) * ((x' - x) ⬝ᵥ (P *ᵥ (x' - x))) := by ring
  have h_bound : (x' - x) ⬝ᵥ (P *ᵥ (x' - w)) - (1/2 : ℝ) * ((x' - x) ⬝ᵥ (P *ᵥ (x' - x))) ≤ oNorm (P *ᵥ (x' - w)) * oNorm (x' - x) := by
    have h_nonpos : -(1/2 : ℝ) * ((x' - x) ⬝ᵥ (P *ᵥ (x' - x))) ≤ 0 := by
      have h_nonneg : 0 ≤ (x' - x) ⬝ᵥ (P *ᵥ (x' - x)) := hpsd (x' - x)
      linarith
    have h_main : (x' - x) ⬝ᵥ (P *ᵥ (x' - w)) ≤ oNorm (P *ᵥ (x' - w)) * oNorm (x' - x) := by
      have h_abs : |(x' - x) ⬝ᵥ (P *ᵥ (x' - w))| ≤ oNorm (x' - x) * oNorm (P *ᵥ (x' - w)) := abs_dot_le (x' - x) (P *ᵥ (x' - w))
      have h_le_abs : (x' - x) ⬝ᵥ (P *ᵥ (x' - w)) ≤ |(x' - x) ⬝ᵥ (P *ᵥ (x' - w))| := le_abs_self _
      have h_mul_comm : oNorm (x' - x) * oNorm (P *ᵥ (x' - w)) = oNorm (P *ᵥ (x' - w)) * oNorm (x' - x) := mul_comm _ _
      linarith
    linarith
  linarith

theorem xi_ellF {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P)
    (zz wv y : Fin d → ℝ) (hz : P *ᵥ zz = wv) (κ : ℝ) :
    κ + ((2 : ℝ) • wv) ⬝ᵥ y - y ⬝ᵥ (P *ᵥ y) = (κ + zz ⬝ᵥ (P *ᵥ zz)) - 2 * ellF P zz y := by
  have h_ellF : 2 * ellF P zz y = (y - zz) ⬝ᵥ (P *ᵥ (y - zz)) := by
    dsimp [ellF]
    ring
  rw [h_ellF]
  have h_expand : (y - zz) ⬝ᵥ (P *ᵥ (y - zz)) = y ⬝ᵥ (P *ᵥ y) - y ⬝ᵥ (P *ᵥ zz) - zz ⬝ᵥ (P *ᵥ y) + zz ⬝ᵥ (P *ᵥ zz) := by
    calc
      (y - zz) ⬝ᵥ (P *ᵥ (y - zz)) = (y - zz) ⬝ᵥ (P *ᵥ y - P *ᵥ zz) := by rw [Matrix.mulVec_sub]
      _ = (y - zz) ⬝ᵥ (P *ᵥ y) - (y - zz) ⬝ᵥ (P *ᵥ zz) := by rw [dotProduct_sub]
      _ = (y ⬝ᵥ (P *ᵥ y) - zz ⬝ᵥ (P *ᵥ y)) - (y ⬝ᵥ (P *ᵥ zz) - zz ⬝ᵥ (P *ᵥ zz)) := by rw [sub_dotProduct, sub_dotProduct]
      _ = y ⬝ᵥ (P *ᵥ y) - y ⬝ᵥ (P *ᵥ zz) - zz ⬝ᵥ (P *ᵥ y) + zz ⬝ᵥ (P *ᵥ zz) := by ring
  rw [h_expand]
  have h_smul : ((2 : ℝ) • wv) ⬝ᵥ y = 2 * (wv ⬝ᵥ y) := by
    rw [smul_dotProduct, smul_eq_mul]
  rw [h_smul]
  have h_zz_dot_Py : zz ⬝ᵥ (P *ᵥ y) = wv ⬝ᵥ y := by
    rw [← hP, dotProduct_transpose_mulVec, hz, dotProduct_comm]
  rw [h_zz_dot_Py]
  have h_y_dot_Pz : y ⬝ᵥ (P *ᵥ zz) = wv ⬝ᵥ y := by
    rw [hz, dotProduct_comm]
  rw [h_y_dot_Pz]
  ring

theorem obj_ellF {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P) (w y : Fin d → ℝ) :
    y ⬝ᵥ (P *ᵥ y) / 2 - (P *ᵥ w) ⬝ᵥ y = ellF P w y - w ⬝ᵥ (P *ᵥ w) / 2 := by
  have h_symm (a b : Fin d → ℝ) : a ⬝ᵥ (P *ᵥ b) = (P *ᵥ a) ⬝ᵥ b := by
    calc
      a ⬝ᵥ (P *ᵥ b) = (a ᵥ* P) ⬝ᵥ b := by rw [Matrix.dotProduct_mulVec]
      _ = (a ᵥ* (Pᵀ)ᵀ) ⬝ᵥ b := by rw [transpose_transpose]
      _ = (Pᵀ *ᵥ a) ⬝ᵥ b := by rw [Matrix.vecMul_transpose]
      _ = (P *ᵥ a) ⬝ᵥ b := by rw [hP]
  have h_symm' : y ⬝ᵥ (P *ᵥ w) = (P *ᵥ w) ⬝ᵥ y := by
    rw [h_symm y w, dotProduct_comm, h_symm w y]
  unfold ellF
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [h_symm w y, h_symm']
  ring

theorem det_one_add_ne {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (hH : opN H < 1) :
    (1 + H).det ≠ 0 := by
  by_contra hdet
  have hzero : (1 + H).det = 0 := by simpa using hdet
  have h_exists := ((Matrix.exists_mulVec_eq_zero_iff (M := 1 + H)).mpr hzero)
  rcases h_exists with ⟨v, hv_ne, hv_eq⟩
  have hvec_eq : H *ᵥ v = -v := by
    have h_add : (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ v + H *ᵥ v = 0 := by
      calc
        (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ v + H *ᵥ v = ((1 : Matrix (Fin d) (Fin d) ℝ) + H) *ᵥ v := by
          rw [Matrix.add_mulVec]
        _ = 0 := hv_eq
    have h_one : (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ v = v := by simp
    have h_eq : v + H *ᵥ v = 0 := by
      simpa [h_one] using h_add
    exact eq_neg_of_add_eq_zero_right h_eq
  have h_onorm_eq : oNorm (H *ᵥ v) = oNorm v := by
    rw [hvec_eq]
    unfold oNorm
    simp [dotProduct_neg, neg_neg]
  have h_le : oNorm (H *ᵥ v) ≤ opN H * oNorm v := oNorm_mulVec_le H v
  have h_onorm_pos : 0 < oNorm v := by
    unfold oNorm
    refine Real.sqrt_pos.mpr ?_
    have h_dot_pos : 0 < v ⬝ᵥ v := by
      have h_nonneg : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
      have h_ne_zero : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr hv_ne
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    exact h_dot_pos
  have h_ineq : oNorm v ≤ opN H * oNorm v := by
    linarith
  have h_one_le : 1 ≤ opN H := by
    nlinarith
  linarith

theorem posDef_mul_transpose {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0) :
    (B * Bᵀ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · have h := Matrix.isHermitian_mul_conjTranspose_self B
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  · intro x hx
    have hstar : star x = x := by simp
    rw [hstar]
    have hdetT : Bᵀ.det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact hB
    have h_mulVec_ne_zero : Bᵀ.mulVec x ≠ 0 := by
      intro hzero
      have h_exists : ∃ v, v ≠ 0 ∧ Bᵀ.mulVec v = 0 := ⟨x, hx, hzero⟩
      have hdet0 := (Matrix.exists_mulVec_eq_zero_iff (M := Bᵀ)).mp h_exists
      exact hdetT hdet0
    have hcalc : x ⬝ᵥ (B * Bᵀ).mulVec x = (Bᵀ.mulVec x) ⬝ᵥ (Bᵀ.mulVec x) := by
      calc
        x ⬝ᵥ (B * Bᵀ).mulVec x
            = x ⬝ᵥ B.mulVec (Bᵀ.mulVec x) := by rw [Matrix.mulVec_mulVec]
        _ = (Matrix.vecMul x B) ⬝ᵥ (Bᵀ.mulVec x) := by rw [Matrix.dotProduct_mulVec]
        _ = (Bᵀ.mulVec x) ⬝ᵥ (Bᵀ.mulVec x) := by rw [Matrix.mulVec_transpose]
    rw [hcalc]
    have hpos : 0 < (Bᵀ.mulVec x) ⬝ᵥ star (Bᵀ.mulVec x) := by
      rw [Matrix.dotProduct_self_star_pos_iff]
      exact h_mulVec_ne_zero
    simpa using hpos

theorem xi_err {d : ℕ} (η η' tq l l' R Gb A B : ℝ) (G G' y : Fin d → ℝ)
    (hη : 0 ≤ η) (hηr : |η' - η| ≤ tq / 16 * η) (htq0 : 0 ≤ tq) (htq : tq ≤ 1 / 1000) (hR : 0 ≤ R)
    (hy : oNorm y ≤ R) (hl : |l| ≤ R * Gb) (hG : oNorm G ≤ Gb) (hdl : |l' - l| ≤ A)
    (hdG : oNorm (G' - G) ≤ B) :
    |η' * (l' - G' ⬝ᵥ y) - η * (l - G ⬝ᵥ y)| ≤
      η * (101 / 100) * (A + R * B) + η * tq / 16 * (21 / 10) * R * Gb := by
  have hGb_nonneg : 0 ≤ Gb := by
    have h := oNorm_nonneg G
    linarith
  have hA_nonneg : 0 ≤ A := by
    have h := abs_nonneg (l' - l)
    linarith
  have hB_nonneg : 0 ≤ B := by
    have h := oNorm_nonneg (G' - G)
    linarith
  have h_dot_Gy : |G ⬝ᵥ y| ≤ R * Gb := by
    have h1 : |G ⬝ᵥ y| ≤ oNorm G * oNorm y := abs_dot_le G y
    have h2 : oNorm G * oNorm y ≤ Gb * R :=
      mul_le_mul hG hy (oNorm_nonneg y) hGb_nonneg
    linarith
  have h_dot_G'y : |(G' - G) ⬝ᵥ y| ≤ R * B := by
    have h1 : |(G' - G) ⬝ᵥ y| ≤ oNorm (G' - G) * oNorm y := abs_dot_le (G' - G) y
    have h2 : oNorm (G' - G) * oNorm y ≤ B * R :=
      mul_le_mul hdG hy (oNorm_nonneg y) hB_nonneg
    linarith
  have h_bound_l' : |l' - G' ⬝ᵥ y| ≤ A + 2 * R * Gb + R * B := by
    have h_eq : l' - G' ⬝ᵥ y = (l' - l) + (l - G ⬝ᵥ y) - (G' - G) ⬝ᵥ y := by
      calc
        l' - G' ⬝ᵥ y = l' - G ⬝ᵥ y - (G' ⬝ᵥ y - G ⬝ᵥ y) := by ring
        _ = (l' - l + l - G ⬝ᵥ y) - (G' ⬝ᵥ y - G ⬝ᵥ y) := by ring
        _ = (l' - l) + (l - G ⬝ᵥ y) - (G' ⬝ᵥ y - G ⬝ᵥ y) := by ring
        _ = (l' - l) + (l - G ⬝ᵥ y) - (G' - G) ⬝ᵥ y := by simp [sub_dotProduct]
    rw [h_eq]
    calc
      |(l' - l) + (l - G ⬝ᵥ y) - (G' - G) ⬝ᵥ y| ≤
          |(l' - l) + (l - G ⬝ᵥ y)| + |(G' - G) ⬝ᵥ y| := abs_sub _ _
      _ ≤ (|l' - l| + |l - G ⬝ᵥ y|) + |(G' - G) ⬝ᵥ y| := by
        nlinarith [abs_add_le (l' - l) (l - G ⬝ᵥ y)]
      _ = |l' - l| + |l - G ⬝ᵥ y| + |(G' - G) ⬝ᵥ y| := by ring
      _ ≤ |l' - l| + (|l| + |G ⬝ᵥ y|) + |(G' - G) ⬝ᵥ y| := by
        have h1 : |l - G ⬝ᵥ y| ≤ |l| + |G ⬝ᵥ y| := abs_sub _ _
        nlinarith
      _ ≤ A + (R * Gb + R * Gb) + R * B := by
        nlinarith
      _ = A + 2 * R * Gb + R * B := by ring
  have h_bound_diff : |(l' - l) - (G' - G) ⬝ᵥ y| ≤ A + R * B := by
    calc
      |(l' - l) - (G' - G) ⬝ᵥ y| ≤ |l' - l| + |(G' - G) ⬝ᵥ y| := abs_sub _ _
      _ ≤ A + R * B := by nlinarith
  have h_eq : η' * (l' - G' ⬝ᵥ y) - η * (l - G ⬝ᵥ y) =
      (η' - η) * (l' - G' ⬝ᵥ y) + η * ((l' - l) - (G' - G) ⬝ᵥ y) := by
    simp [sub_dotProduct]
    ring
  rw [h_eq]
  calc
    |(η' - η) * (l' - G' ⬝ᵥ y) + η * ((l' - l) - (G' - G) ⬝ᵥ y)| ≤
        |(η' - η) * (l' - G' ⬝ᵥ y)| + |η * ((l' - l) - (G' - G) ⬝ᵥ y)| := abs_add_le _ _
    _ = |η' - η| * |l' - G' ⬝ᵥ y| + |η| * |(l' - l) - (G' - G) ⬝ᵥ y| := by
      simp [abs_mul]
    _ ≤ (tq / 16 * η) * (A + 2 * R * Gb + R * B) + η * (A + R * B) := by
      have hη_abs : |η| = η := abs_of_nonneg hη
      rw [hη_abs]
      have h_nonneg_abs2 : 0 ≤ |l' - G' ⬝ᵥ y| := abs_nonneg _
      have h_nonneg_tqη : 0 ≤ tq / 16 * η := by nlinarith
      have h1 : |η' - η| * |l' - G' ⬝ᵥ y| ≤ (tq / 16 * η) * (A + 2 * R * Gb + R * B) :=
        mul_le_mul hηr h_bound_l' h_nonneg_abs2 h_nonneg_tqη
      have h2 : η * |(l' - l) - (G' - G) ⬝ᵥ y| ≤ η * (A + R * B) :=
        mul_le_mul_of_nonneg_left h_bound_diff hη
      nlinarith
    _ = η * ((1 + tq / 16) * (A + R * B) + (tq / 16) * (2 * R * Gb)) := by ring
    _ ≤ η * ((101 / 100) * (A + R * B) + (tq / 16) * (21 / 10) * R * Gb) := by
      have h_ineq1 : 1 + tq / 16 ≤ 101 / 100 := by
        nlinarith
      have h_ineq2 : (2 : ℝ) ≤ 21 / 10 := by norm_num
      have h_nonneg1 : 0 ≤ A + R * B := by
        nlinarith
      have h_nonneg2 : 0 ≤ R * Gb := by
        nlinarith
      have h_main : (1 + tq / 16) * (A + R * B) + (tq / 16) * (2 * R * Gb) ≤
          (101 / 100) * (A + R * B) + (tq / 16) * (21 / 10) * R * Gb := by
        nlinarith
      nlinarith
    _ = η * (101 / 100) * (A + R * B) + η * tq / 16 * (21 / 10) * R * Gb := by ring

set_option maxHeartbeats 800000 in
theorem s5_err (η η' Y Y' ν' lam q q' tq eY Yb Dq : ℝ) (hη : 0 ≤ η)
    (hηr : |η' - η| ≤ tq / 16 * η) (hν : |ν' * (1 - lam) - 1| ≤ tq / 16) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 1000)
    (htq0 : 0 ≤ tq) (htq : tq ≤ 1 / 1000) (hY : |Y| ≤ Yb) (hYY : |Y' - Y| ≤ eY)
    (hq : 99 / 100 ≤ q) (hq' : 99 / 100 ≤ q') (hqq : |q' - q| ≤ Dq) :
    |η' * Y' * ν' / q' - η * Y / ((1 - lam) * q)| ≤ 103 / 100 * η * (eY + 3 * tq / 16 * Yb + Yb * Dq) := by
  have hpos_q : 0 < q := by linarith
  have hpos_q' : 0 < q' := by linarith
  have hpos_1ml : 0 < 1 - lam := by linarith
  set m := 1 / (1 - lam) with hm_def
  have hm_pos : 0 < m := div_pos (by norm_num) hpos_1ml
  have hm_nonneg : 0 ≤ m := by linarith
  have hm_ge_one : 1 ≤ m := by
    rw [hm_def]
    exact one_le_one_div hpos_1ml (by linarith)
  have hm_le : m ≤ 1000 / 999 := by
    rw [hm_def]
    have h : 999 / 1000 ≤ 1 - lam := by linarith
    have hpos_999 : 0 < (999 : ℝ) / 1000 := by norm_num
    have h_one_div : 1 / (1 - lam) ≤ 1 / (999 / 1000) :=
      (one_div_le_one_div hpos_1ml hpos_999).mpr h
    have h_eq : 1 / ((999 : ℝ) / 1000) = 1000 / 999 := by norm_num
    rw [h_eq] at h_one_div
    exact h_one_div
  set f := ν' * (1 - lam) - 1 with hf_def
  have hf_bound : |f| ≤ tq / 16 := hν
  have hν'_eq : ν' = m * (1 + f) := by
    dsimp [m, f]
    field_simp [hpos_1ml.ne.symm]
    ring
  have h_decomp : η' * Y' * ν' / q' - η * Y / ((1 - lam) * q) =
      η' * ν' * (Y' / q' - Y / q) + (η' * ν' - η * m) * (Y / q) := by
    field_simp [hpos_q.ne.symm, hpos_q'.ne.symm, hpos_1ml.ne.symm]
    dsimp [m]
    field_simp [hpos_1ml.ne.symm]
    ring
  rw [h_decomp]
  have h_tri : |η' * ν' * (Y' / q' - Y / q) + (η' * ν' - η * m) * (Y / q)| ≤
      |η' * ν'| * |Y' / q' - Y / q| + |η' * ν' - η * m| * |Y / q| := by
    calc
      |η' * ν' * (Y' / q' - Y / q) + (η' * ν' - η * m) * (Y / q)| ≤
          |η' * ν' * (Y' / q' - Y / q)| + |(η' * ν' - η * m) * (Y / q)| := abs_add_le _ _
      _ = |η' * ν'| * |Y' / q' - Y / q| + |(η' * ν' - η * m) * (Y / q)| := by rw [abs_mul]
      _ = |η' * ν'| * |Y' / q' - Y / q| + |η' * ν' - η * m| * |Y / q| := by simp [abs_mul]
  have h_eta_abs : |η'| ≤ η * (1 + tq / 16) := by
    calc
      |η'| = |η + (η' - η)| := by ring_nf
      _ ≤ |η| + |η' - η| := abs_add_le _ _
      _ = η + |η' - η| := by rw [abs_of_nonneg hη]
      _ ≤ η + (tq / 16 * η) := by nlinarith
      _ = η * (1 + tq / 16) := by ring
  have h_abs_1pf : |1 + f| ≤ 1 + tq / 16 := by
    calc
      |1 + f| ≤ |1| + |f| := abs_add_le _ _
      _ = 1 + |f| := by simp
      _ ≤ 1 + tq / 16 := by nlinarith
  have h_nu_abs : |ν'| ≤ m * (1 + tq / 16) := by
    rw [hν'_eq, abs_mul]
    have hm_abs : |m| = m := abs_of_nonneg hm_nonneg
    rw [hm_abs]
    exact mul_le_mul_of_nonneg_left h_abs_1pf hm_nonneg
  have h_hnv_abs : |η' * ν'| ≤ η * m * (1 + 2.001 * tq / 16) := by
    rw [abs_mul]
    have h_sq_bound : (1 + tq / 16) * (1 + tq / 16) ≤ 1 + 2.001 * tq / 16 := by
      nlinarith
    have h_nonneg_eta_m : 0 ≤ η * m := by nlinarith
    have h_mul : |η'| * |ν'| ≤ (η * (1 + tq / 16)) * (m * (1 + tq / 16)) :=
      mul_le_mul h_eta_abs h_nu_abs (abs_nonneg _) (by nlinarith)
    calc
      |η'| * |ν'| ≤ (η * (1 + tq / 16)) * (m * (1 + tq / 16)) := h_mul
      _ = η * m * ((1 + tq / 16) * (1 + tq / 16)) := by ring
      _ ≤ η * m * (1 + 2.001 * tq / 16) :=
        mul_le_mul_of_nonneg_left h_sq_bound h_nonneg_eta_m
  have h_hnv_diff_abs : |η' * ν' - η * m| ≤ (2.001 * tq / 16) * (η * m) := by
    have h_expr : η' * ν' - η * m = η * m * f + (η' - η) * m * (1 + f) := by
      calc
        η' * ν' - η * m = η' * (m * (1 + f)) - η * m := by rw [hν'_eq]
        _ = m * (η' * (1 + f) - η) := by ring
        _ = m * ((η + (η' - η)) * (1 + f) - η) := by ring
        _ = m * (η * (1 + f) + (η' - η) * (1 + f) - η) := by ring
        _ = m * (η * f + (η' - η) * (1 + f)) := by ring
        _ = η * m * f + (η' - η) * m * (1 + f) := by ring
    rw [h_expr]
    refine le_trans (abs_add_le _ _) ?_
    have h_nonneg_eta_m : 0 ≤ η * m := mul_nonneg hη hm_nonneg
    have h1 : |η * m * f| ≤ η * m * (tq / 16) := by
      calc
        |η * m * f| = |η * m| * |f| := abs_mul _ _
        _ = (|η| * |m|) * |f| := by rw [abs_mul]
        _ = (η * m) * |f| := by rw [abs_of_nonneg hη, abs_of_nonneg hm_nonneg]
        _ ≤ (η * m) * (tq / 16) := mul_le_mul_of_nonneg_left hf_bound h_nonneg_eta_m
        _ = η * m * (tq / 16) := by ring
    have h2 : |(η' - η) * m * (1 + f)| ≤ (tq / 16 * η) * m * (1 + tq / 16) := by
      calc
        |(η' - η) * m * (1 + f)| = |(η' - η) * m| * |1 + f| := abs_mul _ _
        _ = (|η' - η| * |m|) * |1 + f| := by rw [abs_mul]
        _ = (|η' - η| * m) * |1 + f| := by rw [abs_of_nonneg hm_nonneg]
        _ ≤ ((tq / 16 * η) * m) * |1 + f| := by
          have htemp : |η' - η| * m ≤ (tq / 16 * η) * m :=
            mul_le_mul_of_nonneg_right hηr hm_nonneg
          exact mul_le_mul_of_nonneg_right htemp (abs_nonneg _)
        _ ≤ ((tq / 16 * η) * m) * (1 + tq / 16) :=
          mul_le_mul_of_nonneg_left h_abs_1pf (by nlinarith)
        _ = (tq / 16 * η) * m * (1 + tq / 16) := by ring
    have h_sum : η * m * (tq / 16) + (tq / 16 * η) * m * (1 + tq / 16) ≤
        (2.001 * tq / 16) * (η * m) := by
      have h_factor : η * m * (tq / 16) + (tq / 16 * η) * m * (1 + tq / 16) =
          η * m * (2 * tq / 16 + (tq / 16) * (tq / 16)) := by ring
      have h_target : (2.001 * tq / 16) * (η * m) = η * m * (2.001 * tq / 16) := by ring
      rw [h_factor, h_target]
      apply mul_le_mul_of_nonneg_left ?_ h_nonneg_eta_m
      nlinarith
    nlinarith
  have hpos_099 : 0 < (0.99 : ℝ) := by norm_num
  have hpos_09801 : 0 < (0.9801 : ℝ) := by norm_num
  have h_nonneg_eY : 0 ≤ eY := by
    have : 0 ≤ |Y' - Y| := abs_nonneg _
    linarith
  have h_nonneg_Yb : 0 ≤ Yb := by
    have : 0 ≤ |Y| := abs_nonneg _
    linarith
  have h_nonneg_Dq : 0 ≤ Dq := by
    have : 0 ≤ |q' - q| := abs_nonneg _
    linarith
  have h_Y_div_diff : |Y' / q' - Y / q| ≤ eY / 0.99 + Yb * Dq / 0.9801 := by
    have h_expr : Y' / q' - Y / q = (Y' - Y) / q' + Y * (q - q') / (q' * q) := by
      field_simp [hpos_q.ne.symm, hpos_q'.ne.symm]
      ring
    rw [h_expr]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(Y' - Y) / q'| ≤ eY / 0.99 := by
      rw [abs_div]
      have h_q'_abs : |q'| = q' := abs_of_nonneg (by linarith)
      rw [h_q'_abs]
      have h_inv_q' : 1 / q' ≤ 1 / 0.99 := by
        refine ((one_div_le_one_div hpos_q' hpos_099).mpr ?_)
        linarith
      calc
        |Y' - Y| / q' = |Y' - Y| * (1 / q') := by ring
        _ ≤ eY * (1 / q') := mul_le_mul_of_nonneg_right hYY (by positivity)
        _ ≤ eY * (1 / 0.99) := mul_le_mul_of_nonneg_left h_inv_q' h_nonneg_eY
        _ = eY / 0.99 := by ring
    have h2 : |Y * (q - q') / (q' * q)| ≤ Yb * Dq / 0.9801 := by
      rw [abs_div, abs_mul]
      have h_qq : |q - q'| ≤ Dq := by
        have : |q - q'| = |q' - q| := by rw [← abs_neg, neg_sub]
        rw [this]
        exact hqq
      have h_denom : |q' * q| = q' * q := abs_of_nonneg (by nlinarith)
      rw [h_denom]
      have h_inv_qq : 1 / (q' * q) ≤ 1 / 0.9801 := by
        refine ((one_div_le_one_div (by nlinarith) hpos_09801).mpr ?_)
        nlinarith
      calc
        |Y| * |q - q'| / (q' * q) = (|Y| * |q - q'|) * (1 / (q' * q)) := by ring
        _ ≤ (Yb * Dq) * (1 / (q' * q)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hY h_qq (abs_nonneg _) h_nonneg_Yb)
            (by positivity)
        _ ≤ (Yb * Dq) * (1 / 0.9801) := mul_le_mul_of_nonneg_left h_inv_qq (mul_nonneg h_nonneg_Yb h_nonneg_Dq)
        _ = Yb * Dq / 0.9801 := by ring
    nlinarith
  have h_Y_div : |Y / q| ≤ Yb / 0.99 := by
    rw [abs_div]
    have h_q_abs : |q| = q := abs_of_nonneg (by linarith)
    rw [h_q_abs]
    have h_div1 : |Y| / q ≤ Yb / q :=
      (div_le_div_of_nonneg_right hY (by linarith))
    have h_div2 : Yb / q ≤ Yb / 0.99 := by
      have h_inv : 1 / q ≤ 1 / 0.99 :=
        ((one_div_le_one_div hpos_q hpos_099).mpr (by linarith))
      calc
        Yb / q = Yb * (1 / q) := by ring
        _ ≤ Yb * (1 / 0.99) := mul_le_mul_of_nonneg_left h_inv h_nonneg_Yb
        _ = Yb / 0.99 := by ring
    linarith
  have h_total : |η' * ν'| * |Y' / q' - Y / q| + |η' * ν' - η * m| * |Y / q| ≤
      103 / 100 * η * (eY + 3 * tq / 16 * Yb + Yb * Dq) := by
    have h_nonneg_abs3 : 0 ≤ |Y' / q' - Y / q| := abs_nonneg _
    have h_nonneg_abs4 : 0 ≤ |Y / q| := abs_nonneg _
    have h_nonneg_term1 : 0 ≤ η * m * (1 + 2.001 * tq / 16) :=
      mul_nonneg (mul_nonneg hη hm_nonneg) (by nlinarith)
    have h_nonneg_term2 : 0 ≤ 2.001 * tq / 16 * (η * m) :=
      mul_nonneg (by nlinarith) (mul_nonneg hη hm_nonneg)
    have h_term1 : |η' * ν'| * |Y' / q' - Y / q| ≤
        (η * m * (1 + 2.001 * tq / 16)) * (eY / 0.99 + Yb * Dq / 0.9801) :=
      mul_le_mul h_hnv_abs h_Y_div_diff h_nonneg_abs3 h_nonneg_term1
    have h_term2 : |η' * ν' - η * m| * |Y / q| ≤
        ((2.001 * tq / 16) * (η * m)) * (Yb / 0.99) :=
      mul_le_mul h_hnv_diff_abs h_Y_div h_nonneg_abs4 h_nonneg_term2
    have h_lhs_bound : |η' * ν'| * |Y' / q' - Y / q| + |η' * ν' - η * m| * |Y / q| ≤
        (η * m * (1 + 2.001 * tq / 16)) * (eY / 0.99 + Yb * Dq / 0.9801) +
        ((2.001 * tq / 16) * (η * m)) * (Yb / 0.99) := by
      nlinarith
    apply le_trans h_lhs_bound
    have h_factor_lhs : (η * m * (1 + 2.001 * tq / 16)) * (eY / 0.99 + Yb * Dq / 0.9801) +
        ((2.001 * tq / 16) * (η * m)) * (Yb / 0.99) =
        η * (m * (1 + 2.001 * tq / 16) * (eY / 0.99 + Yb * Dq / 0.9801) +
          (2.001 * tq / 16) * m * Yb / 0.99) := by ring
    have h_factor_rhs : 103 / 100 * η * (eY + 3 * tq / 16 * Yb + Yb * Dq) =
        η * (103 / 100 * (eY + 3 * tq / 16 * Yb + Yb * Dq)) := by ring
    rw [h_factor_lhs, h_factor_rhs]
    apply mul_le_mul_of_nonneg_left ?_ hη
    have h_eY : m * (1 + 2.001 * tq / 16) * (eY / 0.99) ≤ 103 / 100 * eY := by
      have h_coeff : m * (1 + 2.001 * tq / 16) / 0.99 ≤ 103 / 100 := by
        have h_bound : m * (1 + 2.001 * tq / 16) / 0.99 ≤
            (1000/999 : ℝ) * (1 + 2.001 * (1/1000) / 16) / 0.99 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num)
          apply mul_le_mul hm_le ?_ (by positivity) (by norm_num)
          gcongr
        have h_num : (1000/999 : ℝ) * (1 + 2.001 * (1/1000) / 16) / 0.99 ≤ 103/100 := by
          norm_num
        linarith
      calc
        m * (1 + 2.001 * tq / 16) * (eY / 0.99) = (m * (1 + 2.001 * tq / 16) / 0.99) * eY := by ring
        _ ≤ (103 / 100) * eY := mul_le_mul_of_nonneg_right h_coeff h_nonneg_eY
        _ = 103 / 100 * eY := by ring
    have h_YbDq : m * (1 + 2.001 * tq / 16) * (Yb * Dq / 0.9801) ≤ 103 / 100 * (Yb * Dq) := by
      have h_coeff : m * (1 + 2.001 * tq / 16) / 0.9801 ≤ 103 / 100 := by
        have h_bound : m * (1 + 2.001 * tq / 16) / 0.9801 ≤
            (1000/999 : ℝ) * (1 + 2.001 * (1/1000) / 16) / 0.9801 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num)
          apply mul_le_mul hm_le ?_ (by positivity) (by norm_num)
          gcongr
        have h_num : (1000/999 : ℝ) * (1 + 2.001 * (1/1000) / 16) / 0.9801 ≤ 103/100 := by
          norm_num
        linarith
      calc
        m * (1 + 2.001 * tq / 16) * (Yb * Dq / 0.9801) = (m * (1 + 2.001 * tq / 16) / 0.9801) * (Yb * Dq) := by ring
        _ ≤ (103 / 100) * (Yb * Dq) := mul_le_mul_of_nonneg_right h_coeff (mul_nonneg h_nonneg_Yb h_nonneg_Dq)
        _ = 103 / 100 * (Yb * Dq) := by ring
    have h_tqYb : (2.001 * tq / 16) * m * Yb / 0.99 ≤ 103 / 100 * (3 * tq / 16 * Yb) := by
      have h_coeff : 2.001 * m / 0.99 ≤ 103 / 100 * 3 := by
        have h_bound : 2.001 * m / 0.99 ≤ 2.001 * (1000/999) / 0.99 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num)
          apply mul_le_mul_of_nonneg_left hm_le (by norm_num)
        have h_num : 2.001 * (1000/999 : ℝ) / 0.99 ≤ 103/100 * 3 := by
          norm_num
        linarith
      have h_nonneg_tqYb : 0 ≤ tq / 16 * Yb := mul_nonneg (div_nonneg htq0 (by norm_num)) h_nonneg_Yb
      calc
        (2.001 * tq / 16) * m * Yb / 0.99 = (2.001 * m / 0.99) * (tq / 16 * Yb) := by ring
        _ ≤ (103 / 100 * 3) * (tq / 16 * Yb) := mul_le_mul_of_nonneg_right h_coeff h_nonneg_tqYb
        _ = 103 / 100 * (3 * tq / 16 * Yb) := by ring
    have h_expand : m * (1 + 2.001 * tq / 16) * (eY / 0.99 + Yb * Dq / 0.9801) +
        (2.001 * tq / 16) * m * Yb / 0.99 =
        (m * (1 + 2.001 * tq / 16) * (eY / 0.99)) +
        (m * (1 + 2.001 * tq / 16) * (Yb * Dq / 0.9801)) +
        ((2.001 * tq / 16) * m * Yb / 0.99) := by ring
    rw [h_expand]
    linarith
  calc
    |η' * ν' * (Y' / q' - Y / q) + (η' * ν' - η * m) * (Y / q)| ≤
        |η' * ν'| * |Y' / q' - Y / q| + |η' * ν' - η * m| * |Y / q| := h_tri
    _ ≤ 103 / 100 * η * (eY + 3 * tq / 16 * Yb + Yb * Dq) := h_total

theorem dw_err {d : ℕ} (μ w w' : Fin d → ℝ) (a a' Da Dw W1 A1 : ℝ)
    (ha : |a' - a| ≤ Da) (ha' : |a'| ≤ A1) (hw : oNorm w ≤ W1) (hww : oNorm (w' - w) ≤ Dw) :
    oNorm ((μ - a' • w') - (μ - a • w)) ≤ Da * W1 + A1 * Dw := by
  have h_eq : (μ - a' • w') - (μ - a • w) = -((a' - a) • w + a' • (w' - w)) := by
    calc
      (μ - a' • w') - (μ - a • w) = a • w - a' • w' := by
        abel
      _ = -((a' - a) • w + a' • (w' - w)) := by
        simp [smul_sub, sub_smul]
  rw [h_eq]
  have oNorm_neg (v : Fin d → ℝ) : oNorm (-v) = oNorm v := by
    simp [oNorm_eq_norm, norm_neg]
  rw [oNorm_neg]
  calc
    oNorm ((a' - a) • w + a' • (w' - w)) ≤ oNorm ((a' - a) • w) + oNorm (a' • (w' - w)) := by
      rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
      exact norm_add_le _ _
    _ = |a' - a| * oNorm w + |a'| * oNorm (w' - w) := by
      simp [oNorm_eq_norm, norm_smul]
    _ ≤ Da * W1 + A1 * Dw := by
      have h_nonneg_Da : 0 ≤ Da := by
        have h := abs_nonneg (a' - a)
        linarith
      have h_nonneg_A1 : 0 ≤ A1 := by
        have h := abs_nonneg a'
        linarith
      have h_nonneg_oNorm_w : 0 ≤ oNorm w := oNorm_nonneg _
      have h_nonneg_oNorm_w' : 0 ≤ oNorm (w' - w) := oNorm_nonneg _
      have h1 : |a' - a| * oNorm w ≤ Da * W1 := by
        exact mul_le_mul ha hw h_nonneg_oNorm_w h_nonneg_Da
      have h2 : |a'| * oNorm (w' - w) ≤ A1 * Dw := by
        exact mul_le_mul ha' hww h_nonneg_oNorm_w' h_nonneg_A1
      exact add_le_add h1 h2

theorem ellF_err {d : ℕ} (P P' : Matrix (Fin d) (Fin d) ℝ) (w w' y : Fin d → ℝ)
    (DP Dw L R W0 : ℝ) (hP : opN (P' - P) ≤ DP) (hw : oNorm (w - w') ≤ Dw) (hL : opN P ≤ L) (hy : oNorm y ≤ R)
    (hw0 : oNorm w ≤ W0) :
    |ellF P' w' y - ellF P w y| ≤
      (R + W0 + Dw) ^ 2 / 2 * DP + L * Dw * (2 * R + 2 * W0 + Dw) / 2 := by
  have h_ellF := ellF_diff P P' w w' y
  have h_tri_sub (a b : Fin d → ℝ) : oNorm (a - b) ≤ oNorm a + oNorm b := by
    rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
    calc
      ‖WithLp.toLp 2 (a - b)‖ = ‖WithLp.toLp 2 a - WithLp.toLp 2 b‖ := by
        rw [WithLp.toLp_sub]
      _ ≤ ‖WithLp.toLp 2 a‖ + ‖WithLp.toLp 2 b‖ := norm_sub_le _ _
  have h_tri_add (a b : Fin d → ℝ) : oNorm (a + b) ≤ oNorm a + oNorm b := by
    rw [oNorm_eq_norm, oNorm_eq_norm, oNorm_eq_norm]
    calc
      ‖WithLp.toLp 2 (a + b)‖ = ‖WithLp.toLp 2 a + WithLp.toLp 2 b‖ := by
        rw [WithLp.toLp_add]
      _ ≤ ‖WithLp.toLp 2 a‖ + ‖WithLp.toLp 2 b‖ := norm_add_le _ _
  have h_yw : oNorm (y - w) ≤ R + W0 := by
    calc
      oNorm (y - w) ≤ oNorm y + oNorm w := h_tri_sub y w
      _ ≤ R + W0 := by gcongr
  have h_yw' : oNorm (y - w') ≤ R + W0 + Dw := by
    calc
      oNorm (y - w') = oNorm ((y - w) + (w - w')) := by
        rw [sub_add_sub_cancel]
      _ ≤ oNorm (y - w) + oNorm (w - w') := h_tri_add (y - w) (w - w')
      _ ≤ (R + W0) + Dw := by gcongr
      _ = R + W0 + Dw := by ring
  have hDw_nonneg : 0 ≤ Dw := by
    have := oNorm_nonneg (w - w')
    linarith
  have hDP_nonneg : 0 ≤ DP := by
    have := opN_nonneg (P' - P)
    linarith
  have hL_nonneg : 0 ≤ L := by
    have := opN_nonneg P
    linarith
  have hR_nonneg : 0 ≤ R := by
    have := oNorm_nonneg y
    linarith
  have hW0_nonneg : 0 ≤ W0 := by
    have := oNorm_nonneg w
    linarith
  have hyw_nonneg : 0 ≤ oNorm (y - w) := oNorm_nonneg _
  have hyw'_nonneg : 0 ≤ oNorm (y - w') := oNorm_nonneg _
  have hww'_nonneg : 0 ≤ oNorm (w - w') := oNorm_nonneg _
  have h1 : oNorm (y - w') ^ 2 / 2 * opN (P' - P) ≤ (R + W0 + Dw) ^ 2 / 2 * DP := by
    have hsq : oNorm (y - w') ^ 2 ≤ (R + W0 + Dw) ^ 2 :=
      pow_le_pow_left₀ hyw'_nonneg h_yw' 2
    nlinarith
  have h2 : oNorm (w - w') * opN P * (oNorm (y - w') + oNorm (y - w)) / 2 ≤
      L * Dw * (2 * R + 2 * W0 + Dw) / 2 := by
    have hsum : oNorm (y - w') + oNorm (y - w) ≤ 2 * R + 2 * W0 + Dw := by
      have htemp : oNorm (y - w') + oNorm (y - w) ≤ (R + W0 + Dw) + (R + W0) := by
        gcongr
      have htemp2 : (R + W0 + Dw) + (R + W0) = 2 * R + 2 * W0 + Dw := by ring
      linarith
    have h_mul : oNorm (w - w') * opN P * (oNorm (y - w') + oNorm (y - w)) ≤
        Dw * L * (2 * R + 2 * W0 + Dw) := by
      have hprod1 : oNorm (w - w') * opN P ≤ Dw * L :=
        mul_le_mul hw hL (opN_nonneg _) hDw_nonneg
      have hsum_nonneg : 0 ≤ oNorm (y - w') + oNorm (y - w) := by positivity
      have hDwL_nonneg : 0 ≤ Dw * L := by positivity
      exact mul_le_mul hprod1 hsum hsum_nonneg hDwL_nonneg
    nlinarith
  have hsum_le := add_le_add h1 h2
  linarith

theorem Le_le_Ne (Ne Le : ℝ) (hNe : 0 < Ne) (hLe : Le = 36 * Real.log Ne)
    (h : 17467 ≤ Le) : Le ≤ Ne ^ 2 / 100 := by
  rw [hLe]
  have hlog : 9 ≤ Real.log Ne := by
    have hineq : (17467 : ℝ) / 36 ≤ Real.log Ne := by
      linarith
    have h9lt : (9 : ℝ) < (17467 : ℝ) / 36 := by norm_num
    linarith
  have hNe_ge_exp9 : Real.exp 9 ≤ Ne := by
    calc
      Real.exp 9 ≤ Real.exp (Real.log Ne) := Real.exp_le_exp_of_le hlog
      _ = Ne := Real.exp_log hNe
  have h_exp9_ge_3600 : 3600 ≤ Real.exp 9 := by
    have h1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
    have h_exp9 : Real.exp 9 = (Real.exp 1) ^ 9 := by
      calc
        Real.exp 9 = Real.exp ((9 : ℕ) • (1 : ℝ)) := by norm_num
        _ = (Real.exp 1) ^ (9 : ℕ) := Real.exp_nsmul (1 : ℝ) 9
        _ = (Real.exp 1) ^ 9 := by norm_num
    rw [h_exp9]
    have h_pow : (2.7182818283 : ℝ) ^ 9 ≤ (Real.exp 1) ^ 9 := by
      gcongr
    have h_3600 : (3600 : ℝ) ≤ (2.7182818283 : ℝ) ^ 9 := by norm_num
    linarith
  have hNe_ge_3600 : 3600 ≤ Ne := by linarith
  have hlog_le_Ne : Real.log Ne ≤ Ne := by
    have hlogle := Real.log_le_sub_one_of_pos hNe
    linarith
  have h1 : 36 * Real.log Ne ≤ 36 * Ne := by nlinarith
  have h2 : 36 * Ne ≤ Ne ^ 2 / 100 := by
    nlinarith
  linarith

theorem tp_small_gen (tp n d Ne Le η Yb : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hNe : 0 < Ne)
    (hLe1 : 1 ≤ Le) (hLeNe : Le ≤ Ne ^ 2 / 100) (htp : n * (d * Ne) * tp ≤ 1) (htp0 : 0 ≤ tp)
    (hη : η = Real.sqrt d / (Le * Real.sqrt n)) (hY : 16 * Real.sqrt Le ≤ Yb) : tp ≤ 1 / 100 * η * Yb := by
  have hLe_pos : 0 < Le := by linarith
  have hLe_sqrt_pos : 0 < Real.sqrt Le := Real.sqrt_pos.mpr hLe_pos
  have hn_pos : 0 < n := by linarith
  have hn_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hd_pos : 0 < d := by linarith
  have hd_sqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd_pos
  have hη_nonneg : 0 ≤ η := by
    rw [hη]
    refine div_nonneg (Real.sqrt_nonneg _) ?_
    positivity
  have hYb_nonneg : 0 ≤ Yb := by
    have : 0 ≤ 16 * Real.sqrt Le := by positivity
    linarith
  -- √Le ≤ Ne/10 from hLeNe
  have h_sqrtLe_le : Real.sqrt Le ≤ Ne / 10 := by
    have hsq : Le ≤ (Ne / 10) ^ 2 := by
      nlinarith
    have h_nonneg : 0 ≤ Ne / 10 := by linarith
    calc
      Real.sqrt Le ≤ Real.sqrt ((Ne / 10) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Ne / 10 := Real.sqrt_sq h_nonneg
  -- tp ≤ 1/(n*d*Ne) from htp
  have h_tp_bound : tp ≤ 1 / (n * d * Ne) := by
    have h : n * d * Ne * tp ≤ 1 := by
      calc
        n * d * Ne * tp = n * (d * Ne) * tp := by ring
        _ ≤ 1 := htp
    have hpos : 0 < n * d * Ne := by positivity
    apply (le_div_iff₀ hpos).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  -- √n ≥ 1 and √d ≥ 1
  have h_sqrt_n_ge_one : 1 ≤ Real.sqrt n := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn
  have h_sqrt_d_ge_one : 1 ≤ Real.sqrt d := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt hd
  -- Key inequality: tp * √Le * √n ≤ (16/100) * √d
  have h_key : tp * Real.sqrt Le * Real.sqrt n ≤ (16 / 100) * Real.sqrt d := by
    calc
      tp * Real.sqrt Le * Real.sqrt n ≤ (1 / (n * d * Ne)) * Real.sqrt Le * Real.sqrt n := by
        have h_nonneg : 0 ≤ Real.sqrt Le * Real.sqrt n := by positivity
        nlinarith
      _ ≤ (1 / (n * d * Ne)) * (Ne / 10) * Real.sqrt n := by
        have h_nonneg : 0 ≤ 1 / (n * d * Ne) * Real.sqrt n := by positivity
        nlinarith
      _ = Real.sqrt n / (10 * n * d) := by
        field_simp [hNe.ne']
      _ = 1 / (10 * Real.sqrt n * d) := by
        field_simp [hn_sqrt_pos.ne', hn_pos.ne']
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ n)]
      _ ≤ 1 / 10 := by
        refine (one_div_le_one_div ?_ ?_).mpr ?_
        · positivity
        · positivity
        · have : 1 ≤ Real.sqrt n * d := by
            nlinarith
          nlinarith
      _ ≤ (16 / 100) * Real.sqrt d := by
        have h : (1 : ℝ) / 10 ≤ 16 / 100 := by norm_num
        have h2 : 16 / 100 ≤ (16 / 100) * Real.sqrt d := by
          have hpos' : 0 ≤ 16 / 100 := by norm_num
          nlinarith
        linarith
  -- From h_key, divide by √Le * √n > 0 to get tp ≤ (16/100) * √d / (√Le * √n)
  have h_main : tp ≤ (16 / 100) * Real.sqrt d / (Real.sqrt Le * Real.sqrt n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa [mul_assoc] using h_key
  -- Now show (16/100) * √d / (√Le * √n) ≤ 1/100 * η * Yb
  have h_aux : (16 / 100) * Real.sqrt d / (Real.sqrt Le * Real.sqrt n) ≤ 1 / 100 * η * Yb := by
    calc
      (16 / 100) * Real.sqrt d / (Real.sqrt Le * Real.sqrt n) =
          1 / 100 * (Real.sqrt d / (Le * Real.sqrt n)) * (16 * Real.sqrt Le) := by
        field_simp [hLe_sqrt_pos.ne', hn_sqrt_pos.ne']
        rw [Real.sq_sqrt (by linarith : 0 ≤ Le)]
      _ = 1 / 100 * η * (16 * Real.sqrt Le) := by rw [hη]
      _ ≤ 1 / 100 * η * Yb := by
        have hpos_factor : 0 ≤ 1 / 100 * η := by positivity
        have : 0 ≤ Yb := hYb_nonneg
        nlinarith
  -- Combine
  linarith

theorem phi_convexOn {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (P *ᵥ v)) (b : Fin d → ℝ) (k : ℝ) (Ke : Set (Fin d → ℝ))
    (hKe : Convex ℝ Ke) : ConvexOn ℝ Ke (df2Phi P b k) := by
  have hPsymm : P.IsSymm := hP
  refine ⟨hKe, fun x hx y hy a b' ha hb' hab => ?_⟩
  unfold df2Phi
  -- Set up abbreviations for dot products to use ring
  set X := x ⬝ᵥ (P *ᵥ x) with hX
  set Y := y ⬝ᵥ (P *ᵥ y) with hY
  set Z := x ⬝ᵥ (P *ᵥ y) with hZ
  set Bx := b ⬝ᵥ x with hBx
  set By := b ⬝ᵥ y with hBy
  have h_symm : Z = y ⬝ᵥ (P *ᵥ x) := hPsymm.dotProduct_mulVec_comm
  -- Key identity: (x-y)ᵀP(x-y) = X + Y - 2*Z
  have h_diff_sq : (x - y) ⬝ᵥ (P *ᵥ (x - y)) = X + Y - 2 * Z := by
    calc
      (x - y) ⬝ᵥ (P *ᵥ (x - y)) = (x - y) ⬝ᵥ (P *ᵥ x - P *ᵥ y) := by
        simp [Matrix.mulVec_sub]
      _ = (x - y) ⬝ᵥ (P *ᵥ x) - (x - y) ⬝ᵥ (P *ᵥ y) := by rw [dotProduct_sub]
      _ = (x ⬝ᵥ (P *ᵥ x) - y ⬝ᵥ (P *ᵥ x)) - (x ⬝ᵥ (P *ᵥ y) - y ⬝ᵥ (P *ᵥ y)) := by
        simp [sub_dotProduct]
      _ = X + Y - 2 * Z := by
        simp [hX, hY, hZ, ← h_symm]
        ring
  have h_psd_val : 0 ≤ X + Y - 2 * Z := by
    rw [← h_diff_sq]
    exact hpsd (x - y)
  -- Expand (a•x + b'•y) ⬝ᵥ (P *ᵥ (a•x + b'•y)) in terms of X, Y, Z
  have h_expand : (a • x + b' • y) ⬝ᵥ (P *ᵥ (a • x + b' • y)) =
      a^2 * X + b'^2 * Y + (a * b') * (Z + Z) := by
    calc
      (a • x + b' • y) ⬝ᵥ (P *ᵥ (a • x + b' • y)) =
        (a • x + b' • y) ⬝ᵥ (a • (P *ᵥ x) + b' • (P *ᵥ y)) := by
        simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = (a • x + b' • y) ⬝ᵥ (a • (P *ᵥ x)) + (a • x + b' • y) ⬝ᵥ (b' • (P *ᵥ y)) := by
        rw [dotProduct_add]
      _ = ((a • x) ⬝ᵥ (a • (P *ᵥ x)) + (b' • y) ⬝ᵥ (a • (P *ᵥ x))) +
          ((a • x) ⬝ᵥ (b' • (P *ᵥ y)) + (b' • y) ⬝ᵥ (b' • (P *ᵥ y))) := by
        rw [add_dotProduct, add_dotProduct]
      _ = (a * a * (x ⬝ᵥ (P *ᵥ x)) + b' * a * (y ⬝ᵥ (P *ᵥ x))) +
          (a * b' * (x ⬝ᵥ (P *ᵥ y)) + b' * b' * (y ⬝ᵥ (P *ᵥ y))) := by
        simp [smul_dotProduct, dotProduct_smul, mul_assoc, mul_comm, mul_left_comm]
      _ = (a^2 * X + b' * a * (y ⬝ᵥ (P *ᵥ x))) + (a * b' * Z + b'^2 * Y) := by
        simp [hX, hY, hZ]
        rw [pow_two a, pow_two b']
      _ = (a^2 * X + b' * a * Z) + (a * b' * Z + b'^2 * Y) := by rw [h_symm]
      _ = a^2 * X + b'^2 * Y + (a * b') * (Z + Z) := by ring
  -- Linear term
  have h_linear : b ⬝ᵥ (a • x + b' • y) = a * Bx + b' * By := by
    simp [dotProduct_add, dotProduct_smul, hBx, hBy]
  -- Now compute the difference
  have h_diff_nonneg : 0 ≤ a • (1 / 2 * X - Bx + k) + b' • (1 / 2 * Y - By + k) -
      (1 / 2 * ((a • x + b' • y) ⬝ᵥ (P *ᵥ (a • x + b' • y))) - b ⬝ᵥ (a • x + b' • y) + k) := by
    rw [h_expand, h_linear]
    -- Now the goal is a polynomial in a, b', X, Y, Z, Bx, By, k
    simp [smul_eq_mul]
    -- The expression simplifies to (a*b'/2) * (X + Y - 2*Z)
    -- We can verify this by ring
    have ha_eq : a - a^2 = a * b' := by
      have hb' : b' = 1 - a := by linarith
      calc
        a - a^2 = a * (1 - a) := by ring
        _ = a * b' := by rw [hb']
    have hb_eq : b' - b'^2 = a * b' := by
      have ha' : a = 1 - b' := by linarith
      calc
        b' - b'^2 = b' * (1 - b') := by ring
        _ = b' * a := by rw [ha']
        _ = a * b' := by ring
    have h_poly : a * (1 / 2 * X - Bx + k) + b' * (1 / 2 * Y - By + k) -
        (1 / 2 * (a^2 * X + b'^2 * Y + (a * b') * (Z + Z)) - (a * Bx + b' * By) + k) =
        (a * b' / 2) * (X + Y - 2 * Z) := by
      field_simp
      calc
        a * (X - 2 * Bx + 2 * k) + b' * (Y - 2 * By + 2 * k) -
            (a ^ 2 * X + b' ^ 2 * Y + a * b' * Z * (1 + 1) - 2 * (a * Bx + b' * By) + 2 * k)
            = (a - a^2) * X + (b' - b'^2) * Y - 2 * a * b' * Z + 2 * k * (a + b' - 1) := by ring
        _ = (a * b') * X + (a * b') * Y - 2 * a * b' * Z + 2 * k * (a + b' - 1) := by rw [ha_eq, hb_eq]
        _ = (a * b') * (X + Y - 2 * Z) + 2 * k * (a + b' - 1) := by ring
        _ = (a * b') * (X + Y - 2 * Z) := by rw [hab]; ring
        _ = a * b' * (X + Y - 2 * Z) := by ring
    have h_nonneg_ab : 0 ≤ a * b' := mul_nonneg ha hb'
    have h_goal : 0 ≤ (a * b' / 2) * (X + Y - 2 * Z) := by
      have h_nonneg : 0 ≤ X + Y - 2 * Z := h_psd_val
      have h_nonneg_ab' : 0 ≤ a * b' := mul_nonneg ha hb'
      nlinarith
    linarith [h_poly, h_goal]
  -- Unfold the abbreviations and use the above
  simpa [hX, hY, hZ, hBx, hBy] using h_diff_nonneg

theorem phi_scale {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : Pᵀ = P)
    (hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (P *ᵥ v)) (b : Fin d → ℝ) (k R G κ : ℝ) (y : Fin d → ℝ)
    (hgrad : ∀ z : Fin d → ℝ, oNorm z ≤ R → oNorm (P *ᵥ z - b) ≤ G) (hy : oNorm y ≤ R) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) : df2Phi P b k (κ • y) ≤ df2Phi P b k y + G * R * (1 - κ) := by
  set z := κ • y with hz
  set e := y - z with he
  have hz_onorm : oNorm z ≤ R := by
    dsimp [z, oNorm]
    have h_sq : (κ • y) ⬝ᵥ (κ • y) = κ ^ 2 * (y ⬝ᵥ y) := by
      simp [dotProduct_smul, smul_dotProduct, mul_comm]
      ring
    rw [h_sq]
    have h_nonneg_sq : 0 ≤ κ ^ 2 := by nlinarith
    rw [Real.sqrt_mul h_nonneg_sq, Real.sqrt_sq hκ0]
    have h_sqrt_y : Real.sqrt (y ⬝ᵥ y) ≤ R := by
      rw [← oNorm]
      exact hy
    calc
      κ * Real.sqrt (y ⬝ᵥ y) ≤ 1 * Real.sqrt (y ⬝ᵥ y) := by
        gcongr
      _ = Real.sqrt (y ⬝ᵥ y) := by simp
      _ ≤ R := h_sqrt_y
  have hgrad_bound : oNorm (P *ᵥ z - b) ≤ G := hgrad z hz_onorm
  have he_onorm : oNorm e ≤ (1 - κ) * R := by
    have he_eq : e = (1 - κ) • y := by
      dsimp [z, e]
      rw [sub_smul, one_smul]
    rw [he_eq, oNorm]
    have h_sq : ((1 - κ) • y) ⬝ᵥ ((1 - κ) • y) = (1 - κ) ^ 2 * (y ⬝ᵥ y) := by
      simp [dotProduct_smul, smul_dotProduct, mul_comm]
      ring
    rw [h_sq]
    have h_nonneg_sq : 0 ≤ (1 - κ) ^ 2 := by nlinarith
    rw [Real.sqrt_mul h_nonneg_sq, Real.sqrt_sq (sub_nonneg.mpr hκ1)]
    have h_sqrt_y : Real.sqrt (y ⬝ᵥ y) ≤ R := by
      rw [← oNorm]
      exact hy
    calc
      (1 - κ) * Real.sqrt (y ⬝ᵥ y) ≤ (1 - κ) * R := by
        gcongr
      _ = (1 - κ) * R := rfl
  have h_expand : df2Phi P b k y = df2Phi P b k z + (P *ᵥ z - b) ⬝ᵥ e + (1/2 : ℝ) * (e ⬝ᵥ (P *ᵥ e)) := by
    dsimp [df2Phi, z, e]
    have hY : (κ • y) ⬝ᵥ (P *ᵥ (κ • y)) = κ ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by
      calc
        (κ • y) ⬝ᵥ (P *ᵥ (κ • y))
            = (κ • y) ⬝ᵥ (κ • (P *ᵥ y)) := by simp [Matrix.mulVec_smul]
        _ = κ * ((κ • y) ⬝ᵥ (P *ᵥ y)) := by simp [smul_dotProduct]
        _ = κ * (κ * (y ⬝ᵥ (P *ᵥ y))) := by simp
        _ = κ ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by ring
    have hB1 : b ⬝ᵥ (κ • y) = κ * (b ⬝ᵥ y) := by simp [dotProduct_smul]
    have hYcross : (κ • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y)) = κ * (1 - κ) * (y ⬝ᵥ (P *ᵥ y)) := by
      calc
        (κ • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y))
            = (κ • y) ⬝ᵥ ((1 - κ) • (P *ᵥ y)) := by simp [Matrix.mulVec_smul]
        _ = κ * (((1 - κ) • y) ⬝ᵥ (P *ᵥ y)) := by
          -- (κ • y) ⬝ᵥ ((1-κ) • w) = κ * ((1-κ) • y ⬝ᵥ w) = κ * (1-κ) * (y ⬝ᵥ w)
          -- using smul_dotProduct and dotProduct_smul
          simp [smul_dotProduct, mul_comm, mul_assoc]
        _ = κ * ((1 - κ) * (y ⬝ᵥ (P *ᵥ y))) := by simp
        _ = κ * (1 - κ) * (y ⬝ᵥ (P *ᵥ y)) := by ring
    have hB2 : b ⬝ᵥ ((1 - κ) • y) = (1 - κ) * (b ⬝ᵥ y) := by simp [dotProduct_smul]
    have hY2 : ((1 - κ) • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y)) = (1 - κ) ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by
      calc
        ((1 - κ) • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y))
            = ((1 - κ) • y) ⬝ᵥ ((1 - κ) • (P *ᵥ y)) := by
          simp [Matrix.mulVec_smul]
        _ = (1 - κ) * (((1 - κ) • y) ⬝ᵥ (P *ᵥ y)) := by
          simp [smul_dotProduct]
        _ = (1 - κ) * ((1 - κ) * (y ⬝ᵥ (P *ᵥ y))) := by
          simp
        _ = (1 - κ) ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by ring
    calc
      1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k
          = (1 / 2 * (κ ^ 2 * (y ⬝ᵥ (P *ᵥ y))) - κ * (b ⬝ᵥ y) + k) +
            (κ * (1 - κ) * (y ⬝ᵥ (P *ᵥ y)) - (1 - κ) * (b ⬝ᵥ y)) +
            (1/2 : ℝ) * ((1 - κ) ^ 2 * (y ⬝ᵥ (P *ᵥ y))) := by
        ring
      _ = (1 / 2 * ((κ • y) ⬝ᵥ (P *ᵥ (κ • y))) - b ⬝ᵥ (κ • y) + k) +
          ((κ • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y)) - b ⬝ᵥ ((1 - κ) • y)) +
          (1/2 : ℝ) * (((1 - κ) • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y))) := by
        rw [hY, hB1, hYcross, hB2, hY2]
      _ = df2Phi P b k (κ • y) + ((P *ᵥ (κ • y)) - b) ⬝ᵥ (y - κ • y) +
          (1/2 : ℝ) * ((y - κ • y) ⬝ᵥ (P *ᵥ (y - κ • y))) := by
        dsimp [df2Phi]
        have h_sub : y - κ • y = (1 - κ) • y := by
          rw [sub_smul, one_smul]
        have h_mulVec : P *ᵥ (κ • y) = κ • (P *ᵥ y) := by
          simp [Matrix.mulVec_smul]
        have h_symm_dot : (P *ᵥ y) ⬝ᵥ y = y ⬝ᵥ (P *ᵥ y) := by
          calc
            (P *ᵥ y) ⬝ᵥ y = Matrix.vecMul y Pᵀ ⬝ᵥ y := by
              simp [Matrix.vecMul_transpose]
            _ = y ⬝ᵥ (Pᵀ *ᵥ y) := by rw [Matrix.dotProduct_mulVec]
            _ = y ⬝ᵥ (P *ᵥ y) := by rw [hP]
        have h_dot_cross : (κ • y) ⬝ᵥ (P *ᵥ ((1 - κ) • y)) - b ⬝ᵥ ((1 - κ) • y) =
            ((P *ᵥ (κ • y)) - b) ⬝ᵥ (y - κ • y) := by
          rw [h_mulVec, h_sub]
          simp [dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul, smul_eq_mul]
          rw [h_symm_dot]
          ring
        rw [h_dot_cross]
        congr 1
        rw [h_sub]
  have h_nonneg_half : 0 ≤ (1/2 : ℝ) * (e ⬝ᵥ (P *ᵥ e)) := by
    have h_nonneg : 0 ≤ e ⬝ᵥ (P *ᵥ e) := hpsd e
    have : 0 ≤ (1/2 : ℝ) := by norm_num
    exact mul_nonneg this h_nonneg
  have h_bound : (P *ᵥ z - b) ⬝ᵥ e ≥ -G * R * (1 - κ) := by
    have h_abs : |(P *ᵥ z - b) ⬝ᵥ e| ≤ oNorm (P *ᵥ z - b) * oNorm e := abs_dot_le _ _
    have h_lower : -(oNorm (P *ᵥ z - b) * oNorm e) ≤ (P *ᵥ z - b) ⬝ᵥ e := by
      have := abs_le.mp h_abs
      linarith
    have h_nonneg_onorm_Pzb : 0 ≤ oNorm (P *ᵥ z - b) := oNorm_nonneg _
    have h_nonneg_onorm_e : 0 ≤ oNorm e := oNorm_nonneg _
    have h_nonneg_R : 0 ≤ R := le_trans (oNorm_nonneg y) hy
    have h_nonneg_G : 0 ≤ G := by
      have h0 : oNorm (P *ᵥ (0 : Fin d → ℝ) - b) ≤ G := hgrad 0 (by
        dsimp [oNorm]
        simp [h_nonneg_R])
      have h_onorm_b : 0 ≤ oNorm (-b) := oNorm_nonneg _
      linarith
    have h_mul : oNorm (P *ᵥ z - b) * oNorm e ≤ G * ((1 - κ) * R) := by
      have h_nonneg_rhs : 0 ≤ (1 - κ) * R := by
        have : 0 ≤ 1 - κ := sub_nonneg.mpr hκ1
        nlinarith [hy, this]
      exact mul_le_mul hgrad_bound he_onorm h_nonneg_onorm_e h_nonneg_G
    calc
      (P *ᵥ z - b) ⬝ᵥ e ≥ -(oNorm (P *ᵥ z - b) * oNorm e) := h_lower
      _ ≥ -(G * ((1 - κ) * R)) := by linarith
      _ = -G * R * (1 - κ) := by ring
  calc
    df2Phi P b k (κ • y) = df2Phi P b k z := rfl
    _ = df2Phi P b k y - ((P *ᵥ z - b) ⬝ᵥ e + (1/2 : ℝ) * (e ⬝ᵥ (P *ᵥ e))) := by linarith
    _ ≤ df2Phi P b k y + G * R * (1 - κ) := by
      have h_sum : (P *ᵥ z - b) ⬝ᵥ e + (1/2 : ℝ) * (e ⬝ᵥ (P *ᵥ e)) ≥ -G * R * (1 - κ) := by
        nlinarith
      nlinarith

theorem gap_disp (R D E1 κ eps eps' we de GR : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hde : 0 < de)
    (he0 : 0 < eps) (he : eps ≤ 1 / 2) (hee : eps ≤ eps') (hee' : eps' ≤ eps + we) (hκ : κ = (1 - eps') / (1 - eps))
    (hE1 : E1 = GR * R * (1 - κ)) (hGR : GR = R / de ^ 2) :
    2 * R * ((D + E1) / 2) + (1 - κ) * R ≤ R * D + 2 * R ^ 3 * we / de ^ 2 + 2 * R * we := by
  have h_one_minus_eps_pos : 0 < 1 - eps := by linarith
  have h_eps_sub_nonneg : 0 ≤ eps' - eps := by linarith
  have h_eps_sub : eps' - eps ≤ we := by linarith
  have h0 : 0 ≤ 1 - κ := by
    rw [hκ]
    have h_expr : 1 - (1 - eps') / (1 - eps) = (eps' - eps) / (1 - eps) := by
      field_simp [h_one_minus_eps_pos.ne']
      ring
    rw [h_expr]
    exact div_nonneg h_eps_sub_nonneg (by linarith)
  have h1 : 1 - κ ≤ 2 * we := by
    rw [hκ]
    have h_expr : 1 - (1 - eps') / (1 - eps) = (eps' - eps) / (1 - eps) := by
      field_simp [h_one_minus_eps_pos.ne']
      ring
    rw [h_expr]
    have h_denom : 1 / (1 - eps) ≤ 2 := by
      field_simp [h_one_minus_eps_pos.ne']
      linarith
    calc
      (eps' - eps) / (1 - eps) ≤ we / (1 - eps) :=
        div_le_div_of_nonneg_right h_eps_sub (by linarith)
      _ = we * (1 / (1 - eps)) := by ring
      _ ≤ we * 2 := mul_le_mul_of_nonneg_left h_denom (by linarith)
      _ = 2 * we := by ring
  have h_coeff_nonneg : 0 ≤ R ^ 3 / de ^ 2 :=
    div_nonneg (pow_nonneg hR 3) (by positivity)
  calc
    2 * R * ((D + E1) / 2) + (1 - κ) * R = R * (D + E1) + (1 - κ) * R := by ring
    _ = R * D + R * E1 + (1 - κ) * R := by ring
    _ = R * D + R * (GR * R * (1 - κ)) + (1 - κ) * R := by rw [hE1]
    _ = R * D + R * ((R / de ^ 2) * R * (1 - κ)) + (1 - κ) * R := by rw [hGR]
    _ = R * D + (R ^ 3 * (1 - κ)) / de ^ 2 + (1 - κ) * R := by ring
    _ = R * D + ((R ^ 3 / de ^ 2) * (1 - κ)) + R * (1 - κ) := by ring
    _ ≤ R * D + ((R ^ 3 / de ^ 2) * (2 * we)) + R * (2 * we) := by
      nlinarith
    _ = R * D + (R ^ 3 * (2 * we)) / de ^ 2 + R * (2 * we) := by ring
    _ = R * D + 2 * R ^ 3 * we / de ^ 2 + 2 * R * we := by ring

theorem w0_eq (η d n Le de Ne : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hLe : 0 < Le)
    (hNe : 0 < Ne) (hde : de = 1 / Ne) (hη : η = Real.sqrt d / (Le * Real.sqrt n)) :
    η * Real.sqrt (16 * d * n * Le / de) = 4 * d * Real.sqrt (Ne / Le) := by
  rw [hη, hde]
  have hd0 : 0 ≤ d := by linarith
  have hLe0 : 0 ≤ Le := by linarith
  have hNe0 : 0 ≤ Ne := by linarith
  have h_sqrt_n_pos : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  -- simplify the division inside sqrt: 16*d*n*Le / (1/Ne) = 16*d*n*Le*Ne
  have h_div : (16 * d * n * Le) / (1 / Ne) = 16 * d * n * Le * Ne := by field_simp [hNe.ne.symm]
  rw [h_div]
  -- expand sqrt(16*d*n*Le*Ne) = 4*sqrt(d)*sqrt(n)*sqrt(Le)*sqrt(Ne)
  have h_sqrt_prod : Real.sqrt (16 * d * n * Le * Ne) = 4 * Real.sqrt d * Real.sqrt n * Real.sqrt Le * Real.sqrt Ne := by
    calc
      Real.sqrt (16 * d * n * Le * Ne) = Real.sqrt ((16 * d * n) * (Le * Ne)) := by ring
      _ = Real.sqrt (16 * d * n) * Real.sqrt (Le * Ne) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * d * n)]
      _ = Real.sqrt (16 * (d * n)) * Real.sqrt (Le * Ne) := by ring
      _ = (Real.sqrt (16 : ℝ) * Real.sqrt (d * n)) * Real.sqrt (Le * Ne) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (16 : ℝ))]
      _ = (4 * (Real.sqrt d * Real.sqrt n)) * (Real.sqrt Le * Real.sqrt Ne) := by
        rw [Real.sqrt_mul hd0, Real.sqrt_mul hLe0]; norm_num
      _ = 4 * Real.sqrt d * Real.sqrt n * Real.sqrt Le * Real.sqrt Ne := by ring
  rw [h_sqrt_prod]
  -- Now: (Real.sqrt d / (Le * Real.sqrt n)) * (4 * Real.sqrt d * Real.sqrt n * Real.sqrt Le * Real.sqrt Ne) = 4 * d * Real.sqrt (Ne / Le)
  field_simp [h_sqrt_n_pos]
  -- Goal: Real.sqrt d ^ 2 * Real.sqrt Le * Real.sqrt Ne = Le * d * Real.sqrt (Ne / Le)
  have h_sq_sqrt_d : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd0
  have h_sq_sqrt_Le : Real.sqrt Le ^ 2 = Le := Real.sq_sqrt hLe0
  rw [h_sq_sqrt_d, Real.sqrt_div hNe0 Le]
  -- Goal: d * Real.sqrt Le * Real.sqrt Ne = Le * d * (Real.sqrt Ne / Real.sqrt Le)
  field_simp [(Real.sqrt_pos.mpr hLe).ne']
  exact h_sq_sqrt_Le

theorem eM_ge (n R T d de : ℝ) (hn : 1 ≤ n) (hR : 1 ≤ R) (hd : 1 ≤ d) (hde0 : 0 < de)
    (hde1 : de ≤ 1) (hT0 : 0 ≤ T) (hT : T ≤ d / de) :
    de / (64 * n ^ 2 * R ^ 2 * d) ≤ 1 / (16 * n ^ 2 * max 1 (4 * R ^ 2 * T)) := by
  have hnpos : 0 < n := by linarith
  have hRpos : 0 < R := by linarith
  have hdpos : 0 < d := by linarith
  have hR2pos : 0 < R ^ 2 := by nlinarith
  have hden1 : 0 < 64 * n ^ 2 * R ^ 2 * d := by positivity
  have hden2 : 0 < 16 * n ^ 2 * max 1 (4 * R ^ 2 * T) := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  rcases le_total 1 (4 * R ^ 2 * T) with (h | h)
  · rw [max_eq_right h]
    ring_nf
    have hTde : de * T ≤ d := by
      have htemp := (le_div_iff₀ hde0).mp hT
      nlinarith
    nlinarith
  · rw [max_eq_left h]
    ring_nf
    have hn2pos : 0 ≤ n ^ 2 := by nlinarith
    have hR2ge1 : 1 ≤ R ^ 2 := by
      nlinarith
    have hgoal : de ≤ 4 * R ^ 2 * d := by
      nlinarith
    nlinarith

theorem s5_abs (η Y Yb lam q a a' Ds tp eY Dq : ℝ) (hη : 0 ≤ η) (hY : |Y| ≤ Yb)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 1000) (hq : 99 / 100 ≤ q) (ha : a = η * Y / ((1 - lam) * q))
    (haa : |a' - a| ≤ Ds) (hDs : Ds = tp / 2 + 103 / 100 * η * (eY + 3 * tp / 16 * Yb + Yb * Dq))
    (htp0 : 0 ≤ tp) (htp : tp ≤ 1 / 100 * η * Yb) (heY : eY ≤ Yb / 1000) (hDq : Dq ≤ 1 / 1000)
    (htp1 : tp ≤ 1 / 1000) :
    |a'| ≤ 103 / 100 * η * Yb := by
  have hYb_nonneg : 0 ≤ Yb := by
    have h := abs_nonneg Y
    linarith
  have h_one_minus_lam_pos : 0 < 1 - lam := by linarith
  have hq_pos : 0 < q := by linarith
  have h_denom_pos : 0 < (1 - lam) * q := mul_pos h_one_minus_lam_pos hq_pos
  -- |a'| ≤ |a| + Ds by reverse triangle inequality
  have h_triangle : |a'| ≤ |a| + Ds := by
    have h := abs_sub_abs_le_abs_sub a' a
    linarith
  -- bound |a|
  have ha_abs : |a| ≤ η * Yb / ((1 - lam) * q) := by
    rw [ha]
    rw [abs_div, abs_mul, abs_of_nonneg hη]
    have h_denom_abs : |(1 - lam) * q| = (1 - lam) * q := abs_of_pos h_denom_pos
    rw [h_denom_abs]
    have h := mul_le_mul_of_nonneg_left hY hη
    exact div_le_div_of_nonneg_right h (by linarith)
  -- bound denominator from below: (1-lam)*q ≥ 98901/100000
  have h_denom_ge : (1 - lam) * q ≥ (98901 : ℝ)/100000 := by
    have h1 : 1 - lam ≥ (999 : ℝ)/1000 := by linarith
    have h2 : q ≥ (99 : ℝ)/100 := hq
    have h1_nonneg : 0 ≤ 1 - lam := by linarith
    have h2_nonneg : 0 ≤ q := by linarith
    nlinarith
  -- So η*Yb/((1-lam)*q) ≤ η*Yb*(100000/98901)
  have ha_bound : η * Yb / ((1 - lam) * q) ≤ η * Yb * (100000/98901) := by
    have h_pos : 0 < (98901 : ℝ)/100000 := by norm_num
    have h_one_div : 1 / ((1 - lam) * q) ≤ 1 / ((98901 : ℝ)/100000) := by
      refine (one_div_le_one_div ?_ h_pos).mpr h_denom_ge
      exact h_denom_pos
    have h_num_nonneg : 0 ≤ η * Yb := mul_nonneg hη hYb_nonneg
    calc
      η * Yb / ((1 - lam) * q) = (η * Yb) * (1 / ((1 - lam) * q)) := by ring
      _ ≤ (η * Yb) * (1 / ((98901 : ℝ)/100000)) := mul_le_mul_of_nonneg_left h_one_div h_num_nonneg
      _ = η * Yb * (100000/98901) := by ring
  -- bound Ds
  have hDs_bound : Ds ≤ η * Yb / 200 + (103/100) * η * (Yb/1000 + (3/16000) * Yb + Yb/1000) := by
    rw [hDs]
    have h1 : tp / 2 ≤ η * Yb / 200 := by linarith
    have h2 : 3 * tp / 16 * Yb ≤ (3/16000) * Yb := by nlinarith
    have h3 : eY ≤ Yb / 1000 := heY
    have h4 : Yb * Dq ≤ Yb / 1000 := by nlinarith
    have h_factor_nonneg : 0 ≤ (103/100 : ℝ) * η := by nlinarith
    nlinarith
  -- combine: |a| + Ds ≤ 103/100 * η * Yb
  have h_total : |a| + Ds ≤ 103/100 * η * Yb := by
    have h_num_nonneg : 0 ≤ η * Yb := mul_nonneg hη hYb_nonneg
    have h_coeff : (100000/98901 : ℝ) + 1/200 + (103/100)*(1/1000 + 3/16000 + 1/1000) ≤ 103/100 := by
      field_simp
      norm_num
    nlinarith
  linarith

end AdversarialBco.Bit.BLP.RC
