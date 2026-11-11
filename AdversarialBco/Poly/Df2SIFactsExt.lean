/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvTools

@[expose] public section

/-!
# The extension: Lipschitz bound, sign, values on `K_ε`

For a closed convex `K ⊇ B̄(0, 1)`, `ε ∈ (0, 1)`, `f` convex on `K` with values in `[0, 1]` there, and `c ≥ (1 - ε)/ε`:
the extension `extOf K ε c f` (Df2EvTools.lean) is nonnegative, equals `f` on `K_ε = (1 - ε) K`, and
is `(1/ε + (2 + c)/(1 - ε))`-Lipschitz. Convexity is `extOf_convex`
of Df2EvTools.lean.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly.SIF

open AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-- (G2) `pip` is `1/(1 - ε)`-Lipschitz. -/
theorem pipOf_lip (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hball : Metric.closedBall 0 1 ⊆ K)
    (ε : ℝ) (hε1 : ε < 1) (x y : EuclideanSpace ℝ (Fin d)) :
    |pipOf K ε x - pipOf K ε y| ≤ ‖x - y‖ / (1 - ε) := by
  have hball' : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K :=
    Metric.ball_subset_closedBall.trans hball
  have hlip : LipschitzWith (1 : NNReal) (gauge K) := by
    have := Convex.lipschitzWith_gauge hK (by norm_num : (0 : NNReal) < 1) hball'
    simpa [inv_one] using this
  have hgauge : |gauge K x - gauge K y| ≤ ‖x - y‖ := by
    have hdist := hlip.dist_le_mul x y
    simpa [Real.dist_eq, dist_eq_norm, one_mul] using hdist
  have hpos : 0 < 1 - ε := by linarith
  have hdiv : |gauge K x / (1 - ε) - gauge K y / (1 - ε)| ≤ ‖x - y‖ / (1 - ε) := by
    calc
      |gauge K x / (1 - ε) - gauge K y / (1 - ε)| = |(gauge K x - gauge K y) / (1 - ε)| := by rw [sub_div]
      _ = |gauge K x - gauge K y| / |1 - ε| := by rw [abs_div]
      _ = |gauge K x - gauge K y| / (1 - ε) := by rw [abs_of_pos hpos]
      _ ≤ ‖x - y‖ / (1 - ε) := by
        gcongr
  have hmax : |max 1 (gauge K x / (1 - ε)) - max 1 (gauge K y / (1 - ε))| ≤
      |gauge K x / (1 - ε) - gauge K y / (1 - ε)| := by
    simpa [max_comm] using abs_max_sub_max_le_abs (gauge K x / (1 - ε)) (gauge K y / (1 - ε)) 1
  calc
    |pipOf K ε x - pipOf K ε y| = |max 1 (gauge K x / (1 - ε)) - max 1 (gauge K y / (1 - ε))| := rfl
    _ ≤ |gauge K x / (1 - ε) - gauge K y / (1 - ε)| := hmax
    _ ≤ ‖x - y‖ / (1 - ε) := hdiv

/-- (G3), one direction: for `y ∈ K` and `y' ∈ K_ε`, `f y' - f y ≤ ‖y' - y‖/ε`. -/
theorem lip_on_keps (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hball : Metric.closedBall 0 1 ⊆ K)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f) (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (y y' : EuclideanSpace ℝ (Fin d)) (hy : y ∈ K)
    (hy' : (1 - ε)⁻¹ • y' ∈ K) :
    f y' - f y ≤ ‖y' - y‖ / ε := by
  by_cases h_eq : y' = y
  · subst h_eq
    simp
  · set t := ‖y' - y‖ with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr h_eq)
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    set h := t⁻¹ • (y' - y) with hh_def
    have hh_norm : ‖h‖ = 1 := by
      rw [hh_def, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹), ← ht_def]
      field_simp [ne_of_gt ht_pos]
    set z := y' + ε • h with hz_def
    have hz_mem : z ∈ K := by
      have hh_mem_ball : h ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact hh_norm.le
      have hh_mem : h ∈ K := hball hh_mem_ball
      have h1 : 0 ≤ 1 - ε := by linarith
      have h2 : 0 ≤ ε := le_of_lt hε0
      have hsum : (1 - ε) + ε = 1 := by ring
      have hz_eq : z = (1 - ε) • ((1 - ε)⁻¹ • y') + ε • h := by
        rw [hz_def, hh_def]
        calc
          y' + ε • (t⁻¹ • (y' - y)) = ((1 - ε) • ((1 - ε)⁻¹ • y')) + ε • (t⁻¹ • (y' - y)) := by
            rw [smul_inv_smul₀ (show 1 - ε ≠ 0 from by linarith)]
          _ = (1 - ε) • ((1 - ε)⁻¹ • y') + ε • (t⁻¹ • (y' - y)) := rfl
      rw [hz_eq]
      exact hK hy' hh_mem h1 h2 hsum
    set a := t / (t + ε) with ha_def
    have ha_nonneg : 0 ≤ a := by
      rw [ha_def]
      positivity
    have ha_le_one : a ≤ 1 := by
      rw [ha_def]
      exact (div_le_one (by positivity)).mpr (by linarith)
    have ha_mul_eq : a * ε / t = 1 - a := by
      rw [ha_def]
      field_simp [ne_of_gt ht_pos, show t + ε ≠ 0 from by positivity]
      ring
    have hy'_eq : y' = (1 - a) • y + a • z := by
      rw [hz_def, hh_def]
      have hdiff : (1 - a) • y + a • (y' + ε • (t⁻¹ • (y' - y))) - y' = 0 := by
        calc
          (1 - a) • y + a • (y' + ε • (t⁻¹ • (y' - y))) - y'
              = (1 - a) • y + (a • y' + a • (ε • (t⁻¹ • (y' - y)))) - y' := by rw [smul_add]
          _ = ((1 - a) • y + a • y') + a • (ε • (t⁻¹ • (y' - y))) - y' := by abel
          _ = ((1 - a) • y + a • y' - y') + a • (ε • (t⁻¹ • (y' - y))) := by abel
          _ = ((1 - a) • y + a • y' - y') + (a * ε) • (t⁻¹ • (y' - y)) := by rw [smul_smul]
          _ = ((1 - a) • y + a • y' - y') + ((a * ε) * t⁻¹) • (y' - y) := by rw [smul_smul]
          _ = ((1 - a) • y + a • y' - y') + (a * ε / t) • (y' - y) := by ring
          _ = ((1 - a) • y + a • y' - y') + (1 - a) • (y' - y) := by rw [ha_mul_eq]
          _ = ((1 - a) • y + a • y' - y') + ((1 - a) • y' - (1 - a) • y) := by rw [smul_sub]
          _ = ((1 - a) • y - (1 - a) • y) + (a • y' - y' + (1 - a) • y') := by abel
          _ = 0 + (a • y' - y' + (1 - a) • y') := by rw [sub_self]
          _ = a • y' - y' + (1 - a) • y' := by rw [zero_add]
          _ = (a • y' + (1 - a) • y') - y' := by abel
          _ = ((a + (1 - a)) • y') - y' := by rw [add_smul]
          _ = (1 • y') - y' := by
            have h : a + (1 - a) = 1 := by ring
            simp [h]
          _ = y' - y' := by rw [one_smul]
          _ = 0 := by rw [sub_self]
      exact (sub_eq_zero.mp hdiff).symm
    have hfy_lower : 0 ≤ f y := (hf01 y hy).1
    have hfz_upper : f z ≤ 1 := (hf01 z hz_mem).2
    have h_convex : f y' ≤ (1 - a) • f y + a • f z := by
      rw [hy'_eq]
      have h1a_nonneg : 0 ≤ 1 - a := by linarith
      exact hf.2 hy hz_mem h1a_nonneg ha_nonneg (by ring)
    have h_ineq : f y' ≤ f y + a := by
      have h1 : (1 - a) • f y + a • f z ≤ (1 - a) • f y + a • (1 : ℝ) := by
        have hs := smul_le_smul_of_nonneg_left hfz_upper ha_nonneg
        linarith
      have h2 : (1 - a) • f y + a • (1 : ℝ) = f y + a • (1 - f y) := by
        simp [smul_eq_mul]
        ring
      have h3 : f y + a • (1 - f y) ≤ f y + a := by
        have hsmul : a • (1 - f y : ℝ) ≤ a • (1 : ℝ) :=
          smul_le_smul_of_nonneg_left (by linarith) ha_nonneg
        have h := add_le_add_left hsmul (f y)
        simpa [smul_eq_mul, mul_one] using h
      linarith
    have h_diff : f y' - f y ≤ a := by linarith
    have ha_le_t_div_eps : a ≤ t / ε := by
      rw [ha_def]
      exact div_le_div_of_nonneg_left ht_nonneg hε0 (by linarith)
    linarith

/-- The extension is nonnegative. -/
theorem extOf_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (hc : 0 ≤ c)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ extOf K ε c f x := by
  rw [AdversarialBco.Poly.EvGY.extOf]
  have hpip_ge_one : 1 ≤ pipOf K ε x := by
    rw [AdversarialBco.Poly.EvGY.pipOf]
    exact le_max_left _ _
  have hpip_pos : 0 < pipOf K ε x := by
    linarith
  have hzero_mem_K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      simp
    exact hball h0
  have h_one_minus_eps_nonneg : 0 ≤ 1 - ε := by linarith
  have h_eps_nonneg : 0 ≤ ε := by linarith
  have h_sum : (1 - ε) + ε = 1 := by ring
  have hpip_mem_K : (pipOf K ε x)⁻¹ • x ∈ K := by
    have htemp := pip_play_mem K hK hKc hball ε hε0 hε1 x
    -- htemp : (1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x) ∈ K
    have htemp' := (convex_iff_add_mem.mp hK) htemp hzero_mem_K (a := 1 - ε) (b := ε) h_one_minus_eps_nonneg h_eps_nonneg h_sum
    -- htemp' : (1 - ε) • ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) + ε • 0 ∈ K
    -- simplify htemp'
    have hsimp : (1 - ε) • ((1 - ε)⁻¹ • ((pipOf K ε x)⁻¹ • x)) + ε • (0 : EuclideanSpace ℝ (Fin d)) = (pipOf K ε x)⁻¹ • x := by
      have h_ne_zero : 1 - ε ≠ 0 := by linarith
      simp [smul_smul, smul_zero, h_ne_zero]
    rw [hsimp] at htemp'
    exact htemp'
  have hf_nonneg : 0 ≤ f ((pipOf K ε x)⁻¹ • x) := by
    have hmem := hf01 ((pipOf K ε x)⁻¹ • x) hpip_mem_K
    exact hmem.left
  have hfirst_term_nonneg : 0 ≤ pipOf K ε x * f ((pipOf K ε x)⁻¹ • x) := by
    nlinarith
  have hsecond_term_nonneg : 0 ≤ c * (pipOf K ε x - 1) := by
    have : 0 ≤ pipOf K ε x - 1 := by linarith
    nlinarith
  nlinarith

/-- The extension equals `f` on `K_ε`. -/
theorem extOf_eq_of_mem (K : Set (EuclideanSpace ℝ (Fin d))) (_hball : Metric.closedBall 0 1 ⊆ K)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (hε1 : ε < 1) (c : ℝ) (y : EuclideanSpace ℝ (Fin d))
    (hy : (1 - ε)⁻¹ • y ∈ K) : extOf K ε c f y = f y := by
  have hpos : 0 < 1 - ε := sub_pos.mpr hε1
  have hpos' : 0 ≤ 1 - ε := hpos.le
  have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ := inv_nonneg.mpr hpos'
  have hgauge1 : gauge K ((1 - ε)⁻¹ • y) ≤ 1 := gauge_le_one_of_mem hy
  have hgauge_eq : gauge K ((1 - ε)⁻¹ • y) = (1 - ε)⁻¹ * gauge K y := by
    simpa [smul_eq_mul] using gauge_smul_of_nonneg hinv_nonneg y
  have hineq : (1 - ε)⁻¹ * gauge K y ≤ 1 := by
    linarith
  have hgauge_y_le : gauge K y ≤ 1 - ε := by
    calc
      gauge K y = ((1 - ε) * (1 - ε)⁻¹) * gauge K y := by field_simp [hpos.ne.symm]
      _ = (1 - ε) * ((1 - ε)⁻¹ * gauge K y) := by ring
      _ ≤ (1 - ε) * 1 := mul_le_mul_of_nonneg_left hineq hpos'
      _ = 1 - ε := by ring
  have hdiv : gauge K y / (1 - ε) ≤ 1 :=
    (div_le_one hpos).mpr hgauge_y_le
  have hpip : pipOf K ε y = 1 := by
    unfold pipOf
    exact max_eq_left hdiv
  unfold extOf
  rw [hpip]
  simp

/-- (G7) the Lipschitz bound of the extension. -/
theorem extOf_lip (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f)
    (hf01 : ∀ x ∈ K, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ)
    (hc : (1 - ε) / ε ≤ c) (x x' : EuclideanSpace ℝ (Fin d)) :
    |extOf K ε c f x - extOf K ε c f x'| ≤ (1 / ε + (2 + c) / (1 - ε)) * ‖x - x'‖ := by
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by
    have : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      simp
    exact hball this
  have hεpos' : 0 < 1 - ε := by linarith
  have h_one_minus_ε_ne_zero : 1 - ε ≠ 0 := by linarith
  set t := ‖x - x'‖ with ht
  set ℓ := (1 - ε)⁻¹ with hℓ
  have hℓpos : 0 < ℓ := by
    rw [hℓ]
    exact inv_pos.mpr hεpos'
  have hℓ_nonneg : 0 ≤ ℓ := by linarith
  -- Helper lemma: the core inequality for any pair (a, b)
  have h_bound_pair (a b : EuclideanSpace ℝ (Fin d)) :
      extOf K ε c f b - extOf K ε c f a ≤ (1 / ε + (2 + c) / (1 - ε)) * ‖a - b‖ := by
    set ta := ‖a - b‖ with hta
    set Pa := pipOf K ε a with hPa
    set ya := Pa⁻¹ • a with hya
    set lam := Pa + ta * ℓ with hlam
    have hPapos : (1 : ℝ) ≤ Pa := by
      rw [hPa]
      exact le_max_left _ _
    have hPa_nonneg : 0 ≤ Pa := by linarith
    have hPa_ne_zero : Pa ≠ 0 := by linarith
    have hlam_pos : 0 < lam := by
      rw [hlam]
      have : 0 ≤ ta * ℓ := mul_nonneg (norm_nonneg _) hℓ_nonneg
      linarith
    have hlam_nonneg : 0 ≤ lam := by linarith
    have hlam_ge_Pa : Pa ≤ lam := by
      rw [hlam]
      have : 0 ≤ ta * ℓ := mul_nonneg (norm_nonneg _) hℓ_nonneg
      linarith
    have hPlam_b : pipOf K ε b ≤ lam := by
      have h := pipOf_lip K hK hball ε hε1 a b
      rw [hlam]
      have hbound : |Pa - pipOf K ε b| ≤ ta * ℓ := by
        simpa [hPa, hta, hℓ, div_eq_inv_mul, mul_comm] using h
      have h' : pipOf K ε b - Pa ≤ ta * ℓ := by
        have := abs_le.mp hbound
        linarith
      linarith
    have hya_in_K : ya ∈ K := by
      rw [hya]
      have hmem : (1 - ε)⁻¹ • ((pipOf K ε a)⁻¹ • a) ∈ K :=
        pip_play_mem K hK hKc hball ε hε0 hε1 a
      have h_eq : (1 - ε) • ((1 - ε)⁻¹ • ((pipOf K ε a)⁻¹ • a)) = (pipOf K ε a)⁻¹ • a := by
        rw [smul_smul]
        have : (1 - ε) * (1 - ε)⁻¹ = 1 := by field_simp [h_one_minus_ε_ne_zero]
        rw [this, one_smul]
      have hmem' : (1 - ε) • ((1 - ε)⁻¹ • ((pipOf K ε a)⁻¹ • a)) ∈ K :=
        hK.smul_mem_of_zero_mem h0 hmem ⟨by linarith, by linarith⟩
      rw [h_eq] at hmem'
      rw [hPa]
      exact hmem'
    have hfya_range : f ya ∈ Set.Icc (0 : ℝ) 1 := hf01 ya hya_in_K
    have hfya_high : f ya ≤ 1 := hfya_range.2
    set θa := Pa / lam with hθa
    have hθa0 : 0 ≤ θa := div_nonneg hPa_nonneg hlam_nonneg
    have hθa1 : θa ≤ 1 := (div_le_one hlam_pos).mpr hlam_ge_Pa
    have h_diff_eq : lam⁻¹ • b - θa • ya = lam⁻¹ • (b - a) := by
      calc
        lam⁻¹ • b - θa • ya = lam⁻¹ • b - (Pa / lam) • (Pa⁻¹ • a) := by rw [hθa, hya]
        _ = lam⁻¹ • b - ((Pa / lam) * Pa⁻¹) • a := by rw [smul_smul]
        _ = lam⁻¹ • b - (lam⁻¹) • a := by
          have h_scalar : (Pa / lam) * Pa⁻¹ = lam⁻¹ := by
            calc
              (Pa / lam) * Pa⁻¹ = Pa * Pa⁻¹ / lam := by ring
              _ = 1 / lam := by field_simp [hPa_ne_zero]
              _ = lam⁻¹ := by rw [one_div]
          rw [h_scalar]
        _ = lam⁻¹ • (b - a) := by rw [smul_sub]
    have h_ext_min := ext_min K hK hKc hball f hf hf01 ε hε0 hε1 c hc b lam hPlam_b
    have h_ext_b : extOf K ε c f b ≤ lam * f (lam⁻¹ • b) + c * (lam - 1) := by
      dsimp [extOf]
      linarith
    have h_ext_a : extOf K ε c f a = Pa * f ya + c * (Pa - 1) := by
      simp [extOf, hPa, hya]
    have h_bound1 : extOf K ε c f b - (Pa * f ya + c * (Pa - 1)) ≤
        lam * (f (lam⁻¹ • b) - f ya) + (lam - Pa) * (f ya + c) := by
      linarith
    have h_split : f (lam⁻¹ • b) - f ya =
        (f (lam⁻¹ • b) - f (θa • ya)) + (f (θa • ya) - f ya) := by ring
    have h_lip : f (lam⁻¹ • b) - f (θa • ya) ≤ ‖lam⁻¹ • b - θa • ya‖ / ε := by
      have hmem_θy : θa • ya ∈ K := by
        have hmem : (1 - ε)⁻¹ • ((pipOf K ε a)⁻¹ • a) ∈ K :=
          pip_play_mem K hK hKc hball ε hε0 hε1 a
        have hmem_ya : (1 - ε)⁻¹ • ya ∈ K := by simpa [hPa, hya] using hmem
        have h_eq : (Pa / lam) • ya = ((Pa / lam) * (1 - ε)) • ((1 - ε)⁻¹ • ya) := by
          symm
          calc
            ((Pa / lam) * (1 - ε)) • ((1 - ε)⁻¹ • ya) = ((Pa / lam) * (1 - ε) * (1 - ε)⁻¹) • ya := by
              rw [smul_smul]
            _ = ((Pa / lam) * ((1 - ε) * (1 - ε)⁻¹)) • ya := by ring
            _ = ((Pa / lam) * 1) • ya := by field_simp [h_one_minus_ε_ne_zero]
            _ = (Pa / lam) • ya := by ring
        rw [hθa, hya, h_eq]
        have h_coeff0 : 0 ≤ (Pa / lam) * (1 - ε) :=
          mul_nonneg (div_nonneg hPa_nonneg hlam_nonneg) (by linarith)
        have h_coeff1 : (Pa / lam) * (1 - ε) ≤ 1 := by
          have hineq : Pa * (1 - ε) ≤ lam := by
            rw [hlam]
            have : -Pa * ε ≤ 0 := by nlinarith
            have : 0 ≤ ta * (1 - ε)⁻¹ := mul_nonneg (norm_nonneg _) (by linarith)
            nlinarith
          have : (Pa / lam) * (1 - ε) = Pa * (1 - ε) / lam := by ring
          rw [this]
          exact (div_le_one hlam_pos).mpr hineq
        exact hK.smul_mem_of_zero_mem h0 hmem_ya ⟨h_coeff0, h_coeff1⟩
      have hmem_lam_inv_b : (1 - ε)⁻¹ • (lam⁻¹ • b) ∈ K := by
        have hmem : (1 - ε)⁻¹ • ((pipOf K ε b)⁻¹ • b) ∈ K :=
          pip_play_mem K hK hKc hball ε hε0 hε1 b
        have hpip_ne_zero : pipOf K ε b ≠ 0 := by
          have : 1 ≤ pipOf K ε b := le_max_left _ _
          linarith
        have h_eq : (1 - ε)⁻¹ • (lam⁻¹ • b) =
            (pipOf K ε b / lam) • ((1 - ε)⁻¹ • ((pipOf K ε b)⁻¹ • b)) := by
          calc
            (1 - ε)⁻¹ • (lam⁻¹ • b) = lam⁻¹ • ((1 - ε)⁻¹ • b) := by
              rw [smul_comm (1 - ε)⁻¹ lam⁻¹ b]
            _ = ((pipOf K ε b)⁻¹ * (pipOf K ε b / lam)) • ((1 - ε)⁻¹ • b) := by
              field_simp [hpip_ne_zero, hlam_pos.ne']
            _ = (pipOf K ε b)⁻¹ • ((pipOf K ε b / lam) • ((1 - ε)⁻¹ • b)) := by rw [mul_smul]
            _ = (pipOf K ε b / lam) • ((pipOf K ε b)⁻¹ • ((1 - ε)⁻¹ • b)) := by
              rw [smul_comm (pipOf K ε b)⁻¹]
            _ = (pipOf K ε b / lam) • ((1 - ε)⁻¹ • ((pipOf K ε b)⁻¹ • b)) := by
              rw [smul_comm (pipOf K ε b)⁻¹]
        rw [h_eq]
        have h_coeff0 : 0 ≤ pipOf K ε b / lam :=
          div_nonneg (by
            have : 1 ≤ pipOf K ε b := le_max_left _ _
            linarith) hlam_nonneg
        have h_coeff1 : pipOf K ε b / lam ≤ 1 := (div_le_one hlam_pos).mpr hPlam_b
        exact hK.smul_mem_of_zero_mem h0 hmem ⟨h_coeff0, h_coeff1⟩
      have := lip_on_keps K hK hball f hf hf01 ε hε0 hε1 (θa • ya) (lam⁻¹ • b) hmem_θy hmem_lam_inv_b
      simpa [sub_sub] using this
    have h_ray : f (θa • ya) - f ya ≤ 1 - θa := by
      have hray := ray_bounds K hK h0 f hf hf01 ε hε0 hε1 ya
        (by
          simpa [hPa, hya] using pip_play_mem K hK hKc hball ε hε0 hε1 a
        ) θa hθa0 hθa1
      rcases hray with ⟨_, hray_upper⟩
      linarith
    have h_term1 : lam * (f (lam⁻¹ • b) - f (θa • ya)) ≤ ta / ε := by
      calc
        lam * (f (lam⁻¹ • b) - f (θa • ya)) ≤ lam * (‖lam⁻¹ • b - θa • ya‖ / ε) :=
          mul_le_mul_of_nonneg_left h_lip hlam_nonneg
        _ = lam * ((lam⁻¹ * ta) / ε) := by
          rw [h_diff_eq]
          have h_norm : ‖lam⁻¹ • (b - a)‖ = lam⁻¹ * ‖b - a‖ := by
            rw [norm_smul_of_nonneg (by exact le_of_lt (inv_pos.mpr hlam_pos))]
          rw [h_norm, hta, norm_sub_rev]
        _ = (lam * lam⁻¹) * ta / ε := by ring
        _ = 1 * ta / ε := by field_simp [hlam_pos.ne']
        _ = ta / ε := by simp
    have h_term2 : lam * (f (θa • ya) - f ya) ≤ ta * ℓ := by
      calc
        lam * (f (θa • ya) - f ya) ≤ lam * (1 - θa) :=
          mul_le_mul_of_nonneg_left h_ray hlam_nonneg
        _ = lam * (1 - Pa / lam) := by rw [hθa]
        _ = lam - Pa := by field_simp
        _ = ta * ℓ := by
          rw [hlam]
          ring
    have h_term3 : (lam - Pa) * (f ya + c) ≤ (ta * ℓ) * (1 + c) := by
      have h_diff : lam - Pa = ta * ℓ := by
        rw [hlam]
        ring
      rw [h_diff]
      have h_nonneg_ta_lam : 0 ≤ ta * ℓ := mul_nonneg (norm_nonneg _) hℓ_nonneg
      have : f ya + c ≤ 1 + c := by linarith
      nlinarith
    have h_sum : lam * (f (lam⁻¹ • b) - f ya) + (lam - Pa) * (f ya + c) ≤
        ta / ε + ta * ℓ * (2 + c) := by
      have h_split_lam : lam * (f (lam⁻¹ • b) - f ya) =
          lam * (f (lam⁻¹ • b) - f (θa • ya)) + lam * (f (θa • ya) - f ya) := by
        rw [h_split, mul_add]
      rw [h_split_lam]
      nlinarith
    have h_target : ta / ε + ta * ℓ * (2 + c) = (1 / ε + (2 + c) / (1 - ε)) * ta := by
      rw [hℓ]
      ring
    rw [h_target] at h_sum
    linarith
  -- Now apply the helper lemma to get both directions
  have h_main : extOf K ε c f x' - extOf K ε c f x ≤ (1 / ε + (2 + c) / (1 - ε)) * t := by
    simpa [ht] using h_bound_pair x x'
  have h_symm : extOf K ε c f x - extOf K ε c f x' ≤ (1 / ε + (2 + c) / (1 - ε)) * t := by
    simpa [ht, norm_sub_rev] using h_bound_pair x' x
  -- Combine using abs_le
  rw [abs_le]
  constructor
  · linarith
  · linarith

end AdversarialBco.Poly.SIF
