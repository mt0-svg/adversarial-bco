/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Trunc

@[expose] public section

/-!
# The truncation and compensator core of Lemmas S# and QM: proofs

One theorem per `Prop` of `AdversarialBco/Poly/Trunc.lean`, named after it in lower camel case, and the 16 leaves
they are assembled from. `ssharp_compensator_arith` sets
`maxHeartbeats 400000` with `in`.
-/

open AdversarialBco.Poly MeasureTheory ProbabilityTheory

universe u

/-! ## Leaves -/

theorem AdversarialBco.Poly.trunc_centred_mean {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (G : Set Ω) (X : Ω → ℝ) (hG : MeasurableSet G)
    (hX : Integrable X μ) : μ[truncCentred μ m G X | m] =ᵐ[μ] 0 := by
  have hY : Integrable (G.indicator X) μ := hX.indicator (hm G hG)
  have : SigmaFinite (μ.trim hm) := by infer_instance
  have h_cond := condExp_condExp_of_le (f := G.indicator X) (μ := μ) (le_refl m) hm
  unfold truncCentred
  calc
    μ[G.indicator X - μ[G.indicator X | m] | m] =ᵐ[μ] μ[G.indicator X | m] - μ[μ[G.indicator X | m] | m] :=
      condExp_sub hY (integrable_condExp (μ := μ) (f := G.indicator X) (m := m)) m
    _ =ᵐ[μ] μ[G.indicator X | m] - μ[G.indicator X | m] :=
      (Filter.EventuallyEq.refl _ _).sub h_cond
    _ =ᵐ[μ] 0 := by simp

theorem AdversarialBco.Poly.trunc_centred_bound {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (G : Set Ω) (X : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hXB : ∀ᵐ ω ∂μ, ω ∈ G → |X ω| ≤ B) : ∀ᵐ ω ∂μ, |truncCentred μ m G X ω| ≤ 2 * B := by
  let Y := G.indicator X
  have hY_bound : ∀ᵐ ω ∂μ, |Y ω| ≤ B := by
    filter_upwards [hXB] with ω hω
    by_cases hωG : ω ∈ G
    · have hXω : |X ω| ≤ B := hω hωG
      simpa [Y, Set.indicator_of_mem hωG] using hXω
    · simpa [Y, hωG, abs_zero] using hB
  have h_cond_bound : ∀ᵐ ω ∂μ, |μ[Y | m] ω| ≤ B :=
    ae_bdd_abs_condExp_of_ae_bdd_abs hY_bound
  filter_upwards [hY_bound, h_cond_bound] with ω hY h_cond
  have h_trunc : truncCentred μ m G X ω = Y ω - μ[Y | m] ω := rfl
  rw [h_trunc]
  calc
    |Y ω - μ[Y | m] ω| ≤ |Y ω| + |μ[Y | m] ω| := abs_sub _ _
    _ ≤ B + B := add_le_add hY h_cond
    _ = 2 * B := by ring

theorem AdversarialBco.Poly.trunc_centred_var {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (G : Set Ω) (X : Ω → ℝ) (hG : MeasurableSet G)
    (hX : MemLp X 2 μ) :
    (μ[fun ω => truncCentred μ m G X ω ^ 2 | m] ≤ᵐ[μ] μ[G.indicator (fun ω => X ω ^ 2) | m]) ∧
      μ[G.indicator (fun ω => X ω ^ 2) | m] ≤ᵐ[μ] μ[fun ω => X ω ^ 2 | m] := by
  let Y := G.indicator X
  have hG0 : MeasurableSet[m0] G := hm G hG
  have hY_mem : MemLp Y 2 μ := hX.indicator hG0
  have hY_int_sq : Integrable (fun ω => Y ω ^ 2) μ := hY_mem.integrable_sq
  have hX_int_sq : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have hY_int_indicator_sq : Integrable (G.indicator (fun ω => X ω ^ 2)) μ :=
    hX_int_sq.indicator hG0
  have h_sq_nonneg : ∀ ω, 0 ≤ X ω ^ 2 := fun ω => sq_nonneg (X ω)
  have h_indicator_sq_le : G.indicator (fun ω => X ω ^ 2) ≤ (fun ω => X ω ^ 2) :=
    Set.indicator_le_self' (fun ω hω => sq_nonneg (X ω))
  have h_part2 : μ[G.indicator (fun ω => X ω ^ 2) | m] ≤ᵐ[μ] μ[fun ω => X ω ^ 2 | m] :=
    condExp_mono hY_int_indicator_sq hX_int_sq (ae_of_all μ h_indicator_sq_le)
  have h_part1 : μ[fun ω => truncCentred μ m G X ω ^ 2 | m] ≤ᵐ[μ] μ[G.indicator (fun ω => X ω ^ 2) | m] := by
    have h_trunc_eq : (fun ω => truncCentred μ m G X ω ^ 2) = (fun ω => (Y ω - μ[Y | m] ω) ^ 2) := by
      ext ω
      simp [truncCentred, Y]
    have h_Y_sq_eq : Y ^ 2 = G.indicator (fun ω => X ω ^ 2) := by
      ext ω
      by_cases hω : ω ∈ G
      · simp [Y, hω]
      · simp [Y, hω]
    have h_nonneg_condExp_sq : 0 ≤ᵐ[μ] (fun ω => (μ[Y | m] ω) ^ 2) := by
      filter_upwards with ω
      apply pow_two_nonneg
    calc
      μ[fun ω => truncCentred μ m G X ω ^ 2 | m] =ᵐ[μ] μ[fun ω => (Y ω - μ[Y | m] ω) ^ 2 | m] := by
        rw [h_trunc_eq]
      _ = Var[Y; μ | m] := rfl
      _ =ᵐ[μ] μ[Y ^ 2 | m] - μ[Y | m] ^ 2 := condVar_ae_eq_condExp_sq_sub_sq_condExp hm hY_mem
      _ ≤ᵐ[μ] μ[Y ^ 2 | m] := by
        filter_upwards [h_nonneg_condExp_sq] with ω hω
        exact sub_le_self _ hω
      _ = μ[G.indicator (fun ω => X ω ^ 2) | m] := by rw [h_Y_sq_eq]
  exact And.intro h_part1 h_part2

theorem AdversarialBco.Poly.trunc_decomp {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (G : Set Ω) (X : Ω → ℝ) (hG : MeasurableSet G)
    (hX : Integrable X μ) :
    ∀ᵐ ω ∂μ, ω ∈ G → X ω - μ[X | m] ω = truncCentred μ m G X ω - truncComp μ m G X ω := by
  have hXG : Integrable (G.indicator X) μ := hX.indicator (hm G hG)
  have hXGc : Integrable (Gᶜ.indicator X) μ := hX.indicator (hm (Gᶜ) hG.compl)
  have h_indicator_add : G.indicator X + Gᶜ.indicator X = X := Set.indicator_self_add_compl G X
  have h_cond_exp_add : μ[G.indicator X | m] + μ[Gᶜ.indicator X | m] =ᵐ[μ] μ[G.indicator X + Gᶜ.indicator X | m] :=
    (MeasureTheory.condExp_add hXG hXGc m).symm
  have h_cond_exp_eq : μ[G.indicator X | m] + μ[Gᶜ.indicator X | m] =ᵐ[μ] μ[X | m] :=
    h_cond_exp_add.trans (by rw [h_indicator_add])
  filter_upwards [h_cond_exp_eq] with ω hω hωG
  dsimp [truncCentred, truncComp]
  rw [Set.indicator_of_mem hωG]
  -- hω : (μ[G.indicator X | m] + μ[Gᶜ.indicator X | m]) ω = (μ[X | m]) ω
  -- i.e. μ[G.indicator X | m] ω + μ[Gᶜ.indicator X | m] ω = μ[X | m] ω
  rw [Pi.add_apply] at hω
  rw [← hω]
  ring

theorem AdversarialBco.Poly.quad_disc_of_rat (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ q : ℚ, 0 ≤ a - 2 * (q : ℝ) * b + (q : ℝ) ^ 2 * c) : b ^ 2 ≤ a * c := by
  by_contra! hlt
  -- hlt : a * c < b ^ 2
  rcases lt_or_eq_of_le hc with (hcpos | hcz)
  · -- case c > 0
    have hcpos' : 0 < c := hcpos
    set e := b ^ 2 - a * c with he
    have hepos : 0 < e := by
      dsimp [e]
      linarith
    have h_identity (t : ℝ) : a - 2 * t * b + t ^ 2 * c = c * (t - b / c) ^ 2 - e / c := by
      field_simp [hcpos'.ne']
      ring
    set s := Real.sqrt e / (2 * c) with hs
    have hsqrt_pos : 0 < Real.sqrt e := Real.sqrt_pos.mpr hepos
    have hden_pos : 0 < 2 * c := by nlinarith
    have hs_pos : 0 < s := div_pos hsqrt_pos hden_pos
    have hsq_sqrt : (Real.sqrt e) ^ 2 = e := Real.sq_sqrt hepos.le
    have hcsq_lt_e : c ^ 2 * s ^ 2 < e := by
      dsimp [s]
      have hcalc : c ^ 2 * ((Real.sqrt e) / (2 * c)) ^ 2 = e / 4 := by
        calc
          c ^ 2 * ((Real.sqrt e) / (2 * c)) ^ 2 = c ^ 2 * ((Real.sqrt e) ^ 2 / ((2 * c) ^ 2)) := by ring
          _ = c ^ 2 * (e / (4 * c ^ 2)) := by rw [hsq_sqrt]; ring
          _ = e / 4 := by field_simp [hcpos'.ne']
      rw [hcalc]
      nlinarith
    have h_lt : b / c - s < b / c + s := by
      nlinarith
    rcases exists_rat_btwn h_lt with ⟨q, hq1, hq2⟩
    -- hq1 : b / c - s < (q : ℝ), hq2 : (q : ℝ) < b / c + s
    have h_abs_lt : |(q : ℝ) - b / c| < s := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have h_abs_lt' := abs_lt.mp h_abs_lt
    -- h_abs_lt' : -s < (q : ℝ) - b / c ∧ (q : ℝ) - b / c < s
    have h_sq_lt : ((q : ℝ) - b / c) ^ 2 < s ^ 2 :=
      sq_lt_sq' h_abs_lt'.1 h_abs_lt'.2
    have hq_val := h q
    rw [h_identity (q : ℝ)] at hq_val
    -- hq_val : 0 ≤ c * ((q : ℝ) - b / c) ^ 2 - e / c
    have h_cs_bound : c * ((q : ℝ) - b / c) ^ 2 < e / c := by
      have h1 : c * ((q : ℝ) - b / c) ^ 2 < c * s ^ 2 := by
        nlinarith
      have h2 : c * s ^ 2 = e / (4 * c) := by
        dsimp [s]
        field_simp [hcpos'.ne']
        nlinarith
      have h3 : e / (4 * c) < e / c :=
        div_lt_div_of_pos_left hepos hcpos' (by nlinarith)
      nlinarith
    nlinarith
  · -- case c = 0
    have hcz' : c = 0 := hcz.symm
    rw [hcz'] at hlt h
    simp at hlt h
    -- hlt : 0 < b ^ 2
    -- h : ∀ q : ℚ, 0 ≤ a - 2 * (q : ℝ) * b
    have hb_ne_zero : b ≠ 0 := by
      intro hbz
      rw [hbz] at hlt
      simp at hlt
    by_cases hb_pos : 0 < b
    · -- b > 0: pick q > a / (2 * b)
      rcases exists_rat_gt (a / (2 * b)) with ⟨q, hq⟩
      have hq_val := h q
      -- hq_val : 2 * (q : ℝ) * b ≤ a
      -- hq : a / (2 * b) < (q : ℝ)
      have ha_lt : a < 2 * (q : ℝ) * b := by
        have hpos : 0 < 2 * b := by nlinarith
        calc
          a = (a / (2 * b)) * (2 * b) := by field_simp [hb_pos.ne']
          _ < (q : ℝ) * (2 * b) := by nlinarith
          _ = 2 * (q : ℝ) * b := by ring
      linarith
    · -- b ≤ 0, and since b ≠ 0, b < 0
      have hb_neg : b < 0 := by
        by_contra! hb_nonneg
        have hbz' : b = 0 := by linarith
        exact hb_ne_zero hbz'
      rcases exists_rat_lt (a / (2 * b)) with ⟨q, hq⟩
      have hq_val := h q
      -- hq_val : 2 * (q : ℝ) * b ≤ a
      -- hq : (q : ℝ) < a / (2 * b)
      have ha_lt : a < 2 * (q : ℝ) * b := by
        have hneg : 2 * b < 0 := by nlinarith
        calc
          a = (a / (2 * b)) * (2 * b) := by field_simp [hb_neg.ne']
          _ < (q : ℝ) * (2 * b) := by nlinarith
          _ = 2 * (q : ℝ) * b := by ring
      linarith

theorem AdversarialBco.Poly.condExp_cauchy_schwarz {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0) (A : Set Ω) (X : Ω → ℝ) (hA : MeasurableSet A)
    (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, |μ[A.indicator X | m] ω| ≤
      Real.sqrt (μ[fun ω => X ω ^ 2 | m] ω) * Real.sqrt (μ[A.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  set Y := A.indicator (fun _ => (1 : ℝ)) with hY_def
  have hY_nonneg : 0 ≤ Y := by
    intro ω; dsimp [Y]; exact Set.indicator_nonneg (fun _ _ => by norm_num) ω
  have hY_nonneg_ae : 0 ≤ᵐ[μ] Y := ae_of_all μ hY_nonneg
  have hY_sq_eq_Y : Y ^ 2 = Y := by
    ext ω; dsimp [Y]
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h]
  have hXY_eq : A.indicator X = X * Y := by
    ext ω; dsimp [Y]
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h]
  have hX_sq_int : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have hX_int : Integrable X μ := hX.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hA_m0 : MeasurableSet[m0] A := hm A hA
  have hY_int : Integrable Y μ := (integrable_const (1 : ℝ)).indicator hA_m0
  have hXY_int : Integrable (A.indicator X) μ := hX_int.indicator hA_m0
  have hY_sq_eq_Y_apply (ω : Ω) : Y ω ^ 2 = Y ω := by
    have h := congrFun hY_sq_eq_Y ω; simpa only [Pi.pow_apply] using h
  -- For each q : ℚ, the quadratic form (X - qY)^2 ≥ 0 pointwise
  have h_quad_nonneg (q : ℚ) : 0 ≤ᵐ[μ] (fun ω => X ω ^ 2 - 2 * (q : ℝ) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω) := by
    refine (ae_of_all μ ?_)
    intro ω
    have h_nonneg_sq : 0 ≤ (X ω - (q : ℝ) * Y ω) ^ 2 := sq_nonneg _
    have hgoal : 0 ≤ X ω ^ 2 - 2 * (q : ℝ) * ((A.indicator X) ω) + (q : ℝ) ^ 2 * Y ω := by
      calc
        0 ≤ (X ω - (q : ℝ) * Y ω) ^ 2 := h_nonneg_sq
        _ = X ω ^ 2 - 2 * (q : ℝ) * (X ω * Y ω) + (q : ℝ) ^ 2 * (Y ω ^ 2) := by ring
        _ = X ω ^ 2 - 2 * (q : ℝ) * ((A.indicator X) ω) + (q : ℝ) ^ 2 * Y ω := by
          rw [hXY_eq, Pi.mul_apply, hY_sq_eq_Y_apply]
    simpa using hgoal
  -- Expand μ[(X - qY)^2 | m] using condExp_add and condExp_smul
  have h_quad_cond_exp (q : ℚ) : 0 ≤ᵐ[μ] (fun ω =>
      μ[fun ω => X ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[A.indicator X | m] ω + (q : ℝ) ^ 2 * μ[Y | m] ω) := by
    have h_nonneg : 0 ≤ᵐ[μ] μ[fun ω => (X ω - (q : ℝ) * Y ω) ^ 2 | m] :=
      condExp_nonneg (ae_of_all μ fun ω => pow_two_nonneg _)
    -- Step 1: Replace the integrand using pointwise equality
    have h_replace : μ[fun ω => (X ω - (q : ℝ) * Y ω) ^ 2 | m] =ᵐ[μ]
        μ[fun ω => X ω ^ 2 - 2 * (q : ℝ) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω | m] := by
      refine condExp_congr_ae (ae_of_all μ fun ω => ?_)
      calc
        (X ω - (q : ℝ) * Y ω) ^ 2 = X ω ^ 2 - 2 * (q : ℝ) * (X ω * Y ω) + (q : ℝ) ^ 2 * (Y ω ^ 2) := by ring
        _ = X ω ^ 2 - 2 * (q : ℝ) * ((A.indicator X) ω) + (q : ℝ) ^ 2 * Y ω := by
          rw [hXY_eq, Pi.mul_apply, hY_sq_eq_Y_apply]
    -- Step 2: Expand the conditional expectation using condExp_add and condExp_smul
    have h_int_mid : Integrable (fun ω => (-2 * (q : ℝ)) * (A.indicator X) ω) μ :=
      hXY_int.smul (-2 * (q : ℝ))
    have h_int_last : Integrable (fun ω => (q : ℝ) ^ 2 * Y ω) μ :=
      hY_int.smul ((q : ℝ) ^ 2)
    have h_expand : μ[fun ω => X ω ^ 2 - 2 * (q : ℝ) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω | m] =ᵐ[μ]
        (fun ω => μ[fun ω => X ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[A.indicator X | m] ω + (q : ℝ) ^ 2 * μ[Y | m] ω) := by
      calc
        μ[fun ω => X ω ^ 2 - 2 * (q : ℝ) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω | m] =ᵐ[μ]
            μ[(fun ω => X ω ^ 2) + (fun ω => (-2 * (q : ℝ)) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω) | m] := by
          refine condExp_congr_ae (ae_of_all μ fun ω => ?_)
          simp only [Pi.add_apply]; ring
        _ =ᵐ[μ] μ[fun ω => X ω ^ 2 | m] + μ[fun ω => (-2 * (q : ℝ)) * (A.indicator X) ω + (q : ℝ) ^ 2 * Y ω | m] :=
          condExp_add hX_sq_int (h_int_mid.add h_int_last) m
        _ =ᵐ[μ] μ[fun ω => X ω ^ 2 | m] + (μ[fun ω => (-2 * (q : ℝ)) * (A.indicator X) ω | m] + μ[fun ω => (q : ℝ) ^ 2 * Y ω | m]) := by
          have h := condExp_add h_int_mid h_int_last m
          refine (Filter.EventuallyEq.refl _ _).add h
        _ =ᵐ[μ] μ[fun ω => X ω ^ 2 | m] + (((-2 * (q : ℝ)) • μ[A.indicator X | m]) + ((q : ℝ) ^ 2 • μ[Y | m])) := by
          have h := (condExp_smul (μ := μ) (-2 * (q : ℝ)) (A.indicator X) m).add
            (condExp_smul (μ := μ) ((q : ℝ) ^ 2) Y m)
          refine (Filter.EventuallyEq.refl _ _).add h
        _ = (fun ω => μ[fun ω => X ω ^ 2 | m] ω + (((-2 * (q : ℝ)) • μ[A.indicator X | m]) ω + ((q : ℝ) ^ 2 • μ[Y | m]) ω)) := rfl
        _ = (fun ω => μ[fun ω => X ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[A.indicator X | m] ω + (q : ℝ) ^ 2 * μ[Y | m] ω) := by
          ext ω; simp; ring
    -- Step 3: Combine nonnegativity with the expansion
    filter_upwards [h_nonneg, h_replace, h_expand] with ω h_nonneg_ω h_replace_ω h_expand_ω
    rw [h_replace_ω] at h_nonneg_ω
    rw [h_expand_ω] at h_nonneg_ω
    exact h_nonneg_ω
  -- Combine all q using countable intersection: ∀ᵐ ω, ∀ q, 0 ≤ f_q ω
  have h_all_q : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 ≤ μ[fun ω => X ω ^ 2 | m] ω - 2 * (q : ℝ) * μ[A.indicator X | m] ω + (q : ℝ) ^ 2 * μ[Y | m] ω := by
    rw [ae_all_iff]
    exact h_quad_cond_exp
  have h_sq_nonneg : 0 ≤ᵐ[μ] μ[fun ω => X ω ^ 2 | m] :=
    condExp_nonneg (ae_of_all μ fun ω => pow_two_nonneg _)
  have h_Y_nonneg : 0 ≤ᵐ[μ] μ[Y | m] :=
    condExp_nonneg hY_nonneg_ae
  -- Apply quad_disc_of_rat and take square roots
  filter_upwards [h_all_q, h_sq_nonneg, h_Y_nonneg] with ω h_all h_sq h_Y
  have h_disc : (μ[A.indicator X | m] ω) ^ 2 ≤ (μ[fun ω => X ω ^ 2 | m] ω) * (μ[Y | m] ω) :=
    quad_disc_of_rat (μ[fun ω => X ω ^ 2 | m] ω) (μ[A.indicator X | m] ω) (μ[Y | m] ω) h_Y h_all
  calc
    |μ[A.indicator X | m] ω| = Real.sqrt ((μ[A.indicator X | m] ω) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((μ[fun ω => X ω ^ 2 | m] ω) * (μ[Y | m] ω)) :=
      Real.sqrt_le_sqrt h_disc
    _ = Real.sqrt (μ[fun ω => X ω ^ 2 | m] ω) * Real.sqrt (μ[Y | m] ω) := by
      rw [Real.sqrt_mul h_sq]
    _ = Real.sqrt (μ[fun ω => X ω ^ 2 | m] ω) * Real.sqrt (μ[A.indicator (fun _ => (1 : ℝ)) | m] ω) := by
      simp [Y]

theorem AdversarialBco.Poly.ratio_at_mean (d : ℕ) (lam w : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    (hd : lam * d ≤ 1) (hw : 0 ≤ w) :
    0 ≤ ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ∧
      ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ≤ Real.exp 2 := by
  have h_one_minus_lam_pos : 0 < 1 - lam := by linarith
  have h_one_minus_lam_sq_pos : 0 < (1 - lam) ^ 2 := pow_pos h_one_minus_lam_pos 2
  have h_one_minus_lam_sq_le_one : (1 - lam) ^ 2 ≤ 1 := by
    nlinarith
  have h_div_ge_one : 1 ≤ 1 / (1 - lam) ^ 2 :=
    (one_le_div h_one_minus_lam_sq_pos).mpr h_one_minus_lam_sq_le_one
  have h_nonneg : 0 ≤ 1 / (1 - lam) ^ 2 - 1 := by linarith
  have h_exp_bound : Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hw2 : 0 ≤ w / 2 := by nlinarith
    nlinarith
  have h_exp_ineq : 1 + 2 * lam ≤ Real.exp (2 * lam) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * lam)
  have h_prod_ge_one : 1 ≤ (1 - lam) * (1 + 2 * lam) := by
    nlinarith
  have h_one_minus_lam_nonneg : 0 ≤ 1 - lam := by linarith
  have h_key' : (1 - lam) * (1 + 2 * lam) ≤ (1 - lam) * Real.exp (2 * lam) :=
    mul_le_mul_of_nonneg_left h_exp_ineq h_one_minus_lam_nonneg
  have h_key : 1 ≤ (1 - lam) * Real.exp (2 * lam) := by linarith
  have h_pow : 1 ≤ ((1 - lam) * Real.exp (2 * lam)) ^ d :=
    one_le_pow₀ h_key
  have h_expand : ((1 - lam) * Real.exp (2 * lam)) ^ d = (1 - lam) ^ d * Real.exp (d * (2 * lam)) := by
    calc
      ((1 - lam) * Real.exp (2 * lam)) ^ d = (1 - lam) ^ d * (Real.exp (2 * lam)) ^ d := by
        rw [mul_pow]
      _ = (1 - lam) ^ d * Real.exp (d * (2 * lam)) := by
        rw [← Real.exp_nat_mul (2 * lam) d]
  rw [h_expand] at h_pow
  have hA_pos : 0 < (1 - lam) ^ d := pow_pos h_one_minus_lam_pos d
  have h_inv_bound : ((1 - lam) ^ d)⁻¹ ≤ Real.exp (d * (2 * lam)) := by
    rw [inv_le_iff_one_le_mul₀ hA_pos]
    rw [mul_comm]
    exact h_pow
  have h_d_2lam_le_2 : d * (2 * lam) ≤ 2 := by
    nlinarith
  have h_exp_le : Real.exp (d * (2 * lam)) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr h_d_2lam_le_2
  have hA_bound : ((1 - lam) ^ d)⁻¹ ≤ Real.exp 2 := by
    linarith
  have hA_nonneg : 0 ≤ ((1 - lam) ^ d)⁻¹ := le_of_lt (inv_pos.mpr hA_pos)
  have hB_nonneg : 0 ≤ Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) :=
    le_of_lt (Real.exp_pos _)
  have h_exp2_nonneg : 0 ≤ Real.exp 2 := le_of_lt (Real.exp_pos 2)
  have h_nonneg' : 0 ≤ ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) :=
    mul_nonneg hA_nonneg hB_nonneg
  have h_bound' : ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ≤ Real.exp 2 := by
    calc
      ((1 - lam) ^ d)⁻¹ * Real.exp (-(w / 2) * (1 / (1 - lam) ^ 2 - 1)) ≤ Real.exp 2 * 1 :=
        mul_le_mul hA_bound h_exp_bound hB_nonneg h_exp2_nonneg
      _ = Real.exp 2 := by simp
  exact And.intro h_nonneg' h_bound'

theorem AdversarialBco.Poly.estimator_size (lam r : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp 2) : |1 + (r - 1) / lam| ≤ Real.exp 2 / lam := by
  have h_exp_ge_one : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num : 0 ≤ (2 : ℝ))
  have h_num_lower : -1 ≤ lam + r - 1 := by
    linarith
  have h_num_upper : lam + r - 1 ≤ Real.exp 2 := by
    linarith
  have h_abs_num : |lam + r - 1| ≤ Real.exp 2 := by
    apply abs_le.mpr
    constructor
    · linarith
    · linarith
  calc
    |1 + (r - 1) / lam| = |(lam + r - 1) / lam| := by
      field_simp [hlam.ne.symm]
      ring_nf
    _ = |lam + r - 1| / |lam| := by rw [abs_div]
    _ = |lam + r - 1| / lam := by rw [abs_of_pos hlam]
    _ ≤ Real.exp 2 / lam := by
      exact div_le_div_of_nonneg_right h_abs_num (by linarith)

theorem AdversarialBco.Poly.estimator_unbiased (d : ℕ) (p f : (Fin d → ℝ) → ℝ) (lam : ℝ) (x : Fin d → ℝ)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hp : ∀ y, 0 < p y) :
    ∫ y, p y * (p ((1 - lam)⁻¹ • (y - lam • x)) / ((1 - lam) ^ d * p y)) * f y =
      ∫ z, p z * f ((1 - lam) • z + lam • x) := by
  set c := (1 - lam)⁻¹ with hc_def
  have h_one_minus_lam_pos : 0 < 1 - lam := sub_pos_of_lt hlam1
  have h_one_minus_lam_ne_zero : 1 - lam ≠ 0 := by linarith
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact inv_pos.mpr h_one_minus_lam_pos
  have h_finrank : Module.finrank ℝ (Fin d → ℝ) = d :=
    Module.finrank_fin_fun ℝ
  -- define h(z) = p(z) * f((1-lam) • z + lam • x) / (1-lam)^d
  set h : (Fin d → ℝ) → ℝ := fun z => p z * f ((1 - lam) • z + lam • x) / ((1 - lam) ^ d) with hh_def
  have h_left_integrand : (fun (y : Fin d → ℝ) => p y * (p ((1 - lam)⁻¹ • (y - lam • x)) / ((1 - lam) ^ d * p y)) * f y) =
      fun y => h (c • (y - lam • x)) := by
    ext y
    dsimp [h, c]
    have hp_pos : p y ≠ 0 := by exact ne_of_gt (hp y)
    calc
      p y * (p ((1 - lam)⁻¹ • (y - lam • x)) / ((1 - lam) ^ d * p y)) * f y
          = p ((1 - lam)⁻¹ • (y - lam • x)) * f y / ((1 - lam) ^ d) := by
        field_simp [hp_pos, h_one_minus_lam_ne_zero]
      _ = p ((1 - lam)⁻¹ • (y - lam • x)) * f ((1 - lam) • ((1 - lam)⁻¹ • (y - lam • x)) + lam • x) / ((1 - lam) ^ d) := by
        congr
        have : (1 - lam) • ((1 - lam)⁻¹ • (y - lam • x)) + lam • x = y := by
          calc
            (1 - lam) • ((1 - lam)⁻¹ • (y - lam • x)) + lam • x
                = ((1 - lam) * (1 - lam)⁻¹) • (y - lam • x) + lam • x := by rw [smul_smul]
            _ = (1 : ℝ) • (y - lam • x) + lam • x := by
              field_simp [h_one_minus_lam_ne_zero]
            _ = (y - lam • x) + lam • x := by simp
            _ = y := by simp [sub_add_cancel]
        rw [this]
      _ = h (c • (y - lam • x)) := rfl
  rw [h_left_integrand]
  -- Now we have ∫ y, h (c • (y - lam • x))
  -- Translation invariance: ∫ y, h(c • (y - lam • x)) dy = ∫ y, h(c • y) dy
  have h_translate : (∫ y : Fin d → ℝ, h (c • (y - lam • x))) = (∫ y : Fin d → ℝ, h (c • y)) := by
    -- integral_sub_right_eq_self g a : ∫ x, g (x - a) = ∫ x, g x
    simpa using (MeasureTheory.integral_sub_right_eq_self (fun y => h (c • y)) (lam • x) (μ := volume))
  rw [h_translate]
  -- Now we have ∫ y, h (c • y)
  -- Scaling: ∫ y, h(c • y) dy = |(c ^ finrank ℝ (Fin d → ℝ))⁻¹| • ∫ y, h y
  rw [MeasureTheory.Measure.integral_comp_smul volume h c]
  -- Now we have |(c ^ finrank ℝ (Fin d → ℝ))⁻¹| • ∫ y, h y
  rw [h_finrank]
  -- Now we have |(c ^ d)⁻¹| • ∫ y, h y
  have h_abs : |(c ^ d)⁻¹| = (1 - lam) ^ d := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hc_pos d))]
    rw [hc_def]
    -- ((1 - lam)⁻¹ ^ d)⁻¹ = (1 - lam) ^ d
    rw [inv_pow, inv_inv]
  rw [h_abs]
  -- Now we have (1 - lam) ^ d • ∫ y, h y
  dsimp [h]
  -- Now we have (1 - lam) ^ d • ∫ y, (p y * f ((1 - lam) • y + lam • x) / ((1 - lam) ^ d))
  rw [integral_div]
  -- Now we have (1 - lam) ^ d • ((∫ y, p y * f ((1 - lam) • y + lam • x)) / ((1 - lam) ^ d))
  have h_pow_ne_zero : (1 - lam) ^ d ≠ 0 := pow_ne_zero d h_one_minus_lam_ne_zero
  field_simp [h_pow_ne_zero]


theorem AdversarialBco.Poly.qm_freedman_arith (n L lam eps l : ℝ) (hlam : 0 < lam) (heps : 0 < eps) (hn : 0 ≤ n)
    (hl : 0 ≤ l) (hlL : l ≤ L) :
    Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l) + 4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l ≤
      1 / lam * (Real.exp 2 * Real.sqrt (20 * n * L) + 2 * Real.exp 2 / 3 * L ^ 2 / eps) := by
  have hL : 0 ≤ L := le_trans hl hlL
  have hexp4 : Real.exp 4 = (Real.exp 2) ^ 2 := by
    calc
      Real.exp 4 = Real.exp ((2 : ℕ) * 2) := by norm_num
      _ = (Real.exp 2) ^ (2 : ℕ) := by rw [Real.exp_nat_mul 2 2]
      _ = (Real.exp 2) ^ 2 := by norm_num
  have hpos_div_pos : 0 < Real.exp 2 / lam := div_pos (Real.exp_pos 2) hlam
  have hpos_div_nonneg : 0 ≤ Real.exp 2 / lam := le_of_lt hpos_div_pos
  have hterm1 : Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l) ≤
      Real.exp 2 / lam * Real.sqrt (20 * n * L) := by
    calc
      Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l)
          = Real.sqrt (((Real.exp 2 / lam) ^ 2) * (20 * n * l)) := by
            rw [hexp4]
            ring_nf
      _ = Real.sqrt ((Real.exp 2 / lam) ^ 2) * Real.sqrt (20 * n * l) := by
            rw [Real.sqrt_mul (by positivity : 0 ≤ (Real.exp 2 / lam) ^ 2) (20 * n * l)]
      _ = |Real.exp 2 / lam| * Real.sqrt (20 * n * l) := by rw [Real.sqrt_sq_eq_abs]
      _ = (Real.exp 2 / lam) * Real.sqrt (20 * n * l) := by rw [abs_of_pos hpos_div_pos]
      _ ≤ (Real.exp 2 / lam) * Real.sqrt (20 * n * L) := by
            refine mul_le_mul_of_nonneg_left ?_ hpos_div_nonneg
            refine Real.sqrt_le_sqrt ?_
            nlinarith
  have hterm2 : 4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l ≤ (2 * Real.exp 2 / 3) * (L ^ 2) / (lam * eps) := by
    have h_mul : L * l ≤ L ^ 2 := by
      calc
        L * l ≤ L * L := mul_le_mul_of_nonneg_left hlL hL
        _ = L ^ 2 := by ring
    calc
      4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l = (2 * Real.exp 2 * L * l) / (3 * lam * eps) := by ring
      _ = (2 * Real.exp 2 / 3) * (L * l) / (lam * eps) := by ring
      _ ≤ (2 * Real.exp 2 / 3) * (L ^ 2) / (lam * eps) := by
            have hnum : (2 * Real.exp 2 / 3) * (L * l) ≤ (2 * Real.exp 2 / 3) * (L ^ 2) :=
              mul_le_mul_of_nonneg_left h_mul (by positivity : 0 ≤ 2 * Real.exp 2 / 3)
            exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ lam * eps)
  have hsum : Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l) +
      4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l ≤
      (Real.exp 2 / lam) * Real.sqrt (20 * n * L) + (2 * Real.exp 2 / 3) * (L ^ 2) / (lam * eps) := by
    nlinarith
  calc
    Real.sqrt (2 * (10 * Real.exp 4 * n / lam ^ 2) * l) + 4 * (Real.exp 2 * L / (2 * lam * eps)) / 3 * l
        ≤ (Real.exp 2 / lam) * Real.sqrt (20 * n * L) + (2 * Real.exp 2 / 3) * (L ^ 2) / (lam * eps) := hsum
    _ = 1 / lam * (Real.exp 2 * Real.sqrt (20 * n * L) + 2 * Real.exp 2 / 3 * L ^ 2 / eps) := by ring

theorem AdversarialBco.Poly.qm_compensator_arith (d n : ℕ) (lam eps δ c0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hlam : 0 < lam) (heps : 0 < eps) (hepsn : 1 / eps ≤ Real.sqrt n) (hδ : 0 < δ)
    (hδc : δ ≤ c0 / ((d : ℝ) * n) ^ 3) (hc0 : c0 ≤ Real.exp (-14)) :
    n * (Real.exp 2 / lam * (72 * d / eps) * Real.sqrt (3 * δ / (7 * n))) ≤ 1 / lam := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.one_pos.trans_le hd)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.one_pos.trans_le hn)
  have hdnpos : (0 : ℝ) < (d : ℝ) * (n : ℝ) := mul_pos hdpos hnpos
  have hdn_ge_one : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h_exp_sq : (Real.exp 2) ^ 2 = Real.exp 4 := by
    calc
      (Real.exp 2) ^ 2 = Real.exp 2 * Real.exp 2 := by ring
      _ = Real.exp (2 + 2) := by rw [← Real.exp_add]
      _ = Real.exp 4 := by norm_num
  have h_exp_prod : Real.exp 4 * Real.exp (-14) = Real.exp (-10) := by
    calc
      Real.exp 4 * Real.exp (-14) = Real.exp (4 + (-14)) := by rw [← Real.exp_add]
      _ = Real.exp (-10) := by norm_num
  have h_final : Real.exp (-10) * (72 ^ 2) * 3 / 7 ≤ 1 := by
    have h_exp10_gt : (22026 : ℝ) < Real.exp 10 := by
      have h_exp1_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h_exp10_eq : Real.exp 10 = (Real.exp 1) ^ 10 := by
        rw [← Real.exp_nat_mul 1 10]
        norm_num
      rw [h_exp10_eq]
      have h_pow : (2.7182818283 : ℝ) ^ 10 < (Real.exp 1) ^ 10 := by
        gcongr
      have h_approx : (22026 : ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
      linarith
    have h_exp_neg10 : Real.exp (-10) = (Real.exp 10)⁻¹ := Real.exp_neg 10
    rw [h_exp_neg10]
    have hpos_exp10 : 0 < Real.exp 10 := Real.exp_pos 10
    have h_num : (72 : ℝ) ^ 2 * (3 : ℝ) / (7 : ℝ) = (15552 : ℝ) / 7 := by norm_num
    have h_ineq : (72 : ℝ) ^ 2 * (3 : ℝ) / (7 : ℝ) ≤ Real.exp 10 := by
      rw [h_num]
      have h_lt : (15552 : ℝ) / 7 < (22026 : ℝ) := by norm_num
      linarith
    field_simp [hpos_exp10.ne.symm]
    nlinarith
  have h_main : (n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * Real.sqrt (3 * δ / (7 * (n : ℝ))) ≤ 1 := by
    set S := Real.sqrt (n : ℝ) with hS
    set R := Real.sqrt (3 * δ / (7 * (n : ℝ))) with hR
    have hS_sq : S ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hR_sq : R ^ 2 = 3 * δ / (7 * (n : ℝ)) := Real.sq_sqrt (by positivity)
    have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _
    have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
    have h_bound1 : (n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * R ≤ 72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R := by
      calc
        (n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * R = 72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * ((1 / eps) * R) := by ring
        _ ≤ 72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * (S * R) := by
          gcongr
        _ = 72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R := by ring
    have h_nonneg_orig : 0 ≤ (n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * R := by positivity
    have h_nonneg_bound1 : 0 ≤ 72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R := by positivity
    have h_sq_bound1 : ((n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * R) ^ 2 ≤ (72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R) ^ 2 := by
      gcongr
    have h_sq_eq : (72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R) ^ 2 = Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 * δ / 7 := by
      calc
        (72 * Real.exp 2 * (d : ℝ) * (n : ℝ) * S * R) ^ 2
            = (72 ^ 2) * ((Real.exp 2) ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * (S ^ 2) * (R ^ 2) := by ring
        _ = (72 ^ 2) * Real.exp 4 * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * (n : ℝ) * (3 * δ / (7 * (n : ℝ))) := by
          rw [hS_sq, hR_sq, h_exp_sq]
        _ = Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 * δ / 7 := by
          field_simp
    have hδ_bound : δ ≤ Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3) := by
      apply le_trans hδc
      gcongr
    have h_sq_bound2 : Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 * δ / 7 ≤ 1 := by
      calc
        Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 * δ / 7
            = (Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 / 7) * δ := by ring
        _ ≤ (Real.exp 4 * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 / 7) * (Real.exp (-14) / (((d : ℝ) * (n : ℝ)) ^ 3)) := by
          gcongr
        _ = Real.exp 4 * Real.exp (-14) * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 / (7 * (((d : ℝ) * (n : ℝ)) ^ 3)) := by ring
        _ = Real.exp (-10) * (72 ^ 2) * ((d : ℝ) ^ 2) * ((n : ℝ) ^ 2) * 3 / (7 * ((d : ℝ) ^ 3 * (n : ℝ) ^ 3)) := by
          rw [h_exp_prod]
          ring
        _ = Real.exp (-10) * (72 ^ 2) * 3 / (7 * ((d : ℝ) * (n : ℝ))) := by
          field_simp
        _ = (Real.exp (-10) * (72 ^ 2) * 3 / 7) * (1 / ((d : ℝ) * (n : ℝ))) := by ring
        _ ≤ Real.exp (-10) * (72 ^ 2) * 3 / 7 := by
          have h_factor_nonneg : 0 ≤ Real.exp (-10) * (72 ^ 2) * 3 / 7 := by positivity
          have h_factor_le_one : 1 / ((d : ℝ) * (n : ℝ)) ≤ 1 :=
            (div_le_one hdnpos).mpr hdn_ge_one
          nlinarith
        _ ≤ 1 := h_final
    have h_sq : ((n : ℝ) * Real.exp 2 * (72 * (d : ℝ) / eps) * R) ^ 2 ≤ 1 := by
      linarith
    exact ((sq_le_one_iff₀ h_nonneg_orig).mp h_sq)
  -- Now multiply back by lam
  calc
    n * (Real.exp 2 / lam * (72 * d / eps) * Real.sqrt (3 * δ / (7 * n)))
        = (n * Real.exp 2 * (72 * d / eps) * Real.sqrt (3 * δ / (7 * n))) * (1 / lam) := by ring
    _ ≤ 1 * (1 / lam) := by
      gcongr
    _ = 1 / lam := by ring

theorem AdversarialBco.Poly.ssharp_range_arith (d L a eps y w ell : ℝ) (hd : 1 ≤ d) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (heps : 0 < eps) (hy : |y| ≤ L / (2 * eps)) (hw : 0 ≤ w) (hwell : w ≤ 8 * d / 3 * ell) (hell : ell ≤ L) :
    2 * Real.exp 2 * a * |y| * (2 * (4 * w + 1)) ≤ 24 * Real.exp 2 * a * d * L ^ 2 / eps ∧
      ∀ l : ℝ, 0 ≤ l → l ≤ L →
        4 * (24 * Real.exp 2 * a * d * L ^ 2 / eps) / 3 * l ≤ 32 * Real.exp 2 * a * d * L ^ 3 / eps := by
  have hexp_pos : 0 < Real.exp 2 := Real.exp_pos 2
  have hexp_nonneg : 0 ≤ Real.exp 2 := hexp_pos.le
  have hd_nonneg : 0 ≤ d := by linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have heps_nonneg : 0 ≤ eps := heps.le
  have hy_nonneg : 0 ≤ |y| := abs_nonneg _
  -- bound 4*w + 1 ≤ (35/3)*d*L
  have hw_bound : 4 * w + 1 ≤ (35/3 : ℝ) * d * L := by
    have hell_nonneg : 0 ≤ ell := by
      have hpos : 0 < 8 * d / 3 := by nlinarith
      nlinarith
    have h1 : 4 * w + 1 ≤ 4 * ((8 * d / 3) * ell) + 1 := by nlinarith
    have h2 : 4 * ((8 * d / 3) * ell) + 1 ≤ 4 * ((8 * d / 3) * L) + 1 := by nlinarith
    have h3 : 4 * ((8 * d / 3) * L) + 1 = (32/3 : ℝ) * d * L + 1 := by ring
    have h4 : (32/3 : ℝ) * d * L + 1 ≤ (35/3 : ℝ) * d * L := by
      have hdL : 1 ≤ d * L := by nlinarith
      nlinarith
    nlinarith
  have hA : 2 * Real.exp 2 * a * |y| * (2 * (4 * w + 1)) ≤ 24 * Real.exp 2 * a * d * L ^ 2 / eps := by
    have hcoeff1 : 0 ≤ 2 * Real.exp 2 * a * (2 * (4 * w + 1)) := by positivity
    have hcoeff2 : 0 ≤ 2 * Real.exp 2 * a * (L / (2 * eps)) := by positivity
    have hcoeff3 : 0 ≤ 2 * Real.exp 2 * a * (L / (2 * eps)) * 2 := by positivity
    calc
      2 * Real.exp 2 * a * |y| * (2 * (4 * w + 1))
          = ((2 * Real.exp 2 * a) * (2 * (4 * w + 1))) * |y| := by ring
      _ ≤ ((2 * Real.exp 2 * a) * (2 * (4 * w + 1))) * (L / (2 * eps)) :=
        mul_le_mul_of_nonneg_left hy hcoeff1
      _ = (2 * Real.exp 2 * a) * (L / (2 * eps)) * (2 * (4 * w + 1)) := by ring
      _ = (2 * Real.exp 2 * a * (L / (2 * eps)) * 2) * (4 * w + 1) := by ring
      _ ≤ (2 * Real.exp 2 * a * (L / (2 * eps)) * 2) * ((35/3 : ℝ) * d * L) :=
        mul_le_mul_of_nonneg_left hw_bound hcoeff3
      _ = 2 * Real.exp 2 * a * (L / (2 * eps)) * (2 * ((35/3 : ℝ) * d * L)) := by ring
      _ = (70/3 : ℝ) * Real.exp 2 * a * d * L ^ 2 / eps := by ring
      _ ≤ 24 * Real.exp 2 * a * d * L ^ 2 / eps := by
        have hcoeff : (70/3 : ℝ) ≤ 24 := by norm_num
        have hpos' : 0 ≤ Real.exp 2 * a * d * L ^ 2 := by positivity
        have htemp : (70/3 : ℝ) * (Real.exp 2 * a * d * L ^ 2) ≤ 24 * (Real.exp 2 * a * d * L ^ 2) := by
          nlinarith
        calc
          (70/3 : ℝ) * Real.exp 2 * a * d * L ^ 2 / eps
              = ((70/3 : ℝ) * (Real.exp 2 * a * d * L ^ 2)) / eps := by ring
          _ ≤ (24 * (Real.exp 2 * a * d * L ^ 2)) / eps :=
            (div_le_div_of_nonneg_right htemp heps.le)
          _ = 24 * Real.exp 2 * a * d * L ^ 2 / eps := by ring
  have hB : ∀ l : ℝ, 0 ≤ l → l ≤ L →
      4 * (24 * Real.exp 2 * a * d * L ^ 2 / eps) / 3 * l ≤ 32 * Real.exp 2 * a * d * L ^ 3 / eps := by
    intro l hl_nonneg hl_le_L
    have hcoeff_nonneg : 0 ≤ 32 * Real.exp 2 * a * d * L ^ 2 / eps := by positivity
    calc
      4 * (24 * Real.exp 2 * a * d * L ^ 2 / eps) / 3 * l
          = (32 * Real.exp 2 * a * d * L ^ 2 / eps) * l := by ring
      _ ≤ (32 * Real.exp 2 * a * d * L ^ 2 / eps) * L :=
        mul_le_mul_of_nonneg_left hl_le_L hcoeff_nonneg
      _ = 32 * Real.exp 2 * a * d * L ^ 3 / eps := by ring
  exact And.intro hA hB

set_option maxHeartbeats 400000 in
theorem AdversarialBco.Poly.ssharp_compensator_arith (d n : ℕ) (a eps δ c0 : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (ha : 0 ≤ a) (heps : 0 < eps) (hepsn : 1 / eps ≤ Real.sqrt n) (hδ : 0 < δ)
    (hδc : δ ≤ c0 / ((d : ℝ) * n) ^ 3) (hc0 : c0 ≤ 7 / (3 * (8352 * Real.exp 2) ^ 2)) :
    n * (4 * Real.exp 2 * a * (72 * d / eps) * (29 * d) * Real.sqrt (3 * δ / (7 * n))) ≤ a * Real.sqrt (d * n) := by
  -- Casts
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by linarith
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hEpos : 0 < Real.exp 2 := Real.exp_pos 2
  have hE_nonneg : 0 ≤ Real.exp 2 := by linarith
  -- Nonnegativity of both sides
  have hleft_nonneg : 0 ≤ n * (4 * Real.exp 2 * a * (72 * (d : ℝ) / eps) * (29 * (d : ℝ)) * Real.sqrt (3 * δ / (7 * (n : ℝ)))) := by
    positivity
  have hright_nonneg : 0 ≤ a * Real.sqrt ((d : ℝ) * (n : ℝ)) := by
    positivity
  -- Square both sides: prove x^2 ≤ y^2 to get x ≤ y
  have h_sq_goal : (n * (4 * Real.exp 2 * a * (72 * (d : ℝ) / eps) * (29 * (d : ℝ)) * Real.sqrt (3 * δ / (7 * (n : ℝ))))) ^ 2 ≤
      (a * Real.sqrt ((d : ℝ) * (n : ℝ))) ^ 2 := by
    -- Abbreviations
    set E := Real.exp 2 with hE
    set S := Real.sqrt (n : ℝ) with hS
    set R := Real.sqrt (3 * δ / (7 * (n : ℝ))) with hR
    have hS_sq : S ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
    have hR_sq : R ^ 2 = 3 * δ / (7 * (n : ℝ)) := Real.sq_sqrt (by positivity : 0 ≤ 3 * δ / (7 * (n : ℝ)))
    have hS_nonneg : 0 ≤ S := Real.sqrt_nonneg _
    have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
    -- Simplify RHS^2
    have hRHS_sq : (a * Real.sqrt ((d : ℝ) * (n : ℝ))) ^ 2 = a ^ 2 * (d : ℝ) * (n : ℝ) := by
      calc
        (a * Real.sqrt ((d : ℝ) * (n : ℝ))) ^ 2 = a ^ 2 * ((Real.sqrt ((d : ℝ) * (n : ℝ))) ^ 2) := by ring
        _ = a ^ 2 * ((d : ℝ) * (n : ℝ)) := by rw [Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ) * (n : ℝ))]
        _ = a ^ 2 * (d : ℝ) * (n : ℝ) := by ring
    -- Simplify LHS^2
    have hLHS_sq : (n * (4 * E * a * (72 * (d : ℝ) / eps) * (29 * (d : ℝ)) * R)) ^ 2 =
        (8352 : ℝ)^2 * E^2 * a^2 * (d : ℝ)^4 * (n : ℝ) * (3 * δ) / (7 * eps^2) := by
      calc
        (n * (4 * E * a * (72 * (d : ℝ) / eps) * (29 * (d : ℝ)) * R)) ^ 2 =
            ((8352 : ℝ) * E * a * (d : ℝ)^2 * ((n : ℝ) / eps) * R) ^ 2 := by ring
        _ = (8352 : ℝ)^2 * E^2 * a^2 * (d : ℝ)^4 * ((n : ℝ)^2 / eps^2) * R^2 := by ring
        _ = (8352 : ℝ)^2 * E^2 * a^2 * (d : ℝ)^4 * ((n : ℝ)^2 / eps^2) * (3 * δ / (7 * (n : ℝ))) := by rw [hR_sq]
        _ = (8352 : ℝ)^2 * E^2 * a^2 * (d : ℝ)^4 * (n : ℝ) * (3 * δ) / (7 * eps^2) := by
          field_simp [ne_of_gt hd_pos, ne_of_gt hn_pos]
    rw [hLHS_sq, hRHS_sq]
    -- Now we need: K^2 * E^2 * a^2 * d^4 * n * 3δ / (7 * eps^2) ≤ a^2 * d * n
    -- Handle a = 0 case
    by_cases ha_zero : a = 0
    · simp [ha_zero]
    · have ha_pos : 0 < a := by
        by_contra! h
        exact ha_zero (le_antisymm h ha)
      have ha_sq_pos : 0 < a ^ 2 := by positivity
      -- From hepsn: 1/eps ≤ S, derive 1 ≤ n * eps^2
      have h_eps_sq_le_n : 1 ≤ (n : ℝ) * eps ^ 2 := by
        have h_mul : 1 ≤ eps * S := by
          calc
            1 = (1 / eps) * eps := by field_simp [ne_of_gt heps]
            _ ≤ S * eps := mul_le_mul_of_nonneg_right hepsn (by positivity)
            _ = eps * S := mul_comm _ _
        have h_sq : (1 : ℝ) ≤ (eps * S)^2 := by
          nlinarith
        have h_expand : (eps * S)^2 = eps ^ 2 * S ^ 2 := by ring
        rw [h_expand] at h_sq
        rw [hS_sq] at h_sq
        rw [mul_comm] at h_sq
        exact h_sq
      -- Clear denominator
      have h_denom_pos : 0 < 7 * eps ^ 2 := by positivity
      rw [div_le_iff₀ h_denom_pos]
      -- Goal: K^2 * E^2 * a^2 * d^4 * n * 3δ ≤ (a^2 * d * n) * (7 * eps^2)
      -- Cancel a^2 * n (both > 0)
      -- We need: K^2 * E^2 * d^3 * 3δ ≤ 7 * eps^2
      -- Using the chain of inequalities from the hint
      have h_main : (8352 : ℝ)^2 * E^2 * (d : ℝ)^3 * (3 * δ) ≤ 7 * eps ^ 2 := by
        -- Step 1: δ ≤ c0 / (d*n)^3
        have h_step1 : (8352 : ℝ)^2 * E^2 * (d : ℝ)^3 * (3 * δ) ≤
                     (8352 : ℝ)^2 * E^2 * (d : ℝ)^3 * (3 * (c0 / ((d : ℝ) * (n : ℝ)) ^ 3)) := by
          have h_coeff_nonneg : 0 ≤ (8352 : ℝ)^2 * E^2 * (d : ℝ)^3 := by positivity
          apply mul_le_mul_of_nonneg_left ?_ h_coeff_nonneg
          -- Goal: 3 * δ ≤ 3 * (c0 / ((d : ℝ) * (n : ℝ)) ^ 3)
          have h3pos : 0 ≤ (3 : ℝ) := by norm_num
          apply mul_le_mul_of_nonneg_left hδc h3pos
        -- Step 2: Simplify the RHS: d^3 * (c0 / (d*n)^3) = c0 / n^3
        have h_step2 : (8352 : ℝ)^2 * E^2 * (d : ℝ)^3 * (3 * (c0 / ((d : ℝ) * (n : ℝ)) ^ 3)) =
                      (8352 : ℝ)^2 * E^2 * 3 * c0 / (n : ℝ)^3 := by
          field_simp [ne_of_gt hd_pos, ne_of_gt hn_pos]
        rw [h_step2] at h_step1
        -- Step 3: Using hc0: c0 ≤ 7 / (3 * K^2 * E^2)
        have h_step3 : (8352 : ℝ)^2 * E^2 * 3 * c0 / (n : ℝ)^3 ≤ 7 / (n : ℝ)^3 := by
          have hn_cube_pos : 0 < (n : ℝ)^3 := by positivity
          have h_temp : (8352 : ℝ)^2 * E^2 * 3 * c0 ≤ 7 := by
            -- From hc0: c0 ≤ 7 / (3 * (8352 * E)^2)
            -- Rewrite: 3 * (8352 * E)^2 = 8352^2 * E^2 * 3
            have h_eq : 3 * ((8352 : ℝ) * E)^2 = (8352 : ℝ)^2 * E^2 * 3 := by ring
            rw [h_eq] at hc0
            -- hc0: c0 ≤ 7 / (8352^2 * E^2 * 3)
            have hpos : 0 < (8352 : ℝ)^2 * E^2 * 3 := by positivity
            -- (le_div_iff₀ hpos).mp hc0 : c0 * (8352^2 * E^2 * 3) ≤ 7
            have htemp2 := (le_div_iff₀ hpos).mp hc0
            linarith
          have h_temp2 : ((8352 : ℝ)^2 * E^2 * 3 * c0) * (n : ℝ)^3 ≤ 7 * (n : ℝ)^3 := by
            nlinarith
          exact (div_le_div_iff₀ hn_cube_pos hn_cube_pos).mpr h_temp2
        -- Step 4: Using h_eps_sq_le_n: 1 ≤ n * eps^2, derive 7/n^3 ≤ 7*eps^2
        have h_step4 : 7 / (n : ℝ)^3 ≤ 7 * eps ^ 2 := by
          have hn_cube_pos : 0 < (n : ℝ)^3 := by positivity
          -- Need: 7/n^3 ≤ 7*eps^2, i.e., 1/n^3 ≤ eps^2, i.e., 1 ≤ n^3 * eps^2
          -- From h_eps_sq_le_n: 1 ≤ n * eps^2, and n ≥ 1 so n^3 ≥ n
          have hn_cube_ge_n : (n : ℝ) ≤ (n : ℝ)^3 := by
            have h_one_le_n_sq : 1 ≤ (n : ℝ)^2 := by
              nlinarith
            nlinarith
          have h_eps_sq_le_n_cube : 1 ≤ (n : ℝ)^3 * eps ^ 2 := by
            nlinarith
          apply (div_le_iff₀ hn_cube_pos).mpr
          nlinarith
        -- Combine: h_step1, h_step3, h_step4
        linarith
      -- Now we have: K^2 * E^2 * d^3 * 3δ ≤ 7 * eps^2
      -- Multiply both sides by a^2 * n (positive) to get the original goal
      have hpos_an : 0 ≤ a ^ 2 * (n : ℝ) := by positivity
      nlinarith
  -- Now use the squared inequality to get the original: x^2 ≤ y^2 and x,y ≥ 0 → x ≤ y
  nlinarith

theorem AdversarialBco.Poly.ssharp_sum_arith (d n L CW a eps : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hCW : 0 ≤ CW) (ha : 0 ≤ a) (heps : 0 < eps) :
    Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + 32 * Real.exp 2 * a * d * L ^ 3 / eps +
        a * Real.sqrt (d * n) ≤
      max (Real.sqrt (22 * CW) + 1) (32 * Real.exp 2) * a *
        (L ^ (3 / 2 : ℝ) * Real.sqrt (d * n) + d * L ^ 3 / eps) := by
  set P := L ^ (3 / 2 : ℝ) with hPdef
  set C := max (Real.sqrt (22 * CW) + 1) (32 * Real.exp 2) with hCdef
  have hC_le1 : Real.sqrt (22 * CW) + 1 ≤ C := by
    rw [hCdef]
    exact le_max_left _ _
  have hC_le2 : 32 * Real.exp 2 ≤ C := by
    rw [hCdef]
    exact le_max_right _ _
  have hL_nonneg : 0 ≤ L := by linarith
  have hd_nonneg : 0 ≤ d := by linarith
  have hn_nonneg : 0 ≤ n := by linarith
  have hP_nonneg : 0 ≤ P := by
    rw [hPdef]
    exact Real.rpow_nonneg hL_nonneg _
  have hP_ge_one : 1 ≤ P := by
    rw [hPdef]
    exact Real.one_le_rpow hL (by norm_num : (0 : ℝ) ≤ 3/2)
  have hP_sq : P ^ 2 = L ^ 3 := by
    rw [hPdef]
    calc
      (L ^ (3/2 : ℝ)) ^ 2 = (L ^ (3/2 : ℝ)) ^ (2 : ℝ) := by norm_num
      _ = L ^ ((3/2 : ℝ) * (2 : ℝ)) := by rw [← Real.rpow_mul hL_nonneg (3/2 : ℝ) (2 : ℝ)]
      _ = L ^ (3 : ℝ) := by ring
      _ = L ^ 3 := by norm_num
  have h_sqrt_L3 : Real.sqrt (L ^ 3) = P := by
    rw [hPdef]
    calc
      Real.sqrt (L ^ 3) = (L ^ 3) ^ (1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (L ^ (3 : ℝ)) ^ (1/2 : ℝ) := by norm_num
      _ = L ^ ((3 : ℝ) * (1/2 : ℝ)) := by rw [← Real.rpow_mul hL_nonneg (3 : ℝ) (1/2 : ℝ)]
      _ = L ^ (3/2 : ℝ) := by ring
  have h_sqrt_dn_nonneg : 0 ≤ Real.sqrt (d * n) := Real.sqrt_nonneg _
  have h_22CW_nonneg : 0 ≤ 22 * CW := by nlinarith
  have h_dn_nonneg : 0 ≤ d * n := by nlinarith
  have h_term1_sq : 2 * CW * d * (1 + 10 * L ^ 2 * n) * L ≤ 22 * CW * d * n * L ^ 3 := by
    have hL_sq_n_ge_one : 1 ≤ L ^ 2 * n := by
      have hL_sq_ge_one : 1 ≤ L ^ 2 := by
        nlinarith
      nlinarith
    by_cases hCWzero : CW = 0
    · subst hCWzero; simp
    · have hCWpos : 0 < CW := by
        by_contra! h
        apply hCWzero
        linarith
      have h_factor : 1 + 10 * L ^ 2 * n ≤ 11 * L ^ 2 * n := by
        nlinarith
      have h_nonneg : 0 ≤ 2 * CW * d * L := by positivity
      nlinarith
  have h_term1_sq' : 2 * CW * d * (1 + 10 * L ^ 2 * n) * L ≤ (Real.sqrt (22 * CW) * P * Real.sqrt (d * n)) ^ 2 := by
    calc
      2 * CW * d * (1 + 10 * L ^ 2 * n) * L ≤ 22 * CW * d * n * L ^ 3 := h_term1_sq
      _ = (22 * CW) * (d * n) * (L ^ 3) := by ring
      _ = ((Real.sqrt (22 * CW)) ^ 2) * ((Real.sqrt (d * n)) ^ 2) * (P ^ 2) := by
        rw [Real.sq_sqrt h_22CW_nonneg, Real.sq_sqrt h_dn_nonneg, hP_sq]
      _ = ((Real.sqrt (22 * CW)) ^ 2) * (P ^ 2) * ((Real.sqrt (d * n)) ^ 2) := by ring
      _ = (Real.sqrt (22 * CW) * P * Real.sqrt (d * n)) ^ 2 := by ring
  have h_term1 : Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) ≤ Real.sqrt (22 * CW) * P * Real.sqrt (d * n) := by
    have h_nonneg_target : 0 ≤ Real.sqrt (22 * CW) * P * Real.sqrt (d * n) := by
      positivity
    rw [Real.sqrt_le_iff]
    exact ⟨h_nonneg_target, h_term1_sq'⟩
  have h_sqrt_term3 : Real.sqrt (d * n) ≤ P * Real.sqrt (d * n) := by
    calc
      Real.sqrt (d * n) = 1 * Real.sqrt (d * n) := by ring
      _ ≤ P * Real.sqrt (d * n) := mul_le_mul_of_nonneg_right hP_ge_one h_sqrt_dn_nonneg
  have h_term13 : Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + a * Real.sqrt (d * n) ≤
      (Real.sqrt (22 * CW) + 1) * a * P * Real.sqrt (d * n) := by
    have h1' : Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a ≤ (Real.sqrt (22 * CW) * P * Real.sqrt (d * n)) * a :=
      mul_le_mul_of_nonneg_right h_term1 ha
    have h3' : a * Real.sqrt (d * n) ≤ a * (P * Real.sqrt (d * n)) :=
      mul_le_mul_of_nonneg_left h_sqrt_term3 ha
    have hsum := add_le_add h1' h3'
    calc
      Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + a * Real.sqrt (d * n) ≤
          (Real.sqrt (22 * CW) * P * Real.sqrt (d * n)) * a + a * (P * Real.sqrt (d * n)) := hsum
      _ = a * P * Real.sqrt (d * n) * (Real.sqrt (22 * CW) + 1) := by ring
      _ = (Real.sqrt (22 * CW) + 1) * a * P * Real.sqrt (d * n) := by ring
  have h_one_le_C : 1 ≤ C := by
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (22 * CW) := Real.sqrt_nonneg _
    linarith
  have h_term13' : Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + a * Real.sqrt (d * n) ≤
      C * a * P * Real.sqrt (d * n) := by
    have h_nonneg : 0 ≤ a * P * Real.sqrt (d * n) := by positivity
    calc
      Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + a * Real.sqrt (d * n) ≤
          (Real.sqrt (22 * CW) + 1) * a * P * Real.sqrt (d * n) := h_term13
      _ ≤ C * (a * P * Real.sqrt (d * n)) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hC_le1 h_nonneg
      _ = C * a * P * Real.sqrt (d * n) := by ring
  have h_term2 : 32 * Real.exp 2 * a * d * L ^ 3 / eps ≤ C * a * d * L ^ 3 / eps := by
    have h_eps_nonneg : 0 ≤ eps := le_of_lt heps
    have hprod : 32 * Real.exp 2 * a * d * L ^ 3 ≤ C * a * d * L ^ 3 := by
      have h_nonneg : 0 ≤ a * d * L ^ 3 := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hC_le2 h_nonneg
    exact (div_le_div_of_nonneg_right hprod h_eps_nonneg)
  have h_sum_raw := add_le_add h_term13' h_term2
  have h_sum : Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + 32 * Real.exp 2 * a * d * L ^ 3 / eps +
      a * Real.sqrt (d * n) ≤ C * a * P * Real.sqrt (d * n) + C * a * d * L ^ 3 / eps := by
    calc
      Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + 32 * Real.exp 2 * a * d * L ^ 3 / eps +
          a * Real.sqrt (d * n) = (Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + a * Real.sqrt (d * n)) +
          32 * Real.exp 2 * a * d * L ^ 3 / eps := by abel
      _ ≤ C * a * P * Real.sqrt (d * n) + C * a * d * L ^ 3 / eps := h_sum_raw
  calc
    Real.sqrt (2 * CW * d * (1 + 10 * L ^ 2 * n) * L) * a + 32 * Real.exp 2 * a * d * L ^ 3 / eps +
        a * Real.sqrt (d * n) ≤ C * a * P * Real.sqrt (d * n) + C * a * d * L ^ 3 / eps := h_sum
    _ = C * a * (P * Real.sqrt (d * n) + d * L ^ 3 / eps) := by ring
    _ = max (Real.sqrt (22 * CW) + 1) (32 * Real.exp 2) * a *
        (L ^ (3 / 2 : ℝ) * Real.sqrt (d * n) + d * L ^ 3 / eps) := by rw [hCdef, hPdef]

theorem AdversarialBco.Poly.ssharp_moment_arith (d : ℝ) (hd : 1 ≤ d) :
    d * (d + 2) * (d + 4) * (d + 6) ≤ (d + 6) ^ 4 ∧ 4 * (d + 6) + 1 ≤ 29 * d := by
  have hd0 : 0 ≤ d := by linarith
  have hd2 : 0 ≤ d + 2 := by linarith
  have hd4 : 0 ≤ d + 4 := by linarith
  have hd6 : 0 ≤ d + 6 := by linarith
  have hle1 : d ≤ d + 6 := by linarith
  have hle2 : d + 2 ≤ d + 6 := by linarith
  have hle3 : d + 4 ≤ d + 6 := by linarith
  have hprod1 : d * (d + 2) ≤ (d + 6) * (d + 6) := by
    exact mul_le_mul hle1 hle2 hd2 hd6
  have hprod2 : d * (d + 2) * (d + 4) ≤ (d + 6) * (d + 6) * (d + 6) := by
    nlinarith
  have hprod3 : d * (d + 2) * (d + 4) * (d + 6) ≤ (d + 6) * (d + 6) * (d + 6) * (d + 6) := by
    nlinarith
  constructor
  · -- d * (d + 2) * (d + 4) * (d + 6) ≤ (d + 6) ^ 4
    simpa [pow_succ, pow_one] using hprod3
  · -- 4 * (d + 6) + 1 ≤ 29 * d
    nlinarith

theorem AdversarialBco.Poly.sum_decomp (t : ℕ) (D z b : ℕ → ℝ) (h : ∀ s, s < t → D s = z s - b s) :
    |∑ s ∈ Finset.range t, D s| ≤ |∑ s ∈ Finset.range t, z s| + ∑ s ∈ Finset.range t, |b s| := by
  have hsum : (∑ s ∈ Finset.range t, D s) = (∑ s ∈ Finset.range t, z s) - (∑ s ∈ Finset.range t, b s) := by
    calc
      (∑ s ∈ Finset.range t, D s) = (∑ s ∈ Finset.range t, (z s - b s)) := by
        refine Finset.sum_congr rfl (λ s hs => ?_)
        rw [h s (Finset.mem_range.1 hs)]
      _ = (∑ s ∈ Finset.range t, z s) - (∑ s ∈ Finset.range t, b s) := Finset.sum_sub_distrib z b
  rw [hsum]
  calc
    |(∑ s ∈ Finset.range t, z s) - (∑ s ∈ Finset.range t, b s)| ≤ |∑ s ∈ Finset.range t, z s| + |∑ s ∈ Finset.range t, b s| :=
      abs_sub _ _
    _ ≤ |∑ s ∈ Finset.range t, z s| + ∑ s ∈ Finset.range t, |b s| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs b (Finset.range t)

/-! ## The interface statements -/

namespace AdversarialBco.Poly

theorem truncCentredMean : TruncCentredMean.{u} := fun μ _ m hm G X hG hX =>
  trunc_centred_mean μ m hm G X hG hX

theorem truncCentredBound : TruncCentredBound.{u} := fun μ _ m hm G X B hB hXB =>
  trunc_centred_bound μ m hm G X B hB hXB

theorem truncCentredVar : TruncCentredVar.{u} := fun μ _ m hm G X hG hX =>
  trunc_centred_var μ m hm G X hG hX

theorem truncDecomp : TruncDecomp.{u} := fun μ _ m hm G X hG hX =>
  trunc_decomp μ m hm G X hG hX

theorem condExpCauchySchwarz : CondExpCauchySchwarz.{u} := fun μ _ m hm A X hA hX =>
  condExp_cauchy_schwarz μ m hm A X hA hX

theorem ratioAtMean : RatioAtMean := ratio_at_mean

theorem estimatorSize : EstimatorSize := estimator_size

theorem estimatorUnbiased : EstimatorUnbiased := estimator_unbiased

theorem qmFreedmanArith : QMFreedmanArith := qm_freedman_arith

theorem qmCompensatorArith : QMCompensatorArith := qm_compensator_arith

theorem sSharpRangeArith : SSharpRangeArith := ssharp_range_arith

theorem sSharpCompensatorArith : SSharpCompensatorArith := ssharp_compensator_arith

theorem sSharpSumArith : SSharpSumArith := ssharp_sum_arith

theorem sSharpMomentArith : SSharpMomentArith := ssharp_moment_arith

theorem sumDecomp : SumDecomp := sum_decomp

end AdversarialBco.Poly
