/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvVSum
public import AdversarialBco.Poly.Df2EvMeas
public import AdversarialBco.Poly.Df2Layer2Proof

@[expose] public section

/-!
# The budget of Y: the frozen functions and one round

With `B = 4 L²/ε²` (`yB`) and, for the rounds `u < m`, `Z_u = 1{π(X_u) ≤ √L} min(Y_u², B)`:

* the frozen functions of the parameter, the state and the draw that the process reads (`pOf`, `jOf`, `aOf`, `fOf`,
  `zOf`), and their measurability from (L1) (`Df2EpochMeas`);
* one round: `4 P² + 8 v²/ε² ≤ 8 + 10 v²/ε²` for `P = pip(X_u)`, `v = P - 1`, `ε ≤ 1/2` (`round_arith`), the bounds on
  the event Pi (`jOf_bounds`), and the integral of the bound of a round against the law of the draw
  (`integral_fOf_le`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly

open Layer2 ApMeas

namespace EvGY

section Frozen

variable {d : ℕ} (n : ℕ) (δ : ℝ) {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)

/-- `pip(X)` at a frozen point `(q, st, z)`. -/
noncomputable def pOf (x : Θ × Df2St d × (Fin d → ℝ)) : ℝ :=
  df2Pip (df2oPar d n δ) (Kθ x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2))

/-- The indicator of Pi at a frozen point. -/
noncomputable def jOf (x : Θ × Df2St d × (Fin d → ℝ)) : ℝ :=
  if gauge (Kθ x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) ≤ Real.sqrt (df2oPar d n δ).Le then 1 else 0

/-- The loss at the play, at a frozen point, read through the extension. -/
noncomputable def aOf (u : ℕ) (x : Θ × Df2St d × (Fin d → ℝ)) : ℝ :=
  (df2Ext (df2oPar d n δ) (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) -
    2 * (pOf n δ Kθ x - 1) / (df2oPar d n δ).eps) / pOf n δ Kθ x

variable (d) in
/-- The truncation level `B = 4 L²/ε²`. -/
noncomputable def yB : ℝ := 4 * (df2oPar d n δ).Le ^ 2 / (df2oPar d n δ).eps ^ 2

/-- The bound of the conditional mean of a round at a frozen point `((q, st), z)`:
`8 + (10/ε²) 1{π(X) ≤ √L} v(X)²`. -/
noncomputable def fOf (y : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  8 + 10 / (df2oPar d n δ).eps ^ 2 * (jOf n δ Kθ (y.1.1, y.1.2, y.2) * (pOf n δ Kθ (y.1.1, y.1.2, y.2) - 1) ^ 2)

omit [MeasurableSpace Θ] in
theorem one_le_pOf (x : Θ × Df2St d × (Fin d → ℝ)) : 1 ≤ pOf n δ Kθ x := le_max_left _ _

omit [MeasurableSpace Θ] in
theorem jOf_mem (x : Θ × Df2St d × (Fin d → ℝ)) : jOf n δ Kθ x = 0 ∨ jOf n δ Kθ x = 1 := by
  unfold jOf; split_ifs <;> simp

omit [MeasurableSpace Θ] in
theorem aOf_eq (u : ℕ) (x : Θ × Df2St d × (Fin d → ℝ)) :
    aOf n δ Kθ gθ u x =
      gθ u x.1 ((pOf n δ Kθ x)⁻¹ • (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2) : E d)) := by
  have hP : pOf n δ Kθ x ≠ 0 := by have := one_le_pOf n δ Kθ x; positivity
  unfold aOf
  rw [show df2Ext (df2oPar d n δ) (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) =
      pOf n δ Kθ x * gθ u x.1 ((pOf n δ Kθ x)⁻¹ • (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2) : E d)) +
        2 * (pOf n δ Kθ x - 1) / (df2oPar d n δ).eps from rfl]
  rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hP]

/-- `pip(x) ≤ 2 √L` when `π(x) ≤ √L`, `ε ≤ 1/2`, `L ≥ 1`. -/
theorem pip_le_two_sqrt (p : Df2OPar) (K : Set (E d)) (x : E d) (L : ℝ) (hL : 1 ≤ L) (hε0 : 0 < p.eps)
    (hε : p.eps ≤ 1 / 2) (hx : gauge K x ≤ Real.sqrt L) : df2Pip p K x ≤ 2 * Real.sqrt L := by
  have hs : 1 ≤ Real.sqrt L := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL
  have h1 : (0 : ℝ) < 1 - p.eps := by linarith
  unfold df2Pip
  refine max_le (by linarith) ?_
  rw [div_le_iff₀ h1]
  have := gauge_nonneg (s := K) x
  nlinarith

/-- The play lies in the body. -/
theorem play_mem (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K) (hball : Metric.closedBall 0 1 ⊆ K)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (x : E d) : (pipOf K ε x)⁻¹ • x ∈ K := by
  have h := pip_play_mem K hK hKc hball ε hε0 hε1 x
  have h0 : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
  have h1 := hK.smul_mem_of_zero_mem h0 h (t := 1 - ε) ⟨by linarith, by linarith⟩
  rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - ε) ≠ 0), one_smul] at h1

variable {m : ℕ} (ap : ApFun d)

theorem measurable_X : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) =>
    (x.1, (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2) : E d)) :=
  measurable_fst.prodMk ((WithLp.measurable_toLp 2 _).comp ((measurable_xOf n δ).comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))

theorem measurable_gaugeX (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) :
    Measurable fun x : Θ × Df2St d × (Fin d → ℝ) => gauge (Kθ x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) := by
  have h := hmeas.1.comp (measurable_X n δ)
  exact h

theorem measurable_pOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) : Measurable (pOf n δ Kθ) := by
  have hg := measurable_gaugeX n δ Kθ gθ ap hmeas
  unfold pOf df2Pip
  exact measurable_const.max (hg.div_const _)

theorem measurable_jOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) : Measurable (jOf n δ Kθ) := by
  have hg := measurable_gaugeX n δ Kθ gθ ap hmeas
  unfold jOf
  exact Measurable.ite (measurableSet_le hg measurable_const) measurable_const measurable_const

theorem measurable_aOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {u : ℕ} (hu : u < m) :
    Measurable (aOf n δ Kθ gθ u) := by
  have hext : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) =>
      df2Ext (df2oPar d n δ) (Kθ x.1) (gθ u x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) := by
    have h := (hmeas.2.1 u hu).comp (measurable_X n δ)
    exact h
  have hp := measurable_pOf n δ Kθ gθ ap hmeas
  unfold aOf
  exact (hext.sub (((hp.sub_const 1).const_mul 2).div_const _)).div hp

theorem measurable_fOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) : Measurable (fOf n δ Kθ) := by
  have hr : Measurable fun y : (Θ × Df2St d) × (Fin d → ℝ) => ((y.1.1, y.1.2, y.2) : Θ × Df2St d × (Fin d → ℝ)) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hj := (measurable_jOf n δ Kθ gθ ap hmeas).comp hr
  have hp := (measurable_pOf n δ Kθ gθ ap hmeas).comp hr
  unfold fOf
  exact measurable_const.add (measurable_const.mul (hj.mul ((hp.sub_const 1).pow_const 2)))


/-- The truncated square of round `u` at a frozen point and a noise value. -/
noncomputable def zOf (u : ℕ) (y : (Θ × Df2St d × (Fin d → ℝ)) × ℝ) : ℝ :=
  jOf n δ Kθ y.1 * min ((pOf n δ Kθ y.1 * (aOf n δ Kθ gθ u y.1 + y.2) + 2 * (pOf n δ Kθ y.1 - 1) /
    (df2oPar d n δ).eps) ^ 2) (yB d n δ)

theorem measurable_zOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {u : ℕ} (hu : u < m) :
    Measurable (zOf n δ Kθ gθ u) := by
  have hj : Measurable fun y : (Θ × Df2St d × (Fin d → ℝ)) × ℝ => jOf n δ Kθ y.1 :=
    (measurable_jOf n δ Kθ gθ ap hmeas).comp measurable_fst
  have hp : Measurable fun y : (Θ × Df2St d × (Fin d → ℝ)) × ℝ => pOf n δ Kθ y.1 :=
    (measurable_pOf n δ Kθ gθ ap hmeas).comp measurable_fst
  have ha : Measurable fun y : (Θ × Df2St d × (Fin d → ℝ)) × ℝ => aOf n δ Kθ gθ u y.1 :=
    (measurable_aOf n δ Kθ gθ ap hmeas hu).comp measurable_fst
  have hY : Measurable fun y : (Θ × Df2St d × (Fin d → ℝ)) × ℝ =>
      pOf n δ Kθ y.1 * (aOf n δ Kθ gθ u y.1 + y.2) + 2 * (pOf n δ Kθ y.1 - 1) / (df2oPar d n δ).eps :=
    (hp.mul (ha.add measurable_snd)).add (((hp.sub_const 1).const_mul 2).div_const _)
  unfold zOf
  exact hj.mul ((hY.pow_const 2).min measurable_const)

end Frozen

/-! ## One round of Y -/

/-- `4 P² + 8 v²/ε² ≤ 8 + 10 v²/ε²` for `v = P - 1`, `ε ≤ 1/2`. -/
theorem round_arith (P ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    4 * P ^ 2 + 8 * (P - 1) ^ 2 / ε ^ 2 ≤ 8 + 10 / ε ^ 2 * (P - 1) ^ 2 := by
  have h1 : 4 * P ^ 2 ≤ 8 + 8 * (P - 1) ^ 2 := by nlinarith [sq_nonneg (P - 2)]
  have hε2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have h2 : 8 * (P - 1) ^ 2 ≤ 2 * (P - 1) ^ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hε2 (sq_nonneg (P - 1))]
  have h3 : 10 / ε ^ 2 * (P - 1) ^ 2 = 2 * (P - 1) ^ 2 / ε ^ 2 + 8 * (P - 1) ^ 2 / ε ^ 2 := by ring
  linarith

/-- The sigma-field of round `u` given the draw: `𝒢_u ∨ σ(ξ_u)`. -/
abbrev hOf {d : ℕ} {Ω : Type} {m0 : MeasurableSpace Ω} (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → Fin d → ℝ) (u : ℕ) :
    MeasurableSpace Ω :=
  𝒢 u ⊔ MeasurableSpace.comap (ξ u) inferInstance

section Round

variable {d : ℕ} {n : ℕ} {δ : ℝ} {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)}
  {gθ : ℕ → Θ → E d → ℝ} {ap : ApFun d}

omit [MeasurableSpace Θ] in
/-- On Pi, `1 ≤ P ≤ 2 √L`; so `0 ≤ 1{Pi} (P - 1)² ≤ 4 L` and `|1{Pi} P| ≤ 2 √L`. -/
theorem jOf_bounds (hL : 1 ≤ (df2oPar d n δ).Le) (hε0 : 0 < (df2oPar d n δ).eps) (hε : (df2oPar d n δ).eps ≤ 1 / 2)
    (x : Θ × Df2St d × (Fin d → ℝ)) :
    |jOf n δ Kθ x * pOf n δ Kθ x| ≤ 2 * Real.sqrt (df2oPar d n δ).Le ∧
      |jOf n δ Kθ x * (pOf n δ Kθ x - 1)| ≤ 2 * Real.sqrt (df2oPar d n δ).Le ∧
      0 ≤ jOf n δ Kθ x * (pOf n δ Kθ x - 1) ^ 2 ∧ jOf n δ Kθ x * (pOf n δ Kθ x - 1) ^ 2 ≤ 4 * (df2oPar d n δ).Le := by
  have hP1 := one_le_pOf n δ Kθ x
  have hs0 : 0 ≤ Real.sqrt (df2oPar d n δ).Le := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (df2oPar d n δ).Le by linarith)
  rcases jOf_mem n δ Kθ x with h | h
  · rw [h]; simp only [zero_mul, abs_zero, le_refl, true_and]
    refine ⟨by positivity, by positivity, by linarith⟩
  · have hg : gauge (Kθ x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2)) ≤ Real.sqrt (df2oPar d n δ).Le := by
      unfold jOf at h; split_ifs at h with hc
      · exact hc
      · norm_num at h
    have hP2 : pOf n δ Kθ x ≤ 2 * Real.sqrt (df2oPar d n δ).Le :=
      pip_le_two_sqrt (df2oPar d n δ) (Kθ x.1) _ _ hL hε0 hε hg
    rw [h, one_mul, one_mul, one_mul, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    refine ⟨hP2, by linarith, sq_nonneg _, ?_⟩
    nlinarith

/-- The integral of the bound of a round against the law of the draw. -/
theorem integral_fOf_le (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (hε0 : 0 < (df2oPar d n δ).eps)
    (hε1 : (df2oPar d n δ).eps < 1) (q : Θ) (hK : Convex ℝ (Kθ q)) (hKc : IsClosed (Kθ q))
    (hball : Metric.closedBall 0 1 ⊆ Kθ q) (st : Df2St d) :
    ∫ z, fOf n δ Kθ ((q, st), z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤
      8 + 10 / (df2oPar d n δ).eps ^ 2 *
        ∫ z, (pOf n δ Kθ (q, st, z) - 1) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  have hv : Integrable (fun z => (pOf n δ Kθ (q, st, z) - 1) ^ 2) (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    integrable_vsq_pi (Kθ q) hK hKc hball _ hε0.le hε1 st.mu st.A (df2oPar d n δ).lam
  have hmz : Measurable fun z : Fin d → ℝ => ((q, st, z) : Θ × Df2St d × (Fin d → ℝ)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hjm : Measurable fun z => jOf n δ Kθ (q, st, z) := (measurable_jOf n δ Kθ gθ ap hmeas).comp hmz
  have hpm : Measurable fun z => pOf n δ Kθ (q, st, z) := (measurable_pOf n δ Kθ gθ ap hmeas).comp hmz
  have hjle : ∀ z, jOf n δ Kθ (q, st, z) * (pOf n δ Kθ (q, st, z) - 1) ^ 2 ≤ (pOf n δ Kθ (q, st, z) - 1) ^ 2 := by
    intro z
    rcases jOf_mem n δ Kθ (q, st, z) with h | h <;> rw [h]
    · simp only [zero_mul]; exact sq_nonneg _
    · rw [one_mul]
  have hj0 : ∀ z, 0 ≤ jOf n δ Kθ (q, st, z) * (pOf n δ Kθ (q, st, z) - 1) ^ 2 := by
    intro z
    rcases jOf_mem n δ Kθ (q, st, z) with h | h <;> rw [h]
    · simp only [zero_mul, le_refl]
    · rw [one_mul]; exact sq_nonneg _
  have hjv : Integrable (fun z => jOf n δ Kθ (q, st, z) * (pOf n δ Kθ (q, st, z) - 1) ^ 2)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    refine hv.mono' (hjm.mul ((hpm.sub_const 1).pow_const 2)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hj0 z)]
    exact hjle z
  have hle := integral_mono hjv hv hjle
  unfold fOf
  rw [integral_add (integrable_const _) (hjv.const_mul _), integral_const, integral_const_mul]
  simp only [probReal_univ, one_smul]
  have : (0 : ℝ) ≤ 10 / (df2oPar d n δ).eps ^ 2 := by positivity
  gcongr

end Round

end EvGY

end AdversarialBco.Poly
