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
# The budget of Y

`df2EvYProp_of : Df2SIFacts → Df2EvYProp`. With `B = 4 L²/ε²` and, for the rounds `u < m`,
`Z_u = 1{π(X_u) ≤ √L} min(Y_u², B)`, adapted and in `[0, B]`:

* given `𝒢_u` and `ξ_u`, `E[Z_u | 𝒢_u ∨ σ(ξ_u)] ≤ 1{π(X_u) ≤ √L} (4 P² + 8 v²/ε²) ≤ 8 + 10 · 1{π(X_u) ≤ √L} v²/ε²`
  (`P = pip(X_u)`, `v = P - 1`; the noise is centred with `E[e² | ·] ≤ 1`);
* given `𝒢_u` (the tower and freezing, `ξ_u` independent of `𝒢_u`),
  `E[Z_u | 𝒢_u] ≤ W_u = 8 + (10/ε²) E_z v(μ_u + (1 - λ) A_u z)²`;
* Freedman's inequality uniform over the horizons `t ≤ m` (`freedman_W`): with probability at least `1 - δ_e/7`,
  `∑_{u < t} Z_u < 2 ∑_{u < t} W_u + B log(7/δ_e)` for every `t ≤ m`.

On `G`, at `t = τ + 1`: `Z_u = Y_u²` for `u ≤ τ` (Pi gives the indicator, `|Y_u| ≤ 2 L/ε` by Noise and Pi), and
`∑_{u ≤ τ} W_u ≤ 8 n + (10/ε²)(n ε²/4)` (`vsum_le_quarter`), `B log(7/δ_e) ≤ n` (row R7). So `∑_{u ≤ τ} Y_u² > 22 n`
lies in the exceptional event. The horizon `τ + 1` depends on `ω`: the bound holds for all horizons at once, so no
measurability of `τ` is read.
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

/-! ## The process on `Ω` -/

theorem measurable_stOr {d : ℕ} (d0 : Df2St d) : Measurable fun M : Df2Mode d => M.stOr d0 := by
  have heq : (fun M : Df2Mode d => M.stOr d0) = fun M => if M.code.1 = 2 then M.code.2 else d0 := by
    funext M; cases M <;> rfl
  rw [heq]
  exact Measurable.ite ((measurable_fst.comp measurable_mode_code) (measurableSet_singleton 2))
    (measurable_snd.comp measurable_mode_code) measurable_const

section Proc

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
  (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d) {Ω : Type} {m0 : MeasurableSpace Ω} (θ : Ω → Θ)
  (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)

/-- The state of round `u` at `ω`. -/
noncomputable def stW (u : ℕ) (ω : Ω) : Df2St d := (ctxW n δ Kθ ap θ ω).st (pathW gθ θ ξ e ω) u

/-- The frozen point of round `u` at `ω`: the parameter, the state, the draw. -/
noncomputable def xW (u : ℕ) (ω : Ω) : Θ × Df2St d × (Fin d → ℝ) :=
  (θ ω, stW n δ Kθ gθ ap θ ξ e u ω, ξ u ω)

variable (m) in
/-- `Z_u = 1{π(X_u) ≤ √L} min(Y_u², B)` for `u < m`, and `0` after the horizon. -/
noncomputable def zW (u : ℕ) (ω : Ω) : ℝ :=
  if u < m then zOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω, e u ω) else 0

/-- `W_u = 8 + (10/ε²) E_z v(μ_u + (1 - λ) A_u z)²`. -/
noncomputable def wW (u : ℕ) (ω : Ω) : ℝ :=
  8 + 10 / (df2oPar d n δ).eps ^ 2 * vmom (ctxW n δ Kθ ap θ ω) (pathW gθ θ ξ e ω) u

theorem measurable_stW (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (𝒢 : Filtration ℕ m0)
    (hθ : Measurable[𝒢 0] θ) (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s))
    {u : ℕ} (hu : u ≤ m) : Measurable[𝒢 u] (stW n δ Kθ gθ ap θ ξ e u) := by
  have h := (measurable_stOr (df2Init (df2oPar d n δ) d)).comp
    (measurable_mode n δ Kθ gθ ap hmeas 𝒢 θ ξ e hθ hξ he u hu)
  exact h

omit [MeasurableSpace Θ] in
theorem zW_nonneg (hB : 0 ≤ yB d n δ) (u : ℕ) (ω : Ω) : 0 ≤ zW n δ m Kθ gθ ap θ ξ e u ω := by
  unfold zW zOf
  split_ifs
  · rcases jOf_mem n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) with h | h <;> rw [h]
    · simp
    · rw [one_mul]; exact le_min (sq_nonneg _) hB
  · exact le_rfl

omit [MeasurableSpace Θ] in
theorem zW_le (hB : 0 ≤ yB d n δ) (u : ℕ) (ω : Ω) : zW n δ m Kθ gθ ap θ ξ e u ω ≤ yB d n δ := by
  unfold zW zOf
  split_ifs
  · rcases jOf_mem n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) with h | h <;> rw [h]
    · simpa using hB
    · rw [one_mul]; exact min_le_right _ _
  · exact hB

theorem measurable_zW (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (𝒢 : Filtration ℕ m0)
    (hθ : Measurable[𝒢 0] θ) (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s))
    (u : ℕ) : StronglyMeasurable[𝒢 (u + 1)] (zW n δ m Kθ gθ ap θ ξ e u) := by
  by_cases hu : u < m
  · have hfun : zW n δ m Kθ gθ ap θ ξ e u = fun ω => zOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω, e u ω) :=
      funext fun ω => by simp only [zW, hu, ite_true]
    rw [hfun]
    have hst : Measurable[𝒢 (u + 1)] (stW n δ Kθ gθ ap θ ξ e u) :=
      (measurable_stW n δ Kθ gθ ap θ ξ e hmeas 𝒢 hθ hξ he hu.le).mono (𝒢.mono (Nat.le_succ u)) le_rfl
    have hθ' : Measurable[𝒢 (u + 1)] θ := hθ.mono (𝒢.mono (Nat.zero_le _)) le_rfl
    have hx : Measurable[𝒢 (u + 1)] fun ω => (xW n δ Kθ gθ ap θ ξ e u ω, e u ω) :=
      (hθ'.prodMk (hst.prodMk (hξ u))).prodMk (he u)
    have h := (measurable_zOf n δ Kθ gθ ap hmeas hu).comp hx
    exact h.stronglyMeasurable
  · have hfun : zW n δ m Kθ gθ ap θ ξ e u = fun _ => 0 := funext fun ω => by simp only [zW, hu, ite_false]
    rw [hfun]
    exact stronglyMeasurable_const

end Proc

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

/-- One round: `E[Z_u | 𝒢_u] ≤ W_u` almost surely. -/
theorem condExp_zW_le (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q))
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (θ : Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hθ : Measurable[𝒢 0] θ) (hE : Df2SetE d μ 𝒢 ξ e) (u : ℕ) :
    μ[zW n δ m Kθ gθ ap θ ξ e u | 𝒢 u] ≤ᵐ[μ] wW n δ Kθ gθ ap θ ξ e u := by
  have hP := evGPar d n δ hd hn hδ0
  have hε0 := hP.eps0
  have hε1 : (df2oPar d n δ).eps < 1 := by linarith
  have hL1 : 1 ≤ (df2oPar d n δ).Le := by linarith [hP.L504]
  by_cases hu : u < m
  swap
  · have hfun : zW n δ m Kθ gθ ap θ ξ e u = 0 := funext fun ω => by simp only [zW, hu, ite_false, Pi.zero_apply]
    rw [hfun, condExp_zero]
    refine ae_of_all _ fun ω => ?_
    have := vmom_nonneg (ctxW n δ Kθ ap θ ω) (pathW gθ θ ξ e ω) u
    show (0 : ℝ) ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * vmom (ctxW n δ Kθ ap θ ω) (pathW gθ θ ξ e ω) u
    positivity

  have hξm : Measurable[m0] (ξ u) := (hE.xi_meas u).mono (𝒢.le _) le_rfl
  have hH : hOf 𝒢 ξ u ≤ m0 := sup_le (𝒢.le u) hξm.comap_le
  have hst := measurable_stW n δ Kθ gθ ap θ ξ e hmeas 𝒢 hθ hE.xi_meas hE.e_meas hu.le
  have hθu : Measurable[𝒢 u] θ := hθ.mono (𝒢.mono (Nat.zero_le u)) le_rfl
  have hx : Measurable[𝒢 u] fun ω => (θ ω, stW n δ Kθ gθ ap θ ξ e u ω) := hθu.prodMk hst
  have hxH : Measurable[hOf 𝒢 ξ u] (xW n δ Kθ gθ ap θ ξ e u) :=
    (hθu.mono le_sup_left le_rfl).prodMk ((hst.mono le_sup_left le_rfl).prodMk
      ((comap_measurable (ξ u)).mono le_sup_right le_rfl))
  have hJ : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) :=
    ((measurable_jOf n δ Kθ gθ ap hmeas).comp hxH).stronglyMeasurable
  have hPm : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) :=
    ((measurable_pOf n δ Kθ gθ ap hmeas).comp hxH).stronglyMeasurable
  have ham : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω) :=
    ((measurable_aOf n δ Kθ gθ ap hmeas hu).comp hxH).stronglyMeasurable
  have hvm : StronglyMeasurable[hOf 𝒢 ξ u] fun ω => pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1 :=
    (((measurable_pOf n δ Kθ gθ ap hmeas).comp hxH).sub_const 1).stronglyMeasurable
  have ha01 : ∀ ω, aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω) ∈ Set.Icc (0 : ℝ) 1 := by
    intro ω
    obtain ⟨hK, hKc, hball, -, -⟩ := hbody (θ ω)
    rw [aOf_eq]
    exact (hadm (θ ω) u hu).2 _ (play_mem (Kθ (θ ω)) hK hKc hball _ hε0 hε1 _)
  have hB0 : 0 ≤ yB d n δ := by unfold yB; positivity
  have he : Measurable[m0] (e u) := (hE.e_meas u).mono (𝒢.le _) le_rfl
  have h1 := condExp_round_le (hOf 𝒢 ξ u) μ hH (fun ω => jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω))
    (fun ω => pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω)) (fun ω => aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω))
    (fun ω => pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1) hJ (fun ω => jOf_mem n δ Kθ _) hPm ham ha01 hvm
    (2 * Real.sqrt (df2oPar d n δ).Le) (fun ω => (jOf_bounds hL1 hε0 heps _).1)
    (fun ω => (jOf_bounds hL1 hε0 heps _).2.1) (df2oPar d n δ).eps (yB d n δ) hε0 hB0 (e u) he (hE.e_int u)
    (hE.e_mean u) (hE.e_exp u)
  have hzW : zW n δ m Kθ gθ ap θ ξ e u = fun ω => jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) *
      min ((pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) * (aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω) + e u ω) +
        2 * (pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1) / (df2oPar d n δ).eps) ^ 2) (yB d n δ) :=
    funext fun ω => by simp only [zW, hu, ite_true]; rfl
  have h2 : ∀ ω, jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) * (4 * pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) ^ 2 +
      8 * (pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1) ^ 2 / (df2oPar d n δ).eps ^ 2) ≤
      fOf n δ Kθ ((θ ω, stW n δ Kθ gθ ap θ ξ e u ω), ξ u ω) := by
    intro ω
    show _ ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * (jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) *
      (pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1) ^ 2)
    rcases jOf_mem n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) with h | h <;> rw [h]
    · simp only [zero_mul, mul_zero, add_zero]; norm_num
    · simp only [one_mul]; exact round_arith _ _ hε0 heps
  have hYF : μ[zW n δ m Kθ gθ ap θ ξ e u | hOf 𝒢 ξ u] ≤ᵐ[μ]
      fun ω => fOf n δ Kθ ((θ ω, stW n δ Kθ gθ ap θ ξ e u ω), ξ u ω) := by
    rw [hzW]
    exact h1.trans (ae_of_all _ h2)
  have hint : Integrable (zW n δ m Kθ gθ ap θ ξ e u) μ := by
    refine Integrable.of_bound ((measurable_zW n δ Kθ gθ ap θ ξ e hmeas 𝒢 hθ hE.xi_meas hE.e_meas u).mono
      (𝒢.le _)).aestronglyMeasurable (yB d n δ) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (zW_nonneg n δ Kθ gθ ap θ ξ e hB0 u ω)]
    exact zW_le n δ Kθ gθ ap θ ξ e hB0 u ω
  have hF0 : ∀ y, 0 ≤ fOf n δ Kθ y := by
    intro y
    have := (jOf_bounds (Kθ := Kθ) hL1 hε0 heps (y.1.1, y.1.2, y.2)).2.2.1
    unfold fOf; positivity
  have hFC : ∀ y, fOf n δ Kθ y ≤ 8 + 10 / (df2oPar d n δ).eps ^ 2 * (4 * (df2oPar d n δ).Le) := by
    intro y
    have := (jOf_bounds (Kθ := Kθ) hL1 hε0 heps (y.1.1, y.1.2, y.2)).2.2.2
    unfold fOf
    have : (0 : ℝ) ≤ 10 / (df2oPar d n δ).eps ^ 2 := by positivity
    gcongr
  have h3 := condExp_le_freeze lemmaFR (𝒢 u) (hOf 𝒢 ξ u) μ le_sup_left hH (fun ω => (θ ω, stW n δ Kθ gθ ap θ ξ e u ω))
    (ξ u) hx hξm (hE.xi_indep u) _ hint (fOf n δ Kθ) (measurable_fOf n δ Kθ gθ ap hmeas) _ hF0 hFC hYF
  rw [hE.xi_law u] at h3
  refine h3.trans (ae_of_all _ fun ω => ?_)
  obtain ⟨hK, hKc, hball, -, -⟩ := hbody (θ ω)
  exact integral_fOf_le (gθ := gθ) (ap := ap) hmeas hε0 hε1 (θ ω) hK hKc hball _

end Round

/-! ## The budget -/

section Main

variable {d : ℕ} {n : ℕ} {δ : ℝ} {m : ℕ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)}
  {gθ : ℕ → Θ → E d → ℝ} {ap : ApFun d} {Ω : Type} {m0 : MeasurableSpace Ω} {θ : Ω → Θ}
  {ξ : ℕ → Ω → Fin d → ℝ} {e : ℕ → Ω → ℝ}

omit [MeasurableSpace Θ] in
/-- `Y_u = P (a + e) + 2 (P - 1)/ε` at the frozen point of round `u`. -/
theorem Y_eq_frozen (ω : Ω) (u : ℕ) :
    (ctxW n δ Kθ ap θ ω).Y (pathW gθ θ ξ e ω) u =
      pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) * (aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω) + e u ω) +
        2 * (pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) - 1) / (df2oPar d n δ).eps := by
  rw [aOf_eq]
  rfl

omit [MeasurableSpace Θ] in
/-- On Noise and Pi at round `u < m`, `Z_u = Y_u²`. -/
theorem zW_eq_sq (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) (ω : Ω)
    {u : ℕ} (hu : u < m) (he : |e u ω| ≤ Real.sqrt (df2Lg (df2oPar d n δ) n))
    (hg : gauge (Kθ (θ ω)) (WithLp.toLp 2 (xOf n δ (stW n δ Kθ gθ ap θ ξ e u ω) (ξ u ω))) ≤
      Real.sqrt (df2oPar d n δ).Le) :
    zW n δ m Kθ gθ ap θ ξ e u ω = (ctxW n δ Kθ ap θ ω).Y (pathW gθ θ ξ e ω) u ^ 2 := by
  have hP := evGPar d n δ hd hn hδ0
  have hε0 := hP.eps0
  have hε1 : (df2oPar d n δ).eps < 1 := by linarith
  have hj : jOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) = 1 := ite_eq_left hg
  have hP2 : pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω) ≤ 2 * Real.sqrt (df2oPar d n δ).Le :=
    pip_le_two_sqrt (df2oPar d n δ) (Kθ (θ ω)) _ _ (by linarith [hP.L504]) hε0 heps hg
  have ha : aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω) ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hK, hKc, hball, -, -⟩ := hbody (θ ω)
    rw [aOf_eq]
    exact (hadm (θ ω) u hu).2 _ (play_mem (Kθ (θ ω)) hK hKc hball _ hε0 hε1 _)
  have hmax := ymax_le (df2oPar d n δ).Le (df2Lg (df2oPar d n δ) n) (df2oPar d n δ).eps
    (pOf n δ Kθ (xW n δ Kθ gθ ap θ ξ e u ω)) (aOf n δ Kθ gθ u (xW n δ Kθ gθ ap θ ξ e u ω)) (e u ω)
    (by linarith [hP.L504]) hP.LgLe hε0 heps (one_le_pOf n δ Kθ _) hP2 ha he
  rw [Y_eq_frozen]
  unfold zW zOf
  rw [ite_eq_left hu, hj, one_mul]
  apply min_eq_left
  refine hmax.trans (le_of_eq ?_)
  unfold yB
  ring

end Main

/-- The budget of Y: on every instance of setting (E), `G` holds and `Y` fails with probability at most `δ_e/7`. -/
theorem df2EvYProp_of (hSI : Df2SIFacts) : Df2EvYProp := by
  intro d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ξ e hθ hE
  have hP := evGPar d n δ hd hn hδ0
  have hB : 0 < yB d n δ := by unfold yB; have := hP.L504; have := hP.eps0; positivity
  have hde7 : 0 < (df2oPar d n δ).δe / 7 := by have := hP.de; positivity
  have hF := freedman_W μ 𝒢 (zW n δ m Kθ gθ ap θ ξ e) (wW n δ Kθ gθ ap θ ξ e) (yB d n δ) hB
    (measurable_zW n δ Kθ gθ ap θ ξ e hmeas 𝒢 hθ hE.xi_meas hE.e_meas) (zW_nonneg n δ Kθ gθ ap θ ξ e hB.le)
    (zW_le n δ Kθ gθ ap θ ξ e hB.le) (condExp_zW_le hd hn hδ0 heps hbody hadm hmeas μ 𝒢 θ ξ e hθ hE) m
    ((df2oPar d n δ).δe / 7) hde7
  refine le_trans (measure_mono ?_) (hF.trans (le_of_eq (congrArg ENNReal.ofReal (by ring))))
  intro ω hω
  obtain ⟨hG, hY⟩ := hω
  have H := detBase (π := pathW gθ θ ξ e ω) hSI hd hn hδ0 hδ1 heps hm1 hmn (hbody (θ ω)) hap (hadm (θ ω))
  have hτm : (ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m < m := H.tau_lt
  refine ⟨(ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1, hτm, ?_⟩
  have hZ : ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1), zW n δ m Kθ gθ ap θ ξ e u ω =
      ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1),
        (ctxW n δ Kθ ap θ ω).Y (pathW gθ θ ξ e ω) u ^ 2 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hut : u ≤ (ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    exact zW_eq_sq hd hn hδ0 heps hbody hadm ω (lt_of_le_of_lt hut hτm) (hG u hut).1 (hG u hut).2.1
  have hY' : 22 * (n : ℝ) < ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1),
      (ctxW n δ Kθ ap θ ω).Y (pathW gθ θ ξ e ω) u ^ 2 := lt_of_not_ge hY
  have hV := vsum_le_quarter hSI d n δ (Kθ (θ ω)) ap (pathW gθ θ ξ e ω) m hd hn hδ0 hδ1 heps hm1 hmn
    (hbody (θ ω)) hap (hadm (θ ω)) _ le_rfl
  have hW : ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1), wW n δ Kθ gθ ap θ ξ e u ω =
      ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1 : ℕ) * 8 + 10 / (df2oPar d n δ).eps ^ 2 *
        ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1),
          vmom (df2CtxAt d n δ (Kθ (θ ω)) ap) (pathW gθ θ ξ e ω) u := by
    unfold wW
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hτn : (((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt hτm).trans hmn
  have hε0 := hP.eps0
  have hεne : (df2oPar d n δ).eps ^ 2 ≠ 0 := by positivity
  have hWb : 10 / (df2oPar d n δ).eps ^ 2 *
      ∑ u ∈ Finset.range ((ctxW n δ Kθ ap θ ω).tau (pathW gθ θ ξ e ω) m + 1),
        vmom (df2CtxAt d n δ (Kθ (θ ω)) ap) (pathW gθ θ ξ e ω) u ≤ 10 / 4 * n := by
    calc _ ≤ 10 / (df2oPar d n δ).eps ^ 2 * (1 / 4 * n * (df2oPar d n δ).eps ^ 2) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 10 / 4 * n := by field_simp
  have hyb := yb_arith n (df2oPar d n δ).Le (df2oPar d n δ).eps (df2oPar d n δ).δe hP.de H.x_ge H.Le_eq hε0
    H.rows.r7
  have hyb' : yB d n δ * Real.log (1 / ((df2oPar d n δ).δe / 7)) ≤ n := hyb
  rw [hZ, hW]
  linarith

end EvGY

end AdversarialBco.Poly
