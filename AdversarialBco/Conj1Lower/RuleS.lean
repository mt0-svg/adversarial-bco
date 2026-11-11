/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Bayes
public import AdversarialBco.Conj1Lower.Moments
public import AdversarialBco.Conj1Lower.Geom
public import AdversarialBco.Conj1Lower.Balance
public import AdversarialBco.Conj1Lower.CellMeas

@[expose] public section

/-!
# The rule S' of the genie (Section 9 of the paper)

The strategy `S'(g, k, L, σ)` as an instance of the generic Bayes core of Bayes.lean.

* Parameters `SParams` (`g`, `k`, `L`, `sc` the noise scale `σ`, `b` the offset of the losses); derived:
  `κ = g/k` (`SParams.kappa`), `ε = k`, `r₁ = 5 d^{1/2}` (`rOne`), the floor `w* = κ r₁/L` (`SParams.w`, the `wStar`
  of Balance.lean).
* The frame of a law `π`: the mean `meanV π` and covariance `covM π` (Moments.lean), the operator
  `frameS = M^{1/2}` (`frameA` of Frame.lean), `D_M` (`dmS`), the live test `d_live ≥ d/2` (`liveS`), the dent
  `dentS π x θ = D_π(x; θ)` and the answer `ansS` (`answer` of Cells.lean: the cell of the tip if ripe, `none` for
  rest).
* `ruleS d P : Rule d (Option Cell)`: on a live round the answer `ansS` and the signal `b + D_π(x; θ)`; on a dead
  round the answer `none` and the signal `b` (constants, so the posterior does not move: `bayesUpd_const`).
* Measurability (Lemma 9.3): `ruleS_meas`, from the measurability of `cfc` in the matrix
  (`measurable_cfc_of_continuous`), of `dLive` (a limit of continuous traces), of the dent (an infimum over rational
  `λ`), of the moments and the ripeness masses along a measurable family of densities.
* The deterministic strategy of a fixed tip `xo` and noise sequence `z` (`stratOf`), a `Strategy d` that reads the
  past plays only, and its transcript against any learner (`transcript_stratOf`): the history of Bayes.lean.
* The mean regret of a round: `regret_round`, Lemma 9.5 for the dent.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace AdversarialBco.Lower.Bayes

open RealRAM

/-! ## Parameters -/

/-- The parameters of the strategy `S'(g, k, L, σ)`: the depth `g`, the scale `k`, the Lipschitz constant `L`, the
noise scale `sc` (`σ`) and the offset `b` of the losses. -/
structure SParams where
  /-- The depth `g`. -/
  g : ℝ
  /-- The scale `k` (also the `ε` of the dent). -/
  k : ℝ
  /-- The Lipschitz constant `L` of the losses. -/
  L : ℝ
  /-- The noise scale `σ`. -/
  sc : ℝ
  /-- The offset `b` of the losses. -/
  b : ℝ

/-- `κ = g/k`. -/
noncomputable def SParams.kappa (P : SParams) : ℝ := P.g / P.k

/-- `r₁ = 5 d^{1/2}`. -/
noncomputable def rOne (d : ℕ) : ℝ := 5 * Real.sqrt d

/-- The floor `w* = κ r₁/L`, the `wStar` of Balance.lean. -/
noncomputable def SParams.w (P : SParams) (d : ℕ) : ℝ := wStar d P.k P.L P.g

theorem SParams.w_eq (P : SParams) (d : ℕ) : P.w d = P.kappa * rOne d / P.L := rfl

/-! ## The frame of a law and the rule -/

section Rule

variable {d : ℕ}

/-- `M^{1/2}` of the frame of `π` as an operator: `|v|_M = ‖frameS P d π v‖`. -/
noncomputable def frameS (P : SParams) (d : ℕ) (π : Measure (E d)) : E d →L[ℝ] E d :=
  frameA (P.w d) (covM π)

/-- `D_M = tr(M Σ)` of the frame of `π`. -/
noncomputable def dmS (P : SParams) (d : ℕ) (π : Measure (E d)) : ℝ :=
  DM (P.w d) (covM π)

/-- The round is live: `d_live(π) ≥ d/2`. -/
def liveS (P : SParams) (d : ℕ) (π : Measure (E d)) : Prop :=
  (d : ℝ) / 2 ≤ dLive (P.w d) (covM π)

noncomputable instance liveS.decidable (P : SParams) (π : Measure (E d)) : Decidable (liveS P d π) :=
  inferInstanceAs (Decidable ((d : ℝ) / 2 ≤ dLive (P.w d) (covM π)))

/-- The dent of the law `π` at the tip `θ`, read at the play `x`: `D_π(x; θ)`. -/
noncomputable def dentS (P : SParams) (d : ℕ) (π : Measure (E d)) (x θ : E d) : ℝ :=
  dent (frameS P d π) (meanV π) P.kappa P.k (rOne d) θ x

/-- The answer on a live round: the cell of `(π, x)` that contains the tip if it is ripe, `none` (rest) otherwise. -/
noncomputable def ansS (P : SParams) (d : ℕ) (π : Measure (E d)) (x θ : E d) : Option Cell :=
  answer π (frameS P d π) (meanV π) P.k d (dmS P d π) x θ

/-- The rule `S'`: on a live round the answer `ansS` and the signal `b + D_π(x; θ)`; on a dead round the answer
`none` and the signal `b`. -/
noncomputable def ruleS (d : ℕ) (P : SParams) : Rule d (Option Cell) where
  ans π x θ := if liveS P d π then ansS P d π x θ else none
  sig π x θ := P.b + if liveS P d π then dentS P d π x θ else 0

theorem ruleS_sig_sub (P : SParams) (π : Measure (E d)) (x θ : E d) :
    (ruleS d P).sig π x θ - P.b = if liveS P d π then dentS P d π x θ else 0 := by
  simp [ruleS]

/-- On a dead round the answer and the signal do not depend on the tip. -/
theorem ruleS_dead (P : SParams) {π : Measure (E d)} (h : ¬ liveS P d π) (x θ : E d) :
    (ruleS d P).ans π x θ = none ∧ (ruleS d P).sig π x θ = P.b := by
  simp [ruleS, h]

end Rule

/-! ## Measurability of the frame and of the dent in the matrix -/

section MatMeas

variable {d : ℕ}

/-- `S ↦ f(S)` is measurable for a continuous `f` (continuous on the self-adjoint matrices, `0` off them). -/
theorem measurable_cfc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun S : Matrix (Fin d) (Fin d) ℝ => cfc f S) := by
  classical
  let s : Set (Matrix (Fin d) (Fin d) ℝ) := {S | IsSelfAdjoint S}
  have hs : IsClosed s := isClosed_eq continuous_star continuous_id
  have hcont : ContinuousOn (fun S : Matrix (Fin d) (Fin d) ℝ => cfc f S) s := by
    open scoped Matrix.Norms.L2Operator in
    exact ContinuousOn.cfc_of_mem_nhdsSet (s := Set.univ) f (by simp) continuousOn_id
      (fun S hS => hS) hf.continuousOn
  have heq : (fun S : Matrix (Fin d) (Fin d) ℝ => cfc f S) =
      s.piecewise (fun S => cfc f S) (fun _ => 0) := by
    funext S
    by_cases hS : S ∈ s
    · simp [Set.piecewise, hS]
    · simp only [Set.piecewise, hS, ite_false]
      exact cfc_apply_of_not_predicate S hS
  rw [heq]
  exact hcont.measurable_piecewise continuousOn_const hs.measurableSet

theorem measurable_clipSqrt {w : ℝ} (hw : w ≠ 0) : Measurable (clipSqrt (d := d) w) := by
  have hw2 : w ^ 2 > 0 := sq_pos_iff.mpr hw
  have hpos : ∀ s : ℝ, Real.sqrt (max s (w ^ 2)) ≠ 0 := by
    intro s
    refine (Real.sqrt_pos.mpr ?_).ne'
    exact lt_of_lt_of_le hw2 (le_max_right _ _)
  have hcont : Continuous (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) :=
    Continuous.inv₀ (Continuous.sqrt (continuous_id.max continuous_const)) hpos
  have h_eq : clipSqrt (d := d) w = (fun S : Matrix (Fin d) (Fin d) ℝ => cfc (fun s : ℝ => (Real.sqrt (max s (w ^ 2)))⁻¹) S) := by
    ext S; rfl
  rw [h_eq]
  exact measurable_cfc_of_continuous hcont

theorem measurable_clipM {w : ℝ} (hw : w ≠ 0) : Measurable (clipM (d := d) w) := by
  have h_max_cont : Continuous (fun s : ℝ => max s (w ^ 2)) :=
    continuous_max.comp (Continuous.prodMk continuous_id continuous_const)
  have h_inv_cont : Continuous (fun s : ℝ => (max s (w ^ 2))⁻¹) :=
    h_max_cont.inv₀ (fun s => by
      have hle : w ^ 2 ≤ max s (w ^ 2) := le_max_right _ _
      have hsq_pos : w ^ 2 > 0 := sq_pos_iff.mpr hw
      linarith)
  have h := measurable_cfc_of_continuous (d := d) h_inv_cont
  unfold clipM
  exact h

theorem measurable_DM {w : ℝ} (hw : w ≠ 0) : Measurable (DM (d := d) w) := by
  have e : DM (d := d) w = fun S => ∑ i, ∑ j, clipM w S i j * S j i := by
    funext S
    simp [DM, Matrix.trace, Matrix.mul_apply]
  rw [e]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((measurable_clipM hw).eval_matrix (i := i) (j := j)).mul (measurable_id.eval_matrix (i := j) (j := i))

/-- `d_live` is measurable: the limit of the traces of `f_j(S)`, `f_j(s) = min 1 (max 0 (1 + j (s - w²)))`. -/
theorem measurable_dLive (w : ℝ) : Measurable (dLive (d := d) w) := by
  classical
  let f : ℕ → ℝ → ℝ := fun j s => min 1 (max 0 (1 + (j : ℝ) * (s - w ^ 2)))
  have hfc : ∀ j, Continuous (f j) := fun j => by fun_prop
  have hlim : ∀ s : ℝ, Tendsto (fun j => f j s) atTop (𝓝 (if w ^ 2 ≤ s then 1 else 0)) := by
    intro s
    by_cases hs : w ^ 2 ≤ s
    · simp only [hs, ↓reduceIte]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
      have : 0 ≤ (j : ℝ) * (s - w ^ 2) := mul_nonneg (Nat.cast_nonneg j) (sub_nonneg.2 hs)
      simp only [f]
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    · simp only [hs, ↓reduceIte]
      push Not at hs
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (w ^ 2 - s))
      refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun j hj => ?_)
      have hpos : 0 < w ^ 2 - s := by linarith
      have hj' : 1 / (w ^ 2 - s) ≤ (j : ℝ) := hN.le.trans (by exact_mod_cast hj)
      have : 1 ≤ (j : ℝ) * (w ^ 2 - s) := by
        rw [div_le_iff₀ hpos] at hj'; linarith
      simp only [f]
      rw [max_eq_left (by nlinarith), min_eq_right (by norm_num)]
  have hmeas : ∀ j, Measurable (fun S : Matrix (Fin d) (Fin d) ℝ => Matrix.trace (cfc (f j) S)) := fun j =>
    (Continuous.measurable (continuous_id.matrix_trace)).comp (measurable_cfc_of_continuous (hfc j))
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun S => ?_)
  by_cases hS : S.IsHermitian
  · simp only [dLive]
    rw [trace_cfc_eq_sum _ S hS]
    have : (fun j => Matrix.trace (cfc (f j) S)) = fun j => ∑ i, f j (hS.eigenvalues i) := by
      funext j; exact trace_cfc_eq_sum _ S hS
    rw [this]
    exact tendsto_finsetSum _ fun i _ => hlim _
  · have hS' : ¬ IsSelfAdjoint S := fun h => hS h
    simp only [dLive]
    rw [cfc_apply_of_not_predicate S hS']
    have : (fun j => Matrix.trace (cfc (f j) S)) = fun _ => (0 : ℝ) := by
      funext j; rw [cfc_apply_of_not_predicate S hS', Matrix.trace_zero]
    rw [this, Matrix.trace_zero]
    exact tendsto_const_nhds

theorem measurable_frameA_apply {w : ℝ} (hw : w ≠ 0) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × E d => frameA w p.1 p.2) := by
  have h : (fun p : Matrix (Fin d) (Fin d) ℝ × E d => frameA w p.1 p.2) =
      (fun q : Matrix (Fin d) (Fin d) ℝ × E d => Matrix.toEuclideanCLM (𝕜 := ℝ) q.1 q.2) ∘
        (fun p : Matrix (Fin d) (Fin d) ℝ × E d => (clipSqrt w p.1, p.2)) := rfl
  rw [h]
  exact Matrix.continuous_uncurry_toEuclideanCLM.measurable.comp
    (((measurable_clipSqrt hw).comp measurable_fst).prodMk measurable_snd)

/-- The dent of the frame of `S`, as a function of `(S, m, x, θ)` (Lemma 9.3). -/
theorem measurable_dent_frame {w κ ε r₁ : ℝ} (hw : w ≠ 0) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d =>
      dent (frameA w p.1) p.2.1 κ ε r₁ p.2.2.2 p.2.2.1) := by
  have heq : (fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d =>
      dent (frameA w p.1) p.2.1 κ ε r₁ p.2.2.2 p.2.2.1) =
      fun p => ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1}, ((r : ℚ) : ℝ) *
        (κ * huber r₁ ε ‖frameA w p.1 (p.2.2.2 + ((r : ℚ) : ℝ)⁻¹ • (p.2.2.1 - p.2.2.2) - p.2.1)‖) := by
    funext p
    rw [dent_eq_iInf_rat _ _ κ ε r₁ hκ hε hr]
    rfl
  rw [heq]
  refine Measurable.iInf fun r => ?_
  have hhub : Measurable (huber r₁ ε) := by
    unfold huber
    exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  have hv : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d =>
      (p.1, p.2.2.2 + ((r : ℚ) : ℝ)⁻¹ • (p.2.2.1 - p.2.2.2) - p.2.1) :=
    measurable_fst.prodMk (by fun_prop)
  have hA : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d =>
      frameA w p.1 (p.2.2.2 + ((r : ℚ) : ℝ)⁻¹ • (p.2.2.1 - p.2.2.2) - p.2.1) := by
    have := (measurable_frameA_apply (d := d) hw).comp hv
    exact this
  have h2 := hhub.comp hA.norm
  exact (h2.const_mul κ).const_mul _

/-- The cell map, as a function of `(S, m, D_M, x, θ)` (Lemma 9.3). -/
theorem measurable_cellOf_frame {w : ℝ} (hw : w ≠ 0) (k dd : ℝ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d =>
      cellOf (frameA w p.1) p.2.1 k dd p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hA := measurable_frameA_apply (d := d) hw
  have px : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d => (p.1, p.2.2.2.1 - p.2.1) := by
    fun_prop
  have pθ : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d => (p.1, p.2.2.2.2 - p.2.1) := by
    fun_prop
  have hT := ((hA.comp px).inner (hA.comp pθ)).div (hA.comp px).norm
  have pR : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d => (p.1, p.2.2.2.2 - p.2.1) := by
    fun_prop
  have hR := (hA.comp pR).norm.pow_const 2
  have hD : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d => p.2.2.1 := by fun_prop
  classical
  unfold cellOf
  refine Measurable.ite (measurableSet_lt measurable_const hT) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_const hR) measurable_const ?_
  exact Measurable.ite (measurableSet_lt hR (hD.div_const 64)) measurable_const measurable_const

/-- The read `T`, as a function of `(S, m, x, θ)`. -/
theorem measurable_readT_frame {w : ℝ} (hw : w ≠ 0) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d => readT (frameA w p.1) p.2.1 p.2.2.2 p.2.2.1) := by
  have hA := measurable_frameA_apply (d := d) hw
  have px : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d => (p.1, p.2.2.1 - p.2.1) := by
    fun_prop
  have pθ : Measurable fun p : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d => (p.1, p.2.2.2 - p.2.1) := by
    fun_prop
  have hx := hA.comp px
  have hθ := hA.comp pθ
  exact (hx.inner hθ).div hx.norm

end MatMeas

/-! ## Integrals along a measurable family of densities (Lemma 9.3) -/

section DensMeas

variable {d : ℕ} {H : Type} [MeasurableSpace H]

/-- A Bochner integral against `π0.withDensity (g h)` is measurable in the parameter. -/
theorem measurable_integral_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) {Q : Type} [MeasurableSpace Q] {hp : Q → H}
    (hhp : Measurable hp) {F : Q × E d → ℝ} (hF : Measurable F) :
    Measurable (fun q => ∫ θ, F (q, θ) ∂π0.withDensity (g (hp q))) := by
  have hgq : Measurable (fun r : Q × E d => g (hp r.1) r.2) :=
    hg.comp ((hhp.comp measurable_fst).prodMk measurable_snd)
  have heq : (fun q => ∫ θ, F (q, θ) ∂π0.withDensity (g (hp q))) =
      fun q => ∫ θ, (g (hp q) θ).toReal • F (q, θ) ∂π0 := by
    funext q
    exact integral_withDensity_eq_integral_toReal_smul (hgq.comp (measurable_prodMk_left (x := q)))
      (ae_of_all _ fun θ => lt_top_iff_ne_top.2 (hfin _ θ)) _
  rw [heq]
  exact ((hgq.ennreal_toReal.smul hF).stronglyMeasurable.integral_prod_right' (ν := π0)).measurable

/-- A vector-valued Bochner integral against `π0.withDensity (g h)` is measurable in the parameter. -/
theorem measurable_integral_dens_vec (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) {Q : Type} [MeasurableSpace Q] {hp : Q → H}
    (hhp : Measurable hp) {F : Q × E d → E d} (hF : Measurable F) :
    Measurable (fun q => ∫ θ, F (q, θ) ∂π0.withDensity (g (hp q))) := by
  have hgq : Measurable (fun r : Q × E d => g (hp r.1) r.2) :=
    hg.comp ((hhp.comp measurable_fst).prodMk measurable_snd)
  have heq : (fun q => ∫ θ, F (q, θ) ∂π0.withDensity (g (hp q))) =
      fun q => ∫ θ, (g (hp q) θ).toReal • F (q, θ) ∂π0 := by
    funext q
    exact integral_withDensity_eq_integral_toReal_smul (hgq.comp (measurable_prodMk_left (x := q)))
      (ae_of_all _ fun θ => lt_top_iff_ne_top.2 (hfin _ θ)) _
  rw [heq]
  exact ((hgq.ennreal_toReal.smul hF).stronglyMeasurable.integral_prod_right' (ν := π0)).measurable

/-- The mass of a measurable family of sets under `π0.withDensity (g h)` is measurable in the parameter. -/
theorem measurable_measureReal_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) {Q : Type} [MeasurableSpace Q] {hp : Q → H}
    (hhp : Measurable hp) {S : Set (Q × E d)} (hS : MeasurableSet S) :
    Measurable (fun q => (π0.withDensity (g (hp q))).real {θ | (q, θ) ∈ S}) := by
  have h_meas_set (q : Q) : MeasurableSet {θ | (q, θ) ∈ S} :=
    measurable_prodMk_left hS
  have h_meas_uncurried : Measurable (fun (r : Q × E d) => g (hp r.1) r.2) :=
    hg.comp (Measurable.prodMk (hhp.comp measurable_fst) measurable_snd)
  have h_meas_f : Measurable (S.indicator (fun (r : Q × E d) => g (hp r.1) r.2)) :=
    h_meas_uncurried.indicator hS
  have h_meas_lintegral : Measurable (fun (q : Q) =>
      (∫⁻ θ, S.indicator (fun (r : Q × E d) => g (hp r.1) r.2) (q, θ) ∂π0).toReal) :=
    h_meas_f.lintegral_prod_right'.ennreal_toReal
  have h_eq (q : Q) : (∫⁻ θ, S.indicator (fun (r : Q × E d) => g (hp r.1) r.2) (q, θ) ∂π0).toReal =
      (π0.withDensity (g (hp q))).real {θ | (q, θ) ∈ S} := by
    rw [measureReal_def, withDensity_apply _ (h_meas_set q), ← lintegral_indicator (h_meas_set q) (g (hp q))]
    refine congrArg ENNReal.toReal (lintegral_congr (fun θ => ?_))
    simp [Set.indicator]
  simpa [h_eq] using h_meas_lintegral

/-- A set integral over a measurable family of sets against `π0.withDensity (g h)` is measurable in the
parameter. -/
theorem measurable_setIntegral_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) {Q : Type} [MeasurableSpace Q] {hp : Q → H}
    (hhp : Measurable hp) {S : Set (Q × E d)} (hS : MeasurableSet S) {F : Q × E d → ℝ} (hF : Measurable F) :
    Measurable (fun q => ∫ θ in {θ | (q, θ) ∈ S}, F (q, θ) ∂π0.withDensity (g (hp q))) := by
  have e : (fun q => ∫ θ in {θ | (q, θ) ∈ S}, F (q, θ) ∂π0.withDensity (g (hp q))) =
      fun q => ∫ θ, S.indicator F (q, θ) ∂π0.withDensity (g (hp q)) := by
    funext q
    have hs : MeasurableSet {θ : E d | (q, θ) ∈ S} := measurable_prodMk_left hS
    rw [← integral_indicator hs]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [e]
  exact measurable_integral_dens π0 hg hfin hhp (hF.indicator hS)

/-- The mean of `π0.withDensity (g h)` is measurable in `h`. -/
theorem measurable_meanV_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun h => meanV (π0.withDensity (g h))) := by
  have h := measurable_integral_dens_vec π0 hg hfin (hp := id) (hhp := measurable_id) (F := Prod.snd) (hF := measurable_snd)
  simpa [meanV] using h

/-- The second moment of `π0.withDensity (g h)` about a measurable centre is measurable in `h`. -/
theorem measurable_secMom_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) {m : H → E d} (hm : Measurable m) :
    Measurable (fun h => secMom (π0.withDensity (g h)) (m h)) := by
  have hc : ∀ i : Fin d, Measurable fun θ : E d => θ.ofLp i := fun i =>
    (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
  refine Measurable.of_eval_matrix _ fun i j => ?_
  have hF : Measurable fun r : H × E d => (r.2.ofLp i - (m r.1).ofLp i) * (r.2.ofLp j - (m r.1).ofLp j) :=
    (((hc i).comp measurable_snd).sub ((hc i).comp (hm.comp measurable_fst))).mul
      (((hc j).comp measurable_snd).sub ((hc j).comp (hm.comp measurable_fst)))
  exact measurable_integral_dens π0 hg hfin measurable_id hF

/-- The covariance of `π0.withDensity (g h)` is measurable in `h`. -/
theorem measurable_covM_dens (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun h => covM (π0.withDensity (g h))) := by
  have h_mean : Measurable (fun h => meanV (π0.withDensity (g h))) :=
    measurable_meanV_dens π0 hg hfin
  have h_secMom : Measurable (fun h => secMom (π0.withDensity (g h)) (meanV (π0.withDensity (g h)))) :=
    measurable_secMom_dens π0 hg hfin h_mean
  simpa [covM] using h_secMom

end DensMeas

/-! ## The rule along a family of densities, and `Rule.Meas` -/

section RuleMeas

variable {d : ℕ} {H : Type} [MeasurableSpace H]

/-- The live rounds form a measurable set of parameters. -/
theorem measurableSet_liveS_dens (P : SParams) (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    MeasurableSet {h | liveS P d (π0.withDensity (g h))} := by
  have h := (measurable_dLive (d := d) (P.w d)).comp (measurable_covM_dens π0 hg hfin)
  exact measurableSet_le measurable_const h

/-- The dent of the frame of `π0.withDensity (g h)` is measurable in `(h, x, θ)`. -/
theorem measurable_dentS_dens (P : SParams) (hw : P.w d ≠ 0) (hκ : 0 ≤ P.kappa) (hk : 0 ≤ P.k)
    (π0 : Measure (E d)) [SFinite π0] {g : H → E d → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun p : H × E d × E d => dentS P d (π0.withDensity (g p.1)) p.2.1 p.2.2) := by
  have hrOne : 0 ≤ rOne d := by
    rw [rOne]
    positivity
  have h_meas_map : Measurable (fun (p : H × E d × E d) =>
      (covM (π0.withDensity (g p.1)), meanV (π0.withDensity (g p.1)), p.2.1, p.2.2)) := by
    refine Measurable.prod ?_ ?_
    · -- covM (π0.withDensity (g p.1)) is measurable in p
      refine (measurable_covM_dens π0 hg hfin).comp ?_
      exact measurable_fst
    · -- (meanV ..., p.2.1, p.2.2) is measurable
      refine Measurable.prod ?_ ?_
      · -- meanV (π0.withDensity (g p.1)) is measurable in p
        refine (measurable_meanV_dens π0 hg hfin).comp ?_
        exact measurable_fst
      · -- (p.2.1, p.2.2) is measurable
        exact measurable_snd
  have h_eq : (fun (p : H × E d × E d) => dentS P d (π0.withDensity (g p.1)) p.2.1 p.2.2) =
      (fun (q : Matrix (Fin d) (Fin d) ℝ × E d × E d × E d) =>
        dent (frameA (P.w d) q.1) q.2.1 P.kappa P.k (rOne d) q.2.2.2 q.2.2.1) ∘
      (fun (p : H × E d × E d) =>
        (covM (π0.withDensity (g p.1)), meanV (π0.withDensity (g p.1)), p.2.1, p.2.2)) := by
    ext p
    simp [dentS, frameS]
  rw [h_eq]
  exact (measurable_dent_frame hw hκ hk hrOne).comp h_meas_map

/-- The cell map of the frame of `π0.withDensity (g h)` is measurable in `(h, x, θ)`. -/
theorem measurable_cellOf_dens (P : SParams) (hw : P.w d ≠ 0) (π0 : Measure (E d)) [SFinite π0]
    {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun p : H × E d × E d => cellOf (frameS P d (π0.withDensity (g p.1)))
      (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2) := by
  have hcovM := measurable_covM_dens π0 hg hfin
  have hmeanV := measurable_meanV_dens π0 hg hfin
  have hDM := measurable_DM (d := d) hw
  have hcovM' : Measurable (fun p : H × E d × E d => covM (π0.withDensity (g p.1))) :=
    hcovM.comp measurable_fst
  have hmeanV' : Measurable (fun p : H × E d × E d => meanV (π0.withDensity (g p.1))) :=
    hmeanV.comp measurable_fst
  have hDM' : Measurable (fun p : H × E d × E d => DM (P.w d) (covM (π0.withDensity (g p.1)))) :=
    hDM.comp hcovM'
  have hx : Measurable (fun p : H × E d × E d => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hθ : Measurable (fun p : H × E d × E d => p.2.2) :=
    measurable_snd.comp measurable_snd
  have h_tuple : Measurable (fun p : H × E d × E d =>
    (covM (π0.withDensity (g p.1)),
     meanV (π0.withDensity (g p.1)),
     DM (P.w d) (covM (π0.withDensity (g p.1))),
     p.2.1, p.2.2)) := by
    refine Measurable.prodMk hcovM' ?_
    refine Measurable.prodMk hmeanV' ?_
    refine Measurable.prodMk hDM' ?_
    refine Measurable.prodMk hx hθ
  have h_cell := measurable_cellOf_frame (d := d) hw P.k (d : ℝ)
  have h_eq : (fun p : H × E d × E d => cellOf (frameS P d (π0.withDensity (g p.1)))
      (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2) =
    (fun p : Matrix (Fin d) (Fin d) ℝ × E d × ℝ × E d × E d =>
      cellOf (frameA (P.w d) p.1) p.2.1 P.k (d : ℝ) p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∘
    (fun p : H × E d × E d =>
      (covM (π0.withDensity (g p.1)), meanV (π0.withDensity (g p.1)),
       DM (P.w d) (covM (π0.withDensity (g p.1))), p.2.1, p.2.2)) := by
    ext p; rfl
  rw [h_eq]
  exact h_cell.comp h_tuple

/-- Ripeness of each cell is a measurable condition on `(h, x)` (Lemma 9.3). -/
theorem measurableSet_ripe_dens (P : SParams) (hw : P.w d ≠ 0) (π0 : Measure (E d)) [SFinite π0]
    {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) (c : Cell) :
    MeasurableSet {p : H × E d | ripe (π0.withDensity (g p.1)) (frameS P d (π0.withDensity (g p.1)))
      (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2 c} := by
  have hcell := measurable_cellOf_dens P hw π0 hg hfin
  have hS : ∀ c : Cell, MeasurableSet {r : (H × E d) × E d | cellOf (frameS P d (π0.withDensity (g r.1.1)))
      (meanV (π0.withDensity (g r.1.1))) P.k d (dmS P d (π0.withDensity (g r.1.1))) r.1.2 r.2 = c} := fun c =>
    (hcell.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
      (measurableSet_singleton c)
  have hmass : ∀ c : Cell, Measurable fun q : H × E d => (π0.withDensity (g q.1)).real
      (cellSet (frameS P d (π0.withDensity (g q.1))) (meanV (π0.withDensity (g q.1))) P.k d
        (dmS P d (π0.withDensity (g q.1))) q.2 c) := fun c => by
    have h := measurable_measureReal_dens π0 hg measurable_fst (hS c)
    exact h
  have hcov := measurable_covM_dens π0 hg hfin
  have hmean := measurable_meanV_dens π0 hg hfin
  have hF : Measurable fun r : (H × E d) × E d => readT (frameS P d (π0.withDensity (g r.1.1)))
      (meanV (π0.withDensity (g r.1.1))) r.2 r.1.2 ^ 2 := by
    have h1 := (measurable_readT_frame (d := d) hw).comp ((hcov.comp measurable_fst.fst).prodMk
      ((hmean.comp measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd)))
    exact h1.pow_const 2
  have hmom : Measurable fun q : H × E d => ∫ θ in cellSet (frameS P d (π0.withDensity (g q.1)))
      (meanV (π0.withDensity (g q.1))) P.k d (dmS P d (π0.withDensity (g q.1))) q.2 Cell.tail,
      readT (frameS P d (π0.withDensity (g q.1))) (meanV (π0.withDensity (g q.1))) θ q.2 ^ 2
        ∂π0.withDensity (g q.1) :=
    measurable_setIntegral_dens π0 hg hfin measurable_fst (hS Cell.tail) hF
  cases c with
  | tail =>
    simp only [ripe, Set.ofPred_or]
    exact (measurableSet_le measurable_const (hmass Cell.tail)).union (measurableSet_le measurable_const hmom)
  | outer =>
    simp only [ripe]
    exact measurableSet_le measurable_const (hmass Cell.outer)
  | inner =>
    simp only [ripe]
    exact measurableSet_le measurable_const (hmass Cell.inner)
  | regular =>
    simp only [ripe, Set.ofPred_false]
    exact MeasurableSet.empty

/-- The answer of a live round is measurable in `(h, x, θ)`. -/
theorem measurable_ansS_dens (P : SParams) (hw : P.w d ≠ 0) (π0 : Measure (E d)) [SFinite π0]
    {g : H → E d → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (hfin : ∀ h θ, g h θ ≠ ∞) :
    Measurable (fun p : H × E d × E d => ansS P d (π0.withDensity (g p.1)) p.2.1 p.2.2) := by
  classical
  have hcell := measurable_cellOf_dens P hw π0 hg hfin
  have hR : ∀ c : Cell, MeasurableSet {p : H × E d × E d | ripe (π0.withDensity (g p.1))
      (frameS P d (π0.withDensity (g p.1))) (meanV (π0.withDensity (g p.1))) P.k d
      (dmS P d (π0.withDensity (g p.1))) p.2.1 c} := fun c => by
    have h := (measurableSet_ripe_dens P hw π0 hg hfin c).preimage
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd) : Measurable fun p : H × E d × E d => (p.1, p.2.1))
    exact h
  have hT : MeasurableSet {p : H × E d × E d | ripe (π0.withDensity (g p.1))
      (frameS P d (π0.withDensity (g p.1))) (meanV (π0.withDensity (g p.1))) P.k d
      (dmS P d (π0.withDensity (g p.1))) p.2.1 (cellOf (frameS P d (π0.withDensity (g p.1)))
        (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2)} := by
    have e : {p : H × E d × E d | ripe (π0.withDensity (g p.1))
        (frameS P d (π0.withDensity (g p.1))) (meanV (π0.withDensity (g p.1))) P.k d
        (dmS P d (π0.withDensity (g p.1))) p.2.1 (cellOf (frameS P d (π0.withDensity (g p.1)))
          (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2)} =
        ⋃ c : Cell, ((fun p : H × E d × E d => cellOf (frameS P d (π0.withDensity (g p.1)))
          (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2) ⁻¹' {c} ∩
          {p : H × E d × E d | ripe (π0.withDensity (g p.1))
            (frameS P d (π0.withDensity (g p.1))) (meanV (π0.withDensity (g p.1))) P.k d
            (dmS P d (π0.withDensity (g p.1))) p.2.1 c}) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨c, hc, h⟩; rw [hc]; exact h
    rw [e]
    exact MeasurableSet.iUnion fun c => (hcell (measurableSet_singleton c)).inter (hR c)
  have hs : Measurable fun p : H × E d × E d => some (cellOf (frameS P d (π0.withDensity (g p.1)))
      (meanV (π0.withDensity (g p.1))) P.k d (dmS P d (π0.withDensity (g p.1))) p.2.1 p.2.2) :=
    (Measurable.of_discrete (f := (some : Cell → Option Cell))).comp hcell
  exact Measurable.ite hT hs measurable_const

/-- The rule `S'` is measurable along every measurable family of densities: the hypothesis of the Bayes core. -/
theorem ruleS_meas (P : SParams) (hw : P.w d ≠ 0) (hκ : 0 ≤ P.kappa) (hk : 0 ≤ P.k) (π0 : Measure (E d))
    [SFinite π0] : (ruleS d P).Meas π0 := by
  intro H _ g hg hfin _
  have hL : MeasurableSet {p : H × E d × E d | liveS P d (π0.withDensity (g p.1))} :=
    measurable_fst (measurableSet_liveS_dens P π0 hg hfin)
  refine ⟨?_, ?_⟩
  · show Measurable fun p : H × E d × E d => if liveS P d (π0.withDensity (g p.1))
      then ansS P d (π0.withDensity (g p.1)) p.2.1 p.2.2 else none
    exact Measurable.ite hL (measurable_ansS_dens P hw π0 hg hfin) measurable_const
  · show Measurable fun p : H × E d × E d => P.b + if liveS P d (π0.withDensity (g p.1))
      then dentS P d (π0.withDensity (g p.1)) p.2.1 p.2.2 else 0
    exact measurable_const.add
      (Measurable.ite hL (measurable_dentS_dens P hw hκ hk π0 hg hfin) measurable_const)

end RuleMeas

/-! ## Posterior facts for the other modules -/

section PostFacts

variable {d : ℕ} {α : Type} [MeasurableSpace α]

theorem post_absolutelyContinuous (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) :
    post π0 R sc t h ≪ π0 := by
  exact withDensity_absolutelyContinuous π0 _

/-- The posterior lives where the prior lives. -/
theorem post_ae_mem (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) {S : Set (E d)}
    (hS : ∀ᵐ θ ∂π0, θ ∈ S) : ∀ᵐ θ ∂post π0 R sc t h, θ ∈ S := by
  exact (post_absolutelyContinuous π0 R sc t h).ae_le hS

/-- Every posterior has a bounded density with respect to the prior. -/
theorem dens_le_bound (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (t : ℕ) (h : Hist d α) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ θ, dens π0 R sc t h θ ≤ C := by
  induction' t with t ih
  · refine ⟨1, by simp, ?_⟩
    intro θ
    simp [dens]
  · rcases ih with ⟨C, hC_ne_top, hC_bound⟩
    by_cases hcond : (∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0) = 0 ∨
        (∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0) = ∞
    · rw [dens_succ, ite_eq_left hcond]
      exact ⟨C, hC_ne_top, hC_bound⟩
    · rw [dens_succ, ite_eq_right hcond]
      set N := ∫⁻ θ, dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ∂π0 with hN_def
      have hN0 : N ≠ 0 := by
        intro hNzero
        apply hcond
        left
        exact hNzero
      have hNfin : N ≠ ∞ := by
        intro hNinf
        apply hcond
        right
        exact hNinf
      set B := ENNReal.ofReal (Real.sqrt (2 * Real.pi * (noiseVar sc : ℝ)))⁻¹ with hB_def
      have hB_ne_top : B ≠ ∞ := ENNReal.ofReal_ne_top
      have hL_bound (θ : E d) : roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ≤ B := by
        simpa [roundLik, hB_def] using lik_le (R.ans (π0.withDensity (dens π0 R sc t h)) (h.1 t))
          (R.sig (π0.withDensity (dens π0 R sc t h)) (h.1 t)) (noiseVar sc) (h.2.2 t) (h.2.1 t) θ
      set C' := max C (N⁻¹ * (C * B)) with hC'_def
      have hprod_ne_top : N⁻¹ * (C * B) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hN0) (ENNReal.mul_ne_top hC_ne_top hB_ne_top)
      have hC'_ne_top : C' ≠ ∞ := by
        rw [hC'_def]
        intro hmax
        rcases (max_eq_iff.mp hmax) with (⟨hC_eq, _⟩ | ⟨hprod_eq, _⟩)
        · exact hC_ne_top hC_eq
        · exact hprod_ne_top hprod_eq
      refine ⟨C', hC'_ne_top, ?_⟩
      intro θ
      have h_mul : dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ ≤ C * B :=
        mul_le_mul' (hC_bound θ) (hL_bound θ)
      have h_main : N⁻¹ * (dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ) ≤
          N⁻¹ * (C * B) := by
        apply mul_le_mul_of_nonneg_left h_mul
        exact zero_le
      calc
        N⁻¹ * (dens π0 R sc t h θ * roundLik R sc (π0.withDensity (dens π0 R sc t h)) t h θ)
            ≤ N⁻¹ * (C * B) := h_main
        _ ≤ C' := by
          rw [hC'_def]
          exact le_max_right _ _

end PostFacts

/-! ## The deterministic strategy of a fixed tip and noise sequence -/

section Strategy

variable {d : ℕ} {α : Type} [MeasurableSpace α] [Inhabited α]

/-- The plays `x 0, ..., x (t - 1)`, padded with `0`. -/
def padF {t : ℕ} (x : Fin t → E d) : ℕ → E d := fun s => if h : s < t then x ⟨s, h⟩ else 0

/-- The learner whose seed is a list of `t` plays: it plays them in order. -/
def replayPol (d t : ℕ) : Learner (Fin t → E d) d := fun s x _ _ => padF x s

/-- The history replayed from the past plays `x`, for the tip `xo` and the noise sequence `z`. -/
noncomputable def replay (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (xo : E d) (z : ℕ → ℝ) (t : ℕ)
    (x : Fin t → E d) : Hist d α :=
  hist π0 R sc (replayPol d t) t (xo, z, x)

/-- The deterministic strategy of the tip `xo` and the noise sequence `z`: the loss of round `t`, given the past plays
`x`, is the signal of the posterior replayed from `x`, plus `sc z_t`. It reads the past plays only. -/
noncomputable def stratOf (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (xo : E d) (z : ℕ → ℝ) : Strategy d :=
  fun t x _ y => R.sig (post π0 R sc t (replay π0 R sc xo z t x)) y xo + sc * z t

/-- Replaying the plays of a run gives back its history. -/
theorem replay_hist (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) {Ω : Type} (pol : Learner Ω d) (xo : E d)
    (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    replay π0 R sc xo z t (fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i) = hist π0 R sc pol t (xo, z, ω) := by
  let _ : MeasurableSpace Ω := ⊤
  have key : ∀ u ≤ t, hist π0 R sc (replayPol d t) u (xo, z, fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i) =
      hist π0 R sc pol u (xo, z, ω) := by
    intro u
    induction u with
    | zero => intro _; rfl
    | succ u ih =>
      intro hu
      have hu' : u < t := hu
      have h1 := ih hu'.le
      have hplay : play (replayPol d t) u (fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i)
          (hist π0 R sc pol u (xo, z, ω)) = play pol u ω (hist π0 R sc pol u (xo, z, ω)) := by
        show padF (fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i) u = _
        simp only [padF, hu', ↓reduceDIte]
        exact (hist_stable π0 R sc pol (xo, z, ω) hu').1.trans (hist_succ_self π0 R sc pol (xo, z, ω) u).1
      rw [hist_succ, hist_succ, h1]
      dsimp only
      rw [hplay]
  exact key t le_rfl

/-- The transcript of a learner with its seed `ω` against `stratOf` in the noiseless game is the history of the
sample `(xo, z, ω)`: the plays and the observations. -/
theorem transcript_stratOf (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) {Ω : Type} (pol : Learner Ω d)
    (xo : E d) (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    transcript (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω) t =
      (fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i, fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).2.1 i) := by
  induction t with
  | zero =>
    refine Prod.ext (funext fun i => Fin.elim0 i) (funext fun i => Fin.elim0 i)
  | succ t ih =>
    let _ : MeasurableSpace Ω := ⊤
    simp only [transcript]
    rw [ih]
    dsimp only
    have hrep := replay_hist π0 R sc pol xo z ω t
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> dsimp only
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, hist_succ]
        simp only [Hist.push, Fin.val_last, Function.update_self]
        rfl
      · rw [Fin.snoc_castSucc, hist_succ]
        simp only [Hist.push, Fin.val_castSucc]
        rw [Function.update_of_ne j.isLt.ne]
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last, hist_succ]
        simp only [Hist.push, Fin.val_last, Function.update_self, stratOf, hrep, add_zero]
        rfl
      · rw [Fin.snoc_castSucc, hist_succ]
        simp only [Hist.push, Fin.val_castSucc]
        rw [Function.update_of_ne j.isLt.ne]

/-- The point of round `t` against `stratOf` is the play of the history. -/
theorem plays_stratOf (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) {Ω : Type} (pol : Learner Ω d) (xo : E d)
    (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω) t =
      play pol t ω (hist π0 R sc pol t (xo, z, ω)) := by
  unfold plays
  rw [transcript_stratOf π0 R sc pol xo z ω t]
  rfl

/-- The loss of round `t` against `stratOf`, on the run of the learner. -/
theorem lossAd_stratOf (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) {Ω : Type} (pol : Learner Ω d) (xo : E d)
    (z : ℕ → ℝ) (ω : Ω) (t : ℕ) :
    lossAd (stratOf π0 R sc xo z) (fun _ => 0) (plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω)) t =
      fun y => R.sig (post π0 R sc t (hist π0 R sc pol t (xo, z, ω))) y xo + sc * z t := by
  let _ : MeasurableSpace Ω := ⊤
  funext y
  unfold lossAd
  simp [stratOf]
  have h_plays_eq : (fun i : Fin t => (plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω)) i) =
      (fun i : Fin t => (hist π0 R sc pol t (xo, z, ω)).1 i) := by
    funext i
    have hi : (i : ℕ) < t := i.2
    calc
      (plays (stratOf π0 R sc xo z) (fun _ => 0) (fun s => pol s ω)) (i : ℕ)
          = play pol (i : ℕ) ω (hist π0 R sc pol (i : ℕ) (xo, z, ω)) := by
        simpa using plays_stratOf π0 R sc pol xo z ω (i : ℕ)
      _ = (hist π0 R sc pol ((i : ℕ) + 1) (xo, z, ω)).1 (i : ℕ) := by
        simpa using ((hist_succ_self π0 R sc pol (xo, z, ω) (i : ℕ)).1).symm
      _ = (hist π0 R sc pol t (xo, z, ω)).1 (i : ℕ) := by
        simpa using ((hist_stable π0 R sc pol (xo, z, ω) hi).1).symm
      _ = (hist π0 R sc pol t (xo, z, ω)).1 i := rfl
  rw [h_plays_eq]
  rw [replay_hist π0 R sc pol xo z ω t]

omit [MeasurableSpace α] in
/-- `stratOf` reads the past plays only. -/
theorem stratOf_obs (π0 : Measure (E d)) (R : Rule d α) (sc : ℝ) (xo : E d) (z : ℕ → ℝ) (t : ℕ)
    (x : Fin t → E d) (o o' : Fin t → ℝ) : stratOf π0 R sc xo z t x o = stratOf π0 R sc xo z t x o' := rfl

/-- The loss of `stratOf` at a point is measurable in the history. -/
theorem measurable_stratOf [Fintype α] [MeasurableSingletonClass α] (π0 : Measure (E d)) [IsProbabilityMeasure π0]
    (R : Rule d α) (hR : R.Meas π0) (sc : ℝ) (xo : E d) (z : ℕ → ℝ) (t : ℕ) (y : E d) :
    Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => stratOf π0 R sc xo z t h.1 h.2 y := by
  have hrp : ∀ s < t, Measurable fun p : (Fin t → E d) × (Fin s → E d) × (Fin s → ℝ) =>
      replayPol d t s p.1 p.2.1 p.2.2 := by
    intro s hs
    have e : (fun p : (Fin t → E d) × (Fin s → E d) × (Fin s → ℝ) => replayPol d t s p.1 p.2.1 p.2.2) =
        fun p => p.1 ⟨s, hs⟩ := by
      funext p
      simp [replayPol, padF, hs]
    rw [e]
    exact (measurable_pi_apply _).comp measurable_fst
  have hh := measurable_hist π0 R hR sc hrp le_rfl
  obtain ⟨_, hS⟩ := measurable_rule_post π0 R hR sc t
  have hrep : Measurable fun x : Fin t → E d => replay π0 R sc xo z t x :=
    hh.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h2 := hS.comp (((hrep.comp measurable_fst).prodMk (measurable_const.prodMk measurable_const)) :
    Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => (replay π0 R sc xo z t h.1, y, xo))
  exact h2.add measurable_const

end Strategy

/-! ## The mean regret of a round -/

section MeanRegret

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- The mean regret of a round, Lemma 9.5 for the dent: the dent at the tip, on the live rounds, has the mean of the
posterior mean of the dent. -/
theorem regret_round (P : SParams) (hw : P.w d ≠ 0) (hκ : 0 ≤ P.kappa) (hk : 0 ≤ P.k) (hsc : P.sc ≠ 0)
    (π0 : Measure (E d)) [IsProbabilityMeasure π0] (μ : Measure Ω) [SFinite μ] {pol : Learner Ω d} {n : ℕ}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {t : ℕ}
    (ht : t < n) :
    ∫⁻ s, ENNReal.ofReal ((ruleS d P).sig (post π0 (ruleS d P) P.sc t (hist π0 (ruleS d P) P.sc pol t s))
        (play pol t s.2.2 (hist π0 (ruleS d P) P.sc pol t s)) s.1 - P.b) ∂gameLaw π0 μ =
      ∫⁻ s, ∫⁻ θ, ENNReal.ofReal ((ruleS d P).sig (post π0 (ruleS d P) P.sc t (hist π0 (ruleS d P) P.sc pol t s))
          (play pol t s.2.2 (hist π0 (ruleS d P) P.sc pol t s)) θ - P.b)
        ∂post π0 (ruleS d P) P.sc t (hist π0 (ruleS d P) P.sc pol t s) ∂gameLaw π0 μ := by
  have hR := ruleS_meas P hw hκ hk π0
  obtain ⟨_, hS⟩ := measurable_rule_post π0 (ruleS d P) hR P.sc t
  have hxp : Measurable fun q : E d × Hist d (Option Cell) × Ω => play pol t q.2.2 q.2.1 := by
    have h1 := measurable_play (α := Option Cell) (hpol t ht)
    exact h1.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hF : Measurable fun q : E d × Hist d (Option Cell) × Ω => ENNReal.ofReal
      ((ruleS d P).sig (post π0 (ruleS d P) P.sc t q.2.1) (play pol t q.2.2 q.2.1) q.1 - P.b) := by
    have h2 := hS.comp ((measurable_fst.comp measurable_snd).prodMk (hxp.prodMk measurable_fst))
    exact ENNReal.measurable_ofReal.comp (h2.sub measurable_const)
  exact post_disintegrates' π0 μ (ruleS d P) hR hsc hpol ht.le hF

end MeanRegret

end AdversarialBco.Lower.Bayes
