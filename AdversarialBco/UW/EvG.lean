/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCProc
public import AdversarialBco.UW.EvPar
public import AdversarialBco.Poly.Df2EvAdGV

@[expose] public section

/-!
# Event (a) at the level for the reference of Theorem UW

`evGPropUW : EvGPropUW`: on every instance of setting (E) at T4U, event (a) at the level fails with probability at
most `3 δc/7`. The event asks, for `s ≤ τ`, the noise of the unweighted path `|e_s| ≤ x^{1/2}`, the gauge of the
weighted epoch's sample `π(X_s) ≤ L_e^{1/2}` and the draw `|ξ_s|² ≤ (8d/3) x`, at `x = log(14 n/δc)` and
`L_e = 36 log(1/δc)`.

The proof is Theorem U's `EvAd.df2EvGPropAdV_holds` (Poly/Df2EvAdGV.lean) with two changes.

* The gauge part reads the weighted epoch, whose mode before round `s` is measurable in `𝒢 s` (`measurable_modeEW`,
  UW/EvCProc.lean), at the threshold `L_e^{1/2}`, above the spread level `L` of T4U: `pi_tail_at` and
  `pi_round_law_at` are `EvGY.pi_tail` and `EvGY.pi_round_law` at a threshold `s ≥ 2`, and `pi_le_budget_at` gives
  `exp(-2 L (L_e^{1/2} - 2)²) ≤ 2 e^{-x}` from `x ≤ L_e`, `L ≤ L_e`, `L ≥ 504`.
* The levels are those of `δc`: `2 e^{-x} = δc/(7 n)` (`EvP.two_exp_lgW`), three parts per round, `m ≤ n` rounds.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Poly.EvGY

variable {d : ℕ}

/-! ## The gauge tail at a threshold -/

/-- `P(π(μ + T g) > s) ≤ exp(-2 L (s - 2)²)` for `π(μ) ≤ 1`, `‖T‖ ≤ 1/(2 √L)`, `s ≥ 2` (`pi_tail` at a threshold). -/
theorem pi_tail_at (hd : 1 ≤ d) (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : E d) (hmu : gauge K mu ≤ 1)
    (T : E d →L[ℝ] E d) (Le : ℝ) (hLe : 1 ≤ Le) (hT : ‖T‖ ≤ 1 / (2 * Real.sqrt Le)) (s : ℝ) (hs : 2 ≤ s) :
    stdGaussian (E d) {g | s < gauge K (mu + T g)} ≤ ENNReal.ofReal (Real.exp (-(2 * Le * (s - 2) ^ 2))) := by
  have hLe0 : 0 < Le := by linarith
  have hsq : 0 < Real.sqrt Le := Real.sqrt_pos.2 hLe0
  have habs : Absorbent ℝ K :=
    absorbent_nhds_zero (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball)
  by_cases hT0 : ‖T‖ = 0
  · have hT' : T = 0 := norm_eq_zero.1 hT0
    have hempty : {g | s < gauge K (mu + T g)} = (∅ : Set (E d)) := by
      ext g
      simp only [hT', _root_.zero_apply, add_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_lt]
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  have hTpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hT0)
  have hc : ∫ g, gauge K (T g) ∂(stdGaussian (E d)) ≤ 1 := by
    have h1 := gauge_mean_le hd K hK hKc hball T (1 / (2 * Real.sqrt Le)) (by positivity) hT
    have h2 := mw_small hd Le hLe
    calc _ ≤ 1 / (2 * Real.sqrt Le) * pgMw K * Real.sqrt d := h1
      _ = (1 / (2 * Real.sqrt Le) * Real.sqrt d) * pgMw K := by ring
      _ ≤ (1 / (2 * Real.sqrt Le) * Real.sqrt d) * df2Mw d := by gcongr
      _ = 1 / (2 * Real.sqrt Le) * (df2Mw d * Real.sqrt d) := by ring
      _ ≤ 1 / (2 * Real.sqrt Le) * (2 * Real.sqrt Le) := by gcongr
      _ = 1 := by field_simp [hsq.ne']
  have hsub : {g | s < gauge K (mu + T g)} ⊆
      {g | (∫ h, gauge K (T h) ∂(stdGaussian (E d))) + (s - 2) ≤ gauge K (T g)} := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have := gauge_add_le hK habs mu (T g)
    linarith
  have hT2 : 4 * Le * ‖T‖ ^ 2 ≤ 1 := by
    have h1 : ‖T‖ * (2 * Real.sqrt Le) ≤ 1 := (le_div_iff₀ (by linarith)).1 hT
    have h0 : 0 ≤ ‖T‖ * (2 * Real.sqrt Le) := by positivity
    have h3 : (‖T‖ * (2 * Real.sqrt Le)) ^ 2 = 4 * Le * ‖T‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hLe0.le]
      ring
    nlinarith
  refine (measure_mono hsub).trans ((gauge_conc K hK hKc hball T (s - 2) (by linarith)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))))
  rw [le_div_iff₀ (by have := pow_pos hTpos 2; linarith)]
  nlinarith [mul_nonneg (sq_nonneg (s - 2)) (sub_nonneg.2 hT2)]

/-- The gauge in one round, in the coordinates `Fin d → ℝ`, at a state with `π(μ) ≤ 1` and `|A w|² ≤ 2 σ² |w|²`,
`σ² = 1/(8 L)`, at a threshold `s ≥ 2` (`pi_round_law` at a threshold). -/
theorem pi_round_law_at (hd : 1 ≤ d) (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hball : Metric.closedBall 0 1 ⊆ K) (hMw : pgMw K ≤ df2Mw d) (mu : Fin d → ℝ)
    (hmu : gauge K (WithLp.toLp 2 mu) ≤ 1) (A : Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (Le : ℝ) (hLe : 1 ≤ Le) (hA : ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ 2 * (1 / (8 * Le)) * (w ⬝ᵥ w))
    (s : ℝ) (hs : 2 ≤ s) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1)
        {x | s < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} ≤
      ENNReal.ofReal (Real.exp (-(2 * Le * (s - 2) ^ 2))) := by
  set T := (1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A with hTdef
  have hLe_pos : 0 < Le := by linarith
  have hk_pos : 0 ≤ 2 * (1 / (8 * Le)) := by positivity
  have hA_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ Real.sqrt (2 * (1 / (8 * Le))) :=
    toEuclideanCLM_norm_le A (2 * (1 / (8 * Le))) hk_pos hA
  have h_sqrt : Real.sqrt (2 * (1 / (8 * Le))) = 1 / (2 * Real.sqrt Le) := by
    calc
      Real.sqrt (2 * (1 / (8 * Le))) = Real.sqrt ((1 : ℝ) / (4 * Le)) := by
        field_simp [hLe_pos.ne.symm]
        ring_nf
      _ = Real.sqrt 1 / Real.sqrt (4 * Le) := by rw [Real.sqrt_div (by norm_num) _]
      _ = 1 / Real.sqrt (4 * Le) := by norm_num
      _ = 1 / (Real.sqrt 4 * Real.sqrt Le) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
      _ = 1 / (2 * Real.sqrt Le) := by norm_num
  have hT_norm : ‖T‖ ≤ 1 / (2 * Real.sqrt Le) := by
    rw [hTdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - lam)]
    calc (1 - lam) * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ 1 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ 1 / (2 * Real.sqrt Le) := by rw [one_mul, ← h_sqrt]; exact hA_norm
  have h_meas : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp 2 _
  have h_set_eq : {x : Fin d → ℝ | s < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)))} =
      (WithLp.toLp 2) ⁻¹' {g : EuclideanSpace ℝ (Fin d) | s < gauge K (WithLp.toLp 2 mu + T g)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have h1 : WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x)) =
        WithLp.toLp 2 mu + WithLp.toLp 2 ((1 - lam) • (A *ᵥ x)) := by
      rw [WithLp.toLp_add]
    have h2 : WithLp.toLp 2 ((1 - lam) • (A *ᵥ x)) = (1 - lam) • WithLp.toLp 2 (A *ᵥ x) := by
      rw [WithLp.toLp_smul]
    have h3 : WithLp.toLp 2 (A *ᵥ x) = Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x) := by
      rw [toEuclideanCLM_toLp]
    calc
      s < gauge K (WithLp.toLp 2 (mu + (1 - lam) • (A *ᵥ x))) ↔
          s < gauge K (WithLp.toLp 2 mu + WithLp.toLp 2 ((1 - lam) • (A *ᵥ x))) := by
        rw [h1]
      _ ↔ s < gauge K (WithLp.toLp 2 mu + (1 - lam) • WithLp.toLp 2 (A *ᵥ x)) := by
        rw [h2]
      _ ↔ s < gauge K (WithLp.toLp 2 mu + (1 - lam) • (Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 x))) := by
        rw [h3]
      _ ↔ s < gauge K (WithLp.toLp 2 mu + ((1 - lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 x)) := by
        simp [_root_.smul_apply]
      _ ↔ s < gauge K (WithLp.toLp 2 mu + T (WithLp.toLp 2 x)) := by
        rw [hTdef]
  have h_gauge_measurable :
      MeasurableSet {g : EuclideanSpace ℝ (Fin d) | s < gauge K (WithLp.toLp 2 mu + T g)} := by
    have h_cont : Continuous (gauge K : EuclideanSpace ℝ (Fin d) → ℝ) :=
      continuous_gauge hK (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball)
    have h_comp : Continuous fun g : EuclideanSpace ℝ (Fin d) => gauge K (WithLp.toLp 2 mu + T g) :=
      h_cont.comp (continuous_const.add T.continuous)
    exact measurableSet_lt measurable_const h_comp.measurable
  rw [h_set_eq, ← Measure.map_apply h_meas h_gauge_measurable, map_pi_eq_stdGaussian]
  exact pi_tail_at hd K hK hKc hball hMw (WithLp.toLp 2 mu) hmu T Le hLe hT_norm s hs

/-- The gauge at the level costs no more than the budget of a round: `exp(-2 L (√L_e - 2)²) ≤ 2 e^{-x}` for
`L ≥ 504`, `L ≤ L_e`, `x ≤ L_e`. -/
theorem pi_le_budget_at (Le le lg : ℝ) (hLe : 504 ≤ Le) (hle : Le ≤ le) (hlg : lg ≤ le) :
    Real.exp (-(2 * Le * (Real.sqrt le - 2) ^ 2)) ≤ 2 * Real.exp (-lg) := by
  have hle0 : 0 ≤ le := by linarith
  have hr2 : Real.sqrt le ^ 2 = le := Real.sq_sqrt hle0
  have hr0 : 0 ≤ Real.sqrt le := Real.sqrt_nonneg _
  have hr22 : 22 ≤ Real.sqrt le := by nlinarith
  have h1 : Real.sqrt le ^ 2 / 2 ≤ (Real.sqrt le - 2) ^ 2 := by nlinarith
  have h2 : Le * Real.sqrt le ^ 2 ≤ 2 * Le * (Real.sqrt le - 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Le)]
  have h3 : lg ≤ 2 * Le * (Real.sqrt le - 2) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Le - 1) (sq_nonneg (Real.sqrt le))]
  have := Real.exp_pos (-lg)
  calc Real.exp (-(2 * Le * (Real.sqrt le - 2) ^ 2)) ≤ Real.exp (-lg) := Real.exp_le_exp.2 (by linarith)
    _ ≤ 2 * Real.exp (-lg) := by linarith

/-! ## The gauge in one round of the weighted epoch -/

section Pi

variable {Θ : Type} [MeasurableSpace Θ]

variable (p : Df2OPar) (s0 : ℝ) (Kθ : Θ → Set (E d)) in
/-- The event of the gauge at a good state, as a set of `((θ, mode), ξ)`, at the table `p` and the threshold `s0`. -/
def piSetW : Set ((Θ × Df2Mode d) × (Fin d → ℝ)) :=
  {x | x.1.2.code.1 = 2 ∧ gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1 ∧
    x.1.2.code.2.A ∈ spreadSet (2 * p.sig2) ∧
    s0 < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOfE p x.1.2.code.2 x.2))}

theorem measurableSet_piSetW (p : Df2OPar) (s0 : ℝ) {Kθ : Θ → Set (E d)}
    (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) : MeasurableSet (piSetW p s0 Kθ) := by
  have hcode : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code :=
    ApMeas.measurable_mode_code.comp (measurable_snd.comp measurable_fst)
  have hst : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code.2 := measurable_snd.comp hcode
  have hq : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.1 := measurable_fst.comp measurable_fst
  have h1 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) | x.1.2.code.1 = 2} :=
    (measurable_fst.comp hcode) (measurableSet_singleton 2)
  have hmu : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      (x.1.1, (WithLp.toLp 2 x.1.2.code.2.mu : E d)) :=
    hq.prodMk ((WithLp.measurable_toLp 2 _).comp (ApMeas.measurable_st_mu.comp hst))
  have hg2 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) := by
    have h := hg.comp hmu
    exact h
  have h2 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1} := measurableSet_le hg2 measurable_const
  have h3 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) | x.1.2.code.2.A ∈ spreadSet (2 * p.sig2)} :=
    (ApMeas.measurable_st_A.comp hst) (isClosed_spread _).measurableSet
  have hX : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      (x.1.1, (WithLp.toLp 2 (xOfE p x.1.2.code.2 x.2) : E d)) := by
    have hx : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => (x.1.2.code.2, x.2) := hst.prodMk measurable_snd
    have h := (measurable_xOfE p).comp hx
    exact hq.prodMk ((WithLp.measurable_toLp 2 _).comp h)
  have hg4 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 (xOfE p x.1.2.code.2 x.2)) := by
    have h := hg.comp hX
    exact h
  have h4 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      s0 < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOfE p x.1.2.code.2 x.2))} :=
    measurableSet_lt measurable_const hg4
  exact h1.inter (h2.inter (h3.inter h4))

theorem two_le_sqrt_leW {n : ℕ} {ρ : RefW} (hreg : RegimeW d n ρ) : 2 ≤ Real.sqrt (leW ρ.δc) := by
  have hL := EvP.Le_ge hreg
  have hle := EvP.Le_le_leW hreg
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  calc (2 : ℝ) = Real.sqrt 4 := h4.symm
    _ ≤ Real.sqrt (leW ρ.δc) := Real.sqrt_le_sqrt (by linarith)

/-- The gauge in one round of the weighted epoch: the event of the body parameter, the mode before round `s` and
`ξ_s` has probability at most `exp(-2 L (√L_e - 2)²)`. -/
theorem pi_roundW {n : ℕ} {ρ : RefW} (hreg : RegimeW d n ρ) {m : ℕ} {V : Type} [MeasurableSpace V]
    {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ} {apθ : V → ApFun d}
    (hbody : ∀ q, Df2Body d (parW d n ρ.u).R (Kθ q)) (hmeas : Df2EpochMeasV (parW d n ρ.u) n m Kθ gθ apθ)
    {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (θ : ℕ → Ω → Θ) (ψ : ℕ → Ω → V) (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ)
    (e : ℕ → Ω → ℝ) (hθ : ∀ s, Measurable[𝒢 s] (θ s)) (hψ : ∀ s, Measurable[𝒢 (s + 1)] (ψ s))
    (hE : Df2SetE d μ 𝒢 ξ e) {s : ℕ} (hs : s ≤ m) :
    μ {ω | ((θ 0 ω, modeEW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω) s), ξ s ω) ∈
        piSetW (parW d n ρ.u) (Real.sqrt (leW ρ.δc)) Kθ} ≤
      ENNReal.ofReal (Real.exp (-(2 * (parW d n ρ.u).Le * (Real.sqrt (leW ρ.δc) - 2) ^ 2))) := by
  have hz : Measurable[𝒢 s] fun ω =>
      (θ 0 ω, modeEW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω) s) :=
    ((hθ 0).mono (𝒢.mono (Nat.zero_le s)) le_rfl).prodMk
      (measurable_modeEW (parW d n ρ.u) n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas
        s hs)
  have hx : Measurable[m0] (ξ s) := (hE.xi_meas s).mono (𝒢.le _) le_rfl
  have hL := EvP.Le_ge hreg
  have hs2 := two_le_sqrt_leW hreg
  obtain ⟨hlam0, hlam1⟩ := EvP.lam_bounds hreg
  refine freeze_le (𝒢 s) μ (𝒢.le s) _ (ξ s) hz hx (hE.xi_indep s) _ (measurableSet_piSetW _ _ hmeas.1) _ ?_
  intro a
  rw [hE.xi_law s]
  by_cases hgood : a.2.code.1 = 2 ∧ gauge (Kθ a.1) (WithLp.toLp 2 a.2.code.2.mu) ≤ 1 ∧
      a.2.code.2.A ∈ spreadSet (2 * (parW d n ρ.u).sig2)
  · obtain ⟨-, hmu, hA⟩ := hgood
    obtain ⟨hKcv, hKc, hball, -, hMw⟩ := hbody a.1
    refine (measure_mono fun x hx => hx.2.2.2).trans ?_
    refine pi_round_law_at hreg.hd (Kθ a.1) hKcv hKc hball hMw a.2.code.2.mu hmu a.2.code.2.A
      (parW d n ρ.u).lam hlam0.le hlam1 (parW d n ρ.u).Le (by linarith) ?_ _ hs2
    intro w
    have := hA w
    rwa [EvP.sig2_eq] at this
  · have : Prod.mk a ⁻¹' piSetW (parW d n ρ.u) (Real.sqrt (leW ρ.δc)) Kθ = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => hgood ⟨hx.1, hx.2.1, hx.2.2.1⟩
    rw [this, measure_empty]
    exact zero_le

end Pi

/-! ## The budget -/

/-- **Event (a) at the level** fails with probability at most `3 δc/7` on every instance of setting (E) at T4U. -/
theorem evGPropUW : EvGPropUW := by
  intro d n m ρ hreg hm1 hmn Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  show μ {ω | ¬ EvGW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) (pathP gθ θ ξ e ω)
      (pathW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω)) (lgW n ρ.δc) (leW ρ.δc) m} ≤
    ENNReal.ofReal (3 / 7 * ρ.δc)
  have hx : ∀ s, Measurable[m0] (ξ s) := fun s => (hE.xi_meas s).mono (𝒢.le _) le_rfl
  have heps0 := EvP.eps_pos hreg
  have heps1 := EvP.eps_lt_one hreg
  have hlam := EvP.lam_pos hreg
  have hlg0 := EvP.lgW_nonneg hreg
  have hdc := hreg.dc_pos
  have hsub : {ω | ¬ EvGW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) (pathP gθ θ ξ e ω)
        (pathW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω)) (lgW n ρ.δc) (leW ρ.δc) m} ⊆
      ⋃ s ∈ Finset.range m,
        ({ω | Real.sqrt (lgW n ρ.δc) < |e s ω|} ∪
          {ω | ((θ 0 ω, modeEW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω) s), ξ s ω) ∈
            piSetW (parW d n ρ.u) (Real.sqrt (leW ρ.δc)) Kθ} ∪
          {ω | 8 * d / 3 * lgW n ρ.δc < ξ s ω ⬝ᵥ ξ s ω}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, EvGW, not_forall] at hω
    obtain ⟨s, hs, hfail⟩ := hω
    set c := ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω with hc
    set π := pathP gθ θ ξ e ω with hπ
    set πw := pathW c ρ.b0 ρ.y0 π with hπw
    have hτ := EvGY.tau_lt c πw hm1
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨s, by omega, ?_⟩
    by_cases h1 : |e s ω| ≤ Real.sqrt (lgW n ρ.δc)
    · by_cases h3 : ξ s ω ⬝ᵥ ξ s ω ≤ 8 * d / 3 * lgW n ρ.δc
      · have h2 : ¬ gauge c.Kt (WithLp.toLp 2 (c.X πw s)) ≤ Real.sqrt (leW ρ.δc) :=
          fun h2 => hfail ⟨h1, h2, h3⟩
        refine Or.inl (Or.inr ?_)
        have hp : LPar c πw := ⟨EvP.sig2_pos hreg, EvP.de_pos hreg, EvP.eta_kap_nonneg hreg, heps1,
          (hbody (θ 0 ω)).2.2.1 (Metric.mem_closedBall_self zero_le_one), rfl⟩
        have hH : ∀ u < c.tau πw m, ∀ v, 0 ≤ df2Sq (c.sHess πw u) v := fun u hu v =>
          sHess_nonneg c πw u (hbody (θ 0 ω)) (EvAd.admAd Kθ gθ hadm θ hK ω u (by omega)) heps0 heps1 hlam v
        have hI := linv_le_tau c πw hp (fun s => hap (ψ s ω)) hH s hs
        have hmode : modeEW c ρ.b0 ρ.y0 π s = .run (c.st πw s) := by
          rw [← mode_pathW]
          exact hI.run
        show (modeEW c ρ.b0 ρ.y0 π s).code.1 = 2 ∧
          gauge (Kθ (θ 0 ω)) (WithLp.toLp 2 (modeEW c ρ.b0 ρ.y0 π s).code.2.mu) ≤ 1 ∧
          (modeEW c ρ.b0 ρ.y0 π s).code.2.A ∈ spreadSet (2 * (parW d n ρ.u).sig2) ∧
          Real.sqrt (leW ρ.δc) <
            gauge (Kθ (θ 0 ω)) (WithLp.toLp 2 (xOfE (parW d n ρ.u) (modeEW c ρ.b0 ρ.y0 π s).code.2 (ξ s ω)))
        rw [hmode]
        exact ⟨rfl, gauge_le_one_of_keps _ _ heps0.le heps1 _ hI.mu, fun w => hI.A_sq_le c πw hp w,
          lt_of_not_ge h2⟩
      · exact Or.inr (lt_of_not_ge h3)
    · exact Or.inl (Or.inl (lt_of_not_ge h1))
  have hb : ∀ s ∈ Finset.range m,
      μ ({ω | Real.sqrt (lgW n ρ.δc) < |e s ω|} ∪
          {ω | ((θ 0 ω, modeEW (ctxP (parW d n ρ.u) n Kθ apθ θ ψ ω) ρ.b0 ρ.y0 (pathP gθ θ ξ e ω) s), ξ s ω) ∈
            piSetW (parW d n ρ.u) (Real.sqrt (leW ρ.δc)) Kθ} ∪
          {ω | 8 * d / 3 * lgW n ρ.δc < ξ s ω ⬝ᵥ ξ s ω}) ≤
        ENNReal.ofReal (3 * (ρ.δc / (7 * n))) := by
    intro s hs
    have hsm : s ≤ m := (Finset.mem_range.1 hs).le
    have hle : 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance ≤ m0 := sup_le (𝒢.le s) (hx s).comap_le
    have hN := noise_round μ _ hle (e s) ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.e_int s) (hE.e_exp s) _ hlg0
    have hG := gauss_round hreg.hd μ (ξ s) (hx s) (hE.xi_law s) (lgW n ρ.δc)
    have hPi := (pi_roundW hreg hbody hmeas μ 𝒢 θ ψ hK ξ e hθ hψ hE hsm).trans
      (ENNReal.ofReal_le_ofReal (pi_le_budget_at _ _ _ (by linarith [EvP.Le_ge hreg]) (EvP.Le_le_leW hreg)
        (EvP.lgW_le_leW hreg)))
    rw [EvP.two_exp_lgW hreg.hn hdc] at hN hG hPi
    have h0 : 0 ≤ ρ.δc / (7 * n) := by positivity
    have h3 : ENNReal.ofReal (3 * (ρ.δc / (7 * n))) =
        ENNReal.ofReal (ρ.δc / (7 * n)) + ENNReal.ofReal (ρ.δc / (7 * n)) + ENNReal.ofReal (ρ.δc / (7 * n)) := by
      rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0]
      ring_nf
    rw [h3]
    exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hN hPi)) hG)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ Finset.range m, ENNReal.ofReal (3 * (ρ.δc / (7 * n))) := Finset.sum_le_sum hb
    _ = ENNReal.ofReal (m * (3 * (ρ.δc / (7 * n)))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (3 / 7 * ρ.δc) := by
      apply ENNReal.ofReal_le_ofReal
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hreg.hn
      calc (m : ℝ) * (3 * (ρ.δc / (7 * n))) ≤ n * (3 * (ρ.δc / (7 * n))) :=
            mul_le_mul_of_nonneg_right hmn' (by positivity)
        _ = 3 / 7 * ρ.δc := by field_simp

end AdversarialBco.UW
