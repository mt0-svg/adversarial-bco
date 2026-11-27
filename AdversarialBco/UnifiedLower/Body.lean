/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.StopTop
public import AdversarialBco.Poly.PgProcProof
public import AdversarialBco.StatementUnifiedLower

@[expose] public section

/-!
# Clauses (a) and (b) of `TheoremLowerU` on every body of the class

The strategy of Theorem lowerbody (the tip `x°` and the clamped noise `z` fixed, `stratOf`, Conj1Lower/Top.lean) is
more than `StratsLip`: on a body inside `B(0, R0)` its losses take values in `[1/8, 7/8]` (the offset `b = 1/4`, the
dent between `0` and `L (R0 + 1/2) + g ≤ 1/2`, the clamped noise in `[-1/8, 1/8]`) and are `L`-Lipschitz on all of
`ℝ^d` with `L = σ/R0` (Lemma LEGAL, `dentS_lipschitz`, is global). The class `StratsMid K n L` records this, and:

* `stratOf_mid`: the strategy of a tip and a clamped noise sequence is in `StratsMid K n L`;
* `lowerBody_mid`, `lowerBodyProb_mid`: Corollary RIPE-K-B (`lowerBody_of_inputs_ext`, R0Ext.lean) and Corollary
  LU-P (`lowerBodyProb_of_inputs_ext`, StopTop.lean) with the strategy in `StratsMid K n (sigB n / R0)`, their proofs
  copied with `stratOf_mid` in place of `stratOf_mem`;
* `pullStrat_mem_mid`: the pull-back by an affine map `T` keeps the class, the Lipschitz constant multiplied by that of
  `T` (Lemma AFF, the paper's affine invariance, with the global constant);
* `exists_position` (Lemma POS, the paper's position lemma): every body of `BodyU` has an affine image between
  `B(0, 1/2)` and `B(0, 67 d (ln(2d + 2))^{1/2})`, from Theorem PG (`Poly.pgThm`) at `δ = 1/2`; the Lipschitz constant
  of such a position is at most `R''/r0` (`dist_le_of_ball_image`), so the pulled-back losses are
  `1/(8 r0)`-Lipschitz;
* `lowerU_mean`, `lowerU_prob`: clauses (a) and (b) of `TheoremLowerU`.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

namespace AdversarialBco.UnifiedLower.Body

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Top AdversarialBco.Lower.Stop

variable {d : ℕ}

/-! ## The class of the strategy of the tip -/

/-- The strategies of `Strats K n` whose loss, for `t < n` and every history, reads the past points only, takes values
in `[1/8, 7/8]` on `K` and is `L`-Lipschitz on all of `E d`. -/
def StratsMid (K : Set (E d)) (n : ℕ) (L : ℝ) : Set (Strategy d) :=
  {σ | σ ∈ Strats K n ∧ ∀ t < n, ∀ (x : Fin t → E d) (o o' : Fin t → ℝ), σ t x o = σ t x o' ∧
    (∀ y ∈ K, 1 / 8 ≤ σ t x o y ∧ σ t x o y ≤ 7 / 8) ∧ ∀ y z : E d, |σ t x o y - σ t x o z| ≤ L * dist y z}

/-- The class `StratsMid` at a constant at most `1/(4 r0)` is inside `StratsLowU K n r0`. -/
theorem stratsMid_lowU {K : Set (E d)} {n : ℕ} {L r0 : ℝ} (hr0 : 0 < r0) (hL : L ≤ 1 / (4 * r0))
    {σ : Strategy d} (hσ : σ ∈ StratsMid K n L) : σ ∈ StratsLowU K n r0 := by
  refine ⟨hσ.1, fun t ht x o o' => ⟨(hσ.2 t ht x o o').1, (hσ.2 t ht x o o').2.1, fun y z => ?_⟩⟩
  have h := (hσ.2 t ht x o o').2.2 y z
  have h4 : 0 < 4 * r0 := by positivity
  calc |σ t x o y - σ t x o z| ≤ L * dist y z := h
    _ ≤ 1 / (4 * r0) * dist y z := mul_le_mul_of_nonneg_right hL dist_nonneg
    _ = dist y z / (4 * r0) := by ring

section Tip

variable {R0 : ℝ}

/-- Lemma LEGAL-K with the range and the global constant: on a convex body `K` inside `B(0, R0)`, the strategy of a
tip and a noise sequence with `|σ z_i| ≤ 1/8` is in `StratsMid K n L`. -/
theorem stratOf_mid (I : Inputs) {P : SParams} (hP : Good P d R0) {K : Set (E d)} (hK : Convex ℝ K)
    (hKR : K ⊆ Metric.closedBall (0 : E d) R0) (n : ℕ) (xo : E d) (z : ℕ → ℝ) (hz : ∀ i, |P.sc * z i| ≤ 1 / 8) :
    stratOf (prior d (1 / 2)) (ruleS d P) P.sc xo z ∈ StratsMid K n P.L := by
  refine ⟨(stratOf_mem I hP hK hKR n xo z hz).1, fun t _ x o o' => ⟨rfl, fun y hy => ?_, fun y y' => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := sig_post_bounds I hP t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x) (hKR hy) xo
    obtain ⟨h3, h4⟩ := abs_le.1 (hz t)
    have := hP.rng
    have := hP.b_eq
    simp only [stratOf]
    constructor <;> linarith
  · have hS := (post_cov I hP P.sc t (replay (prior d (1 / 2)) (ruleS d P) P.sc xo z t x)).1
    simp only [stratOf, ruleS_sig, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub]
    rw [dist_eq_norm]
    split_ifs
    · exact dentS_lipschitz hP hS y y' xo
    · simp only [sub_self, abs_zero]
      exact mul_nonneg hP.L_pos.le (norm_nonneg _)

end Tip

/-! ## Corollaries RIPE-K-B and LU-P with the class `StratsMid` -/

section Top

variable {R0 : ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- Corollary RIPE-K-B (`lowerBody_of_inputs_ext`, R0Ext.lean) with the strategy in `StratsMid K n (sigB n / R0)`; the
proof is that of `lowerBody_of_inputs_ext` with `stratOf_mid` in place of `stratOf_mem`. -/
theorem lowerBody_mid (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0)
    (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsMid K n (sigB n / R0), Integrable (fun ω => regretAd K σ (fun t => pol t ω) n) μ ∧
      7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd K σ (fun t => pol t ω) n ∂μ := by
  have hP := good_pK_ext hd hn hR1 hRk
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hbal := ripeK_balance_ext hd hn hR1 hRk (gameFacts_ext I hd hn hR1 hRk μ hpolB)
    (ER := ∫ s, regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)
      ∂gameLaw (prior d (1 / 2)) μ)
    (by rw [sum_Df_eq I hP μ hpolB]; exact coupling I hP μ hn1 hpolB)
  rw [integral_gameLaw_assoc (prior d (1 / 2)) μ
    (fun s => regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2))] at hbal
  have hm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω =>
      regG (prior d (1 / 2)) (pK d n R0) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2) :=
    (measurable_regG hP hpolB).comp ((measurable_fst.comp measurable_fst).prodMk
      (((measurable_clampZ _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  have hb : ∀ p : (E d × (ℕ → ℝ)) × Ω,
      |regG (prior d (1 / 2)) (pK d n R0) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2)| ≤ n / 2 := fun p =>
    abs_le.2 ⟨by linarith [regG_nonneg hP (prior d (1 / 2)) pol n (p.1.1, clampZ (ellB n) p.1.2, p.2),
      (by positivity : (0 : ℝ) ≤ n / 2)], regG_le I hP hpolB _⟩
  have hN : ((prior d (1 / 2)).prod gaussStream)
      {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} = 0 := by
    have h0 := ae_iff.1 (prior_ae_mem d (1 / 2))
    have hs : {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} =
        {θ | θ ∉ Metric.closedBall (0 : E d) (1 / 2)} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, h0, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((prior d (1 / 2)).prod gaussStream) μ hm hb hN
  have ha1 : a.1 ∈ Metric.closedBall (0 : E d) (1 / 2) := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ K := hK1 ha1
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hz : ∀ i, |(pK d n R0).sc * clampZ (ellB n) a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hP.sc_pos, ← sigB_mul_ellB hn1]
    exact mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hP.sc_pos.le
  have hσ := stratOf_mid I hP hK hK2 n a.1 (clampZ (ellB n) a.2) hz
  refine ⟨_, hσ, integrable_regretAd_stratOf I hP μ hpolB hxo _, ?_⟩
  have he : (fun ω => regretAd K
      (stratOf (prior d (1 / 2)) (ruleS d (pK d n R0)) (pK d n R0).sc a.1 (clampZ (ellB n) a.2))
        (fun t => pol t ω) n) =
      fun ω => regG (prior d (1 / 2)) (pK d n R0) pol n (a.1, clampZ (ellB n) a.2, ω) :=
    funext fun ω => regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  rw [he]
  exact hbal.trans ha

/-- (LU-P), the derandomisation (`derand_prob`, StopTop.lean) with the strategy in `StratsMid K n P.L`. -/
theorem derand_prob_mid (I : Inputs) {P : SParams} (hP : Good P d R0) {n : ℕ} (hsc : P.sc * ellB n ≤ 1 / 8)
    {K : Set (E d)} (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K)
    (hK2 : K ⊆ Metric.closedBall 0 R0) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) {θ pr : ℝ}
    (hpr : pr ≤ (gameLaw (prior d (1 / 2)) μ).real
      {s | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)}) :
    ∃ σ ∈ StratsMid K n P.L, Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      ENNReal.ofReal pr ≤ μ {ω | θ ≤ regretAd K σ (fun t => pol t ω) n} := by
  have hπ := isProbabilityMeasure_prior d (show (0 : ℝ) < 1 / 2 by norm_num)
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hm := measurable_regG hP hpolB
  have hmc : Measurable fun s : Sample d Ω => (s.1, clampZ (ellB n) s.2.1, s.2.2) :=
    measurable_fst.prodMk (((measurable_clampZ _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  set A := {s : Sample d Ω | θ ≤ regG (prior d (1 / 2)) P pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} with hA_def
  have hA : MeasurableSet A := measurableSet_le measurable_const (hm.comp hmc)
  have hassoc : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => ((p.1.1, p.1.2, p.2) : Sample d Ω) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hGm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) :=
    (measurable_const.indicator hA).comp hassoc
  have hGb : ∀ p : (E d × (ℕ → ℝ)) × Ω, |A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2)| ≤ 1 := fun p => by
    by_cases hp : ((p.1.1, p.1.2, p.2) : Sample d Ω) ∈ A
    · rw [Set.indicator_of_mem hp, Pi.one_apply, abs_one]
    · rw [Set.indicator_of_notMem hp, abs_zero]
      norm_num
  have hN : ((prior d (1 / 2)).prod gaussStream)
      {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} = 0 := by
    have h0 := ae_iff.1 (prior_ae_mem d (1 / 2))
    have hs : {a : E d × (ℕ → ℝ) | a.1 ∉ Metric.closedBall (0 : E d) (1 / 2)} =
        {θ | θ ∉ Metric.closedBall (0 : E d) (1 / 2)} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, h0, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((prior d (1 / 2)).prod gaussStream) μ hGm hGb hN
  have ha1 : a.1 ∈ Metric.closedBall (0 : E d) (1 / 2) := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ K := hK1 ha1
  have hℓ : 0 ≤ ellB n := Real.sqrt_nonneg _
  have hz : ∀ i, |P.sc * clampZ (ellB n) a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hP.sc_pos]
    exact (mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hP.sc_pos.le).trans hsc
  have hσ := stratOf_mid I hP hK hK2 n a.1 (clampZ (ellB n) a.2) hz
  have hmω : Measurable fun ω : Ω => regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) :=
    hm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hω : ∀ ω, regretAd K (stratOf (prior d (1 / 2)) (ruleS d P) P.sc a.1 (clampZ (ellB n) a.2))
      (fun t => pol t ω) n = regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω) := fun ω =>
    regretAd_stratOf hP (prior d (1 / 2)) pol n hxo _ ω
  refine ⟨_, hσ, ?_, ?_⟩
  · simp only [hω]
    exact hmω
  · simp only [hω]
    set B := {ω : Ω | θ ≤ regG (prior d (1 / 2)) P pol n (a.1, clampZ (ellB n) a.2, ω)} with hB_def
    have hB : MeasurableSet B := measurableSet_le measurable_const hmω
    have h1 : ∫ p, A.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) ∂((prior d (1 / 2)).prod gaussStream).prod μ =
        (gameLaw (prior d (1 / 2)) μ).real A :=
      (integral_gameLaw_assoc (prior d (1 / 2)) μ (A.indicator 1)).symm.trans (integral_indicator_one hA)
    have h2 : ∫ ω, A.indicator (1 : Sample d Ω → ℝ) (a.1, a.2, ω) ∂μ = μ.real B := by
      rw [← integral_indicator_one hB]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      beta_reduce
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ((a.1, a.2, ω) : Sample d Ω) ∈ A from hω)]
        rfl
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ((a.1, a.2, ω) : Sample d Ω) ∉ A from hω)]
    have ha' : (gameLaw (prior d (1 / 2)) μ).real A ≤ μ.real B := by
      rw [← h1, ← h2]
      exact ha
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ B)]
    exact hpr.trans ha'

/-- Corollary LU-P (`lowerBodyProb_of_inputs_ext`, StopTop.lean) with the strategy in `StratsMid K n (sigB n / R0)`;
the proof is that of `lowerBodyProb_of_inputs_ext` with `derand_prob_mid` in place of `derand_prob`. -/
theorem lowerBodyProb_mid (I : Inputs) {n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)}
    (hK : Convex ℝ K) (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0)
    (hR1 : 1 ≤ R0) (hRk : R0 ≤ d * kRipe d) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd K n pol) :
    ∃ σ ∈ StratsMid K n (sigB n / R0), Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (1 / 2 : ℝ≥0∞) ≤ μ {ω | 28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        regretAd K σ (fun t => pol t ω) n} := by
  have hP := good_pK_ext hd hn hR1 hRk
  have hG := isProbabilityMeasure_gameLaw (prior d (1 / 2)) μ
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hdim := ripeB_dim d hdR
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hn0 : 0 < n := by omega
  have hn4 := ripeB_n d n hdR hnR
  obtain ⟨hs0, hs4⟩ := ripeB_sig d n hdR hnR
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hR0 : 0 < R0 := by linarith
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hΓ : 4 ≤ gamR d n := gamR_ge d n (by linarith) hn4
  have h16 := (ripeK_params_ext hd hn hR1 hRk).2.2.2
  have hX : Real.exp 1 / 2 ≤ xCount d ((pK d n R0).w d) := by
    have := Real.exp_one_lt_d9
    exact le_trans (by linarith) h16
  have hxc : 16 ≤ xCount d ((pK d n R0).w d) := h16
  have hN : 0 < nStar d ((pK d n R0).w d) := by
    have h1 := nStar_ge_x d ((pK d n R0).w d) (by linarith)
    have hpos : 0 < xCount d ((pK d n R0).w d) / 2 := by linarith
    have h8 : 1 ≤ Real.log (xCount d ((pK d n R0).w d) / 2) := by
      rw [Real.le_log_iff_exp_le hpos]
      have := Real.exp_one_lt_d9
      linarith
    nlinarith
  set Y := 1 / 10 ^ 5 * sigB n * ((d : ℝ) * Real.sqrt d) * Real.sqrt (n * gamR d n) / kRipe d with hY_def
  have hthr := ripe_prob_threshold d n hdR hnR
  rw [← hY_def] at hthr
  have hθ0 : 0 < 28 / 10 ^ 10 * ((d : ℝ) * Real.sqrt d) * Real.sqrt n / Real.log d := by
    have := ripeB_log d hdR
    have : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnn
    positivity
  set x := Y - 1 / 2 - sigB n * Real.sqrt n with hx_def
  have hsq : 0 ≤ sigB n * Real.sqrt n := mul_nonneg hs0.le (Real.sqrt_nonneg _)
  have hx : 0 ≤ x := by linarith
  have hfacts := stopFacts_of_good I hP hX hN μ hn0 hpolB hx
  have hYx : x + 1 / 2 + (pK d n R0).sc * Real.sqrt n = Y := by
    change x + 1 / 2 + sigB n * Real.sqrt n = Y
    rw [hx_def]
    ring
  rw [hYx] at hfacts
  have hq := stop_rate_K hd1 hs0 hR1 hn4 hdim (R2_ripe_Kext d n (sigB n) R0 hd1 hdim hs0 hR1 hRk hnR)
    (log_x_ripe_ge_Kext d n (kRipe d) R0 (by linarith) (by linarith) hnn (by linarith) hR0
      (log_R0_le_ext d n (kRipe d) R0 hd1 (by linarith) hR0 hRk hnR)) hY_def hfacts
  have hcross := prob_regG_ge hP μ hn0 hpolB x
  set θ := 28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d with hθ_def
  have hθ : θ ≤ x - 7 * (pK d n R0).sc * Real.sqrt n := by
    change θ ≤ x - 7 * sigB n * Real.sqrt n
    rw [hθ_def, rpow_three_halves d (by linarith), hx_def]
    linarith
  have hmono : (gameLaw (prior d (1 / 2)) μ).real
      {s | x - 7 * (pK d n R0).sc * Real.sqrt n ≤ regG (prior d (1 / 2)) (pK d n R0) pol n s} ≤
      (gameLaw (prior d (1 / 2)) μ).real {s | θ ≤ regG (prior d (1 / 2)) (pK d n R0) pol n s} :=
    measureReal_mono fun s hs => le_trans hθ hs
  have hclamp := prob_regG_clamped (P := pK d n R0) μ pol hn1 θ
  have hn2 : 2 / (n : ℝ) ^ 2 ≤ 1 / 1000 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h100 : (100 : ℝ) ≤ n := by
      have : (4000000 : ℝ) ^ 10 ≤ n := (pow_le_pow_left₀ (by norm_num) hdR 10).trans hnR
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpr : (1 / 2 : ℝ) ≤ (gameLaw (prior d (1 / 2)) μ).real
      {s | θ ≤ regG (prior d (1 / 2)) (pK d n R0) pol n (s.1, clampZ (ellB n) s.2.1, s.2.2)} := by
    linarith
  have hsc : (pK d n R0).sc * ellB n ≤ 1 / 8 := (sigB_mul_ellB hn1).le
  obtain ⟨σ, hσ, hm, hge⟩ := derand_prob_mid I hP hsc hK hK1 hK2 μ hpol hpr
  refine ⟨σ, hσ, hm, le_trans (le_of_eq ?_) hge⟩
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

end Top

/-! ## The affine pull-back with the global constant -/

/-- Lemma AFF with the class `StratsMid`: the pull-back by `T` of a strategy of `StratsMid (T '' K) n L` is in
`StratsMid K n (L M)` when `T` is `M`-Lipschitz. -/
theorem pullStrat_mem_mid (T : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {n : ℕ} {σ : Strategy d} {L M : ℝ}
    (hL : 0 ≤ L) (hT : ∀ y z, dist (T y) (T z) ≤ M * dist y z) (hσ : σ ∈ StratsMid (T '' K) n L) :
    pullStrat T σ ∈ StratsMid K n (L * M) := by
  refine ⟨pullStrat_mem_strats T hσ.1, fun t ht x o o' => ⟨?_, fun y hy => ?_, fun y z => ?_⟩⟩
  · have h := (hσ.2 t ht (fun i => T (x i)) o o').1
    show (fun z => σ t (fun i => T (x i)) o (T z)) = fun z => σ t (fun i => T (x i)) o' (T z)
    rw [h]
  · exact (hσ.2 t ht (fun i => T (x i)) o o).2.1 (T y) ⟨y, hy, rfl⟩
  · have h := (hσ.2 t ht (fun i => T (x i)) o o).2.2 (T y) (T z)
    calc |pullStrat T σ t x o y - pullStrat T σ t x o z| ≤ L * dist (T y) (T z) := h
      _ ≤ L * (M * dist y z) := mul_le_mul_of_nonneg_left (hT y z) hL
      _ = L * M * dist y z := by ring

/-- An affine map that sends `B̄(a, r0)` into `B̄(0, R)` is `R/r0`-Lipschitz. -/
theorem dist_le_of_ball_image (T : E d ≃ᵃ[ℝ] E d) {a : E d} {r0 R : ℝ} (hr0 : 0 < r0)
    (hT : T '' closedBall a r0 ⊆ closedBall 0 R) (y z : E d) : dist (T y) (T z) ≤ R / r0 * dist y z := by
  set L := T.toAffineMap.linear with hL
  have hlin : ∀ u v : E d, T u - T v = L (u - v) := fun u v => by
    simpa [hL, vsub_eq_sub] using (T.toAffineMap.linearMap_vsub u v).symm
  have hnorm : ∀ v : E d, ‖v‖ = r0 → ‖L v‖ ≤ R := by
    intro v hv
    have h1 : T (a + v) ∈ closedBall (0 : E d) R := hT ⟨a + v, by simp [dist_eq_norm, hv], rfl⟩
    have h2 : T (a - v) ∈ closedBall (0 : E d) R := hT ⟨a - v, by simp [hv], rfl⟩
    rw [mem_closedBall_zero_iff] at h1 h2
    have h3 : T (a + v) - T (a - v) = (2 : ℝ) • L v := by
      rw [hlin, show a + v - (a - v) = (2 : ℝ) • v by module, map_smul]
    have h4 : ‖(2 : ℝ) • L v‖ ≤ 2 * R := by
      rw [← h3]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_smul, Real.norm_two] at h4
    linarith
  rw [dist_eq_norm, dist_eq_norm, hlin]
  by_cases hu : y - z = 0
  · simp [hu]
  · have hpos : 0 < ‖y - z‖ := norm_pos_iff.2 hu
    set v := (r0 / ‖y - z‖) • (y - z) with hv
    have hvn : ‖v‖ = r0 := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr0 hpos), div_mul_cancel₀ _ hpos.ne']
    have hyz : y - z = (‖y - z‖ / r0) • v := by
      rw [hv, smul_smul, div_mul_div_cancel₀ hr0.ne', div_self hpos.ne', one_smul]
    rw [hyz, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hr0)]
    calc ‖y - z‖ / r0 * ‖L v‖ ≤ ‖y - z‖ / r0 * R := mul_le_mul_of_nonneg_left (hnorm v hvn) (by positivity)
      _ = R / r0 * ((‖y - z‖ / r0) * r0) := by field_simp
      _ = R / r0 * ‖(‖y - z‖ / r0) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hr0), hvn]

/-! ## Lemma POS from Theorem PG -/

theorem det_pgOp (M : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (𝕜 := ℝ) M : E d →ₗ[ℝ] E d) = M.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The radius of the position of Theorem PG, halved: `67 d (ln(2d + 2))^{1/2}`. -/
noncomputable def posR (d : ℕ) : ℝ := 67 * d * Real.sqrt (Real.log (2 * d + 2))

/-- **Lemma POS** (the paper's position lemma): every body of `BodyU` has an affine image between `B̄(0, 1/2)` and
`B̄(0, 67 d (ln(2d + 2))^{1/2})`; from Theorem PG (`Poly.pgThm`) at `δ = 1/2`, whose failure event has probability at
most `1/2 < 1`. -/
theorem exists_position (hd : 1 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) :
    ∃ T : E d ≃ᵃ[ℝ] E d, closedBall (0 : E d) (1 / 2) ⊆ T '' K ∧ T '' K ⊆ closedBall 0 (posR d) := by
  obtain ⟨hr0, hr0R, hKc, hKv, hK1, hK2⟩ := hb
  set K' : Set (E d) := (fun x => a + x) ⁻¹' K with hK'
  have hK'v : Convex ℝ K' := hKv.translate_preimage_right a
  have hK'c : IsClosed K' := hKc.isClosed.preimage (continuous_const.add continuous_id)
  have hK'1 : closedBall (0 : E d) r0 ⊆ K' := fun x hx => hK1 (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rwa [mem_closedBall, dist_zero_right] at hx)
  have hK'2 : K' ⊆ closedBall (0 : E d) R0 := fun x hx => by
    have := hK2 hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at this
    rwa [mem_closedBall, dist_zero_right]
  have hpg := Poly.pgThm d K' r0 R0 (1 / 2) hd hK'v hK'c hr0 hr0R hK'1 hK'2 (by norm_num) (by norm_num)
  obtain ⟨ω, hω⟩ : ∃ ω, Poly.PgGood d K' (134 * d * Real.sqrt (Real.log (2 * d + 2)))
      (Poly.pg d K' r0 R0 (1 / 2) ω) := by
    by_contra hne
    push Not at hne
    have huniv : {ω | ¬ Poly.PgGood d K' (134 * d * Real.sqrt (Real.log (2 * d + 2)))
        (Poly.pg d K' r0 R0 (1 / 2) ω)} = Set.univ := Set.eq_univ_of_forall hne
    rw [huniv, measure_univ] at hpg
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) := hpg
    rw [ENNReal.one_le_ofReal] at this
    norm_num at this
  obtain ⟨Q, -, hdet, hin, hout, -⟩ := hω
  set A : E d →L[ℝ] E d := Poly.pgOp Q with hA
  have hdetA : LinearMap.det (A : E d →ₗ[ℝ] E d) ≠ 0 := by
    rw [hA, Poly.pgOp, det_pgOp]
    exact hdet
  set Ae : E d ≃ₗ[ℝ] E d := LinearMap.equivOfDetNeZero (A : E d →ₗ[ℝ] E d) hdetA with hAe
  have hAe_apply : ∀ y, Ae y = A y := fun y => rfl
  set L2 : E d ≃ₗ[ℝ] E d := (LinearEquiv.smulOfNeZero ℝ (E d) 2 two_ne_zero).trans Ae with hL2
  have hL2_apply : ∀ y, L2 y = A ((2 : ℝ) • y) := fun y => rfl
  set S : E d ≃ᵃ[ℝ] E d := L2.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (E d) (a + Poly.pgMu Q)) with hS
  have hS_apply : ∀ y, S y = a + (Poly.pgMu Q + A ((2 : ℝ) • y)) := fun y => by
    rw [hS, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, LinearEquiv.coe_toAffineEquiv, hL2_apply,
      vadd_eq_add, add_assoc]
  have himg : S.symm '' K = S ⁻¹' K := AffineEquiv.image_symm S K
  refine ⟨S.symm, ?_, ?_⟩
  · intro y hy
    rw [himg, Set.mem_preimage, hS_apply]
    have h2y : (2 : ℝ) • y ∈ closedBall (0 : E d) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_two]
      rw [mem_closedBall, dist_zero_right] at hy
      linarith
    exact hin h2y
  · intro y hy
    rw [himg, Set.mem_preimage, hS_apply] at hy
    have h2y := hout hy
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_two] at h2y
    rw [mem_closedBall, dist_zero_right, posR]
    have : (134 : ℝ) * d * Real.sqrt (Real.log (2 * d + 2)) = 2 * (67 * d * Real.sqrt (Real.log (2 * d + 2))) := by
      ring
    linarith

/-- The radius of the position is at least `1` and at most `d (120 ln d + 68)` for `d ≥ 4·10^6`. -/
theorem posR_bounds (hd : 4000000 ≤ d) : 1 ≤ posR d ∧ posR d ≤ d * kRipe d := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog2 : 1 ≤ Real.log (2 * d + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hsq1 : 1 ≤ Real.sqrt (Real.log (2 * d + 2)) := Real.one_le_sqrt.2 hlog2
  have hsq : Real.sqrt (Real.log (2 * d + 2)) ≤ (1 + Real.log (2 * d + 2)) / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Real.log (2 * d + 2) by linarith),
      Real.sqrt_nonneg (Real.log (2 * d + 2)), sq_nonneg (Real.sqrt (Real.log (2 * d + 2)) - 1)]
  have hl3 : Real.log (2 * d + 2) ≤ Real.log 3 + Real.log d := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hl3' : Real.log 3 < 2 := by
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
    linarith
  have hld : 1 ≤ Real.log d := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  constructor
  · unfold posR
    have : (1 : ℝ) ≤ 67 * d := by linarith
    nlinarith
  · unfold posR kRipe
    have hdp : (0 : ℝ) ≤ d := by linarith
    have : 67 * Real.sqrt (Real.log (2 * d + 2)) ≤ 120 * Real.log d + 68 := by nlinarith
    nlinarith

/-! ## Clauses (a) and (b) -/

/-- `sigB n ≤ 1/8` for `n ≥ 2`. -/
theorem sigB_le (n : ℕ) (hn : 1 < n) : sigB n ≤ 1 / 8 := by
  have h := sigB_mul_ellB hn
  have hl : 1 ≤ ellB n := by
    unfold ellB
    rw [Real.one_le_sqrt]
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have := Real.log_two_gt_d9
    linarith
  have hs : 0 ≤ sigB n := by unfold sigB; positivity
  nlinarith

/-- The position of a body and its constants: an affine `T` with `B̄(0, 1/2) ⊆ T K ⊆ B̄(0, R'')`,
`1 ≤ R'' ≤ d kRipe d`, `T` being `R''/r0`-Lipschitz. -/
theorem position_facts {d : ℕ} (hd : 4000000 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) :
    ∃ T : E d ≃ᵃ[ℝ] E d, Convex ℝ (T '' K) ∧ closedBall (0 : E d) (1 / 2) ⊆ T '' K ∧
      T '' K ⊆ closedBall 0 (posR d) ∧ ∀ y z, dist (T y) (T z) ≤ posR d / r0 * dist y z := by
  obtain ⟨T, h1, h2⟩ := exists_position (by omega) hb
  refine ⟨T, hb.2.2.2.1.affine_image T.toAffineMap, h1, h2, dist_le_of_ball_image T (a := a) hb.1 ?_⟩
  exact (Set.image_mono hb.2.2.2.2.1).trans h2

/-- **Clause (a) of `TheoremLowerU`.** -/
theorem lowerU_mean {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)} {a : E d} {r0 R0 : ℝ}
    (hb : BodyU K a r0 R0) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    LowerMean K n r0 μ pol (7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) := by
  obtain ⟨T, hKc, hK1, hK2, hT⟩ := position_facts hd hb
  obtain ⟨hR1, hRk⟩ := posR_bounds hd
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  obtain ⟨σ', hσ', hint, hmean⟩ :=
    lowerBody_mid lowerTopInputs hd hn hKc hK1 hK2 hR1 hRk μ (isLearnerAd_push T hpol)
  have hr0 := hb.1
  have hs := sigB_le n hn1
  have hs0 : 0 ≤ sigB n := by unfold sigB; positivity
  have hpull := pullStrat_mem_mid T (L := sigB n / posR d) (M := posR d / r0) (by positivity) hT hσ'
  refine ⟨pullStrat T σ', stratsMid_lowU hr0 ?_ hpull, ?_, ?_⟩
  · have hR0 : 0 < posR d := by linarith
    rw [show sigB n / posR d * (posR d / r0) = sigB n / r0 by field_simp]
    rw [div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  · simpa only [regretAd_pushLearner] using hint
  · simpa only [regretAd_pushLearner] using hmean

/-- **Clause (b) of `TheoremLowerU`.** -/
theorem lowerU_prob {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {K : Set (E d)} {a : E d} {r0 R0 : ℝ}
    (hb : BodyU K a r0 R0) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    LowerProb K n r0 μ pol (28 / 10 ^ 10 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d) (1 / 2) := by
  obtain ⟨T, hKc, hK1, hK2, hT⟩ := position_facts hd hb
  obtain ⟨hR1, hRk⟩ := posR_bounds hd
  have hn1 : 1 < n := by
    have h1 : 1 < d ^ 10 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  obtain ⟨σ', hσ', hm, hprob⟩ :=
    lowerBodyProb_mid lowerTopInputs hd hn hKc hK1 hK2 hR1 hRk μ (isLearnerAd_push T hpol)
  have hr0 := hb.1
  have hs := sigB_le n hn1
  have hs0 : 0 ≤ sigB n := by unfold sigB; positivity
  have hpull := pullStrat_mem_mid T (L := sigB n / posR d) (M := posR d / r0) (by positivity) hT hσ'
  refine ⟨pullStrat T σ', stratsMid_lowU hr0 ?_ hpull, ?_, ?_⟩
  · have hR0 : 0 < posR d := by linarith
    rw [show sigB n / posR d * (posR d / r0) = sigB n / r0 by field_simp]
    rw [div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  · simpa only [regretAd_pushLearner] using hm
  · simpa only [regretAd_pushLearner] using hprob

end AdversarialBco.UnifiedLower.Body
