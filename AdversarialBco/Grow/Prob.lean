/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Cheb
public import AdversarialBco.UnifiedLower.Body

@[expose] public section

/-!
# Route G on a body in position: the change of measure, the clamp and the derandomisation

Route G on a convex `K` with `B(0, 1/2) ⊆ K ⊆ B(0, R0)`, at the parameters `P` of the static game
and the budget `B`, with `γ = 1 - 3k²/d²`, `a = 2 (2^20 + 17) g k²/(γ d²)` (the price of PRICE-U (ii) in units of
`E D`), `M₀ = n γ g/2`, the threshold `(1 - η) M₀`, the clamp level `ℓ_c` and the fine bound `w = (g/k)((d+2)/2 + k)/σ`
on the shift:

* `stratG_mid`, `regretAd_stratG`: the strategy of a tip on the sphere and a clamped noise sequence is in
  `StratsMid K n L_D`, and the regret against it is `Σ_{t < n} D(x_t; θ)`;
* `prob_shift_ge`: `q₀ ≤ P(T⁻¹ E')` with `q₀ = 1 - n a/(η² M₀) - 2 n e^{-(ℓ_c - w)²/2}` and
  `E' = {Reg ≥ (1 - η) M₀, |Z_i| ≤ ℓ_c for i < n}` (Facts 1, 5, Chebyshev, the Gaussian tail with a shift);
* `growBody_mid`: some strategy of `StratsMid K n L_D` has `P(Reg_n ≥ (1 - η) M₀) ≥ q₀ e^{-(B + (2B)^{1/2})/q₀}`, with
  the regret measurable and nonnegative at every seed.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace AdversarialBco.Grow

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Stop AdversarialBco.Lower.Top
  AdversarialBco.UnifiedLower.Body

variable {d : ℕ}

/-! ## The strategy of a tip and a noise sequence -/

/-- The strategy of the tip `θ` and the noise sequence `z`: `f_t = b + D(·; θ) + σ z_t`, fixed in advance. -/
noncomputable def stratG (P : GP) (θ : E d) (z : ℕ → ℝ) : Strategy d :=
  stratOf (tipLaw d) (ruleG d P) P.sc θ z

theorem stratG_apply (P : GP) (θ : E d) (z : ℕ → ℝ) (t : ℕ) (x : Fin t → E d) (o : Fin t → ℝ) (y : E d) :
    stratG P θ z t x o y = P.b + dentG d P.g P.k θ y + P.sc * z t := rfl

/-- **Lemma LEGAL-S**: on a convex `K` inside `B(0, R0)`, with `b = 1/4`, `L_D R0 + g ≤ 1/2` and `|σ z_t| ≤ 1/8`,
the strategy is in `StratsMid K n L_D`, `L_D = (g/k) 5 √d c`. -/
theorem stratG_mid {P : GP} (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) (hb : P.b = 1 / 4) {K : Set (E d)} (hK : Convex ℝ K)
    {R0 : ℝ} (hKR : K ⊆ Metric.closedBall (0 : E d) R0)
    (hleg : P.g / P.k * (5 * Real.sqrt d) * frameC d * R0 + P.g / P.k * P.k ≤ 1 / 2) (n : ℕ) (θ : E d)
    (z : ℕ → ℝ) (hz : ∀ i, |P.sc * z i| ≤ 1 / 8) :
    stratG P θ z ∈ StratsMid K n (P.g / P.k * (5 * Real.sqrt d) * frameC d) := by
  have hbd : ∀ t (x : Fin t → E d) (o : Fin t → ℝ), ∀ y ∈ K, 1 / 8 ≤ stratG P θ z t x o y ∧
      stratG P θ z t x o y ≤ 7 / 8 := fun t x o y hy => by
    rw [stratG_apply]
    have h1 := dentG_nonneg (d := d) hg hk θ y
    have h2 := dentG_le_bowlG (d := d) hg hk θ y
    have h3 := bowlG_le (d := d) hg hk y
    have hy' : ‖y‖ ≤ R0 := by simpa using hKR hy
    have hL : 0 ≤ P.g / P.k * (5 * Real.sqrt d) * frameC d := by
      have := (frameC_pos d).le
      have : 0 ≤ P.g / P.k := div_nonneg hg hk
      positivity
    have h4 := mul_le_mul_of_nonneg_left hy' hL
    obtain ⟨h5, h6⟩ := abs_le.1 (hz t)
    constructor <;> linarith
  refine ⟨fun t _ => ⟨fun x o => ⟨?_, fun y hy => ?_⟩, fun y _ => by
      show Measurable fun _ : (Fin t → E d) × (Fin t → ℝ) => P.b + dentG d P.g P.k θ y + P.sc * z t
      exact measurable_const⟩, fun t _ x o o' =>
    ⟨rfl, fun y hy => hbd t x o y hy, fun y y' => ?_⟩⟩
  · have h := ((dentG_convexOn (d := d) hg hk θ).subset (Set.subset_univ _) hK).add_const (P.b + P.sc * z t)
    convert h using 1
    funext y
    simp only [stratG_apply, Pi.add_apply]
    ring
  · obtain ⟨h1, h2⟩ := hbd t x o y hy
    exact ⟨by linarith, by linarith⟩
  · rw [stratG_apply, stratG_apply, dist_eq_norm]
    have h := dentG_lipschitz (d := d) hg hk θ y y'
    have : P.b + dentG d P.g P.k θ y + P.sc * z t - (P.b + dentG d P.g P.k θ y' + P.sc * z t) =
        dentG d P.g P.k θ y - dentG d P.g P.k θ y' := by ring
    rw [this]
    exact h

/-- The regret against the strategy of a tip in `K` is the sum of the dents at the tip. -/
theorem regretAd_stratG {P : GP} (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) {Ω : Type} (pol : Learner Ω d) (n : ℕ)
    {K : Set (E d)} {θ : E d} (hθ : θ ∈ K) (z : ℕ → ℝ) (ω : Ω) :
    regretAd K (stratG P θ z) (fun t => pol t ω) n = regGG P pol n (θ, z, ω) := by
  let _ : MeasurableSpace Ω := ⊤
  unfold regretAd regretPts stratG
  simp only [lossAd_stratOf, plays_stratOf]
  have hinf : sInf ((fun y => ∑ t ∈ range n, ((ruleG d P).sig (post (tipLaw d) (ruleG d P) P.sc t
      (hist (tipLaw d) (ruleG d P) P.sc pol t (θ, z, ω))) y θ + P.sc * z t)) '' K) =
      ∑ t ∈ range n, (P.b + P.sc * z t) := by
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨θ, hθ, Finset.sum_congr rfl fun t _ => ?_⟩
      show P.b + dentG d P.g P.k θ θ + P.sc * z t = P.b + P.sc * z t
      rw [dentG_self hg hk]
      ring
    · rintro _ ⟨y, -, rfl⟩
      refine Finset.sum_le_sum fun t _ => ?_
      show P.b + P.sc * z t ≤ P.b + dentG d P.g P.k θ y + P.sc * z t
      linarith [dentG_nonneg (d := d) hg hk θ y]
  rw [hinf, regGG, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  show P.b + dentG d P.g P.k θ (play pol t ω (hist (tipLaw d) (ruleG d P) P.sc pol t (θ, z, ω))) + P.sc * z t -
    (P.b + P.sc * z t) = dentG d P.g P.k θ (xG P pol t (θ, z, ω))
  rw [xG, histG]
  ring

/-! ## The constants -/

/-- `γ = 1 - 3k²/d²`. -/
noncomputable def gamG (d : ℕ) (k : ℝ) : ℝ := 1 - 3 * k ^ 2 / (d : ℝ) ^ 2

/-- The price in units of `E D`: `a = 2 (2^20 + 17) g k²/(γ d²)`. -/
noncomputable def aG (d : ℕ) (P : GP) : ℝ := 2 * (2 ^ 20 + 17) * P.g * P.k ^ 2 / (gamG d P.k * (d : ℝ) ^ 2)

/-- The fine bound on the shift: `w = (g/k)((d + 2)/2 + k)/σ`. -/
noncomputable def wG (d : ℕ) (P : GP) : ℝ := P.g / P.k * (((d : ℝ) + 2) / 2 + P.k) / P.sc

/-- `M₀ = n γ g/2`. -/
noncomputable def mZero (d n : ℕ) (P : GP) : ℝ := n * (gamG d P.k * P.g / 2)

/-- `q₀ = 1 - n a/(η² M₀) - 2 n e^{-(ℓ_c - w)²/2}`. -/
noncomputable def qZero (d n : ℕ) (P : GP) (η ℓc : ℝ) : ℝ :=
  1 - n * aG d P / (η ^ 2 * mZero d n P) - n * (2 * Real.exp (-(ℓc - wG d P) ^ 2 / 2))

/-- The hypotheses of Route G on a body in position, at the parameters `P`, the budget `B`, `η` and the clamp
level `ℓ_c`. -/
structure RouteG (d n : ℕ) (P : GP) (R0 B η ℓc : ℝ) : Prop where
  cells : CellsOK d P.k
  g_pos : 0 < P.g
  sc_pos : 0 < P.sc
  b_eq : P.b = 1 / 4
  n_pos : 0 < n
  B_nonneg : 0 ≤ B
  η_pos : 0 < η
  η_le : η ≤ 1
  R0_nonneg : 0 ≤ R0
  clamp : P.sc * ℓc ≤ 1 / 8
  w_le : wG d P ≤ ℓc
  leg : P.g / P.k * (5 * Real.sqrt d) * frameC d * R0 + P.g / P.k * P.k ≤ 1 / 2
  γ_pos : 0 < gamG d P.k
  budget : mZero d n P ≤ B / (aG d P / (2 * P.sc ^ 2))

variable {n : ℕ} {P : GP} {R0 B η ℓc : ℝ}

theorem RouteG.k_pos (hR : RouteG d n P R0 B η ℓc) : 0 < P.k := by linarith [hR.cells.one_le_k]

theorem RouteG.d_pos (hR : RouteG d n P R0 B η ℓc) : (0 : ℝ) < d := by exact_mod_cast hR.cells.one_le_d

theorem RouteG.aG_pos (hR : RouteG d n P R0 B η ℓc) : 0 < aG d P := by
  have := hR.k_pos
  have := hR.d_pos
  have := hR.γ_pos
  have := hR.g_pos
  unfold aG
  positivity

theorem RouteG.mZero_pos (hR : RouteG d n P R0 B η ℓc) : 0 < mZero d n P := by
  have := hR.γ_pos
  have := hR.g_pos
  have : (0 : ℝ) < n := by exact_mod_cast hR.n_pos
  unfold mZero
  positivity

/-- PRICE-U (i) in the form of Fact 5: `E D ≥ γ g/2` at every play. -/
theorem RouteG.floor (hR : RouteG d n P R0 B η ℓc) (x : E d) :
    gamG d P.k * P.g / 2 ≤ ∫ θ, dentG d P.g P.k θ x ∂tipLaw d := by
  have h := price_floor hR.cells hR.g_pos x
  have hq : P.g ≤ bowlG d P.g P.k x := by
    have := bowl_ge (frameG d) 0 (P.g / P.k) P.k (5 * Real.sqrt d) (div_nonneg hR.g_pos.le hR.k_pos.le)
      (by positivity) x
    have he : P.g / P.k * P.k = P.g := div_mul_cancel₀ _ hR.k_pos.ne'
    unfold bowlG
    linarith
  have := hR.γ_pos
  unfold gamG at this ⊢
  nlinarith

/-- PRICE-U (ii) in units of `E D`: `E (q - D)² ≤ a E D`. -/
theorem RouteG.gap (hR : RouteG d n P R0 B η ℓc) (x : E d) :
    ∫ θ, (bowlG d P.g P.k x - dentG d P.g P.k θ x) ^ 2 ∂tipLaw d ≤ aG d P * ∫ θ, dentG d P.g P.k θ x ∂tipLaw d := by
  have h1 := price_gap hR.cells hR.g_pos x
  have h2 := price_floor hR.cells hR.g_pos x
  have hγ := hR.γ_pos
  have hd := hR.d_pos
  have hq : bowlG d P.g P.k x ≤ 2 * (∫ θ, dentG d P.g P.k θ x ∂tipLaw d) / gamG d P.k := by
    rw [le_div_iff₀ hγ]
    unfold gamG at hγ ⊢
    linarith
  have hc : 0 ≤ (2 ^ 20 + 17) * P.g * (P.k ^ 2 / (d : ℝ) ^ 2) := by
    have := hR.g_pos
    positivity
  calc ∫ θ, (bowlG d P.g P.k x - dentG d P.g P.k θ x) ^ 2 ∂tipLaw d
      ≤ (2 ^ 20 + 17) * P.g * (P.k ^ 2 / (d : ℝ) ^ 2) * bowlG d P.g P.k x := h1
    _ ≤ (2 ^ 20 + 17) * P.g * (P.k ^ 2 / (d : ℝ) ^ 2) * (2 * (∫ θ, dentG d P.g P.k θ x ∂tipLaw d) / gamG d P.k) :=
        mul_le_mul_of_nonneg_left hq hc
    _ = aG d P * ∫ θ, dentG d P.g P.k θ x ∂tipLaw d := by
        unfold aG
        field_simp

/-- Fact 4: `c(x) ≤ Π E D` with `Π = a/(2σ²)`. -/
theorem RouteG.price (hR : RouteG d n P R0 B η ℓc) (x : E d) :
    cG P x ≤ aG d P / (2 * P.sc ^ 2) * ∫ θ, dentG d P.g P.k θ x ∂tipLaw d := by
  unfold cG
  have hs : 0 < 2 * P.sc ^ 2 := by have := hR.sc_pos; positivity
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
  exact hR.gap x

/-! ## The probability under the null world -/

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The regret of the real run reads the noise before round `n` only. -/
theorem regGG_congr (P : GP) (pol : Learner Ω d) (n : ℕ) (θ : E d) {z z' : ℕ → ℝ} (hz : ∀ i < n, z i = z' i)
    (ω : Ω) : regGG P pol n (θ, z, ω) = regGG P pol n (θ, z', ω) := by
  let _ : MeasurableSpace Ω := ⊤
  unfold regGG xG histG
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hist_congr (tipLaw d) (ruleG d P) P.sc pol t (θ, z, ω) (θ, z', ω) rfl
    (fun i hi => hz i (lt_trans hi (Finset.mem_range.1 ht))) rfl]

/-- The event of Route G: the regret above the threshold and no noise clamped before round `n`. -/
def eventG (P : GP) (pol : Learner Ω d) (n : ℕ) (θG ℓc : ℝ) : Set (Sample d Ω) :=
  {s | θG ≤ regGG P pol n s ∧ ∀ i < n, |s.2.1 i| ≤ ℓc}

theorem gameLaw_sphere (μ : Measure Ω) [IsProbabilityMeasure μ] (hd : 1 ≤ d) :
    gameLaw (tipLaw d) μ {s | ‖s.1‖ ≠ 1 / 2} = 0 := by
  have hs : {s : Sample d Ω | ‖s.1‖ ≠ 1 / 2} = {θ : E d | ‖θ‖ ≠ 1 / 2} ×ˢ Set.univ := by
    ext s
    simp
  rw [hs]
  unfold gameLaw
  rw [Measure.prod_prod, tipLaw_sphere hd, zero_mul]

/-- **The null world gives the event probability at least `q₀`**: `q₀ ≤ P(T⁻¹ E')`. -/
theorem prob_shift_ge (hR : RouteG d n P R0 B η ℓc) (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) :
    qZero d n P η ℓc ≤ (gameLaw (tipLaw d) μ).real
      (shiftAll (mG P pol n B) n ⁻¹' eventG P pol n ((1 - η) * mZero d n P) ℓc) := by
  have hG := isProbabilityMeasure_gameLaw (tipLaw d) μ
  have hg := hR.g_pos.le
  have hk := hR.k_pos.le
  have hpm : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  set T := shiftAll (mG P pol n B) n with hT
  set Ev := eventG P pol n ((1 - η) * mZero d n P) ℓc with hEv
  have hTm : Measurable T := measurable_shiftAll (measurable_mG hg hk hpm B) n
  have hEm : MeasurableSet Ev := by
    have : Ev = {s : Sample d Ω | (1 - η) * mZero d n P ≤ regGG P pol n s} ∩
        ⋂ i ∈ range n, {s : Sample d Ω | |s.2.1 i| ≤ ℓc} := by
      ext s
      simp [hEv, eventG]
    rw [this]
    exact (measurableSet_le measurable_const (measurable_regGG hg hk hpm)).inter
      (Finset.measurableSet_biInter _ fun i _ => measurableSet_le (measurable_noise i).abs measurable_const)
  -- the three bad events
  set Ae := {s : Sample d Ω | stopS P pol n B s < (1 - η) * mZero d n P}
  set Af := {s : Sample d Ω | ∃ i < n, ℓc - wG d P < |s.2.1 i|}
  set Ag := {s : Sample d Ω | ‖s.1‖ ≠ 1 / 2}
  have hsub : (T ⁻¹' Ev)ᶜ ⊆ Ae ∪ Af ∪ Ag := by
    intro s hs
    by_contra hn
    simp only [Set.mem_union, not_or] at hn
    obtain ⟨⟨he, hf⟩, hgs⟩ := hn
    simp only [Ae, Af, Ag, Set.mem_ofPred_eq, not_lt, not_exists, not_and, not_lt, not_not] at he hf hgs
    apply hs
    refine ⟨he.trans (regGG_shift_ge hg hk hR.sc_pos.ne' s), fun i hi => ?_⟩
    rw [shiftAll_noise (mG_readsBefore P pol n B) n s i, ite_eq_left hi]
    have hw := abs_mG_le_sphere (pol := pol) (n := n) hR.cells.one_le_d hg hk hR.sc_pos B i (s := s) hgs.le
    calc |s.2.1 i + mG P pol n B i s| ≤ |s.2.1 i| + |mG P pol n B i s| := abs_add_le _ _
      _ ≤ (ℓc - wG d P) + wG d P := add_le_add (hf i hi) hw
      _ = ℓc := by ring
  -- their probabilities
  have he : (gameLaw (tipLaw d) μ).real Ae ≤ n * aG d P / (η ^ 2 * mZero d n P) :=
    prob_stopS_lt μ hg hk hpm hR.aG_pos.le hR.η_pos hR.η_le hR.mZero_pos
      (fun y => by
        have h := stop_mass_ge (pol := pol) (n := n) (B := B) hg hk hR.floor hR.price
          (div_pos hR.aG_pos (by have := hR.sc_pos; positivity)) y
        have hb := hR.budget
        unfold mZero at hb ⊢
        exact (le_min le_rfl hb).trans h) hR.gap
  have hf : (gameLaw (tipLaw d) μ).real Af ≤ n * (2 * Real.exp (-(ℓc - wG d P) ^ 2 / 2)) :=
    gameLaw_bad_le (tipLaw d) μ n (by linarith [hR.w_le])
  have hgz : (gameLaw (tipLaw d) μ).real Ag = 0 := by
    rw [measureReal_def, gameLaw_sphere μ hR.cells.one_le_d, ENNReal.toReal_zero]
  have hc := measureReal_mono (μ := gameLaw (tipLaw d) μ) hsub
  rw [probReal_compl_eq_one_sub (hTm hEm)] at hc
  unfold qZero
  have : (gameLaw (tipLaw d) μ).real (Ae ∪ Af ∪ Ag) ≤
      (gameLaw (tipLaw d) μ).real Ae + (gameLaw (tipLaw d) μ).real Af + (gameLaw (tipLaw d) μ).real Ag := by
    linarith [measureReal_union_le (μ := gameLaw (tipLaw d) μ) (Ae ∪ Af) Ag,
      measureReal_union_le (μ := gameLaw (tipLaw d) μ) Ae Af]
  linarith

/-- **Route G on a body in position.** Some strategy of `StratsMid K n L_D` has
`P(Reg_n ≥ (1 - η) M₀) ≥ q₀ e^{-(B + (2B)^{1/2})/q₀}` over the learner's seed, with the regret measurable and
nonnegative at every seed. -/
theorem growBody_mid (hR : RouteG d n P R0 B η ℓc) {K : Set (E d)} (hK : Convex ℝ K)
    (hK1 : Metric.closedBall (0 : E d) (1 / 2) ⊆ K) (hK2 : K ⊆ Metric.closedBall 0 R0) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) (hq0 : 0 < qZero d n P η ℓc) :
    ∃ σ ∈ StratsMid K n (P.g / P.k * (5 * Real.sqrt d) * frameC d),
      Measurable (fun ω => regretAd K σ (fun t => pol t ω) n) ∧
      (∀ ω, 0 ≤ regretAd K σ (fun t => pol t ω) n) ∧
      ENNReal.ofReal (qZero d n P η ℓc * Real.exp (-(B + Real.sqrt (2 * B)) / qZero d n P η ℓc)) ≤
        μ {ω | (1 - η) * mZero d n P ≤ regretAd K σ (fun t => pol t ω) n} := by
  have hG := isProbabilityMeasure_gameLaw (tipLaw d) μ
  have hg := hR.g_pos.le
  have hk := hR.k_pos.le
  have hpolB : IsLearnerAd (Metric.closedBall 0 R0) n pol := fun t ht =>
    ⟨(hpol t ht).1, fun ω x o => hK2 ((hpol t ht).2 ω x o)⟩
  have hpm : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2 :=
    fun t ht => (hpol t ht).1
  set θG := (1 - η) * mZero d n P with hθG
  set q0 := qZero d n P η ℓc with hq0_def
  set p0 := q0 * Real.exp (-(B + Real.sqrt (2 * B)) / q0) with hp0
  have hℓ : 0 ≤ ℓc := by
    have : 0 ≤ wG d P := by
      have := hR.sc_pos
      have := div_nonneg hg hk
      have := hR.d_pos
      unfold wG
      positivity
    linarith [hR.w_le]
  -- the event of the clamped regret
  have hmc : Measurable fun s : Sample d Ω => (s.1, clampZ ℓc s.2.1, s.2.2) :=
    measurable_fst.prodMk (((measurable_clampZ _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  set Ac := {s : Sample d Ω | θG ≤ regGG P pol n (s.1, clampZ ℓc s.2.1, s.2.2)} with hAc
  have hAcm : MeasurableSet Ac := measurableSet_le measurable_const ((measurable_regGG hg hk hpm).comp hmc)
  have hEm : MeasurableSet (eventG P pol n θG ℓc) := by
    have : eventG P pol n θG ℓc = {s : Sample d Ω | θG ≤ regGG P pol n s} ∩
        ⋂ i ∈ range n, {s : Sample d Ω | |s.2.1 i| ≤ ℓc} := by
      ext s
      simp [eventG]
    rw [this]
    exact (measurableSet_le measurable_const (measurable_regGG hg hk hpm)).inter
      (Finset.measurableSet_biInter _ fun i _ => measurableSet_le (measurable_noise i).abs measurable_const)
  have hEA : eventG P pol n θG ℓc ⊆ Ac := fun s hs => by
    obtain ⟨h1, h2⟩ := hs
    show θG ≤ regGG P pol n (s.1, clampZ ℓc s.2.1, s.2.2)
    rw [regGG_congr P pol n s.1 (z := clampZ ℓc s.2.1) (z' := s.2.1)
      (fun i hi => clampZ_of_abs_le (h2 i hi)) s.2.2]
    exact h1
  -- the change of measure
  have hW := abs_mG_le (pol := pol) (n := n) hg hk hR.sc_pos hR.R0_nonneg hpolB B
  have hbud := budget_mG μ hg hk hR.sc_pos hpm hR.B_nonneg hW
  have hcm := measure_ge_shift (tipLaw d) μ (measurable_mG hg hk hpm B) (mG_readsBefore P pol n B) hW n hbud
    hEm hq0 (prob_shift_ge hR μ hpolB)
  have hPA : ENNReal.ofReal p0 ≤ gameLaw (tipLaw d) μ Ac := hcm.trans (measure_mono hEA)
  -- the derandomisation
  have hassoc : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => ((p.1.1, p.1.2, p.2) : Sample d Ω) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hGm : Measurable fun p : (E d × (ℕ → ℝ)) × Ω => Ac.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) :=
    (measurable_const.indicator hAcm).comp hassoc
  have hGb : ∀ p : (E d × (ℕ → ℝ)) × Ω, |Ac.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2)| ≤ 1 := fun p => by
    by_cases hp : ((p.1.1, p.1.2, p.2) : Sample d Ω) ∈ Ac
    · rw [Set.indicator_of_mem hp, Pi.one_apply, abs_one]
    · rw [Set.indicator_of_notMem hp, abs_zero]
      norm_num
  have hN : ((tipLaw d).prod gaussStream) {a : E d × (ℕ → ℝ) | ‖a.1‖ ≠ 1 / 2} = 0 := by
    have hs : {a : E d × (ℕ → ℝ) | ‖a.1‖ ≠ 1 / 2} = {θ : E d | ‖θ‖ ≠ 1 / 2} ×ˢ Set.univ := by
      ext a
      simp
    rw [hs, Measure.prod_prod, tipLaw_sphere hR.cells.one_le_d, zero_mul]
  obtain ⟨a, haN, ha⟩ := exists_good_point ((tipLaw d).prod gaussStream) μ hGm hGb hN
  have ha1 : ‖a.1‖ = 1 / 2 := by
    by_contra h
    exact haN h
  have hxo : a.1 ∈ K := hK1 (by rw [Metric.mem_closedBall, dist_zero_right, ha1])
  have hz : ∀ i, |P.sc * clampZ ℓc a.2 i| ≤ 1 / 8 := fun i => by
    rw [abs_mul, abs_of_pos hR.sc_pos]
    exact (mul_le_mul_of_nonneg_left (abs_clampZ_le hℓ a.2 i) hR.sc_pos.le).trans hR.clamp
  have hσ := stratG_mid hg hk hR.b_eq hK hK2 hR.leg n a.1 (clampZ ℓc a.2) hz
  have hω : ∀ ω, regretAd K (stratG P a.1 (clampZ ℓc a.2)) (fun t => pol t ω) n =
      regGG P pol n (a.1, clampZ ℓc a.2, ω) := fun ω => regretAd_stratG hg hk pol n hxo _ ω
  have hmω : Measurable fun ω : Ω => regGG P pol n (a.1, clampZ ℓc a.2, ω) :=
    (measurable_regGG hg hk hpm).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  refine ⟨_, hσ, ?_, fun ω => ?_, ?_⟩
  · simp only [hω]
    exact hmω
  · rw [hω]
    exact Finset.sum_nonneg fun t _ => dentG_nonneg hg hk _ _
  · simp only [hω]
    set Bω := {ω : Ω | θG ≤ regGG P pol n (a.1, clampZ ℓc a.2, ω)} with hBω
    have hB : MeasurableSet Bω := measurableSet_le measurable_const hmω
    have h1 : ∫ p, Ac.indicator (1 : Sample d Ω → ℝ) (p.1.1, p.1.2, p.2) ∂((tipLaw d).prod gaussStream).prod μ =
        (gameLaw (tipLaw d) μ).real Ac :=
      (integral_gameLaw_assoc (tipLaw d) μ (Ac.indicator 1)).symm.trans (integral_indicator_one hAcm)
    have h2 : ∫ ω, Ac.indicator (1 : Sample d Ω → ℝ) (a.1, a.2, ω) ∂μ = μ.real Bω := by
      rw [← integral_indicator_one hB]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      beta_reduce
      by_cases hωB : ω ∈ Bω
      · rw [Set.indicator_of_mem hωB, Set.indicator_of_mem (show ((a.1, a.2, ω) : Sample d Ω) ∈ Ac from hωB)]
        rfl
      · rw [Set.indicator_of_notMem hωB,
          Set.indicator_of_notMem (show ((a.1, a.2, ω) : Sample d Ω) ∉ Ac from hωB)]
    have ha' : (gameLaw (tipLaw d) μ).real Ac ≤ μ.real Bω := by
      rw [← h1, ← h2]
      exact ha
    calc ENNReal.ofReal p0 ≤ gameLaw (tipLaw d) μ Ac := hPA
      _ = ENNReal.ofReal ((gameLaw (tipLaw d) μ).real Ac) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (μ.real Bω) := ENNReal.ofReal_le_ofReal ha'
      _ = μ Bω := ofReal_measureReal (measure_ne_top _ _)

end AdversarialBco.Grow
