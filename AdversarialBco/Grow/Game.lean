/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Grow.Price
public import AdversarialBco.Grow.Shift
public import AdversarialBco.Conj1Lower.Top

@[expose] public section

/-!
# The static-dent game of Route G, its null world and the coupling

Route G at the vertex law. The game of Bayes.lean with two rules that answer nothing:

* `ruleG`: the signal `b + D(x; θ)` of the static dent; the real run `histG`, its plays `xG`, its regret
  `regGG = Σ_{t < n} D(x_t; θ)`;
* `ruleQ`: the signal `b + q(x)` of the bowl, which does not read the tip; the fake run `histF` on the noise and the
  seed alone, its plays `xF`;
* the price `cG x = E (q(x) - D(x; ·))²/(2σ²)`, its stopped sums `cumF`, and the shift of round `t`,
  `mG t = 1{C_t ≤ B} (q(x̃_t) - D(x̃_t; θ))/σ` for `t < n`;
* `histG_shift` (Fact 1): on the rounds before the budget is spent, the real run on the shifted sample is the fake
  run, so `regGG (T s) ≥ stopS s = Σ_{t < n} 1{C_u ≤ B, u < t} D(x̃_t; θ)` (`regGG_shift_ge`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace AdversarialBco.Grow

open AdversarialBco.Lower AdversarialBco.Lower.Bayes AdversarialBco.Lower.Stop

variable {d : ℕ}

/-! ## The rules -/

/-- The parameters of the static game: the depth `g`, the order `k`, the offset `b`, the noise scale `σ`. -/
structure GP where
  g : ℝ
  k : ℝ
  b : ℝ
  sc : ℝ

/-- The rule of the static dent: no answer, the signal `b + D(x; θ)`. -/
noncomputable def ruleG (d : ℕ) (P : GP) : Rule d Unit where
  ans _ _ _ := ()
  sig _ x θ := P.b + dentG d P.g P.k θ x

/-- The rule of the bowl: the signal `b + q(x)`, which does not read the tip. -/
noncomputable def ruleQ (d : ℕ) (P : GP) : Rule d Unit where
  ans _ _ _ := ()
  sig _ x _ := P.b + bowlG d P.g P.k x

theorem measurable_dentG {g k : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) :
    Measurable fun p : E d × E d => dentG d g k p.1 p.2 := by
  have heq : (fun p : E d × E d => dentG d g k p.1 p.2) = fun p => ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1},
      ((r : ℚ) : ℝ) * bowl (frameG d) 0 (g / k) k (5 * Real.sqrt d) (p.1 + ((r : ℚ) : ℝ)⁻¹ • (p.2 - p.1)) := by
    funext p
    exact dent_eq_iInf_rat _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) p.1 p.2
  rw [heq]
  refine Measurable.iInf fun r => ?_
  exact (continuous_const.mul ((continuous_bowl _ _ _ _ _).comp (by fun_prop))).measurable

theorem measurable_bowlG (g k : ℝ) : Measurable (bowlG d g k) := (continuous_bowl _ _ _ _ _).measurable

theorem ruleG_meas (P : GP) (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) (π0 : Measure (E d)) : (ruleG d P).Meas π0 := by
  intro H _ g _ _ _
  refine ⟨measurable_of_subsingleton_codomain _, ?_⟩
  have h2 : Measurable fun p : H × E d × E d => (p.2.2, p.2.1) :=
    (measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd)
  have h := (measurable_dentG (d := d) hg hk).comp h2
  rw [Function.comp_def] at h
  exact h.const_add P.b

theorem ruleQ_meas (P : GP) (π0 : Measure (E d)) : (ruleQ d P).Meas π0 := by
  intro H _ g _ _ _
  refine ⟨measurable_of_subsingleton_codomain _, ?_⟩
  have h2 : Measurable fun p : H × E d × E d => p.2.1 := measurable_fst.comp measurable_snd
  have h := (measurable_bowlG (d := d) P.g P.k).comp h2
  rw [Function.comp_def] at h
  exact h.const_add P.b

/-! ## The runs -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- The history of the real game on the sample `s = (θ, Z, ω)`. -/
noncomputable def histG (P : GP) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : Hist d Unit :=
  hist (tipLaw d) (ruleG d P) P.sc pol t s

/-- The play of round `t` of the real game. -/
noncomputable def xG (P : GP) (pol : Learner Ω d) (t : ℕ) (s : Sample d Ω) : E d :=
  play pol t s.2.2 (histG P pol t s)

/-- The regret of the real game: `Σ_{t < n} D(x_t; θ)`. -/
noncomputable def regGG (P : GP) (pol : Learner Ω d) (n : ℕ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ range n, dentG d P.g P.k s.1 (xG P pol t s)

/-- The history of the fake run, against the bowl, on the noise and the seed `y = (Z, ω)`. -/
noncomputable def histF (P : GP) (pol : Learner Ω d) (t : ℕ) (y : (ℕ → ℝ) × Ω) : Hist d Unit :=
  hist (tipLaw d) (ruleQ d P) P.sc pol t (0, y.1, y.2)

/-- The play of round `t` of the fake run. -/
noncomputable def xF (P : GP) (pol : Learner Ω d) (t : ℕ) (y : (ℕ → ℝ) × Ω) : E d :=
  play pol t y.2 (histF P pol t y)

/-- The price of a play: `c(x) = E (q(x) - D(x; ·))²/(2σ²)`. -/
noncomputable def cG (P : GP) (x : E d) : ℝ :=
  (∫ θ, (bowlG d P.g P.k x - dentG d P.g P.k θ x) ^ 2 ∂tipLaw d) / (2 * P.sc ^ 2)

/-- The price of round `t < n` of the fake run (`0` from round `n` on). -/
noncomputable def priceF (P : GP) (pol : Learner Ω d) (n t : ℕ) (y : (ℕ → ℝ) × Ω) : ℝ :=
  if t < n then cG P (xF P pol t y) else 0

/-- The budget spent up to round `t`: `C_t = Σ_{u ≤ t} c(x̃_u)`. -/
noncomputable def cumF (P : GP) (pol : Learner Ω d) (n t : ℕ) (y : (ℕ → ℝ) × Ω) : ℝ :=
  ∑ u ∈ range (t + 1), priceF P pol n u y

/-- The gap of round `t < n` at the tip, in units of `σ`: `(q(x̃_t) - D(x̃_t; θ))/σ`. -/
noncomputable def gapF (P : GP) (pol : Learner Ω d) (n t : ℕ) (s : Sample d Ω) : ℝ :=
  if t < n then (bowlG d P.g P.k (xF P pol t s.2) - dentG d P.g P.k s.1 (xF P pol t s.2)) / P.sc else 0

/-- The shift of round `t`: the gap while the budget `B` is not spent. -/
noncomputable def mG (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (t : ℕ) (s : Sample d Ω) : ℝ :=
  if cumF P pol n t s.2 ≤ B then gapF P pol n t s else 0

/-! ## The fake run reads neither the tip nor the noise of its round -/

theorem histF_congr (P : GP) (pol : Learner Ω d) {t : ℕ} {y y' : (ℕ → ℝ) × Ω} (h1 : ∀ i < t, y.1 i = y'.1 i)
    (h2 : y.2 = y'.2) : histF P pol t y = histF P pol t y' :=
  hist_congr _ _ _ _ t _ _ rfl h1 h2

theorem xF_congr (P : GP) (pol : Learner Ω d) {t : ℕ} {y y' : (ℕ → ℝ) × Ω} (h1 : ∀ i < t, y.1 i = y'.1 i)
    (h2 : y.2 = y'.2) : xF P pol t y = xF P pol t y' := by
  unfold xF
  rw [histF_congr P pol h1 h2, h2]

theorem cumF_congr (P : GP) (pol : Learner Ω d) (n : ℕ) {t : ℕ} {y y' : (ℕ → ℝ) × Ω}
    (h1 : ∀ i < t, y.1 i = y'.1 i) (h2 : y.2 = y'.2) : cumF P pol n t y = cumF P pol n t y' := by
  unfold cumF priceF
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
  rw [xF_congr P pol (fun i hi => h1 i (lt_of_lt_of_le hi hu')) h2]

/-- The shift of round `t` reads the tip, the seed and the noise before `t` only. -/
theorem mG_readsBefore (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (t : ℕ) : ReadsBefore t (mG P pol n B t) := by
  intro s s' h1 h2 h3
  have hc := cumF_congr P pol n (y := s.2) (y' := s'.2) h3 h2
  have hx := xF_congr P pol (t := t) (y := s.2) (y' := s'.2) h3 h2
  unfold mG gapF
  rw [hc, hx, h1]

/-! ## Measurability -/

section Meas

variable {P : GP} {pol : Learner Ω d} {n : ℕ}

theorem measurable_histG (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {t : ℕ}
    (ht : t ≤ n) : Measurable (histG P pol t) :=
  measurable_hist (tipLaw d) (ruleG d P) (ruleG_meas P hg hk _) P.sc hpol ht

theorem measurable_xG (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {t : ℕ}
    (ht : t < n) : Measurable (xG P pol t) :=
  (measurable_play (α := Unit) (hpol t ht)).comp ((measurable_snd.comp measurable_snd).prodMk
    (measurable_histG hg hk hpol ht.le))

theorem measurable_regGG (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    Measurable (regGG P pol n) := by
  refine Finset.measurable_sum _ fun t ht => ?_
  have h2 : Measurable fun s : Sample d Ω => (s.1, xG P pol t s) :=
    measurable_fst.prodMk (measurable_xG hg hk hpol (Finset.mem_range.1 ht))
  have h := (measurable_dentG (d := d) hg hk).comp h2
  rw [Function.comp_def] at h
  exact h

theorem measurable_histF
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {t : ℕ}
    (ht : t ≤ n) : Measurable (histF P pol t) := by
  have h := measurable_hist (tipLaw d) (ruleQ d P) (ruleQ_meas P _) P.sc hpol ht
  have h2 : Measurable fun y : (ℕ → ℝ) × Ω => ((0 : E d), y.1, y.2) :=
    measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
  exact h.comp h2

theorem measurable_xF
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {t : ℕ}
    (ht : t < n) : Measurable (xF P pol t) :=
  (measurable_play (α := Unit) (hpol t ht)).comp (measurable_snd.prodMk (measurable_histF hpol ht.le))

theorem cG_eq (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) (x : E d) : cG P x =
    ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool, (bowlG d P.g P.k x - dentG d P.g P.k (vtx d ε) x) ^ 2 /
      (2 * P.sc ^ 2) := by
  unfold cG
  have hm : Measurable fun θ => (bowlG d P.g P.k x - dentG d P.g P.k θ x) ^ 2 :=
    (measurable_const.sub (measurable_dent_tip _ _ _ _ _ (div_nonneg hg hk) hk (by positivity) x)).pow_const 2
  rw [integral_tipLaw hm, mul_div_assoc, Finset.sum_div]

theorem measurable_dentG_play (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) {α : Type} [MeasurableSpace α] {θ : α → E d}
    {x : α → E d} (hθ : Measurable θ) (hx : Measurable x) :
    Measurable fun a => dentG d P.g P.k (θ a) (x a) := by
  have h := (measurable_dentG (d := d) hg hk).comp (hθ.prodMk hx)
  rw [Function.comp_def] at h
  exact h

theorem measurable_cG (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) : Measurable (cG (d := d) P) := by
  have he : cG (d := d) P = fun x => ((2 : ℝ) ^ d)⁻¹ * ∑ ε : Fin d → Bool,
      (bowlG d P.g P.k x - dentG d P.g P.k (vtx d ε) x) ^ 2 / (2 * P.sc ^ 2) := funext (cG_eq hg hk)
  rw [he]
  refine measurable_const.mul (Finset.measurable_sum _ fun ε _ => ?_)
  exact (((measurable_bowlG _ _).sub (measurable_dentG_play hg hk measurable_const measurable_id)).pow_const
    2).div_const _

theorem measurable_priceF (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) (t : ℕ) :
    Measurable (priceF P pol n t) := by
  unfold priceF
  by_cases ht : t < n
  · simp only [ht, ite_true]
    exact (measurable_cG hg hk).comp (measurable_xF hpol ht)
  · simp only [ht, ite_false]
    exact measurable_const

theorem measurable_cumF (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) (t : ℕ) :
    Measurable (cumF P pol n t) :=
  Finset.measurable_sum _ fun u _ => measurable_priceF hg hk hpol u

theorem measurable_gapF (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) (t : ℕ) :
    Measurable (gapF P pol n t) := by
  unfold gapF
  by_cases ht : t < n
  · simp only [ht, ite_true]
    have hx : Measurable fun s : Sample d Ω => xF P pol t s.2 := (measurable_xF hpol ht).comp measurable_snd
    exact (((measurable_bowlG _ _).comp hx).sub (measurable_dentG_play hg hk measurable_fst hx)).div_const _
  · simp only [ht, ite_false]
    exact measurable_const

theorem measurable_mG (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) (B : ℝ)
    (t : ℕ) : Measurable (mG P pol n B t) :=
  Measurable.ite (measurableSet_le ((measurable_cumF hg hk hpol t).comp measurable_snd) measurable_const)
    (measurable_gapF hg hk hpol t) measurable_const

end Meas

/-! ## Bounds on the shift -/

section Bounds

variable {P : GP} {pol : Learner Ω d} {n : ℕ}

/-- The crude bound: `0 ≤ m_t ≤ q(x̃_t)/σ ≤ (L_D R0 + g)/σ` for plays in `B(0, R0)`. -/
theorem abs_mG_le (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) (hsc : 0 < P.sc) {R0 : ℝ} (hR0 : 0 ≤ R0)
    (hpol : IsLearnerAd (Metric.closedBall 0 R0) n pol) (B : ℝ) (t : ℕ) (s : Sample d Ω) :
    |mG P pol n B t s| ≤ (P.g / P.k * (5 * Real.sqrt d) * frameC d * R0 + P.g / P.k * P.k) / P.sc := by
  have hR : ∀ t < n, ‖xF P pol t s.2‖ ≤ R0 := fun t ht => by
    have := (hpol t ht).2 s.2.2 (fun i => (histF P pol t s.2).1 i) (fun i => (histF P pol t s.2).2.1 i)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hκ : 0 ≤ P.g / P.k * (5 * Real.sqrt d) * frameC d := by
    have := (frameC_pos d).le
    have : 0 ≤ P.g / P.k := div_nonneg hg hk
    positivity
  unfold mG gapF
  split_ifs with h1 h2
  · rw [abs_of_nonneg (div_nonneg (sub_nonneg.2 (dentG_le_bowlG hg hk _ _)) hsc.le)]
    refine div_le_div_of_nonneg_right ?_ hsc.le
    have h3 := bowlG_le (d := d) hg hk (xF P pol t s.2)
    have h4 := dentG_nonneg (d := d) hg hk s.1 (xF P pol t s.2)
    have h5 := mul_le_mul_of_nonneg_left (hR t h2) hκ
    linarith
  all_goals
    rw [abs_zero]
    have : 0 ≤ P.g / P.k * P.k := by have := div_nonneg hg hk; positivity
    positivity

omit [MeasurableSpace Ω] in
/-- The fine bound on the sphere: `|m_t| ≤ (g/k)((d + 2)/2 + k)/σ` for `‖θ‖ ≤ 1/2`. -/
theorem abs_mG_le_sphere (hd : 1 ≤ d) (hg : 0 ≤ P.g) (hk : 0 ≤ P.k) (hsc : 0 < P.sc) (B : ℝ) (t : ℕ)
    {s : Sample d Ω} (hs : ‖s.1‖ ≤ 1 / 2) :
    |mG P pol n B t s| ≤ P.g / P.k * (((d : ℝ) + 2) / 2 + P.k) / P.sc := by
  have hW : 0 ≤ P.g / P.k * (((d : ℝ) + 2) / 2 + P.k) / P.sc := by
    have := div_nonneg hg hk
    positivity
  unfold mG gapF
  split_ifs
  · rw [abs_of_nonneg (div_nonneg (sub_nonneg.2 (dentG_le_bowlG hg hk _ _)) hsc.le)]
    exact div_le_div_of_nonneg_right (gap_le_sphere hd hg hk hs _) hsc.le
  all_goals rw [abs_zero]; exact hW

end Bounds

/-! ## The budget -/

omit [MeasurableSpace Ω] in
theorem cG_nonneg (P : GP) (x : E d) : 0 ≤ cG P x :=
  div_nonneg (integral_nonneg fun θ => sq_nonneg _) (by positivity)

omit [MeasurableSpace Ω] in
theorem priceF_nonneg (P : GP) (pol : Learner Ω d) (n t : ℕ) (y : (ℕ → ℝ) × Ω) : 0 ≤ priceF P pol n t y := by
  unfold priceF
  split_ifs
  · exact cG_nonneg P _
  · exact le_rfl

/-- **Fact 2, the budget**: `Σ_{t < n} E m_t² ≤ 2B`; the fake run and its prices read no tip. -/
theorem budget_mG (μ : Measure Ω) [IsProbabilityMeasure μ] {P : GP} {pol : Learner Ω d} {n : ℕ} (hg : 0 ≤ P.g)
    (hk : 0 ≤ P.k) (hsc : 0 < P.sc)
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) {B w : ℝ}
    (hB : 0 ≤ B) (hmb : ∀ t s, |mG P pol n B t s| ≤ w) :
    ∑ t ∈ range n, ∫ s, mG P pol n B t s ^ 2 ∂gameLaw (tipLaw d) μ ≤ 2 * B := by
  refine budget_le (tipLaw d) μ (g := priceF P pol n) (h := gapF P pol n) hB (fun t s => rfl)
    (measurable_mG hg hk hpol B) hmb (priceF_nonneg P pol n) (measurable_priceF hg hk hpol) (fun t y => ?_) n
  unfold gapF priceF
  by_cases ht : t < n
  · simp only [ht, ite_true]
    unfold cG
    rw [show (fun θ : E d => ((bowlG d P.g P.k (xF P pol t ((θ, y) : Sample d Ω).2) -
        dentG d P.g P.k ((θ, y) : Sample d Ω).1 (xF P pol t ((θ, y) : Sample d Ω).2)) / P.sc) ^ 2) =
        fun θ => (bowlG d P.g P.k (xF P pol t y) - dentG d P.g P.k θ (xF P pol t y)) ^ 2 / P.sc ^ 2 from
      funext fun θ => by rw [div_pow]]
    rw [integral_div]
    field_simp
  · simp [ht]

/-! ## Fact 1: the real run on the shifted sample is the fake run until the budget is spent -/

omit [MeasurableSpace Ω] in
/-- On the rounds before the budget is spent, the real run on the shifted sample is the fake run. -/
theorem histG_shift {P : GP} {pol : Learner Ω d} {n : ℕ} {B : ℝ} (hsc : P.sc ≠ 0) (s : Sample d Ω) {t : ℕ}
    (ht : t ≤ n) (hall : ∀ u < t, cumF P pol n u s.2 ≤ B) :
    histG P pol t (shiftAll (mG P pol n B) n s) = histF P pol t s.2 := by
  let _ : MeasurableSpace Ω := ⊤
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (by omega) (fun u hu => hall u (by omega))
    have htn : t < n := by omega
    have hct : cumF P pol n t s.2 ≤ B := hall t (by omega)
    unfold histG histF at ih' ⊢
    rw [hist_succ, hist_succ, ih', shiftAll_seed]
    have hnoise := shiftAll_noise (mG_readsBefore P pol n B) n s t
    rw [ite_eq_left htn] at hnoise
    have hm : mG P pol n B t s = (bowlG d P.g P.k (xF P pol t s.2) - dentG d P.g P.k s.1 (xF P pol t s.2)) / P.sc := by
      unfold mG gapF
      rw [ite_eq_left hct, ite_eq_left htn]
    congr 1
    show P.b + dentG d P.g P.k (shiftAll (mG P pol n B) n s).1
        (play pol t s.2.2 (hist (tipLaw d) (ruleQ d P) P.sc pol t (0, s.2.1, s.2.2))) +
        P.sc * (shiftAll (mG P pol n B) n s).2.1 t =
      P.b + bowlG d P.g P.k (play pol t s.2.2 (hist (tipLaw d) (ruleQ d P) P.sc pol t (0, s.2.1, s.2.2))) +
        P.sc * s.2.1 t
    rw [hnoise, hm, shiftAll_fst]
    have hx : play pol t s.2.2 (hist (tipLaw d) (ruleQ d P) P.sc pol t (0, s.2.1, s.2.2)) = xF P pol t s.2 := rfl
    rw [hx]
    field_simp
    ring

omit [MeasurableSpace Ω] in
theorem xG_shift {P : GP} {pol : Learner Ω d} {n : ℕ} {B : ℝ} (hsc : P.sc ≠ 0) (s : Sample d Ω) {t : ℕ}
    (ht : t < n) (hall : ∀ u < t, cumF P pol n u s.2 ≤ B) :
    xG P pol t (shiftAll (mG P pol n B) n s) = xF P pol t s.2 := by
  unfold xG xF
  rw [histG_shift hsc s ht.le hall, shiftAll_seed]

open Classical in
/-- The stopped sum of the dents along the fake run: `S = Σ_{t < n} 1{C_u ≤ B for u < t} D(x̃_t; θ)`. -/
noncomputable def stopS (P : GP) (pol : Learner Ω d) (n : ℕ) (B : ℝ) (s : Sample d Ω) : ℝ :=
  ∑ t ∈ range n, if ∀ u ∈ range t, cumF P pol n u s.2 ≤ B then dentG d P.g P.k s.1 (xF P pol t s.2) else 0

omit [MeasurableSpace Ω] in
/-- **Fact 1**: the regret of the real run on the shifted sample is at least the stopped sum. -/
theorem regGG_shift_ge {P : GP} {pol : Learner Ω d} {n : ℕ} {B : ℝ} (hg : 0 ≤ P.g) (hk : 0 ≤ P.k)
    (hsc : P.sc ≠ 0) (s : Sample d Ω) :
    stopS P pol n B s ≤ regGG P pol n (shiftAll (mG P pol n B) n s) := by
  unfold stopS regGG
  refine Finset.sum_le_sum fun t ht => ?_
  split_ifs with h
  · rw [xG_shift hsc s (Finset.mem_range.1 ht) fun u hu => h u (Finset.mem_range.2 hu), shiftAll_fst]
  · exact dentG_nonneg hg hk _ _

end AdversarialBco.Grow
