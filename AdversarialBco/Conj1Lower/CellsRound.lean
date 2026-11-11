/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Cells
public import AdversarialBco.Conj1Lower.Balance

@[expose] public section

/-!
# The fields of `RoundFacts` that come from the cells

Lemma 9.7 and Lemma LEAK, in the shapes of the fields of `RoundFacts` (Balance.lean).
One round, one path: the law `π` of the tip given `(G_{t-1}, U)`, the frame `(m, A)` with `D_M = DMv`, the play `x`;
the parameters `κ = g/k`, `ε = k`, `r₁ = 5 d^{1/2}` of the strategy `S'(g, k, L, σ)`. The reals of `RoundFacts`:

* `a = massAnn`, the mass of the ripe cells; `pr = massRest`, the mass of rest; `preg = massReg`;
* `H = entAns`, the entropy of the answer: `∑_{c ripe} p_c ln(1/p_c) + p_rest ln(1/p_rest)`;
* `Dbar = dentMean = ∫ D(x; θ) dπ(θ)`, `Drest = dentRest = ∫_{rest} D(x; θ) dπ(θ)`;
* `Pay = ∑_{c ripe} P c`, `P c` the term of the ripe cell `c` in the payment `P'_t` (Ledger.lean proves the bounds (L3) to
  (L5) of Lemma 9.8 on it, the hypotheses of `cells_leak`).

The field `price` is `Irest ≤ g/(σ² P_R) (Drest/pr)` when `pr ≥ 1/2`; Lemma 9.6 (Info.lean) gives
`Irest ≤ E[(q - D)² | rest]/(2σ²) = gapRest/pr/(2σ²)` (the (S1) bound with the centring constant `q(x)` of rest), and
`cells_price` bounds the right side.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Lower

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

open Classical in
/-- The ripe cells. -/
noncomputable def ripeCells (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : Finset Cell :=
  Finset.univ.filter (ripe π A m k dd DMv x)

/-- `a = ∑_{c ripe} π(c)`, the mass announced. -/
noncomputable def massAnn (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : ℝ :=
  ∑ c ∈ ripeCells π A m k dd DMv x, π.real (cellSet A m k dd DMv x c)

/-- `pr = π(rest)`. -/
noncomputable def massRest (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : ℝ :=
  π.real (restSet π A m k dd DMv x)

/-- `preg = π(regular)`. -/
noncomputable def massReg (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : ℝ :=
  π.real (cellSet A m k dd DMv x Cell.regular)

/-- `H = H(A_t)`, the entropy of the answer. -/
noncomputable def entAns (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : ℝ :=
  ∑ c ∈ ripeCells π A m k dd DMv x,
      π.real (cellSet A m k dd DMv x c) * Real.log (1 / π.real (cellSet A m k dd DMv x c)) +
    massRest π A m k dd DMv x * Real.log (1 / massRest π A m k dd DMv x)

/-- `Dbar = ∫ D(x; θ) dπ(θ)`, with `κ = g/k`, `ε = k`, `r₁ = 5 d^{1/2}`. -/
noncomputable def dentMean (π : Measure V) (A : V →L[ℝ] V) (m : V) (g k dd : ℝ) (x : V) : ℝ :=
  ∫ θ, dent A m (g / k) k (5 * Real.sqrt dd) θ x ∂π

/-- `Drest = ∫_{rest} D(x; θ) dπ(θ)`. -/
noncomputable def dentRest (π : Measure V) (A : V →L[ℝ] V) (m : V) (g k dd DMv : ℝ) (x : V) : ℝ :=
  ∫ θ in restSet π A m k dd DMv x, dent A m (g / k) k (5 * Real.sqrt dd) θ x ∂π

/-- `E[(q - D)²; rest]`, the second moment of the gap on rest. -/
noncomputable def gapRest (π : Measure V) (A : V →L[ℝ] V) (m : V) (g k dd DMv : ℝ) (x : V) : ℝ :=
  ∫ θ in restSet π A m k dd DMv x,
    (bowl A m (g / k) k (5 * Real.sqrt dd) x - dent A m (g / k) k (5 * Real.sqrt dd) θ x) ^ 2 ∂π

end Defs

/-! ## The partition: `mass`, `a_nonneg`, `pr_nonneg` -/

/-- The cells partition the space: their masses sum to `1`. -/
theorem sum_cellSet_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    ∑ c, π.real (cellSet A m k dd DMv x c) = 1 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset Cell)) (cellSet A m k dd DMv x) :=
    fun c _ c' _ hcc' => Set.disjoint_left.2 fun θ h1 h2 => hcc' ((show _ = c from h1).symm.trans h2)
  rw [← measureReal_biUnion_finset hdisj fun c _ => measurableSet_cellSet A m k dd DMv x c]
  have : (⋃ c ∈ (Finset.univ : Finset Cell), cellSet A m k dd DMv x c) = Set.univ := by
    ext θ; simp [cellSet]
  rw [this, probReal_univ]

/-- Rest is the union of the cells that are not ripe. -/
theorem massRest_eq_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    massRest π A m k dd DMv x =
      ∑ c ∈ Finset.univ \ ripeCells π A m k dd DMv x, π.real (cellSet A m k dd DMv x c) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ \ ripeCells π A m k dd DMv x)) (cellSet A m k dd DMv x) :=
    fun c _ c' _ hcc' => Set.disjoint_left.2 fun θ h1 h2 => hcc' ((show _ = c from h1).symm.trans h2)
  have hset : restSet π A m k dd DMv x =
      ⋃ c ∈ Finset.univ \ ripeCells π A m k dd DMv x, cellSet A m k dd DMv x c := by
    rw [restSet_eq]
    ext θ
    simp [cellSet, ripeCells]
  unfold massRest
  rw [hset, measureReal_biUnion_finset hdisj fun c _ => measurableSet_cellSet A m k dd DMv x c]

/-- `RoundFacts.mass`: `a + pr = 1`. -/
theorem cells_mass {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    massAnn π A m k dd DMv x + massRest π A m k dd DMv x = 1 := by
  rw [massRest_eq_sum, massAnn, add_comm, Finset.sum_sdiff (Finset.subset_univ _), sum_cellSet_eq_one]

/-- `RoundFacts.a_nonneg`. -/
theorem cells_a_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : 0 ≤ massAnn π A m k dd DMv x := by
  exact Finset.sum_nonneg fun _ _ => measureReal_nonneg

/-- `RoundFacts.pr_nonneg`. -/
theorem cells_pr_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : 0 ≤ massRest π A m k dd DMv x := by
  exact measureReal_nonneg

/-! ## Lemma LEAK: `leak`, `leak_mass` -/

/-- `RoundFacts.leak` and `RoundFacts.leak_mass` (Lemma LEAK), with `Pay = ∑_{c ripe} P c`: each ripe cell against its
own term `P c` of the payment, which satisfies (L3) on the tail and (L4), (L5) on the inner and the outer cell. -/
theorem cells_leak {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (hk : 1 ≤ k)
    (hd : 2048 * k ≤ dd) (x : V) (P : Cell → ℝ)
    (hPt : ripe π A m k dd DMv x Cell.tail →
      π.real (cellSet A m k dd DMv x Cell.tail) * k / 4 ≤ P Cell.tail ∧
        (∫ θ in cellSet A m k dd DMv x Cell.tail, readT A m θ x ^ 2 ∂π) / 8 ≤ P Cell.tail)
    (hPs : ∀ c, c = Cell.outer ∨ c = Cell.inner → ripe π A m k dd DMv x c →
      π.real (cellSet A m k dd DMv x c) * dd / 62 ≤ P c) :
    entAns π A m k dd DMv x ≤ 4 * (3 * Real.log dd + 1) / k * ∑ c ∈ ripeCells π A m k dd DMv x, P c ∧
      massAnn π A m k dd DMv x ≤ 4 / k * ∑ c ∈ ripeCells π A m k dd DMv x, P c := by
  have hmass := cells_mass π A m k dd DMv x
  have hpr0 := cells_pr_nonneg π A m k dd DMv x
  unfold massAnn at hmass
  have hrest : massRest π A m k dd DMv x =
      1 - ∑ c ∈ ripeCells π A m k dd DMv x, π.real (cellSet A m k dd DMv x c) := by linarith
  have hcell : ∀ c ∈ ripeCells π A m k dd DMv x,
      π.real (cellSet A m k dd DMv x c) * (Real.log (1 / π.real (cellSet A m k dd DMv x c)) + 1) ≤
          4 * (3 * Real.log dd + 1) / k * P c ∧
        π.real (cellSet A m k dd DMv x c) ≤ 4 / k * P c := by
    intro c hc
    have hr : ripe π A m k dd DMv x c := by
      unfold ripeCells at hc
      classical
      exact (Finset.mem_filter.1 hc).2
    refine leak_cell π A m k dd DMv hk hd x c hr (P c) ?_ ?_
    · rintro rfl; exact hPt hr
    · intro h; exact hPs c h hr
  constructor
  · unfold entAns
    rw [hrest, Finset.mul_sum]
    calc _ ≤ ∑ c ∈ ripeCells π A m k dd DMv x,
            π.real (cellSet A m k dd DMv x c) * (Real.log (1 / π.real (cellSet A m k dd DMv x c)) + 1) :=
          entropy_le_ripe _ (fun c => π.real (cellSet A m k dd DMv x c)) (fun c _ => measureReal_nonneg)
            (by linarith)
      _ ≤ _ := Finset.sum_le_sum fun c hc => (hcell c hc).1
  · unfold massAnn
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c hc => (hcell c hc).2

/-! ## Lemma 9.7: `price`, `drest_nonneg`, `drest_le`, `floor`, `reg` -/

/-- The second moment of `T` on the tail is finite when the tip has a second moment. -/
theorem integrableOn_tail_readT_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V)
    (h2 : Integrable (fun θ => ‖θ‖ ^ 2) π) :
    IntegrableOn (fun θ => readT A m θ x ^ 2) (cellSet A m k dd DMv x Cell.tail) π := by
  refine Integrable.integrableOn ?_
  have hbound : ∀ θ, readT A m θ x ^ 2 ≤ 2 * ‖A‖ ^ 2 * (‖θ‖ ^ 2 + ‖m‖ ^ 2) := by
    intro θ
    have hT : |readT A m θ x| ≤ ‖A (θ - m)‖ := by
      unfold readT
      rcases eq_or_lt_of_le (norm_nonneg (A (x - m))) with h | h
      · rw [← h, div_zero, abs_zero]; exact norm_nonneg _
      · rw [abs_div, abs_norm, div_le_iff₀ h]
        calc _ ≤ ‖A (x - m)‖ * ‖A (θ - m)‖ := abs_real_inner_le_norm _ _
          _ = _ := mul_comm _ _
    have hA : ‖A (θ - m)‖ ≤ ‖A‖ * (‖θ‖ + ‖m‖) :=
      (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
    have hsq : readT A m θ x ^ 2 ≤ (‖A‖ * (‖θ‖ + ‖m‖)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hT.trans hA) 2
    have hAm : (‖A‖ * (‖θ‖ + ‖m‖)) ^ 2 ≤ 2 * ‖A‖ ^ 2 * (‖θ‖ ^ 2 + ‖m‖ ^ 2) := by
      have := sq_nonneg (‖θ‖ - ‖m‖)
      have := sq_nonneg ‖A‖
      nlinarith
    linarith
  refine Integrable.mono' ((h2.add (integrable_const (‖m‖ ^ 2))).const_mul (2 * ‖A‖ ^ 2))
    ((continuous_readT_tip A m x).pow 2).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbound θ

/-- The dent is integrable in the tip: it is measurable, between `0` and `q(x)`. -/
theorem integrable_dent_tip {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (κ ε r₁ : ℝ) (hκ : 0 ≤ κ)
    (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (x : V) : Integrable (fun θ => dent A m κ ε r₁ θ x) π := by
  refine Integrable.mono' (integrable_const (bowl A m κ ε r₁ x))
    (measurable_dent_tip A m κ ε r₁ hκ hε hr x).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (dent_nonneg A m κ ε r₁ hκ hε hr θ x)]
  exact dent_le_bowl A m κ ε r₁ hκ hε hr θ x

/-- The price of rest (Lemma 9.7 (ii), the part of the cells): for `pr ≥ 1/2`,
`E[(q - D)² | rest]/(2σ²) ≤ g/(σ² P_R) E[D | rest]`. With Lemma 9.6's
`Irest ≤ gapRest/pr/(2σ²)` this is `RoundFacts.price`. -/
theorem cells_price {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (g σ k dd DMv : ℝ)
    (hg : 0 < g) (hσ : 0 < σ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (x : V)
    (hT2 : IntegrableOn (fun θ => readT A m θ x ^ 2) (cellSet A m k dd DMv x Cell.tail) π) :
    1 / 2 ≤ massRest π A m k dd DMv x →
      gapRest π A m g k dd DMv x / massRest π A m k dd DMv x / (2 * σ ^ 2) ≤
        g / (σ ^ 2 * priceR dd k) * (dentRest π A m g k dd DMv x / massRest π A m k dd DMv x) := by
  intro hpr
  have hk0 : 0 < k := by linarith
  have hdd : 0 < dd := by linarith
  have hκ : 0 < g / k := div_pos hg hk0
  set pr := massRest π A m k dd DMv x with hpr_def
  set φ := huber (5 * Real.sqrt dd) k ‖A (x - m)‖ with hφ_def
  set G := gapRest π A m g k dd DMv x with hG
  set Dr := dentRest π A m g k dd DMv x with hDr
  have hpr0 : 0 < pr := by linarith
  have hφk : k ≤ φ := huber_ge _ _ _ (by positivity)
  have hφ0 : 0 ≤ φ := by linarith
  have h1 : G ≤ (g / k) ^ 2 * ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * φ) :=
    rest_second_moment π A m (g / k) k dd DMv hκ hk hd hDM x hT2
  have h2 : massReg π A m k dd DMv x * (g / k * φ / 2) ≤ Dr :=
    rest_floor π A m (g / k) k dd DMv hκ hk0 hd hDM x
  have h3 : 1 / 2 ≤ massReg π A m k dd DMv x / pr :=
    rest_ratio_arith k dd _ pr hk hd hpr (rest_regular_mass π A m k dd DMv hk hd x)
  have hD : g / k * φ ≤ 4 * (Dr / pr) := by
    have hreg : pr / 2 ≤ massReg π A m k dd DMv x := by
      rw [le_div_iff₀ hpr0] at h3; linarith
    have hκφ : 0 ≤ g / k * φ := by positivity
    have h4 : pr * (g / k * φ) ≤ 4 * Dr := by nlinarith
    rw [mul_div_assoc', le_div_iff₀ hpr0]
    linarith
  have hV : G / ((g / k) ^ 2 * pr) ≤ (2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * φ / pr := by
    rw [div_le_div_iff₀ (by positivity) hpr0]
    have : 0 < (g / k) ^ 2 := by positivity
    nlinarith
  have hI : G / pr / (2 * σ ^ 2) ≤ (g / k) ^ 2 * (G / ((g / k) ^ 2 * pr)) / (2 * σ ^ 2) := by
    apply le_of_eq
    field_simp
  exact rest_price_arith g k dd σ φ (Dr / pr) pr _ _ hg hk0 hdd hσ hpr hφ0 hI hV hD

/-- `RoundFacts.drest_nonneg`. -/
theorem cells_drest_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (g k dd DMv : ℝ) (hg : 0 ≤ g) (hk : 0 ≤ k) (x : V) :
    0 ≤ dentRest π A m g k dd DMv x := by
  exact integral_nonneg fun θ => dent_nonneg A m _ _ _ (div_nonneg hg hk) hk (by positivity) θ x

/-- `RoundFacts.drest_le`. -/
theorem cells_drest_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (g k dd DMv : ℝ) (hg : 0 ≤ g)
    (hk : 0 ≤ k) (x : V) : dentRest π A m g k dd DMv x ≤ dentMean π A m g k dd x := by
  exact setIntegral_le_integral (integrable_dent_tip π A m _ _ _ (div_nonneg hg hk) hk (by positivity) x)
    (ae_of_all _ fun θ => dent_nonneg A m _ _ _ (div_nonneg hg hk) hk (by positivity) θ x)

/-- `RoundFacts.floor`: `π(regular) g/2 ≤ E[D]` (Lemma 9.7 (i), `q ≥ κ k = g`). -/
theorem cells_floor {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (g k dd DMv : ℝ) (hg : 0 < g)
    (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (x : V) :
    massReg π A m k dd DMv x * g / 2 ≤ dentMean π A m g k dd x := by
  have h := floor_round π A m (g / k) k dd DMv (div_pos hg hk) hk hd hDM x
  have he : g / k * k / 2 = g / 2 := by field_simp
  rw [he] at h
  unfold massReg dentMean
  linarith

/-- `RoundFacts.reg`: `pr - 3k²/d² ≤ π(regular)` (Lemma 9.7 (i)). -/
theorem cells_reg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (hk : 1 ≤ k)
    (hd : 2048 * k ≤ dd) (x : V) :
    massRest π A m k dd DMv x - 3 * k ^ 2 / dd ^ 2 ≤ massReg π A m k dd DMv x := by
  exact rest_regular_mass π A m k dd DMv hk hd x

end AdversarialBco.Lower
