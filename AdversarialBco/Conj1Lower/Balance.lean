/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The balance of the balance proposition and the arithmetic of the game proposition

The paper's balance and game propositions, with
the channel bound (S1): every answer cell carries at most
`B = (3L/2 + g)²/(8σ²)` nats. Pure arithmetic on reals: no measure, no probability.

The layer of one round, matching the interface `round`

* `RoundFacts`: the per-round facts at one live round of one path (given the history with the answers and the
  learner's seed), as reals: the floor, the price, the leak, the chain rule, the channel bound. `round_bound` turns
  them into three linear inequalities, the case split on `p_rest` done.

Rounds are indexed by `t ∈ Finset.range n`. Who discharges what: CellsRound.lean, Ledger.lean and Info.lean
the fields of `RoundFacts`; Top.lean integrates `round_bound` over the live event, proves the live count, the
regret identity `E R_n = ∑ Dm t` (the legality lemma) and the coupling `E R_n(bounded) ≥ E R_n(Gaussian) - 1/n`;
Ledger.lean the
payment, Info.lean the count.
-/

open Finset

namespace AdversarialBco.Lower

/-! ## Constants of the strategy `S'(g, k, L, σ)` -/

/-- The price of rest of the rest lemma (ii), `P_R = d²/(4194372 k²)`. -/
noncomputable def priceR (dd k : ℝ) : ℝ := dd ^ 2 / (4194372 * k ^ 2)

/-- The floor `w* = κ r₁ / L` with `κ = g/k`, `r₁ = 5 d^{1/2}`. -/
noncomputable def wStar (dd k L g : ℝ) : ℝ := g / k * (5 * Real.sqrt dd) / L

/-- `X = r₀²/(d w²)`, `r₀ = 1/2` (the count at `w`). -/
noncomputable def xCount (dd w : ℝ) : ℝ := (1 / 2) ^ 2 / (dd * w ^ 2)

/-- The count of the count lemma (b), `N* = (d/4) ln(r₀²/(2 d w²)) - (1/2) ln(π d) - 1/d`, `r₀ = 1/2`
(Binet's remainder gives `1/(6d)`; `1/d` is what the crude Stirling bound of route (S3) gives for every
`d ≥ 1`, and (C1) to (C3) hold with it). -/
noncomputable def nStar (dd w : ℝ) : ℝ :=
  dd / 4 * Real.log ((1 / 2) ^ 2 / (2 * dd * w ^ 2)) - Real.log (Real.pi * dd) / 2 - 1 / dd

/-- The ledger's budget of (L6) in the crude form `R_L = (d/2) ln(1 + r₀²/(d w²))`, `r₀ = 1/2` (from
`Λ(π₁) ≤ (d/2) ln(r₀²/d + w²)`, `tr Σ ≤ r₀²`; a term `d + 2` is not needed by (C2)). -/
noncomputable def ledgerR (dd w : ℝ) : ℝ := dd / 2 * Real.log (1 + (1 / 2) ^ 2 / (dd * w ^ 2))

/-- The channel bound (S1): the signal of a cell takes its values in an interval of length `3L/2 + g`, so its
information is at most `(3L/2 + g)²/(8σ²)`. -/
noncomputable def chanB (L g σ : ℝ) : ℝ := (3 * L / 2 + g) ^ 2 / (8 * σ ^ 2)

/-- The scale of the balance proposition's rate, `k = 120 ln d + 68`. -/
noncomputable def kRipe (dd : ℝ) : ℝ := 120 * Real.log dd + 68

/-- The noise scale of the game proposition, `σ = L = 1/(8 (6 ln n)^{1/2})`. -/
noncomputable def sigB (nn : ℝ) : ℝ := 1 / (8 * Real.sqrt (6 * Real.log nn))

/-- `Γ = ln(n/d⁵)`. -/
noncomputable def gamR (dd nn : ℝ) : ℝ := Real.log (nn / dd ^ 5)

/-- The depth of the balance proposition's rate, `g = 2·10⁻⁴ σ d^{3/2} Γ^{1/2}/(k n^{1/2})`. -/
noncomputable def gRipe (dd nn σ : ℝ) : ℝ :=
  2 / 10 ^ 4 * σ * (dd * Real.sqrt dd) * Real.sqrt (gamR dd nn) / (kRipe dd * Real.sqrt nn)

/-! ## The interface `round` -/

/-- The facts of one live round `t`, given the history with the answers `G_{t-1}` and the learner's seed `U`, with
`π = π_t` and the play `x = x_t`:

* `a = ∑_{c ripe} π(c)`, the mass announced; `pr = π(rest)`;
* `H = H(A_t)`, the entropy of the answer; `Iann = ∑_{c ripe} π(c) I_{t,c}`; `Irest = I_{t,rest}`;
  `J = J_t = I(x°; (A_t, Y_t) | G_{t-1}, U)`;
* `Pay = P'_t`, the payment of the ripe cells to the ledger;
* `Dbar = E[D_π(x; x°) | G_{t-1}, U] = ∫ D_π(x; θ) dπ(θ)`, `Drest = ∫_{rest} D_π(x; θ) dπ(θ)`;
* `preg = π(regular)`.

The constants: `dd = d`, `k`, the depth `g`, the noise `σ`, the channel bound `B` (`chanB L g σ` under (S1)).
`Iann` and `Irest` need not be the mutual informations themselves: any reals with the fields below do, for instance
the bounds of route (S1) with one centring constant per answer, the one of rest chosen by the case `p_rest ≥ 1/2`. -/
structure RoundFacts (dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg : ℝ) : Prop where
  /-- The ripe cells and rest partition the ball. -/
  mass : a + pr = 1
  a_nonneg : 0 ≤ a
  pr_nonneg : 0 ≤ pr
  /-- The chain-rule lemma: `J_t = H(A_t) + ∑_c p_c I_{t,c}` over the ripe cells and rest (Info.lean). -/
  chain : J ≤ H + Iann + pr * Irest
  /-- (S1) on each ripe cell: `I_{t,c} ≤ B` (Info.lean). -/
  ann_le : Iann ≤ B * a
  /-- (S1) on rest, used on the rounds with `p_rest < 1/2` only: `I_{t,rest} ≤ B` (Info.lean). -/
  rest_le : pr < 1 / 2 → Irest ≤ B
  /-- Lemma LEAK, the entropy: `H(A_t) ≤ (4 (3 ln d + 1)/k) P'_t`. -/
  leak : H ≤ 4 * (3 * Real.log dd + 1) / k * Pay
  /-- Lemma LEAK, the mass: `∑_{c ripe} p_c ≤ (4/k) P'_t`. -/
  leak_mass : a ≤ 4 / k * Pay
  /-- The rest lemma (ii), the price: `I_{t,rest} ≤ g E[D | rest]/(σ² P_R)` when `p_rest ≥ 1/2`. -/
  price : 1 / 2 ≤ pr → Irest ≤ g / (σ ^ 2 * priceR dd k) * (Drest / pr)
  /-- The dent is nonnegative (Lemma D (a)). -/
  drest_nonneg : 0 ≤ Drest
  /-- The dent is nonnegative off rest (Lemma D (a)). -/
  drest_le : Drest ≤ Dbar
  /-- The rest lemma (i) and `q ≥ g`, the floor: `E[D | G_{t-1}, U] ≥ π(regular) g/2`. -/
  floor : preg * g / 2 ≤ Dbar
  /-- The rest lemma (i), the mass: `π(regular) ≥ p_rest - 3k²/d²`. -/
  reg : pr - 3 * k ^ 2 / dd ^ 2 ≤ preg

/-! ## One round -/

/-- `3k²/d² ≤ 1/1000` for `d ≥ 2048 k`. -/
theorem three_k_sq_le (k dd : ℝ) (hk : 0 < k) (hd : 2048 * k ≤ dd) : 3 * k ^ 2 / dd ^ 2 ≤ 1 / 1000 := by
  have hdd : 0 < dd := by
    linarith
  have hddsq : 0 < dd ^ 2 := pow_pos hdd 2
  have h1000 : (0 : ℝ) < 1000 := by norm_num
  rw [div_le_div_iff₀ hddsq h1000]
  nlinarith

theorem priceR_nonneg (dd k : ℝ) : 0 ≤ priceR dd k := by
  unfold priceR
  apply div_nonneg
  · apply pow_two_nonneg
  · positivity

/-- The information of a round: the case split on `p_rest`. -/
theorem round_J {dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg : ℝ} (hk : 0 < k) (hg : 0 ≤ g) (hB : 0 ≤ B)
    (h : RoundFacts dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg) :
    J ≤ (4 * (3 * Real.log dd + 1) + 8 * B) / k * Pay + g / (σ ^ 2 * priceR dd k) * Dbar := by
  set c := g / (σ ^ 2 * priceR dd k) with hc
  have hc0 : 0 ≤ c := by unfold priceR at hc; rw [hc]; positivity
  have hPay : 0 ≤ Pay := by
    have h1 := h.leak_mass
    have h2 : 0 ≤ 4 / k * Pay := le_trans h.a_nonneg h1
    exact nonneg_of_mul_nonneg_right (by linarith [mul_comm (4 / k) Pay]) (by positivity : (0:ℝ) < 4 / k)
  have hBa : B * a ≤ 4 * B / k * Pay := by
    have := mul_le_mul_of_nonneg_left h.leak_mass hB
    calc B * a ≤ B * (4 / k * Pay) := this
      _ = 4 * B / k * Pay := by ring
  have hBP : 0 ≤ 4 * B / k * Pay := by positivity
  have hcD : 0 ≤ c * Dbar := mul_nonneg hc0 (h.drest_nonneg.trans h.drest_le)
  have hsplit : (4 * (3 * Real.log dd + 1) + 8 * B) / k * Pay =
      4 * (3 * Real.log dd + 1) / k * Pay + 2 * (4 * B / k * Pay) := by ring
  rw [hsplit]
  have hchain := h.chain
  have hleak := h.leak
  have hann := h.ann_le
  by_cases hpr : 1 / 2 ≤ pr
  · have hpr0 : 0 < pr := by linarith
    have hI := mul_le_mul_of_nonneg_left (h.price hpr) hpr0.le
    have hpI : pr * Irest ≤ c * Dbar := by
      calc pr * Irest ≤ pr * (c * (Drest / pr)) := hI
        _ = c * Drest := by field_simp
        _ ≤ c * Dbar := mul_le_mul_of_nonneg_left h.drest_le hc0
    linarith
  · rw [not_le] at hpr
    have hIr := h.rest_le hpr
    have hpa : pr ≤ a := by linarith [h.mass]
    have hpI : pr * Irest ≤ B * a := by
      calc pr * Irest ≤ pr * B := mul_le_mul_of_nonneg_left hIr h.pr_nonneg
        _ ≤ a * B := mul_le_mul_of_nonneg_right hpa hB
        _ = B * a := by ring
    linarith

/-- The floor of a round: `E[D | G_{t-1}, U] ≥ (g/2)(0.999 - ∑_{c ripe} p_c)`. -/
theorem round_floor {dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg : ℝ} (hk : 0 < k)
    (hd : 2048 * k ≤ dd) (hg : 0 ≤ g) (h : RoundFacts dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg) :
    g / 2 * (999 / 1000 - a) ≤ Dbar := by
  have hpr : pr = 1 - a := by linarith [h.mass]
  have hpreg : 999 / 1000 - a ≤ preg := by
    have h1 : pr - 3 * k ^ 2 / dd ^ 2 ≤ preg := h.reg
    have h2 : 3 * k ^ 2 / dd ^ 2 ≤ 1 / 1000 := three_k_sq_le k dd hk hd
    have h3 : pr - 3 * k ^ 2 / dd ^ 2 ≥ 999 / 1000 - a := by
      rw [hpr]
      linarith
    linarith
  have hhalf : 0 ≤ g / 2 := by linarith
  have hfloor' : g / 2 * preg ≤ Dbar := by
    calc
      g / 2 * preg = preg * (g / 2) := mul_comm _ _
      _ = preg * g / 2 := by rw [mul_div_assoc]
      _ ≤ Dbar := h.floor
  calc
    g / 2 * (999 / 1000 - a) ≤ g / 2 * preg := mul_le_mul_of_nonneg_left hpreg hhalf
    _ ≤ Dbar := hfloor'

/-- The round, in the form that is integrated over the game. -/
theorem round_bound {dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg : ℝ} (hk : 0 < k) (hd : 2048 * k ≤ dd)
    (hg : 0 ≤ g) (hB : 0 ≤ B) (h : RoundFacts dd k g σ B a pr H Iann Irest J Pay Dbar Drest preg) :
    J ≤ (4 * (3 * Real.log dd + 1) + 8 * B) / k * Pay + g / (σ ^ 2 * priceR dd k) * Dbar ∧
      g / 2 * (999 / 1000 - a) ≤ Dbar ∧ a ≤ 4 / k * Pay :=
  ⟨round_J hk hg hB h, round_floor hk hd hg h, h.leak_mass⟩

/-- The three inequalities of `round_bound`, holding on the live event `S` of a round, integrated over `S`: the
fields `round_J`, `round_floor`, `round_mass` of the game facts at that round, with `lm t = μ.real S` (for Top.lean). -/
theorem round_integral {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S) (c₁ c g k : ℝ) (J P a D : Ω → ℝ)
    (hJ : MeasureTheory.Integrable J μ) (hP : MeasureTheory.Integrable P μ) (ha : MeasureTheory.Integrable a μ)
    (hD : MeasureTheory.Integrable D μ)
    (h : ∀ ω ∈ S, J ω ≤ c₁ * P ω + c * D ω ∧ g / 2 * (999 / 1000 - a ω) ≤ D ω ∧ a ω ≤ 4 / k * P ω) :
    ∫ ω in S, J ω ∂μ ≤ c₁ * ∫ ω in S, P ω ∂μ + c * ∫ ω in S, D ω ∂μ ∧
      g / 2 * (999 / 1000 * μ.real S - ∫ ω in S, a ω ∂μ) ≤ ∫ ω in S, D ω ∂μ ∧
      ∫ ω in S, a ω ∂μ ≤ 4 / k * ∫ ω in S, P ω ∂μ := by
  open MeasureTheory in
  refine ⟨?_, ?_, ?_⟩
  · rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hP.integrableOn.const_mul _)
      (hD.integrableOn.const_mul _)]
    exact setIntegral_mono_on hJ.integrableOn ((hP.integrableOn.const_mul _).add (hD.integrableOn.const_mul _))
      hS fun ω hω => (h ω hω).1
  · have : g / 2 * (999 / 1000 * μ.real S - ∫ ω in S, a ω ∂μ) = ∫ ω in S, g / 2 * (999 / 1000 - a ω) ∂μ := by
      rw [integral_const_mul, integral_sub (integrable_const _) ha.integrableOn, setIntegral_const, smul_eq_mul]
      ring
    rw [this]
    exact setIntegral_mono_on ((integrable_const _).sub ha.integrableOn |>.const_mul _) hD.integrableOn hS
      fun ω hω => (h ω hω).2.1
  · rw [← integral_const_mul]
    exact setIntegral_mono_on ha.integrableOn (hP.integrableOn.const_mul _) hS fun ω hω => (h ω hω).2.2

/-! ## The count at the floor: (C1) to (C3) -/

theorem nStar_eq_x (dd w : ℝ) :
    nStar dd w = dd / 4 * Real.log (xCount dd w / 2) - Real.log (Real.pi * dd) / 2 - 1 / dd := by
  unfold nStar xCount
  have h : ((1 / 2 : ℝ) ^ 2 / (dd * w ^ 2)) / 2 = (1 / 2 : ℝ) ^ 2 / (2 * dd * w ^ 2) := by
    rw [div_div]
    ring
  rw [h]

/-- `(1/2) ln(π d) + 1/d ≤ 0.0005 d` for `d ≥ 12288`. -/
theorem logpi_le (dd : ℝ) (hd : 12288 ≤ dd) : Real.log (Real.pi * dd) / 2 + 1 / dd ≤ dd / 2000 := by
  have hd0 : 0 < dd := by linarith
  have h1 : Real.log (Real.pi * dd) ≤ Real.log (4 * dd) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.pi_lt_four])
  have h2 : Real.log (4 * dd) = Real.log (2 ^ 16) + Real.log (dd / 16384) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; ring
  have h3 := Real.log_le_sub_one_of_pos (show 0 < dd / 16384 by positivity)
  have h4 : Real.log ((2:ℝ) ^ 16) = 16 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h5 := Real.log_two_lt_d9
  have h6 : 1 / dd ≤ 1 / 12288 := by rw [div_le_div_iff₀ hd0 (by norm_num)]; linarith
  rw [h4] at h2
  rw [h2] at h1
  norm_num at h5
  linarith

theorem nStar_ge_x (dd w : ℝ) (hd : 12288 ≤ dd) : dd / 4 * Real.log (xCount dd w / 2) - dd / 2000 ≤ nStar dd w := by
  rw [nStar_eq_x dd w]
  linarith [logpi_le dd hd]

theorem ledgerR_le_x (dd w : ℝ) (hd : 0 < dd) : ledgerR dd w ≤ dd / 2 * Real.log (1 + xCount dd w) := by
  unfold ledgerR xCount
  exact le_refl _

/-- `2 ln(1 + X) + 0.006 ≤ 3 ln(X/2)` for `X ≥ 15`. -/
theorem log_c2 (X : ℝ) (hX : 15 ≤ X) : 2 * Real.log (1 + X) + 6 / 1000 ≤ 3 * Real.log (X / 2) := by
  have hX0 : 0 < X := by linarith
  have he : Real.exp (6 / 1000) ≤ 101 / 100 := by
    have := Real.add_one_le_exp (-(6 / 1000) : ℝ)
    have h3 : Real.exp (6 / 1000) * Real.exp (-(6 / 1000)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (6 / 1000 : ℝ)]
  have hp : (1 + X) ^ 2 * Real.exp (6 / 1000) ≤ (X / 2) ^ 3 := by
    have : (1 + X) ^ 2 * (101 / 100) ≤ (X / 2) ^ 3 := by nlinarith [sq_nonneg (X - 15), mul_nonneg (by linarith : (0:ℝ) ≤ X - 15) (sq_nonneg X)]
    nlinarith [sq_nonneg (1 + X)]
  have := Real.log_le_log (by positivity) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow, Real.log_pow] at this
  push_cast at this
  linarith

/-- (C2): `R_L ≤ 3 N*` for `X ≥ 15`, `d ≥ 12288`. -/
theorem ledgerR_three (dd w : ℝ) (hd : 12288 ≤ dd) (hX : 15 ≤ xCount dd w) : ledgerR dd w ≤ 3 * nStar dd w := by
  nlinarith [ledgerR_le_x dd w (by linarith), log_c2 (xCount dd w) hX, nStar_ge_x dd w hd]

/-- (R2) gives `X ≥ 16` at the floor `w*`. -/
theorem xCount_wStar_ge (dd k L g : ℝ) (hd : 0 < dd) (hk : 0 < k) (hL : 0 < L) (hg : 0 < g)
    (hR2 : g ≤ k * L / (40 * dd)) : 16 ≤ xCount dd (wStar dd k L g) := by
  have he : xCount dd (wStar dd k L g) = k ^ 2 * L ^ 2 / (100 * g ^ 2 * dd ^ 2) := by
    unfold xCount wStar
    have hs := Real.sq_sqrt hd.le
    have hs0 := Real.sqrt_pos.mpr hd
    generalize Real.sqrt dd = s at *
    subst hs
    field_simp
    ring
  rw [he, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity)] at hR2
  have h0 : 0 ≤ g * (40 * dd) := by positivity
  nlinarith [mul_le_mul hR2 hR2 h0 (by positivity)]

/-! ## The balance proposition: the rate, `L = σ`, `k = 120 ln d + 68`, `g = gRipe d n σ` -/

theorem kRipe_ge (dd : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) : 240 ≤ kRipe dd ∧ 491520 ≤ dd := by
  have hlog_nonneg : 0 ≤ Real.log dd := Real.log_nonneg hd1
  have hkRipe_ge_68 : (68 : ℝ) ≤ kRipe dd := by
    dsimp [kRipe]
    nlinarith
  have hdd_ge_139264 : (139264 : ℝ) ≤ dd := by
    nlinarith
  have h_two_pow_17_pos : (0 : ℝ) < (2 : ℝ) ^ 17 := by norm_num
  have h_131072_le_139264 : (131072 : ℝ) ≤ (139264 : ℝ) := by norm_num
  have h_dd_ge_2pow17 : (2 : ℝ) ^ 17 ≤ dd := by
    nlinarith
  have hlog_ge_11 : (11 : ℝ) ≤ Real.log dd := by
    have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlog_2pow17 : Real.log ((2 : ℝ) ^ 17) = (17 : ℝ) * Real.log 2 := Real.log_pow (2 : ℝ) 17
    have h17log2_gt_11 : (11 : ℝ) < (17 : ℝ) * Real.log 2 := by
      nlinarith
    have hlog_2pow17_gt_11 : (11 : ℝ) < Real.log ((2 : ℝ) ^ 17) := by
      rw [hlog_2pow17]
      exact h17log2_gt_11
    have hlog_le : Real.log ((2 : ℝ) ^ 17) ≤ Real.log dd :=
      Real.log_le_log h_two_pow_17_pos h_dd_ge_2pow17
    nlinarith
  have hkRipe_ge_240 : (240 : ℝ) ≤ kRipe dd := by
    dsimp [kRipe]
    nlinarith
  have hdd_ge_491520 : (491520 : ℝ) ≤ dd := by
    nlinarith
  exact And.intro hkRipe_ge_240 hdd_ge_491520

theorem gamR_ge (dd nn : ℝ) (hd : 0 < dd) (hn : Real.exp 4 * dd ^ 5 ≤ nn) : 4 ≤ gamR dd nn := by
  unfold gamR
  have h5 : 0 < dd ^ 5 := by positivity
  have h : Real.exp 4 ≤ nn / dd ^ 5 := by rw [le_div_iff₀ h5]; exact hn
  calc (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
    _ ≤ Real.log (nn / dd ^ 5) := Real.log_le_log (Real.exp_pos 4) h

theorem n_eq_exp (dd nn : ℝ) (hd : 0 < dd) (hn : 0 < nn) : nn = dd ^ 5 * Real.exp (gamR dd nn) := by
  have hpos : 0 < nn / dd ^ 5 := div_pos hn (pow_pos hd 5)
  calc
    nn = dd ^ 5 * (nn / dd ^ 5) := by field_simp [ne_of_gt (pow_pos hd 5)]
    _ = dd ^ 5 * Real.exp (Real.log (nn / dd ^ 5)) := by rw [Real.exp_log hpos]
    _ = dd ^ 5 * Real.exp (gamR dd nn) := rfl

theorem xCount_ripe (dd nn σ : ℝ) (hd : 0 < dd) (hk : 0 < kRipe dd) (hσ : 0 < σ) (hn : 0 < nn)
    (hΓ : 0 < gamR dd nn) :
    xCount dd (wStar dd (kRipe dd) σ (gRipe dd nn σ)) =
      kRipe dd ^ 4 * nn / (4 / 10 ^ 6 * dd ^ 5 * gamR dd nn) := by
  unfold xCount wStar gRipe
  generalize kRipe dd = k at hk ⊢
  generalize gamR dd nn = Γ at hΓ ⊢
  have hs := Real.sq_sqrt hd.le
  have hr := Real.sq_sqrt hn.le
  have hu := Real.sq_sqrt hΓ.le
  have hs0 := Real.sqrt_pos.mpr hd
  have hr0 := Real.sqrt_pos.mpr hn
  have hu0 := Real.sqrt_pos.mpr hΓ
  generalize Real.sqrt dd = s at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs hr hu
  field_simp
  ring

/-- (R2) at the rate's parameters. -/
theorem R2_ripe (dd nn σ : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) (hσ : 0 < σ)
    (hn : Real.exp 4 * dd ^ 5 ≤ nn) : gRipe dd nn σ ≤ kRipe dd * σ / (40 * dd) := by
  obtain ⟨hk, -⟩ := kRipe_ge dd hd1 hd
  have hd0 : 0 < dd := by linarith
  have hΓ := gamR_ge dd nn hd0 hn
  have hn0 : 0 < nn := lt_of_lt_of_le (by positivity) hn
  have hnE := n_eq_exp dd nn hd0 hn0
  have hexp : gamR dd nn ≤ Real.exp (gamR dd nn) := by linarith [Real.add_one_le_exp (gamR dd nn)]
  have hk1 : 1 ≤ kRipe dd ^ 4 := one_le_pow₀ (by linarith)
  unfold gRipe
  generalize kRipe dd = k at *
  generalize gamR dd nn = Γ at *
  have key : 64 / 10 ^ 6 * dd ^ 5 * Γ ≤ k ^ 4 * nn := by
    have h5 : 0 ≤ dd ^ 5 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hexp h5
    have h2 := mul_le_mul_of_nonneg_right hk1 (by positivity : (0:ℝ) ≤ dd ^ 5 * Real.exp Γ)
    rw [hnE]
    nlinarith [mul_nonneg h5 (by linarith : (0:ℝ) ≤ Γ)]
  have hs := Real.sq_sqrt hd0.le
  have hr := Real.sq_sqrt hn0.le
  have hu := Real.sq_sqrt (by linarith : (0:ℝ) ≤ Γ)
  have hs0 := Real.sqrt_pos.mpr hd0
  have hr0 := Real.sqrt_pos.mpr hn0
  have hu0 := Real.sqrt_nonneg Γ
  generalize Real.sqrt dd = s at *
  generalize Real.sqrt nn = r at *
  generalize Real.sqrt Γ = u at *
  subst hs hr hu
  have hsq : 8 / 10 ^ 3 * s ^ 5 * u ≤ k ^ 2 * r := by
    have : (8 / 10 ^ 3 * s ^ 5 * u) ^ 2 ≤ (k ^ 2 * r) ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hσ.le]

theorem gRipe_pos (dd nn σ : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) (hσ : 0 < σ)
    (hn : Real.exp 4 * dd ^ 5 ≤ nn) : 0 < gRipe dd nn σ := by
  obtain ⟨hk, -⟩ := kRipe_ge dd hd1 hd
  have hd0 : 0 < dd := by linarith
  have hΓ := gamR_ge dd nn hd0 hn
  have hn0 : 0 < nn := lt_of_lt_of_le (by positivity) hn
  unfold gRipe
  have : 0 < Real.sqrt (gamR dd nn) := Real.sqrt_pos.mpr (by linarith)
  have : 0 < Real.sqrt nn := Real.sqrt_pos.mpr hn0
  have : 0 < Real.sqrt dd := Real.sqrt_pos.mpr hd0
  have : 0 < kRipe dd := by linarith
  positivity

theorem gRipe_le (dd nn σ : ℝ) (hd1 : 1 ≤ dd) (hd : 2048 * kRipe dd ≤ dd) (hσ : 0 < σ)
    (hn : Real.exp 4 * dd ^ 5 ≤ nn) : gRipe dd nn σ ≤ σ / 81920 := by
  have h1 := R2_ripe dd nn σ hd1 hd hσ hn
  obtain ⟨hk, -⟩ := kRipe_ge dd hd1 hd
  refine h1.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- (S1): `B ≤ 0.2813` when `L = σ` and `g ≤ σ/81920`. -/
theorem chanB_ripe (σ g : ℝ) (hσ : 0 < σ) (hg0 : 0 ≤ g) (hg : g ≤ σ / 81920) : chanB σ g σ ≤ 2813 / 10000 := by
  unfold chanB
  rw [div_le_iff₀ (by positivity)]
  have h1 : 3 * σ / 2 + g ≤ (3 / 2 + 1 / 81920) * σ := by linarith
  have h2 : 0 ≤ 3 * σ / 2 + g := by positivity
  nlinarith [mul_le_mul h1 h1 h2 (by positivity)]

/-- (R1) at `k = 120 ln d + 68`. -/
theorem R1_ripe (dd B : ℝ) (hB : B ≤ 2813 / 10000) : 40 * (3 * Real.log dd + 1 + 2 * B) ≤ kRipe dd := by
  unfold kRipe
  nlinarith

theorem nStar_ripe_ge (dd Γ N : ℝ) (hd : 0 < dd) (hΓ : 4 ≤ Γ) (hN : dd / 4 * (Γ / 2) - dd / 2000 ≤ N) :
    1248 / 10000 * dd * Γ ≤ N := by
  have hineq : 1248 / 10000 * dd * Γ ≤ dd / 4 * (Γ / 2) - dd / 2000 := by
    nlinarith
  linarith

/-! ## The game proposition: `σ = 1/(8 (6 ln n)^{1/2})`, `n ≥ d^{10}`, `d ≥ 4·10⁶` -/

theorem ripeB_log (dd : ℝ) (hd : 4000000 ≤ dd) : 15 ≤ Real.log dd := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 ^ 15 ≤ 2.7182818286 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 15
  rw [h1]; norm_num at h2 ⊢; linarith

/-- `d ≥ 2048 (120 ln d + 68)` from `d ≥ 4·10⁶`. -/
theorem ripeB_dim (dd : ℝ) (hd : 4000000 ≤ dd) : 2048 * kRipe dd ≤ dd := by
  unfold kRipe
  have hd0 : 0 < dd := by linarith
  have h1 : Real.log dd = Real.log (2 ^ 22) + Real.log (dd / 4194304) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; ring
  have h3 := Real.log_le_sub_one_of_pos (show 0 < dd / 4194304 by positivity)
  have h4 : Real.log ((2:ℝ) ^ 22) = 22 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h5 := Real.log_two_lt_d9
  rw [h4] at h1
  norm_num at h5
  linarith

theorem ripeB_gam (dd nn : ℝ) (hd : 1 ≤ dd) (hn : dd ^ 10 ≤ nn) : Real.log nn / 2 ≤ gamR dd nn := by
  have hddpos : 0 < dd := by linarith
  have hddne0 : dd ≠ 0 := by linarith
  have hnnpos : 0 < nn := by
    have h : 0 < dd ^ 10 := pow_pos hddpos 10
    linarith
  have hnnne0 : nn ≠ 0 := by linarith
  unfold gamR
  have hlogdiv : Real.log (nn / dd ^ 5) = Real.log nn - Real.log (dd ^ 5) :=
    Real.log_div hnnne0 (pow_ne_zero 5 hddne0)
  rw [hlogdiv]
  have hlogpow : Real.log (dd ^ 5) = 5 * Real.log dd := by
    rw [Real.log_pow, Nat.cast_ofNat]
  rw [hlogpow]
  have hlog_le : 10 * Real.log dd ≤ Real.log nn := by
    have h_log_le : Real.log (dd ^ 10) ≤ Real.log nn :=
      Real.log_le_log (pow_pos hddpos 10) hn
    have h_log_pow : Real.log (dd ^ 10) = 10 * Real.log dd := by
      rw [Real.log_pow, Nat.cast_ofNat]
    rw [h_log_pow] at h_log_le
    exact h_log_le
  linarith

theorem ripeB_n (dd nn : ℝ) (hd : 4000000 ≤ dd) (hn : dd ^ 10 ≤ nn) : Real.exp 4 * dd ^ 5 ≤ nn := by
  have h_exp4_lt_55 : Real.exp 4 < 55 := by
    have h_exp4_eq : Real.exp 4 = (Real.exp 1) ^ 4 := by
      calc
        Real.exp 4 = Real.exp ((4 : ℕ) * 1) := by norm_num
        _ = (Real.exp 1) ^ (4 : ℕ) := by rw [Real.exp_nat_mul]
        _ = (Real.exp 1) ^ 4 := rfl
    rw [h_exp4_eq]
    have h_exp1_lt_272 : Real.exp 1 < 2.72 := by
      linarith [Real.exp_one_lt_d9]
    have h_pow_lt : (Real.exp 1) ^ 4 < (2.72 : ℝ) ^ 4 := by
      refine pow_lt_pow_left₀ h_exp1_lt_272 (by positivity) (by norm_num : 4 ≠ 0)
    have h_272_pow_lt_55 : (2.72 : ℝ) ^ 4 < 55 := by norm_num
    linarith
  have h_55_le_dd5 : 55 ≤ dd ^ 5 := by
    have h_55_le_4000000_5 : 55 ≤ (4000000 : ℝ) ^ 5 := by norm_num
    have h_nonneg : 0 ≤ (4000000 : ℝ) := by norm_num
    have h_4000000_5_le_dd5 : (4000000 : ℝ) ^ 5 ≤ dd ^ 5 :=
      pow_le_pow_left₀ h_nonneg hd 5
    exact le_trans h_55_le_4000000_5 h_4000000_5_le_dd5
  have h_exp4_le_dd5 : Real.exp 4 ≤ dd ^ 5 := le_trans (le_of_lt h_exp4_lt_55) h_55_le_dd5
  have h_nonneg_dd5 : 0 ≤ dd ^ 5 := by
    have h_nonneg_dd : 0 ≤ dd := by linarith
    exact pow_nonneg h_nonneg_dd 5
  calc
    Real.exp 4 * dd ^ 5 ≤ dd ^ 5 * dd ^ 5 := mul_le_mul_of_nonneg_right h_exp4_le_dd5 h_nonneg_dd5
    _ = dd ^ 10 := by ring
    _ ≤ nn := hn

theorem ripeB_sig (dd nn : ℝ) (hd : 4000000 ≤ dd) (hn : dd ^ 10 ≤ nn) : 0 < sigB nn ∧ sigB nn ≤ 1 / 4 := by
  have hdd_pos : 0 < dd := by linarith
  have hdd_gt_one : 1 < dd := by linarith
  have hn_gt_one : 1 < nn := by
    have hdd10_gt_one : 1 < dd ^ 10 := by
      have h := pow_lt_pow_left₀ hdd_gt_one (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 10 ≠ 0)
      simpa using h
    linarith
  have hlogpos : 0 < Real.log nn := Real.log_pos hn_gt_one
  have hlog_ge : 1 / 24 ≤ Real.log nn := by
    have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h_2_pos : (0 : ℝ) < 2 := by norm_num
    have h_dd_ge_2 : (2 : ℝ) ≤ dd := by linarith
    have hlog_dd_ge_log_2 : Real.log 2 ≤ Real.log dd :=
      Real.log_le_log h_2_pos h_dd_ge_2
    have hlog_nn_ge_10log_dd : 10 * Real.log dd ≤ Real.log nn := by
      calc
        10 * Real.log dd = Real.log (dd ^ 10) := by
          rw [Real.log_pow, Nat.cast_ofNat]
        _ ≤ Real.log nn := Real.log_le_log (by positivity) hn
    have hlog2_gt_1_24 : (1 : ℝ) / 24 < Real.log 2 := by
      have : (0.6931471803 : ℝ) > 1 / 24 := by norm_num
      linarith
    have h_lt : (1 : ℝ) / 24 < Real.log nn := by
      calc
        (1 : ℝ) / 24 < Real.log 2 := hlog2_gt_1_24
        _ ≤ Real.log dd := hlog_dd_ge_log_2
        _ = (1/10 : ℝ) * (10 * Real.log dd) := by ring
        _ ≤ (1/10 : ℝ) * Real.log nn := by gcongr
        _ ≤ Real.log nn := by
          have : 0 < Real.log nn := hlogpos
          nlinarith
    exact le_of_lt h_lt
  have h_sqrt_pos : 0 < Real.sqrt (6 * Real.log nn) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have h_pos : 0 < sigB nn := by
    unfold sigB
    refine div_pos (by norm_num) ?_
    nlinarith
  have h_le : sigB nn ≤ 1 / 4 := by
    unfold sigB
    have h_sq : (1/2 : ℝ) ≤ Real.sqrt (6 * Real.log nn) := by
      have h_sq' : ((1 : ℝ)/2)^2 ≤ 6 * Real.log nn := by
        nlinarith
      calc
        (1/2 : ℝ) = Real.sqrt (((1 : ℝ)/2)^2) := by
          rw [Real.sqrt_sq (by norm_num : 0 ≤ (1/2 : ℝ))]
        _ ≤ Real.sqrt (6 * Real.log nn) := Real.sqrt_le_sqrt h_sq'
    have h_denom_pos : 0 < 8 * Real.sqrt (6 * Real.log nn) := by nlinarith
    have h_four_pos : 0 < (4 : ℝ) := by norm_num
    apply (one_div_le_one_div h_denom_pos h_four_pos).mpr
    nlinarith
  exact And.intro h_pos h_le

/-- `2.5·10⁻⁵/(8 · 12^{1/2}) ≥ 9.02·10⁻⁷`. -/
theorem ripeB_coef (nn Γ : ℝ) (hn : 1 < nn) (hΓ : Real.log nn / 2 ≤ Γ) :
    902 / 10 ^ 9 * Real.sqrt nn ≤ 25 / 10 ^ 6 * sigB nn * Real.sqrt (nn * Γ) := by
  have hL : 0 < Real.log nn := Real.log_pos hn
  have hΓ0 : 0 < Γ := by linarith
  have hn0 : 0 < nn := by linarith
  unfold sigB
  rw [Real.sqrt_mul hn0.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
  have ha := Real.sq_sqrt hL.le
  have hb := Real.sq_sqrt hΓ0.le
  have hc := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have ha0 := Real.sqrt_pos.mpr hL
  have hb0 := Real.sqrt_pos.mpr hΓ0
  have hc0 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 6)
  have hr0 := Real.sqrt_pos.mpr hn0
  generalize Real.sqrt (Real.log nn) = a at *
  generalize Real.sqrt Γ = b at *
  generalize Real.sqrt 6 = c at *
  generalize Real.sqrt nn = r at *
  have hcle : c ≤ 24495 / 10000 := by nlinarith
  have hba : 70703 / 100000 * a ≤ b := by
    have : (70703 / 100000 * a) ^ 2 ≤ b ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) hb0.le).mp this
  rw [show 25 / 10 ^ 6 * (1 / (8 * (c * a))) * (r * b) = 25 / 10 ^ 6 * r * b / (8 * c * a) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hba hr0.le, mul_le_mul_of_nonneg_right hcle (mul_nonneg hr0.le ha0.le)]

theorem rpow_three_halves (dd : ℝ) (hd : 0 ≤ dd) : dd ^ (3 / 2 : ℝ) = dd * Real.sqrt dd := by
  have hsum_ne_zero : (1 : ℝ) + (1/2 : ℝ) ≠ 0 := by norm_num
  calc
    dd ^ (3 / 2 : ℝ) = dd ^ ((1 : ℝ) + (1/2 : ℝ)) := by norm_num
    _ = dd ^ (1 : ℝ) * dd ^ (1/2 : ℝ) := by rw [Real.rpow_add' hd hsum_ne_zero]
    _ = dd * dd ^ (1/2 : ℝ) := by rw [Real.rpow_one dd]
    _ = dd * Real.sqrt dd := by rw [Real.sqrt_eq_rpow]

/-- The parameters of the game proposition satisfy the hypotheses of the strategy and of the lemmas of the other
modules:
`σ ∈ (0, 1/4]`, `0 < g ≤ σ/81920`, `3σ/2 + g ≤ 1/2` (the legality lemma), `k ≥ 240`, `d ≥ 2048 k` (Lemmas REGULAR, REST,
LEAK), `X ≥ 16` at the floor (the count lemma, (C1) to (C3)), `B ≤ 0.2813` and (R1), `n ≥ e⁴ d⁵`. -/
theorem ripeB_params {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) :
    0 < sigB n ∧ sigB n ≤ 1 / 4 ∧ 0 < gRipe d n (sigB n) ∧ gRipe d n (sigB n) ≤ sigB n / 81920 ∧
      3 * sigB n / 2 + gRipe d n (sigB n) ≤ 1 / 2 ∧ 240 ≤ kRipe d ∧ 2048 * kRipe d ≤ d ∧
      16 ≤ xCount d (wStar d (kRipe d) (sigB n) (gRipe d n (sigB n))) ∧
      chanB (sigB n) (gRipe d n (sigB n)) (sigB n) ≤ 2813 / 10000 ∧
      40 * (3 * Real.log d + 1 + 2 * chanB (sigB n) (gRipe d n (sigB n)) (sigB n)) ≤ kRipe d ∧
      Real.exp 4 * (d : ℝ) ^ 5 ≤ n := by
  have hdR : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (d : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
  obtain ⟨hs0, hs4⟩ := ripeB_sig d n hdR hnR
  have hdim := ripeB_dim d hdR
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hn4 := ripeB_n d n hdR hnR
  have hg := gRipe_pos d n (sigB n) hd1 hdim hs0 hn4
  have hgle := gRipe_le d n (sigB n) hd1 hdim hs0 hn4
  obtain ⟨hk240, -⟩ := kRipe_ge d hd1 hdim
  have hB := chanB_ripe (sigB n) _ hs0 hg.le hgle
  refine ⟨hs0, hs4, hg, hgle, by linarith, hk240, hdim, ?_, hB, R1_ripe _ _ hB, hn4⟩
  exact xCount_wStar_ge d (kRipe d) (sigB n) _ (by linarith) (by linarith) hs0 hg
    (R2_ripe d n _ hd1 hdim hs0 hn4)

end AdversarialBco.Lower
