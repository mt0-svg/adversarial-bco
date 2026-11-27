/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementUnifiedLower
public import AdversarialBco.Conj1Lower.Sanity
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# Clause (c) of `TheoremLowerU`: Lemma SMALL

Lemma SMALL (the paper's section on every dimension), in the class `StratsLowU` (the losses `1/2 + ε_t s/4`). For
every `d, n ≥ 1`, every body of `BodyU` and
every learner, random-sign linear losses along one direction give a strategy with mean regret at least
`√n/(4√3)` and one with regret at least `√n/(8√3)` with probability at least `1/48`.

* The direction (`exists_sdir`): `s(y) = (2⟨y, e_1⟩ - α - β)/(β - α)` with `[α, β]` the projection of `K` on `e_1`,
  affine, in `[-1, 1]` on `K` and attaining `±1` there, `1/r0`-Lipschitz since `β - α ≥ 2 r0` (`SDir`).
* The strategy of the signs `ε ∈ {0, 1}^n` (`stratSign`): the loss `1/2 + ε_t s/4` in round `t`; it is in
  `StratsLowU K n r0` (`stratSign_mem`), and the regret is at least `(|S_n| + M_n)/4` with `S_n = Σ_t ε_t` and
  `M_n = Σ_t ε_t s(x_t)` (`regretAd_sign_ge`).
* The averages over the cube, for one seed: `E M_n = 0`, `E M_n² ≤ n` (`sum_mSum`, `sum_mSum_sq`; `x_t` reads the signs
  before `t`, and the flip of one coordinate pairs the cube), `E S_n² = n`, `E S_n⁴ ≤ 3 n²` (`sum_sSum_sq`,
  `sum_sSum_four`), hence `E |S_n| ≥ (n/3)^{1/2}` from `3 v² x² - x⁴ ≤ 2 v³ |x|` at `v² = 3 n` (`sum_abs_sSum`), and a
  Paley-Zygmund count (`card_gt_of_moments`): at least `2^n/48` signs give `(|S_n| + M_n)/4 > √n/(8√3)`.
* The signs are averaged seed by seed, on the finite cube; the derandomisation picks one sign vector for the mean and
  one for the probability (`lowerU_small_mean`, `lowerU_small_prob`).
-/

open MeasureTheory Metric Finset
open scoped RealInnerProductSpace

namespace AdversarialBco.UnifiedLower.Small

open RealRAM AdversarialBco.Lower AdversarialBco.Lower.Sanity

/-! ## Signs on the cube -/

section Cube

variable {n : ℕ}

/-- The sign `±1` of a coin. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> norm_num [sgn]

theorem abs_sgn_le (b : Bool) : |sgn b| ≤ 1 := by cases b <;> norm_num [sgn]

/-- The flip of the coordinate `u`. -/
def flipC (u : Fin n) (ε : Fin n → Bool) : Fin n → Bool := Function.update ε u (!ε u)

theorem flipC_self (u : Fin n) (ε : Fin n → Bool) : flipC u ε u = !ε u := by simp [flipC]

theorem flipC_ne {u i : Fin n} (h : i ≠ u) (ε : Fin n → Bool) : flipC u ε i = ε i := by
  simp [flipC, Function.update_of_ne h]

theorem flipC_involutive (u : Fin n) : Function.Involutive (flipC u) := by
  intro ε
  funext i
  by_cases h : i = u
  · subst h
    simp [flipC]
  · rw [flipC_ne h, flipC_ne h]

/-- `F` reads the coordinates below `t` only. -/
def DepBelow {α : Type*} (t : ℕ) (F : (Fin n → Bool) → α) : Prop :=
  ∀ ε ε' : Fin n → Bool, (∀ i : Fin n, (i : ℕ) < t → ε i = ε' i) → F ε = F ε'

theorem DepBelow.flipC_eq {α : Type*} {t : ℕ} {F : (Fin n → Bool) → α} (hF : DepBelow t F) (u : Fin n)
    (hu : t ≤ u) (ε : Fin n → Bool) : F (flipC u ε) = F ε :=
  hF _ _ fun i hi => flipC_ne (fun h => by rw [h] at hi; omega) ε

/-- The sign of a coordinate against a function that does not read it sums to `0` over the cube. -/
theorem sum_sgn_mul (u : Fin n) (F : (Fin n → Bool) → ℝ) (hF : ∀ ε, F (flipC u ε) = F ε) :
    ∑ ε, sgn (ε u) * F ε = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm _ (flipC_involutive u)) (fun ε => sgn (ε u) * F ε)
  have h2 : ∀ ε, sgn ((Function.Involutive.toPerm _ (flipC_involutive u)) ε u) *
      F ((Function.Involutive.toPerm _ (flipC_involutive u)) ε) = -(sgn (ε u) * F ε) := by
    intro ε
    rw [Function.Involutive.coe_toPerm, flipC_self, hF]
    cases ε u <;> simp [sgn]
  simp only [h2, Finset.sum_neg_distrib] at h
  linarith

/-- The sign of round `t`, `0` from round `n` on. -/
noncomputable def sg (ε : Fin n → Bool) (t : ℕ) : ℝ := if h : t < n then sgn (ε ⟨t, h⟩) else 0

theorem sg_sq {t : ℕ} (ht : t < n) (ε : Fin n → Bool) : sg ε t ^ 2 = 1 := by
  rw [sg, dite_eq_left ht, sgn_sq]

theorem abs_sg_le (ε : Fin n → Bool) (t : ℕ) : |sg ε t| ≤ 1 := by
  unfold sg
  split_ifs
  · exact abs_sgn_le _
  · simp

theorem sg_congr {t : ℕ} {ε ε' : Fin n → Bool} (h : ∀ i : Fin n, (i : ℕ) < t + 1 → ε i = ε' i) :
    sg ε t = sg ε' t := by
  unfold sg
  split_ifs with ht
  · rw [h ⟨t, ht⟩ (by simp)]
  · rfl

theorem sum_sg_mul {t : ℕ} (ht : t < n) (F : (Fin n → Bool) → ℝ) (hF : DepBelow t F) :
    ∑ ε, sg ε t * F ε = 0 := by
  simp only [sg, ht, ↓reduceDIte]
  exact sum_sgn_mul ⟨t, ht⟩ F (hF.flipC_eq ⟨t, ht⟩ le_rfl)

/-- The partial sum `Σ_{u < t} ε_u X_u`. -/
noncomputable def mSum (X : ℕ → (Fin n → Bool) → ℝ) (t : ℕ) (ε : Fin n → Bool) : ℝ :=
  ∑ u ∈ range t, sg ε u * X u ε

theorem mSum_succ (X : ℕ → (Fin n → Bool) → ℝ) (t : ℕ) (ε : Fin n → Bool) :
    mSum X (t + 1) ε = mSum X t ε + sg ε t * X t ε := by
  simp only [mSum, Finset.sum_range_succ]

theorem mSum_dep (X : ℕ → (Fin n → Bool) → ℝ) (hX : ∀ u, DepBelow u (X u)) (t : ℕ) :
    DepBelow t (mSum X t) := by
  intro ε ε' h
  unfold mSum
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := Finset.mem_range.1 hu
  rw [sg_congr (fun i hi => h i (by omega)), hX u ε ε' (fun i hi => h i (by omega))]

theorem sum_cube_one : ∑ _ε : (Fin n → Bool), (1 : ℝ) = 2 ^ n := by simp

theorem sum_mSum (X : ℕ → (Fin n → Bool) → ℝ) (hX : ∀ u, DepBelow u (X u)) {t : ℕ} (ht : t ≤ n) :
    ∑ ε, mSum X t ε = 0 := by
  unfold mSum
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun u hu => sum_sg_mul (by have := Finset.mem_range.1 hu; omega) _ (hX u)

theorem sum_mSum_sq (X : ℕ → (Fin n → Bool) → ℝ) (hX : ∀ u, DepBelow u (X u))
    (hX1 : ∀ u < n, ∀ ε, X u ε ^ 2 ≤ 1) : ∀ t ≤ n, ∑ ε, mSum X t ε ^ 2 ≤ t * 2 ^ n
  | 0, _ => by simp [mSum]
  | t + 1, ht => by
    have ih := sum_mSum_sq X hX hX1 t (by omega)
    have hexp : ∀ ε, mSum X (t + 1) ε ^ 2 =
        mSum X t ε ^ 2 + sg ε t * (2 * mSum X t ε * X t ε) + X t ε ^ 2 := by
      intro ε
      rw [mSum_succ]
      have := sg_sq (by omega : t < n) ε
      linear_combination X t ε ^ 2 * this
    simp only [hexp, Finset.sum_add_distrib]
    rw [sum_sg_mul (by omega) _ (fun ε ε' h => by rw [mSum_dep X hX t ε ε' h, hX t ε ε' h])]
    have h2 : ∑ ε : (Fin n → Bool), X t ε ^ 2 ≤ 2 ^ n :=
      (Finset.sum_le_sum fun ε _ => hX1 t (by omega) ε).trans sum_cube_one.le
    push_cast
    linarith

/-- The sum of the signs `S_t = Σ_{u < t} ε_u`. -/
noncomputable def sSum (t : ℕ) (ε : Fin n → Bool) : ℝ := mSum (fun _ _ => 1) t ε

theorem sSum_dep (t : ℕ) : DepBelow t (sSum (n := n) t) :=
  mSum_dep _ (fun _ _ _ _ => rfl) t

theorem sum_sSum_sq : ∀ t ≤ n, ∑ ε : (Fin n → Bool), sSum t ε ^ 2 = t * 2 ^ n
  | 0, _ => by simp [sSum, mSum]
  | t + 1, ht => by
    have ih := sum_sSum_sq t (by omega)
    have hexp : ∀ ε : Fin n → Bool, sSum (t + 1) ε ^ 2 = sSum t ε ^ 2 + sg ε t * (2 * sSum t ε) + 1 := by
      intro ε
      rw [sSum, mSum_succ, ← sSum]
      have := sg_sq (by omega : t < n) ε
      linear_combination this
    simp only [hexp, Finset.sum_add_distrib]
    rw [sum_sg_mul (by omega) _ (fun ε ε' h => by rw [sSum_dep t ε ε' h]), ih, sum_cube_one]
    push_cast
    ring

theorem sum_sSum_four : ∀ t ≤ n, ∑ ε : (Fin n → Bool), sSum t ε ^ 4 ≤ 3 * t ^ 2 * 2 ^ n
  | 0, _ => by simp [sSum, mSum]
  | t + 1, ht => by
    have ih := sum_sSum_four t (by omega)
    have h2 := sum_sSum_sq (n := n) t (by omega)
    have hexp : ∀ ε : Fin n → Bool, sSum (t + 1) ε ^ 4 =
        sSum t ε ^ 4 + 6 * sSum t ε ^ 2 + 1 + sg ε t * (4 * sSum t ε ^ 3 + 4 * sSum t ε) := by
      intro ε
      rw [sSum, mSum_succ, ← sSum]
      have := sg_sq (by omega : t < n) ε
      linear_combination (6 * sSum t ε ^ 2 + 4 * sSum t ε * sg ε t + sg ε t ^ 2 + 1) * this
    simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sg_mul (by omega) _ (fun ε ε' h => by rw [sSum_dep t ε ε' h]), h2, sum_cube_one]
    push_cast
    have : (0 : ℝ) ≤ 2 ^ n := by positivity
    nlinarith

theorem quartic_abs (x v : ℝ) (hv : 0 < v) : 3 * v ^ 2 * x ^ 2 - x ^ 4 ≤ 2 * v ^ 3 * |x| := by
  have ha := abs_nonneg x
  have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h4 : x ^ 4 = |x| ^ 4 := by
    rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, h2]
    ring
  rw [h2, h4]
  nlinarith [mul_nonneg (mul_nonneg ha (sq_nonneg (|x| - v))) (by linarith : 0 ≤ |x| + 2 * v)]

/-- `E |S_n| ≥ (n/3)^{1/2}`: from `E S_n² = n`, `E S_n⁴ ≤ 3 n²` and `3 v² x² - x⁴ ≤ 2 v³ |x|` at `v² = 3 n`. -/
theorem sum_abs_sSum (hn : 1 ≤ n) : 2 ^ n * (Real.sqrt n / Real.sqrt 3) ≤ ∑ ε : (Fin n → Bool), |sSum n ε| := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  set v := Real.sqrt 3 * Real.sqrt n with hv
  have hv0 : 0 < v := mul_pos hs3 hsn
  have hv2 : v ^ 2 = 3 * n := by
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hnr.le]
  have hsum : ∑ ε : (Fin n → Bool), (3 * v ^ 2 * sSum n ε ^ 2 - sSum n ε ^ 4) ≤
      ∑ ε : (Fin n → Bool), 2 * v ^ 3 * |sSum n ε| := Finset.sum_le_sum fun ε _ => quartic_abs _ v hv0
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_sSum_sq n le_rfl] at hsum
  have h4 := sum_sSum_four (n := n) n le_rfl
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hv3 : v ^ 3 = 3 * n * v := by rw [pow_succ, hv2]
  rw [hv3, hv2] at hsum
  -- `6 n v Σ |S| ≥ 6 n² 2^n`, so `Σ |S| ≥ n 2^n / v = 2^n √n/√3`
  have key : (n : ℝ) * 2 ^ n ≤ v * ∑ ε : (Fin n → Bool), |sSum n ε| := by
    have : 6 * n * (n * 2 ^ n) ≤ 6 * n * (v * ∑ ε : (Fin n → Bool), |sSum n ε|) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hnv : (n : ℝ) / v = Real.sqrt n / Real.sqrt 3 := by
    rw [hv, div_eq_div_iff hv0.ne' hs3.ne']
    nth_rewrite 1 [← Real.mul_self_sqrt hnr.le]
    ring
  rw [← hnv, mul_div_assoc', div_le_iff₀ hv0]
  linarith

/-- A Paley-Zygmund count on a finite set: if the mean of `Z` is at least `m ≥ 0` and the mean of `Z²` at most `V`,
at least a fraction `m²/(4V)` of the points have `Z > m/2`. -/
theorem card_gt_of_moments {ι : Type*} [Fintype ι] (Z : ι → ℝ) {m V : ℝ} (hm : 0 ≤ m) (hV : 0 < V)
    (h1 : Fintype.card ι * m ≤ ∑ i, Z i) (h2 : ∑ i, Z i ^ 2 ≤ Fintype.card ι * V) :
    Fintype.card ι * m ^ 2 ≤ 4 * V * (univ.filter fun i => m / 2 < Z i).card := by
  classical
  set T := univ.filter fun i => m / 2 < Z i with hT
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun i => m / 2 < Z i) Z
  have hc : ∑ i ∈ univ.filter (fun i => ¬ m / 2 < Z i), Z i ≤ N * (m / 2) := by
    calc ∑ i ∈ univ.filter (fun i => ¬ m / 2 < Z i), Z i ≤ ∑ i ∈ univ.filter (fun i => ¬ m / 2 < Z i), m / 2 :=
          Finset.sum_le_sum fun i hi => not_lt.1 (Finset.mem_filter.1 hi).2
      _ = (univ.filter (fun i => ¬ m / 2 < Z i)).card * (m / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (m / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [hN]
          exact_mod_cast Finset.card_le_univ _
  have hTZ : N * (m / 2) ≤ ∑ i ∈ T, Z i := by linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := Z)
  have hsub : ∑ i ∈ T, Z i ^ 2 ≤ ∑ i, Z i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => sq_nonneg _
  have hsq : (N * (m / 2)) ^ 2 ≤ (∑ i ∈ T, Z i) ^ 2 := pow_le_pow_left₀ (by positivity) hTZ 2
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hfin : N * N * m ^ 2 ≤ N * (4 * V * T.card) := by
    have := hsq.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsub.trans h2) hTc))
    nlinarith
  rcases eq_or_lt_of_le hN0 with h0 | hpos
  · rw [← h0]
    simp only [zero_mul]
    positivity
  · exact le_of_mul_le_mul_left (by linarith) hpos

end Cube

/-! ## The direction and the strategy of the signs -/

section Game

variable {d : ℕ}

/-- A direction for Lemma SMALL on `K` at the inner radius `r0`: affine, continuous, with values in `[-1, 1]` on `K`
attaining `1` and `-1` there, and `1/r0`-Lipschitz on `E d`. -/
structure SDir (K : Set (E d)) (r0 : ℝ) (s : E d → ℝ) : Prop where
  bound : ∀ y ∈ K, |s y| ≤ 1
  top : ∃ p ∈ K, s p = 1
  bot : ∃ p ∈ K, s p = -1
  lip : ∀ y z, |s y - s z| ≤ dist y z / r0
  aff : ∀ (y z : E d) (a b : ℝ), a + b = 1 → s (a • y + b • z) = a * s y + b * s z
  cont : Continuous s

/-- The direction of the first coordinate, normalised by the projection `[α, β]` of `K`. -/
theorem exists_sdir (hd : 1 ≤ d) {K : Set (E d)} {a : E d} {r0 R0 : ℝ} (hb : BodyU K a r0 R0) :
    ∃ s : E d → ℝ, SDir K r0 s := by
  obtain ⟨hr0, -, hKc, -, hK1, -⟩ := hb
  set e : E d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  set lf : E d → ℝ := fun y => ⟪y, e⟫ with hlf
  have hlfc : Continuous lf := continuous_id.inner continuous_const
  have haK : a ∈ K := hK1 (mem_closedBall_self hr0.le)
  obtain ⟨pm, hpm, hmin⟩ := hKc.exists_isMinOn ⟨a, haK⟩ hlfc.continuousOn
  obtain ⟨pp, hpp, hmax⟩ := hKc.exists_isMaxOn ⟨a, haK⟩ hlfc.continuousOn
  set α := lf pm with hα
  set β := lf pp with hβ
  have hplus : a + r0 • e ∈ K := hK1 (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr0, he, mul_one])
  have hminus : a - r0 • e ∈ K := hK1 (by rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr0, he, mul_one])
  have hlfp : lf (a + r0 • e) = lf a + r0 := by
    simp only [hlf, inner_add_left, real_inner_smul_left, hee, mul_one]
  have hlfm : lf (a - r0 • e) = lf a - r0 := by
    simp only [hlf, inner_sub_left, real_inner_smul_left, hee, mul_one]
  have hβ1 : lf a + r0 ≤ β := hlfp ▸ hmax hplus
  have hα1 : α ≤ lf a - r0 := hlfm ▸ hmin hminus
  have hw : 2 * r0 ≤ β - α := by linarith
  have hw0 : 0 < β - α := by linarith
  refine ⟨fun y => (2 * lf y - α - β) / (β - α), ⟨?_, ⟨pp, hpp, ?_⟩, ⟨pm, hpm, ?_⟩, ?_, ?_, ?_⟩⟩
  · intro y hy
    have h1 : α ≤ lf y := hmin hy
    have h2 : lf y ≤ β := hmax hy
    rw [abs_div, abs_of_pos hw0, div_le_one hw0, abs_le]
    constructor <;> linarith
  · show (2 * β - α - β) / (β - α) = 1
    rw [div_eq_one_iff_eq hw0.ne']
    ring
  · show (2 * α - α - β) / (β - α) = -1
    rw [div_eq_iff hw0.ne']
    ring
  · intro y z
    have hyz : |lf y - lf z| ≤ dist y z := by
      rw [show lf y - lf z = ⟪y - z, e⟫ by simp only [hlf, inner_sub_left], dist_eq_norm]
      exact (abs_real_inner_le_norm _ _).trans (by rw [he, mul_one])
    rw [show (2 * lf y - α - β) / (β - α) - (2 * lf z - α - β) / (β - α) = 2 * (lf y - lf z) / (β - α) by ring,
      abs_div, abs_mul, abs_of_pos hw0, abs_two, div_le_div_iff₀ hw0 hr0]
    have hd0 : 0 ≤ dist y z := dist_nonneg
    nlinarith
  · intro y z a' b' hab
    have hl : lf (a' • y + b' • z) = a' * lf y + b' * lf z := by
      simp only [hlf, inner_add_left, real_inner_smul_left]
    show (2 * lf (a' • y + b' • z) - α - β) / (β - α) =
      a' * ((2 * lf y - α - β) / (β - α)) + b' * ((2 * lf z - α - β) / (β - α))
    rw [hl, mul_div_assoc', mul_div_assoc', ← add_div]
    congr 1
    linear_combination (α + β) * hab
  · exact ((continuous_const.mul hlfc).sub continuous_const |>.sub continuous_const).div_const _

/-- The strategy of the signs `ε`: the loss `1/2 + ε_t s/4` in round `t` (`1/2` from round `n` on). -/
noncomputable def stratSign {n : ℕ} (s : E d → ℝ) (ε : Fin n → Bool) : Strategy d :=
  fun t _ _ y => 1 / 2 + sg ε t * s y / 4

theorem stratSign_bounds {n : ℕ} {K : Set (E d)} {r0 : ℝ} {s : E d → ℝ} (hs : SDir K r0 s) (ε : Fin n → Bool)
    (t : ℕ) {y : E d} (hy : y ∈ K) : 1 / 4 ≤ 1 / 2 + sg ε t * s y / 4 ∧ 1 / 2 + sg ε t * s y / 4 ≤ 3 / 4 := by
  have h : |sg ε t * s y| ≤ 1 := by
    rw [abs_mul]
    calc |sg ε t| * |s y| ≤ 1 * 1 := mul_le_mul (abs_sg_le ε t) (hs.bound y hy) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> linarith

/-- The strategy of the signs is a strategy of the lower bound. -/
theorem stratSign_mem {n : ℕ} {K : Set (E d)} (hK : Convex ℝ K) {r0 : ℝ} (hr0 : 0 < r0) {s : E d → ℝ}
    (hs : SDir K r0 s) (ε : Fin n → Bool) : stratSign s ε ∈ StratsLowU K n r0 := by
  refine ⟨fun t _ => ⟨fun x o => ⟨⟨hK, fun y _ z _ a b _ _ hab => le_of_eq ?_⟩, fun y hy => ?_⟩,
    fun y _ => measurable_const⟩, fun t _ x o o' => ⟨rfl, fun y hy => ?_, fun y z => ?_⟩⟩
  · simp only [stratSign, smul_eq_mul]
    rw [hs.aff y z a b hab]
    linear_combination (-1 / 2 : ℝ) * hab
  · obtain ⟨h1, h2⟩ := stratSign_bounds hs ε t hy
    exact ⟨by simp only [stratSign]; linarith, by simp only [stratSign]; linarith⟩
  · obtain ⟨h1, h2⟩ := stratSign_bounds hs ε t hy
    exact ⟨by simp only [stratSign]; linarith, by simp only [stratSign]; linarith⟩
  · simp only [stratSign]
    rw [show 1 / 2 + sg ε t * s y / 4 - (1 / 2 + sg ε t * s z / 4) = sg ε t * (s y - s z) / 4 by ring,
      abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have h1 := abs_sg_le ε t
    have h2 := hs.lip y z
    have h3 : |s y - s z| * |sg ε t| ≤ dist y z / r0 * 1 :=
      mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    rw [div_mul_eq_mul_div, mul_one, le_div_iff₀ hr0] at h3
    nlinarith [abs_nonneg (sg ε t), abs_nonneg (s y - s z)]

/-- The regret against the strategy of the signs, written out: the losses are `1/2 + ε_t s/4` whatever the run. -/
theorem regretAd_sign {n : ℕ} (K : Set (E d)) (s : E d → ℝ) (ε : Fin n → Bool) (p : Policy d) :
    regretAd K (stratSign s ε) p n =
      ∑ t ∈ range n, (1 / 2 + sg ε t * s (plays (stratSign s ε) (fun _ => 0) p t) / 4) -
        sInf ((fun y => ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4)) '' K) := rfl

/-- The points of the rounds `u` read the signs before `u` only. -/
theorem plays_sign_dep {n : ℕ} (s : E d → ℝ) (p : Policy d) (u : ℕ) :
    DepBelow u fun ε : Fin n → Bool => plays (stratSign s ε) (fun _ => 0) p u := by
  intro ε ε' h
  refine plays_congr (fun _ => 0) p u fun v hv => ?_
  funext x o y
  simp only [stratSign]
  rw [sg_congr fun i hi => h i (by omega)]

/-- The regret against the strategy of the signs is at least `(|S_n| + M_n)/4`. -/
theorem regretAd_sign_ge {n : ℕ} {K : Set (E d)} {r0 : ℝ} {s : E d → ℝ} (hs : SDir K r0 s) (ε : Fin n → Bool)
    (p : Policy d) :
    (|sSum n ε| + mSum (fun u ε => s (plays (stratSign s ε) (fun _ => 0) p u)) n ε) / 4 ≤
      regretAd K (stratSign s ε) p n := by
  rw [regretAd_sign]
  have hval : ∀ y, ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4) = n / 2 + sSum n ε * s y / 4 := by
    intro y
    simp only [sSum, mSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Finset.sum_mul, Finset.sum_div]
    ring
  have hplay : ∑ t ∈ range n, (1 / 2 + sg ε t * s (plays (stratSign s ε) (fun _ => 0) p t) / 4) =
      n / 2 + mSum (fun u ε => s (plays (stratSign s ε) (fun _ => 0) p u)) n ε / 4 := by
    simp only [mSum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_div]
    ring
  have hbdd : BddBelow ((fun y => ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4)) '' K) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun t _ => by linarith [(stratSign_bounds hs ε t hy).1]
  have hinf : sInf ((fun y => ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4)) '' K) ≤ n / 2 - |sSum n ε| / 4 := by
    rcases le_or_gt 0 (sSum n ε) with h0 | h0
    · obtain ⟨pm, hpm, hspm⟩ := hs.bot
      refine (csInf_le hbdd ⟨pm, hpm, rfl⟩).trans (le_of_eq ?_)
      show ∑ t ∈ range n, (1 / 2 + sg ε t * s pm / 4) = _
      rw [hval pm, hspm, abs_of_nonneg h0]
      ring
    · obtain ⟨pp, hpp, hspp⟩ := hs.top
      refine (csInf_le hbdd ⟨pp, hpp, rfl⟩).trans (le_of_eq ?_)
      show ∑ t ∈ range n, (1 / 2 + sg ε t * s pp / 4) = _
      rw [hval pp, hspp, abs_of_neg h0]
      ring
  rw [hplay]
  linarith

end Game

/-! ## The transcript of an oblivious continuous strategy -/

theorem measurable_transcript_obl {d n : ℕ} {Ω : Type} [MeasurableSpace Ω] {σ : Strategy d}
    (f : ℕ → E d → ℝ) (hσ : ∀ t x o, σ t x o = f t) (hf : ∀ t, Measurable (f t)) {pol : Learner Ω d}
    (hpol : ∀ t < n, Measurable fun p : Ω × (Fin t → E d) × (Fin t → ℝ) => pol t p.1 p.2.1 p.2.2) :
    ∀ t ≤ n, Measurable fun ω => transcript σ (fun _ => 0) (fun t => pol t ω) t
  | 0, _ => measurable_const
  | t + 1, ht => by
    have ih := measurable_transcript_obl f hσ hf hpol t (by omega)
    have hy : Measurable fun ω => pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
        (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 :=
      (hpol t (by omega)).comp (measurable_id.prodMk (ih.fst.prodMk ih.snd))
    simp only [transcript, hσ]
    exact (measurable_snoc ih.fst hy).prodMk (measurable_snoc ih.snd (((hf t).comp hy).add measurable_const))

/-! ## Clause (c) -/

section Clause

variable {d n : ℕ} {K : Set (E d)} {r0 : ℝ} {s : E d → ℝ} {Ω : Type} [MeasurableSpace Ω]

/-- The per-seed averages over the signs: the regret has sum at least `2^n √n/(4√3)`, and at least `2^n/48` signs give
a regret at least `√n/(8√3)`. -/
theorem seed_facts (hn : 1 ≤ n) (hs : SDir K r0 s) (p : Policy d) (hp : ∀ t < n, ∀ x o, p t x o ∈ K) :
    2 ^ n * (Real.sqrt n / (4 * Real.sqrt 3)) ≤ ∑ ε : (Fin n → Bool), regretAd K (stratSign s ε) p n ∧
      (2 ^ n : ℝ) ≤ 48 * (univ.filter fun ε : Fin n → Bool =>
        Real.sqrt n / (8 * Real.sqrt 3) ≤ regretAd K (stratSign s ε) p n).card := by
  classical
  set X : ℕ → (Fin n → Bool) → ℝ := fun u ε => s (plays (stratSign s ε) (fun _ => 0) p u) with hX
  have hXd : ∀ u, DepBelow u (X u) := fun u ε ε' h => congrArg s (plays_sign_dep s p u ε ε' h)
  have hX1 : ∀ u < n, ∀ ε, X u ε ^ 2 ≤ 1 := fun u hu ε => by
    have := hs.bound _ (plays_mem (stratSign s ε) (fun _ => 0) p hp hu)
    rw [sq_le_one_iff_abs_le_one]
    exact this
  set Z : (Fin n → Bool) → ℝ := fun ε => (|sSum n ε| + mSum X n ε) / 4 with hZ
  have hZR : ∀ ε, Z ε ≤ regretAd K (stratSign s ε) p n := fun ε => regretAd_sign_ge hs ε p
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  set m0 := Real.sqrt n / (4 * Real.sqrt 3) with hm0
  have hm00 : 0 ≤ m0 := by positivity
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  -- the mean of `Z`
  have hZsum : 2 ^ n * m0 ≤ ∑ ε, Z ε := by
    have h1 := sum_abs_sSum (n := n) hn
    have h2 := sum_mSum X hXd (le_refl n)
    simp only [hZ, ← Finset.sum_div, Finset.sum_add_distrib, h2, add_zero]
    rw [hm0, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    calc 2 ^ n * (Real.sqrt n / (4 * Real.sqrt 3)) * 4 = 2 ^ n * (Real.sqrt n / Real.sqrt 3) := by
          field_simp
      _ ≤ _ := h1
  -- the second moment of `Z`
  have hZsq : ∑ ε, Z ε ^ 2 ≤ 2 ^ n * (n / 4) := by
    have h1 := sum_sSum_sq (n := n) n le_rfl
    have h2 := sum_mSum_sq X hXd hX1 n le_rfl
    have hpt : ∀ ε, Z ε ^ 2 ≤ (sSum n ε ^ 2 + mSum X n ε ^ 2) / 8 := fun ε => by
      simp only [hZ]
      nlinarith [sq_nonneg (|sSum n ε| - mSum X n ε), sq_abs (sSum n ε)]
    calc ∑ ε, Z ε ^ 2 ≤ ∑ ε, (sSum n ε ^ 2 + mSum X n ε ^ 2) / 8 := Finset.sum_le_sum fun ε _ => hpt ε
      _ = ((∑ ε, sSum n ε ^ 2) + ∑ ε, mSum X n ε ^ 2) / 8 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ (n * 2 ^ n + n * 2 ^ n) / 8 := by rw [h1]; linarith
      _ = 2 ^ n * (n / 4) := by ring
  refine ⟨hZsum.trans (Finset.sum_le_sum fun ε _ => hZR ε), ?_⟩
  -- Paley-Zygmund on the cube
  have hPZ := card_gt_of_moments Z hm00 (by positivity : (0 : ℝ) < n / 4) (by rw [hcard]; exact hZsum)
    (by rw [hcard]; exact hZsq)
  rw [hcard] at hPZ
  have hm2 : m0 ^ 2 = n / 48 := by
    rw [hm0, div_pow, mul_pow, Real.sq_sqrt hnr.le, Real.sq_sqrt (by norm_num)]
    ring
  rw [hm2] at hPZ
  have hsubset : (univ.filter fun ε : Fin n → Bool => m0 / 2 < Z ε) ⊆
      univ.filter fun ε : Fin n → Bool => Real.sqrt n / (8 * Real.sqrt 3) ≤ regretAd K (stratSign s ε) p n := by
    intro ε hε
    rw [Finset.mem_filter] at hε ⊢
    refine ⟨hε.1, le_trans (le_of_eq ?_) (hε.2.le.trans (hZR ε))⟩
    rw [hm0]
    field_simp
    ring
  have hc : ((univ.filter fun ε : Fin n → Bool => m0 / 2 < Z ε).card : ℝ) ≤
      (univ.filter fun ε : Fin n → Bool => Real.sqrt n / (8 * Real.sqrt 3) ≤
        regretAd K (stratSign s ε) p n).card := by exact_mod_cast Finset.card_le_card hsubset
  have : (2 : ℝ) ^ n * (n / 48) ≤ n * (univ.filter fun ε : Fin n → Bool => m0 / 2 < Z ε).card := by
    linarith
  have h48 : (2 : ℝ) ^ n ≤ 48 * (univ.filter fun ε : Fin n → Bool => m0 / 2 < Z ε).card := by
    have h' : n * ((2 : ℝ) ^ n) ≤ n * (48 * (univ.filter fun ε : Fin n → Bool => m0 / 2 < Z ε).card) := by
      nlinarith
    exact le_of_mul_le_mul_left h' hnr
  linarith

/-- The regret against the strategy of the signs is measurable in the seed and bounded. -/
theorem regret_sign_meas (hs : SDir K r0 s) (ε : Fin n → Bool) {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    Measurable (fun ω => regretAd K (stratSign s ε) (fun t => pol t ω) n) ∧
      ∀ ω, |regretAd K (stratSign s ε) (fun t => pol t ω) n +
        sInf ((fun y => ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4)) '' K)| ≤ n := by
  have htr := measurable_transcript_obl (σ := stratSign s ε) (fun t y => 1 / 2 + sg ε t * s y / 4)
    (fun _ _ _ => rfl) (fun t => (measurable_const.add ((measurable_const.mul hs.cont.measurable).div_const _)))
    (pol := pol) fun t ht => (hpol t ht).1
  have hpl : ∀ t < n, Measurable fun ω => plays (stratSign s ε) (fun _ => 0) (fun t => pol t ω) t := fun t ht =>
    (hpol t ht).1.comp (measurable_id.prodMk ((htr t ht.le).fst.prodMk (htr t ht.le).snd))
  refine ⟨?_, fun ω => ?_⟩
  · simp only [regretAd_sign]
    refine (Finset.measurable_sum _ fun t ht => ?_).sub measurable_const
    exact measurable_const.add ((measurable_const.mul (hs.cont.measurable.comp (hpl t
      (Finset.mem_range.1 ht)))).div_const _)
  · rw [regretAd_sign, sub_add_cancel]
    have hb : ∀ t ∈ range n, |1 / 2 + sg ε t * s (plays (stratSign s ε) (fun _ => 0) (fun t => pol t ω) t) / 4| ≤
        1 := fun t ht => by
      obtain ⟨h1, h2⟩ := stratSign_bounds hs ε t
        (plays_mem (stratSign s ε) (fun _ => 0) (fun t => pol t ω) (fun t ht => (hpol t ht).2 ω)
          (Finset.mem_range.1 ht))
      rw [abs_le]
      constructor <;> linarith
    calc _ ≤ ∑ t ∈ range n, |1 / 2 + sg ε t * s (plays (stratSign s ε) (fun _ => 0) (fun t => pol t ω) t) / 4| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range n, (1 : ℝ) := Finset.sum_le_sum hb
      _ = n := by simp

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Clause (c), the mean. -/
theorem lowerU_small_mean (hd : 1 ≤ d) (hn : 1 ≤ n) {a : E d} {R0 : ℝ} (hb : BodyU K a r0 R0)
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    LowerMean K n r0 μ pol (Real.sqrt n / (4 * Real.sqrt 3)) := by
  obtain ⟨s, hs⟩ := exists_sdir hd hb
  have hint : ∀ ε : Fin n → Bool, Integrable (fun ω => regretAd K (stratSign s ε) (fun t => pol t ω) n) μ := by
    intro ε
    obtain ⟨hm, hb'⟩ := regret_sign_meas hs ε hpol
    set C := sInf ((fun y => ∑ t ∈ range n, (1 / 2 + sg ε t * s y / 4)) '' K)
    have h1 : Integrable (fun ω => regretAd K (stratSign s ε) (fun t => pol t ω) n + C) μ :=
      Integrable.of_bound (hm.add measurable_const).aestronglyMeasurable n
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb' ω)
    exact (h1.sub (integrable_const C)).congr (ae_of_all _ fun ω => by simp)
  have hsum : ∀ ω, 2 ^ n * (Real.sqrt n / (4 * Real.sqrt 3)) ≤
      ∑ ε : (Fin n → Bool), regretAd K (stratSign s ε) (fun t => pol t ω) n := fun ω =>
    (seed_facts hn hs (fun t => pol t ω) fun t ht => (hpol t ht).2 ω).1
  have hI : ∫ ω, ∑ ε : (Fin n → Bool), regretAd K (stratSign s ε) (fun t => pol t ω) n ∂μ =
      ∑ ε : (Fin n → Bool), ∫ ω, regretAd K (stratSign s ε) (fun t => pol t ω) n ∂μ :=
    integral_finsetSum _ fun ε _ => hint ε
  have hge : ∑ _ε : (Fin n → Bool), Real.sqrt n / (4 * Real.sqrt 3) ≤
      ∑ ε : (Fin n → Bool), ∫ ω, regretAd K (stratSign s ε) (fun t => pol t ω) n ∂μ := by
    rw [← hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
    rw [this]
    calc 2 ^ n * (Real.sqrt n / (4 * Real.sqrt 3)) = ∫ _ω, 2 ^ n * (Real.sqrt n / (4 * Real.sqrt 3)) ∂μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_finsetSum _ fun ε _ => hint ε) hsum
  obtain ⟨ε, -, hε⟩ := Finset.exists_le_of_sum_le univ_nonempty hge
  exact ⟨stratSign s ε, stratSign_mem hb.2.2.2.1 hb.1 hs ε, hint ε, hε⟩

/-- Clause (c), the probability. -/
theorem lowerU_small_prob (hd : 1 ≤ d) (hn : 1 ≤ n) {a : E d} {R0 : ℝ} (hb : BodyU K a r0 R0)
    {pol : Learner Ω d} (hpol : IsLearnerAd K n pol) :
    LowerProb K n r0 μ pol (Real.sqrt n / (8 * Real.sqrt 3)) (1 / 48) := by
  classical
  obtain ⟨s, hs⟩ := exists_sdir hd hb
  set θ := Real.sqrt n / (8 * Real.sqrt 3) with hθ
  set A : (Fin n → Bool) → Set Ω := fun ε => {ω | θ ≤ regretAd K (stratSign s ε) (fun t => pol t ω) n} with hA
  have hAm : ∀ ε, MeasurableSet (A ε) := fun ε =>
    measurableSet_le measurable_const (regret_sign_meas hs ε hpol).1
  have hcount : ∀ ω, (2 ^ n : ℝ) / 48 ≤ ∑ ε : (Fin n → Bool), (A ε).indicator (1 : Ω → ℝ) ω := by
    intro ω
    have h := (seed_facts hn hs (fun t => pol t ω) fun t ht => (hpol t ht).2 ω).2
    have he : ∑ ε : (Fin n → Bool), (A ε).indicator (1 : Ω → ℝ) ω =
        (univ.filter fun ε : Fin n → Bool => θ ≤ regretAd K (stratSign s ε) (fun t => pol t ω) n).card := by
      simp only [Set.indicator_apply, Pi.one_apply, hA, Set.mem_ofPred_eq]
      rw [Finset.sum_boole]
    rw [he]
    linarith
  have hint1 : ∀ ε, Integrable ((A ε).indicator (1 : Ω → ℝ)) μ := fun ε =>
    (integrable_const (1 : ℝ)).indicator (hAm ε)
  have hI : ∫ ω, ∑ ε : (Fin n → Bool), (A ε).indicator (1 : Ω → ℝ) ω ∂μ = ∑ ε : (Fin n → Bool), μ.real (A ε) := by
    rw [integral_finsetSum _ fun ε _ => hint1 ε]
    exact Finset.sum_congr rfl fun ε _ => integral_indicator_one (hAm ε)
  have hge : ∑ _ε : (Fin n → Bool), (1 / 48 : ℝ) ≤ ∑ ε : (Fin n → Bool), μ.real (A ε) := by
    rw [← hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
    rw [this]
    calc (2 : ℝ) ^ n * (1 / 48) = ∫ _ω, (2 : ℝ) ^ n / 48 ∂μ := by simp; ring
      _ ≤ _ := integral_mono (integrable_const _)
          (integrable_finsetSum _ fun ε _ => hint1 ε) hcount
  obtain ⟨ε, -, hε⟩ := Finset.exists_le_of_sum_le univ_nonempty hge
  refine ⟨stratSign s ε, stratSign_mem hb.2.2.2.1 hb.1 hs ε, (regret_sign_meas hs ε hpol).1, ?_⟩
  have h48 : (1 / 48 : ENNReal) = ENNReal.ofReal (1 / 48) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [h48, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)]
  exact hε

end Clause

end AdversarialBco.UnifiedLower.Small
