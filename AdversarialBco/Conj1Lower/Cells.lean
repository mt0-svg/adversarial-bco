/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Dent

@[expose] public section

/-!
# The cells of the paper's section on the lower bound: Lemma REGULAR, ripeness, the pointwise bounds of the rest lemma,
the ratios of
Lemma LEAK

The parameters of the strategy: `ε = k`, `r₁ = 5 d^{1/2}`, `κ = g/k`; here `dd` is the dimension as a real number and `DMv`
the value of `D_M = tr(M Σ)` of the frame (Frame.lean, `DM`). The frame `(m, A)` and the play `x` are fixed; `θ` is the
tip. `T = readT A m θ x`, `R² = ‖A (θ - m)‖²`.

* `cellOf`: tail (`T > (2k)^{1/2}`), else outer (`R² > 4d`), else inner (`R² < D_M/64`), else regular; a partition
  by construction, with the regular cell of the section on the lower bound (`cellOf_regular_iff`).
* `ripe π`: the tail is ripe if its mass is at least `ε₁ = k³/d³` or `E_π[T²; tail] ≥ ε₃ = k³/d²`; the outer and the
  inner cell if their mass is at least `ε₂ = k²/d²`; the regular cell never. `answer`: the cell of the tip if it is
  ripe, `none` (the cell rest) otherwise.
* Lemma REGULAR: `regular_closed` (i), `regular_dev` and `regular_const` (ii), `regular_half` (iii).
* The rest lemma, pointwise: the gap `q(x) - D(x; θ)` is in `[0, κ φ(a)]` (`gap_nonneg`, `gap_le_bowl`), at most `2κk`
  off
  the tail (`gap_nontail`), `κ² (4T² + r₁T) φ(a)` squared on the tail (`gap_sq_tail`), `κ² 2^20 (k³/d²) φ(a)` squared
  on the regular cell (`gap_sq_regular`); the arithmetic of its proof (`rest_mass_arith`, `rest_shell_arith`,
  `rest_tail_arith`, `rest_ratio_arith`, `rest_price_arith`).
* Lemma LEAK, the ratios: `plog_le_one_sub`, `plog_mono`, `entropy_le_ripe`, `leak_tail_mass`, `leak_tail_moment`,
  `leak_shell`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace AdversarialBco.Lower

/-- The four cells of a round. -/
inductive Cell
  | tail
  | outer
  | inner
  | regular
  deriving DecidableEq

instance : Fintype Cell :=
  ⟨{Cell.tail, Cell.outer, Cell.inner, Cell.regular}, fun c => by cases c <;> simp⟩

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The cell of the tip `θ` for the play `x`, in the frame `(m, A)` with `D_M = DMv`, dimension `dd` and scale `k`: the
tail first, then the outer cell, the inner cell, the regular cell. -/
noncomputable def cellOf (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x θ : V) : Cell :=
  if Real.sqrt (2 * k) < readT A m θ x then Cell.tail
  else if 4 * dd < ‖A (θ - m)‖ ^ 2 then Cell.outer
  else if ‖A (θ - m)‖ ^ 2 < DMv / 64 then Cell.inner
  else Cell.regular

/-- The set of tips in the cell `c`. -/
def cellSet (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) (c : Cell) : Set V :=
  {θ | cellOf A m k dd DMv x θ = c}

/-- `ε₁ = k³/d³`. -/
noncomputable def epsTail (k dd : ℝ) : ℝ := k ^ 3 / dd ^ 3

/-- `ε₂ = k²/d²`. -/
noncomputable def epsShell (k dd : ℝ) : ℝ := k ^ 2 / dd ^ 2

/-- `ε₃ = k³/d²`. -/
noncomputable def epsMom (k dd : ℝ) : ℝ := k ^ 3 / dd ^ 2

/-- Ripeness of a cell for the law `π` of the tip. -/
def ripe [MeasurableSpace V] (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : Cell → Prop
  | Cell.tail => epsTail k dd ≤ π.real (cellSet A m k dd DMv x Cell.tail) ∨
      epsMom k dd ≤ ∫ θ in cellSet A m k dd DMv x Cell.tail, readT A m θ x ^ 2 ∂π
  | Cell.outer => epsShell k dd ≤ π.real (cellSet A m k dd DMv x Cell.outer)
  | Cell.inner => epsShell k dd ≤ π.real (cellSet A m k dd DMv x Cell.inner)
  | Cell.regular => False

open Classical in
/-- The genie's answer for the tip `θ`: its cell if that cell is ripe, `none` (the cell rest) otherwise. -/
noncomputable def answer [MeasurableSpace V] (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x θ : V) :
    Option Cell :=
  if ripe π A m k dd DMv x (cellOf A m k dd DMv x θ) then some (cellOf A m k dd DMv x θ) else none

/-- The cell rest: the tips whose answer is `none` (the regular cell and the cells that are not ripe). -/
def restSet [MeasurableSpace V] (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) : Set V :=
  {θ | answer π A m k dd DMv x θ = none}

end Defs

/-! ## The cells -/

theorem cellOf_tail_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (k dd DMv : ℝ) (x θ : V) :
    cellOf A m k dd DMv x θ = Cell.tail ↔ Real.sqrt (2 * k) < readT A m θ x := by
  unfold cellOf
  constructor
  · intro h
    by_cases hc : Real.sqrt (2 * k) < readT A m θ x
    · exact hc
    · have h_if : (if Real.sqrt (2 * k) < readT A m θ x then Cell.tail
        else if 4 * dd < ‖A (θ - m)‖ ^ 2 then Cell.outer
        else if ‖A (θ - m)‖ ^ 2 < DMv / 64 then Cell.inner
        else Cell.regular) = (if 4 * dd < ‖A (θ - m)‖ ^ 2 then Cell.outer
        else if ‖A (θ - m)‖ ^ 2 < DMv / 64 then Cell.inner
        else Cell.regular) := by
        rw [ite_eq_right hc]
      rw [h_if] at h
      by_cases hc2 : 4 * dd < ‖A (θ - m)‖ ^ 2
      · rw [ite_eq_left hc2] at h
        injection h
      · rw [ite_eq_right hc2] at h
        by_cases hc3 : ‖A (θ - m)‖ ^ 2 < DMv / 64
        · rw [ite_eq_left hc3] at h
          injection h
        · rw [ite_eq_right hc3] at h
          injection h
  · intro h
    rw [ite_eq_left h]

theorem readT_le_of_ne_tail {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (k dd DMv : ℝ) (x θ : V) (h : cellOf A m k dd DMv x θ ≠ Cell.tail) :
    readT A m θ x ≤ Real.sqrt (2 * k) := by
  by_contra! hlt
  apply h
  unfold cellOf
  rw [ite_eq_left hlt]

theorem cellOf_outer_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (k dd DMv : ℝ) (x θ : V) :
    cellOf A m k dd DMv x θ = Cell.outer ↔
      readT A m θ x ≤ Real.sqrt (2 * k) ∧ 4 * dd < ‖A (θ - m)‖ ^ 2 := by
  unfold cellOf
  split_ifs with h1 h2 h3
  · -- h1: Real.sqrt (2 * k) < readT A m θ x, cell = Cell.tail → simplified to False
    constructor
    · intro h_eq; exact False.elim h_eq
    · intro ⟨hle, _⟩; exact not_le.mpr h1 hle
  · -- h1 false, h2: 4 * dd < ‖A (θ - m)‖ ^ 2, cell = Cell.outer
    constructor
    · intro _; exact ⟨le_of_not_gt h1, h2⟩
    · intro ⟨_, _⟩; rfl
  · -- h1 false, h2 false, h3: ‖A (θ - m)‖ ^ 2 < DMv / 64, cell = Cell.inner → simplified to False
    constructor
    · intro h_eq; exact False.elim h_eq
    · intro ⟨_, hlt⟩; exact h2 hlt
  · -- h1 false, h2 false, h3 false, cell = Cell.regular → simplified to False
    constructor
    · intro h_eq; exact False.elim h_eq
    · intro ⟨_, hlt⟩; exact h2 hlt

theorem cellOf_inner_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (k dd DMv : ℝ) (x θ : V) :
    cellOf A m k dd DMv x θ = Cell.inner ↔
      readT A m θ x ≤ Real.sqrt (2 * k) ∧ ‖A (θ - m)‖ ^ 2 ≤ 4 * dd ∧ ‖A (θ - m)‖ ^ 2 < DMv / 64 := by
  unfold cellOf
  by_cases h1 : Real.sqrt (2 * k) < readT A m θ x
  · rw [if_pos h1]
    constructor
    · intro h; injection h
    · intro h; rcases h with ⟨hle, _, _⟩; linarith
  · rw [if_neg h1]
    by_cases h2 : 4 * dd < ‖A (θ - m)‖ ^ 2
    · rw [if_pos h2]
      constructor
      · intro h; injection h
      · intro h; rcases h with ⟨_, hle, _⟩; linarith
    · rw [if_neg h2]
      by_cases h3 : ‖A (θ - m)‖ ^ 2 < DMv / 64
      · rw [if_pos h3]
        constructor
        · intro _; exact ⟨le_of_not_gt h1, le_of_not_gt h2, h3⟩
        · intro _; rfl
      · rw [if_neg h3]
        constructor
        · intro h; injection h
        · intro h; rcases h with ⟨_, _, hge⟩; linarith

/-- The regular cell is that of the section on the lower bound: `T ≤ (2k)^{1/2}` and `D_M/64 ≤ R² ≤ 4d`. -/
theorem cellOf_regular_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (k dd DMv : ℝ) (x θ : V) :
    cellOf A m k dd DMv x θ = Cell.regular ↔
      readT A m θ x ≤ Real.sqrt (2 * k) ∧ DMv / 64 ≤ ‖A (θ - m)‖ ^ 2 ∧ ‖A (θ - m)‖ ^ 2 ≤ 4 * dd := by
  unfold cellOf
  split_ifs with h1 h2 h3
  · -- h1: Real.sqrt (2 * k) < readT A m θ x
    constructor
    · intro h_eq; simp at h_eq
    · intro h_and; rcases h_and with ⟨hle, _, _⟩; linarith
  · -- h1: ¬ (Real.sqrt (2 * k) < readT A m θ x), h2: 4 * dd < ‖A (θ - m)‖ ^ 2
    constructor
    · intro h_eq; simp at h_eq
    · intro h_and; rcases h_and with ⟨_, _, hle⟩; linarith
  · -- h1: ¬ (Real.sqrt (2 * k) < readT A m θ x), h2: ¬ (4 * dd < ‖A (θ - m)‖ ^ 2), h3: ‖A (θ - m)‖ ^ 2 < DMv / 64
    constructor
    · intro h_eq; simp at h_eq
    · intro h_and; rcases h_and with ⟨_, hle, _⟩; linarith
  · -- all conditions false: regular branch
    constructor
    · intro _; exact ⟨not_lt.mp h1, not_lt.mp h3, not_lt.mp h2⟩
    · intro _; rfl

theorem answer_eq_some_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x θ : V) (c : Cell) :
    answer π A m k dd DMv x θ = some c ↔ cellOf A m k dd DMv x θ = c ∧ ripe π A m k dd DMv x c := by
  unfold answer
  split_ifs with h
  · -- h : ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)
    constructor
    · intro h_eq
      have h_cell : cellOf A m k dd DMv x θ = c := by
        simpa using h_eq
      refine ⟨h_cell, ?_⟩
      simpa [h_cell] using h
    · intro ⟨h_cell, h_ripe⟩
      simp [h_cell]
  · -- h : ¬ ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)
    constructor
    · intro h_eq
      simp at h_eq
    · intro ⟨h_cell, h_ripe⟩
      have h_ripe' : ripe π A m k dd DMv x (cellOf A m k dd DMv x θ) := by
        simpa [h_cell] using h_ripe
      exact absurd h_ripe' h

/-! ## Lemma REGULAR -/

/-- Lemma REGULAR (i): `R² ≤ 4d` puts the tip in the closed form, `|θ - m|_M + ρ ≤ r₁ = 5 d^{1/2}`. -/
theorem regular_closed {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (k dd : ℝ) (hk : 0 < k) (hd : 2048 * k ≤ dd) (θ : V) (hR : ‖A (θ - m)‖ ^ 2 ≤ 4 * dd) :
    ‖A (θ - m)‖ + rho A m k θ ≤ 5 * Real.sqrt dd := by
  set R := ‖A (θ - m)‖ with hRdef
  have hR_nonneg : 0 ≤ R := norm_nonneg _
  have hdd_pos : 0 < dd := by
    nlinarith
  have hR_sq_le : R ^ 2 ≤ 4 * dd := hR
  have h_sum_sq_le : R ^ 2 + 2 * k ≤ 9 * dd := by
    nlinarith
  have hR_le_2sqrt : R ≤ 2 * Real.sqrt dd := by
    calc
      R = Real.sqrt (R ^ 2) := by rw [Real.sqrt_sq hR_nonneg]
      _ ≤ Real.sqrt (4 * dd) := Real.sqrt_le_sqrt hR_sq_le
      _ = Real.sqrt 4 * Real.sqrt dd := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) dd]
      _ = 2 * Real.sqrt dd := by norm_num
  have h_sqrt_le : Real.sqrt (R ^ 2 + 2 * k) ≤ 3 * Real.sqrt dd := by
    calc
      Real.sqrt (R ^ 2 + 2 * k) ≤ Real.sqrt (9 * dd) := Real.sqrt_le_sqrt h_sum_sq_le
      _ = Real.sqrt 9 * Real.sqrt dd := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (9 : ℝ)) dd]
      _ = 3 * Real.sqrt dd := by norm_num
  calc
    ‖A (θ - m)‖ + rho A m k θ = R + Real.sqrt (R ^ 2 + 2 * k) := by
      simp [rho, hRdef]
    _ ≤ (2 * Real.sqrt dd) + (3 * Real.sqrt dd) := by
      nlinarith
    _ = 5 * Real.sqrt dd := by ring

/-- Lemma REGULAR (ii): for a regular tip, `q - D ≤ κ 512 k²/D_M` at every play. -/
theorem regular_dev {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ k dd DMv : ℝ) (hκ : 0 < κ) (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : 0 < DMv) (θ x : V)
    (hT : readT A m θ x ≤ Real.sqrt (2 * k)) (hR1 : DMv / 64 ≤ ‖A (θ - m)‖ ^ 2)
    (hR2 : ‖A (θ - m)‖ ^ 2 ≤ 4 * dd) :
    bowl A m κ k (5 * Real.sqrt dd) x - κ * (512 * k ^ 2 / DMv) ≤ dent A m κ k (5 * Real.sqrt dd) θ x := by
  set r₁ := 5 * Real.sqrt dd with hr₁
  set h := hq A m k θ x with hh
  set ρ := rho A m k θ with hρ
  set R := ‖A (θ - m)‖ with hR
  have hr₁_nonneg : 0 ≤ r₁ := by
    have hdd_nonneg : 0 ≤ dd := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt dd := Real.sqrt_nonneg _
    nlinarith
  have hreg : R + ρ ≤ r₁ := by
    have hreg' := regular_closed A m k dd hk hd θ hR2
    simpa [hr₁, hρ, hR] using hreg'
  have hbound := dent_closed_form_bound A m κ k r₁ hκ hk θ x hreg
  -- hbound : bowl A m κ k r₁ x - κ * (2 * max (hq A m k θ x) 0 ^ 2 / rho A m k θ ^ 2) ≤ dent A m κ k r₁ θ x
  have hdiv : 2 * max h 0 ^ 2 / ρ ^ 2 ≤ 512 * k ^ 2 / DMv := by
    by_cases hnonpos : h ≤ 0
    · have hmax : max h 0 = 0 := max_eq_right hnonpos
      rw [hmax]
      simp
      positivity
    · have hpos : 0 < h := by linarith
      have hmax : max h 0 = h := max_eq_left hpos.le
      rw [hmax]
      have hform := dent_closed_form A m κ k r₁ hκ hk θ x hreg
      rcases hform with ⟨_, hcase2⟩
      have hpos_case := hcase2 hpos
      rcases hpos_case with ⟨hx_le_r₁, _, _⟩
      have hhgen : hgen A m k r₁ θ x = h := by
        dsimp [hgen]
        rw [if_pos hx_le_r₁, hh]
      have hh_le_2k : hgen A m k r₁ θ x ≤ 2 * k :=
        hgen_le_two_k A m k r₁ hk.le hr₁_nonneg θ x hT
      have hh_le_2k' : h ≤ 2 * k := by linarith
      have hsq : h ^ 2 ≤ 4 * k ^ 2 := by nlinarith
      have hρ_sq_eq : ρ ^ 2 = R ^ 2 + 2 * k := by
        dsimp [ρ, rho]
        have h_nonneg : 0 ≤ ‖A (θ - m)‖ ^ 2 + 2 * k := by
          nlinarith [sq_nonneg (‖A (θ - m)‖)]
        rw [Real.sq_sqrt h_nonneg]
      have hρ_sq_ge : DMv / 64 ≤ ρ ^ 2 := by
        rw [hρ_sq_eq]
        linarith
      have hρ_sq_pos : 0 < ρ ^ 2 := by
        rw [hρ_sq_eq]
        have hR_sq_nonneg : 0 ≤ R ^ 2 := sq_nonneg _
        nlinarith
      rw [div_le_div_iff₀ hρ_sq_pos hDM]
      nlinarith
  have hgoal : bowl A m κ k r₁ x - κ * (512 * k ^ 2 / DMv) ≤ dent A m κ k r₁ θ x := by
    have h_mul : κ * (2 * max h 0 ^ 2 / ρ ^ 2) ≤ κ * (512 * k ^ 2 / DMv) := by
      nlinarith
    linarith
  simpa [hr₁] using hgoal

/-- Lemma REGULAR (ii), the constants: `512 k²/D_M ≤ 1024 k²/d ≤ k/2` when `D_M ≥ d/2`, `d ≥ 2048 k`. -/
theorem regular_const (k dd DMv : ℝ) (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) :
    512 * k ^ 2 / DMv ≤ 1024 * k ^ 2 / dd ∧ 1024 * k ^ 2 / dd ≤ k / 2 := by
  have hdd_pos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    nlinarith
  have hDMv_pos : 0 < DMv := by
    have : 0 < dd / 2 := by nlinarith
    nlinarith
  have h2_pos : 0 < (2 : ℝ) := by norm_num
  constructor
  · rw [div_le_div_iff₀ hDMv_pos hdd_pos]
    nlinarith
  · rw [div_le_div_iff₀ hdd_pos h2_pos]
    nlinarith

/-- Lemma REGULAR (iii): on a live round (`D_M ≥ d/2`), `D ≥ q/2` for a regular tip at every play. -/
theorem regular_half {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ k dd DMv : ℝ) (hκ : 0 < κ) (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (θ x : V)
    (hT : readT A m θ x ≤ Real.sqrt (2 * k)) (hR1 : DMv / 64 ≤ ‖A (θ - m)‖ ^ 2)
    (hR2 : ‖A (θ - m)‖ ^ 2 ≤ 4 * dd) :
    bowl A m κ k (5 * Real.sqrt dd) x / 2 ≤ dent A m κ k (5 * Real.sqrt dd) θ x := by
  have hDMpos : 0 < DMv := by
    have hddpos : 0 < dd := by linarith
    linarith
  have hdev := regular_dev A m κ k dd DMv hκ hk hd hDMpos θ x hT hR1 hR2
  rcases regular_const k dd DMv hk hd hDM with ⟨hconst1, hconst2⟩
  have hconst : 512 * k ^ 2 / DMv ≤ k / 2 := hconst1.trans hconst2
  have hbowl := bowl_ge A m κ k (5 * Real.sqrt dd) (by linarith) (by positivity) x
  have hineq1 : κ * (512 * k ^ 2 / DMv) ≤ κ * (k / 2) :=
    mul_le_mul_of_nonneg_left hconst (by linarith)
  have hineq2 : κ * (k / 2) = (κ * k) / 2 := by ring
  have hineq3 : (κ * k) / 2 ≤ bowl A m κ k (5 * Real.sqrt dd) x / 2 :=
    div_le_div_of_nonneg_right hbowl (by norm_num)
  have hineq4 : κ * (512 * k ^ 2 / DMv) ≤ bowl A m κ k (5 * Real.sqrt dd) x / 2 := by
    linarith
  linarith

/-! ## The rest lemma, pointwise -/

theorem gap_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x : V) :
    0 ≤ bowl A m κ ε r₁ x - dent A m κ ε r₁ θ x := by
  have h_one_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    refine ⟨by norm_num, by norm_num⟩
  have h_bowl_nonneg : ∀ y : V, 0 ≤ (bowl A m κ ε r₁) y := by
    intro y
    dsimp [bowl, huber]
    have hsq : 0 ≤ ‖A (y - m)‖ ^ 2 := pow_two_nonneg _
    have hnorm : 0 ≤ ‖A (y - m)‖ := norm_nonneg _
    split_ifs with h
    · nlinarith
    · have hlt : r₁ < ‖A (y - m)‖ := by linarith
      have hpos : 0 ≤ r₁ * ‖A (y - m)‖ - r₁ ^ 2 / 2 + ε := by
        have : r₁ * ‖A (y - m)‖ - r₁ ^ 2 / 2 + ε = r₁ * (‖A (y - m)‖ - r₁ / 2) + ε := by ring
        rw [this]
        have h_nonneg : 0 ≤ r₁ * (‖A (y - m)‖ - r₁ / 2) := by
          have h_inner : 0 ≤ ‖A (y - m)‖ - r₁ / 2 := by linarith
          nlinarith
        nlinarith
      nlinarith
  have h_bdd : BddBelow (Set.range (fun (l : Set.Ioc (0 : ℝ) 1) =>
    (l : ℝ) * (bowl A m κ ε r₁) (θ + (l : ℝ)⁻¹ • (x - θ)))) := by
    refine ⟨0, ?_⟩
    rintro z ⟨l, rfl⟩
    have hl : 0 ≤ (l : ℝ) := l.2.1.le
    have hbowl := h_bowl_nonneg (θ + (l : ℝ)⁻¹ • (x - θ))
    nlinarith
  have hdent_le_bowl : dent A m κ ε r₁ θ x ≤ bowl A m κ ε r₁ x := by
    calc
      dent A m κ ε r₁ θ x = hull (bowl A m κ ε r₁) θ x := rfl
      _ = ⨅ l : Set.Ioc (0 : ℝ) 1, (l : ℝ) * (bowl A m κ ε r₁) (θ + (l : ℝ)⁻¹ • (x - θ)) := rfl
      _ ≤ (1 : ℝ) * (bowl A m κ ε r₁) (θ + ((1 : ℝ)⁻¹) • (x - θ)) := by
        apply csInf_le h_bdd
        exact ⟨⟨1, h_one_mem⟩, rfl⟩
      _ = bowl A m κ ε r₁ x := by simp
  linarith

theorem gap_le_bowl {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x : V) :
    bowl A m κ ε r₁ x - dent A m κ ε r₁ θ x ≤ κ * huber r₁ ε ‖A (x - m)‖ := by
  dsimp [bowl]
  have h := dent_nonneg A m κ ε r₁ hκ hε hr θ x
  linarith

/-- Off the tail, `q - D ≤ 2κk` (Lemma D (d), (d1)). -/
theorem gap_nontail {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ k r₁ : ℝ) (hκ : 0 ≤ κ) (hk : 0 ≤ k) (hr : 0 < r₁) (θ x : V)
    (hT : readT A m θ x ≤ Real.sqrt (2 * k)) :
    bowl A m κ k r₁ x - dent A m κ k r₁ θ x ≤ κ * (2 * k) := by
  have h_dent_tangent := dent_tangent A m κ k r₁ hκ hk hr θ x
  have h_hgen := hgen_le_two_k A m k r₁ hk (le_of_lt hr) θ x hT
  have h_nonneg_two_k : 0 ≤ 2 * k := by nlinarith
  have h_max : max (hgen A m k r₁ θ x) 0 ≤ 2 * k :=
    max_le h_hgen h_nonneg_two_k
  have h_mul : κ * max (hgen A m k r₁ θ x) 0 ≤ κ * (2 * k) :=
    mul_le_mul_of_nonneg_left h_max hκ
  linarith

/-- On the tail, `(q - D)² ≤ κ² (4T² + r₁ T) φ(a)` (Lemma D (d), (d2)). -/
theorem gap_sq_tail {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ k r₁ : ℝ) (hκ : 0 ≤ κ) (hk : 0 < k) (hr : 0 < r₁) (θ x : V)
    (hT : Real.sqrt (2 * k) < readT A m θ x) :
    (bowl A m κ k r₁ x - dent A m κ k r₁ θ x) ^ 2 ≤
      κ ^ 2 * ((4 * readT A m θ x ^ 2 + r₁ * readT A m θ x) * huber r₁ k ‖A (x - m)‖) := by
  set G := bowl A m κ k r₁ x - dent A m κ k r₁ θ x with hG
  set φ := huber r₁ k ‖A (x - m)‖ with hφ
  set u := max (hgen A m k r₁ θ x) 0 with hu
  have hG_nonneg : 0 ≤ G := by
    have h := dent_le_bowl A m κ k r₁ hκ (by linarith) (by linarith) θ x
    linarith
  have hG_le_κu : G ≤ κ * u := by
    have h := dent_tangent A m κ k r₁ hκ (by linarith) hr θ x
    linarith
  have hG_le_κφ : G ≤ κ * φ := by
    have h_dent_nonneg : 0 ≤ dent A m κ k r₁ θ x :=
      dent_nonneg A m κ k r₁ hκ (by linarith) (by linarith) θ x
    have h_bowl_eq : bowl A m κ k r₁ x = κ * φ := by
      rw [hφ, bowl]
    linarith
  have hG_le_κ_min : G ≤ κ * min u φ := by
    have h_min : G ≤ min (κ * u) (κ * φ) := le_min hG_le_κu hG_le_κφ
    rw [← mul_min_of_nonneg u φ hκ] at h_min
    exact h_min
  have h_sq : G ^ 2 ≤ (κ * min u φ) ^ 2 := by
    nlinarith
  have h_min_sq : (min u φ) ^ 2 ≤ (4 * readT A m θ x ^ 2 + r₁ * readT A m θ x) * huber r₁ k ‖A (x - m)‖ := by
    rw [hu, hφ]
    exact hgen_tail A m k r₁ hk (by linarith) θ x hT
  calc
    G ^ 2 ≤ (κ * min u φ) ^ 2 := h_sq
    _ = κ ^ 2 * (min u φ) ^ 2 := by ring
    _ ≤ κ ^ 2 * ((4 * readT A m θ x ^ 2 + r₁ * readT A m θ x) * huber r₁ k ‖A (x - m)‖) := by
      have hκsq_nonneg : 0 ≤ κ ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h_min_sq hκsq_nonneg

/-- On the regular cell of a live round, `(q - D)² ≤ κ² 2^20 (k³/d²) φ(a)`. -/
theorem gap_sq_regular {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ k dd DMv : ℝ) (hκ : 0 < κ) (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (θ x : V)
    (hT : readT A m θ x ≤ Real.sqrt (2 * k)) (hR1 : DMv / 64 ≤ ‖A (θ - m)‖ ^ 2)
    (hR2 : ‖A (θ - m)‖ ^ 2 ≤ 4 * dd) :
    (bowl A m κ k (5 * Real.sqrt dd) x - dent A m κ k (5 * Real.sqrt dd) θ x) ^ 2 ≤
      κ ^ 2 * (2 ^ 20 * (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) := by
  have hDM_pos : 0 < DMv := by linarith
  have hdd_pos : 0 < dd := by linarith
  set G := bowl A m κ k (5 * Real.sqrt dd) x - dent A m κ k (5 * Real.sqrt dd) θ x with hG_def
  have hG_nonneg : 0 ≤ G := by
    rw [hG_def]
    exact gap_nonneg A m κ k (5 * Real.sqrt dd) (by linarith) (by positivity) (by positivity) θ x
  have h_regular_dev : bowl A m κ k (5 * Real.sqrt dd) x - κ * (512 * k ^ 2 / DMv) ≤
      dent A m κ k (5 * Real.sqrt dd) θ x :=
    regular_dev A m κ k dd DMv hκ hk hd hDM_pos θ x hT hR1 hR2
  have hG_le : G ≤ κ * (512 * k ^ 2 / DMv) := by
    rw [hG_def]
    linarith
  have h_reg_const := regular_const k dd DMv hk hd hDM
  have h_512_le_1024 : 512 * k ^ 2 / DMv ≤ 1024 * k ^ 2 / dd := h_reg_const.1
  have hG_le' : G ≤ κ * (1024 * k ^ 2 / dd) := by
    apply le_trans hG_le
    gcongr
  have h_sq : G ^ 2 ≤ (κ * (1024 * k ^ 2 / dd)) ^ 2 :=
    pow_le_pow_left₀ hG_nonneg hG_le' 2
  have h_expand : (κ * (1024 * k ^ 2 / dd)) ^ 2 = κ ^ 2 * (2 ^ 20 * k ^ 4 / dd ^ 2) := by
    field_simp [hdd_pos.ne']
    ring
  have h_huber : k ≤ huber (5 * Real.sqrt dd) k ‖A (x - m)‖ :=
    huber_ge (5 * Real.sqrt dd) k ‖A (x - m)‖ (by positivity)
  have h_k4_eq : (k ^ 3 / dd ^ 2) * k = k ^ 4 / dd ^ 2 := by
    field_simp [hdd_pos.ne']
  have h_k4_le : (k ^ 3 / dd ^ 2) * k ≤ (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖ := by
    rw [h_k4_eq]
    calc
      k ^ 4 / dd ^ 2 = (k ^ 3 / dd ^ 2) * k := by
        field_simp [hdd_pos.ne']
      _ ≤ (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖ := by
        gcongr
  have h_final_eq : κ ^ 2 * (2 ^ 20 * k ^ 4 / dd ^ 2) = κ ^ 2 * (2 ^ 20 * ((k ^ 3 / dd ^ 2) * k)) := by
    congr
    field_simp [hdd_pos.ne']
  have h_final_le : κ ^ 2 * (2 ^ 20 * ((k ^ 3 / dd ^ 2) * k)) ≤
      κ ^ 2 * (2 ^ 20 * (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) := by
    have h_nonneg : 0 ≤ κ ^ 2 * (2 ^ 20 : ℝ) := by positivity
    calc
      κ ^ 2 * (2 ^ 20 * ((k ^ 3 / dd ^ 2) * k)) = (κ ^ 2 * (2 ^ 20 : ℝ)) * ((k ^ 3 / dd ^ 2) * k) := by ring
      _ ≤ (κ ^ 2 * (2 ^ 20 : ℝ)) * ((k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) :=
        mul_le_mul_of_nonneg_left h_k4_le h_nonneg
      _ = κ ^ 2 * (2 ^ 20 * (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) := by ring
  rw [hG_def]
  calc
    G ^ 2 ≤ (κ * (1024 * k ^ 2 / dd)) ^ 2 := h_sq
    _ = κ ^ 2 * (2 ^ 20 * k ^ 4 / dd ^ 2) := h_expand
    _ = κ ^ 2 * (2 ^ 20 * ((k ^ 3 / dd ^ 2) * k)) := h_final_eq
    _ ≤ κ ^ 2 * (2 ^ 20 * (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) := h_final_le

/-- The masses of the cells of rest outside the regular cell: `ε₁ + 2 ε₂ ≤ 3 k²/d² ≤ 0.001`. -/
theorem rest_mass_arith (k dd : ℝ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) :
    epsTail k dd + 2 * epsShell k dd ≤ 3 * k ^ 2 / dd ^ 2 ∧ 3 * k ^ 2 / dd ^ 2 ≤ 1 / 1000 := by
  have hdd_pos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    nlinarith
  have hk_div_dd_le_one : k / dd ≤ 1 := by
    apply (div_le_one hdd_pos).mpr
    nlinarith
  have hk_sq_div_dd_sq_nonneg : 0 ≤ k ^ 2 / dd ^ 2 := by
    positivity
  have h_epsTail_le_epsShell : epsTail k dd ≤ epsShell k dd := by
    dsimp [epsTail, epsShell]
    calc
      k ^ 3 / dd ^ 3 = (k ^ 2 / dd ^ 2) * (k / dd) := by ring
      _ ≤ (k ^ 2 / dd ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hk_div_dd_le_one hk_sq_div_dd_sq_nonneg
      _ = k ^ 2 / dd ^ 2 := by ring
  have h_first : epsTail k dd + 2 * epsShell k dd ≤ 3 * k ^ 2 / dd ^ 2 := by
    dsimp [epsTail, epsShell]
    field_simp [hdd_pos.ne.symm]
    nlinarith
  have h_second : 3 * k ^ 2 / dd ^ 2 ≤ 1 / 1000 := by
    field_simp [hdd_pos.ne.symm]
    nlinarith
  exact And.intro h_first h_second

/-- The inner and outer cells of rest: `2 ε₂ 4k² ≤ 8 (k³/d²) φ` for `φ ≥ k`. -/
theorem rest_shell_arith (k dd φ : ℝ) (hk : 0 < k) (hd : 0 < dd) (hφ : k ≤ φ) :
    2 * epsShell k dd * (4 * k ^ 2) ≤ 8 * (k ^ 3 / dd ^ 2) * φ := by
  unfold epsShell
  have hdd : dd ^ 2 ≠ 0 := by positivity
  field_simp [hdd]
  nlinarith

/-- The tail of rest: `4 E[T²; tail] + r₁ E[T; tail] ≤ 9 k³/d²` from `E[T²; tail] ≤ ε₃` and
`E[T; tail] ≤ (ε₁ ε₃)^{1/2}`, `r₁ = 5 d^{1/2}`. -/
theorem rest_tail_arith (k dd S M : ℝ) (hk : 0 < k) (hd : 0 < dd) (hS : S ≤ epsMom k dd)
    (hM : M ≤ Real.sqrt (epsTail k dd * epsMom k dd)) :
    4 * S + 5 * Real.sqrt dd * M ≤ 9 * (k ^ 3 / dd ^ 2) := by
  have hk3 : 0 ≤ k ^ 3 := by positivity
  have hdd2 : 0 ≤ dd ^ 2 := by positivity
  have hdd_sqrt_pos : Real.sqrt dd > 0 := Real.sqrt_pos.mpr hd
  have hdd_sqrt_ne : Real.sqrt dd ≠ 0 := hdd_sqrt_pos.ne.symm
  have h_eps_prod : epsTail k dd * epsMom k dd = k ^ 6 / dd ^ 5 := by
    dsimp [epsTail, epsMom]
    field_simp [hd.ne.symm]
  have h_sqrt_eps : Real.sqrt (epsTail k dd * epsMom k dd) = k ^ 3 / (dd ^ 2 * Real.sqrt dd) := by
    rw [h_eps_prod]
    rw [Real.sqrt_div (by positivity : 0 ≤ k ^ 6)]
    have hk6_sq : k ^ 6 = (k ^ 3) ^ 2 := by ring
    rw [hk6_sq, Real.sqrt_sq hk3]
    have h_sqrt_dd5 : Real.sqrt (dd ^ 5) = dd ^ 2 * Real.sqrt dd := by
      calc
        Real.sqrt (dd ^ 5) = Real.sqrt ((dd ^ 2) ^ 2 * dd) := by
          rw [show dd ^ 5 = (dd ^ 2) ^ 2 * dd by ring]
        _ = Real.sqrt ((dd ^ 2) ^ 2) * Real.sqrt dd := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ (dd ^ 2) ^ 2)]
        _ = dd ^ 2 * Real.sqrt dd := by rw [Real.sqrt_sq hdd2]
    rw [h_sqrt_dd5]
  have h_bound_M : 5 * Real.sqrt dd * M ≤ 5 * (k ^ 3 / dd ^ 2) := by
    have hM' : Real.sqrt dd * M ≤ Real.sqrt dd * Real.sqrt (epsTail k dd * epsMom k dd) :=
      mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
    have h_eq : Real.sqrt dd * Real.sqrt (epsTail k dd * epsMom k dd) = k ^ 3 / dd ^ 2 := by
      rw [h_sqrt_eps]
      field_simp [hd.ne.symm, hdd_sqrt_ne]
    calc
      5 * Real.sqrt dd * M = 5 * (Real.sqrt dd * M) := by ring
      _ ≤ 5 * (Real.sqrt dd * Real.sqrt (epsTail k dd * epsMom k dd)) := by nlinarith
      _ = 5 * (k ^ 3 / dd ^ 2) := by rw [h_eq]
  have h_bound_S : 4 * S ≤ 4 * (k ^ 3 / dd ^ 2) := by
    have : epsMom k dd = k ^ 3 / dd ^ 2 := rfl
    rw [this] at hS
    nlinarith
  nlinarith

/-- The rest lemma (i), the ratio: `p_rest ≥ 1/2` and `π(regular) ≥ p_rest - 3k²/d²` give `π(regular)/p_rest ≥ 1/2`. -/
theorem rest_ratio_arith (k dd preg pr : ℝ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hpr : 1 / 2 ≤ pr)
    (hreg : pr - 3 * k ^ 2 / dd ^ 2 ≤ preg) : 1 / 2 ≤ preg / pr := by
  have hpr_pos : 0 < pr := by linarith
  have hdd_pos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    nlinarith
  have hk_nonneg : 0 ≤ k := by linarith
  have hdd_nonneg : 0 ≤ dd := by linarith
  -- bound: 3*k^2/dd^2 ≤ 1/4
  have h_bound : 3 * k ^ 2 / dd ^ 2 ≤ 1/4 := by
    -- from hd: 2048*k ≤ dd, square both sides: (2048*k)^2 ≤ dd^2
    have h_sq : (2048 * k) ^ 2 ≤ dd ^ 2 := by
      have h_nonneg : 0 ≤ 2048 * k := by nlinarith
      nlinarith
    -- using div_le_div_iff₀ to clear denominators
    have h_main : 3 * k ^ 2 / dd ^ 2 ≤ 3 / ((2048 : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ (by nlinarith : 0 < dd ^ 2) (by nlinarith : 0 < (2048 : ℝ) ^ 2)).mpr
      nlinarith
    have h_final : 3 / ((2048 : ℝ) ^ 2) ≤ 1/4 := by nlinarith
    nlinarith
  -- from hreg: preg ≥ pr - 3*k^2/dd^2 ≥ pr - 1/4 ≥ pr/2 (since pr ≥ 1/2)
  have h_preg_ge : pr / 2 ≤ preg := by
    have h_intermediate : pr / 2 ≤ pr - 3 * k ^ 2 / dd ^ 2 := by
      have h_pr_half_ge_quarter : 1/4 ≤ pr / 2 := by nlinarith
      nlinarith
    nlinarith
  -- convert to 1/2 ≤ preg / pr using le_div_iff₀
  rw [le_div_iff₀ hpr_pos]
  nlinarith

/-- The rest lemma (ii), the final arithmetic: `I ≤ κ² V/(2σ²)`, `V ≤ (2^20 + 17)(k³/d²) φ / p_rest`, `κ φ ≤ 4 Dbar`,
`p_rest ≥ 1/2`, `κ = g/k` give `I ≤ g/(σ² P_R) Dbar` with `P_R = d²/(4194372 k²)`. -/
theorem rest_price_arith (g k dd σ φ Dbar pr I Vr : ℝ) (hg : 0 < g) (hk : 0 < k) (hd : 0 < dd) (hσ : 0 < σ)
    (hpr : 1 / 2 ≤ pr) (hφ : 0 ≤ φ) (hI : I ≤ (g / k) ^ 2 * Vr / (2 * σ ^ 2))
    (hV : Vr ≤ (2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * φ / pr) (hD : g / k * φ ≤ 4 * Dbar) :
    I ≤ g / (σ ^ 2 * (dd ^ 2 / (4194372 * k ^ 2))) * Dbar := by
  have h_gk_pos : 0 < g / k := div_pos hg hk
  have h_pr_pos : 0 < pr := by linarith
  have h_Dbar_nonneg : 0 ≤ Dbar := by
    have : 0 ≤ (g / k) * φ := mul_nonneg (by linarith) hφ
    linarith
  by_cases hVr_nonpos : Vr ≤ 0
  · have h_nonpos : (g / k) ^ 2 * Vr / (2 * σ ^ 2) ≤ 0 := by
      have : (g / k) ^ 2 * Vr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hVr_nonpos
      exact div_nonpos_of_nonpos_of_nonneg this (by positivity)
    have h_rhs_nonneg : 0 ≤ g / (σ ^ 2 * (dd ^ 2 / (4194372 * k ^ 2))) * Dbar := by
      have hpos : 0 ≤ g / (σ ^ 2 * (dd ^ 2 / (4194372 * k ^ 2))) :=
        div_nonneg (by linarith) (by positivity)
      exact mul_nonneg hpos h_Dbar_nonneg
    linarith
  · have hVr_nonneg : 0 ≤ Vr := by linarith
    have h_gk_sq_phi_le : (g / k) ^ 2 * φ ≤ 4 * (g / k) * Dbar := by
      calc
        (g / k) ^ 2 * φ = (g / k) * ((g / k) * φ) := by ring
        _ ≤ (g / k) * (4 * Dbar) := mul_le_mul_of_nonneg_left hD (by linarith)
        _ = 4 * (g / k) * Dbar := by ring
    have h_pr_inv_le_two : 1 / pr ≤ 2 := by
      have hpos_half : 0 < (1/2 : ℝ) := by norm_num
      have htemp := (one_div_le_one_div h_pr_pos hpos_half).mpr hpr
      -- htemp : 1 / pr ≤ 1 / (1/2)
      simpa [div_div] using htemp
    have h_const : (4194372 : ℝ) = 4 * ((2 : ℝ) ^ 20 + 17) := by norm_num
    calc
      I ≤ (g / k) ^ 2 * Vr / (2 * σ ^ 2) := hI
      _ ≤ (g / k) ^ 2 * ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * φ / pr) / (2 * σ ^ 2) := by
        have h_num_le : (g / k) ^ 2 * Vr ≤ (g / k) ^ 2 * ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * φ / pr) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
        exact div_le_div_of_nonneg_right h_num_le (by positivity)
      _ = ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) / pr) * ((g / k) ^ 2 * φ) / (2 * σ ^ 2) := by ring
      _ ≤ ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) / pr) * (4 * (g / k) * Dbar) / (2 * σ ^ 2) := by
        have h_factor_nonneg : 0 ≤ (2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) / pr := by positivity
        have h_num_le : ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) / pr) * ((g / k) ^ 2 * φ) ≤
                        ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) / pr) * (4 * (g / k) * Dbar) :=
          mul_le_mul_of_nonneg_left h_gk_sq_phi_le h_factor_nonneg
        exact div_le_div_of_nonneg_right h_num_le (by positivity)
      _ = 4 * (2 ^ 20 + 17) * g * k ^ 2 * Dbar / (pr * (2 * σ ^ 2 * dd ^ 2)) := by
        field_simp [hd.ne']
      _ ≤ 4 * (2 ^ 20 + 17) * g * k ^ 2 * Dbar / ((1/2) * (2 * σ ^ 2 * dd ^ 2)) := by
        have h_denom_le : (1/2 : ℝ) * (2 * σ ^ 2 * dd ^ 2) ≤ pr * (2 * σ ^ 2 * dd ^ 2) := by
          have hpos : 0 ≤ 2 * σ ^ 2 * dd ^ 2 := by positivity
          nlinarith
        have h_num_nonneg : 0 ≤ 4 * (2 ^ 20 + 17) * g * k ^ 2 * Dbar := by positivity
        have h_denom_pos' : 0 < (1/2 : ℝ) * (2 * σ ^ 2 * dd ^ 2) := by positivity
        exact div_le_div_of_nonneg_left h_num_nonneg h_denom_pos' h_denom_le
      _ = 4 * (2 ^ 20 + 17) * g * k ^ 2 * Dbar / (σ ^ 2 * dd ^ 2) := by ring
      _ = g / (σ ^ 2 * (dd ^ 2 / (4194372 * k ^ 2))) * Dbar := by
        field_simp [h_const]
        ring

/-! ## The rest lemma, integrated against the law of the tip -/

theorem continuous_readT_tip {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m x : V) : Continuous fun θ => readT A m θ x := by
  simp [readT, div_eq_mul_inv]
  have hg : Continuous fun θ : V => A θ - A m :=
    A.continuous.sub continuous_const
  apply Continuous.mul
  · exact Continuous.inner continuous_const hg
  · exact continuous_const

theorem measurableSet_cellSet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) (c : Cell) :
    MeasurableSet (cellSet A m k dd DMv x c) := by
  have hT : Measurable fun θ => readT A m θ x := (continuous_readT_tip A m x).measurable
  have hR : Measurable fun θ : V => ‖A (θ - m)‖ ^ 2 :=
    ((A.continuous.comp (continuous_id.sub continuous_const)).norm.pow 2).measurable
  have h1 : MeasurableSet {θ | Real.sqrt (2 * k) < readT A m θ x} := measurableSet_lt measurable_const hT
  have h2 : MeasurableSet {θ : V | 4 * dd < ‖A (θ - m)‖ ^ 2} := measurableSet_lt measurable_const hR
  have h3 : MeasurableSet {θ : V | ‖A (θ - m)‖ ^ 2 < DMv / 64} := measurableSet_lt hR measurable_const
  cases c
  · convert h1 using 1
    ext θ
    simp only [cellSet, cellOf, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  · convert h1.compl.inter h2 using 1
    ext θ
    simp only [cellSet, cellOf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    split_ifs <;> simp_all
  · convert (h1.compl.inter h2.compl).inter h3 using 1
    ext θ
    simp only [cellSet, cellOf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    split_ifs <;> simp_all
  · convert (h1.compl.inter h2.compl).inter h3.compl using 1
    ext θ
    simp only [cellSet, cellOf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    split_ifs <;> simp_all

theorem restSet_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    restSet π A m k dd DMv x = {θ | ¬ ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)} := by
  ext θ
  simp [restSet, answer]

theorem measurableSet_restSet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    MeasurableSet (restSet π A m k dd DMv x) := by
  rw [restSet_eq]
  have h_eq : {θ | ¬ ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)} = ⋃ c : Cell, cellSet A m k dd DMv x c ∩ {θ | ¬ ripe π A m k dd DMv x c} := by
    ext θ
    constructor
    · intro hθ
      refine Set.mem_iUnion.mpr ?_
      refine ⟨cellOf A m k dd DMv x θ, ?_, hθ⟩
      dsimp [cellSet]
    · intro hθ
      rcases Set.mem_iUnion.mp hθ with ⟨c, hc, hripe⟩
      dsimp [cellSet] at hc
      have h_eq' : cellOf A m k dd DMv x θ = c := hc
      simpa [h_eq'] using hripe
  rw [h_eq]
  refine MeasurableSet.iUnion (fun c => ?_)
  refine (measurableSet_cellSet A m k dd DMv x c).inter ?_
  exact MeasurableSet.const _

theorem regular_subset_restSet {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V) :
    cellSet A m k dd DMv x Cell.regular ⊆ restSet π A m k dd DMv x := by
  intro θ hθ
  rw [restSet_eq]
  simp only [cellSet, Set.mem_ofPred_eq] at hθ ⊢
  rw [hθ]
  simp [ripe]

theorem measurable_dent_tip {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (A : V →L[ℝ] V) (m : V) (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (x : V) :
    Measurable fun θ => dent A m κ ε r₁ θ x := by
  have h_eq : (fun θ => dent A m κ ε r₁ θ x) =
      fun θ => ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1},
        ((r : ℚ) : ℝ) * bowl A m κ ε r₁ (θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ)) := by
    ext θ
    exact dent_eq_iInf_rat A m κ ε r₁ hκ hε hr θ x
  rw [h_eq]
  refine Measurable.iInf ?_
  intro r
  have h_cont : Continuous (fun (θ : V) => ((r : ℚ) : ℝ) * bowl A m κ ε r₁ (θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ))) := by
    have h_bowl_cont : Continuous (bowl A m κ ε r₁) := continuous_bowl A m κ ε r₁
    have h_inner_cont : Continuous (fun (θ : V) => θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ)) := by
      have : Continuous (fun (θ : V) => ((r : ℚ) : ℝ)⁻¹ • (x - θ)) := by
        apply Continuous.smul
        · exact continuous_const
        · continuity
      continuity
    have h_comp_cont : Continuous (fun (θ : V) => bowl A m κ ε r₁ (θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ))) :=
      h_bowl_cont.comp h_inner_cont
    refine Continuous.mul ?_ h_comp_cont
    exact continuous_const
  exact h_cont.measurable

/-- The rest lemma (i), the mass: `π(regular) ≥ π(rest) - 3k²/d²` (the cells of rest outside the regular cell are not
ripe). -/
theorem rest_regular_mass {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (hk : 1 ≤ k)
    (hd : 2048 * k ≤ dd) (x : V) :
    π.real (restSet π A m k dd DMv x) - 3 * k ^ 2 / dd ^ 2 ≤ π.real (cellSet A m k dd DMv x Cell.regular) := by
  classical
    have h_rest_eq := restSet_eq π A m k dd DMv x
    have h_meas : MeasurableSet (cellSet A m k dd DMv x Cell.regular) :=
      measurableSet_cellSet A m k dd DMv x Cell.regular
    have h_arith := rest_mass_arith k dd hk hd
    rcases h_arith with ⟨h_arith₁, h_arith₂⟩
    have h_fin : ∀ s : Set V, π s ≠ ⊤ := measure_ne_top π
    -- restSet = cellSet regular ∪ (cellSet tail ∩ not ripe tail) ∪ (cellSet outer ∩ not ripe outer) ∪ (cellSet inner ∩ not ripe inner)
    have h_decomp : restSet π A m k dd DMv x =
        cellSet A m k dd DMv x Cell.regular ∪
        (cellSet A m k dd DMv x Cell.tail ∩ {θ | ¬ ripe π A m k dd DMv x Cell.tail}) ∪
        (cellSet A m k dd DMv x Cell.outer ∩ {θ | ¬ ripe π A m k dd DMv x Cell.outer}) ∪
        (cellSet A m k dd DMv x Cell.inner ∩ {θ | ¬ ripe π A m k dd DMv x Cell.inner}) := by
      ext θ; constructor
      · intro hθ
        rw [h_rest_eq, Set.mem_ofPred_eq] at hθ
        -- hθ : ¬ ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)
        -- Use match with equality to case split on cellOf
        match h_cell_val : cellOf A m k dd DMv x θ with
        | Cell.tail =>
          have h_cell : θ ∈ cellSet A m k dd DMv x Cell.tail := by
            simp [cellSet, h_cell_val]
          have h_not_ripe : ¬ ripe π A m k dd DMv x Cell.tail := by
            simpa [h_cell_val] using hθ
          simp [h_cell, h_not_ripe]
        | Cell.outer =>
          have h_cell : θ ∈ cellSet A m k dd DMv x Cell.outer := by
            simp [cellSet, h_cell_val]
          have h_not_ripe : ¬ ripe π A m k dd DMv x Cell.outer := by
            simpa [h_cell_val] using hθ
          simp [h_cell, h_not_ripe]
        | Cell.inner =>
          have h_cell : θ ∈ cellSet A m k dd DMv x Cell.inner := by
            simp [cellSet, h_cell_val]
          have h_not_ripe : ¬ ripe π A m k dd DMv x Cell.inner := by
            simpa [h_cell_val] using hθ
          simp [h_cell, h_not_ripe]
        | Cell.regular =>
          have h_cell : θ ∈ cellSet A m k dd DMv x Cell.regular := by
            simp [cellSet, h_cell_val]
          simp [h_cell]
      · intro hθ
        -- hθ : θ ∈ R ∪ T ∪ O ∪ I
        -- Break down the nested unions using cases
        rw [Set.mem_union, Set.mem_union, Set.mem_union] at hθ
        -- hθ : (((θ ∈ R ∨ θ ∈ T) ∨ θ ∈ O) ∨ θ ∈ I)
        cases hθ with
        | inl hθ =>
          cases hθ with
          | inl hθ =>
            cases hθ with
            | inl hθ =>
              -- θ ∈ cellSet regular
              rw [h_rest_eq, Set.mem_ofPred_eq]
              have h_cell_reg : cellOf A m k dd DMv x θ = Cell.regular := by
                simpa [cellSet] using hθ
              rw [h_cell_reg]
              simp [ripe]
            | inr hθ =>
              -- θ ∈ cellSet tail ∩ not ripe tail
              rw [Set.mem_inter_iff] at hθ
              rcases hθ with ⟨hθ_cell, hθ_ripe⟩
              rw [h_rest_eq, Set.mem_ofPred_eq]
              have h_cell_tail : cellOf A m k dd DMv x θ = Cell.tail := by
                simpa [cellSet] using hθ_cell
              rw [h_cell_tail]
              exact hθ_ripe
          | inr hθ =>
            -- θ ∈ cellSet outer ∩ not ripe outer
            rw [Set.mem_inter_iff] at hθ
            rcases hθ with ⟨hθ_cell, hθ_ripe⟩
            rw [h_rest_eq, Set.mem_ofPred_eq]
            have h_cell_outer : cellOf A m k dd DMv x θ = Cell.outer := by
              simpa [cellSet] using hθ_cell
            rw [h_cell_outer]
            exact hθ_ripe
        | inr hθ =>
          -- θ ∈ cellSet inner ∩ not ripe inner
          rw [Set.mem_inter_iff] at hθ
          rcases hθ with ⟨hθ_cell, hθ_ripe⟩
          rw [h_rest_eq, Set.mem_ofPred_eq]
          have h_cell_inner : cellOf A m k dd DMv x θ = Cell.inner := by
            simpa [cellSet] using hθ_cell
          rw [h_cell_inner]
          exact hθ_ripe
    -- Now bound the measure of the union
    have h_bound : π.real (cellSet A m k dd DMv x Cell.regular ∪
        (cellSet A m k dd DMv x Cell.tail ∩ {θ | ¬ ripe π A m k dd DMv x Cell.tail}) ∪
        (cellSet A m k dd DMv x Cell.outer ∩ {θ | ¬ ripe π A m k dd DMv x Cell.outer}) ∪
        (cellSet A m k dd DMv x Cell.inner ∩ {θ | ¬ ripe π A m k dd DMv x Cell.inner})) ≤
        π.real (cellSet A m k dd DMv x Cell.regular) + epsTail k dd + epsShell k dd + epsShell k dd := by
      -- First, get the conditional bounds
      have h_tail_cond_bound : π.real (cellSet A m k dd DMv x Cell.tail ∩
          {θ | ¬ ripe π A m k dd DMv x Cell.tail}) ≤ epsTail k dd := by
        by_cases h_ripe : ripe π A m k dd DMv x Cell.tail
        · have h_empty : cellSet A m k dd DMv x Cell.tail ∩ {θ | ¬ ripe π A m k dd DMv x Cell.tail} = ∅ := by
            ext θ; constructor
            · intro h; rcases h with ⟨hcell, hripe⟩; exact hripe h_ripe
            · intro h; exfalso; simp at h
          simp [h_empty]
          have h_nonneg : 0 ≤ epsTail k dd := by
            dsimp [epsTail]
            have hk' : 0 ≤ k := by linarith
            have hdd' : 0 ≤ dd := by
              have : 0 ≤ 2048 * k := by nlinarith
              linarith
            positivity
          exact h_nonneg
        · dsimp [ripe] at h_ripe
          -- h_ripe : ¬ (epsTail ≤ π.real ... ∨ epsMom ≤ ...)
          rcases (not_or.mp h_ripe) with ⟨h_le, _⟩
          have h_inter_eq : cellSet A m k dd DMv x Cell.tail ∩
              {θ | ¬ ripe π A m k dd DMv x Cell.tail} = cellSet A m k dd DMv x Cell.tail := by
            ext θ; constructor
            · intro h; exact h.1
            · intro h; refine ⟨h, ?_⟩; exact h_ripe
          rw [h_inter_eq]
          linarith
      have h_outer_cond_bound : π.real (cellSet A m k dd DMv x Cell.outer ∩
          {θ | ¬ ripe π A m k dd DMv x Cell.outer}) ≤ epsShell k dd := by
        by_cases h_ripe : ripe π A m k dd DMv x Cell.outer
        · have h_empty : cellSet A m k dd DMv x Cell.outer ∩ {θ | ¬ ripe π A m k dd DMv x Cell.outer} = ∅ := by
            ext θ; constructor
            · intro h; rcases h with ⟨hcell, hripe⟩; exact hripe h_ripe
            · intro h; exfalso; simp at h
          simp [h_empty]
          have h_nonneg : 0 ≤ epsShell k dd := by
            dsimp [epsShell]
            have hk' : 0 ≤ k := by linarith
            have hdd' : 0 ≤ dd := by
              have : 0 ≤ 2048 * k := by nlinarith
              linarith
            positivity
          exact h_nonneg
        · dsimp [ripe] at h_ripe
          -- h_ripe : ¬ (epsShell ≤ π.real ... ∨ ...)
          -- After dsimp, this is already simplified; h_ripe is the inequality we need
          have h_inter_eq : cellSet A m k dd DMv x Cell.outer ∩
              {θ | ¬ ripe π A m k dd DMv x Cell.outer} = cellSet A m k dd DMv x Cell.outer := by
            ext θ; constructor
            · intro h; exact h.1
            · intro h; refine ⟨h, ?_⟩; exact h_ripe
          rw [h_inter_eq]
          linarith
      have h_inner_cond_bound : π.real (cellSet A m k dd DMv x Cell.inner ∩
          {θ | ¬ ripe π A m k dd DMv x Cell.inner}) ≤ epsShell k dd := by
        by_cases h_ripe : ripe π A m k dd DMv x Cell.inner
        · have h_empty : cellSet A m k dd DMv x Cell.inner ∩ {θ | ¬ ripe π A m k dd DMv x Cell.inner} = ∅ := by
            ext θ; constructor
            · intro h; rcases h with ⟨hcell, hripe⟩; exact hripe h_ripe
            · intro h; exfalso; simp at h
          simp [h_empty]
          have h_nonneg : 0 ≤ epsShell k dd := by
            dsimp [epsShell]
            have hk' : 0 ≤ k := by linarith
            have hdd' : 0 ≤ dd := by
              have : 0 ≤ 2048 * k := by nlinarith
              linarith
            positivity
          exact h_nonneg
        · dsimp [ripe] at h_ripe
          have h_inter_eq : cellSet A m k dd DMv x Cell.inner ∩
              {θ | ¬ ripe π A m k dd DMv x Cell.inner} = cellSet A m k dd DMv x Cell.inner := by
            ext θ; constructor
            · intro h; exact h.1
            · intro h; refine ⟨h, ?_⟩; exact h_ripe
          rw [h_inter_eq]
          linarith
      -- Now combine using measureReal_union_le
      set R := cellSet A m k dd DMv x Cell.regular
      set T := cellSet A m k dd DMv x Cell.tail ∩ {θ | ¬ ripe π A m k dd DMv x Cell.tail}
      set O := cellSet A m k dd DMv x Cell.outer ∩ {θ | ¬ ripe π A m k dd DMv x Cell.outer}
      set I := cellSet A m k dd DMv x Cell.inner ∩ {θ | ¬ ripe π A m k dd DMv x Cell.inner}
      have h1 : π.real (R ∪ T ∪ O ∪ I) ≤ π.real (R ∪ T ∪ O) + π.real I := measureReal_union_le _ _
      have h2 : π.real (R ∪ T ∪ O) ≤ π.real (R ∪ T) + π.real O := measureReal_union_le _ _
      have h3 : π.real (R ∪ T) ≤ π.real R + π.real T := measureReal_union_le _ _
      have hsum : π.real (R ∪ T ∪ O) + π.real I ≤ π.real R + π.real T + π.real O + π.real I := by
        nlinarith
      have hfinal : π.real (R ∪ T) + π.real O + π.real I ≤ π.real R + epsTail k dd + epsShell k dd + epsShell k dd := by
        nlinarith
      nlinarith
    -- Now use h_decomp and h_bound to prove the goal
    rw [h_decomp]
    calc
      π.real (cellSet A m k dd DMv x Cell.regular ∪
          (cellSet A m k dd DMv x Cell.tail ∩ {θ | ¬ ripe π A m k dd DMv x Cell.tail}) ∪
          (cellSet A m k dd DMv x Cell.outer ∩ {θ | ¬ ripe π A m k dd DMv x Cell.outer}) ∪
          (cellSet A m k dd DMv x Cell.inner ∩ {θ | ¬ ripe π A m k dd DMv x Cell.inner})) -
          3 * k ^ 2 / dd ^ 2 ≤
          (π.real (cellSet A m k dd DMv x Cell.regular) + epsTail k dd + epsShell k dd + epsShell k dd) -
          3 * k ^ 2 / dd ^ 2 := by nlinarith
      _ = π.real (cellSet A m k dd DMv x Cell.regular) + (epsTail k dd + 2 * epsShell k dd) -
          3 * k ^ 2 / dd ^ 2 := by ring
      _ ≤ π.real (cellSet A m k dd DMv x Cell.regular) + 3 * k ^ 2 / dd ^ 2 - 3 * k ^ 2 / dd ^ 2 := by nlinarith
      _ = π.real (cellSet A m k dd DMv x Cell.regular) := by ring
      _ ≤ π.real (cellSet A m k dd DMv x Cell.regular) := le_rfl

/-- The rest lemma (i), the floor: `E[D; rest] ≥ π(regular) q(x)/2` on a live round. -/
theorem rest_floor {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (κ k dd DMv : ℝ) (hκ : 0 < κ)
    (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (x : V) :
    π.real (cellSet A m k dd DMv x Cell.regular) * (bowl A m κ k (5 * Real.sqrt dd) x / 2) ≤
      ∫ θ in restSet π A m k dd DMv x, dent A m κ k (5 * Real.sqrt dd) θ x ∂π := by
  set r₁ := 5 * Real.sqrt dd with hr₁_def
  set f := fun θ : V => dent A m κ k r₁ θ x with hf_def
  set q := bowl A m κ k r₁ x with hq_def
  set Reg := cellSet A m k dd DMv x Cell.regular with hReg_def
  set Rest := restSet π A m k dd DMv x with hRest_def
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ
  have hk_nonneg : 0 ≤ k := le_of_lt hk
  have hr₁_nonneg : 0 ≤ r₁ := by
    dsimp [r₁]
    have hsq : 0 ≤ Real.sqrt dd := Real.sqrt_nonneg _
    nlinarith
  have hε_nonneg : 0 ≤ k := hk_nonneg
  have hsub : Reg ⊆ Rest := by
    dsimp [Reg, Rest]
    exact regular_subset_restSet π A m k dd DMv x
  have hf_nonneg : ∀ θ, 0 ≤ f θ := by
    intro θ
    dsimp [f]
    exact dent_nonneg A m κ k r₁ hκ_nonneg hε_nonneg hr₁_nonneg θ x
  have hf_le_q : ∀ θ, f θ ≤ q := by
    intro θ
    dsimp [f, q]
    exact dent_le_bowl A m κ k r₁ hκ_nonneg hε_nonneg hr₁_nonneg θ x
  have hmeas_f : Measurable f := by
    dsimp [f]
    exact measurable_dent_tip A m κ k r₁ hκ_nonneg hε_nonneg hr₁_nonneg x
  have hmeas_Rest : MeasurableSet Rest := by
    dsimp [Rest]
    exact measurableSet_restSet π A m k dd DMv x
  have hmeas_Reg : MeasurableSet Reg := by
    dsimp [Reg]
    exact measurableSet_cellSet A m k dd DMv x Cell.regular
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, bowl]
    have hhuber : 0 ≤ huber r₁ k (‖A (x - m)‖) := by
      dsimp [huber]
      split
      · nlinarith
      · have hpos : 0 ≤ r₁ * ‖A (x - m)‖ - r₁ ^ 2 / 2 + k := by
          nlinarith
        nlinarith
    nlinarith
  have hhalf : ∀ θ ∈ Reg, q / 2 ≤ f θ := by
    intro θ hθ
    have hreg : cellOf A m k dd DMv x θ = Cell.regular := by
      dsimp [Reg] at hθ
      exact hθ
    rcases (cellOf_regular_iff A m k dd DMv x θ).mp hreg with ⟨hT, hR1, hR2⟩
    dsimp [f, q, r₁]
    exact regular_half A m κ k dd DMv hκ hk hd hDM θ x hT hR1 hR2
  have hfi_rest : IntegrableOn f Rest π := by
    have h_fin : π Rest ≠ ⊤ := measure_ne_top π Rest
    refine Measure.integrableOn_of_bounded (M := q) h_fin hmeas_f.aestronglyMeasurable ?_
    filter_upwards [ae_of_all _ hf_nonneg] with θ hθ
    have : ‖f θ‖ ≤ q := by
      rw [Real.norm_of_nonneg (hf_nonneg θ)]
      exact hf_le_q θ
    exact this
  have hfi_const : IntegrableOn (fun _ => q / 2) Reg π :=
    integrableOn_const (hs := measure_ne_top π Reg)
  have hfi_f : IntegrableOn f Reg π := by
    have h_fin : π Reg ≠ ⊤ := measure_ne_top π Reg
    refine Measure.integrableOn_of_bounded (M := q) h_fin hmeas_f.aestronglyMeasurable ?_
    filter_upwards [ae_of_all _ hf_nonneg] with θ hθ
    have : ‖f θ‖ ≤ q := by
      rw [Real.norm_of_nonneg (hf_nonneg θ)]
      exact hf_le_q θ
    exact this
  have h_nonneg_ae_rest : 0 ≤ᵐ[π.restrict Rest] f :=
    ae_of_all _ hf_nonneg
  have h_sub_ae : Reg ≤ᵐ[π] Rest := by
    have h_sdiff_empty : Reg \ Rest = ∅ := Set.sdiff_eq_empty.mpr hsub
    have h_measure_zero : π (Reg \ Rest) = 0 := by
      rw [h_sdiff_empty, measure_empty]
    exact (ae_le_set (μ := π) (s := Reg) (t := Rest)).mpr h_measure_zero
  calc
    π.real Reg * (q / 2) = (∫ θ in Reg, (q / 2) ∂π) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ ≤ ∫ θ in Reg, f θ ∂π := by
      refine MeasureTheory.setIntegral_mono_on hfi_const hfi_f hmeas_Reg (fun θ hθ => hhalf θ hθ)
    _ ≤ ∫ θ in Rest, f θ ∂π := by
      refine MeasureTheory.setIntegral_mono_set hfi_rest h_nonneg_ae_rest h_sub_ae

/-- The first moment of `T` on the tail: `E[T; tail] ≤ (π(tail) E[T²; tail])^{1/2}`. -/
theorem tail_first_moment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (x : V)
    (hT2 : IntegrableOn (fun θ => readT A m θ x ^ 2) (cellSet A m k dd DMv x Cell.tail) π) :
    ∫ θ in cellSet A m k dd DMv x Cell.tail, readT A m θ x ∂π ≤
      Real.sqrt (π.real (cellSet A m k dd DMv x Cell.tail) *
        ∫ θ in cellSet A m k dd DMv x Cell.tail, readT A m θ x ^ 2 ∂π) := by
  set s := cellSet A m k dd DMv x Cell.tail
  set I := ∫ θ in s, readT A m θ x ∂π with hI
  set Q := ∫ θ in s, readT A m θ x ^ 2 ∂π with hQ
  set p := π.real s with hp
  have hT2' : Integrable (fun θ => readT A m θ x ^ 2) (π.restrict s) := hT2
  have hTm : AEStronglyMeasurable (fun θ => readT A m θ x) (π.restrict s) :=
    (continuous_readT_tip A m x).aestronglyMeasurable
  have hTi : Integrable (fun θ => readT A m θ x) (π.restrict s) := by
    refine Integrable.mono' ((hT2'.div_const 2).add (integrable_const (1 / 2 : ℝ))) hTm
      (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs]
    have h1 := sq_nonneg (|readT A m θ x| - 1)
    have h2 := sq_abs (readT A m θ x)
    show |readT A m θ x| ≤ readT A m θ x ^ 2 / 2 + 1 / 2
    nlinarith
  have hbound : ∀ a : ℝ, 0 < a → I ≤ Q / (2 * a) + a / 2 * p := by
    intro a ha
    have h := integral_mono hTi ((hT2'.div_const (2 * a)).add (integrable_const (a / 2))) fun θ => by
      show readT A m θ x ≤ readT A m θ x ^ 2 / (2 * a) + a / 2
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (readT A m θ x - a)]
    simp only [Pi.add_apply] at h
    rw [integral_add (hT2'.div_const _) (integrable_const _), integral_div, setIntegral_const,
      smul_eq_mul] at h
    rw [hI, hQ, hp]
    linarith
  by_contra hcon
  push_neg at hcon
  have hI0 : 0 < I := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
  have hp0 : 0 < p := by
    rcases (measureReal_nonneg : 0 ≤ p).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : π s = 0 := (measureReal_eq_zero_iff (measure_ne_top π s)).1 h.symm
      have hr : π.restrict s = 0 := Measure.restrict_eq_zero.2 hz
      have : I = 0 := by rw [hI, hr, integral_zero_measure]
      linarith
  have h := hbound (I / p) (div_pos hI0 hp0)
  have e1 : Q / (2 * (I / p)) = Q * p / (2 * I) := by field_simp
  have e2 : I / p / 2 * p = I / 2 := by field_simp
  rw [e1, e2] at h
  have h3 : I / 2 ≤ Q * p / (2 * I) := by linarith
  rw [le_div_iff₀ (by positivity)] at h3
  have h4 : I ^ 2 ≤ p * Q := by nlinarith
  exact absurd ((Real.le_sqrt' hI0).2 h4) (not_le.2 hcon)

/-- The rest lemma (ii), the second moment of the gap on rest, on a live round:
`E[(q - D)²; rest] ≤ κ² (2^20 + 17) (k³/d²) φ(a)`. -/
theorem rest_second_moment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (κ k dd DMv : ℝ)
    (hκ : 0 < κ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (x : V)
    (hT2 : IntegrableOn (fun θ => readT A m θ x ^ 2) (cellSet A m k dd DMv x Cell.tail) π) :
    ∫ θ in restSet π A m k dd DMv x,
        (bowl A m κ k (5 * Real.sqrt dd) x - dent A m κ k (5 * Real.sqrt dd) θ x) ^ 2 ∂π ≤
      κ ^ 2 * ((2 ^ 20 + 17) * (k ^ 3 / dd ^ 2) * huber (5 * Real.sqrt dd) k ‖A (x - m)‖) := by
  classical
  have hk0 : 0 < k := by linarith
  have hdd : 0 < dd := by linarith
  have hsq : 0 < Real.sqrt dd := Real.sqrt_pos.2 hdd
  set r₁ := 5 * Real.sqrt dd with hr₁
  have hrpos : 0 < r₁ := by rw [hr₁]; positivity
  set q := bowl A m κ k r₁ x with hq
  set φ := huber r₁ k ‖A (x - m)‖ with hφ
  have hφk : k ≤ φ := huber_ge r₁ k _ hrpos.le
  set K := k ^ 3 / dd ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set G : V → ℝ := fun θ => (q - dent A m κ k r₁ θ x) ^ 2 with hG
  have hGm : Measurable G :=
    (measurable_const.sub (measurable_dent_tip A m κ k r₁ hκ.le hk0.le hrpos.le x)).pow_const 2
  have hG0 : ∀ θ, 0 ≤ G θ := fun θ => sq_nonneg _
  have hgap0 : ∀ θ, 0 ≤ q - dent A m κ k r₁ θ x := fun θ => gap_nonneg A m κ k r₁ hκ.le hk0.le hrpos.le θ x
  have hGle : ∀ θ, G θ ≤ (κ * φ) ^ 2 := fun θ =>
    pow_le_pow_left₀ (hgap0 θ) (gap_le_bowl A m κ k r₁ hκ.le hk0.le hrpos.le θ x) 2
  have hGint : ∀ s, IntegrableOn G s π := fun s =>
    (Integrable.of_bound hGm.aestronglyMeasurable ((κ * φ) ^ 2) (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 θ)]; exact hGle θ)).integrableOn
  -- the four pieces of rest
  set Rest := restSet π A m k dd DMv x with hRestdef
  have hRestm : MeasurableSet Rest := measurableSet_restSet π A m k dd DMv x
  set Cs : Cell → Set V := fun c => Rest ∩ cellSet A m k dd DMv x c with hCs
  have hCm : ∀ c, MeasurableSet (Cs c) := fun c => hRestm.inter (measurableSet_cellSet A m k dd DMv x c)
  have hcell : ∀ c θ, θ ∈ Cs c → cellOf A m k dd DMv x θ = c := fun c θ h => h.2
  have hdisj : ∀ (s : Set V) (c : Cell), (∀ θ ∈ s, cellOf A m k dd DMv x θ ≠ c) → Disjoint s (Cs c) :=
    fun s c h => Set.disjoint_left.2 fun θ h1 h2 => h θ h1 (hcell c θ h2)
  have hRest : Rest = Cs Cell.regular ∪ Cs Cell.tail ∪ Cs Cell.outer ∪ Cs Cell.inner := by
    ext θ
    simp only [hCs, Set.mem_union, Set.mem_inter_iff, cellSet, Set.mem_setOf_eq]
    cases cellOf A m k dd DMv x θ <;> simp
  have hsplit : ∫ θ in Rest, G θ ∂π = ∫ θ in Cs Cell.regular, G θ ∂π + ∫ θ in Cs Cell.tail, G θ ∂π +
      ∫ θ in Cs Cell.outer, G θ ∂π + ∫ θ in Cs Cell.inner, G θ ∂π := by
    rw [hRest, setIntegral_union _ (hCm _) (hGint _) (hGint _), setIntegral_union _ (hCm _) (hGint _) (hGint _),
      setIntegral_union _ (hCm _) (hGint _) (hGint _)]
    · exact hdisj _ _ fun θ h => by rw [hcell _ θ h]; decide
    · refine hdisj _ _ fun θ h => ?_
      rcases h with h | h <;> rw [hcell _ θ h] <;> decide
    · refine hdisj _ _ fun θ h => ?_
      rcases h with (h | h) | h <;> rw [hcell _ θ h] <;> decide
  -- membership in rest: the cell of the tip is not ripe
  have hnr : ∀ c θ, θ ∈ Cs c → ¬ ripe π A m k dd DMv x c := fun c θ h => by
    have h1 := h.1
    rw [hRestdef, restSet_eq] at h1
    rw [← hcell c θ h]; exact h1
  -- the regular piece
  have hreg : ∫ θ in Cs Cell.regular, G θ ∂π ≤ κ ^ 2 * (2 ^ 20 * K * φ) := by
    calc ∫ θ in Cs Cell.regular, G θ ∂π ≤ ∫ θ in Cs Cell.regular, κ ^ 2 * (2 ^ 20 * K * φ) ∂π := by
          refine setIntegral_mono_on (hGint _) (integrableOn_const) (hCm _) fun θ hθ => ?_
          obtain ⟨hT, hR1, hR2⟩ := (cellOf_regular_iff A m k dd DMv x θ).1 (hcell _ θ hθ)
          exact gap_sq_regular A m κ k dd DMv hκ hk0 hd hDM θ x hT hR1 hR2
      _ = π.real (Cs Cell.regular) * (κ ^ 2 * (2 ^ 20 * K * φ)) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * (κ ^ 2 * (2 ^ 20 * K * φ)) := by
          refine mul_le_mul_of_nonneg_right measureReal_le_one ?_
          have : 0 ≤ φ := by linarith
          positivity
      _ = _ := one_mul _
  -- the outer and inner pieces
  have hshell : ∀ c, c = Cell.outer ∨ c = Cell.inner →
      ∫ θ in Cs c, G θ ∂π ≤ epsShell k dd * (κ * (2 * k)) ^ 2 := by
    intro c hc
    have hmass : π.real (Cs c) ≤ epsShell k dd := by
      by_cases hr : ripe π A m k dd DMv x c
      · have : Cs c = ∅ := Set.eq_empty_of_forall_notMem fun θ hθ => hnr c θ hθ hr
        rw [this, measureReal_empty]; unfold epsShell; positivity
      · have hlt : π.real (cellSet A m k dd DMv x c) < epsShell k dd := by
          rcases hc with rfl | rfl <;> simpa [ripe] using hr
        exact (measureReal_mono Set.inter_subset_right).trans hlt.le
    calc ∫ θ in Cs c, G θ ∂π ≤ ∫ θ in Cs c, (κ * (2 * k)) ^ 2 ∂π := by
          refine setIntegral_mono_on (hGint _) (integrableOn_const) (hCm _) fun θ hθ => ?_
          have hne : cellOf A m k dd DMv x θ ≠ Cell.tail := by
            rw [hcell c θ hθ]; rcases hc with rfl | rfl <;> decide
          exact pow_le_pow_left₀ (hgap0 θ)
            (gap_nontail A m κ k r₁ hκ.le hk0.le hrpos θ x (readT_le_of_ne_tail A m k dd DMv x θ hne)) 2
      _ = π.real (Cs c) * (κ * (2 * k)) ^ 2 := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
  -- the tail piece
  have htail : ∫ θ in Cs Cell.tail, G θ ∂π ≤ κ ^ 2 * (9 * K * φ) := by
    by_cases hr : ripe π A m k dd DMv x Cell.tail
    · have : Cs Cell.tail = ∅ := Set.eq_empty_of_forall_notMem fun θ hθ => hnr _ θ hθ hr
      rw [this, setIntegral_empty]
      have : 0 ≤ φ := by linarith
      positivity
    · simp only [ripe, not_or, not_le] at hr
      obtain ⟨hmass, hmom⟩ := hr
      set Tl := cellSet A m k dd DMv x Cell.tail with hTl
      have hTlm : MeasurableSet Tl := measurableSet_cellSet A m k dd DMv x Cell.tail
      have hCT : Cs Cell.tail = Tl := by
        refine Set.Subset.antisymm Set.inter_subset_right fun θ hθ => ⟨?_, hθ⟩
        rw [hRestdef, restSet_eq]
        show ¬ ripe π A m k dd DMv x (cellOf A m k dd DMv x θ)
        rw [show cellOf A m k dd DMv x θ = Cell.tail from hθ]
        simp only [ripe, not_or, not_le]
        exact ⟨hmass, hmom⟩
      set T : V → ℝ := fun θ => readT A m θ x with hT
      have hTpos : ∀ θ ∈ Tl, 0 < T θ := fun θ hθ =>
        lt_of_le_of_lt (Real.sqrt_nonneg _) ((cellOf_tail_iff A m k dd DMv x θ).1 hθ)
      have hTint : IntegrableOn T Tl π := by
        refine Integrable.mono' (hT2.add (integrableOn_const (C := (1 : ℝ)))) ?_ ?_
        · exact (continuous_readT_tip A m x).measurable.aestronglyMeasurable
        · refine (ae_restrict_iff' hTlm).2 (ae_of_all _ fun θ hθ => ?_)
          rw [Real.norm_eq_abs, abs_of_pos (hTpos θ hθ)]
          simp only [Pi.add_apply, hT]
          nlinarith [sq_nonneg (readT A m θ x - 1)]
      have hM := tail_first_moment π A m k dd DMv x hT2
      rw [hCT]
      calc ∫ θ in Tl, G θ ∂π ≤ ∫ θ in Tl, κ ^ 2 * φ * (4 * T θ ^ 2 + r₁ * T θ) ∂π := by
            refine setIntegral_mono_on (hGint _) ?_ hTlm fun θ hθ => ?_
            · exact ((hT2.const_mul 4).add (hTint.const_mul r₁)).const_mul (κ ^ 2 * φ)
            · have := gap_sq_tail A m κ k r₁ hκ.le hk0 hrpos θ x ((cellOf_tail_iff A m k dd DMv x θ).1 hθ)
              simp only [hG, hT]
              nlinarith [this]
        _ = κ ^ 2 * φ * (4 * ∫ θ in Tl, T θ ^ 2 ∂π + r₁ * ∫ θ in Tl, T θ ∂π) := by
            rw [integral_const_mul, integral_add (hT2.const_mul 4) (hTint.const_mul r₁), integral_const_mul,
              integral_const_mul]
        _ ≤ κ ^ 2 * φ * (9 * K) := by
            refine mul_le_mul_of_nonneg_left ?_ (by have : 0 ≤ φ := (by linarith); positivity)
            refine rest_tail_arith k dd _ _ hk0 hdd hmom.le (hM.trans (Real.sqrt_le_sqrt ?_))
            have hS0 : 0 ≤ ∫ θ in Tl, T θ ^ 2 ∂π := setIntegral_nonneg hTlm fun θ _ => sq_nonneg _
            exact mul_le_mul hmass.le hmom.le hS0 (by unfold epsTail; positivity)
        _ = κ ^ 2 * (9 * K * φ) := by ring
  -- the total
  have hsh := rest_shell_arith k dd φ hk0 hdd hφk
  have ho := hshell Cell.outer (Or.inl rfl)
  have hi := hshell Cell.inner (Or.inr rfl)
  show ∫ θ in Rest, G θ ∂π ≤ _
  rw [hsplit]
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have : epsShell k dd * (κ * (2 * k)) ^ 2 * 2 = κ ^ 2 * (2 * epsShell k dd * (4 * k ^ 2)) := by ring
  nlinarith [mul_le_mul_of_nonneg_left hsh hκ2]

/-! ## Lemma LEAK, the ratios -/

/-- `p ln(1/p) ≤ 1 - p` on `[0, 1]`. -/
theorem plog_le_one_sub (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : p * Real.log (1 / p) ≤ 1 - p := by
  by_cases hp : p = 0
  · -- p = 0 case
    subst hp
    simp
  · -- p > 0 case
    have hpos : 0 < p := lt_of_le_of_ne h0 (fun h => hp (h.symm))
    have hpos_inv : 0 < 1 / p := div_pos (by norm_num) hpos
    have hlog : Real.log (1 / p) ≤ (1 / p) - 1 := Real.log_le_sub_one_of_pos hpos_inv
    calc
      p * Real.log (1 / p) ≤ p * ((1 / p) - 1) := mul_le_mul_of_nonneg_left hlog h0
      _ = p * (1 / p) - p := by ring
      _ = 1 - p := by
        field_simp [hp]
    -- alternative: rw [mul_sub, mul_one_div_cancel hp, sub_sub_cancel]

/-- `p (ln(1/p) + 1)` is nondecreasing on `[0, 1]`. -/
theorem plog_mono (p q : ℝ) (h0 : 0 ≤ p) (hpq : p ≤ q) (h1 : q ≤ 1) :
    p * (Real.log (1 / p) + 1) ≤ q * (Real.log (1 / q) + 1) := by
  have hq_nonneg : 0 ≤ q := h0.trans hpq
  -- simplify: Real.log (1 / x) = -Real.log x for x ≠ 0, and Real.log (1/0) = Real.log 0 = 0 = -Real.log 0
  -- We handle p=0 separately because log_div needs nonzero denominators
  by_cases hpz : p = 0
  · rw [hpz]
    by_cases hqz : q = 0
    · subst hqz; simp
    · have hqpos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hqz)
      have hlog_nonpos : Real.log q ≤ 0 := Real.log_nonpos hq_nonneg h1
      simp
      have hpos : 0 ≤ -Real.log q + 1 := by linarith
      exact mul_nonneg hq_nonneg hpos
  · have hppos : 0 < p := lt_of_le_of_ne h0 (Ne.symm hpz)
    have hqpos : 0 < q := lt_of_lt_of_le hppos hpq
    have hlog_nonpos : Real.log q ≤ 0 := Real.log_nonpos hq_nonneg h1
    -- key inequality: p*log p - q*log q ≥ -(q-p)*(1+log q)
    have hkey : p * Real.log p - q * Real.log q ≥ -(q - p) * (1 + Real.log q) := by
      -- from Real.one_sub_inv_le_log_of_pos at x = p/q: 1 - q/p ≤ log p - log q
      have hdivpos : 0 < p / q := div_pos hppos hqpos
      have hineq : 1 - ((p / q)⁻¹) ≤ Real.log (p / q) :=
        Real.one_sub_inv_le_log_of_pos hdivpos
      have hlog_div : Real.log (p / q) = Real.log p - Real.log q :=
        Real.log_div hppos.ne.symm hqpos.ne.symm
      rw [hlog_div] at hineq
      have hinv_eq : (p / q)⁻¹ = q / p := by field_simp
      rw [hinv_eq] at hineq
      -- hineq : 1 - q/p ≤ log p - log q
      have h_mul : p - q ≤ p * (Real.log p - Real.log q) := by
        have htemp := mul_le_mul_of_nonneg_left hineq (by linarith : 0 ≤ p)
        have hleft : p * (1 - q / p) = p - q := by field_simp [hppos.ne.symm]
        rw [hleft] at htemp
        exact htemp
      calc
        p * Real.log p - q * Real.log q = p * (Real.log p - Real.log q) + (p - q) * Real.log q := by ring
        _ ≥ (p - q) + (p - q) * Real.log q := by linarith
        _ = (p - q) * (1 + Real.log q) := by ring
        _ = -(q - p) * (1 + Real.log q) := by ring
    -- now use hkey to prove the goal
    have hlog_p : Real.log (1 / p) = -Real.log p := by
      rw [one_div, Real.log_inv]
    have hlog_q : Real.log (1 / q) = -Real.log q := by
      rw [one_div, Real.log_inv]
    rw [hlog_p, hlog_q]
    -- goal: p * (-Real.log p + 1) ≤ q * (-Real.log q + 1)
    -- i.e., p - p*log p ≤ q - q*log q  ↔  p - q ≤ p*log p - q*log q
    have h_sub_nonpos : p - q ≤ 0 := sub_nonpos.mpr hpq
    have h_prod_nonneg : 0 ≤ (p - q) * Real.log q :=
      mul_nonneg_of_nonpos_of_nonpos h_sub_nonpos hlog_nonpos
    -- from hkey: p*log p - q*log q ≥ -(q-p)*(1+log q) = (p-q)*(1+log q) = (p-q) + (p-q)*log q
    have hkey' : p * Real.log p - q * Real.log q ≥ (p - q) + (p - q) * Real.log q := by
      have h_eq : -(q - p) * (1 + Real.log q) = (p - q) + (p - q) * Real.log q := by ring
      rw [h_eq] at hkey
      exact hkey
    -- since (p-q)*log q ≥ 0, we have p-q ≤ (p-q) + (p-q)*log q ≤ p*log p - q*log q
    have h_ineq : p - q ≤ p * Real.log p - q * Real.log q :=
      le_trans (by
        have : (p - q) + (p - q) * Real.log q - (p - q) = (p - q) * Real.log q := by ring
        have h_nonneg : 0 ≤ (p - q) + (p - q) * Real.log q - (p - q) := by
          rw [this]; exact h_prod_nonneg
        linarith) hkey'
    -- rearrange: p - q ≤ p*log p - q*log q  ↔  p - p*log p ≤ q - q*log q
    linarith

/-- The entropy of the answer: with the masses `p i` of the ripe cells (`i ∈ s`) and the rest
`1 - Σ p i ≥ 0`, `H ≤ Σ_{ripe} p (ln(1/p) + 1)`. -/
theorem entropy_le_ripe {ι : Type*} (s : Finset ι) (p : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∑ i ∈ s, p i ≤ 1) :
    ∑ i ∈ s, p i * Real.log (1 / p i) + (1 - ∑ i ∈ s, p i) * Real.log (1 / (1 - ∑ i ∈ s, p i)) ≤
      ∑ i ∈ s, p i * (Real.log (1 / p i) + 1) := by
  set r := 1 - ∑ i ∈ s, p i with hr
  have hr0 : 0 ≤ r := by
    linarith
  have hr1 : r ≤ 1 := by
    have hsum0 : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg h0
    linarith
  calc
    ∑ i ∈ s, p i * Real.log (1 / p i) + (1 - ∑ i ∈ s, p i) * Real.log (1 / (1 - ∑ i ∈ s, p i))
        = ∑ i ∈ s, p i * Real.log (1 / p i) + r * Real.log (1 / r) := by
      simp [r]
    _ ≤ ∑ i ∈ s, p i * Real.log (1 / p i) + (1 - r) := by
      have h := plog_le_one_sub r hr0 hr1
      linarith
    _ = ∑ i ∈ s, p i * Real.log (1 / p i) + ∑ i ∈ s, p i := by
      dsimp [r]
      ring
    _ = ∑ i ∈ s, (p i * Real.log (1 / p i) + p i) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ s, p i * (Real.log (1 / p i) + 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      ring

/-- Lemma LEAK, a tail ripe by its mass, against its ledger term `P ≥ p k/4`. -/
theorem leak_tail_mass (k dd p P : ℝ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hp : epsTail k dd ≤ p) (hp1 : p ≤ 1)
    (hP : p * k / 4 ≤ P) :
    p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P ∧ p ≤ 4 / k * P := by
  have hkpos : 0 < k := by linarith
  have hddpos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    nlinarith
  have hlog_dd_nonneg : 0 ≤ Real.log dd := by
    have : 1 ≤ dd := by nlinarith
    exact Real.log_nonneg this
  have hp_pos : 0 < p := by
    have : 0 < epsTail k dd := by
      dsimp [epsTail]
      positivity
    nlinarith
  have hp_nonneg : 0 ≤ p := by linarith
  have h_one_div_p_pos : 0 < 1 / p := div_pos (by norm_num) hp_pos
  have h_log_bound : Real.log (1 / p) ≤ 3 * Real.log dd := by
    dsimp [epsTail] at hp
    have hpos_k3_dd3 : 0 < k ^ 3 / dd ^ 3 := by positivity
    have h_one_div : 1 / p ≤ dd ^ 3 / k ^ 3 := by
      calc
        1 / p ≤ 1 / (k ^ 3 / dd ^ 3) :=
          (one_div_le_one_div hp_pos hpos_k3_dd3).mpr hp
        _ = dd ^ 3 / k ^ 3 := by field_simp
    calc
      Real.log (1 / p) ≤ Real.log (dd ^ 3 / k ^ 3) :=
        Real.log_le_log (by positivity) h_one_div
      _ = Real.log (dd ^ 3) - Real.log (k ^ 3) := Real.log_div (by positivity) (by positivity)
      _ = 3 * Real.log dd - 3 * Real.log k := by simp [Real.log_pow]
      _ ≤ 3 * Real.log dd := by
        have hlogk_nonneg : 0 ≤ Real.log k := Real.log_nonneg hk
        nlinarith
  have h_factor_nonneg : 0 ≤ 4 * (3 * Real.log dd + 1) / k :=
    div_nonneg (by
      have : 0 ≤ 3 * Real.log dd := by nlinarith
      nlinarith) (by linarith)
  have h_first : p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P := by
    calc
      p * (Real.log (1 / p) + 1) ≤ p * (3 * Real.log dd + 1) := by nlinarith
      _ = (4 * (3 * Real.log dd + 1) / k) * (p * k / 4) := by
        field_simp [hkpos.ne.symm]
      _ ≤ (4 * (3 * Real.log dd + 1) / k) * P :=
        mul_le_mul_of_nonneg_left hP h_factor_nonneg
  have h_second : p ≤ 4 / k * P := by
    have h_nonneg : 0 ≤ 4 / k := div_nonneg (by norm_num) (by linarith)
    calc
      p = (4 / k) * (p * k / 4) := by
        field_simp [hkpos.ne.symm]
      _ ≤ (4 / k) * P := mul_le_mul_of_nonneg_left hP h_nonneg
  exact And.intro h_first h_second

/-- Lemma LEAK, a tail ripe by its second moment `S = E[T²; tail]`, against its ledger term `P ≥ S/8`. -/
theorem leak_tail_moment (k dd p S P : ℝ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hp0 : 0 ≤ p)
    (hp : p < epsTail k dd) (hS : epsMom k dd ≤ S) (hP : S / 8 ≤ P) :
    p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P ∧ p ≤ 4 / k * P := by
  have hkpos : 0 < k := by linarith
  have hddpos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    linarith
  have hk_le_dd : k ≤ dd := by
    nlinarith
  have h_epsTail_eq : epsTail k dd = epsMom k dd / dd := by
    unfold epsTail epsMom
    field_simp [ne_of_gt hddpos]
  have h_epsTail_le_one : epsTail k dd ≤ 1 := by
    unfold epsTail
    have hk_nonneg : 0 ≤ k := by linarith
    have hdd_nonneg : 0 ≤ dd := by linarith
    have hk3_le_dd3 : k ^ 3 ≤ dd ^ 3 := by
      have h_sq : k * k ≤ dd * dd := mul_le_mul hk_le_dd hk_le_dd hk_nonneg hdd_nonneg
      have h_dd_sq_nonneg : 0 ≤ dd * dd := mul_nonneg hdd_nonneg hdd_nonneg
      have h_cube : (k * k) * k ≤ (dd * dd) * dd :=
        mul_le_mul h_sq hk_le_dd hk_nonneg h_dd_sq_nonneg
      calc
        k ^ 3 = (k * k) * k := by ring
        _ ≤ (dd * dd) * dd := h_cube
        _ = dd ^ 3 := by ring
    exact (div_le_one (by positivity)).mpr hk3_le_dd3
  have hp_le_epsTail : p ≤ epsTail k dd := by linarith
  have hp_le_one : p ≤ 1 := by linarith
  have h_two_k_le_dd : 2 * k ≤ dd := by
    nlinarith
  have hPpos : 0 < P := by
    have hepsMom_pos : 0 < epsMom k dd := by
      unfold epsMom
      positivity
    have hSpos : 0 < S := by linarith
    linarith
  have h_log_dd_nonneg : 0 ≤ Real.log dd := Real.log_nonneg (by linarith)
  have h_log_term_nonneg : 0 ≤ 3 * Real.log dd + 1 := by nlinarith
  have h_mass : p ≤ 4 / k * P := by
    have h_lt : p < 4 / k * P := by
      calc
        p < epsTail k dd := hp
        _ = epsMom k dd / dd := h_epsTail_eq
        _ ≤ S / dd := div_le_div_of_nonneg_right hS (by linarith)
        _ ≤ (8 * P) / dd := by
          have hS_le_8P : S ≤ 8 * P := by linarith
          exact div_le_div_of_nonneg_right hS_le_8P (by linarith)
        _ = (8 / dd) * P := by ring
        _ ≤ (4 / k) * P := by
          have h_div : 8 / dd ≤ 4 / k := by
            apply (div_le_div_iff₀ hddpos hkpos).mpr
            nlinarith
          nlinarith
        _ = 4 / k * P := by ring
    exact le_of_lt h_lt
  have h_entropy : p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P := by
    have h_plog : p * (Real.log (1 / p) + 1) ≤ epsTail k dd * (Real.log (1 / epsTail k dd) + 1) :=
      plog_mono p (epsTail k dd) hp0 hp_le_epsTail h_epsTail_le_one
    have h_log_bound : Real.log (1 / epsTail k dd) ≤ 3 * Real.log dd := by
      have h_eq : 1 / epsTail k dd = (dd ^ 3) / (k ^ 3) := by
        unfold epsTail
        field_simp [ne_of_gt hkpos, ne_of_gt hddpos]
      rw [h_eq]
      rw [Real.log_div (by positivity : dd ^ 3 ≠ 0) (by positivity : k ^ 3 ≠ 0)]
      rw [Real.log_pow, Real.log_pow]
      have h_log_k_nonneg : 0 ≤ Real.log k := Real.log_nonneg hk
      have : (3 : ℝ) * Real.log dd - (3 : ℝ) * Real.log k ≤ 3 * Real.log dd := by linarith
      exact this
    calc
      p * (Real.log (1 / p) + 1) ≤ epsTail k dd * (Real.log (1 / epsTail k dd) + 1) := h_plog
      _ ≤ epsTail k dd * (3 * Real.log dd + 1) := by
        nlinarith
      _ = (epsTail k dd) * (3 * Real.log dd + 1) := rfl
      _ = (epsMom k dd / dd) * (3 * Real.log dd + 1) := by rw [h_epsTail_eq]
      _ ≤ (S / dd) * (3 * Real.log dd + 1) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hS (by linarith)) h_log_term_nonneg
      _ ≤ ((8 * P) / dd) * (3 * Real.log dd + 1) := by
        have hS_le_8P : S ≤ 8 * P := by linarith
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hS_le_8P (by linarith)) h_log_term_nonneg
      _ = (8 / dd) * P * (3 * Real.log dd + 1) := by ring
      _ = (8 * P * (3 * Real.log dd + 1)) / dd := by ring
      _ ≤ (4 * P * (3 * Real.log dd + 1)) / k := by
        have hPX_nonneg : 0 ≤ P * (3 * Real.log dd + 1) :=
          mul_nonneg (by linarith) h_log_term_nonneg
        have h_div : 8 / dd ≤ 4 / k := by
          apply (div_le_div_iff₀ hddpos hkpos).mpr
          nlinarith
        calc
          (8 * P * (3 * Real.log dd + 1)) / dd = (8 / dd) * (P * (3 * Real.log dd + 1)) := by ring
          _ ≤ (4 / k) * (P * (3 * Real.log dd + 1)) :=
            mul_le_mul_of_nonneg_right h_div hPX_nonneg
          _ = (4 * P * (3 * Real.log dd + 1)) / k := by ring
      _ = (4 / k) * P * (3 * Real.log dd + 1) := by ring
      _ = 4 * (3 * Real.log dd + 1) / k * P := by ring
  exact And.intro h_entropy h_mass

/-- Lemma LEAK, an inner or outer cell ripe by its mass, against its ledger term `P ≥ p d/62`. -/
theorem leak_shell (k dd p P : ℝ) (hk : 1 ≤ k) (hd : 2048 * k ≤ dd) (hp : epsShell k dd ≤ p) (hp1 : p ≤ 1)
    (hP : p * dd / 62 ≤ P) :
    p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P ∧ p ≤ 4 / k * P := by
  have hkpos : 0 < k := by linarith
  have hddpos : 0 < dd := by
    have : 0 < 2048 * k := by nlinarith
    linarith
  have hdd_sq_pos : 0 < dd ^ 2 := by nlinarith
  have hk_sq_pos : 0 < k ^ 2 := by nlinarith
  have hepspos : 0 < epsShell k dd := by
    dsimp [epsShell]
    positivity
  have hppos : 0 < p := by linarith
  have hPpos : 0 ≤ P := by
    have : 0 ≤ p * dd / 62 := by
      apply div_nonneg
      · nlinarith
      · norm_num
    linarith
  have hL_nonneg : 0 ≤ Real.log dd := by
    have hdd_one : 1 ≤ dd := by
      have : 1 ≤ 2048 * 1 := by norm_num
      linarith
    exact Real.log_nonneg hdd_one
  have h_log_bound : Real.log (1 / p) ≤ 2 * Real.log dd := by
    have h_one_div_p_pos : 0 < 1 / p := div_pos (by norm_num) hppos
    have h_dd_sq_div_k_sq_pos : 0 < dd ^ 2 / k ^ 2 := div_pos hdd_sq_pos hk_sq_pos
    have h_ineq : 1 / p ≤ dd ^ 2 / k ^ 2 := by
      dsimp [epsShell] at hp
      -- hp: k^2 / dd^2 ≤ p
      -- Goal: 1/p ≤ dd^2/k^2, equivalent to k^2 ≤ p * dd^2
      have h_mul : k ^ 2 ≤ p * dd ^ 2 := (div_le_iff₀ hdd_sq_pos).mp hp
      apply (div_le_div_iff₀ hppos hk_sq_pos).2
      -- Goal: 1 * k^2 ≤ dd^2 * p, i.e., k^2 ≤ p * dd^2
      simpa [mul_comm] using h_mul
    have h_log_ineq : Real.log (1 / p) ≤ Real.log (dd ^ 2 / k ^ 2) :=
      Real.log_le_log h_one_div_p_pos h_ineq
    have h_log_div : Real.log (dd ^ 2 / k ^ 2) = Real.log (dd ^ 2) - Real.log (k ^ 2) :=
      Real.log_div (by nlinarith) (by nlinarith)
    have h_log_pow_dd : Real.log (dd ^ 2) = 2 * Real.log dd := by
      simpa using Real.log_pow dd 2
    have h_log_pow_k : Real.log (k ^ 2) = 2 * Real.log k := by
      simpa using Real.log_pow k 2
    have h_log_k_nonneg : 0 ≤ Real.log k := Real.log_nonneg hk
    rw [h_log_div, h_log_pow_dd, h_log_pow_k] at h_log_ineq
    have h_sub_le : 2 * Real.log dd - 2 * Real.log k ≤ 2 * Real.log dd := by nlinarith
    linarith
  have h_first : p * (Real.log (1 / p) + 1) ≤ 4 * (3 * Real.log dd + 1) / k * P := by
    have h_key : 62 * (2 * Real.log dd + 1) / dd ≤ 4 * (3 * Real.log dd + 1) / k := by
      apply (div_le_div_iff₀ hddpos hkpos).2
      nlinarith
    have h_nonneg_coeff : 0 ≤ 62 * (2 * Real.log dd + 1) / dd := by
      apply div_nonneg
      · nlinarith
      · linarith
    calc
      p * (Real.log (1 / p) + 1) ≤ p * (2 * Real.log dd + 1) := by
        nlinarith
      _ = (62 * (2 * Real.log dd + 1) / dd) * (p * dd / 62) := by
        field_simp [hddpos.ne.symm]
      _ ≤ (62 * (2 * Real.log dd + 1) / dd) * P :=
        mul_le_mul_of_nonneg_left hP h_nonneg_coeff
      _ ≤ (4 * (3 * Real.log dd + 1) / k) * P :=
        mul_le_mul_of_nonneg_right h_key hPpos
  have h_second : p ≤ 4 / k * P := by
    have h_ineq : 62 / dd ≤ 4 / k := by
      apply (div_le_div_iff₀ hddpos hkpos).2
      nlinarith
    calc
      p = (62 / dd) * (p * dd / 62) := by
        field_simp [hddpos.ne.symm]
      _ ≤ (62 / dd) * P :=
        mul_le_mul_of_nonneg_left hP (by
          apply div_nonneg; norm_num; linarith)
      _ ≤ (4 / k) * P :=
        mul_le_mul_of_nonneg_right h_ineq hPpos
  exact And.intro h_first h_second

/-- The floor of a round (the balance proposition, "the floor"): `E_π[D(x; θ)] ≥ π(regular) g/2` with `g = κ k`, on a
live
round. -/
theorem floor_round {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (π : Measure V) [IsFiniteMeasure π] (A : V →L[ℝ] V) (m : V) (κ k dd DMv : ℝ) (hκ : 0 < κ)
    (hk : 0 < k) (hd : 2048 * k ≤ dd) (hDM : dd / 2 ≤ DMv) (x : V) :
    π.real (cellSet A m k dd DMv x Cell.regular) * (κ * k / 2) ≤
      ∫ θ, dent A m κ k (5 * Real.sqrt dd) θ x ∂π := by
  have hr : 0 ≤ 5 * Real.sqrt dd := by positivity
  set f := fun θ => dent A m κ k (5 * Real.sqrt dd) θ x with hf
  have hfm : Measurable f := measurable_dent_tip A m κ k _ hκ.le hk.le hr x
  have hf0 : ∀ θ, 0 ≤ f θ := fun θ => dent_nonneg A m κ k _ hκ.le hk.le hr θ x
  have hfint : Integrable f π := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (bowl A m κ k (5 * Real.sqrt dd) x)
      (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 θ)]
    exact dent_le_bowl A m κ k _ hκ.le hk.le hr θ x
  have hReg := measurableSet_cellSet A m k dd DMv x Cell.regular
  have hq : κ * k ≤ bowl A m κ k (5 * Real.sqrt dd) x := bowl_ge A m κ k _ hκ.le hr x
  calc π.real (cellSet A m k dd DMv x Cell.regular) * (κ * k / 2)
      = ∫ _ in cellSet A m k dd DMv x Cell.regular, κ * k / 2 ∂π := by
        rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ θ in cellSet A m k dd DMv x Cell.regular, f θ ∂π := by
        refine setIntegral_mono_on integrableOn_const hfint.integrableOn hReg fun θ hθ => ?_
        obtain ⟨hT, hR1, hR2⟩ := (cellOf_regular_iff A m k dd DMv x θ).1 hθ
        have := regular_half A m κ k dd DMv hκ hk hd hDM θ x hT hR1 hR2
        simp only [hf]
        linarith
    _ ≤ ∫ θ, f θ ∂π := setIntegral_le_integral hfint (ae_of_all _ hf0)

/-- Lemma LEAK for one ripe cell, against its ledger term `P` (the bounds (L3) to (L5) of the ledger lemma as
hypotheses): `p (ln(1/p) + 1) ≤ (4 (3 ln d + 1)/k) P` and `p ≤ (4/k) P`, `p` the mass of the cell. -/
theorem leak_cell {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (π : Measure V) [IsProbabilityMeasure π] (A : V →L[ℝ] V) (m : V) (k dd DMv : ℝ) (hk : 1 ≤ k)
    (hd : 2048 * k ≤ dd) (x : V) (c : Cell) (hc : ripe π A m k dd DMv x c) (P : ℝ)
    (hPt : c = Cell.tail → π.real (cellSet A m k dd DMv x Cell.tail) * k / 4 ≤ P ∧
      (∫ θ in cellSet A m k dd DMv x Cell.tail, readT A m θ x ^ 2 ∂π) / 8 ≤ P)
    (hPs : c = Cell.outer ∨ c = Cell.inner → π.real (cellSet A m k dd DMv x c) * dd / 62 ≤ P) :
    π.real (cellSet A m k dd DMv x c) * (Real.log (1 / π.real (cellSet A m k dd DMv x c)) + 1) ≤
        4 * (3 * Real.log dd + 1) / k * P ∧
      π.real (cellSet A m k dd DMv x c) ≤ 4 / k * P := by
  have h1 : π.real (cellSet A m k dd DMv x c) ≤ 1 := measureReal_le_one
  have h0 : 0 ≤ π.real (cellSet A m k dd DMv x c) := measureReal_nonneg
  cases c with
  | tail =>
    obtain ⟨hPm, hPS⟩ := hPt rfl
    rcases hc with hm | hS
    · exact leak_tail_mass k dd _ P hk hd hm h1 hPm
    · by_cases hm : epsTail k dd ≤ π.real (cellSet A m k dd DMv x Cell.tail)
      · exact leak_tail_mass k dd _ P hk hd hm h1 hPm
      · exact leak_tail_moment k dd _ _ P hk hd h0 (not_le.1 hm) hS hPS
  | outer => exact leak_shell k dd _ P hk hd hc h1 (hPs (Or.inl rfl))
  | inner => exact leak_shell k dd _ P hk hd hc h1 (hPs (Or.inr rfl))
  | regular => exact hc.elim

end AdversarialBco.Lower
