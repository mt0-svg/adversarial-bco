/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# The dent: Lemma D

The dent is the lower convex hull of a bowl `q` and of the point `(θ, 0)`. Everything here is on a real inner product
space `V` (the game uses `V = ℝ^d`); the metric of the section on the lower bound, `|v|_M = (vᵀ M v)^{1/2}`, is `‖A v‖`
for the square root
`A = M^{1/2}` (`AdversarialBco.Lower.frameA` in Frame.lean), and `⟨u, v⟩_M = ⟪A u, A v⟫`.

* `hull q θ x = inf_{λ ∈ (0, 1]} λ q(θ + (x - θ)/λ)`: for `q ≥ 0` this is the
  `inf {λ q(y) : λ ∈ [0, 1], x = θ + λ (y - θ)}` (at `x = θ` both are `0`).
* `huber r₁ ε`: the profile `φ`; `bowl A m κ ε r₁ x = κ φ(|x - m|_M)`; `dent = hull ∘ bowl`.
* `hq`, `rho`, `devq`, `readT`, `hgen`: the `h`, `ρ`, `dev`, `T`, `hgen` of the section on the lower bound.

Statements: Lemma D (a) `dent_convexOn`, `dent_nonneg`, `dent_le_bowl`, `dent_self`; (b) `dent_lipschitz`;
(c) `dent_closed_form`, `devq_bounds`, `dent_closed_form_bound`; (d) `dent_tangent`; (d1) `hgen_le_two_k`;
(d2) `hgen_tail`; the infimum over rational `λ` (`dent_eq_iInf_rat`, for the measurability lemma of the lower bound).
-/

open scoped RealInnerProductSpace

namespace AdversarialBco.Lower

/-! ## Definitions -/

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Huber profile of the bowl: `φ(r) = r²/2 + ε` for `r ≤ r₁`, `φ(r) = r₁ r - r₁²/2 + ε` for `r > r₁`. -/
noncomputable def huber (r₁ ε r : ℝ) : ℝ :=
  if r ≤ r₁ then r ^ 2 / 2 + ε else r₁ * r - r₁ ^ 2 / 2 + ε

/-- The lower convex hull of `q` and of the point `(θ, 0)`, read at `x`. -/
noncomputable def hull (q : V → ℝ) (θ x : V) : ℝ :=
  ⨅ l : Set.Ioc (0 : ℝ) 1, (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ))

/-- The bowl `q(x) = κ φ(|x - m|_M)`, with `|v|_M = ‖A v‖`. -/
noncomputable def bowl (A : V →L[ℝ] V) (m : V) (κ ε r₁ : ℝ) (x : V) : ℝ :=
  κ * huber r₁ ε ‖A (x - m)‖

/-- The dent of tip `θ`: the lower hull of the bowl and of `(θ, 0)`. -/
noncomputable def dent (A : V →L[ℝ] V) (m : V) (κ ε r₁ : ℝ) (θ x : V) : ℝ :=
  hull (bowl A m κ ε r₁) θ x

/-- `h(x, θ) = ⟨x - m, θ - m⟩_M - |x - m|_M²/2 + ε`. -/
noncomputable def hq (A : V →L[ℝ] V) (m : V) (ε : ℝ) (θ x : V) : ℝ :=
  ⟪A (x - m), A (θ - m)⟫ - ‖A (x - m)‖ ^ 2 / 2 + ε

/-- `ρ(θ) = (|θ - m|_M² + 2ε)^{1/2}`. -/
noncomputable def rho (A : V →L[ℝ] V) (m : V) (ε : ℝ) (θ : V) : ℝ :=
  Real.sqrt (‖A (θ - m)‖ ^ 2 + 2 * ε)

/-- `dev = ρ² - h - ρ (ρ² - 2h)^{1/2}`. -/
noncomputable def devq (ρ h : ℝ) : ℝ :=
  ρ ^ 2 - h - ρ * Real.sqrt (ρ ^ 2 - 2 * h)

/-- The read `T = ⟨x - m, θ - m⟩_M / |x - m|_M` (`0` where `|x - m|_M = 0`). -/
noncomputable def readT (A : V →L[ℝ] V) (m θ x : V) : ℝ :=
  ⟪A (x - m), A (θ - m)⟫ / ‖A (x - m)‖

/-- The tangent plane of the bowl at `x`, read at `θ`, divided by `κ`: `h` for `|x - m|_M ≤ r₁`,
`r₁ T - r₁²/2 + ε` beyond. -/
noncomputable def hgen (A : V →L[ℝ] V) (m : V) (ε r₁ : ℝ) (θ x : V) : ℝ :=
  if ‖A (x - m)‖ ≤ r₁ then hq A m ε θ x else r₁ * readT A m θ x - r₁ ^ 2 / 2 + ε

/-- The slope factor of the bowl's gradient at `x`: the gradient is `κ c A*A (x - m)`. -/
noncomputable def slope (A : V →L[ℝ] V) (m : V) (r₁ : ℝ) (x : V) : ℝ :=
  if ‖A (x - m)‖ ≤ r₁ then 1 else r₁ / ‖A (x - m)‖

end Defs

/-! ## The hull of a nonnegative function -/

theorem hull_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ x : V)
    (h0 : ∀ y, 0 ≤ q y) : 0 ≤ hull q θ x := by
  unfold hull
  refine le_ciInf ?_
  intro l
  have hl : (0 : ℝ) ≤ (l : ℝ) := l.property.1.le
  have hq : 0 ≤ q (θ + (l : ℝ)⁻¹ • (x - θ)) := h0 _
  exact mul_nonneg hl hq

theorem hull_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ x : V)
    (h0 : ∀ y, 0 ≤ q y) : hull q θ x ≤ q x := by
  have h_bdd : BddBelow (Set.range (λ (l : Set.Ioc (0 : ℝ) 1) => (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨l, rfl⟩
    have hlpos : 0 ≤ (l : ℝ) := by
      have hpos := l.2.1
      linarith
    have hq_nonneg : 0 ≤ q (θ + (l : ℝ)⁻¹ • (x - θ)) := h0 _
    nlinarith
  have h_one_mem : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> norm_num
  calc
    hull q θ x = ⨅ l : Set.Ioc (0 : ℝ) 1, (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) := rfl
    _ ≤ (1 : ℝ) * q (θ + ((1 : ℝ)⁻¹) • (x - θ)) := ciInf_le h_bdd ⟨1, h_one_mem⟩
    _ = q x := by
      simp

theorem hull_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ : V)
    (h0 : ∀ y, 0 ≤ q y) : hull q θ θ = 0 := by
  have hqθ_nonneg : 0 ≤ q θ := h0 θ
  have h_nonneg : 0 ≤ hull q θ θ := by
    refine le_ciInf ?_
    intro l
    have hl_nonneg : (0 : ℝ) ≤ (l : ℝ) := l.2.1.le
    have hterm_nonneg : 0 ≤ q (θ + ((l : ℝ)⁻¹ • (θ - θ))) := h0 _
    exact mul_nonneg hl_nonneg hterm_nonneg
  have h_le : hull q θ θ ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    set l : ℝ := min 1 (ε / (q θ + 1)) with hl_def
    have hqθ_add_one_pos : 0 < q θ + 1 := by linarith
    have hl_pos : 0 < l := by
      rw [hl_def]
      refine lt_min_iff.mpr ⟨by norm_num, div_pos hε hqθ_add_one_pos⟩
    have hl_le_one : l ≤ 1 := by
      rw [hl_def]
      exact min_le_left _ _
    have hl_mem : l ∈ Set.Ioc (0 : ℝ) 1 := ⟨hl_pos, hl_le_one⟩
    let l' : Set.Ioc (0 : ℝ) 1 := ⟨l, hl_mem⟩
    have hbdd : BddBelow (Set.range (λ (x : Set.Ioc (0 : ℝ) 1) => (x : ℝ) * q (θ + ((x : ℝ)⁻¹ • (θ - θ))))) := by
      refine ⟨0, ?_⟩
      rintro y ⟨x, rfl⟩
      have hx_nonneg : 0 ≤ (x : ℝ) := x.2.1.le
      have hterm_nonneg : 0 ≤ q (θ + ((x : ℝ)⁻¹ • (θ - θ))) := h0 _
      exact mul_nonneg hx_nonneg hterm_nonneg
    have h_hull_le_term : hull q θ θ ≤ (l : ℝ) * q (θ + ((l : ℝ)⁻¹ • (θ - θ))) := by
      simpa [hull] using ciInf_le hbdd l'
    have h_term_eq : (l : ℝ) * q (θ + ((l : ℝ)⁻¹ • (θ - θ))) = (l : ℝ) * q θ := by
      simp [sub_self, smul_zero, add_zero]
    rw [h_term_eq] at h_hull_le_term
    have h_lt : (l : ℝ) * q θ < ε := by
      have hl_le_div : l ≤ ε / (q θ + 1) := by
        rw [hl_def]
        exact min_le_right _ _
      have h_mul : l * (q θ + 1) ≤ ε := by
        calc
          l * (q θ + 1) ≤ (ε / (q θ + 1)) * (q θ + 1) := by nlinarith
          _ = ε := by field_simp [hqθ_add_one_pos.ne.symm]
      have h_lt_mul : (l : ℝ) * q θ < l * (q θ + 1) := by
        nlinarith
      linarith
    linarith
  exact le_antisymm h_le h_nonneg

theorem iInf_Ioc_mul_const (c : ℝ) (hc : 0 ≤ c) : ⨅ l : Set.Ioc (0 : ℝ) 1, (l : ℝ) * c = 0 := by
  apply le_antisymm
  · by_contra! h
    set v := ⨅ l : Set.Ioc (0 : ℝ) 1, (l : ℝ) * c
    have hvpos : 0 < v := h
    have hdenom_pos : 0 < 2 * (c + 1) := by nlinarith
    set l₀ := min (1 : ℝ) (v / (2 * (c + 1))) with hl₀
    have hl₀pos : 0 < l₀ := by
      refine lt_min_iff.mpr ⟨by norm_num, div_pos hvpos hdenom_pos⟩
    have hl₀le1 : l₀ ≤ 1 := min_le_left _ _
    have hl₀mem : l₀ ∈ Set.Ioc (0 : ℝ) 1 := ⟨hl₀pos, hl₀le1⟩
    have hl₀_le_vdiv : l₀ ≤ v / (2 * (c + 1)) := by
      rw [hl₀]
      exact min_le_right _ _
    have h_mul_lt_v : (l₀ : ℝ) * c < v := by
      calc
        (l₀ : ℝ) * c ≤ (v / (2 * (c + 1))) * c := by
          nlinarith
        _ = v * (c / (2 * (c + 1))) := by ring
        _ < v * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hvpos
          exact (div_lt_one hdenom_pos).mpr (by nlinarith)
        _ = v := by simp
    have hbdd : BddBelow (Set.range (λ l : Set.Ioc (0 : ℝ) 1 => (l : ℝ) * c)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨l, rfl⟩
      have hl_nonneg : 0 ≤ (l : ℝ) := l.2.1.le
      nlinarith
    have hciInf_le := ciInf_le hbdd ⟨l₀, hl₀mem⟩
    linarith
  · have h_nonempty : Nonempty (Set.Ioc (0 : ℝ) 1) := by
      refine ⟨⟨1, by norm_num, by norm_num⟩⟩
    refine le_ciInf ?_
    intro l
    have hl_nonneg : 0 ≤ (l : ℝ) := l.2.1.le
    nlinarith

theorem hull_convexOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ : V)
    (hq : ConvexOn ℝ Set.univ q) (h0 : ∀ y, 0 ≤ q y) : ConvexOn ℝ Set.univ (hull q θ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp_rw [Set.mem_univ] at hx hy
  rcases ha.eq_or_lt with (rfl | ha_pos)
  · -- a = 0, b = 1
    have hb1 : b = 1 := by linarith
    subst hb1
    simp [hull]
  rcases hb.eq_or_lt with (rfl | hb_pos)
  · -- b = 0, a = 1
    have ha1 : a = 1 := by linarith
    subst ha1
    simp [hull]
  -- now a > 0, b > 0, a + b = 1
  set F : V → Set.Ioc (0 : ℝ) 1 → ℝ := λ z l => (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (z - θ))
  have hF_nonneg : ∀ z l, 0 ≤ F z l := by
    intro z l
    dsimp [F]
    have hl0 : 0 ≤ (l : ℝ) := l.2.1.le
    have hq0 : 0 ≤ q (θ + ((l : ℝ)⁻¹ : ℝ) • (z - θ)) := h0 _
    nlinarith
  have h_nonempty : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, by norm_num, by norm_num⟩⟩
  have h_bdd_below (z : V) : BddBelow (Set.range (F z)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨l, rfl⟩
    exact hF_nonneg z l
  -- For any l₁, l₂ ∈ Ioc 0 1, we have F(a•x + b•y, a*l₁ + b*l₂) ≤ a * F(x, l₁) + b * F(y, l₂)
  have h_key (l₁ l₂ : Set.Ioc (0 : ℝ) 1) : F (a • x + b • y) ⟨a * (l₁ : ℝ) + b * (l₂ : ℝ), by
      have hpos : 0 < a * (l₁ : ℝ) + b * (l₂ : ℝ) := by
        have h1 : 0 < (l₁ : ℝ) := l₁.2.1
        have h2 : 0 < (l₂ : ℝ) := l₂.2.1
        nlinarith
      have hle1 : a * (l₁ : ℝ) + b * (l₂ : ℝ) ≤ 1 := by
        have h1 : (l₁ : ℝ) ≤ 1 := l₁.2.2
        have h2 : (l₂ : ℝ) ≤ 1 := l₂.2.2
        nlinarith
      exact ⟨hpos, hle1⟩⟩ ≤ a * F x l₁ + b * F y l₂ := by
    set l : Set.Ioc (0 : ℝ) 1 := ⟨a * (l₁ : ℝ) + b * (l₂ : ℝ), by
      have hpos : 0 < a * (l₁ : ℝ) + b * (l₂ : ℝ) := by
        have h1 : 0 < (l₁ : ℝ) := l₁.2.1
        have h2 : 0 < (l₂ : ℝ) := l₂.2.1
        nlinarith
      have hle1 : a * (l₁ : ℝ) + b * (l₂ : ℝ) ≤ 1 := by
        have h1 : (l₁ : ℝ) ≤ 1 := l₁.2.2
        have h2 : (l₂ : ℝ) ≤ 1 := l₂.2.2
        nlinarith
      exact ⟨hpos, hle1⟩⟩
    have hpos_l : 0 < (l : ℝ) := l.2.1
    -- Key identity: θ + l⁻¹ • (a•x + b•y - θ) = (a*l₁/l) • (θ + l₁⁻¹ • (x - θ)) + (b*l₂/l) • (θ + l₂⁻¹ • (y - θ))
    have h_eq : θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - θ) =
        ((a * (l₁ : ℝ)) / (l : ℝ)) • (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ)) +
        ((b * (l₂ : ℝ)) / (l : ℝ)) • (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ)) := by
      set y₁ := θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ)
      set y₂ := θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ)
      have hx_sub' : x - θ = (l₁ : ℝ) • (y₁ - θ) := by
        dsimp [y₁]
        have hl₁ : (l₁ : ℝ) ≠ 0 := ne_of_gt l₁.2.1
        calc
          x - θ = (1 : ℝ) • (x - θ) := by simp
          _ = (((l₁ : ℝ)⁻¹) * (l₁ : ℝ)) • (x - θ) := by
            have h : ((l₁ : ℝ)⁻¹) * (l₁ : ℝ) = 1 := inv_mul_cancel₀ hl₁
            simp [h]
          _ = (l₁ : ℝ) • (((l₁ : ℝ)⁻¹) • (x - θ)) := by rw [smul_smul, mul_comm]
          _ = (l₁ : ℝ) • (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ) - θ) := by simp
      have hy_sub' : y - θ = (l₂ : ℝ) • (y₂ - θ) := by
        dsimp [y₂]
        have hl₂ : (l₂ : ℝ) ≠ 0 := ne_of_gt l₂.2.1
        calc
          y - θ = (1 : ℝ) • (y - θ) := by simp
          _ = (((l₂ : ℝ)⁻¹) * (l₂ : ℝ)) • (y - θ) := by
            have h : ((l₂ : ℝ)⁻¹) * (l₂ : ℝ) = 1 := inv_mul_cancel₀ hl₂
            simp [h]
          _ = (l₂ : ℝ) • (((l₂ : ℝ)⁻¹) • (y - θ)) := by rw [smul_smul, mul_comm]
          _ = (l₂ : ℝ) • (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ) - θ) := by simp
      calc
        θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - θ)
            = θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - (a + b) • θ) := by
              rw [hab, one_smul]
        _ = θ + ((l : ℝ)⁻¹ : ℝ) • (a • (x - θ) + b • (y - θ)) := by
          simp [smul_sub, add_smul, smul_add]
          abel
        _ = θ + ((l : ℝ)⁻¹ : ℝ) • (a • ((l₁ : ℝ) • (y₁ - θ)) + b • ((l₂ : ℝ) • (y₂ - θ))) := by
              rw [hx_sub', hy_sub']
        _ = θ + ((l : ℝ)⁻¹ : ℝ) • ((a * (l₁ : ℝ)) • (y₁ - θ) + (b * (l₂ : ℝ)) • (y₂ - θ)) := by
              simp [smul_smul, mul_comm]
        _ = θ + ((a * (l₁ : ℝ)) / (l : ℝ)) • (y₁ - θ) + ((b * (l₂ : ℝ)) / (l : ℝ)) • (y₂ - θ) := by
              simp [smul_smul, mul_comm, div_eq_inv_mul, add_assoc]
        _ = (1 - (a * (l₁ : ℝ)) / (l : ℝ) - (b * (l₂ : ℝ)) / (l : ℝ)) • θ +
            ((a * (l₁ : ℝ)) / (l : ℝ)) • y₁ + ((b * (l₂ : ℝ)) / (l : ℝ)) • y₂ := by
              simp [smul_sub, sub_smul]
              abel
        _ = ((a * (l₁ : ℝ)) / (l : ℝ)) • y₁ + ((b * (l₂ : ℝ)) / (l : ℝ)) • y₂ := by
              have hsum : (a * (l₁ : ℝ)) / (l : ℝ) + (b * (l₂ : ℝ)) / (l : ℝ) = 1 := by
                field_simp [hpos_l.ne']
                ring
              rw [show (1 : ℝ) - (a * (l₁ : ℝ)) / (l : ℝ) - (b * (l₂ : ℝ)) / (l : ℝ) = 0 by linarith]
              simp
        _ = ((a * (l₁ : ℝ)) / (l : ℝ)) • (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ)) +
            ((b * (l₂ : ℝ)) / (l : ℝ)) • (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ)) := by
              dsimp [y₁, y₂]
    have h_coeff_nonneg1 : 0 ≤ (a * (l₁ : ℝ)) / (l : ℝ) := by
      refine div_nonneg (mul_nonneg ha_pos.le l₁.2.1.le) hpos_l.le
    have h_coeff_nonneg2 : 0 ≤ (b * (l₂ : ℝ)) / (l : ℝ) := by
      refine div_nonneg (mul_nonneg hb_pos.le l₂.2.1.le) hpos_l.le
    have h_coeff_sum : (a * (l₁ : ℝ)) / (l : ℝ) + (b * (l₂ : ℝ)) / (l : ℝ) = 1 := by
      field_simp [hpos_l.ne']
      ring
    have hx_mem : θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ) ∈ Set.univ := Set.mem_univ _
    have hy_mem : θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ) ∈ Set.univ := Set.mem_univ _
    have hq_ineq : q (θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - θ)) ≤
        ((a * (l₁ : ℝ)) / (l : ℝ)) * q (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ)) +
        ((b * (l₂ : ℝ)) / (l : ℝ)) * q (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ)) := by
      rw [h_eq]
      have := hq.2 hx_mem hy_mem h_coeff_nonneg1 h_coeff_nonneg2 h_coeff_sum
      simpa [smul_eq_mul] using this
    -- Now multiply by l and use the definition of F
    dsimp [F]
    have h_mul : (l : ℝ) * q (θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - θ)) ≤
        a * ((l₁ : ℝ) * q (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ))) +
        b * ((l₂ : ℝ) * q (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ))) := by
      have h := hq_ineq
      -- h: q(...) ≤ (a*l₁/l) * q(y₁) + (b*l₂/l) * q(y₂)
      -- Multiply both sides by l (which is > 0)
      have hpos_l' : 0 ≤ (l : ℝ) := hpos_l.le
      calc
        (l : ℝ) * q (θ + ((l : ℝ)⁻¹ : ℝ) • (a • x + b • y - θ))
            ≤ (l : ℝ) * (((a * (l₁ : ℝ)) / (l : ℝ)) * q (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ)) +
              ((b * (l₂ : ℝ)) / (l : ℝ)) * q (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ))) := by
          nlinarith
        _ = a * ((l₁ : ℝ) * q (θ + ((l₁ : ℝ)⁻¹ : ℝ) • (x - θ))) +
            b * ((l₂ : ℝ) * q (θ + ((l₂ : ℝ)⁻¹ : ℝ) • (y - θ))) := by
          field_simp [hpos_l.ne']
    exact h_mul
  -- Now the main inequality: for all l₁, l₂, hull(a•x + b•y) ≤ a * F(x, l₁) + b * F(y, l₂)
  have h_forall (l₁ l₂ : Set.Ioc (0 : ℝ) 1) : hull q θ (a • x + b • y) ≤ a * F x l₁ + b * F y l₂ := by
    calc
      hull q θ (a • x + b • y) = (⨅ (l' : Set.Ioc (0 : ℝ) 1), F (a • x + b • y) l') := rfl
      _ ≤ F (a • x + b • y) ⟨a * (l₁ : ℝ) + b * (l₂ : ℝ), by
          have hpos : 0 < a * (l₁ : ℝ) + b * (l₂ : ℝ) := by
            have h1 : 0 < (l₁ : ℝ) := l₁.2.1
            have h2 : 0 < (l₂ : ℝ) := l₂.2.1
            nlinarith
          have hle1 : a * (l₁ : ℝ) + b * (l₂ : ℝ) ≤ 1 := by
            have h1 : (l₁ : ℝ) ≤ 1 := l₁.2.2
            have h2 : (l₂ : ℝ) ≤ 1 := l₂.2.2
            nlinarith
          exact ⟨hpos, hle1⟩⟩ := ciInf_le (h_bdd_below (a • x + b • y)) _
      _ ≤ a * F x l₁ + b * F y l₂ := h_key l₁ l₂
  -- Take inf over l₁
  have h_inf1 (l₂ : Set.Ioc (0 : ℝ) 1) : hull q θ (a • x + b • y) ≤ a * hull q θ x + b * F y l₂ := by
    have h_le : hull q θ (a • x + b • y) - b * F y l₂ ≤ a * hull q θ x := by
      have h_forall_l1 : ∀ l₁ : Set.Ioc (0 : ℝ) 1, hull q θ (a • x + b • y) - b * F y l₂ ≤ a * F x l₁ := by
        intro l₁
        have h := h_forall l₁ l₂
        nlinarith
      have h_bdd : BddBelow (Set.range (λ (l₁ : Set.Ioc (0 : ℝ) 1) => a * F x l₁)) := by
        refine ⟨0, ?_⟩
        rintro y ⟨l₁, rfl⟩
        have ha0 : 0 ≤ a := ha_pos.le
        have hF0 : 0 ≤ F x l₁ := hF_nonneg x l₁
        nlinarith
      calc
        hull q θ (a • x + b • y) - b * F y l₂ ≤ ⨅ (l₁ : Set.Ioc (0 : ℝ) 1), a * F x l₁ := le_ciInf h_forall_l1
        _ = a * (⨅ (l₁ : Set.Ioc (0 : ℝ) 1), F x l₁) := by
          simpa [smul_eq_mul] using (Real.smul_iInf_of_nonneg (ha_pos.le) (λ l₁ => F x l₁)).symm
        _ = a * hull q θ x := rfl
    nlinarith
  -- Take inf over l₂
  have h_final : hull q θ (a • x + b • y) ≤ a * hull q θ x + b * hull q θ y := by
    have h_forall_l2 : ∀ l₂ : Set.Ioc (0 : ℝ) 1, hull q θ (a • x + b • y) - a * hull q θ x ≤ b * F y l₂ := by
      intro l₂
      have h := h_inf1 l₂
      nlinarith
    have h_bdd : BddBelow (Set.range (λ (l₂ : Set.Ioc (0 : ℝ) 1) => b * F y l₂)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨l₂, rfl⟩
      have hb0 : 0 ≤ b := hb_pos.le
      have hF0 : 0 ≤ F y l₂ := hF_nonneg y l₂
      nlinarith
    have h_le : hull q θ (a • x + b • y) - a * hull q θ x ≤ ⨅ (l₂ : Set.Ioc (0 : ℝ) 1), b * F y l₂ :=
      le_ciInf h_forall_l2
    have h_inf_mul : (⨅ (l₂ : Set.Ioc (0 : ℝ) 1), b * F y l₂) = b * hull q θ y := by
      simpa [smul_eq_mul, hull] using (Real.smul_iInf_of_nonneg (hb_pos.le) (λ l₂ => F y l₂)).symm
    rw [h_inf_mul] at h_le
    nlinarith
  -- Convert to SMul form if needed
  simpa [smul_eq_mul] using h_final

theorem hull_lipschitz {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ : V)
    (K : ℝ) (h0 : ∀ y, 0 ≤ q y) (hK : ∀ y z, |q y - q z| ≤ K * ‖y - z‖) (x y : V) :
    |hull q θ x - hull q θ y| ≤ K * ‖x - y‖ := by
  have h_nonempty : Nonempty (Set.Ioc (0 : ℝ) 1) := by
    refine ⟨⟨1, by norm_num, by norm_num⟩⟩
  haveI := h_nonempty
  have h_bdd_below_x : BddBelow (Set.range (λ (l : Set.Ioc (0 : ℝ) 1) => (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨l, rfl⟩
    have hl_nonneg : 0 ≤ (l : ℝ) := by linarith [l.2.1]
    have hq_nonneg : 0 ≤ q (θ + (l : ℝ)⁻¹ • (x - θ)) := h0 _
    nlinarith
  have h_bdd_below_y : BddBelow (Set.range (λ (l : Set.Ioc (0 : ℝ) 1) => (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨l, rfl⟩
    have hl_nonneg : 0 ≤ (l : ℝ) := by linarith [l.2.1]
    have hq_nonneg : 0 ≤ q (θ + (l : ℝ)⁻¹ • (y - θ)) := h0 _
    nlinarith
  have h_bound (l : Set.Ioc (0 : ℝ) 1) : |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ))| ≤ K * ‖x - y‖ := by
    have hlpos : 0 < (l : ℝ) := l.2.1
    have hqdiff : |q (θ + (l : ℝ)⁻¹ • (x - θ)) - q (θ + (l : ℝ)⁻¹ • (y - θ))| ≤ K * ‖(θ + (l : ℝ)⁻¹ • (x - θ)) - (θ + (l : ℝ)⁻¹ • (y - θ))‖ :=
      hK _ _
    have hnorm : ‖(θ + (l : ℝ)⁻¹ • (x - θ)) - (θ + (l : ℝ)⁻¹ • (y - θ))‖ = (l : ℝ)⁻¹ * ‖x - y‖ := by
      have h_eq : (θ + (l : ℝ)⁻¹ • (x - θ)) - (θ + (l : ℝ)⁻¹ • (y - θ)) = (l : ℝ)⁻¹ • (x - y) := by
        calc
          (θ + (l : ℝ)⁻¹ • (x - θ)) - (θ + (l : ℝ)⁻¹ • (y - θ)) = ((θ + (l : ℝ)⁻¹ • (x - θ)) - θ) - (l : ℝ)⁻¹ • (y - θ) := by rw [sub_add_eq_sub_sub]
          _ = (l : ℝ)⁻¹ • (x - θ) - (l : ℝ)⁻¹ • (y - θ) := by rw [add_sub_cancel_left]
          _ = (l : ℝ)⁻¹ • ((x - θ) - (y - θ)) := by rw [← smul_sub]
          _ = (l : ℝ)⁻¹ • (x - y) := by
            have h_inner : (x - θ) - (y - θ) = x - y := by abel
            rw [h_inner]
      rw [h_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos_of_pos hlpos)]
    have hmain : |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ))| ≤ (l : ℝ) * |q (θ + (l : ℝ)⁻¹ • (x - θ)) - q (θ + (l : ℝ)⁻¹ • (y - θ))| := by
      rw [← mul_sub, abs_mul, abs_of_pos hlpos]
    calc
      |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ))| ≤ (l : ℝ) * |q (θ + (l : ℝ)⁻¹ • (x - θ)) - q (θ + (l : ℝ)⁻¹ • (y - θ))| := hmain
      _ ≤ (l : ℝ) * (K * ‖(θ + (l : ℝ)⁻¹ • (x - θ)) - (θ + (l : ℝ)⁻¹ • (y - θ))‖) := by
        nlinarith
      _ = (l : ℝ) * (K * ((l : ℝ)⁻¹ * ‖x - y‖)) := by rw [hnorm]
      _ = K * ‖x - y‖ := by
        field_simp [hlpos.ne']
  have h_lower_bound : ∀ (l : Set.Ioc (0 : ℝ) 1), hull q θ x - K * ‖x - y‖ ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) := by
    intro l
    have hx_le : hull q θ x ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) := ciInf_le h_bdd_below_x l
    have hxy : (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) + K * ‖x - y‖ := by
      have := h_bound l
      linarith [abs_sub_le_iff.mp this]
    linarith
  have h_upper_bound : ∀ (l : Set.Ioc (0 : ℝ) 1), hull q θ y - K * ‖x - y‖ ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) := by
    intro l
    have hy_le : hull q θ y ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) := ciInf_le h_bdd_below_y l
    have hyx : (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) + K * ‖x - y‖ := by
      have h_bound' : |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ))| ≤ K * ‖x - y‖ := by
        have : |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ))| = |(l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) - (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (y - θ))| := by
          rw [abs_sub_comm]
        rw [this]
        exact h_bound l
      linarith [abs_sub_le_iff.mp h_bound']
    linarith
  have h_left : hull q θ x - K * ‖x - y‖ ≤ hull q θ y := le_ciInf h_lower_bound
  have h_right : hull q θ y - K * ‖x - y‖ ≤ hull q θ x := le_ciInf h_upper_bound
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

theorem hull_ge_of_slope {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ)
    (θ x : V) (s : ℝ) (h0 : ∀ y, 0 ≤ q y)
    (hs : ∀ l : ℝ, 0 < l → l ≤ 1 → q x + (l⁻¹ - 1) * s ≤ q (θ + l⁻¹ • (x - θ))) :
    q x - max (q x - s) 0 ≤ hull q θ x := by
  have h_nonempty : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, by norm_num, le_rfl⟩⟩
  refine le_ciInf ?_
  intro l
  have hlpos : 0 < (l : ℝ) := l.2.1
  have hle1 : (l : ℝ) ≤ 1 := l.2.2
  have h_ineq := hs (l : ℝ) hlpos hle1
  -- h_ineq : q x + ((l : ℝ)⁻¹ - 1) * s ≤ q (θ + (l : ℝ)⁻¹ • (x - θ))
  have h_mul : (l : ℝ) * q x + (1 - (l : ℝ)) * s ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ)) := by
    have h_mul' := mul_le_mul_of_nonneg_left h_ineq hlpos.le
    -- h_mul' : (l : ℝ) * (q x + ((l : ℝ)⁻¹ - 1) * s) ≤ (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (x - θ))
    have h_left : (l : ℝ) * (q x + ((l : ℝ)⁻¹ - 1) * s) = (l : ℝ) * q x + (1 - (l : ℝ)) * s := by
      calc
        (l : ℝ) * (q x + ((l : ℝ)⁻¹ - 1) * s) = (l : ℝ) * q x + (l : ℝ) * (((l : ℝ)⁻¹ - 1) * s) := by ring
        _ = (l : ℝ) * q x + ((l : ℝ) * ((l : ℝ)⁻¹ - 1)) * s := by ring
        _ = (l : ℝ) * q x + ((l : ℝ) * (l : ℝ)⁻¹ - (l : ℝ)) * s := by ring
        _ = (l : ℝ) * q x + (1 - (l : ℝ)) * s := by
          field_simp [ne_of_gt hlpos]
    linarith
  have h_min_eq : q x - max (q x - s) 0 = min (q x) s := by
    by_cases h : q x ≤ s
    · have hmax : max (q x - s) 0 = 0 := max_eq_right (by linarith)
      rw [hmax, sub_zero, min_eq_left h]
    · have hmax : max (q x - s) 0 = q x - s := max_eq_left (by linarith [not_le.mp h])
      rw [hmax, sub_sub_cancel, min_eq_right (by linarith)]
  rw [h_min_eq]
  have h_min_le : min (q x) s ≤ (l : ℝ) * q x + (1 - (l : ℝ)) * s := by
    by_cases h : q x ≤ s
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right (by linarith)]
      nlinarith
  linarith

theorem ratio_mono (ψ : ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hconv : ConvexOn ℝ (Set.Ioi 0) ψ)
    (htan : ∀ τ, 0 < τ → τ * (ψ ρ / ρ) ≤ ψ τ) (t τ : ℝ) (ht : ρ ≤ t) (htτ : t ≤ τ) :
    ψ t / t ≤ ψ τ / τ := by
  have ht_pos : 0 < t := lt_of_lt_of_le hρ ht
  have hτ_pos : 0 < τ := lt_of_lt_of_le ht_pos htτ
  have h_le : ρ ≤ τ := le_trans ht htτ
  set c := ψ ρ / ρ with hc_def
  have hψρ : ψ ρ = c * ρ := by
    dsimp [c]
    field_simp [hρ.ne']
  have hψτ : c * τ ≤ ψ τ := by
    simpa [hc_def, mul_comm] using htan τ hτ_pos
  by_cases h_eq : τ = ρ
  · -- then t = ρ = τ, trivial
    have ht_eq : t = ρ := le_antisymm (by simpa [h_eq] using htτ) ht
    rw [ht_eq, h_eq]
  · -- τ ≠ ρ, so τ > ρ
    have h_lt : ρ < τ := by
      by_contra! H
      apply h_eq
      linarith
    have h_denom_pos : 0 < τ - ρ := sub_pos.mpr h_lt
    set μ := (t - ρ) / (τ - ρ) with hμ_def
    have hμ_nonneg : 0 ≤ μ := div_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr h_le)
    have hμ_le_one : μ ≤ 1 := by
      refine (div_le_one h_denom_pos).mpr ?_
      linarith
    have h_sum : (1 - μ) + μ = 1 := by ring
    have h_nonneg1 : 0 ≤ 1 - μ := by linarith
    have ht_expr : t = (1 - μ) * ρ + μ * τ := by
      dsimp [μ]
      field_simp [h_denom_pos.ne']
      ring
    have h_conv_ineq : ψ ((1 - μ) * ρ + μ * τ) ≤ (1 - μ) * ψ ρ + μ * ψ τ := by
      have hmem_ρ : ρ ∈ Set.Ioi 0 := hρ
      have hmem_τ : τ ∈ Set.Ioi 0 := hτ_pos
      have := hconv.2 hmem_ρ hmem_τ h_nonneg1 hμ_nonneg h_sum
      simpa [smul_eq_mul] using this
    have h_bound : ψ t ≤ (1 - μ) * ψ ρ + μ * ψ τ := by
      rw [ht_expr]
      exact h_conv_ineq
    set δ := ψ τ - c * τ with hδ_def
    have hδ_nonneg : 0 ≤ δ := by linarith
    have hψτ_eq : ψ τ = c * τ + δ := by linarith
    have h_bound2 : ψ t ≤ c * t + μ * δ := by
      rw [hψρ, hψτ_eq] at h_bound
      -- h_bound: ψ t ≤ (1 - μ) * (c * ρ) + μ * (c * τ + δ)
      -- = c * ((1 - μ) * ρ + μ * τ) + μ * δ = c * t + μ * δ
      have h_temp : (1 - μ) * (c * ρ) + μ * (c * τ + δ) = c * t + μ * δ := by
        rw [ht_expr]
        ring
      rw [h_temp] at h_bound
      exact h_bound
    have h_μτ_le_t : μ * τ ≤ t := by
      dsimp [μ]
      field_simp [h_denom_pos.ne']
      nlinarith
    have h_goal_mul : ψ t * τ ≤ ψ τ * t := by
      have h1 : ψ t * τ ≤ (c * t + μ * δ) * τ := by nlinarith
      have h2 : (c * t + μ * δ) * τ ≤ ψ τ * t := by
        rw [hψτ_eq]
        have : μ * δ * τ ≤ δ * t := by
          nlinarith
        nlinarith
      nlinarith
    rw [div_le_div_iff₀ ht_pos hτ_pos]
    exact h_goal_mul

theorem hull_ray {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ) (θ v : V)
    (ρ t : ℝ) (hρ : 0 < ρ) (ht : 0 < t) (h0 : ∀ y, 0 ≤ q y)
    (hconv : ConvexOn ℝ (Set.Ioi 0) (fun τ : ℝ => q (θ + τ • v)))
    (htan : ∀ τ, 0 < τ → τ * (q (θ + ρ • v) / ρ) ≤ q (θ + τ • v)) :
    hull q θ (θ + t • v) = if t ≤ ρ then t * (q (θ + ρ • v) / ρ) else q (θ + t • v) := by
  set ψ := fun (τ : ℝ) => q (θ + τ • v) with hψ_def
  set c := ψ ρ / ρ with hc_def
  have hψ_nonneg : ∀ τ, 0 ≤ ψ τ := by
    intro τ; dsimp [ψ]; apply h0
  have htan' : ∀ τ, 0 < τ → τ * c ≤ ψ τ := by
    intro τ hτ; dsimp [c, ψ]; exact htan τ hτ
  have hne : Nonempty (Set.Ioc (0 : ℝ) 1) := by
    refine ⟨⟨1, by norm_num, le_rfl⟩⟩
  have hterm : ∀ (l : Set.Ioc (0 : ℝ) 1), (l : ℝ) * q (θ + (l : ℝ)⁻¹ • ((θ + t • v) - θ)) = t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) := by
    intro l
    have hlpos : 0 < (l : ℝ) := l.2.1
    calc
      (l : ℝ) * q (θ + (l : ℝ)⁻¹ • ((θ + t • v) - θ)) = (l : ℝ) * q (θ + (l : ℝ)⁻¹ • (t • v)) := by
        simp
      _ = (l : ℝ) * q (θ + ((l : ℝ)⁻¹ * t) • v) := by
        simp [smul_smul]
      _ = (l : ℝ) * ψ ((l : ℝ)⁻¹ * t) := by
        simp [ψ]
      _ = (l : ℝ) * ψ (t / (l : ℝ)) := by
        simp [div_eq_inv_mul]
      _ = t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) := by
        field_simp [hlpos.ne.symm, ht.ne.symm]
  have hull_eq : hull q θ (θ + t • v) = ⨅ l : Set.Ioc (0 : ℝ) 1, t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) := by
    dsimp [hull]
    have : (fun (l : Set.Ioc (0 : ℝ) 1) => (l : ℝ) * q (θ + (l : ℝ)⁻¹ • ((θ + t • v) - θ))) =
           (fun (l : Set.Ioc (0 : ℝ) 1) => t * (ψ (t / (l : ℝ)) / (t / (l : ℝ)))) := by
      ext l; exact hterm l
    rw [this]
  rw [hull_eq]
  have hbdd : BddBelow (Set.range (fun (l : Set.Ioc (0 : ℝ) 1) => t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨l, rfl⟩
    have hpos_ratio : 0 ≤ ψ (t / (l : ℝ)) / (t / (l : ℝ)) :=
      div_nonneg (hψ_nonneg _) (div_nonneg (by linarith) (by linarith [l.2.1]))
    exact mul_nonneg (by linarith) hpos_ratio
  by_cases hle : t ≤ ρ
  · rw [if_pos hle]
    apply le_antisymm
    · set l0 : Set.Ioc (0 : ℝ) 1 := ⟨t / ρ, div_pos ht hρ, (div_le_one hρ).mpr hle⟩ with hl0_def
      have hterm0 : t * (ψ (t / (l0 : ℝ)) / (t / (l0 : ℝ))) = t * c := by
        dsimp [l0]
        have h_eq : t / (t / ρ) = ρ := by
          field_simp [hρ.ne.symm, ht.ne.symm]
        calc
          t * (ψ (t / ((t / ρ) : ℝ)) / (t / ((t / ρ) : ℝ))) = t * (ψ (t / (t / ρ)) / (t / (t / ρ))) := rfl
          _ = t * (ψ ρ / ρ) := by simp [h_eq]
          _ = t * c := rfl
      calc
        ⨅ l : Set.Ioc (0 : ℝ) 1, t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) ≤ t * (ψ (t / (l0 : ℝ)) / (t / (l0 : ℝ))) :=
          ciInf_le hbdd l0
        _ = t * c := hterm0
    · apply le_ciInf
      intro l
      have hlpos : 0 < (l : ℝ) := l.2.1
      have hτpos : 0 < t / (l : ℝ) := div_pos ht hlpos
      have hineq : (t / (l : ℝ)) * c ≤ ψ (t / (l : ℝ)) := htan' (t / (l : ℝ)) hτpos
      have hdiv : c ≤ ψ (t / (l : ℝ)) / (t / (l : ℝ)) :=
        (le_div_iff₀ hτpos).mpr (by rwa [mul_comm])
      exact mul_le_mul_of_nonneg_left hdiv (by linarith)
  · rw [if_neg (by linarith : ¬ t ≤ ρ)]
    apply le_antisymm
    · set l1 : Set.Ioc (0 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩ with hl1_def
      have hterm1 : t * (ψ (t / (l1 : ℝ)) / (t / (l1 : ℝ))) = ψ t := by
        dsimp [l1]
        field_simp [ht.ne.symm]
      calc
        ⨅ l : Set.Ioc (0 : ℝ) 1, t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) ≤ t * (ψ (t / (l1 : ℝ)) / (t / (l1 : ℝ))) :=
          ciInf_le hbdd l1
        _ = ψ t := hterm1
    · apply le_ciInf
      intro l
      have hlpos : 0 < (l : ℝ) := l.2.1
      have hτpos : 0 < t / (l : ℝ) := div_pos ht hlpos
      have hτ_ge_t : t ≤ t / (l : ℝ) := by
        apply (le_div_iff₀ hlpos).mpr
        nlinarith [l.2.2]
      have h_ratio : ψ t / t ≤ ψ (t / (l : ℝ)) / (t / (l : ℝ)) :=
        ratio_mono ψ ρ hρ hconv htan' t (t / (l : ℝ)) (by linarith) hτ_ge_t
      calc
        ψ t = t * (ψ t / t) := by field_simp [ht.ne.symm]
        _ ≤ t * (ψ (t / (l : ℝ)) / (t / (l : ℝ))) :=
          mul_le_mul_of_nonneg_left h_ratio (by linarith)

theorem hull_eq_iInf_rat {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : V → ℝ)
    (hq : Continuous q) (θ x : V) (h0 : ∀ y, 0 ≤ q y) :
    hull q θ x = ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1}, ((r : ℚ) : ℝ) * q (θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ)) := by
  let f : ℝ → ℝ := λ l => l * q (θ + l⁻¹ • (x - θ))
  have hf_cont_on_pos : ContinuousOn f (Set.Ioi 0) := by
    intro l hl
    have hl_ne : l ≠ 0 := ne_of_gt hl
    have h_cont : ContinuousAt f l := by
      have h_inv_cont : ContinuousAt (λ (t : ℝ) => t⁻¹) l :=
        continuousAt_inv₀ hl_ne
      have h_smul_cont : ContinuousAt (λ (t : ℝ) => t⁻¹ • (x - θ)) l :=
        ContinuousAt.smul h_inv_cont continuousAt_const
      have h_inner_cont : ContinuousAt (λ (t : ℝ) => θ + t⁻¹ • (x - θ)) l :=
        ContinuousAt.add continuousAt_const h_smul_cont
      have hq_cont : ContinuousAt q (θ + l⁻¹ • (x - θ)) := hq.continuousAt
      have hq_comp : ContinuousAt (q ∘ (λ t => θ + t⁻¹ • (x - θ))) l :=
        ContinuousAt.comp (g := q) (f := (λ t => θ + t⁻¹ • (x - θ))) hq_cont h_inner_cont
      have h_mul : ContinuousAt (λ t => t * (q ∘ (λ s => θ + s⁻¹ • (x - θ))) t) l :=
        ContinuousAt.mul continuousAt_id hq_comp
      simpa [f, Function.comp_def] using h_mul
    exact h_cont.continuousWithinAt
  have h0' : ∀ l : Set.Ioc (0 : ℝ) 1, 0 ≤ f (l : ℝ) := by
    intro l
    have hl_pos : 0 < (l : ℝ) := l.2.1
    have hq_nonneg := h0 (θ + ((l : ℝ)⁻¹) • (x - θ))
    nlinarith [hl_pos, hq_nonneg]
  have hBddBelow : BddBelow (Set.range (λ (l : Set.Ioc (0 : ℝ) 1) => f (l : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨l, rfl⟩
    exact h0' l
  have hNonempty : Nonempty (Set.Ioc (0 : ℝ) 1) := by
    refine ⟨⟨1, by norm_num, le_rfl⟩⟩
  have hBddBelowRat : BddBelow (Set.range (λ (r : {r : ℚ // 0 < r ∧ r ≤ 1}) => f (r : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨r, rfl⟩
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast r.2.1
    have hq_nonneg := h0 (θ + (((r : ℝ))⁻¹) • (x - θ))
    nlinarith [hr_pos, hq_nonneg]
  have hNonemptyRat : Nonempty {r : ℚ // 0 < r ∧ r ≤ 1} := by
    refine ⟨⟨(1 : ℚ), by norm_num, by norm_num⟩⟩
  have hull_eq : hull q θ x = ⨅ l : Set.Ioc (0 : ℝ) 1, f (l : ℝ) := by
    simp [hull, f]
  rw [hull_eq]
  apply le_antisymm
  · -- ≤ direction: real infimum ≤ rational infimum
    refine le_ciInf ?_
    intro r
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast r.2.1
    have hr_le : (r : ℝ) ≤ 1 := by exact_mod_cast r.2.2
    have hr_mem : (r : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨hr_pos, hr_le⟩
    let l : Set.Ioc (0 : ℝ) 1 := ⟨(r : ℝ), hr_mem⟩
    have hle : ⨅ l : Set.Ioc (0 : ℝ) 1, f (l : ℝ) ≤ f (l : ℝ) := ciInf_le hBddBelow l
    simpa using hle
  · -- ≥ direction: rational infimum ≤ real infimum
    refine le_ciInf ?_
    intro l
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    have hl_pos : 0 < (l : ℝ) := l.2.1
    have hl_le_one : (l : ℝ) ≤ 1 := l.2.2
    have h_cont_at : ContinuousAt f (l : ℝ) :=
      hf_cont_on_pos.continuousAt (isOpen_Ioi.mem_nhds hl_pos)
    have h_metric := Metric.continuousAt_iff.mp h_cont_at
    rcases h_metric ε hε with ⟨δ, hδ_pos, hδ⟩
    -- Pick δ' = min δ (l/2) so that l - δ' > 0
    let δ' := min δ ((l : ℝ) / 2)
    have hδ'_pos : 0 < δ' := by
      refine lt_min_iff.mpr ⟨hδ_pos, half_pos hl_pos⟩
    have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
    have hl_sub_δ'_pos : 0 < (l : ℝ) - δ' := by
      have : δ' ≤ (l : ℝ) / 2 := min_le_right _ _
      linarith
    have h_interval : (l : ℝ) - δ' < (l : ℝ) := by
      nlinarith
    rcases exists_rat_btwn (by nlinarith : (l : ℝ) - δ' < (l : ℝ)) with ⟨r, hr_low, hr_high⟩
    have hr_pos : 0 < (r : ℝ) := by linarith
    have hr_le_one : (r : ℝ) ≤ 1 := by linarith
    have hr_mem : (r : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨hr_pos, hr_le_one⟩
    let r' : {r : ℚ // 0 < r ∧ r ≤ 1} := ⟨r, by exact_mod_cast hr_pos, by exact_mod_cast hr_le_one⟩
    have h_dist : |(r : ℝ) - (l : ℝ)| < δ := by
      have : (l : ℝ) - δ' < (r : ℝ) := hr_low
      have : (r : ℝ) < (l : ℝ) := hr_high
      have h_abs : |(r : ℝ) - (l : ℝ)| < δ' := by
        rw [abs_lt]
        constructor <;> nlinarith
      nlinarith
    have h_f_dist : dist (f (r : ℝ)) (f (l : ℝ)) < ε := hδ h_dist
    have h_f_lt : f (r : ℝ) < f (l : ℝ) + ε := by
      have : f (r : ℝ) - f (l : ℝ) ≤ |f (r : ℝ) - f (l : ℝ)| := le_abs_self _
      have h_abs : |f (r : ℝ) - f (l : ℝ)| = dist (f (r : ℝ)) (f (l : ℝ)) := by rw [Real.dist_eq]
      rw [h_abs] at this
      linarith
    have h_inf_le : ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1}, f (r : ℝ) ≤ f (r : ℝ) :=
      ciInf_le hBddBelowRat r'
    linarith

/-! ## The Huber profile -/

theorem huber_convexOn (r₁ ε : ℝ) (hr : 0 ≤ r₁) : ConvexOn ℝ Set.univ (huber r₁ ε) := by
  have h_support (a s : ℝ) : huber r₁ ε a + min a r₁ * (s - a) ≤ huber r₁ ε s := by
    unfold huber
    by_cases ha : a ≤ r₁
    · have hmin : min a r₁ = a := min_eq_left ha
      rw [hmin]
      by_cases hs : s ≤ r₁
      · rw [if_pos ha, if_pos hs]
        nlinarith [sq_nonneg (s - a)]
      · have hs' : r₁ < s := by linarith
        rw [if_pos ha, if_neg hs]
        nlinarith [sq_nonneg (s - r₁), sq_nonneg (a - r₁)]
    · have hmin : min a r₁ = r₁ := min_eq_right (by linarith)
      rw [hmin]
      by_cases hs : s ≤ r₁
      · rw [if_neg ha, if_pos hs]
        nlinarith [sq_nonneg (s - r₁)]
      · have hs' : r₁ < s := by linarith
        rw [if_neg ha, if_neg hs]
        have h_eq : r₁ * a - r₁ ^ 2 / 2 + ε + r₁ * (s - a) = r₁ * s - r₁ ^ 2 / 2 + ε := by ring
        rw [h_eq]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp [smul_eq_mul] at *
  set z := a * x + b * y with hz_def
  set m := min z r₁ with hm_def
  have hz_ineq : huber r₁ ε z + m * (x - z) ≤ huber r₁ ε x := h_support z x
  have hz'_ineq : huber r₁ ε z + m * (y - z) ≤ huber r₁ ε y := h_support z y
  have hz_mul : a * (huber r₁ ε z + m * (x - z)) ≤ a * huber r₁ ε x :=
    mul_le_mul_of_nonneg_left hz_ineq ha
  have hz'_mul : b * (huber r₁ ε z + m * (y - z)) ≤ b * huber r₁ ε y :=
    mul_le_mul_of_nonneg_left hz'_ineq hb
  have h_add := add_le_add hz_mul hz'_mul
  have hsum : a * (x - z) + b * (y - z) = 0 := by
    calc
      a * (x - z) + b * (y - z) = (a * x + b * y) - (a + b) * z := by ring
      _ = z - (a + b) * z := by rw [hz_def]
      _ = z - 1 * z := by rw [hab]
      _ = 0 := by ring
  have h_eq : a * (huber r₁ ε z + m * (x - z)) + b * (huber r₁ ε z + m * (y - z)) =
      huber r₁ ε z := by
    calc
      a * (huber r₁ ε z + m * (x - z)) + b * (huber r₁ ε z + m * (y - z))
          = (a + b) * huber r₁ ε z + m * (a * (x - z) + b * (y - z)) := by ring
      _ = 1 * huber r₁ ε z + m * 0 := by rw [hab, hsum]
      _ = huber r₁ ε z := by ring
  rw [h_eq] at h_add
  exact h_add

theorem huber_monotoneOn (r₁ ε : ℝ) (hr : 0 ≤ r₁) : MonotoneOn (huber r₁ ε) (Set.Ici 0) := by
  intro a ha b hb hle
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  unfold huber
  split_ifs with ha1 hb1
  · -- both ≤ r₁: a²/2 + ε ≤ b²/2 + ε
    nlinarith
  · -- a ≤ r₁ < b: a²/2 + ε ≤ r₁*b - r₁²/2 + ε
    have : r₁ * r₁ ≤ r₁ * b := by nlinarith
    nlinarith
  · -- r₁ < a ≤ r₁ (impossible since a ≤ r₁)
    nlinarith
  · -- r₁ < a ≤ r₁ (impossible since b ≤ r₁)
    nlinarith

theorem huber_subgrad (r₁ ε a s : ℝ) (hr : 0 ≤ r₁) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    huber r₁ ε a + min a r₁ * (s - a) ≤ huber r₁ ε s := by
  unfold huber
  split_ifs with h₁ h₂
  · -- a ≤ r₁, s ≤ r₁
    have hmin : min a r₁ = a := min_eq_left h₁
    rw [hmin]
    nlinarith [sq_nonneg (s - a)]
  · -- a ≤ r₁, s > r₁
    have hmin : min a r₁ = a := min_eq_left h₁
    rw [hmin]
    nlinarith
  · -- a > r₁, s ≤ r₁
    have hmin : min a r₁ = r₁ := min_eq_right (by linarith)
    rw [hmin]
    nlinarith [sq_nonneg (s - r₁)]
  · -- a > r₁, s > r₁
    have hmin : min a r₁ = r₁ := min_eq_right (by linarith)
    rw [hmin]
    ring_nf
    rfl

theorem huber_sub_le (r₁ ε a b : ℝ) (hr : 0 ≤ r₁) (ha : 0 ≤ a) (hb : 0 ≤ b) (hle : a ≤ b) :
    huber r₁ ε b - huber r₁ ε a ≤ r₁ * (b - a) := by
  dsimp [huber]
  split_ifs with ha_le hb_le
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem huber_lipschitz (r₁ ε a b : ℝ) (hr : 0 ≤ r₁) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |huber r₁ ε a - huber r₁ ε b| ≤ r₁ * |a - b| := by
  rcases le_total a b with (hle | hle)
  · have habs : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    rw [habs]
    have h_huber_le : huber r₁ ε a ≤ huber r₁ ε b := by
      dsimp [huber]
      split_ifs with ha_le hb_le
      · nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
    have h_nonpos : huber r₁ ε a - huber r₁ ε b ≤ 0 := sub_nonpos.mpr h_huber_le
    rw [abs_of_nonpos h_nonpos]
    simpa [neg_sub] using huber_sub_le r₁ ε a b hr ha hb hle
  · have habs : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hle)
    rw [habs]
    have h_huber_le : huber r₁ ε b ≤ huber r₁ ε a := by
      dsimp [huber]
      split_ifs with hb_le ha_le
      · nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
    have h_nonneg : 0 ≤ huber r₁ ε a - huber r₁ ε b := sub_nonneg.mpr h_huber_le
    rw [abs_of_nonneg h_nonneg]
    exact huber_sub_le r₁ ε b a hr hb ha hle


theorem huber_ge (r₁ ε a : ℝ) (hr : 0 ≤ r₁) : ε ≤ huber r₁ ε a := by
  unfold huber
  split_ifs with h
  · nlinarith
  · nlinarith

theorem huber_le_lin (r₁ ε a : ℝ) (ha : 0 ≤ a) : huber r₁ ε a ≤ r₁ * a + ε := by
  unfold huber
  split_ifs with h
  · -- a ≤ r₁: need a^2/2 + ε ≤ r₁*a + ε
    nlinarith
  · -- r₁ < a: need r₁*a - r₁^2/2 + ε ≤ r₁*a + ε
    nlinarith

/-! ## The bowl -/

theorem bowl_convexOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r₁) : ConvexOn ℝ Set.univ (bowl A m κ ε r₁) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp [bowl]
  have h_affine : (a • x + b • y) - m = a • (x - m) + b • (y - m) := by
    calc
      (a • x + b • y) - m = (a • x + b • y) - ((a + b) • m) := by rw [hab, one_smul]
      _ = (a • x + b • y) - (a • m + b • m) := by rw [add_smul]
      _ = (a • x - a • m) + (b • y - b • m) := by abel
      _ = a • (x - m) + b • (y - m) := by simp [smul_sub]
  have h_norm_convex : ‖A ((a • x + b • y) - m)‖ ≤ a • ‖A (x - m)‖ + b • ‖A (y - m)‖ := by
    rw [h_affine]
    calc
      ‖A (a • (x - m) + b • (y - m))‖ = ‖a • A (x - m) + b • A (y - m)‖ := by simp
      _ ≤ ‖a • A (x - m)‖ + ‖b • A (y - m)‖ := norm_add_le _ _
      _ = a • ‖A (x - m)‖ + b • ‖A (y - m)‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        simp [smul_eq_mul]
  have h_nonneg_sum : 0 ≤ a • ‖A (x - m)‖ + b • ‖A (y - m)‖ := by
    have hx' : 0 ≤ ‖A (x - m)‖ := norm_nonneg _
    have hy' : 0 ≤ ‖A (y - m)‖ := norm_nonneg _
    positivity
  have h_huber_mono : huber r₁ ε ‖A ((a • x + b • y) - m)‖ ≤
      huber r₁ ε (a • ‖A (x - m)‖ + b • ‖A (y - m)‖) :=
    huber_monotoneOn r₁ ε hr (norm_nonneg _) h_nonneg_sum h_norm_convex
  have h_huber_convex : huber r₁ ε (a • ‖A (x - m)‖ + b • ‖A (y - m)‖) ≤
      a • huber r₁ ε ‖A (x - m)‖ + b • huber r₁ ε ‖A (y - m)‖ :=
    (huber_convexOn r₁ ε hr).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  calc
    κ * huber r₁ ε ‖A ((a • x + b • y) - m)‖
        ≤ κ * huber r₁ ε (a • ‖A (x - m)‖ + b • ‖A (y - m)‖) :=
      mul_le_mul_of_nonneg_left h_huber_mono hκ
    _ ≤ κ * (a • huber r₁ ε ‖A (x - m)‖ + b • huber r₁ ε ‖A (y - m)‖) :=
      mul_le_mul_of_nonneg_left h_huber_convex hκ
    _ = a • (κ * huber r₁ ε ‖A (x - m)‖) + b • (κ * huber r₁ ε ‖A (y - m)‖) := by
      ring

theorem bowl_ge {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r₁) (x : V) : κ * ε ≤ bowl A m κ ε r₁ x := by
  unfold bowl
  exact mul_le_mul_of_nonneg_left (huber_ge r₁ ε _ hr) hκ

theorem bowl_lipschitz {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r₁) (x y : V) :
    |bowl A m κ ε r₁ x - bowl A m κ ε r₁ y| ≤ κ * r₁ * ‖A‖ * ‖x - y‖ := by
  dsimp [bowl]
  have hsub : κ * huber r₁ ε ‖A (x - m)‖ - κ * huber r₁ ε ‖A (y - m)‖ =
      κ * (huber r₁ ε ‖A (x - m)‖ - huber r₁ ε ‖A (y - m)‖) := by ring
  rw [hsub, abs_mul, abs_of_nonneg hκ]
  have hh := huber_lipschitz r₁ ε ‖A (x - m)‖ ‖A (y - m)‖ hr (norm_nonneg _) (norm_nonneg _)
  have hineq1 : κ * |huber r₁ ε ‖A (x - m)‖ - huber r₁ ε ‖A (y - m)‖| ≤
      κ * (r₁ * |‖A (x - m)‖ - ‖A (y - m)‖|) :=
    mul_le_mul_of_nonneg_left hh hκ
  refine le_trans hineq1 ?_
  have habs : |‖A (x - m)‖ - ‖A (y - m)‖| ≤ ‖A (x - m) - A (y - m)‖ :=
    abs_norm_sub_norm_le _ _
  have hnorm : ‖A (x - m) - A (y - m)‖ ≤ ‖A‖ * ‖x - y‖ := by
    rw [← map_sub A (x - m) (y - m), sub_sub_sub_cancel_right]
    exact ContinuousLinearMap.le_opNorm A (x - y)
  have hinner1 : r₁ * |‖A (x - m)‖ - ‖A (y - m)‖| ≤ r₁ * ‖A (x - m) - A (y - m)‖ :=
    mul_le_mul_of_nonneg_left habs hr
  have hinner2 : r₁ * ‖A (x - m) - A (y - m)‖ ≤ r₁ * (‖A‖ * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left hnorm hr
  have h_mid : κ * (r₁ * |‖A (x - m)‖ - ‖A (y - m)‖|) ≤ κ * (r₁ * (‖A‖ * ‖x - y‖)) := by
    apply mul_le_mul_of_nonneg_left ?_ hκ
    exact le_trans hinner1 hinner2
  have h_final : κ * (r₁ * (‖A‖ * ‖x - y‖)) = κ * r₁ * ‖A‖ * ‖x - y‖ := by ring
  rw [← h_final]
  exact h_mid

theorem bowl_subgrad {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r₁) (x y : V) :
    bowl A m κ ε r₁ x + κ * slope A m r₁ x * ⟪A (x - m), A (y - x)⟫ ≤ bowl A m κ ε r₁ y := by
  set z := A (x - m) with hz
  set w := A (y - m) with hw
  have hsub : A (y - x) = w - z := by
    calc
      A (y - x) = A ((y - m) - (x - m)) := by abel
      _ = A (y - m) - A (x - m) := by rw [A.map_sub]
      _ = w - z := by rw [hz, hw]
  have haz : 0 ≤ ‖z‖ := norm_nonneg _
  have hsw : 0 ≤ ‖w‖ := norm_nonneg _
  rw [hsub]
  dsimp [bowl, slope]
  rw [← hz, ← hw]
  have hinner : ⟪z, w - z⟫ ≤ ‖z‖ * (‖w‖ - ‖z‖) := by
    have h1 : ⟪z, w - z⟫ = ⟪z, w⟫ - ‖z‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have h2 : ⟪z, w⟫ ≤ ‖z‖ * ‖w‖ := real_inner_le_norm _ _
    have h3 : ‖z‖ * ‖w‖ - ‖z‖ ^ 2 = ‖z‖ * (‖w‖ - ‖z‖) := by ring
    rw [h1]
    nlinarith
  by_cases ha : ‖z‖ ≤ r₁
  · rw [if_pos ha]
    have hmin : min ‖z‖ r₁ = ‖z‖ := min_eq_left ha
    have hkey_raw : huber r₁ ε ‖z‖ + min ‖z‖ r₁ * (‖w‖ - ‖z‖) ≤ huber r₁ ε ‖w‖ :=
      huber_subgrad r₁ ε ‖z‖ ‖w‖ hr haz hsw
    have hkey : huber r₁ ε ‖z‖ + ‖z‖ * (‖w‖ - ‖z‖) ≤ huber r₁ ε ‖w‖ := by
      rw [hmin] at hkey_raw
      exact hkey_raw
    have hinner_bound : ⟪z, w - z⟫ ≤ ‖z‖ * (‖w‖ - ‖z‖) := hinner
    nlinarith
  · rw [if_neg (by linarith : ¬ ‖z‖ ≤ r₁)]
    have ha_pos : 0 < ‖z‖ := by
      by_contra! H
      have hz0 : ‖z‖ = 0 := by linarith
      have : r₁ < 0 := by linarith
      linarith [hr, this]
    have hmin : min ‖z‖ r₁ = r₁ := min_eq_right (by linarith)
    have hkey_raw : huber r₁ ε ‖z‖ + min ‖z‖ r₁ * (‖w‖ - ‖z‖) ≤ huber r₁ ε ‖w‖ :=
      huber_subgrad r₁ ε ‖z‖ ‖w‖ hr haz hsw
    have hkey : huber r₁ ε ‖z‖ + r₁ * (‖w‖ - ‖z‖) ≤ huber r₁ ε ‖w‖ := by
      rw [hmin] at hkey_raw
      exact hkey_raw
    have hinner_bound : (r₁ / ‖z‖) * ⟪z, w - z⟫ ≤ (r₁ / ‖z‖) * (‖z‖ * (‖w‖ - ‖z‖)) := by
      have hdiv : 0 ≤ r₁ / ‖z‖ := div_nonneg hr (by linarith)
      exact mul_le_mul_of_nonneg_left hinner hdiv
    have hsimpl : (r₁ / ‖z‖) * (‖z‖ * (‖w‖ - ‖z‖)) = r₁ * (‖w‖ - ‖z‖) := by
      field_simp [ne_of_gt ha_pos]
    rw [hsimpl] at hinner_bound
    nlinarith

theorem bowl_sub_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hr : 0 < r₁) (θ x : V) :
    bowl A m κ ε r₁ x - κ * slope A m r₁ x * ⟪A (x - m), A (x - θ)⟫ = κ * hgen A m ε r₁ θ x := by
  set z := A (x - m) with hz
  set p := A (θ - m) with hp
  set a := ‖z‖ with ha
  have hz_sub : A (x - θ) = z - p := by
    calc
      A (x - θ) = A ((x - m) - (θ - m)) := by abel
      _ = A (x - m) - A (θ - m) := by rw [A.map_sub]
      _ = z - p := by rw [hz, hp]
  have ha_sq : ⟪z, z⟫ = a ^ 2 := by
    rw [ha, real_inner_self_eq_norm_sq]
  have ha_pos (h : ¬ a ≤ r₁) : a ≠ 0 := by
    have ha_gt : r₁ < a := by linarith
    have ha_nonneg : 0 ≤ a := norm_nonneg _
    linarith
  have h_inner_sub : ⟪z, z - p⟫ = a ^ 2 - ⟪z, p⟫ := by
    rw [inner_sub_right, ha_sq]
  unfold bowl slope hgen hq readT huber
  rw [← hz, ← hp, ← ha, hz_sub, h_inner_sub]
  split_ifs with hle
  · -- case ‖z‖ ≤ r₁
    ring
  · -- case r₁ < ‖z‖
    have haz : a ≠ 0 := ha_pos hle
    field_simp [haz]
    ring

theorem continuous_bowl {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) : Continuous (bowl A m κ ε r₁) := by
  have h_huber : Continuous (huber r₁ ε) := by
    -- huber r₁ ε r = if r ≤ r₁ then r^2/2 + ε else r₁*r - r₁^2/2 + ε
    -- Use Continuous.if_le with f(r)=r, g(r)=r₁, f'(r)=r^2/2+ε, g'(r)=r₁*r - r₁^2/2+ε
    refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · -- f'(r) = r^2/2 + ε is continuous
      refine (continuous_id.pow 2).div_const 2 |>.add continuous_const
    · -- g'(r) = r₁*r - r₁^2/2 + ε is continuous
      refine ((continuous_const.mul continuous_id).sub ?_).add continuous_const
      exact (continuous_const.mul continuous_const).div_const 2
    · -- f(r) = r is continuous
      exact continuous_id
    · -- g(r) = r₁ is continuous
      exact continuous_const
    · -- agreement at boundary r = r₁
      intro r hr
      rw [hr]
      ring
  have h_norm_comp : Continuous fun (x : V) => ‖A (x - m)‖ := by
    refine Continuous.norm ?_
    exact A.continuous.comp (continuous_id.sub continuous_const)
  have h_bowl : Continuous (bowl A m κ ε r₁) := by
    -- bowl A m κ ε r₁ x = κ * huber r₁ ε ‖A (x - m)‖
    -- So it's κ * (huber r₁ ε ∘ (fun x => ‖A (x - m)‖))
    have : bowl A m κ ε r₁ = fun x => κ * huber r₁ ε ‖A (x - m)‖ := by
      ext x; rfl
    rw [this]
    exact continuous_const.mul (h_huber.comp h_norm_comp)
  exact h_bowl

/-! ## Lemma D -/

/-- Lemma D (a): the dent is convex. -/
theorem dent_convexOn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ : V) :
    ConvexOn ℝ Set.univ (dent A m κ ε r₁ θ) := by
  have h_bowl_convex : ConvexOn ℝ Set.univ (bowl A m κ ε r₁) :=
    bowl_convexOn A m κ ε r₁ hκ hr
  have h_bowl_nonneg : ∀ x, 0 ≤ bowl A m κ ε r₁ x := by
    intro x
    have h := bowl_ge A m κ ε r₁ hκ hr x
    have h_nonneg_prod : 0 ≤ κ * ε := mul_nonneg hκ hε
    linarith
  have h_dent_eq : dent A m κ ε r₁ θ = hull (bowl A m κ ε r₁) θ := rfl
  rw [h_dent_eq]
  exact hull_convexOn (bowl A m κ ε r₁) θ h_bowl_convex h_bowl_nonneg

/-- Lemma D (a): `0 ≤ D`. -/
theorem dent_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x : V) : 0 ≤ dent A m κ ε r₁ θ x := by
  unfold dent
  apply hull_nonneg (bowl A m κ ε r₁) θ x
  intro y
  dsimp [bowl]
  have h_huber_nonneg : 0 ≤ huber r₁ ε ‖A (y - m)‖ := by
    dsimp [huber]
    split
    · nlinarith
    · nlinarith
  nlinarith

/-- Lemma D (a): `D ≤ q`. -/
theorem dent_le_bowl {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x : V) :
    dent A m κ ε r₁ θ x ≤ bowl A m κ ε r₁ x := by
  unfold dent
  apply hull_le
  intro y
  have hbowl := bowl_ge A m κ ε r₁ hκ hr y
  have hnonneg : 0 ≤ κ * ε := mul_nonneg hκ hε
  linarith

/-- Lemma D (a): `D(θ; θ) = 0`. -/
theorem dent_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ : V) : dent A m κ ε r₁ θ θ = 0 := by
  unfold dent
  apply hull_self
  intro y
  have hbowl := bowl_ge A m κ ε r₁ hκ hr y
  have hnonneg : 0 ≤ κ * ε := mul_nonneg hκ hε
  linarith

/-- Lemma D (b): the dent has the Lipschitz constant `κ r₁ ‖M^{1/2}‖` of the bowl. -/
theorem dent_lipschitz {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x y : V) :
    |dent A m κ ε r₁ θ x - dent A m κ ε r₁ θ y| ≤ κ * r₁ * ‖A‖ * ‖x - y‖ := by
  unfold dent
  refine hull_lipschitz (bowl A m κ ε r₁) θ (κ * r₁ * ‖A‖) ?h0 ?hK x y
  · intro y
    have hge : κ * ε ≤ bowl A m κ ε r₁ y := bowl_ge A m κ ε r₁ hκ hr y
    have hke : 0 ≤ κ * ε := mul_nonneg hκ hε
    linarith
  · intro y z
    have h := bowl_lipschitz A m κ ε r₁ hκ hr y z
    simpa [mul_assoc] using h

/-- The scalar bounds on `dev` of Lemma D (c): `0 ≤ dev ≤ min(h, 2h²/ρ²)` for `0 ≤ h ≤ ρ²/2`. -/
theorem devq_bounds (ρ h : ℝ) (hρ : 0 < ρ) (h0 : 0 ≤ h) (h1 : h ≤ ρ ^ 2 / 2) :
    0 ≤ devq ρ h ∧ devq ρ h ≤ h ∧ devq ρ h ≤ 2 * h ^ 2 / ρ ^ 2 := by
  have hρ_sq_pos : 0 < ρ ^ 2 := pow_pos hρ 2
  have h_nonneg_sq : 0 ≤ ρ ^ 2 - 2 * h := by nlinarith
  set s := Real.sqrt (ρ ^ 2 - 2 * h) with hs_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = ρ ^ 2 - 2 * h := Real.sq_sqrt h_nonneg_sq
  have hs_le_rho : s ≤ ρ := by
    calc
      s = Real.sqrt (ρ ^ 2 - 2 * h) := rfl
      _ ≤ Real.sqrt (ρ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = |ρ| := Real.sqrt_sq_eq_abs _
      _ = ρ := abs_of_pos hρ
  have h_eq : devq ρ h = (ρ - s) ^ 2 / 2 := by
    dsimp [devq]
    rw [← hs_def]
    have hh : h = (ρ ^ 2 - s ^ 2) / 2 := by linarith
    rw [hh]
    ring
  have h0_devq : 0 ≤ devq ρ h := by
    rw [h_eq]
    nlinarith [sq_nonneg (ρ - s)]
  have h1_devq : devq ρ h ≤ h := by
    rw [h_eq]
    have hh : h = (ρ ^ 2 - s ^ 2) / 2 := by linarith
    rw [hh]
    have h_diff_nonneg : 0 ≤ ρ - s := by nlinarith
    nlinarith
  have h2_devq : devq ρ h ≤ 2 * h ^ 2 / ρ ^ 2 := by
    rw [h_eq]
    have hh : h = (ρ ^ 2 - s ^ 2) / 2 := by linarith
    rw [hh]
    field_simp [hρ_sq_pos.ne']
    nlinarith [sq_nonneg s]
  exact And.intro h0_devq (And.intro h1_devq h2_devq)

/-- The dent on the ray from `θ` through `x`, `t = |x - θ|_M`: `κ (ρ t + ⟨θ - m, x - θ⟩_M)` for `t ≤ ρ`, the bowl
beyond (the computation behind Lemma D (c)). -/
theorem dent_formula {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (θ x : V)
    (hθ : ‖A (θ - m)‖ + rho A m ε θ ≤ r₁) :
    dent A m κ ε r₁ θ x = if ‖A (x - m) - A (θ - m)‖ ≤ rho A m ε θ then
      κ * (rho A m ε θ * ‖A (x - m) - A (θ - m)‖ + ⟪A (θ - m), A (x - m) - A (θ - m)⟫)
      else bowl A m κ ε r₁ x := by
  set p := A (θ - m) with hp
  set z := A (x - m) with hz
  set ρ := rho A m ε θ with hρdef
  set t := ‖z - p‖ with ht
  have hρ2 : ρ ^ 2 = ‖p‖ ^ 2 + 2 * ε := Real.sq_sqrt (by positivity)
  have hρpos : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hr : 0 ≤ r₁ := by have := norm_nonneg p; linarith
  have h0 : ∀ y, 0 ≤ bowl A m κ ε r₁ y := fun y =>
    le_trans (mul_nonneg hκ.le hε.le) (bowl_ge A m κ ε r₁ hκ.le hr y)
  have hxθ : A (x - θ) = z - p := by
    rw [hz, hp, ← map_sub]; congr 1; abel
  rcases (norm_nonneg (z - p)).eq_or_lt with ht0 | htpos
  · -- t = 0: the hull of a function constant along the ray
    have hzp : z - p = 0 := norm_eq_zero.1 ht0.symm
    have ht0' : t = 0 := ht0.symm
    simp only [ht0', hρpos.le, ↓reduceIte, hzp, inner_zero_right, mul_zero, zero_add]
    have hterm : ∀ l : ℝ, bowl A m κ ε r₁ (θ + l⁻¹ • (x - θ)) = bowl A m κ ε r₁ θ := by
      intro l
      unfold bowl
      congr 3
      rw [show θ + l⁻¹ • (x - θ) - m = (θ - m) + l⁻¹ • (x - θ) by abel, map_add, map_smul, hxθ, hzp,
        smul_zero, add_zero]
    unfold dent hull
    simp_rw [hterm]
    exact iInf_Ioc_mul_const _ (h0 θ)
  · -- t > 0: the ray from θ through x
    set e : V := t⁻¹ • (z - p) with he
    set v : V := t⁻¹ • (x - θ) with hv
    have htne : t ≠ 0 := htpos.ne'
    have hxv : θ + t • v = x := by
      rw [hv, smul_smul, mul_inv_cancel₀ htne, one_smul]; abel
    have hAv : A v = e := by rw [hv, map_smul, hxθ]
    have he1 : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, ← ht, inv_mul_cancel₀ htne]
    clear_value v e
    have hAτ : ∀ τ : ℝ, A (θ + τ • v - m) = p + τ • e := by
      intro τ
      rw [show θ + τ • v - m = (θ - m) + τ • v by abel, map_add, map_smul, hAv]
    have hnorm2 : ∀ τ : ℝ, ‖p + τ • e‖ ^ 2 = ‖p‖ ^ 2 + 2 * τ * ⟪p, e⟫ + τ ^ 2 := by
      intro τ
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he1]
      ring
    have hsmall : ∀ τ : ℝ, 0 ≤ τ → τ ≤ ρ →
        bowl A m κ ε r₁ (θ + τ • v) = κ * (τ ^ 2 / 2 + τ * ⟪p, e⟫ + ρ ^ 2 / 2) := by
      intro τ hτ0 hτ
      have hle : ‖p + τ • e‖ ≤ r₁ := by
        calc ‖p + τ • e‖ ≤ ‖p‖ + ‖τ • e‖ := norm_add_le _ _
          _ = ‖p‖ + τ := by rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_nonneg hτ0]
          _ ≤ r₁ := by linarith
      unfold bowl huber
      rw [hAτ, ite_eq_left hle, hnorm2, hρ2]
      ring
    have hconv : ConvexOn ℝ (Set.Ioi 0) (fun τ : ℝ => bowl A m κ ε r₁ (θ + τ • v)) := by
      refine ⟨convex_Ioi 0, fun τ₁ _ τ₂ _ a b ha hb hab => ?_⟩
      have hcomb : θ + (a • τ₁ + b • τ₂) • v = a • (θ + τ₁ • v) + b • (θ + τ₂ • v) := by
        rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, smul_eq_mul, smul_eq_mul]
        have hθ' : θ = a • θ + b • θ := by rw [← add_smul, hab, one_smul]
        conv_lhs => rw [hθ']
        abel
      have := (bowl_convexOn A m κ ε r₁ hκ.le hr).2 (Set.mem_univ (θ + τ₁ • v))
        (Set.mem_univ (θ + τ₂ • v)) ha hb hab
      simpa only [hcomb] using this
    have hval : bowl A m κ ε r₁ (θ + ρ • v) / ρ = κ * (ρ + ⟪p, e⟫) := by
      rw [hsmall ρ hρpos.le le_rfl, div_eq_iff hρpos.ne']
      ring
    have htan : ∀ τ, 0 < τ → τ * (bowl A m κ ε r₁ (θ + ρ • v) / ρ) ≤ bowl A m κ ε r₁ (θ + τ • v) := by
      intro τ hτ
      have hs := bowl_subgrad A m κ ε r₁ hκ.le hr (θ + ρ • v) (θ + τ • v)
      have hle : ‖A (θ + ρ • v - m)‖ ≤ r₁ := by
        rw [hAτ]
        calc ‖p + ρ • e‖ ≤ ‖p‖ + ‖ρ • e‖ := norm_add_le _ _
          _ = ‖p‖ + ρ := by rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_of_pos hρpos]
          _ ≤ r₁ := hθ
      have hsl : slope A m r₁ (θ + ρ • v) = 1 := by unfold slope; rw [ite_eq_left hle]
      have hdiff : A (θ + τ • v - (θ + ρ • v)) = (τ - ρ) • e := by
        rw [show θ + τ • v - (θ + ρ • v) = (τ - ρ) • v by rw [sub_smul]; abel, map_smul, hAv]
      rw [hsl, hdiff, hAτ, inner_smul_right, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        he1, hsmall ρ hρpos.le le_rfl] at hs
      rw [hval]
      simp only [conj_trivial] at hs
      nlinarith [hs]
    have hray := hull_ray (bowl A m κ ε r₁) θ v ρ t hρpos htpos h0 hconv htan
    rw [hxv, hval] at hray
    unfold dent
    rw [hray]
    have hte : t * ⟪p, e⟫ = ⟪p, z - p⟫ := by
      rw [he, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ htne, one_mul]
    split_ifs
    · rw [← hte]; ring
    · rfl

/-- Lemma D (c), the closed form: if `|θ - m|_M + ρ(θ) ≤ r₁`, then `D = q` where `h ≤ 0`, and where `h > 0`,
`|x - m|_M ≤ r₁`, `h ≤ ρ²/2` and `D = q - κ dev`. -/
theorem dent_closed_form {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (θ x : V)
    (hθ : ‖A (θ - m)‖ + rho A m ε θ ≤ r₁) :
    (hq A m ε θ x ≤ 0 → dent A m κ ε r₁ θ x = bowl A m κ ε r₁ x) ∧
      (0 < hq A m ε θ x → ‖A (x - m)‖ ≤ r₁ ∧ hq A m ε θ x ≤ rho A m ε θ ^ 2 / 2 ∧
        dent A m κ ε r₁ θ x = bowl A m κ ε r₁ x - κ * devq (rho A m ε θ) (hq A m ε θ x)) := by
  have hF := dent_formula A m κ ε r₁ hκ hε θ x hθ
  have hhq : hq A m ε θ x = ⟪A (x - m), A (θ - m)⟫ - ‖A (x - m)‖ ^ 2 / 2 + ε := rfl
  set p := A (θ - m) with hp
  set z := A (x - m) with hz
  set ρ := rho A m ε θ with hρdef
  have hρ2 : ρ ^ 2 = ‖p‖ ^ 2 + 2 * ε := Real.sq_sqrt (by positivity)
  have hρpos : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  set t := ‖z - p‖ with ht
  set h := hq A m ε θ x with hh
  have hz2 : ‖z‖ ^ 2 = ‖p‖ ^ 2 + 2 * ⟪p, z - p⟫ + t ^ 2 := by
    have := norm_add_sq_real p (z - p)
    rwa [show p + (z - p) = z by abel] at this
  have hinner : ⟪z, p⟫ = ⟪p, z - p⟫ + ‖p‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]; ring
  have ht2 : t ^ 2 = ρ ^ 2 - 2 * h := by
    rw [hhq, hρ2, hinner]; linarith
  have ht0 : 0 ≤ t := norm_nonneg _
  have hz_le : ‖z‖ ≤ ‖p‖ + t := by
    calc ‖z‖ = ‖p + (z - p)‖ := by rw [show p + (z - p) = z by abel]
      _ ≤ ‖p‖ + t := norm_add_le _ _
  have hbowl : t ≤ ρ → bowl A m κ ε r₁ x = κ * (ρ ^ 2 / 2 + ⟪p, z - p⟫ + t ^ 2 / 2) := by
    intro htρ
    have hle : ‖z‖ ≤ r₁ := by linarith
    unfold bowl huber
    rw [← hz, ite_eq_left hle, hz2, hρ2]
    ring
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · have hρt : ρ ≤ t := by nlinarith
    rw [hF]
    split_ifs with htρ
    · have heq : t = ρ := le_antisymm htρ hρt
      rw [hbowl htρ, heq]; ring
    · rfl
  · have htρ : t < ρ := by nlinarith
    refine ⟨by linarith, by nlinarith, ?_⟩
    rw [hF, ite_eq_left htρ.le, hbowl htρ.le]
    have hsq : Real.sqrt (ρ ^ 2 - 2 * h) = t := by rw [← ht2, Real.sqrt_sq ht0]
    unfold devq
    rw [hsq]
    nlinarith

/-- Lemma D (c), the form used by Lemma REGULAR: `q - κ 2 h₊²/ρ² ≤ D`, and `D = q` where `h ≤ 0`. -/
theorem dent_closed_form_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (θ x : V)
    (hθ : ‖A (θ - m)‖ + rho A m ε θ ≤ r₁) :
    bowl A m κ ε r₁ x - κ * (2 * max (hq A m ε θ x) 0 ^ 2 / rho A m ε θ ^ 2) ≤ dent A m κ ε r₁ θ x := by
  set h := hq A m ε θ x with hh
  set ρ := rho A m ε θ with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, rho]
    apply Real.sqrt_pos.mpr
    have hsq : 0 ≤ ‖A (θ - m)‖ ^ 2 := sq_nonneg _
    nlinarith
  have hdent_cases := dent_closed_form A m κ ε r₁ hκ hε θ x hθ
  rcases hdent_cases with ⟨hcase_le, hcase_gt⟩
  by_cases hh_le : h ≤ 0
  · have hmax : max h 0 = 0 := max_eq_right hh_le
    rw [hmax]
    simp
    rw [hcase_le hh_le]
  · have hhpos : 0 < h := by linarith
    have hmax : max h 0 = h := max_eq_left hhpos.le
    rw [hmax]
    rcases hcase_gt hhpos with ⟨hx_norm, hq_bound, hdent⟩
    have hdevq := devq_bounds ρ h hρpos (by linarith) hq_bound
    rcases hdevq with ⟨_, _, hdevq_bound⟩
    rw [hdent]
    have hineq : κ * devq ρ h ≤ κ * (2 * h ^ 2 / ρ ^ 2) :=
      mul_le_mul_of_nonneg_left hdevq_bound hκ.le
    have hneg : -(κ * (2 * h ^ 2 / ρ ^ 2)) ≤ -(κ * devq ρ h) := by linarith
    have h' := add_le_add_left hneg (bowl A m κ ε r₁ x)
    simpa [sub_eq_add_neg, add_comm] using h'

/-- Lemma D (d), the tangent bound, for every tip: `D(x; θ) ≥ q(x) - κ hgen(x, θ)₊`. -/
theorem dent_tangent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 < r₁) (θ x : V) :
    bowl A m κ ε r₁ x - κ * max (hgen A m ε r₁ θ x) 0 ≤ dent A m κ ε r₁ θ x := by
  unfold dent
  set s := κ * slope A m r₁ x * ⟪A (x - m), A (x - θ)⟫ with hs_def
  have h0 : ∀ y, 0 ≤ bowl A m κ ε r₁ y := by
    intro y
    have := bowl_ge A m κ ε r₁ hκ (by linarith) y
    have hκε : 0 ≤ κ * ε := mul_nonneg hκ hε
    linarith
  have hslope : bowl A m κ ε r₁ x - s = κ * hgen A m ε r₁ θ x := by
    calc
      bowl A m κ ε r₁ x - s = bowl A m κ ε r₁ x - κ * slope A m r₁ x * ⟪A (x - m), A (x - θ)⟫ := by
        rw [hs_def]
      _ = κ * hgen A m ε r₁ θ x := by rw [bowl_sub_tangent A m κ ε r₁ hr θ x]
  have hs : ∀ l : ℝ, 0 < l → l ≤ 1 → (bowl A m κ ε r₁) x + (l⁻¹ - 1) * s ≤ (bowl A m κ ε r₁) (θ + l⁻¹ • (x - θ)) := by
    intro l hlpos hle1
    have hy : θ + l⁻¹ • (x - θ) - x = (l⁻¹ - 1) • (x - θ) := by
      calc
        θ + l⁻¹ • (x - θ) - x = (θ - x) + l⁻¹ • (x - θ) := by abel
        _ = (l⁻¹ - 1) • (x - θ) := by
          rw [sub_smul, one_smul]
          abel
    have hinner : ⟪A (x - m), A (θ + l⁻¹ • (x - θ) - x)⟫ = (l⁻¹ - 1) * ⟪A (x - m), A (x - θ)⟫ := by
      rw [hy, map_smul, inner_smul_right]
    have hbowl := bowl_subgrad A m κ ε r₁ hκ (by linarith) x (θ + l⁻¹ • (x - θ))
    calc
      (bowl A m κ ε r₁) x + (l⁻¹ - 1) * s
          = bowl A m κ ε r₁ x + (l⁻¹ - 1) * (κ * slope A m r₁ x * ⟪A (x - m), A (x - θ)⟫) := rfl
      _ = bowl A m κ ε r₁ x + κ * slope A m r₁ x * ((l⁻¹ - 1) * ⟪A (x - m), A (x - θ)⟫) := by ring
      _ = bowl A m κ ε r₁ x + κ * slope A m r₁ x * ⟪A (x - m), A (θ + l⁻¹ • (x - θ) - x)⟫ := by rw [hinner]
      _ ≤ bowl A m κ ε r₁ (θ + l⁻¹ • (x - θ)) := hbowl
      _ = (bowl A m κ ε r₁) (θ + l⁻¹ • (x - θ)) := rfl
  have hge := hull_ge_of_slope (bowl A m κ ε r₁) θ x s h0 hs
  -- hge : bowl ... x - max (bowl ... x - s) 0 ≤ hull (bowl ...) θ x
  -- Since bowl x - s = κ * hgen, we have max (bowl x - s) 0 = max (κ * hgen) 0
  -- But we need κ * max hgen 0, not max (κ * hgen) 0
  -- Use: max (κ * a) 0 = κ * max a 0 when κ ≥ 0
  have hmax : max ((bowl A m κ ε r₁) x - s) 0 = κ * max (hgen A m ε r₁ θ x) 0 := by
    rw [hslope]
    by_cases hg : 0 ≤ hgen A m ε r₁ θ x
    · rw [max_eq_left (mul_nonneg hκ hg), max_eq_left hg, mul_comm κ]
    · have hg' : hgen A m ε r₁ θ x ≤ 0 := by linarith
      rw [max_eq_right (by nlinarith), max_eq_right hg', mul_zero]
  rw [hmax] at hge
  exact hge

/-- The identity `⟨x - m, θ - m⟩_M = a T`, `a = |x - m|_M` (both sides `0` at `a = 0`). -/
theorem inner_eq_norm_mul_readT {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (m θ x : V) : ⟪A (x - m), A (θ - m)⟫ = ‖A (x - m)‖ * readT A m θ x := by
  dsimp [readT]
  by_cases h : ‖A (x - m)‖ = 0
  · rw [h, zero_mul]
    rw [norm_eq_zero] at h
    rw [h, inner_zero_left]
  · field_simp [h]

/-- (d1), scalar form: `a T - a²/2 + k ≤ 2k` for `a ≥ 0`, `T ≤ (2k)^{1/2}`. -/
theorem d1_scalar (k a T : ℝ) (hk : 0 ≤ k) (ha : 0 ≤ a) (hT : T ≤ Real.sqrt (2 * k)) :
    a * T - a ^ 2 / 2 + k ≤ 2 * k := by
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
  have h_mul : a * T ≤ a * Real.sqrt (2 * k) :=
    mul_le_mul_of_nonneg_left hT ha
  have h_sq_nonneg : 0 ≤ (a - Real.sqrt (2 * k)) ^ 2 := sq_nonneg _
  have h_sqrt_sq : (Real.sqrt (2 * k)) ^ 2 = 2 * k := Real.sq_sqrt (by linarith)
  have h_ineq : a * Real.sqrt (2 * k) ≤ k + a ^ 2 / 2 := by
    nlinarith
  nlinarith

/-- (d1): `T ≤ (2k)^{1/2}` gives `hgen ≤ 2k` at every play. -/
theorem hgen_le_two_k {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (k r₁ : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r₁) (θ x : V)
    (hT : readT A m θ x ≤ Real.sqrt (2 * k)) : hgen A m k r₁ θ x ≤ 2 * k := by
  unfold hgen
  split
  · -- case ‖A (x - m)‖ ≤ r₁
    unfold hq
    rw [inner_eq_norm_mul_readT A m θ x]
    have ha : 0 ≤ ‖A (x - m)‖ := norm_nonneg _
    exact d1_scalar k (‖A (x - m)‖) (readT A m θ x) hk ha hT
  · -- case ¬ ‖A (x - m)‖ ≤ r₁
    exact d1_scalar k r₁ (readT A m θ x) hk hr hT

/-- (d2), scalar form. -/
theorem d2_scalar (k r₁ a T : ℝ) (hk : 0 < k) (hr : 0 ≤ r₁) (ha : 0 ≤ a) (hT : Real.sqrt (2 * k) < T) :
    min (max (if a ≤ r₁ then a * T - a ^ 2 / 2 + k else r₁ * T - r₁ ^ 2 / 2 + k) 0) (huber r₁ k a) ^ 2 ≤
      (4 * T ^ 2 + r₁ * T) * huber r₁ k a := by
  have hTpos : 0 < T := by
    have h_nonneg_sq : 0 ≤ 2 * k := by linarith
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
    linarith
  have hTsq_gt_2k : 2 * k < T ^ 2 :=
    Real.lt_sq_of_sqrt_lt hT
  have hk_lt_Tsq_div_2 : k < T ^ 2 / 2 := by linarith
  have h_huber_pos : 0 < huber r₁ k a := by
    unfold huber
    split
    · have ha_sq_nonneg : 0 ≤ a ^ 2 / 2 := by nlinarith
      nlinarith
    · have h_nonneg : 0 ≤ r₁ * a - r₁ ^ 2 / 2 := by nlinarith
      nlinarith
  have hRHS_nonneg : 0 ≤ 4 * T ^ 2 + r₁ * T := by nlinarith
  set φ := huber r₁ k a with hφ
  set M := max (if a ≤ r₁ then a * T - a ^ 2 / 2 + k else r₁ * T - r₁ ^ 2 / 2 + k) 0 with hM
  have hφ_pos : 0 < φ := h_huber_pos
  have hφ_nonneg : 0 ≤ φ := le_of_lt hφ_pos
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have h_min_sq_le_M_mul_φ : (min M φ) ^ 2 ≤ M * φ := by
    have h_min_le_M : min M φ ≤ M := min_le_left _ _
    have h_min_le_φ : min M φ ≤ φ := min_le_right _ _
    have h_min_nonneg : 0 ≤ min M φ := le_min hM_nonneg hφ_nonneg
    nlinarith
  have hM_le_RHS : M ≤ 4 * T ^ 2 + r₁ * T := by
    rw [hM]
    refine max_le ?_ hRHS_nonneg
    by_cases ha_le_r₁ : a ≤ r₁
    · simp [ha_le_r₁]
      by_cases ha_le_T : a ≤ T
      · have h_bound : a * T - a ^ 2 / 2 + k ≤ a * T + k := by nlinarith
        have h_aT_k_le : a * T + k ≤ 4 * T ^ 2 + r₁ * T := by nlinarith
        nlinarith
      · have h_bound : a * T - a ^ 2 / 2 + k ≤ T ^ 2 / 2 + k := by
          have h_eq : a * T - a ^ 2 / 2 = T ^ 2 / 2 - (a - T) ^ 2 / 2 := by ring
          nlinarith
        have h_lt : T ^ 2 / 2 + k < 4 * T ^ 2 + r₁ * T := by nlinarith
        nlinarith
    · simp [ha_le_r₁]
      nlinarith
  nlinarith

/-- (d2): `T > (2k)^{1/2}` gives `min(hgen₊, φ(a))² ≤ (4T² + r₁ T) φ(a)` at every play. -/
theorem hgen_tail {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V) (m : V)
    (k r₁ : ℝ) (hk : 0 < k) (hr : 0 ≤ r₁) (θ x : V) (hT : Real.sqrt (2 * k) < readT A m θ x) :
    min (max (hgen A m k r₁ θ x) 0) (huber r₁ k ‖A (x - m)‖) ^ 2 ≤
      (4 * readT A m θ x ^ 2 + r₁ * readT A m θ x) * huber r₁ k ‖A (x - m)‖ := by
  have h_inner : ⟪A (x - m), A (θ - m)⟫ = ‖A (x - m)‖ * readT A m θ x :=
    inner_eq_norm_mul_readT A m θ x
  unfold hgen huber hq
  rw [h_inner]
  exact d2_scalar k r₁ ‖A (x - m)‖ (readT A m θ x) hk hr (norm_nonneg _) hT

/-- The dent as an infimum over rational `λ ∈ (0, 1]` (the measurability lemma of the lower bound). -/
theorem dent_eq_iInf_rat {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A : V →L[ℝ] V)
    (m : V) (κ ε r₁ : ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (θ x : V) :
    dent A m κ ε r₁ θ x = ⨅ r : {r : ℚ // 0 < r ∧ r ≤ 1},
      ((r : ℚ) : ℝ) * bowl A m κ ε r₁ (θ + ((r : ℚ) : ℝ)⁻¹ • (x - θ)) := by
  rw [dent]
  refine hull_eq_iInf_rat (bowl A m κ ε r₁) (continuous_bowl A m κ ε r₁) θ x ?_
  intro y
  have h := bowl_ge A m κ ε r₁ hκ hr y
  have h_nonneg : 0 ≤ κ * ε := mul_nonneg hκ hε
  exact h_nonneg.trans h

end AdversarialBco.Lower
