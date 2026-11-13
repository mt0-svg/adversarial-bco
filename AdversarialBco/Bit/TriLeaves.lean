/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.SelfPos
public import AdversarialBco.Bit.PgBit
public import AdversarialBco.Poly.Df2SIFactsCore

@[expose] public section

/-!
# The position theorem, the leaves of the core

The definitions of the core of the position theorem: the subgradient selection `triU` of the gauge of a polytope given
by
rows (the subgradient lemma), the box `triBox` `BX(r, a, b)` of the triangular chart with its coordinate clip `triClip`,
the
loss `triLoss` and its subgradient `triV`. The leaves of the core theorem (Bit/TriCore.lean):

* the box: `tri_box_iff` (the box in terms of `μ` and the matrix), `tri_clip_mem`, `tri_clip_nonexp` (the clip is
  a nonexpansive retraction onto the box), `tri_box_convex`, `tri_avg_mem` (averages of points of the box),
  `tri_box_diam` (the diameter), `tri_det` (`det L = ∏ L_ii > 0` on the box), `tri_opNorm` (the operator norm on the
  box);
* the subgradient: `tri_subgrad` (`V` is a subgradient of the loss on the box), `tri_V_bound` (its norm),
  `tri_loss_meas`, `triU_meas`, `triU_spec` (the subgradient lemma: `triU` selects a subgradient of the gauge);
* the objective: `tri_gauge` (the gauge of a body containing the unit ball is `1`-Lipschitz and below the norm);
* the row (R): `tri_elo_le` (`e_lo ≤ e_h(ρ_h)`), `tri_row_main` (the four terms of the row against `e_lo`).

Each lemma sits in a namespace
`AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

open AdversarialBco.Poly

/-- The quotient `⟪α_k, z⟫/β_k` of row `k` at `z`. -/
noncomputable def triQ {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ) (k : Fin m)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (α k) z / β k

/-- The subgradient of the gauge of the polytope `{z | ⟪α_k, z⟫ ≤ β_k}` at `z` (the subgradient lemma): `α_k/β_k` for
the
least `k` at which the quotient is largest, when that quotient is positive, else `0`. -/
noncomputable def triU {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ k, if 0 < triQ α β k z ∧ (∀ k', triQ α β k' z ≤ triQ α β k z) ∧ (∀ k', k' < k → triQ α β k' z < triQ α β k z)
    then (β k)⁻¹ • α k else 0

end AdversarialBco.Bit

namespace AdversarialBco.Bit

open AdversarialBco.Poly

variable {d : ℕ}

/-- The lower ends of the box `BX(r, a, b)` on the coordinates of `PgSp d`: `-r` on `μ`, `-b` below the diagonal,
`a` on the diagonal, `0` above it. -/
noncomputable def triLo (r a b : ℝ) : Fin d ⊕ Fin d × Fin d → ℝ :=
  Sum.elim (fun _ => -r) (fun p => if p.2 < p.1 then -b else if p.1 = p.2 then a else 0)

/-- The upper ends of the box: `r` on `μ`, `b` on and below the diagonal, `0` above it. -/
noncomputable def triHi (r b : ℝ) : Fin d ⊕ Fin d × Fin d → ℝ :=
  Sum.elim (fun _ => r) (fun p => if p.2 ≤ p.1 then b else 0)

/-- The box `BX(r, a, b)`: `|μ_i| ≤ r`, `L` lower triangular, `a ≤ L_ii ≤ b`, `|L_ij| ≤ b` for `j < i`. -/
def triBox (d : ℕ) (r a b : ℝ) : Set (PgSp d) := {x | ∀ k, triLo r a b k ≤ x k ∧ x k ≤ triHi r b k}

/-- The coordinate clip onto the box. -/
noncomputable def triClip (r a b : ℝ) (x : PgSp d) : PgSp d :=
  WithLp.toLp 2 fun k => max (triLo r a b k) (min (triHi r b k) (x k))

/-- The loss `l(μ, L; y) = π(μ + L y) - (κ/d) Σ_i log L_ii` of Lemma TRI, for a function `π` (the gauge). -/
noncomputable def triLoss (π : EuclideanSpace ℝ (Fin d) → ℝ) (x : PgSp d) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  π (pgMu x + pgOp x y) - pgKappa / d * ∑ i, Real.log (pgMat x i i)

/-- The subgradient of the subgradient lemma, `V = (u, tril(u yᵀ) - (κ/d) diag(1/L_ii))`, `u = u(μ + L y)`. -/
noncomputable def triV (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : PgSp d)
    (y : EuclideanSpace ℝ (Fin d)) : PgSp d :=
  WithLp.toLp 2 (Sum.elim (fun i => u (pgMu x + pgOp x y) i)
    (fun p => (if p.2 ≤ p.1 then u (pgMu x + pgOp x y) p.1 * y p.2 else 0) -
      (if p.1 = p.2 then pgKappa / d / pgMat x p.1 p.1 else 0)))

end AdversarialBco.Bit

namespace AdversarialBco.Bit.Aux_tri_box_iff


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_box_iff {d : ℕ} (r a b : ℝ) (x : PgSp d) :
    x ∈ triBox d r a b ↔
      (∀ i, |pgMu x i| ≤ r) ∧ (∀ i j, i < j → pgMat x i j = 0) ∧ (∀ i, a ≤ pgMat x i i ∧ pgMat x i i ≤ b) ∧
        ∀ i j, j < i → |pgMat x i j| ≤ b := by
  constructor
  · intro h
    have hμ : ∀ i, |(pgMu x).ofLp i| ≤ r := by
      intro i
      have hi := h (Sum.inl i)
      simp [triLo, triHi, Sum.elim] at hi
      rcases hi with ⟨hl, hr⟩
      exact abs_le.mpr ⟨hl, hr⟩
    have hzero : ∀ i j, i < j → pgMat x i j = 0 := by
      intro i j hij
      have hij' := h (Sum.inr (i, j))
      simp [triLo, triHi, Sum.elim] at hij'
      rcases hij' with ⟨hl, hr⟩
      dsimp [pgMat]
      have hji : ¬ (j < i) := lt_asymm hij
      have heq : ¬ (i = j) := ne_of_lt hij
      have hle : ¬ (j ≤ i) := not_le.mpr hij
      rw [if_neg hji, if_neg heq] at hl
      rw [if_neg hle] at hr
      linarith
    have hdiag : ∀ i, a ≤ pgMat x i i ∧ pgMat x i i ≤ b := by
      intro i
      have hi := h (Sum.inr (i, i))
      simp [triLo, triHi, Sum.elim] at hi
      exact hi
    have hbelow : ∀ i j, j < i → |pgMat x i j| ≤ b := by
      intro i j hji
      have hji' := h (Sum.inr (i, j))
      simp [triLo, triHi, Sum.elim] at hji'
      rcases hji' with ⟨hl, hr⟩
      dsimp [pgMat]
      have hle : j ≤ i := le_of_lt hji
      rw [if_pos hji] at hl
      rw [if_pos hle] at hr
      exact abs_le.mpr ⟨hl, hr⟩
    exact ⟨hμ, hzero, hdiag, hbelow⟩
  · intro h
    rcases h with ⟨hμ, hzero, hdiag, hbelow⟩
    intro k
    rcases k with (i | ⟨i, j⟩)
    · -- vector case
      have hi := hμ i
      simp [pgMu] at hi
      rcases abs_le.mp hi with ⟨hl, hr⟩
      simp [triLo, triHi, Sum.elim, hl, hr]
    · -- matrix case
      rcases lt_trichotomy i j with (hij | heq | hji)
      · -- i < j
        have hzero' := hzero i j hij
        dsimp [pgMat] at hzero'
        dsimp [triLo, triHi, Sum.elim]
        have hji' : ¬ (j < i) := lt_asymm hij
        have heq' : ¬ (i = j) := ne_of_lt hij
        have hle' : ¬ (j ≤ i) := not_le.mpr hij
        rw [if_neg hji', if_neg heq', if_neg hle']
        simp [hzero']
      · -- i = j
        subst heq
        have hdiag' := hdiag i
        rcases hdiag' with ⟨hl, hr⟩
        dsimp [pgMat] at hl hr
        dsimp [triLo, triHi, Sum.elim]
        rw [if_neg (lt_irrefl i), if_pos rfl, if_pos (le_refl i)]
        exact ⟨hl, hr⟩
      · -- j < i
        have hbelow' := hbelow i j hji
        rcases abs_le.mp hbelow' with ⟨hl, hr⟩
        dsimp [pgMat] at hl hr
        dsimp [triLo, triHi, Sum.elim]
        have hle' : j ≤ i := le_of_lt hji
        rw [if_pos hji, if_pos hle']
        exact ⟨hl, hr⟩

end AdversarialBco.Bit.Aux_tri_box_iff

namespace AdversarialBco.Bit.Aux_tri_clip_mem


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_clip_mem {d : ℕ} (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b) (hb : 0 ≤ b) (x : PgSp d) :
    triClip r a b x ∈ triBox d r a b := by
  unfold triClip triBox
  intro k
  have h_triLo_le_triHi : triLo r a b k ≤ triHi r b k := by
    rcases k with (i | ⟨i, j⟩)
    · simp [triLo, triHi, hr]
    · simp [triLo, triHi]
      by_cases hji : j < i
      · simp [hji]
        have hle : j ≤ i := Nat.le_of_lt hji
        simp [hle]
        linarith
      · simp [hji]
        by_cases hij : i = j
        · simp [hij]
          exact hab
        · simp [hij]
          by_cases hji' : j ≤ i
          · simp [hji']
            linarith
          · simp [hji']
  constructor
  · exact le_max_left _ _
  · apply max_le h_triLo_le_triHi
    exact min_le_left _ _

end AdversarialBco.Bit.Aux_tri_clip_mem

namespace AdversarialBco.Bit.Aux_tri_clip_nonexp


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_clip_nonexp {d : ℕ} (r a b : ℝ) (y z : PgSp d) (hz : z ∈ triBox d r a b) :
    ‖triClip r a b y - z‖ ≤ ‖y - z‖ := by
  -- coordinate-wise inequality: for any lo, hi, x, z with lo ≤ z ≤ hi,
  -- |max lo (min hi x) - z| ≤ |x - z|
  have hclip {lo hi x z : ℝ} (hzl : lo ≤ z) (hzh : z ≤ hi) : |max lo (min hi x) - z| ≤ |x - z| := by
    have hlohi : lo ≤ hi := le_trans hzl hzh
    by_cases hxlo : x ≤ lo
    · have hmax : max lo (min hi x) = lo := by
        rw [min_eq_right (le_trans hxlo hlohi)]
        exact max_eq_left hxlo
      have hxz : x ≤ z := le_trans hxlo hzl
      have hgoal : |lo - z| ≤ |x - z| := by
        have hloz : lo - z ≤ 0 := sub_nonpos.mpr hzl
        have hxzz : x - z ≤ 0 := sub_nonpos.mpr hxz
        rw [abs_of_nonpos hloz, abs_of_nonpos hxzz]
        linarith
      rw [hmax]
      exact hgoal
    · by_cases hxhi : hi ≤ x
      · have hmax : max lo (min hi x) = hi := by
          rw [min_eq_left hxhi]
          exact max_eq_right hlohi
        have hzx : z ≤ x := le_trans hzh hxhi
        have hgoal : |hi - z| ≤ |x - z| := by
          have hhiz : 0 ≤ hi - z := sub_nonneg.mpr hzh
          have hxzz : 0 ≤ x - z := sub_nonneg.mpr hzx
          rw [abs_of_nonneg hhiz, abs_of_nonneg hxzz]
          linarith
        rw [hmax]
        exact hgoal
      · have hmax : max lo (min hi x) = x := by
          rw [min_eq_right (le_of_not_ge hxhi)]
          exact max_eq_right (le_of_not_ge hxlo)
        rw [hmax]
  -- get the coordinate-wise bounds from hz
  have hz_bounds (k : Fin d ⊕ Fin d × Fin d) : triLo r a b k ≤ z k ∧ z k ≤ triHi r b k := hz k
  -- square both sides: it suffices to compare squared norms
  have h_sq : ‖triClip r a b y - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    -- goal: ∑ i, ‖(triClip r a b y - z).ofLp i‖ ^ 2 ≤ ∑ i, ‖(y - z).ofLp i‖ ^ 2
    refine Finset.sum_le_sum ?_
    intro k _
    -- goal: ‖(triClip r a b y - z).ofLp k‖ ^ 2 ≤ ‖(y - z).ofLp k‖ ^ 2
    -- simplify: (triClip r a b y - z).ofLp k = (triClip r a b y) k - z k
    -- and (y - z).ofLp k = y k - z k
    -- and ‖·‖ on ℝ is |·|
    -- and (triClip r a b y) k = max (triLo r a b k) (min (triHi r b k) (y k))
    have hclip_eq : ‖(triClip r a b y - z).ofLp k‖ ^ 2 = |max (triLo r a b k) (min (triHi r b k) (y k)) - z k| ^ 2 := by
      simp [triClip]
    have hyz_eq : ‖(y - z).ofLp k‖ ^ 2 = |y k - z k| ^ 2 := by
      simp
    rw [hclip_eq, hyz_eq]
    -- goal: |max (triLo r a b k) (min (triHi r b k) (y k)) - z k| ^ 2 ≤ |y k - z k| ^ 2
    have h_abs := hclip (x := y k) (z := z k) (hz_bounds k).1 (hz_bounds k).2
    -- h_abs : |max (triLo r a b k) (min (triHi r b k) (y k)) - z k| ≤ |y k - z k|
    have h_nonneg₁ : 0 ≤ |max (triLo r a b k) (min (triHi r b k) (y k)) - z k| := abs_nonneg _
    have h_nonneg₂ : 0 ≤ |y k - z k| := abs_nonneg _
    nlinarith
  -- convert squared inequality back to norm inequality
  have h_nonneg₁ : 0 ≤ ‖triClip r a b y - z‖ := norm_nonneg _
  have h_nonneg₂ : 0 ≤ ‖y - z‖ := norm_nonneg _
  nlinarith

end AdversarialBco.Bit.Aux_tri_clip_nonexp

namespace AdversarialBco.Bit.Aux_tri_box_convex


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_box_convex (d : ℕ) (r a b : ℝ) : Convex ℝ (triBox d r a b) := by
  rw [convex_iff_add_mem]
  intro x hx y hy c d hc hd hsum k
  rcases hx k with ⟨hxlo, hxhi⟩
  rcases hy k with ⟨hylo, hyhi⟩
  have hlo : triLo r a b k ≤ (c • x + d • y) k := by
    calc
      triLo r a b k = (c + d) * triLo r a b k := by
        rw [hsum, one_mul]
      _ = c * triLo r a b k + d * triLo r a b k := by ring
      _ ≤ c * (x k) + d * (y k) := by
        nlinarith
      _ = (c • x + d • y) k := by
        simp [smul_eq_mul]
  have hhi : (c • x + d • y) k ≤ triHi r b k := by
    calc
      (c • x + d • y) k = c * (x k) + d * (y k) := by
        simp [smul_eq_mul]
      _ ≤ c * triHi r b k + d * triHi r b k := by
        nlinarith
      _ = (c + d) * triHi r b k := by ring
      _ = triHi r b k := by
        rw [hsum, one_mul]
  exact ⟨hlo, hhi⟩

end AdversarialBco.Bit.Aux_tri_box_convex

namespace AdversarialBco.Bit.Aux_tri_avg_mem


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_avg_mem {d : ℕ} (r a b : ℝ) (N : ℕ) (hN : 0 < N) (x : ℕ → PgSp d)
    (hx : ∀ t, x t ∈ triBox d r a b) : ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) ∈ triBox d r a b := by
  intro k
  have hlo : ∀ t, triLo r a b k ≤ x t k := by
    intro t
    exact ((hx t) k).1
  have hhi : ∀ t, x t k ≤ triHi r b k := by
    intro t
    exact ((hx t) k).2
  have hsum_lo : (N : ℝ) • triLo r a b k ≤ ∑ t ∈ Finset.range N, x t k := by
    calc
      (N : ℝ) • triLo r a b k = ∑ t ∈ Finset.range N, triLo r a b k := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range N, x t k := Finset.sum_le_sum fun t _ => hlo t
  have hsum_hi : ∑ t ∈ Finset.range N, x t k ≤ (N : ℝ) • triHi r b k := by
    calc
      ∑ t ∈ Finset.range N, x t k ≤ ∑ t ∈ Finset.range N, triHi r b k :=
        Finset.sum_le_sum fun t _ => hhi t
      _ = (N : ℝ) • triHi r b k := by
        simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpos_ne : (N : ℝ) ≠ 0 := by linarith
  have h_mul_inv : (N : ℝ)⁻¹ * (N : ℝ) = 1 := by field_simp [hpos_ne]
  have h_lower : triLo r a b k ≤ ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) k := by
    calc
      triLo r a b k = ((N : ℝ)⁻¹ * (N : ℝ)) • triLo r a b k := by
        rw [h_mul_inv, one_smul]
      _ = (N : ℝ)⁻¹ • ((N : ℝ) • triLo r a b k) := by rw [← smul_smul]
      _ ≤ (N : ℝ)⁻¹ • (∑ t ∈ Finset.range N, x t k) := by gcongr
      _ = ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) k := by
        simp [PiLp.smul_apply, Finset.sum_apply]
  have h_upper : ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) k ≤ triHi r b k := by
    calc
      ((N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, x t) k = (N : ℝ)⁻¹ • (∑ t ∈ Finset.range N, x t) k := by
        simp [PiLp.smul_apply]
      _ = (N : ℝ)⁻¹ • (∑ t ∈ Finset.range N, x t k) := by simp [Finset.sum_apply]
      _ ≤ (N : ℝ)⁻¹ • ((N : ℝ) • triHi r b k) := by gcongr
      _ = ((N : ℝ)⁻¹ * (N : ℝ)) • triHi r b k := by rw [smul_smul]
      _ = 1 • triHi r b k := by simp [h_mul_inv]
      _ = triHi r b k := by simp
  exact And.intro h_lower h_upper


end AdversarialBco.Bit.Aux_tri_avg_mem

namespace AdversarialBco.Bit.Aux_tri_box_diam


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

-- Helper lemma: sum of i.val over Fin d
private lemma sum_fin_val (d : ℕ) : (∑ i : Fin d, (i : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction' d with d ih
  · simp
  · rw [Fin.sum_univ_succ]
    simp [Fin.val_succ]
    simp_rw [Finset.sum_add_distrib]
    have h_sum_one : (∑ i : Fin d, (1 : ℝ)) = (d : ℝ) := by simp
    rw [h_sum_one, ih]
    ring

-- Helper lemma: cardinality of {j | j < i} in Fin d
private lemma card_filter_lt_eq_val {d : ℕ} (i : Fin d) :
    ((Finset.univ : Finset (Fin d)).filter (fun j => j < i)).card = i.val := by
  simpa using Fin.card_filter_val_lt (n := d) (m := i.val)

-- Helper lemma: sum of cardinalities
private lemma card_filter_lt_sum (d : ℕ) :
    (∑ i : Fin d, ((Finset.univ : Finset (Fin d)).filter (fun j => j < i)).card : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  simp [card_filter_lt_eq_val, sum_fin_val]

-- Helper lemma: tri_box_iff characterization
private lemma tri_box_iff {d : ℕ} (r a b : ℝ) (x : PgSp d) :
    x ∈ triBox d r a b ↔
      (∀ i, |pgMu x i| ≤ r) ∧ (∀ i j, i < j → pgMat x i j = 0) ∧ (∀ i, a ≤ pgMat x i i ∧ pgMat x i i ≤ b) ∧
        ∀ i j, j < i → |pgMat x i j| ≤ b := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hx := h (Sum.inl i)
      unfold triLo triHi at hx
      simp at hx
      rcases hx with ⟨hl, hr⟩
      exact abs_le.mpr ⟨hl, hr⟩
    · intro i j hij
      have htriLo : triLo r a b (Sum.inr (i, j)) = 0 := by
        dsimp [triLo]
        have h_not_ji : ¬ j < i := by
          intro hji; have := lt_trans hij hji; exact lt_irrefl _ this
        have h_ne : i ≠ j := by
          intro heq; have : i < i := heq ▸ hij; exact lt_irrefl _ this
        simp [h_not_ji, h_ne]
      have htriHi : triHi r b (Sum.inr (i, j)) = 0 := by
        dsimp [triHi]
        have h_not_ji_le : ¬ j ≤ i := by
          intro hji_le; have := lt_of_lt_of_le hij hji_le; exact lt_irrefl _ this
        simp [h_not_ji_le]
      have hx := h (Sum.inr (i, j))
      rw [htriLo, htriHi] at hx
      rcases hx with ⟨hl, hr⟩
      have heq : x (Sum.inr (i, j)) = 0 := by linarith
      dsimp [pgMat]
      rw [heq]
    · intro i
      have htriLo : triLo r a b (Sum.inr (i, i)) = a := by
        dsimp [triLo]
        simp
      have htriHi : triHi r b (Sum.inr (i, i)) = b := by
        dsimp [triHi]
        simp
      have hx := h (Sum.inr (i, i))
      rw [htriLo, htriHi] at hx
      rcases hx with ⟨hl, hr⟩
      dsimp [pgMat]
      exact ⟨hl, hr⟩
    · intro i j hji
      have htriLo : triLo r a b (Sum.inr (i, j)) = -b := by
        dsimp [triLo]
        simp [hji]
      have htriHi : triHi r b (Sum.inr (i, j)) = b := by
        dsimp [triHi]
        simp [le_of_lt hji]
      have hx := h (Sum.inr (i, j))
      rw [htriLo, htriHi] at hx
      rcases hx with ⟨hl, hr⟩
      dsimp [pgMat]
      exact abs_le.mpr ⟨hl, hr⟩
  · intro ⟨hμ, hL, hdiag, hoff⟩
    intro k
    rcases k with (i | ⟨i, j⟩)
    · -- k = Sum.inl i
      have hi := hμ i
      dsimp [triLo, triHi, pgMu] at hi ⊢
      exact abs_le.mp hi
    · -- k = Sum.inr (i, j)
      dsimp [triLo, triHi, pgMat]
      by_cases hji : j < i
      · -- j < i
        simp [hji, le_of_lt hji]
        have h := hoff i j hji
        dsimp [pgMat] at h
        exact abs_le.mp h
      · -- ¬ j < i
        have hle : i ≤ j := le_of_not_gt hji
        by_cases heq : i = j
        · -- i = j
          subst heq
          simp
          have h := hdiag i
          dsimp [pgMat] at h
          exact h
        · -- i ≠ j
          have hij : i < j := Ne.lt_of_le heq hle
          have h_not_ji_le : ¬ j ≤ i := by
            intro hji_le
            have := lt_of_lt_of_le hij hji_le
            exact lt_irrefl _ this
          simp [hji, heq, h_not_ji_le]
          have h := hL i j hij
          dsimp [pgMat] at h
          rw [h]
          exact ⟨by norm_num, by norm_num⟩

-- Helper lemma: sp_box_diam bound
private lemma sp_box_diam {d : ℕ} (r a b : ℝ) (μ μ' : Fin d → ℝ) (L L' : Matrix (Fin d) (Fin d) ℝ)
    (hμ : ∀ i, |μ i| ≤ r) (hμ' : ∀ i, |μ' i| ≤ r)
    (hL : ∀ i j, i < j → L i j = 0) (hL' : ∀ i j, i < j → L' i j = 0)
    (hdiag : ∀ i, a ≤ L i i ∧ L i i ≤ b) (hdiag' : ∀ i, a ≤ L' i i ∧ L' i i ≤ b)
    (hoff : ∀ i j, j < i → |L i j| ≤ b) (hoff' : ∀ i j, j < i → |L' i j| ≤ b) :
    ∑ i, (μ i - μ' i) ^ 2 + ∑ i, ∑ j, (L i j - L' i j) ^ 2 ≤
      4 * d * r ^ 2 + d * (b - a) ^ 2 + 2 * d * (d - 1) * b ^ 2 := by
  -- Part 1: bound the μ sum
  have hμsum : ∑ i : Fin d, (μ i - μ' i) ^ 2 ≤ 4 * (d : ℝ) * r ^ 2 := by
    calc
      ∑ i : Fin d, (μ i - μ' i) ^ 2 ≤ ∑ i : Fin d, (2 * r) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hiμ : |μ i| ≤ r := hμ i
        have hiμ' : |μ' i| ≤ r := hμ' i
        have hbound : |μ i - μ' i| ≤ 2 * r := by
          have h := abs_sub (μ i) (μ' i)
          have hsum : |μ i| + |μ' i| ≤ 2 * r := by linarith
          linarith
        have h_abs_sq : (μ i - μ' i) ^ 2 = |μ i - μ' i| ^ 2 := by
          simpa using (sq_abs (μ i - μ' i)).symm
        rw [h_abs_sq]
        have h_nonneg_abs : 0 ≤ |μ i - μ' i| := abs_nonneg _
        nlinarith
      _ = (d : ℝ) * ((2 * r) ^ 2) := by simp
      _ = 4 * (d : ℝ) * r ^ 2 := by ring
  -- Part 2: bound the matrix sum using pointwise inequality
  have hLsum : ∑ i : Fin d, ∑ j : Fin d, (L i j - L' i j) ^ 2 ≤ (d : ℝ) * (b - a) ^ 2 + 2 * (d : ℝ) * ((d : ℝ) - 1) * b ^ 2 := by
    have h_pointwise : ∀ i j : Fin d, (L i j - L' i j) ^ 2 ≤
        (if i = j then (b - a) ^ 2 else 0) + (if j < i then (2 * b) ^ 2 else 0) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have hdi := hdiag i
        have hdi' := hdiag' i
        rcases hdi with ⟨hlo, hhi⟩
        rcases hdi' with ⟨hlo', hhi'⟩
        have hbound : |L i i - L' i i| ≤ b - a := by
          have h_low : -(b - a) ≤ L i i - L' i i := by linarith
          have h_high : L i i - L' i i ≤ b - a := by linarith
          exact abs_le.mpr ⟨h_low, h_high⟩
        have h_abs_sq : (L i i - L' i i) ^ 2 = |L i i - L' i i| ^ 2 := by
          simpa using (sq_abs (L i i - L' i i)).symm
        rw [h_abs_sq]
        simp
        have h_nonneg_abs : 0 ≤ |L i i - L' i i| := abs_nonneg _
        nlinarith
      · by_cases hlt : i < j
        · -- i < j: both L and L' are zero
          have hLij : L i j = 0 := hL i j hlt
          have hL'ij : L' i j = 0 := hL' i j hlt
          have h_not_ji : ¬ j < i := by
            intro hji; have := lt_trans hlt hji; exact lt_irrefl _ this
          simp [hLij, hL'ij, hij, hlt, h_not_ji]
        · -- ¬ i < j and i ≠ j, so j < i
          have hle : j ≤ i := le_of_not_gt hlt
          have hji : j < i := Ne.lt_of_le (Ne.symm hij) hle
          have hLbound : |L i j| ≤ b := hoff i j hji
          have hL'bound : |L' i j| ≤ b := hoff' i j hji
          have hbound : |L i j - L' i j| ≤ 2 * b := by
            have h := abs_sub (L i j) (L' i j)
            have hsum : |L i j| + |L' i j| ≤ 2 * b := by linarith
            linarith
          have h_abs_sq : (L i j - L' i j) ^ 2 = |L i j - L' i j| ^ 2 := by
            simpa using (sq_abs (L i j - L' i j)).symm
          rw [h_abs_sq]
          simp [hij, hji]
          have h_nonneg_abs : 0 ≤ |L i j - L' i j| := abs_nonneg _
          nlinarith
    have h_sum : (∑ i : Fin d, ∑ j : Fin d, (L i j - L' i j) ^ 2) ≤
        (∑ i : Fin d, ∑ j : Fin d, ((if i = j then (b - a) ^ 2 else 0) + (if j < i then (2 * b) ^ 2 else 0))) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => h_pointwise i j))
    have h_rhs : (∑ i : Fin d, ∑ j : Fin d, ((if i = j then (b - a) ^ 2 else 0) + (if j < i then (2 * b) ^ 2 else 0))) =
        (d : ℝ) * (b - a) ^ 2 + 2 * (d : ℝ) * ((d : ℝ) - 1) * b ^ 2 := by
      -- Split the outer sum
      simp_rw [Finset.sum_add_distrib]
      -- Now: (∑ i, ∑ j, if i=j then ...) + (∑ i, ∑ j, if j<i then ...) = ...
      have h_diag : (∑ i : Fin d, ∑ j : Fin d, (if i = j then (b - a) ^ 2 else 0)) = (d : ℝ) * (b - a) ^ 2 := by
        simp
      have h_lower : (∑ i : Fin d, ∑ j : Fin d, (if j < i then (2 * b) ^ 2 else 0)) = 2 * (d : ℝ) * ((d : ℝ) - 1) * b ^ 2 := by
        calc
          (∑ i : Fin d, ∑ j : Fin d, (if j < i then (2 * b) ^ 2 else 0)) =
              (∑ i : Fin d, ((2 * b) ^ 2 * (((Finset.univ : Finset (Fin d)).filter (fun j => j < i)).card : ℝ))) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            rw [← Finset.sum_filter]
            simp [mul_comm]
          _ = (2 * b) ^ 2 * (∑ i : Fin d, ((Finset.univ : Finset (Fin d)).filter (fun j => j < i)).card : ℝ) := by
            simp [Finset.mul_sum]
          _ = (2 * b) ^ 2 * ((d : ℝ) * ((d : ℝ) - 1) / 2) := by rw [card_filter_lt_sum]
          _ = 2 * (d : ℝ) * ((d : ℝ) - 1) * b ^ 2 := by ring
      rw [h_diag, h_lower]
    linarith
  -- Combine μ sum and matrix sum
  have h_total := add_le_add hμsum hLsum
  linarith

theorem _root_.AdversarialBco.Bit.tri_box_diam {d : ℕ} (r a b Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ : 4 * d * r ^ 2 + d * (b - a) ^ 2 + 2 * d * (d - 1) * b ^ 2 ≤ Δ ^ 2) (x x' : PgSp d)
    (hx : x ∈ triBox d r a b) (hx' : x' ∈ triBox d r a b) : ‖x - x'‖ ≤ Δ := by
  -- Get the characterization of membership
  have hx_iff := (tri_box_iff r a b x).mp hx
  have hx'_iff := (tri_box_iff r a b x').mp hx'
  rcases hx_iff with ⟨hμ, hL, hdiag, hoff⟩
  rcases hx'_iff with ⟨hμ', hL', hdiag', hoff'⟩
  -- Norm decomposition: ‖x - x'‖^2 = ‖pgMu (x - x')‖^2 + ∑ i, ∑ j, pgMat (x - x') i j ^ 2
  have h_norm_sq : ‖x - x'‖ ^ 2 = ‖pgMu (x - x')‖ ^ 2 + ∑ i, ∑ j, pgMat (x - x') i j ^ 2 := by
    have h := EuclideanSpace.norm_sq_eq (x - x')
    rw [Fintype.sum_sum_type] at h
    have h1 : (∑ a₁ : Fin d, ‖(x - x').ofLp (Sum.inl a₁)‖ ^ 2) = ‖pgMu (x - x')‖ ^ 2 := by
      have h_pgMu := EuclideanSpace.norm_sq_eq (pgMu (x - x'))
      simpa [pgMu] using h_pgMu.symm
    have h2 : (∑ a₂ : Fin d × Fin d, ‖(x - x').ofLp (Sum.inr a₂)‖ ^ 2) = ∑ i, ∑ j, pgMat (x - x') i j ^ 2 := by
      rw [Fintype.sum_prod_type]
      simp [pgMat]
    rw [h1, h2] at h
    exact h
  -- Express pgMu (x - x') and pgMat (x - x') in terms of x and x'
  have h_pgMu_sub : pgMu (x - x') = pgMu x - pgMu x' := by
    ext i
    simp [pgMu]
  have h_pgMat_sub : pgMat (x - x') = pgMat x - pgMat x' := by
    ext i j
    simp [pgMat]
  rw [h_pgMu_sub, h_pgMat_sub] at h_norm_sq
  -- Now h_norm_sq: ‖x - x'‖^2 = ‖pgMu x - pgMu x'‖^2 + ∑ i, ∑ j, (pgMat x i j - pgMat x' i j)^2
  -- Use EuclideanSpace.norm_sq_eq for pgMu x - pgMu x'
  have h_pgMu_norm_sq : ‖pgMu x - pgMu x'‖ ^ 2 = ∑ i, (pgMu x i - pgMu x' i) ^ 2 := by
    have h := EuclideanSpace.norm_sq_eq (pgMu x - pgMu x')
    simpa using h
  rw [h_pgMu_norm_sq] at h_norm_sq
  -- Now h_norm_sq: ‖x - x'‖^2 = ∑ i, (pgMu x i - pgMu x' i)^2 + ∑ i, ∑ j, (pgMat x i j - pgMat x' i j)^2
  -- Apply sp_box_diam
  have h_bound : ∑ i, (pgMu x i - pgMu x' i) ^ 2 + ∑ i, ∑ j, (pgMat x i j - pgMat x' i j) ^ 2 ≤
      4 * d * r ^ 2 + d * (b - a) ^ 2 + 2 * d * (d - 1) * b ^ 2 :=
    sp_box_diam r a b (pgMu x) (pgMu x') (pgMat x) (pgMat x')
      hμ hμ' hL hL' hdiag hdiag' hoff hoff'
  -- Combine with hΔ
  have h_sq_le : ‖x - x'‖ ^ 2 ≤ Δ ^ 2 := by
    rw [h_norm_sq]
    apply le_trans h_bound
    exact hΔ
  -- From ‖x - x'‖^2 ≤ Δ^2 and 0 ≤ Δ, 0 ≤ ‖x - x'‖, deduce ‖x - x'‖ ≤ Δ
  have h_norm_nonneg : 0 ≤ ‖x - x'‖ := norm_nonneg _
  exact (pow_le_pow_iff_left₀ h_norm_nonneg hΔ0 (by norm_num : 2 ≠ 0)).mp h_sq_le

end AdversarialBco.Bit.Aux_tri_box_diam

namespace AdversarialBco.Bit.Aux_tri_det


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_det {d : ℕ} (r a b : ℝ) (ha : 0 < a) (x : PgSp d) (hx : x ∈ triBox d r a b) :
    (pgMat x).det = ∏ i, pgMat x i i ∧ 0 < (pgMat x).det ∧
      Real.log |(pgMat x).det| = ∑ i, Real.log (pgMat x i i) := by
  have hbox := (tri_box_iff r a b x).mp hx
  rcases hbox with ⟨h_mu_bound, h_lower_tri, h_diag, h_upper⟩
  have h_lower : (pgMat x).IsLowerTriangular := by
    intro i j h
    have : i < j := by
      simpa [OrderDual.toDual_lt_toDual] using h
    exact h_lower_tri i j this
  have h_det_formula : (pgMat x).det = ∏ i : Fin d, pgMat x i i :=
    det_of_isLowerTriangular _ h_lower
  have h_pos_diag : ∀ i, 0 < pgMat x i i := by
    intro i
    have ha_le : a ≤ pgMat x i i := (h_diag i).1
    linarith
  have h_prod_pos : 0 < ∏ i : Fin d, pgMat x i i :=
    Finset.prod_pos fun i _ => h_pos_diag i
  have h_det_pos : 0 < (pgMat x).det := by
    rw [h_det_formula]
    exact h_prod_pos
  have h_log_eq : Real.log |(pgMat x).det| = ∑ i : Fin d, Real.log (pgMat x i i) := by
    rw [abs_of_pos h_det_pos, h_det_formula]
    refine Real.log_prod (fun i hi => ?_)
    exact ne_of_gt (h_pos_diag i)
  exact And.intro h_det_formula (And.intro h_det_pos h_log_eq)

end AdversarialBco.Bit.Aux_tri_det

namespace AdversarialBco.Bit.Aux_tri_opNorm


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

-- Helper lemma: sum of (i.val + 1) over Fin d equals d*(d+1)/2
theorem sum_triangular (d : ℕ) : (∑ i : Fin d, ((i.val : ℝ) + 1)) = (d : ℝ) * ((d : ℝ) + 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    push_cast; ring

-- Helper lemma: number of j ≤ i is i.val + 1
theorem sum_ite_le {d : ℕ} (i : Fin d) : (∑ j : Fin d, if j ≤ i then (1 : ℝ) else 0) = (i.val : ℝ) + 1 := by
  rw [Finset.sum_boole]
  have h : (Finset.univ.filter (fun j : Fin d => j ≤ i)) = Finset.Iic i := by ext j; simp
  rw [h, Fin.card_Iic]; push_cast; ring

theorem _root_.AdversarialBco.Bit.tri_opNorm {d : ℕ} (r a b : ℝ) (ha : 0 ≤ a) (x : PgSp d) (hx : x ∈ triBox d r a b) :
    ‖pgOp x‖ ≤ b * Real.sqrt (d * (d + 1) / 2) := by
  by_cases hd0 : d = 0
  · subst hd0; simp [PgSp, pgOp]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have h0 : Fin d := ⟨0, hd_pos⟩
  rcases (tri_box_iff r a b x).mp hx with ⟨hμ, hzero, hdiag, hbelow⟩
  have hb_nonneg : 0 ≤ b := by
    have hle : a ≤ b := (hdiag h0).1.trans (hdiag h0).2
    linarith
  -- Step 1: Bound the operator norm by the Frobenius norm
  have h_op_le_frob : ‖pgOp x‖ ≤ ‖pgMat x‖ := by
    refine ContinuousLinearMap.opNorm_le_bound' (pgOp x) (norm_nonneg _) ?_
    intro v hv
    -- Express v as WithLp.toLp 2 (WithLp.ofLp v) to use the matrix-vector formula
    have hv_eq : v = WithLp.toLp 2 (WithLp.ofLp v) := by simp
    rw [hv_eq]
    dsimp [pgOp]
    rw [Matrix.toEuclideanCLM_toLp]
    -- Goal: ‖WithLp.toLp 2 (pgMat x *ᵥ (WithLp.ofLp v))‖ ≤ ‖pgMat x‖ * ‖v‖
    -- Use squared norms to avoid square roots
    have h_sq : ‖WithLp.toLp 2 (pgMat x *ᵥ (WithLp.ofLp v))‖ ^ 2 ≤ (‖pgMat x‖ * ‖v‖) ^ 2 := by
      -- First, compute the Frobenius norm squared
      have h_frob_sq : ‖pgMat x‖ ^ 2 = ∑ i, ∑ j, ((pgMat x) i j) ^ 2 := by
        rw [frobenius_norm_def]
        have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
            have : 0 ≤ ‖pgMat x i j‖ := norm_nonneg _
            exact Real.rpow_nonneg this (2 : ℝ)
        calc
          ((∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2
              = (Real.sqrt (∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ))) ^ 2 := by rw [Real.sqrt_eq_rpow]
          _ = ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) := Real.sq_sqrt h_nonneg
          _ = ∑ i, ∑ j, ((pgMat x) i j) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [Real.norm_eq_abs, sq_abs]
      calc
        ‖WithLp.toLp 2 (pgMat x *ᵥ (WithLp.ofLp v))‖ ^ 2
            = ∑ i, ‖(WithLp.toLp 2 (pgMat x *ᵥ (WithLp.ofLp v))).ofLp i‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
        _ = ∑ i, ((pgMat x *ᵥ (WithLp.ofLp v)) i) ^ 2 := by simp
        _ = ∑ i, (∑ j, (pgMat x) i j * (WithLp.ofLp v) j) ^ 2 := by
          simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ i, ((∑ j, ((pgMat x) i j) ^ 2) * (∑ j, (WithLp.ofLp v) j ^ 2)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h_cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
            (fun j => (pgMat x) i j) (WithLp.ofLp v)
          simpa using h_cauchy
        _ = (∑ i, ∑ j, ((pgMat x) i j) ^ 2) * (∑ j, (WithLp.ofLp v) j ^ 2) := by
          rw [Finset.sum_mul]
        _ = ‖pgMat x‖ ^ 2 * (∑ j, (WithLp.ofLp v) j ^ 2) := by rw [h_frob_sq]
        _ = ‖pgMat x‖ ^ 2 * ‖v‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          simp
        _ = (‖pgMat x‖ * ‖v‖) ^ 2 := by ring
    have h_nonneg_left : 0 ≤ ‖WithLp.toLp 2 (pgMat x *ᵥ (WithLp.ofLp v))‖ := norm_nonneg _
    have h_nonneg_right : 0 ≤ ‖pgMat x‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  -- Step 2: Bound the Frobenius norm
  have h_frob_le : ‖pgMat x‖ ≤ b * Real.sqrt (d * (d + 1) / 2) := by
    -- From frobenius_norm_def: ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)
    have h_frob_sq : ‖pgMat x‖ ^ 2 = ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) := by
      rw [frobenius_norm_def]
      have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          have : 0 ≤ ‖pgMat x i j‖ := norm_nonneg _
          exact Real.rpow_nonneg this (2 : ℝ)
      calc
        ((∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2
            = (Real.sqrt (∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ))) ^ 2 := by rw [Real.sqrt_eq_rpow]
        _ = ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) := Real.sq_sqrt h_nonneg
    -- Bound each entry by b
    have h_entry_le : ∀ (i j : Fin d), ‖pgMat x i j‖ ≤ b := by
      intro i j
      by_cases hij : i < j
      · simp [hzero i j hij, hb_nonneg]
      · -- ¬ i < j, so j ≤ i
        have hji : j ≤ i := le_of_not_gt hij
        by_cases hji_lt : j < i
        · -- j < i
          rw [Real.norm_eq_abs]
          exact hbelow i j hji_lt
        · -- ¬ j < i, so j = i
          have heq : j = i := le_antisymm hji (le_of_not_gt hji_lt)
          -- Use rw instead of subst to avoid clearing i
          rw [heq]
          have ha0 := (hdiag i).1
          have ha1 := (hdiag i).2
          have h_nonneg_pg : 0 ≤ pgMat x i i := by linarith
          rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg_pg]
          exact ha1
    -- Pointwise bound: ‖pgMat x i j‖ ^ (2 : ℝ) ≤ (if j ≤ i then b ^ 2 else 0)
    have h_pointwise : ∀ (i j : Fin d), ‖pgMat x i j‖ ^ (2 : ℝ) ≤ (if j ≤ i then b ^ (2 : ℝ) else 0) := by
      intro i j
      by_cases hji : j ≤ i
      · simp [hji]
        have h_le := h_entry_le i j
        have h_nonneg_entry : 0 ≤ ‖pgMat x i j‖ := norm_nonneg _
        have h_sq_le : ‖pgMat x i j‖ ^ 2 ≤ b ^ 2 := by
          nlinarith
        simpa [Real.rpow_two] using h_sq_le
      · simp [hji]
        have hij : i < j := by
          by_contra h
          exact hji (le_of_not_gt h)
        simp [hzero i j hij]
    -- Now bound the double sum
    have h_sum_le : ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) ≤ b ^ 2 * (d * (d + 1) / 2) := by
      calc
        ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) ≤ ∑ i, ∑ j, (if j ≤ i then b ^ (2 : ℝ) else 0) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_pointwise i j
        _ = ∑ i : Fin d, (∑ j, (if j ≤ i then b ^ (2 : ℝ) else 0)) := rfl
        _ = ∑ i : Fin d, b ^ (2 : ℝ) * (∑ j, if j ≤ i then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j, if j ≤ i then b ^ (2 : ℝ) else 0) = b ^ (2 : ℝ) * (∑ j, if j ≤ i then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
            _ = b ^ (2 : ℝ) * (∑ j, if j ≤ i then (1 : ℝ) else 0) := rfl
        _ = ∑ i : Fin d, b ^ (2 : ℝ) * ((i.val : ℝ) + 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sum_ite_le i]
        _ = b ^ (2 : ℝ) * (∑ i : Fin d, ((i.val : ℝ) + 1)) := by
          rw [Finset.mul_sum]
        _ = b ^ (2 : ℝ) * ((d : ℝ) * ((d : ℝ) + 1) / 2) := by rw [sum_triangular d]
        _ = b ^ 2 * (d * (d + 1) / 2) := by
          simp [Real.rpow_two]
    -- Now take square roots
    have h_nonneg_frob : 0 ≤ ‖pgMat x‖ := norm_nonneg _
    have h_nonneg_rhs : 0 ≤ b * Real.sqrt (d * (d + 1) / 2) := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (d * (d + 1) / 2) := Real.sqrt_nonneg _
      exact mul_nonneg hb_nonneg h_sqrt_nonneg
    have h_sq : ‖pgMat x‖ ^ 2 ≤ (b * Real.sqrt (d * (d + 1) / 2)) ^ 2 := by
      rw [h_frob_sq]
      have h_nonneg_arg : 0 ≤ (d : ℝ) * ((d : ℝ) + 1) / 2 := by
        have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        nlinarith
      calc
        ∑ i, ∑ j, ‖pgMat x i j‖ ^ (2 : ℝ) ≤ b ^ 2 * (d * (d + 1) / 2) := h_sum_le
        _ = (b ^ 2) * ((Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2)) ^ 2) := by
          rw [Real.sq_sqrt h_nonneg_arg]
        _ = (b * Real.sqrt ((d : ℝ) * ((d : ℝ) + 1) / 2)) ^ 2 := by ring
    nlinarith
  -- Step 3: Combine
  calc
    ‖pgOp x‖ ≤ ‖pgMat x‖ := h_op_le_frob
    _ ≤ b * Real.sqrt (d * (d + 1) / 2) := h_frob_le

end AdversarialBco.Bit.Aux_tri_opNorm

namespace AdversarialBco.Bit.Aux_tri_gauge


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_gauge {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K)
    (hB : Metric.closedBall 0 1 ⊆ K) : LipschitzWith 1 (gauge K) ∧ ∀ z, 0 ≤ gauge K z ∧ gauge K z ≤ ‖z‖ := by
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K :=
    Metric.ball_subset_closedBall.trans hB
  have h_absorbent : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (absorbent_ball_zero (by norm_num : (0 : ℝ) < 1)).mono Metric.ball_subset_closedBall
  have h_lipschitz : LipschitzWith 1 (gauge K) := by
    have := hKc.lipschitzWith_gauge (by norm_num : (0 : ℝ≥0) < 1) hball
    simpa using this
  refine ⟨h_lipschitz, fun z => ?_⟩
  have h_nonneg : 0 ≤ gauge K z := gauge_nonneg _
  have h_upper : gauge K z ≤ ‖z‖ := by
    calc
      gauge K z ≤ gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) z :=
        gauge_mono h_absorbent hB z
      _ = ‖z‖ / (1 : ℝ) := gauge_closedBall (by norm_num) z
      _ = ‖z‖ := by norm_num
  exact ⟨h_nonneg, h_upper⟩

end AdversarialBco.Bit.Aux_tri_gauge

namespace AdversarialBco.Bit.Aux_triU_meas


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.triU_meas {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ) :
    Measurable (triU α β) := by
  unfold triU
  refine Finset.measurable_sum Finset.univ ?_
  intro k hk
  have h_triQ_meas (k' : Fin m) : Measurable (triQ α β k') := by
    unfold triQ
    have h_cont : Continuous fun z : EuclideanSpace ℝ (Fin d) => inner ℝ (α k') z :=
      continuous_const.inner continuous_id
    exact (h_cont.measurable).div_const (β k')
  have h_cond_meas : MeasurableSet {z | 0 < triQ α β k z ∧ (∀ k', triQ α β k' z ≤ triQ α β k z) ∧ (∀ k', k' < k → triQ α β k' z < triQ α β k z)} := by
    have h1 : MeasurableSet {z | 0 < triQ α β k z} :=
      measurableSet_lt measurable_const (h_triQ_meas k)
    have h2 : MeasurableSet {z | ∀ k', triQ α β k' z ≤ triQ α β k z} := by
      have : {z | ∀ k', triQ α β k' z ≤ triQ α β k z} = ⋂ k' : Fin m, {z | triQ α β k' z ≤ triQ α β k z} := by
        ext z; simp
      simpa [this] using Finset.measurableSet_biInter Finset.univ (fun k' hk' =>
        measurableSet_le (h_triQ_meas k') (h_triQ_meas k))
    have h3 : MeasurableSet {z | ∀ k', k' < k → triQ α β k' z < triQ α β k z} := by
      have : {z | ∀ k', k' < k → triQ α β k' z < triQ α β k z} =
          ⋂ k' ∈ (Finset.filter (· < k) Finset.univ), {z | triQ α β k' z < triQ α β k z} := by
        ext z; simp
      simpa [this] using Finset.measurableSet_biInter (Finset.filter (· < k) Finset.univ) (fun k' hk' =>
        measurableSet_lt (h_triQ_meas k') (h_triQ_meas k))
    have h_and : {z | 0 < triQ α β k z ∧ (∀ k', triQ α β k' z ≤ triQ α β k z) ∧ (∀ k', k' < k → triQ α β k' z < triQ α β k z)} =
        {z | 0 < triQ α β k z} ∩ ({z | ∀ k', triQ α β k' z ≤ triQ α β k z} ∩ {z | ∀ k', k' < k → triQ α β k' z < triQ α β k z}) := by
      ext z; simp
    simpa [h_and] using MeasurableSet.inter h1 (MeasurableSet.inter h2 h3)
  refine Measurable.ite h_cond_meas ?_ measurable_const
  exact measurable_const

end AdversarialBco.Bit.Aux_triU_meas

namespace AdversarialBco.Bit.Aux_triU_spec


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

/-- The rows of a polytope with `‖α_k‖ ≤ β_k`: `β_k ≥ 0`, and `α_k = 0` when `β_k = 0`. -/
theorem triU_rows {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ) (hαβ : ∀ k, ‖α k‖ ≤ β k)
    (k : Fin m) : 0 ≤ β k ∧ (β k = 0 → α k = 0) :=
  ⟨(norm_nonneg _).trans (hαβ k), fun h => norm_le_zero_iff.1 (h ▸ hαβ k)⟩

/-- The polytope is absorbent: it contains the unit ball. -/
theorem triU_absorbent {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hαβ : ∀ k, ‖α k‖ ≤ β k) : Absorbent ℝ {y | ∀ k, inner ℝ (α k) y ≤ β k} := by
  refine (absorbent_ball_zero (𝕜 := ℝ) zero_lt_one).mono fun y hy k => ?_
  have hy1 : ‖y‖ ≤ 1 := by
    have := Metric.mem_ball.1 hy
    rw [dist_zero_right] at this
    exact this.le
  calc inner ℝ (α k) y ≤ ‖α k‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖α k‖ * 1 := mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
    _ ≤ β k := by rw [mul_one]; exact hαβ k

/-- Every quotient is below the gauge. -/
theorem triU_le_gauge {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hαβ : ∀ k, ‖α k‖ ≤ β k) (w : EuclideanSpace ℝ (Fin d)) (k : Fin m) :
    triQ α β k w ≤ gauge {y | ∀ k, inner ℝ (α k) y ≤ β k} w := by
  obtain ⟨hβ0, hβα⟩ := triU_rows α β hαβ k
  rcases hβ0.lt_or_eq with hβ | hβ
  · by_contra hlt
    push Not at hlt
    obtain ⟨b, hb0, hbq, y, hy, rfl⟩ :=
      exists_lt_of_gauge_lt (triU_absorbent α β hαβ) hlt
    have h1 : inner ℝ (α k) (b • y) ≤ b * β k := by
      rw [real_inner_smul_right]
      exact mul_le_mul_of_nonneg_left (hy k) hb0.le
    have h2 : triQ α β k (b • y) ≤ b := by
      unfold triQ
      rw [div_le_iff₀ hβ]
      exact h1
    linarith
  · have hα0 : α k = 0 := hβα hβ.symm
    have : triQ α β k w = 0 := by simp [triQ, hα0]
    rw [this]
    exact gauge_nonneg _

/-- The gauge is below every positive bound of the quotients. -/
theorem triU_gauge_le {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hαβ : ∀ k, ‖α k‖ ≤ β k) (w : EuclideanSpace ℝ (Fin d)) (t : ℝ) (ht : 0 < t)
    (hq : ∀ k, triQ α β k w ≤ t) : gauge {y | ∀ k, inner ℝ (α k) y ≤ β k} w ≤ t := by
  refine gauge_le_of_mem ht.le ⟨t⁻¹ • w, fun k => ?_, smul_inv_smul₀ ht.ne' w⟩
  obtain ⟨hβ0, hβα⟩ := triU_rows α β hαβ k
  rcases hβ0.lt_or_eq with hβ | hβ
  · have h := hq k
    unfold triQ at h
    rw [div_le_iff₀ hβ] at h
    rw [real_inner_smul_right, inv_mul_le_iff₀ ht]
    linarith
  · rw [hβα hβ.symm, inner_zero_left, ← hβ]

/-- The selection condition of `triU` at `z` holds for at most one index. -/
theorem triU_cond_unique {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (k k' : Fin m)
    (hk : 0 < triQ α β k z ∧ (∀ j, triQ α β j z ≤ triQ α β k z) ∧ ∀ j, j < k → triQ α β j z < triQ α β k z)
    (hk' : 0 < triQ α β k' z ∧ (∀ j, triQ α β j z ≤ triQ α β k' z) ∧ ∀ j, j < k' → triQ α β j z < triQ α β k' z) :
    k = k' := by
  have heq : triQ α β k z = triQ α β k' z := le_antisymm (hk'.2.1 k) (hk.2.1 k')
  rcases lt_trichotomy k k' with h | h | h
  · exact absurd (hk'.2.2 k h) (by rw [heq]; exact lt_irrefl _)
  · exact h
  · exact absurd (hk.2.2 k' h) (by rw [heq]; exact lt_irrefl _)

theorem _root_.AdversarialBco.Bit.triU_spec {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hαβ : ∀ k, ‖α k‖ ≤ β k) (z : EuclideanSpace ℝ (Fin d)) :
    (∀ z', inner ℝ (triU α β z) z' ≤ gauge {y | ∀ k, inner ℝ (α k) y ≤ β k} z') ∧
      gauge {y | ∀ k, inner ℝ (α k) y ≤ β k} z = inner ℝ (triU α β z) z ∧ ‖triU α β z‖ ≤ 1 := by
  classical
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (α k) y ≤ β k} with hK
  set C : Fin m → Prop := fun k => 0 < triQ α β k z ∧ (∀ k', triQ α β k' z ≤ triQ α β k z) ∧
    ∀ k', k' < k → triQ α β k' z < triQ α β k z with hC
  by_cases hex : ∃ k0, C k0
  · obtain ⟨k0, hk0⟩ := hex
    have hU : triU α β z = (β k0)⁻¹ • α k0 := by
      unfold triU
      rw [Finset.sum_eq_single k0]
      · exact if_pos hk0
      · intro k _ hk
        refine if_neg fun h => hk ?_
        exact triU_cond_unique α β z k k0 h hk0
      · intro h; exact absurd (Finset.mem_univ k0) h
    obtain ⟨hβ0, hβα⟩ := triU_rows α β hαβ k0
    have hβ : 0 < β k0 := by
      rcases hβ0.lt_or_eq with h | h
      · exact h
      · exfalso
        have : triQ α β k0 z = 0 := by simp [triQ, hβα h.symm]
        linarith [hk0.1]
    have hin : ∀ w, inner ℝ (triU α β z) w = triQ α β k0 w := by
      intro w
      rw [hU, real_inner_smul_left, triQ, div_eq_inv_mul]
    refine ⟨fun z' => ?_, ?_, ?_⟩
    · rw [hin]; exact triU_le_gauge α β hαβ z' k0
    · rw [hin]
      exact le_antisymm (triU_gauge_le α β hαβ z _ hk0.1 hk0.2.1) (triU_le_gauge α β hαβ z k0)
    · rw [hU, norm_smul, norm_inv, Real.norm_of_nonneg hβ.le, inv_mul_le_iff₀ hβ, mul_one]
      exact hαβ k0
  · have hU : triU α β z = 0 := by
      unfold triU
      refine Finset.sum_eq_zero fun k _ => if_neg fun h => hex ⟨k, h⟩
    have hneg : ∀ k, triQ α β k z ≤ 0 := by
      intro k
      by_contra hpos
      push Not at hpos
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨k, Finset.mem_univ _⟩
      set M := Finset.univ.sup' hne fun j => triQ α β j z with hM
      have hle : ∀ j, triQ α β j z ≤ M := fun j => Finset.le_sup' (fun j => triQ α β j z) (Finset.mem_univ j)
      obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup' hne fun j => triQ α β j z
      set S := Finset.univ.filter fun j => triQ α β j z = M with hS
      have hSne : S.Nonempty := ⟨j0, by simp [hS, ← hj0, hM]⟩
      set k0 := S.min' hSne with hk0
      have hk0S : k0 ∈ S := Finset.min'_mem S hSne
      have hk0M : triQ α β k0 z = M := (Finset.mem_filter.1 hk0S).2
      refine hex ⟨k0, ?_, ?_, ?_⟩
      · rw [hk0M]; exact lt_of_lt_of_le hpos (hle k)
      · intro k'; rw [hk0M]; exact hle k'
      · intro k' hk'
        rw [hk0M]
        refine lt_of_le_of_ne (hle k') fun heq => ?_
        have hk'S : k' ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, heq⟩
        exact absurd (Finset.min'_le S k' hk'S) (not_le.2 hk')
    have hg0 : gauge K z = 0 := by
      refine le_antisymm ?_ (gauge_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      exact triU_gauge_le α β hαβ z ε hε fun k => (hneg k).trans hε.le
    refine ⟨fun z' => ?_, ?_, ?_⟩
    · rw [hU, inner_zero_left]; exact gauge_nonneg _
    · rw [hg0, hU, inner_zero_left]
    · rw [hU, norm_zero]; exact zero_le_one

end AdversarialBco.Bit.Aux_triU_spec

namespace AdversarialBco.Bit.Aux_tri_subgrad


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_subgrad {d : ℕ} (r a b : ℝ) (ha : 0 < a) (π : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hu : ∀ z z', inner ℝ (u z) z' ≤ π z')
    (hu' : ∀ z, π z = inner ℝ (u z) z) (x x' : PgSp d) (hx : x ∈ triBox d r a b) (hx' : x' ∈ triBox d r a b)
    (y : EuclideanSpace ℝ (Fin d)) : triLoss π x y + inner ℝ (triV u x y) (x' - x) ≤ triLoss π x' y := by
  -- Extract box conditions from tri_box_iff
  have hx_tri := (tri_box_iff r a b x).mp hx
  have hx'_tri := (tri_box_iff r a b x').mp hx'
  rcases hx_tri with ⟨hμ, hL_lt, hdiag, habove⟩
  rcases hx'_tri with ⟨hμ', hL'_lt, hdiag', habove'⟩
  -- Set z = pgMu x + pgOp x y, z' = pgMu x' + pgOp x' y
  set z := pgMu x + pgOp x y with hz_def
  set z' := pgMu x' + pgOp x' y with hz'_def
  -- Unfold triLoss
  unfold triLoss
  -- Step 1: Gauge inequality π z' - π z ≥ A + B where
  --   A = ∑ i, (u z) i * ((pgMu x') i - (pgMu x) i)
  --   B = ∑ i, ∑ j, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)
  have h_gauge : π z' - π z ≥ (∑ i : Fin d, (u z) i * ((pgMu x') i - (pgMu x) i)) +
      (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) := by
    have h1 : π z' ≥ inner ℝ (u z) z' := hu z z'
    have h2 : π z = inner ℝ (u z) z := hu' z
    have h_diff : π z' - π z ≥ inner ℝ (u z) z' - inner ℝ (u z) z := by linarith
    have h_inner_sub : inner ℝ (u z) z' - inner ℝ (u z) z = inner ℝ (u z) (z' - z) := by
      rw [inner_sub_right]
    rw [h_inner_sub] at h_diff
    -- Now z' - z = (pgMu x' - pgMu x) + (pgOp x' y - pgOp x y)
    have h_zsub : z' - z = (pgMu x' - pgMu x) + (pgOp x' y - pgOp x y) := by
      dsimp [z, z']
      abel
    rw [h_zsub] at h_diff
    rw [inner_add_right] at h_diff
    -- Now we have two terms: inner ℝ (u z) (pgMu x' - pgMu x) + inner ℝ (u z) (pgOp x' y - pgOp x y)
    -- First term = ∑ i, (u z) i * ((pgMu x') i - (pgMu x) i)
    have h_first : inner ℝ (u z) (pgMu x' - pgMu x) = ∑ i : Fin d, (u z) i * ((pgMu x') i - (pgMu x) i) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [Pi.sub_apply, inner, mul_comm]
    -- Second term = ∑ i, ∑ j, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)
    have h_second : inner ℝ (u z) (pgOp x' y - pgOp x y) = ∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j) := by
      -- pgOp x = Matrix.toEuclideanCLM (pgMat x), linear in the matrix
      have h_linear : pgOp x' y - pgOp x y = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x' - pgMat x) y := by
        calc
          pgOp x' y - pgOp x y = ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x')) y - ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x)) y := rfl
          _ = (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x')) - ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x))) y := rfl
          _ = ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (pgMat x' - pgMat x)) y := by
            rw [map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d))]
      rw [h_linear]
      rw [Matrix.inner_toEuclideanCLM]
      -- Now: (u z).ofLp ⬝ᵥ (pgMat x' - pgMat x).mulVec y.ofLp
      -- Expand the dot product and matrix-vector multiplication
      rw [dotProduct]
      -- Now we have ∑ i, (u z).ofLp i * ((pgMat x' - pgMat x) *ᵥ y.ofLp) i
      -- Expand the matrix-vector multiplication
      have h_expand : ∀ i, ((pgMat x' - pgMat x) *ᵥ y.ofLp) i = ∑ j : Fin d, (pgMat x' i j - pgMat x i j) * y.ofLp j := by
        intro i
        simp [Matrix.mulVec_apply, Matrix.row_apply, dotProduct]
      simp_rw [h_expand]
      -- Now we have ∑ i, (u z).ofLp i * (∑ j, (pgMat x' i j - pgMat x i j) * y.ofLp j)
      have h_sum_eq : (∑ i : Fin d, ∑ j : Fin d, (u z) i * (pgMat x' i j - pgMat x i j) * y j) =
          (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hji : j ≤ i
        · simp [hji, mul_comm, mul_left_comm, mul_assoc]
        · have h_lt : i < j := Fin.not_le.mp hji
          have hx_zero := hL_lt i j h_lt
          have hx'_zero := hL'_lt i j h_lt
          simp [hji, hx_zero, hx'_zero]
      simp_rw [Finset.mul_sum]
      -- Now we have ∑ i, ∑ j, (u z).ofLp i * ((pgMat x' i j - pgMat x i j) * y.ofLp j)
      -- Rewrite with associativity to match h_sum_eq
      have h_assoc : (∑ i : Fin d, ∑ j : Fin d, (u z).ofLp i * ((pgMat x' i j - pgMat x i j) * y.ofLp j)) =
          (∑ i : Fin d, ∑ j : Fin d, (u z).ofLp i * (pgMat x' i j - pgMat x i j) * y.ofLp j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [h_assoc]
      rw [h_sum_eq]
    -- Combine the two terms
    have h_sum : inner ℝ (u z) (pgMu x' - pgMu x) + inner ℝ (u z) (pgOp x' y - pgOp x y) =
        (∑ i : Fin d, (u z) i * ((pgMu x') i - (pgMu x) i)) +
        (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) := by
      rw [h_first, h_second]
    linarith
  -- Step 2: Inner product decomposition via pgSp_inner
  have h_inner : inner ℝ (triV u x y) (x' - x) = (∑ i : Fin d, (u z) i * ((pgMu x') i - (pgMu x) i)) +
      (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) -
      (pgKappa / d) * (∑ i : Fin d, (pgMat x' i i - pgMat x i i) / pgMat x i i) := by
    rw [pgSp_inner]
    -- Now: inner ℝ (pgMu (triV u x y)) (pgMu (x' - x)) + ∑ i, ∑ j, pgMat (triV u x y) i j * pgMat (x' - x) i j
    have h_mu : inner ℝ (pgMu (triV u x y)) (pgMu (x' - x)) = ∑ i : Fin d, (u z) i * ((pgMu x') i - (pgMu x) i) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp [triV, pgMu, z]
      simp [Pi.sub_apply, inner, mul_comm]
    have h_mat : (∑ i : Fin d, ∑ j : Fin d, pgMat (triV u x y) i j * pgMat (x' - x) i j) =
        (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) -
        (pgKappa / d) * (∑ i : Fin d, (pgMat x' i i - pgMat x i i) / pgMat x i i) := by
      dsimp [triV, pgMat, z]
      calc
        (∑ i : Fin d, ∑ j : Fin d, ((if j ≤ i then (u z) i * y j else 0) - (if i = j then pgKappa / d / pgMat x i i else 0)) * (pgMat x' i j - pgMat x i j))
            = (∑ i : Fin d, ∑ j : Fin d, ((if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j) - (if i = j then pgKappa / d / pgMat x i i else 0) * (pgMat x' i j - pgMat x i j))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
        _ = (∑ i : Fin d, ∑ j : Fin d, ((if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j))) -
            (∑ i : Fin d, ∑ j : Fin d, ((if i = j then pgKappa / d / pgMat x i i else 0) * (pgMat x' i j - pgMat x i j))) := by
          simp_rw [Finset.sum_sub_distrib]
        _ = (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) -
            (∑ i : Fin d, (pgKappa / d / pgMat x i i) * (pgMat x' i i - pgMat x i i)) := by
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp_rw [ite_mul, zero_mul]
          simp [Finset.sum_ite_eq, Finset.mem_univ]
        _ = (∑ i : Fin d, ∑ j : Fin d, (if j ≤ i then (u z) i * y j else 0) * (pgMat x' i j - pgMat x i j)) -
            (pgKappa / d) * (∑ i : Fin d, (pgMat x' i i - pgMat x i i) / pgMat x i i) := by
          simp_rw [Finset.mul_sum]
          refine congrArg (fun t => _ - t) (Finset.sum_congr rfl (fun i _ => ?_))
          ring
    rw [h_mu, h_mat]
    ring
  -- Step 3: Log inequality using sp_neglog_subgrad
  have h_log : (pgKappa / d) * (∑ i : Fin d, Real.log (pgMat x i i) - ∑ i : Fin d, Real.log (pgMat x' i i)) ≥
      -(pgKappa / d) * (∑ i : Fin d, (pgMat x' i i - pgMat x i i) / pgMat x i i) := by
    have h_nonneg : 0 ≤ pgKappa / d := by
      have hpgKappa : 0 ≤ pgKappa := by
        unfold pgKappa
        norm_num
      have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
      exact div_nonneg hpgKappa hd
    have h_diag_pos : ∀ i : Fin d, 0 < pgMat x i i := by
      intro i
      have ha_le := hdiag i
      linarith
    have h_diag_pos' : ∀ i : Fin d, 0 < pgMat x' i i := by
      intro i
      have ha_le := hdiag' i
      linarith
    -- For each i, apply sp_neglog_subgrad
    have h_each (i : Fin d) : -Real.log (pgMat x i i) - (pgMat x' i i - pgMat x i i) / pgMat x i i ≤ -Real.log (pgMat x' i i) := by
      exact sp_neglog_subgrad (pgMat x i i) (pgMat x' i i) (h_diag_pos i) (h_diag_pos' i)
    -- Sum over i
    have h_sum : (∑ i : Fin d, (-Real.log (pgMat x i i) - (pgMat x' i i - pgMat x i i) / pgMat x i i)) ≤
        (∑ i : Fin d, -Real.log (pgMat x' i i)) := by
      exact Finset.sum_le_sum (fun i _ => h_each i)
    -- Rearrange the sums: ∑ i, -log L_ii = -(∑ i, log L_ii)
    rw [Finset.sum_sub_distrib] at h_sum
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at h_sum
    -- h_sum: -(∑ i, log (pgMat x i i)) - (∑ i, (pgMat x' i i - pgMat x i i) / pgMat x i i) ≤ -(∑ i, log (pgMat x' i i))
    -- Name the sums for clarity
    set A := ∑ i : Fin d, Real.log (pgMat x i i) with hA
    set B := ∑ i : Fin d, Real.log (pgMat x' i i) with hB
    set S2 := ∑ i : Fin d, (pgMat x' i i - pgMat x i i) / pgMat x i i with hS2
    -- Now h_sum: -A - S2 ≤ -B, i.e., -A - S2 ≤ -B
    -- Multiply by K = pgKappa / d ≥ 0
    have h_mul : (pgKappa / d) * (-A - S2) ≤ (pgKappa / d) * (-B) := by
      nlinarith
    -- Goal: K * (A - B) ≥ -K * S2
    -- From h_mul: K*(-A - S2) ≤ K*(-B) → -K*A - K*S2 ≤ -K*B → K*A + K*S2 ≥ K*B → K*(A-B) ≥ -K*S2
    nlinarith
  -- Step 4: Combine gauge, inner, and log inequalities
  linarith

end AdversarialBco.Bit.Aux_tri_subgrad

namespace AdversarialBco.Bit.Aux_tri_V_bound


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_V_bound {d : ℕ} (hd : 1 ≤ d) (r a b : ℝ) (ha : 0 < a)
    (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hu : ∀ z, ‖u z‖ ≤ 1) (x : PgSp d)
    (hx : x ∈ triBox d r a b) (y : EuclideanSpace ℝ (Fin d)) (Md Gb : ℝ) (hy : ‖y‖ ≤ Md) (hGb0 : 0 ≤ Gb)
    (hGb : 1 + (Md + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ Gb ^ 2) : ‖triV u x y‖ ≤ Gb := by
  set z := pgMu x + pgOp x y with hz
  have huz_sq : ∑ i, (u z i) ^ 2 ≤ 1 := by
    have huz_norm : ‖u z‖ ≤ 1 := hu z
    have huz_norm_sq : ‖u z‖ ^ 2 ≤ 1 := by
      have h_nonneg : 0 ≤ ‖u z‖ := norm_nonneg _
      nlinarith
    have h_eq : ‖u z‖ ^ 2 = ∑ i, (u z i) ^ 2 := by
      calc
        ‖u z‖ ^ 2 = ∑ i, ‖(u z).ofLp i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
        _ = ∑ i, ‖(u z) i‖ ^ 2 := by simp
        _ = ∑ i, (u z i) ^ 2 := by simp
    rw [h_eq] at huz_norm_sq
    exact huz_norm_sq
  have h_tri_box := (tri_box_iff r a b x).mp hx
  rcases h_tri_box with ⟨hμ, hzero, hdiag, hbelow⟩
  have hdiag' : ∀ i, a ≤ pgMat x i i := fun i => (hdiag i).1
  have hKappa_nonneg : 0 ≤ pgKappa := by
    unfold pgKappa
    norm_num
  have h_sp_V := sp_V_norm hd (u z) y (pgMat x) pgKappa a hKappa_nonneg ha hdiag' huz_sq
  have h_norm_y : Real.sqrt (∑ j, (y j) ^ 2) = ‖y‖ := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [h_norm_y] at h_sp_V
  have h_bound : 1 + (‖y‖ + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ 1 + (Md + pgKappa / (Real.sqrt d * a)) ^ 2 := by
    have h_sqrt_d_pos : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have ha_pos' : 0 ≤ a := by linarith
    have h_denom_pos : 0 ≤ Real.sqrt d * a := mul_nonneg h_sqrt_d_pos ha_pos'
    have h_add_nonneg : 0 ≤ ‖y‖ + pgKappa / (Real.sqrt d * a) := by
      have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
      have h_div_nonneg : 0 ≤ pgKappa / (Real.sqrt d * a) :=
        div_nonneg hKappa_nonneg h_denom_pos
      nlinarith
    have h_add_nonneg' : 0 ≤ Md + pgKappa / (Real.sqrt d * a) := by
      nlinarith
    nlinarith
  have h_sq_bound : ‖triV u x y‖ ^ 2 ≤ Gb ^ 2 := by
    rw [pgSp_norm_sq (triV u x y)]
    have h_expand : ‖pgMu (triV u x y)‖ ^ 2 + ∑ i, ∑ j, (pgMat (triV u x y) i j) ^ 2 =
        ∑ i, (u z i) ^ 2 + ∑ i, ∑ j, ((if j ≤ i then u z i * y j else 0) -
          (if i = j then pgKappa / d / pgMat x i i else 0)) ^ 2 := by
      dsimp [triV, pgMu, pgMat, z]
      simp only [EuclideanSpace.norm_sq_eq]
      simp
    rw [h_expand]
    have h_le : ∑ i, (u z i) ^ 2 + ∑ i, ∑ j, ((if j ≤ i then u z i * y j else 0) -
        (if i = j then pgKappa / d / pgMat x i i else 0)) ^ 2 ≤
        1 + (‖y‖ + pgKappa / (Real.sqrt d * a)) ^ 2 := by
      -- sp_V_norm gives this with .ofLp, so we need to convert
      simpa using h_sp_V
    have h_le2 : 1 + (‖y‖ + pgKappa / (Real.sqrt d * a)) ^ 2 ≤
        1 + (Md + pgKappa / (Real.sqrt d * a)) ^ 2 := h_bound
    have h_le3 : 1 + (Md + pgKappa / (Real.sqrt d * a)) ^ 2 ≤ Gb ^ 2 := hGb
    nlinarith
  have h_norm_nonneg : 0 ≤ ‖triV u x y‖ := norm_nonneg _
  exact le_of_sq_le_sq h_sq_bound hGb0

end AdversarialBco.Bit.Aux_tri_V_bound

namespace AdversarialBco.Bit.Aux_tri_loss_meas


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_loss_meas {d : ℕ} (π : EuclideanSpace ℝ (Fin d) → ℝ) (hπ : Continuous π) :
    Measurable (Function.uncurry (triLoss π)) := by
  have h_cont : Continuous (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMu p.1 + pgOp p.1 p.2) :=
    (pg_continuous d).2.2
  have h_first : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => π (pgMu p.1 + pgOp p.1 p.2)) :=
    (hπ.comp h_cont).measurable
  have h_second : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgKappa / d * ∑ i, Real.log (pgMat p.1 i i)) := by
    have h_each (i : Fin d) (hi : i ∈ Finset.univ) : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => Real.log (pgMat p.1 i i)) := by
      have h_meas_pgMat : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMat p.1 i i) := by
        have : Continuous (fun (x : PgSp d) => x (Sum.inr (i, i))) :=
          PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d × Fin d => ℝ) (Sum.inr (i, i))
        have h : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => p.1 (Sum.inr (i, i))) :=
          (this.comp continuous_fst).measurable
        simpa [pgMat] using h
      exact Real.measurable_log.comp h_meas_pgMat
    have h_sum : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => ∑ i, Real.log (pgMat p.1 i i)) :=
      Finset.measurable_sum Finset.univ h_each
    exact (h_sum.const_mul (pgKappa / d))
  exact h_first.sub h_second

end AdversarialBco.Bit.Aux_tri_loss_meas

namespace AdversarialBco.Bit.Aux_tri_elo_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_elo_le (d Lh : ℕ) (hd : 1 ≤ d) (hLh : 1 ≤ Lh) :
    pgKappa ^ 2 / (922 * (d : ℝ) ^ 2 * (7 / 5 * Lh) * (627 / 4000 * (2 ^ Lh - 1))) ≤ pgEh d (2 ^ Lh - 1) := by
  set ρ := (2 : ℝ) ^ Lh - 1 with hρ
  have hρpos : 0 < ρ := by
    have h2pow_nat : (2 : ℕ) ^ 1 ≤ (2 : ℕ) ^ Lh :=
      Nat.pow_le_pow_right (by norm_num) hLh
    have h2pow : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ Lh := by
      exact_mod_cast h2pow_nat
    have h2pow_one : (2 : ℝ) ^ (1 : ℕ) = (2 : ℝ) := by norm_num
    rw [h2pow_one] at h2pow
    linarith
  have h_one_plus_ρ : (1 : ℝ) + ρ = (2 : ℝ) ^ Lh := by
    dsimp [ρ]
    ring
  have h_log_one_plus_ρ : Real.log (1 + ρ) = (Lh : ℝ) * Real.log 2 := by
    rw [h_one_plus_ρ, Real.log_pow]
  have h_pgLam_sq : pgLam ρ ^ 2 = 2 * (Lh : ℝ) * Real.log 2 := by
    dsimp [pgLam]
    have h_nonneg : 0 ≤ 2 * Real.log (1 + ρ) := by
      have hlog : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by
        have : 0 ≤ ρ := by linarith
        linarith
      )
      nlinarith
    rw [Real.sq_sqrt h_nonneg, h_log_one_plus_ρ]
    ring
  have h_pgLD : pgLD ρ = (627 / 4000 : ℝ) * ρ := by
    dsimp [pgLD, pgKappa, pgPB]
    ring
  have h_log_lt : Real.log 2 < 7/10 := by
    refine lt_of_lt_of_le Real.log_two_lt_d9 ?_
    norm_num
  have h_log_le : 2 * Real.log 2 ≤ 7/5 := by
    linarith
  have h_main : pgLam ρ ^ 2 * pgLD ρ ≤ (7/5 * (Lh : ℝ)) * ((627/4000 : ℝ) * ρ) := by
    rw [h_pgLam_sq, h_pgLD]
    have hLhpos : 0 < (Lh : ℝ) := by
      exact_mod_cast Nat.one_pos.trans_le hLh
    have h627pos : 0 < (627/4000 : ℝ) := by norm_num
    have hfactor_pos : 0 < (Lh : ℝ) * ((627/4000 : ℝ) * ρ) := by
      positivity
    nlinarith
  have h_pgKappa_sq_nonneg : 0 ≤ pgKappa ^ 2 := by
    dsimp [pgKappa]
    positivity
  have h_denom_pos : 0 < 922 * (d : ℝ) ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by
    have h922pos : 0 < (922 : ℝ) := by norm_num
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.one_pos.trans_le hd
    have hd2pos : 0 < (d : ℝ) ^ 2 := pow_pos hdpos 2
    have h_pgLam_pos : 0 < pgLam ρ := by
      dsimp [pgLam]
      have h_log_pos : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
      have h_inner_pos : 0 < 2 * Real.log (1 + ρ) := by nlinarith
      exact Real.sqrt_pos.mpr h_inner_pos
    have h_pgLam_sq_pos : 0 < pgLam ρ ^ 2 := pow_pos h_pgLam_pos 2
    have h_pgLD_pos : 0 < pgLD ρ := by
      rw [h_pgLD]
      have h627pos : 0 < (627/4000 : ℝ) := by norm_num
      exact mul_pos h627pos hρpos
    refine mul_pos (mul_pos (mul_pos h922pos hd2pos) h_pgLam_sq_pos) h_pgLD_pos
  rw [pgEh, hρ]
  refine div_le_div_of_nonneg_left h_pgKappa_sq_nonneg h_denom_pos ?_
  have h922d2_nonneg : 0 ≤ 922 * (d : ℝ) ^ 2 := by positivity
  nlinarith

end AdversarialBco.Bit.Aux_tri_elo_le

namespace AdversarialBco.Bit.Aux_tri_row_main


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_row_main (Δ Δu Gb Gu β βu ℓ ℓu s N εG elo : ℝ) (hΔ : 0 < Δ) (hΔu : Δ ≤ Δu)
    (hGb : 0 ≤ Gb) (hGu : Gb ≤ Gu) (hβ : 0 ≤ β) (hβu : β ≤ βu) (hℓ : 0 ≤ ℓ) (hℓu : ℓ ≤ ℓu) (hN : 0 < N)
    (hs : 0 < s) (hs1 : Δ ^ 2 < 4 * s ^ 2 * (Gu + βu) ^ 2 * N) (hs2 : s ^ 2 * (Gu + βu) ^ 2 * N ≤ Δ ^ 2)
    (hNc : Δu ^ 2 * (2 * (3 / 2 * (Gu + βu)) ^ 2 + 2 * (2 * Gu ^ 2 * ℓu)) ≤ 9 / 16 * elo ^ 2 * N)
    (hβc : βu ^ 2 * Δu ^ 2 ≤ elo ^ 2 / 64) (hεc : 2 * εG ≤ elo / 8) (helo : 0 ≤ elo) :
    Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + β * Δ + Gb * Δ * Real.sqrt (2 * ℓ / N) + 2 * εG ≤ elo := by
  set G := Gu + βu with hG_def
  have hGu_nonneg : 0 ≤ Gu := le_trans hGb hGu
  have hβu_nonneg : 0 ≤ βu := le_trans hβ hβu
  have hG_nonneg : 0 ≤ G := add_nonneg hGu_nonneg hβu_nonneg
  have hG_pos : 0 < G := by
    by_contra! h
    have hG0 : G = 0 := by linarith
    have hzero : 4 * s ^ 2 * G ^ 2 * N = 0 := by simp [hG0]
    have hpos : 0 < Δ ^ 2 := pow_pos hΔ 2
    have h_lt : Δ ^ 2 < 4 * s ^ 2 * G ^ 2 * N := by simpa [hG_def] using hs1
    linarith
  have h_sqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hG_sqrtN_pos : 0 < G * Real.sqrt N := mul_pos hG_pos h_sqrtN_pos
  have h_sqrtN_nonneg : 0 ≤ Real.sqrt N := le_of_lt h_sqrtN_pos
  have h_s_bound1 : s ≤ Δ / (G * Real.sqrt N) := by
    have hsq : s ^ 2 * G ^ 2 * N ≤ Δ ^ 2 := by simpa [hG_def] using hs2
    have h_nonneg_s : 0 ≤ s := le_of_lt hs
    have h_sqrt_sq : Real.sqrt (s ^ 2 * G ^ 2 * N) = s * G * Real.sqrt N := by
      calc
        Real.sqrt (s ^ 2 * G ^ 2 * N) = Real.sqrt (s ^ 2 * G ^ 2) * Real.sqrt N :=
          Real.sqrt_mul (by positivity : 0 ≤ s ^ 2 * G ^ 2) N
        _ = Real.sqrt (s ^ 2) * Real.sqrt (G ^ 2) * Real.sqrt N := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ s ^ 2) (G ^ 2)]
        _ = |s| * |G| * Real.sqrt N := by simp [Real.sqrt_sq_eq_abs]
        _ = s * G * Real.sqrt N := by
          simp [abs_of_nonneg h_nonneg_s, abs_of_nonneg hG_nonneg]
    have h_sqrt_Δ : Real.sqrt (Δ ^ 2) = Δ := Real.sqrt_sq (le_of_lt hΔ)
    have h_sqrt_ineq : Real.sqrt (s ^ 2 * G ^ 2 * N) ≤ Real.sqrt (Δ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rw [h_sqrt_sq, h_sqrt_Δ] at h_sqrt_ineq
    -- h_sqrt_ineq: s * G * √N ≤ Δ
    -- Need: s ≤ Δ / (G * √N)
    apply (le_div_iff₀ hG_sqrtN_pos).mpr
    simpa [mul_assoc] using h_sqrt_ineq
  have h_s_bound2 : Δ / (G * Real.sqrt N) / 2 < s := by
    have hsq : Δ ^ 2 < 4 * s ^ 2 * G ^ 2 * N := by simpa [hG_def] using hs1
    have h_sqrt_lt : Real.sqrt (Δ ^ 2) < Real.sqrt (4 * s ^ 2 * G ^ 2 * N) :=
      Real.sqrt_lt_sqrt (by positivity) hsq
    have h_sqrt_Δ : Real.sqrt (Δ ^ 2) = Δ := Real.sqrt_sq (le_of_lt hΔ)
    have h_sqrt_rhs : Real.sqrt (4 * s ^ 2 * G ^ 2 * N) = 2 * s * G * Real.sqrt N := by
      calc
        Real.sqrt (4 * s ^ 2 * G ^ 2 * N) = Real.sqrt ((2 * s * G) ^ 2 * N) := by ring_nf
        _ = Real.sqrt ((2 * s * G) ^ 2) * Real.sqrt N := Real.sqrt_mul (by positivity : 0 ≤ (2 * s * G) ^ 2) N
        _ = |2 * s * G| * Real.sqrt N := by rw [Real.sqrt_sq_eq_abs]
        _ = (2 * s * G) * Real.sqrt N := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * s * G)]
        _ = 2 * s * G * Real.sqrt N := by ring
    rw [h_sqrt_Δ, h_sqrt_rhs] at h_sqrt_lt
    -- h_sqrt_lt: Δ < 2 * s * G * √N
    -- Need: Δ / (G * √N) / 2 < s
    -- Using div_lt_iff: a/c < b ↔ a < b*c
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_lt_iff₀ hG_sqrtN_pos).mpr
    simpa [mul_assoc, mul_comm, mul_left_comm] using h_sqrt_lt
  have h_step := sp_step_rule Δ G N s hΔ hG_pos hN h_s_bound2 h_s_bound1
  -- h_step: Δ^2/(2*s*N) + s/2*G^2 ≤ 3/2*Δ*G/√N
  have h_sq_bound : (Gb + β)^2 ≤ G^2 := by
    have h_sum : Gb + β ≤ G := by dsimp [G]; linarith
    have h_nonneg_sum : 0 ≤ Gb + β := add_nonneg hGb hβ
    nlinarith
  have h_first_two : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 ≤ 3 / 2 * Δ * G / Real.sqrt N := by
    calc
      Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 ≤ Δ ^ 2 / (2 * s * N) + s / 2 * G ^ 2 := by
        gcongr
      _ ≤ 3 / 2 * Δ * G / Real.sqrt N := h_step
  have h_fourth_bound : Gb * Δ * Real.sqrt (2 * ℓ / N) ≤ Gu * Δu * Real.sqrt (2 * ℓu / N) := by
    have h_sqrt_bound : Real.sqrt (2 * ℓ / N) ≤ Real.sqrt (2 * ℓu / N) :=
      Real.sqrt_le_sqrt (by
        have : 2 * ℓ / N ≤ 2 * ℓu / N := by
          gcongr
        exact this)
    have h_nonneg_Gb : 0 ≤ Gb := hGb
    have h_nonneg_Δ : 0 ≤ Δ := le_of_lt hΔ
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (2 * ℓ / N) := Real.sqrt_nonneg _
    have h_nonneg_GuΔu : 0 ≤ Gu * Δu := mul_nonneg hGu_nonneg (le_of_lt (lt_of_lt_of_le hΔ hΔu))
    gcongr
  set X := 3 / 2 * G with hX_def
  set Y := Real.sqrt (2 * Gu ^ 2 * ℓu) with hY_def
  have hY_sq' : Y ^ 2 = 2 * Gu ^ 2 * ℓu := by
    rw [hY_def]
    have h_nonneg : 0 ≤ 2 * Gu ^ 2 * ℓu := by
      have : 0 ≤ Gu ^ 2 := pow_two_nonneg _
      have : 0 ≤ ℓu := le_trans hℓ hℓu
      positivity
    rw [Real.sq_sqrt h_nonneg]
  have hX_sq : X ^ 2 = (9/4) * G ^ 2 := by dsimp [X]; ring
  have h_XY_sq : (X + Y)^2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    have h : (X - Y)^2 ≥ 0 := pow_two_nonneg _
    nlinarith
  have hNc' : Δu ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) ≤ 9 / 16 * elo ^ 2 * N := by
    calc
      Δu ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) = Δu ^ 2 * (2 * ((9/4) * G ^ 2) + 2 * (2 * Gu ^ 2 * ℓu)) := by
        rw [hX_sq, hY_sq']
      _ = Δu ^ 2 * (2 * (3/2 * G) ^ 2 + 2 * (2 * Gu ^ 2 * ℓu)) := by ring
      _ ≤ 9 / 16 * elo ^ 2 * N := hNc
  have hΔu_pos : 0 < Δu := lt_of_lt_of_le hΔ hΔu
  have hΔu_nonneg : 0 ≤ Δu := le_of_lt hΔu_pos
  have hX_nonneg : 0 ≤ X := by dsimp [X]; positivity
  have hXY_nonneg : 0 ≤ X + Y := add_nonneg hX_nonneg (Real.sqrt_nonneg _)
  have h_sq_bound2 : (Δu * (X + Y)) ^ 2 ≤ (3/4 * elo * Real.sqrt N) ^ 2 := by
    calc
      (Δu * (X + Y)) ^ 2 = Δu ^ 2 * (X + Y) ^ 2 := by ring
      _ ≤ Δu ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) := by gcongr
      _ ≤ 9 / 16 * elo ^ 2 * N := hNc'
      _ = (3/4 * elo * Real.sqrt N) ^ 2 := by
        calc
          9/16 * elo ^ 2 * N = ((3/4) ^ 2) * elo ^ 2 * N := by ring
          _ = (3/4) ^ 2 * elo ^ 2 * ((Real.sqrt N) ^ 2) := by rw [Real.sq_sqrt (le_of_lt hN)]
          _ = (3/4 * elo * Real.sqrt N) ^ 2 := by ring
  have h_main_term : Δu * (X + Y) ≤ 3/4 * elo * Real.sqrt N := by
    have h_nonneg_du : 0 ≤ Δu * (X + Y) := mul_nonneg hΔu_nonneg hXY_nonneg
    have h_nonneg_rhs : 0 ≤ 3/4 * elo * Real.sqrt N := by positivity
    have h_sq_bound2' : (Δu * (X + Y)) * (Δu * (X + Y)) ≤ (3/4 * elo * Real.sqrt N) * (3/4 * elo * Real.sqrt N) := by
      simpa [sq] using h_sq_bound2
    exact (mul_self_le_mul_self_iff h_nonneg_du h_nonneg_rhs).mpr h_sq_bound2'
  -- Key identity: Y / √N = Gu * √(2*ℓu/N)
  have hY_div_sqrtN : Y / Real.sqrt N = Gu * Real.sqrt (2 * ℓu / N) := by
    calc
      Y / Real.sqrt N = Real.sqrt (2 * Gu ^ 2 * ℓu) / Real.sqrt N := rfl
      _ = Real.sqrt (Gu ^ 2 * (2 * ℓu)) / Real.sqrt N := by ring_nf
      _ = (Real.sqrt (Gu ^ 2) * Real.sqrt (2 * ℓu)) / Real.sqrt N := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ Gu ^ 2) (2 * ℓu)]
      _ = (Gu * Real.sqrt (2 * ℓu)) / Real.sqrt N := by
        rw [Real.sqrt_sq hGu_nonneg]
      _ = Gu * (Real.sqrt (2 * ℓu) / Real.sqrt N) := by ring
      _ = Gu * Real.sqrt (2 * ℓu / N) := by
        rw [Real.sqrt_div (mul_nonneg (by norm_num) (le_trans hℓ hℓu)) N]
  have h_combined : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + Gb * Δ * Real.sqrt (2 * ℓ / N) ≤
      Δu * (X + Y) / Real.sqrt N := by
    calc
      Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + Gb * Δ * Real.sqrt (2 * ℓ / N) ≤
          (3 / 2 * Δ * G / Real.sqrt N) + Gu * Δu * Real.sqrt (2 * ℓu / N) := by
        gcongr
      _ = (3 / 2 * Δ * G) / Real.sqrt N + (Gu * Real.sqrt (2 * ℓu / N)) * Δu := by ring
      _ ≤ (3 / 2 * Δu * G) / Real.sqrt N + (Gu * Real.sqrt (2 * ℓu / N)) * Δu := by
        have h : (3 / 2 * Δ * G) / Real.sqrt N ≤ (3 / 2 * Δu * G) / Real.sqrt N := by
          have hineq : 3/2 * Δ * G ≤ 3/2 * Δu * G := by
            have hpos : 0 ≤ (3/2 : ℝ) := by norm_num
            have h1 : Δ * G ≤ Δu * G := mul_le_mul_of_nonneg_right hΔu hG_nonneg
            have h2 : (3/2) * (Δ * G) ≤ (3/2) * (Δu * G) := mul_le_mul_of_nonneg_left h1 hpos
            simpa [mul_assoc] using h2
          exact div_le_div_of_nonneg_right hineq h_sqrtN_nonneg
        exact add_le_add h (le_refl _)
      _ = Δu * ((3/2 * G) / Real.sqrt N + Gu * Real.sqrt (2 * ℓu / N)) := by ring
      _ = Δu * (X / Real.sqrt N + Gu * Real.sqrt (2 * ℓu / N)) := by rfl
      _ = Δu * (X / Real.sqrt N + Y / Real.sqrt N) := by rw [hY_div_sqrtN]
      _ = Δu * ((X + Y) / Real.sqrt N) := by ring
      _ = Δu * (X + Y) / Real.sqrt N := by ring
  have h_main : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + Gb * Δ * Real.sqrt (2 * ℓ / N) ≤ 3/4 * elo := by
    calc
      Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + Gb * Δ * Real.sqrt (2 * ℓ / N) ≤
          Δu * (X + Y) / Real.sqrt N := h_combined
      _ ≤ (3/4 * elo * Real.sqrt N) / Real.sqrt N := by
        gcongr
      _ = 3/4 * elo := by
        field_simp [ne_of_gt h_sqrtN_pos]
  have h_beta_bound : β * Δ ≤ elo / 8 := by
    have h1 : β * Δ ≤ βu * Δu := by
      gcongr
    have h2 : βu * Δu ≤ elo / 8 := by
      have h_sq : (βu * Δu) ^ 2 ≤ (elo / 8) ^ 2 := by
        calc
          (βu * Δu) ^ 2 = βu ^ 2 * Δu ^ 2 := by ring
          _ ≤ elo ^ 2 / 64 := hβc
          _ = (elo / 8) ^ 2 := by ring
      have h_nonneg_βuΔu : 0 ≤ βu * Δu := mul_nonneg hβu_nonneg hΔu_nonneg
      have h_nonneg_elo8 : 0 ≤ elo / 8 := div_nonneg helo (by norm_num)
      have h_sq' : (βu * Δu) * (βu * Δu) ≤ (elo / 8) * (elo / 8) := by
        simpa [sq] using h_sq
      exact (mul_self_le_mul_self_iff h_nonneg_βuΔu h_nonneg_elo8).mpr h_sq'
    linarith
  calc
    Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + β * Δ + Gb * Δ * Real.sqrt (2 * ℓ / N) + 2 * εG =
        (Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + Gb * Δ * Real.sqrt (2 * ℓ / N)) + (β * Δ + 2 * εG) := by ring
    _ ≤ (3/4 * elo) + (β * Δ + 2 * εG) := by gcongr
    _ ≤ (3/4 * elo) + (elo / 8 + elo / 8) := by gcongr
    _ = elo := by ring


end AdversarialBco.Bit.Aux_tri_row_main
