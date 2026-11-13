/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Poly.Df2Oracle
public import AdversarialBco.Bit.ProjBit

@[expose] public section

/-!
# Lemmas of Procedure FRAME and Theorem ELL-F, the rational frame in the bit model

Statements of the list FR1 to FR18.

* F0 to F2, the rows: `fr_height` (the height computed from the input), `fr_cleared_row` (a row and its cleared integer
  row test the same margin), `fr_test_sq` (the row test on squares, F4 step 1), `fr_margin_iff` (FR14: the closed ball
  `B̄(y, r)` lies in the polytope iff `⟨A_i, y⟩ + r |A_i| ≤ b_i` for every row); at `d = 1`, `fr_d1_signs` (a bounded
  nonempty polytope has rows of both signs), `fr_d1_readoff` (the polytope is the interval `[lo, hi]`) and
  `fr_d1_centre` (FR16: the centre and its size, for `hi - lo ≥ 1`).
* F3 and F4: `fr_lam_sq` (the blow-up factor `λ`), `fr_mat_step` (the matrix step in integers), `fr_rnd_vec` (the
  centre rounding in vector form), `fr_rnd_ediv` (`⌊(2u + v)/(2v)⌋` is the rounded quotient of the machine).
* Theorem ELL-F, proof of (b): `fr_det_factor` (the determinant factor), `fr_lmax_step` (the cap on the largest
  eigenvalue), `fr_abs_margin` (the margins of Lemma ABS), `fr_center_cap` (the centre stays near the kept ball),
  `fr_entry_cap` (the entries of a capped positive definite matrix).

Each lemma sits in a
namespace `AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/

namespace AdversarialBco.Bit.Aux_fr_height


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_height {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    ((∀ i j, (A i j).num.natAbs ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) ∧
        (A i j).den ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den)) ∧
      ∀ i, (b i).num.natAbs ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) ∧
        (b i).den ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den)) ∧
    (∀ M : ℕ, ((∀ i j, (A i j).num.natAbs ≤ M ∧ (A i j).den ≤ M) ∧ ∀ i, (b i).num.natAbs ≤ M ∧ (b i).den ≤ M) →
      Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) ≤ M) ∧
    (0 < m → 1 ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
          max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den)) := by
  set S := Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
    max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) with hS
  have hA_bound : ∀ i j, (A i j).num.natAbs ≤ S ∧ (A i j).den ≤ S := by
    intro i j
    have hmax_num : (A i j).num.natAbs ≤ max (A i j).num.natAbs (A i j).den := le_max_left _ _
    have hmax_den : (A i j).den ≤ max (A i j).num.natAbs (A i j).den := le_max_right _ _
    have hinner : max (A i j).num.natAbs (A i j).den ≤
      Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den) :=
      Finset.le_sup (f := fun j => max (A i j).num.natAbs (A i j).den) (Finset.mem_univ j)
    have hrow : Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den) ≤
      (Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den)) ⊔ max (b i).num.natAbs (b i).den :=
      le_sup_left
    have hsup : (Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den)) ⊔
      max (b i).num.natAbs (b i).den ≤ S :=
      Finset.le_sup (f := fun i => (Finset.univ.sup fun j =>
        max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) (Finset.mem_univ i)
    have hA_num : (A i j).num.natAbs ≤ S :=
      le_trans hmax_num (le_trans hinner (le_trans hrow hsup))
    have hA_den : (A i j).den ≤ S :=
      le_trans hmax_den (le_trans hinner (le_trans hrow hsup))
    exact ⟨hA_num, hA_den⟩
  have hb_bound : ∀ i, (b i).num.natAbs ≤ S ∧ (b i).den ≤ S := by
    intro i
    have hmax_num : (b i).num.natAbs ≤ max (b i).num.natAbs (b i).den := le_max_left _ _
    have hmax_den : (b i).den ≤ max (b i).num.natAbs (b i).den := le_max_right _ _
    have hrow : max (b i).num.natAbs (b i).den ≤
      (Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den)) ⊔ max (b i).num.natAbs (b i).den :=
      le_sup_right
    have hsup : (Finset.univ.sup (fun j => max (A i j).num.natAbs (A i j).den)) ⊔
      max (b i).num.natAbs (b i).den ≤ S :=
      Finset.le_sup (f := fun i => (Finset.univ.sup fun j =>
        max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) (Finset.mem_univ i)
    have hb_num : (b i).num.natAbs ≤ S :=
      le_trans hmax_num (le_trans hrow hsup)
    have hb_den : (b i).den ≤ S :=
      le_trans hmax_den (le_trans hrow hsup)
    exact ⟨hb_num, hb_den⟩
  have h_sup_le : ∀ M : ℕ, ((∀ i j, (A i j).num.natAbs ≤ M ∧ (A i j).den ≤ M) ∧
    ∀ i, (b i).num.natAbs ≤ M ∧ (b i).den ≤ M) → S ≤ M := by
    intro M ⟨hA, hb⟩
    apply Finset.sup_le
    intro i hi
    apply sup_le
    · apply Finset.sup_le
      intro j hj
      rcases hA i j with ⟨hnum, hden⟩
      apply max_le
      · exact hnum
      · exact hden
    · rcases hb i with ⟨hnum, hden⟩
      apply max_le
      · exact hnum
      · exact hden
  have h_pos : 0 < m → 1 ≤ S := by
    intro hmpos
    let i0 : Fin m := ⟨0, hmpos⟩
    rcases hb_bound i0 with ⟨_, hden⟩
    have hden_pos : 1 ≤ (b i0).den := by
      have h := (b i0).den_pos
      omega
    exact le_trans hden_pos hden
  exact ⟨⟨hA_bound, hb_bound⟩, h_sup_le, h_pos⟩

end AdversarialBco.Bit.Aux_fr_height

namespace AdversarialBco.Bit.Aux_fr_cleared_row


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_cleared_row {d : ℕ} (Ai : Fin d → ℚ) (bi D : ℚ) (hD : 0 < D) (α : Fin d → ℤ) (β : ℤ)
    (hα : ∀ j, (α j : ℚ) = D * Ai j) (hβ : (β : ℚ) = D * bi) (ρ : ℝ) (a : Fin d → ℝ) :
    (∑ j, (Ai j : ℝ) * a j + ρ * Real.sqrt (∑ j, (Ai j : ℝ) ^ 2) ≤ (bi : ℝ)) ↔
      ∑ j, (α j : ℝ) * a j + ρ * Real.sqrt (∑ j, (α j : ℝ) ^ 2) ≤ (β : ℝ) := by
  have hD' : (0 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD.le
  have hα' (j : Fin d) : (α j : ℝ) = (D : ℝ) * (Ai j : ℝ) := by
    have := hα j
    exact_mod_cast this
  have hβ' : (β : ℝ) = (D : ℝ) * (bi : ℝ) := by exact_mod_cast hβ
  have hDpos' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hsum1 : (∑ j : Fin d, (α j : ℝ) * a j) = (D : ℝ) * (∑ j : Fin d, (Ai j : ℝ) * a j) := by
    calc
      (∑ j : Fin d, (α j : ℝ) * a j) = (∑ j : Fin d, ((D : ℝ) * (Ai j : ℝ)) * a j) := by simp [hα']
      _ = (∑ j : Fin d, (D : ℝ) * ((Ai j : ℝ) * a j)) := by simp [mul_assoc]
      _ = (D : ℝ) * (∑ j : Fin d, (Ai j : ℝ) * a j) := by simp [Finset.mul_sum]
  have hsum2 : Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) = (D : ℝ) * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2) := by
    calc
      Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) = Real.sqrt (∑ j : Fin d, ((D : ℝ) * (Ai j : ℝ)) ^ 2) := by simp [hα']
      _ = Real.sqrt (∑ j : Fin d, (D : ℝ) ^ 2 * (Ai j : ℝ) ^ 2) := by simp [mul_pow]
      _ = Real.sqrt ((D : ℝ) ^ 2 * (∑ j : Fin d, (Ai j : ℝ) ^ 2)) := by simp [Finset.mul_sum]
      _ = Real.sqrt ((D : ℝ) ^ 2) * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2) := by rw [Real.sqrt_mul (sq_nonneg (D : ℝ))]
      _ = (D : ℝ) * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2) := by rw [Real.sqrt_sq hD']
  have hLHS : (∑ j : Fin d, (α j : ℝ) * a j) + ρ * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) =
      (D : ℝ) * ((∑ j : Fin d, (Ai j : ℝ) * a j) + ρ * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2)) := by
    calc
      (∑ j : Fin d, (α j : ℝ) * a j) + ρ * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) =
          ((D : ℝ) * (∑ j : Fin d, (Ai j : ℝ) * a j)) + ρ * ((D : ℝ) * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2)) := by rw [hsum1, hsum2]
      _ = (D : ℝ) * ((∑ j : Fin d, (Ai j : ℝ) * a j) + ρ * Real.sqrt (∑ j : Fin d, (Ai j : ℝ) ^ 2)) := by ring
  constructor
  · intro h
    rw [hLHS, hβ']
    exact mul_le_mul_of_nonneg_left h hD'
  · intro h
    rw [hLHS, hβ'] at h
    by_contra! hc
    have := mul_lt_mul_of_pos_left hc hDpos'
    linarith

end AdversarialBco.Bit.Aux_fr_cleared_row

namespace AdversarialBco.Bit.Aux_fr_test_sq


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_test_sq {d : ℕ} (α ah : Fin d → ℤ) (β : ℤ) (p : ℕ) :
    (0 ≤ 2 ^ (p + 1) * β - 2 * (α ⬝ᵥ ah) ∧
        2 ^ (2 * p) * (α ⬝ᵥ α) ≤ (2 ^ (p + 1) * β - 2 * (α ⬝ᵥ ah)) ^ 2) ↔
      ∑ j, (α j : ℝ) * ((ah j : ℝ) / 2 ^ p) + 1 / 2 * Real.sqrt (∑ j, (α j : ℝ) ^ 2) ≤ β := by
  set D := 2 ^ (p + 1) * β - 2 * (α ⬝ᵥ ah) with hD
  set n := α ⬝ᵥ α with hn
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    rw [hn, dotProduct]
    -- goal: 0 ≤ ↑(∑ i, α i * α i)
    have hsum_nonneg : 0 ≤ (∑ i : Fin d, α i * α i) := by
      refine Finset.sum_nonneg fun i _ => ?_
      have : 0 ≤ α i * α i := by
        -- α i * α i = (α i)^2 ≥ 0
        simpa [sq] using sq_nonneg (α i)
      exact this
    exact_mod_cast hsum_nonneg
  have h2p_pos : 0 < (2 ^ p : ℝ) := by
    exact_mod_cast pow_pos (by norm_num : 0 < (2 : ℕ)) p
  have h2p_nonneg : 0 ≤ (2 ^ p : ℝ) := le_of_lt h2p_pos
  have h2p1_pos : 0 < (2 ^ (p + 1) : ℝ) := by
    exact_mod_cast pow_pos (by norm_num : 0 < (2 : ℕ)) (p + 1)
  have h2p1_nonneg : 0 ≤ (2 ^ (p + 1) : ℝ) := le_of_lt h2p1_pos
  -- useful power identity
  have h_pow_eq : (2 ^ (2 * p) : ℝ) = ((2 : ℝ) ^ p) ^ 2 := by
    calc
      (2 ^ (2 * p) : ℝ) = ((2 : ℝ) ^ (2 * p)) := by norm_cast
      _ = ((2 : ℝ) ^ (p * 2)) := by rw [mul_comm 2 p]
      _ = (((2 : ℝ) ^ p) ^ 2) := by rw [pow_mul]
  have h_pow_eq' : ((2 : ℝ) ^ (p * 2)) = ((2 : ℝ) ^ p) ^ 2 := by
    rw [pow_mul]
  -- equality of the two sqrt expressions
  have h_sqrt_eq : Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) = Real.sqrt (n : ℝ) := by
    rw [hn, dotProduct]
    have hsum : (∑ j : Fin d, (α j : ℝ) ^ 2) = (∑ j : Fin d, (α j : ℝ) * (α j : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      ring_nf
    rw [hsum]
    simp [Int.cast_sum]
  -- Lemma: 2^p * √n ≤ D (in ℝ) ↔ (0 ≤ D ∧ 2^(2p) * n ≤ D^2) (in ℤ)
  have h_equiv_sqrt : ((2 : ℝ) ^ p * Real.sqrt (n : ℝ) ≤ (D : ℝ)) ↔
      (0 ≤ D ∧ (2 ^ (2 * p) * n : ℤ) ≤ D ^ 2) := by
    constructor
    · intro hle
      have hD_nonnegℝ : 0 ≤ (D : ℝ) := by
        have h_nonneg_prod : 0 ≤ (2 : ℝ) ^ p * Real.sqrt (n : ℝ) :=
          mul_nonneg h2p_nonneg (Real.sqrt_nonneg _)
        linarith
      have hD_nonneg : 0 ≤ D := by exact_mod_cast hD_nonnegℝ
      have hDsqℝ : ((2 : ℝ) ^ p) ^ 2 * (n : ℝ) ≤ (D : ℝ) ^ 2 := by
        -- from hle: 2^p * √n ≤ D
        -- square both sides: (2^p)^2 * n = (2^p * √n)^2 ≤ D^2
        have h_sq_sqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nonneg
        have h_left_sq : ((2 : ℝ) ^ p * Real.sqrt (n : ℝ)) ^ 2 = ((2 : ℝ) ^ p) ^ 2 * (n : ℝ) := by
          ring_nf
          rw [h_sq_sqrt]
        have h_sq_ineq : ((2 : ℝ) ^ p * Real.sqrt (n : ℝ)) ^ 2 ≤ (D : ℝ) ^ 2 := by
          have h_nonneg_prod : 0 ≤ (2 : ℝ) ^ p * Real.sqrt (n : ℝ) :=
            mul_nonneg h2p_nonneg (Real.sqrt_nonneg _)
          have h := mul_le_mul hle hle h_nonneg_prod hD_nonnegℝ
          simpa [pow_two] using h
        simpa [h_left_sq] using h_sq_ineq
      have hDsq : (2 ^ (2 * p) * n : ℤ) ≤ D ^ 2 := by
        have h_cast : ((2 ^ (2 * p) * n : ℤ) : ℝ) ≤ ((D ^ 2 : ℤ) : ℝ) := by
          simpa [h_pow_eq, h_pow_eq', mul_comm, mul_left_comm, mul_assoc] using hDsqℝ
        exact_mod_cast h_cast
      exact ⟨hD_nonneg, hDsq⟩
    · intro ⟨hD_nonneg, hDsq⟩
      have hD_nonnegℝ : 0 ≤ (D : ℝ) := by exact_mod_cast hD_nonneg
      have hDsqℝ : (2 ^ (2 * p) * n : ℝ) ≤ ((D : ℝ) ^ 2) := by
        exact_mod_cast hDsq
      have hDsqℝ' : ((2 : ℝ) ^ p) ^ 2 * (n : ℝ) ≤ (D : ℝ) ^ 2 := by
        simpa [h_pow_eq, h_pow_eq', mul_comm, mul_left_comm, mul_assoc] using hDsqℝ
      -- take square roots: from ((2^p)^2) * n ≤ D^2, we want 2^p * √n ≤ D
      have h_sqrt_mul : Real.sqrt (((2 : ℝ) ^ p) ^ 2 * (n : ℝ)) = Real.sqrt (((2 : ℝ) ^ p) ^ 2) * Real.sqrt (n : ℝ) :=
        Real.sqrt_mul (by positivity : 0 ≤ ((2 : ℝ) ^ p) ^ 2) (n : ℝ)
      have h_sqrt_sq_2p : Real.sqrt (((2 : ℝ) ^ p) ^ 2) = (2 : ℝ) ^ p :=
        Real.sqrt_sq h2p_nonneg
      have h_sqrt_sq_D : Real.sqrt ((D : ℝ) ^ 2) = (D : ℝ) :=
        Real.sqrt_sq hD_nonnegℝ
      -- Apply sqrt to both sides of hDsqℝ'
      have h_sqrt_ineq : Real.sqrt (((2 : ℝ) ^ p) ^ 2 * (n : ℝ)) ≤ Real.sqrt ((D : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hDsqℝ'
      calc
        (2 : ℝ) ^ p * Real.sqrt (n : ℝ) = Real.sqrt (((2 : ℝ) ^ p) ^ 2) * Real.sqrt (n : ℝ) := by
          rw [h_sqrt_sq_2p]
        _ = Real.sqrt (((2 : ℝ) ^ p) ^ 2 * (n : ℝ)) := by rw [h_sqrt_mul]
        _ ≤ Real.sqrt ((D : ℝ) ^ 2) := h_sqrt_ineq
        _ = (D : ℝ) := by rw [h_sqrt_sq_D]
  -- Lemma: the sum inequality is equivalent to 2^p * √n ≤ D
  have h_equiv_sum : (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) ≤ (β : ℝ)) ↔
      ((2 : ℝ) ^ p * Real.sqrt (n : ℝ) ≤ (D : ℝ)) := by
    constructor
    · intro hsum
      -- multiply hsum by 2^(p+1)
      have h_mul : (2 ^ (p + 1) : ℝ) * (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) ≤
          (2 ^ (p + 1) : ℝ) * (β : ℝ) := by
        nlinarith
      -- simplify the left side
      have h_simplify : (2 ^ (p + 1) : ℝ) * (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) =
          2 * ((α ⬝ᵥ ah : ℤ) : ℝ) + (2 : ℝ) ^ p * Real.sqrt (n : ℝ) := by
        calc
          (2 ^ (p + 1) : ℝ) * (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) =
              (2 ^ (p + 1) : ℝ) * (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ))) +
              (2 ^ (p + 1) : ℝ) * (1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) := by ring
          _ = (2 ^ (p + 1) : ℝ) * (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ))) +
              ((2 : ℝ) ^ p) * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by
            ring
          _ = (2 ^ (p + 1) : ℝ) * ((∑ j : Fin d, (α j : ℝ) * (ah j : ℝ)) / (2 ^ p : ℝ)) +
              ((2 : ℝ) ^ p) * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by
            simp [Finset.sum_div, mul_div_assoc]
          _ = (2 ^ (p + 1) : ℝ) * (((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ)) +
              ((2 : ℝ) ^ p) * Real.sqrt (n : ℝ) := by
            simp [dotProduct, Int.cast_sum, h_sqrt_eq]
          _ = 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) + ((2 : ℝ) ^ p) * Real.sqrt (n : ℝ) := by
            field_simp [h2p_pos.ne']
            ring
      -- now we have: 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) + (2^p) * √n ≤ 2^(p+1) * β
      -- rearrange to get 2^p * √n ≤ D
      have hD_eq : (D : ℝ) = (2 ^ (p + 1) : ℝ) * (β : ℝ) - 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) := by
        simp [hD, dotProduct, Int.cast_sum]
      have h_rearranged : ((2 : ℝ) ^ p) * Real.sqrt (n : ℝ) ≤ (D : ℝ) := by
        nlinarith
      exact h_rearranged
    · intro hle
      -- from 2^p * √n ≤ D, we want the sum inequality
      have hD_eq : (D : ℝ) = (2 ^ (p + 1) : ℝ) * (β : ℝ) - 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) := by
        simp [hD, dotProduct, Int.cast_sum]
      have h_rearranged : 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) + ((2 : ℝ) ^ p) * Real.sqrt (n : ℝ) ≤ (2 ^ (p + 1) : ℝ) * (β : ℝ) := by
        nlinarith
      -- now divide both sides by 2^(p+1)
      have h_divided : ((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (n : ℝ) ≤ (β : ℝ) := by
        have htemp : 2 * ((α ⬝ᵥ ah : ℤ) : ℝ) + ((2 : ℝ) ^ p) * Real.sqrt (n : ℝ) =
            (2 ^ (p + 1) : ℝ) * (((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (n : ℝ)) := by
          field_simp [h2p_pos.ne']
          ring
        nlinarith
      -- Now rewrite the sum expression to match
      have h_sum_eq : (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) =
          ((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (n : ℝ) := by
        calc
          (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) =
              (∑ j : Fin d, (α j : ℝ) * ((ah j : ℝ) / (2 ^ p : ℝ))) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by ring
          _ = (∑ j : Fin d, ((α j : ℝ) * (ah j : ℝ)) / (2 ^ p : ℝ)) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by
            refine congrArg (fun t => t + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2)) ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          _ = (∑ j : Fin d, (α j : ℝ) * (ah j : ℝ)) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by
            rw [Finset.sum_div]
          _ = ((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (∑ j : Fin d, (α j : ℝ) ^ 2) := by
            simp [dotProduct, Int.cast_sum]
          _ = ((α ⬝ᵥ ah : ℤ) : ℝ) / (2 ^ p : ℝ) + 1 / 2 * Real.sqrt (n : ℝ) := by rw [h_sqrt_eq]
      rw [h_sum_eq]
      exact h_divided
  -- Now combine the two equivalences
  rw [h_equiv_sum, h_equiv_sqrt]

end AdversarialBco.Bit.Aux_fr_test_sq

namespace AdversarialBco.Bit.Aux_fr_d1_signs


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_d1_signs {m : ℕ} (α β : Fin m → ℝ) (n x₀ : ℝ) (hx₀ : ∀ i, α i * x₀ ≤ β i)
    (hdiam : ∀ x y : ℝ, (∀ i, α i * x ≤ β i) → (∀ i, α i * y ≤ β i) → |x - y| ≤ n) :
    (∃ i, 0 < α i) ∧ ∃ i, α i < 0 := by
  constructor
  · by_contra h
    push Not at h
    have hrow : ∀ i, α i * (x₀ + (|n| + 1)) ≤ β i := by
      intro i
      have := mul_nonpos_of_nonpos_of_nonneg (h i) (by positivity : (0 : ℝ) ≤ |n| + 1)
      nlinarith [hx₀ i]
    have := hdiam _ _ hrow hx₀
    rw [add_sub_cancel_left, abs_of_pos (by positivity)] at this
    linarith [le_abs_self n]
  · by_contra h
    push Not at h
    have hrow : ∀ i, α i * (x₀ - (|n| + 1)) ≤ β i := by
      intro i
      have := mul_nonneg (h i) (by positivity : (0 : ℝ) ≤ |n| + 1)
      nlinarith [hx₀ i]
    have := hdiam _ _ hrow hx₀
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)] at this
    linarith [le_abs_self n]

end AdversarialBco.Bit.Aux_fr_d1_signs

namespace AdversarialBco.Bit.Aux_fr_d1_readoff


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_d1_readoff {m : ℕ} (α β : Fin m → ℝ) (lo hi : ℝ)
    (hlo : ∀ i, α i < 0 → β i / α i ≤ lo) (hlo' : ∃ i, α i < 0 ∧ β i / α i = lo)
    (hhi : ∀ i, 0 < α i → hi ≤ β i / α i) (hhi' : ∃ i, 0 < α i ∧ β i / α i = hi)
    (hz : ∀ i, α i = 0 → 0 ≤ β i) (x : ℝ) :
    (∀ i, α i * x ≤ β i) ↔ lo ≤ x ∧ x ≤ hi := by
  constructor
  · intro h
    rcases hlo' with ⟨i, hαi_neg, h_eq⟩
    have hle : β i / α i ≤ x := by
      rw [div_le_iff_of_neg hαi_neg]
      rw [mul_comm]
      exact h i
    have hlo_le : lo ≤ x := h_eq ▸ hle
    rcases hhi' with ⟨j, hαj_pos, h_eq'⟩
    have hle' : x ≤ β j / α j := by
      rw [le_div_iff₀ hαj_pos]
      rw [mul_comm]
      exact h j
    have hhi_le : x ≤ hi := h_eq' ▸ hle'
    exact ⟨hlo_le, hhi_le⟩
  · intro ⟨hlo_le, hhi_le⟩ i
    rcases lt_trichotomy (α i) 0 with (hneg | heq | hpos)
    · have hdiv : β i / α i ≤ x :=
        le_trans (hlo i hneg) hlo_le
      rw [div_le_iff_of_neg hneg] at hdiv
      rw [mul_comm]
      exact hdiv
    · rw [heq]
      simp [hz i heq]
    · have hdiv : x ≤ β i / α i :=
        le_trans hhi_le (hhi i hpos)
      rw [le_div_iff₀ hpos] at hdiv
      rw [mul_comm]
      exact hdiv

end AdversarialBco.Bit.Aux_fr_d1_readoff

namespace AdversarialBco.Bit.Aux_fr_d1_centre


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_d1_centre (lo hi : ℝ) (h : 1 ≤ hi - lo) (ln ld hn hd : ℤ) (K : ℕ)
    (hld : 0 < ld) (hhd : 0 < hd) (hln : ln.natAbs ≤ K) (hld' : ld.natAbs ≤ K) (hhn : hn.natAbs ≤ K)
    (hhd' : hd.natAbs ≤ K) :
    (∀ x : ℝ, |x - (lo + hi) / 2| ≤ 1 / 2 → lo ≤ x ∧ x ≤ hi) ∧
      ((ln : ℝ) / ld + (hn : ℝ) / hd) / 2 = ((ln * hd + hn * ld : ℤ) : ℝ) / ((2 * ld * hd : ℤ) : ℝ) ∧
      (ln * hd + hn * ld).natAbs ≤ 2 * K ^ 2 ∧ 0 < 2 * ld * hd ∧ (2 * ld * hd).natAbs ≤ 2 * K ^ 2 := by
  have hlo_le_hi : lo ≤ hi := by linarith
  have hld_ne_zero : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne.symm
  have hhd_ne_zero : (hd : ℝ) ≠ 0 := by exact_mod_cast hhd.ne.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx_abs := abs_le.mp hx
    rcases hx_abs with ⟨hx_low, hx_high⟩
    have hlow : lo ≤ x := by
      have hx_low' : (lo + hi - 1) / 2 ≤ x := by linarith
      have hlo_bound : lo ≤ (lo + hi - 1) / 2 := by
        nlinarith
      linarith
    have hhigh : x ≤ hi := by
      have hx_high' : x ≤ (lo + hi + 1) / 2 := by linarith
      have hhi_bound : (lo + hi + 1) / 2 ≤ hi := by
        nlinarith
      linarith
    exact ⟨hlow, hhigh⟩
  · field_simp [hld_ne_zero, hhd_ne_zero]
    push_cast
    ring_nf
  · have hsum : (ln * hd + hn * ld).natAbs ≤ (ln * hd).natAbs + (hn * ld).natAbs :=
      Int.natAbs_add_le _ _
    have h1 : (ln * hd).natAbs ≤ K * K := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hln hhd'
    have h2 : (hn * ld).natAbs ≤ K * K := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hhn hld'
    have hsum' : (ln * hd).natAbs + (hn * ld).natAbs ≤ 2 * (K * K) := by
      omega
    have hsq : K * K = K ^ 2 := by ring
    rw [hsq] at hsum'
    omega
  · positivity
  · have hprod : (2 * ld * hd).natAbs = 2 * ld.natAbs * hd.natAbs := by
      calc
        (2 * ld * hd).natAbs = ((2 : ℤ) * (ld * hd)).natAbs := by ring_nf
        _ = (2 : ℤ).natAbs * (ld * hd).natAbs := by rw [Int.natAbs_mul]
        _ = (2 : ℤ).natAbs * (ld.natAbs * hd.natAbs) := by rw [Int.natAbs_mul]
        _ = 2 * (ld.natAbs * hd.natAbs) := by norm_num
        _ = 2 * ld.natAbs * hd.natAbs := by ring
    rw [hprod]
    have hbound : ld.natAbs * hd.natAbs ≤ K * K := Nat.mul_le_mul hld' hhd'
    have hsq : K * K = K ^ 2 := by ring
    rw [hsq] at hbound
    nlinarith

end AdversarialBco.Bit.Aux_fr_d1_centre

namespace AdversarialBco.Bit.Aux_fr_lam_sq


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_lam_sq (d : ℕ) (hd : 2 ≤ d) (ρ DA : ℝ) (hρ : 0 < ρ)
    (hDA : DA ≤ ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) :
    Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 = 1 + 1 / (4 * d * ((d : ℝ) + 1)) ∧
      Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 + DA / ρ ^ 2 ≤
        1 + 33 / (128 * d * ((d : ℝ) + 1)) ∧
      Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) =
        (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) := by
  have hd_ge_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have hd_plus_one_ne_zero : (d : ℝ) + 1 ≠ 0 := by linarith
  have hd_sq_ne_one : (d : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hd_ne_one : (d : ℝ) - 1 ≠ 0 := by
    nlinarith
  have hnonneg : 0 ≤ (2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1)) := by
    positivity
  have hsqrt_sq : Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 =
      (2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1)) :=
    Real.sq_sqrt hnonneg
  have h_expr_eq : (2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1)) = 1 + 1 / (4 * d * ((d : ℝ) + 1)) := by
    field_simp [hd_ne_zero, hd_plus_one_ne_zero]
    ring
  have hsqrt_sq_eq : Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 =
      1 + 1 / (4 * d * ((d : ℝ) + 1)) := by
    rw [hsqrt_sq, h_expr_eq]
  have hρ_sq_pos : 0 < ρ ^ 2 := pow_pos hρ 2
  have hρ_sq_nonneg : 0 ≤ ρ ^ 2 := hρ_sq_pos.le
  have hDA_div : DA / ρ ^ 2 ≤ 1 / (128 * d * ((d : ℝ) + 1)) := by
    calc
      DA / ρ ^ 2 ≤ (ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) / ρ ^ 2 :=
        div_le_div_of_nonneg_right hDA hρ_sq_nonneg
      _ = 1 / (128 * d * ((d : ℝ) + 1)) := by
        field_simp [hρ_sq_pos.ne']
  have h2 : Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 + DA / ρ ^ 2 ≤
      1 + 33 / (128 * d * ((d : ℝ) + 1)) := by
    rw [hsqrt_sq_eq]
    calc
      1 + 1 / (4 * d * ((d : ℝ) + 1)) + DA / ρ ^ 2 ≤
          1 + 1 / (4 * d * ((d : ℝ) + 1)) + 1 / (128 * d * ((d : ℝ) + 1)) := by
        gcongr
      _ = 1 + (1 / (4 * d * ((d : ℝ) + 1)) + 1 / (128 * d * ((d : ℝ) + 1))) := by ring
      _ = 1 + 33 / (128 * d * ((d : ℝ) + 1)) := by
        field_simp [hd_ne_zero, hd_plus_one_ne_zero]
        ring
  have h3 : Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 *
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) = (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) := by
    rw [hsqrt_sq_eq]
    field_simp [hd_sq_ne_one, hd_ne_one, hd_ne_zero, hd_plus_one_ne_zero]
    ring
  exact And.intro hsqrt_sq_eq (And.intro h2 h3)

end AdversarialBco.Bit.Aux_fr_lam_sq

namespace AdversarialBco.Bit.Aux_fr_mat_step


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_mat_step (d p : ℕ) (hd : 2 ≤ d) (Ah vl vk sh : ℝ) (hs : sh ≠ 0) :
    (d : ℝ) * (2 * d + 1) ^ 2 * (((d : ℝ) + 1) * sh * Ah - 2 * vl * vk) /
        (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1) * (((d : ℝ) + 1) * sh)) =
      2 ^ p * ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) *
        ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) *
          (Ah / 2 ^ p - 2 / ((d : ℝ) + 1) * (vl / 2 ^ p * (vk / 2 ^ p)) / (sh / 2 ^ p))) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hdp1 : (d : ℝ) + 1 ≠ 0 := by linarith
  have hdsq : (d : ℝ) ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hp : (2 : ℝ) ^ p ≠ 0 := pow_ne_zero p (by norm_num : (2 : ℝ) ≠ 0)
  field_simp [hd0, hd1, hdp1, hdsq, hs, hp]
  ring

end AdversarialBco.Bit.Aux_fr_mat_step

namespace AdversarialBco.Bit.Aux_fr_rnd_vec


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_rnd_vec {d : ℕ} (x : Fin d → ℝ) (p : ℕ) :
    ((fun j => (round ((2 : ℝ) ^ p * x j) : ℝ) / 2 ^ p) - x) ⬝ᵥ
        ((fun j => (round ((2 : ℝ) ^ p * x j) : ℝ) / 2 ^ p) - x) ≤ d * (1 / 2 ^ (p + 1)) ^ 2 := by
  set r := fun j : Fin d => (round ((2 : ℝ) ^ p * x j) : ℝ) / ((2 : ℝ) ^ p) with hr
  have h2pos : 0 < ((2 : ℝ) ^ p) := pow_pos (by norm_num) p
  have h_sq_bound : ∀ j, (r j - x j) ^ 2 ≤ ((1 : ℝ) / ((2 : ℝ) ^ (p + 1))) ^ 2 := by
    intro j
    have h_abs : |r j - x j| ≤ (1 : ℝ) / ((2 : ℝ) ^ (p + 1)) := by
      have hround := abs_sub_round ((2 : ℝ) ^ p * x j)
      have h_comm : |(round ((2 : ℝ) ^ p * x j) : ℝ) - (2 : ℝ) ^ p * x j| ≤ (1 : ℝ) / 2 := by
        rw [abs_sub_comm]
        exact hround
      have h_eq : (round ((2 : ℝ) ^ p * x j) : ℝ) / ((2 : ℝ) ^ p) - x j =
          ((round ((2 : ℝ) ^ p * x j) : ℝ) - (2 : ℝ) ^ p * x j) / ((2 : ℝ) ^ p) := by
        field_simp [h2pos.ne.symm]
      calc
        |r j - x j| = |(round ((2 : ℝ) ^ p * x j) : ℝ) / ((2 : ℝ) ^ p) - x j| := rfl
        _ = |((round ((2 : ℝ) ^ p * x j) : ℝ) - (2 : ℝ) ^ p * x j) / ((2 : ℝ) ^ p)| := by rw [h_eq]
        _ = |(round ((2 : ℝ) ^ p * x j) : ℝ) - (2 : ℝ) ^ p * x j| / |((2 : ℝ) ^ p)| := by rw [abs_div]
        _ = |(round ((2 : ℝ) ^ p * x j) : ℝ) - (2 : ℝ) ^ p * x j| / ((2 : ℝ) ^ p) := by
          rw [abs_of_pos h2pos]
        _ ≤ ((1 : ℝ) / 2) / ((2 : ℝ) ^ p) := by
          gcongr
        _ = (1 : ℝ) / (2 * ((2 : ℝ) ^ p)) := by ring
        _ = (1 : ℝ) / ((2 : ℝ) ^ (p + 1)) := by
          rw [pow_succ, mul_comm]
    rw [← sq_abs (r j - x j)]
    have h_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ (p + 1)) := by
      positivity
    gcongr
  calc
    (r - x) ⬝ᵥ (r - x) = ∑ j : Fin d, (r j - x j) * (r j - x j) := rfl
    _ = ∑ j : Fin d, (r j - x j) ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    _ ≤ ∑ j : Fin d, ((1 : ℝ) / ((2 : ℝ) ^ (p + 1))) ^ 2 :=
      Finset.sum_le_sum (fun j _ => h_sq_bound j)
    _ = (Finset.card (Finset.univ : Finset (Fin d))) • (((1 : ℝ) / ((2 : ℝ) ^ (p + 1))) ^ 2) := by
      rw [Finset.sum_const]
    _ = d • (((1 : ℝ) / ((2 : ℝ) ^ (p + 1))) ^ 2) := by
      simp
    _ = d * (((1 : ℝ) / ((2 : ℝ) ^ (p + 1))) ^ 2) := by
      simp

end AdversarialBco.Bit.Aux_fr_rnd_vec

namespace AdversarialBco.Bit.Aux_fr_rnd_ediv


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

open Int

theorem _root_.AdversarialBco.Bit.fr_rnd_ediv (u v : ℤ) (hv : 0 < v) :
    (2 * u + v) / (2 * v) = round ((u : ℝ) / v) ∧ |(((2 * u + v) / (2 * v) : ℤ) : ℝ) - (u : ℝ) / v| ≤ 1 / 2 := by
  have hdiv_eq : (2 * u + v) / (2 * v) = round ((u : ℝ) / v) := by
    rw [round_eq]
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne.symm
    have h_expr : ((u : ℝ) / (v : ℝ) + 1/2) = (((2*u + v : ℤ) : ℝ) / ((2*v : ℤ) : ℝ)) := by
      push_cast
      field_simp [hv']
    rw [h_expr]
    have hv2 : 0 ≤ 2*v := by linarith
    set n : ℕ := Int.toNat (2*v) with hn_def
    have hn_eq : (n : ℝ) = ((2*v : ℤ) : ℝ) := by
      dsimp [n]
      have h := Int.toNat_of_nonneg hv2
      exact_mod_cast h
    have hfloor : ⌊((2*u + v : ℤ) : ℝ) / (n : ℝ)⌋ = (2*u + v) / (2*v) := by
      calc
        ⌊((2*u + v : ℤ) : ℝ) / (n : ℝ)⌋ = ⌊((2*u + v : ℤ) : ℝ)⌋ / (n : ℤ) := Int.floor_div_natCast _ _
        _ = (2*u + v) / (n : ℤ) := by rw [Int.floor_intCast]
        _ = (2*u + v) / (2*v) := by
          have hn_eq_int : (n : ℤ) = 2*v := by
            dsimp [n]
            exact_mod_cast Int.toNat_of_nonneg hv2
          rw [hn_eq_int]
    simpa [hn_eq] using hfloor.symm
  have h_abs : |(((2 * u + v) / (2 * v) : ℤ) : ℝ) - (u : ℝ) / v| ≤ 1 / 2 := by
    rw [hdiv_eq]
    rw [abs_sub_comm]
    exact abs_sub_round ((u : ℝ) / v)
  exact And.intro hdiv_eq h_abs

end AdversarialBco.Bit.Aux_fr_rnd_ediv

namespace AdversarialBco.Bit.Aux_fr_det_factor


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_det_factor (d : ℕ) (hd : 1 ≤ d) :
    (1 + 33 / (128 * d * ((d : ℝ) + 1))) ^ d * Real.exp (-1 / ((d : ℝ) + 1)) ≤
      Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) := by
  have hdpos' : (0 : ℝ) < (d : ℝ) + 1 := by
    have : (0 : ℕ) ≤ d := Nat.zero_le _
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hx_nonneg : 0 ≤ 33 / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
    refine div_nonneg (by norm_num) ?_
    nlinarith
  set x := 33 / (128 * (d : ℝ) * ((d : ℝ) + 1)) with hx_def
  have h_add_one_le_exp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have h_nonneg_add_one : 0 ≤ 1 + x := by linarith
  have h_pow : (1 + x) ^ d ≤ (Real.exp x) ^ d :=
    pow_le_pow_left₀ h_nonneg_add_one h_add_one_le_exp d
  have h_exp_pow : (Real.exp x) ^ d = Real.exp ((d : ℝ) * x) := by
    simpa [mul_comm] using (Real.exp_nat_mul x d).symm
  have h_mul : (1 + x) ^ d * Real.exp (-1 / ((d : ℝ) + 1)) ≤
      (Real.exp x) ^ d * Real.exp (-1 / ((d : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right h_pow (le_of_lt (Real.exp_pos _))
  rw [h_exp_pow] at h_mul
  rw [← Real.exp_add] at h_mul
  have h_compute : (d : ℝ) * x + (-1 / ((d : ℝ) + 1)) = -(95 / (128 * ((d : ℝ) + 1))) := by
    dsimp [x]
    field_simp
    ring
  rw [h_compute] at h_mul
  exact h_mul

end AdversarialBco.Bit.Aux_fr_det_factor

namespace AdversarialBco.Bit.Aux_fr_lmax_step


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_lmax_step {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (Ak As An : Matrix (Fin n) (Fin n) ℝ)
    (Λ ρ DA : ℝ) (hρ : 0 < ρ) (hΛρ : ρ ^ 2 ≤ Λ)
    (hAs : ∀ v : Fin n → ℝ, v ⬝ᵥ (As *ᵥ v) ≤ (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (v ⬝ᵥ (Ak *ᵥ v)))
    (hAk : ∀ v : Fin n → ℝ, v ⬝ᵥ (Ak *ᵥ v) ≤ Λ * (v ⬝ᵥ v))
    (hD : ∀ v : Fin n → ℝ,
      |v ⬝ᵥ ((An - Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 • As) *ᵥ v)| ≤ DA * (v ⬝ᵥ v))
    (hDA : DA ≤ ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) (v : Fin n → ℝ) :
    v ⬝ᵥ (An *ᵥ v) ≤
      ((d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1))) * Λ *
        (v ⬝ᵥ v) := by
  set c := Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 with hc_def
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    apply pow_two_nonneg
  have hc_val : c = ((2 * (d : ℝ) + 1) ^ 2) / (4 * (d : ℝ) * ((d : ℝ) + 1)) := by
    rw [hc_def]
    have h_nonneg : 0 ≤ ((2 * (d : ℝ) + 1) ^ 2) / (4 * (d : ℝ) * ((d : ℝ) + 1)) := by
      refine div_nonneg ?_ ?_
      · apply pow_two_nonneg
      · positivity
    rw [Real.sq_sqrt h_nonneg]
  have hpos_d : 0 < (d : ℝ) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hpos_dp1 : 0 < (d : ℝ) + 1 := by linarith
  have hpos_dm1 : 0 < (d : ℝ) - 1 := by
    have hd' : (1 : ℝ) < (d : ℝ) := by
      have : (2 : ℕ) ≤ d := hd
      have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
      linarith
    linarith
  have hDv := hD v
  rw [abs_le] at hDv
  rcases hDv with ⟨hDv_low, hDv_high⟩
  have h_expand : (An - Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 • As) *ᵥ v =
      An *ᵥ v - (Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2) • (As *ᵥ v) := by
    calc
      (An - Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 • As) *ᵥ v
          = (An *ᵥ v) - ((Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2) • As) *ᵥ v := by
        rw [Matrix.sub_mulVec]
      _ = An *ᵥ v - (Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2) • (As *ᵥ v) := by
        rw [Matrix.smul_mulVec]
  rw [h_expand] at hDv_high
  rw [dotProduct_sub, dotProduct_smul] at hDv_high
  -- dotProduct_smul gives v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w); for ℝ, • = *
  have hDv_high' : v ⬝ᵥ (An *ᵥ v) - c * (v ⬝ᵥ (As *ᵥ v)) ≤ DA * (v ⬝ᵥ v) := by
    simpa [smul_eq_mul] using hDv_high
  have h_ineq1 : v ⬝ᵥ (An *ᵥ v) ≤ c * (v ⬝ᵥ (As *ᵥ v)) + DA * (v ⬝ᵥ v) := by
    linarith
  have hAsv := hAs v
  have h_ineq2 : c * (v ⬝ᵥ (As *ᵥ v)) ≤ c * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (v ⬝ᵥ (Ak *ᵥ v))) :=
    mul_le_mul_of_nonneg_left hAsv hc_nonneg
  have h_ineq3 : c * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (v ⬝ᵥ (Ak *ᵥ v))) =
      ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (v ⬝ᵥ (Ak *ᵥ v)) := by
    rw [hc_val]
    have h_ddm1_ne_zero : (d : ℝ) ^ 2 - 1 ≠ 0 := by
      intro hzero
      have : (d : ℝ) ^ 2 = 1 := by linarith
      have hd' : (1 : ℝ) < (d : ℝ) := by
        have : (2 : ℕ) ≤ d := hd
        have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
        linarith
      nlinarith
    field_simp [hpos_d.ne.symm, hpos_dp1.ne.symm, hpos_dm1.ne.symm, h_ddm1_ne_zero]
    ring
  have h_ineq4 : v ⬝ᵥ (An *ᵥ v) ≤
      ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (v ⬝ᵥ (Ak *ᵥ v)) + DA * (v ⬝ᵥ v) := by
    linarith
  have hAkv := hAk v
  have h_nonneg_coeff : 0 ≤ (d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) := by
    refine div_nonneg ?_ ?_
    · have : 0 ≤ (d : ℝ) := by linarith
      have : 0 ≤ (2 * (d : ℝ) + 1) ^ 2 := pow_two_nonneg _
      nlinarith
    · positivity
  have h_ineq5 : ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (v ⬝ᵥ (Ak *ᵥ v)) ≤
      ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (Λ * (v ⬝ᵥ v)) :=
    mul_le_mul_of_nonneg_left hAkv h_nonneg_coeff
  have h_ineq6 : v ⬝ᵥ (An *ᵥ v) ≤
      ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (Λ * (v ⬝ᵥ v)) + DA * (v ⬝ᵥ v) := by
    linarith
  have h_nonneg_dot : 0 ≤ v ⬝ᵥ v := by
    simpa using dotProduct_self_star_nonneg (R := ℝ) v
  have hDAv : DA * (v ⬝ᵥ v) ≤ (ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right hDA h_nonneg_dot
  have hDAv2 : (ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) * (v ⬝ᵥ v) ≤
      (Λ / (128 * d * ((d : ℝ) + 1))) * (v ⬝ᵥ v) := by
    have h_div : ρ ^ 2 / (128 * d * ((d : ℝ) + 1)) ≤ Λ / (128 * d * ((d : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hΛρ (by positivity)
    exact mul_le_mul_of_nonneg_right h_div h_nonneg_dot
  have h_ineq7 : v ⬝ᵥ (An *ᵥ v) ≤
      ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (Λ * (v ⬝ᵥ v)) +
      (Λ / (128 * d * ((d : ℝ) + 1))) * (v ⬝ᵥ v) := by
    linarith
  calc
    v ⬝ᵥ (An *ᵥ v) ≤
        ((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * (Λ * (v ⬝ᵥ v)) +
        (Λ / (128 * d * ((d : ℝ) + 1))) * (v ⬝ᵥ v) := h_ineq7
    _ = (((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) * Λ +
        (Λ / (128 * d * ((d : ℝ) + 1)))) * (v ⬝ᵥ v) := by ring
    _ = (((d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1))) + (1 / (128 * d * ((d : ℝ) + 1)))) * Λ * (v ⬝ᵥ v) := by ring
    _ = ((d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1))) * Λ * (v ⬝ᵥ v) := by
      ring

end AdversarialBco.Bit.Aux_fr_lmax_step

namespace AdversarialBco.Bit.Aux_fr_abs_margin


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_abs_margin (d : ℕ) (hd : 2 ≤ d) (ρ DA Dc : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hDA0 : 0 ≤ DA) (hDA : DA ≤ ρ ^ 2 / (128 * d * ((d : ℝ) + 1))) (hDc : Dc ≤ 3 * ρ / (128 * d * ((d : ℝ) + 1))) :
    DA < Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) ^ 2 * ρ ^ 2 ∧
      Dc + DA / (Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) * ρ) ≤
        (Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1))) - 1) * ρ := by
  set lam := Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * (d : ℝ) * ((d : ℝ) + 1))) with hlam
  have hd1 : 1 ≤ d := by omega
  have hdpos_nat : 0 < d := by omega
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlam_nonneg : 0 ≤ lam := Real.sqrt_nonneg _
  have hlam_ge_one : 1 ≤ lam := by
    have hlamsq_ge_one : 1 ≤ lam ^ 2 := by
      rw [hlam, Real.sq_sqrt (by positivity : 0 ≤ ((2 * (d : ℝ) + 1) ^ 2 / (4 * (d : ℝ) * ((d : ℝ) + 1))))]
      refine (one_le_div ?_).mpr ?_
      · positivity
      · nlinarith
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (lam ^ 2) := Real.sqrt_le_sqrt hlamsq_ge_one
      _ = lam := Real.sqrt_sq hlam_nonneg
  have hlamsq_ge_one : 1 ≤ lam ^ 2 := by
    rw [hlam, Real.sq_sqrt (by positivity : 0 ≤ ((2 * (d : ℝ) + 1) ^ 2 / (4 * (d : ℝ) * ((d : ℝ) + 1))))]
    refine (one_le_div ?_).mpr ?_
    · positivity
    · nlinarith
  have hρsq_pos : 0 < ρ ^ 2 := pow_pos hρ 2
  have h_denom_gt_one : 1 < 128 * (d : ℝ) * ((d : ℝ) + 1) := by
    nlinarith
  have h_first : DA < lam ^ 2 * ρ ^ 2 := by
    have h_lt : ρ ^ 2 / (128 * (d : ℝ) * ((d : ℝ) + 1)) < ρ ^ 2 :=
      div_lt_self hρsq_pos h_denom_gt_one
    have hρsq_le : ρ ^ 2 ≤ lam ^ 2 * ρ ^ 2 := by
      nlinarith
    nlinarith
  have h_second : Dc + DA / (lam * ρ) ≤ (lam - 1) * ρ := by
    have lamρ_pos : 0 < lam * ρ := mul_pos (by linarith) hρ
    have h_ρ_le_lamρ : ρ ≤ lam * ρ := by
      nlinarith
    have h_div_le : DA / (lam * ρ) ≤ DA / ρ :=
      div_le_div_of_nonneg_left hDA0 hρ h_ρ_le_lamρ
    have h_sum_le : Dc + DA / (lam * ρ) ≤ Dc + DA / ρ := by nlinarith
    have h_DA_div_ρ_le : DA / ρ ≤ ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
      calc
        DA / ρ ≤ (ρ ^ 2 / (128 * (d : ℝ) * ((d : ℝ) + 1))) / ρ :=
          div_le_div_of_nonneg_right hDA hρ.le
        _ = ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
          field_simp [hρ.ne.symm]
    have h_sum_le2 : Dc + DA / ρ ≤ ρ / (32 * (d : ℝ) * ((d : ℝ) + 1)) := by
      have h_add : Dc + DA / ρ ≤ 3 * ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) + ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
        nlinarith
      have h_eq : 3 * ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) + ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) =
          ρ / (32 * (d : ℝ) * ((d : ℝ) + 1)) := by
        field_simp [hdpos.ne.symm]
        ring
      linarith
    have h_pb := pb_cap_lam d hd1
    rcases h_pb with ⟨h_pb1, h_pb2⟩
    have h_denom_pos : 0 < 32 * (d : ℝ) * ((d : ℝ) + 1) := by positivity
    have h_denom2_pos : 0 < 10 * (d : ℝ) * ((d : ℝ) + 1) := by positivity
    have h_denom3_pos : 0 < 2 * (2 * (d : ℝ) + 1) ^ 2 := by positivity
    have h_frac_le : (1 : ℝ) / (32 * (d : ℝ) * ((d : ℝ) + 1)) ≤ (1 : ℝ) / (10 * (d : ℝ) * ((d : ℝ) + 1)) := by
      refine (one_div_le_one_div ?_ ?_).mpr ?_
      · positivity
      · positivity
      · nlinarith
    have h_ineq : (1 : ℝ) / (32 * (d : ℝ) * ((d : ℝ) + 1)) ≤ lam - 1 := by
      linarith
    have h_third : ρ / (32 * (d : ℝ) * ((d : ℝ) + 1)) ≤ (lam - 1) * ρ := by
      calc
        ρ / (32 * (d : ℝ) * ((d : ℝ) + 1)) = ((1 : ℝ) / (32 * (d : ℝ) * ((d : ℝ) + 1))) * ρ := by ring
        _ ≤ (lam - 1) * ρ := mul_le_mul_of_nonneg_right h_ineq hρ.le
    nlinarith
  exact And.intro h_first h_second

end AdversarialBco.Bit.Aux_fr_abs_margin

namespace AdversarialBco.Bit.Aux_fr_center_cap


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_center_cap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (Λ : ℝ)
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) (a z : Fin n → ℝ)
    (hz : (z - a) ⬝ᵥ (A⁻¹ *ᵥ (z - a)) ≤ 1) : (z - a) ⬝ᵥ (z - a) ≤ Λ := by
  set u := z - a with hu
  have hu_dot_self_nonneg : 0 ≤ u ⬝ᵥ u := by
    simpa using dotProduct_star_self_nonneg u
  have h_det_unit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have h_mul_inv : A * A⁻¹ = 1 := mul_nonsing_inv A h_det_unit
  have h_cs := hA.star_dotProduct_mulVec_mul_le u (A⁻¹ *ᵥ u)
  have h_cs' : (u ⬝ᵥ u) * (u ⬝ᵥ u) ≤ (u ⬝ᵥ (A *ᵥ u)) * (u ⬝ᵥ (A⁻¹ *ᵥ u)) := by
    simpa [Matrix.mulVec_mulVec, h_mul_inv, Matrix.one_mulVec, dotProduct_comm] using h_cs
  have h_bound1 : u ⬝ᵥ (A *ᵥ u) ≤ Λ * (u ⬝ᵥ u) := hΛ u
  have h_bound2 : u ⬝ᵥ (A⁻¹ *ᵥ u) ≤ 1 := hz
  have h_nonneg1 : 0 ≤ u ⬝ᵥ (A *ᵥ u) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg u
  have h_nonneg2 : 0 ≤ u ⬝ᵥ (A⁻¹ *ᵥ u) := by
    simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg u
  have h_nonneg_b : 0 ≤ Λ * (u ⬝ᵥ u) := mul_nonneg hΛ0 hu_dot_self_nonneg
  have h_sq_bound : (u ⬝ᵥ u) * (u ⬝ᵥ u) ≤ Λ * (u ⬝ᵥ u) := by
    apply le_trans h_cs' ?_
    have h_temp := mul_le_mul (b := Λ * (u ⬝ᵥ u)) (d := 1) h_bound1 h_bound2 h_nonneg2 h_nonneg_b
    simpa [mul_one] using h_temp
  by_cases h_zero : u ⬝ᵥ u = 0
  · rw [h_zero]
    exact hΛ0
  · have h_pos : 0 < u ⬝ᵥ u := by
      by_contra! hle
      apply h_zero
      linarith
    nlinarith

end AdversarialBco.Bit.Aux_fr_center_cap

namespace AdversarialBco.Bit.Aux_fr_entry_cap


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_entry_cap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (Λ : ℝ)
    (hΛ : ∀ v : Fin n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ Λ * (v ⬝ᵥ v)) (l k : Fin n) : |A l k| ≤ Λ := by
  have hPsd := hA.posSemidef
  have h_symm : A l k = A k l := by
    have h := hA.isHermitian.apply k l
    simpa using h
  by_cases h_eq : l = k
  · subst h_eq
    have h_nonneg : 0 ≤ A l l := hPsd.diag_nonneg
    have h_le : A l l ≤ Λ := by
      have h := hΛ (Pi.single l 1)
      simpa using h
    rw [abs_of_nonneg h_nonneg]
    exact h_le
  · have h_add_nonneg : 0 ≤ A l l + A l k + A k l + A k k := by
      have h := hPsd.dotProduct_mulVec_nonneg (Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ))
      simpa [mulVec_add, dotProduct_add, add_comm, add_left_comm] using h
    have h_sub_nonneg : 0 ≤ A l l - A l k - A k l + A k k := by
      have h := hPsd.dotProduct_mulVec_nonneg (Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ))
      simpa [sub_eq_add_neg, mulVec_add, dotProduct_add, add_comm, add_left_comm, add_assoc, mulVec_neg] using h
    have h_add_le : A l l + A l k + A k l + A k k ≤ 2 * Λ := by
      have h := hΛ (Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ))
      have h_lhs : ((Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ)) ⬝ᵥ (A *ᵥ (Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ)))) =
          A l l + A l k + A k l + A k k := by
        simp [mulVec_add, dotProduct_add, add_comm, add_left_comm]
      have h_rhs : ((Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ)) ⬝ᵥ (Pi.single l (1 : ℝ) + Pi.single k (1 : ℝ))) = (2 : ℝ) := by
        simp [h_eq]
        norm_num
      rw [h_lhs, h_rhs] at h
      simpa [mul_comm] using h
    have h_sub_le : A l l - A l k - A k l + A k k ≤ 2 * Λ := by
      have h := hΛ (Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ))
      have h_lhs : ((Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ)) ⬝ᵥ (A *ᵥ (Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ)))) =
          A l l - A l k - A k l + A k k := by
        simp [sub_eq_add_neg, mulVec_add, dotProduct_add, add_comm, add_left_comm, add_assoc, mulVec_neg]
      have h_rhs : ((Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ)) ⬝ᵥ (Pi.single l (1 : ℝ) - Pi.single k (1 : ℝ))) = (2 : ℝ) := by
        simp [h_eq]
        norm_num
      rw [h_lhs, h_rhs] at h
      simpa [mul_comm] using h
    have h_ll : A l l ≤ Λ := by
      have h := hΛ (Pi.single l 1)
      simpa using h
    have h_kk : A k k ≤ Λ := by
      have h := hΛ (Pi.single k 1)
      simpa using h
    have h_add_nonneg' : 0 ≤ A l l + A k k + 2 * A l k := by
      rw [h_symm] at h_add_nonneg
      linarith
    have h_sub_nonneg' : 0 ≤ A l l + A k k - 2 * A l k := by
      rw [h_symm] at h_sub_nonneg
      linarith
    have h_add_le' : A l l + A k k + 2 * A l k ≤ 2 * Λ := by
      rw [h_symm] at h_add_le
      linarith
    have h_sub_le' : A l l + A k k - 2 * A l k ≤ 2 * Λ := by
      rw [h_symm] at h_sub_le
      linarith
    have h_abs : |A l k| ≤ (A l l + A k k) / 2 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have h_sum_le : (A l l + A k k) / 2 ≤ Λ := by linarith
    linarith

end AdversarialBco.Bit.Aux_fr_entry_cap

namespace AdversarialBco.Bit.Aux_fr_margin_iff


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.fr_margin_iff {d m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall y r ⊆ {x | ∀ i, ⟪A i, x⟫_ℝ ≤ b i} ↔ ∀ i, ⟪A i, y⟫_ℝ + r * ‖A i‖ ≤ b i := by
  constructor
  · intro h i
    by_cases hAi : A i = 0
    · have hy_mem : y ∈ Metric.closedBall y r := by
        rw [Metric.mem_closedBall, dist_self]
        exact hr
      have h0 : ⟪A i, y⟫_ℝ ≤ b i := h hy_mem i
      simpa [hAi] using h0
    · have hnorm_pos : 0 < ‖A i‖ := norm_pos_iff.mpr hAi
      have hnorm_ne_zero : ‖A i‖ ≠ 0 := by linarith
      set x := y + (r / ‖A i‖) • A i with hx_def
      have hx_mem : x ∈ Metric.closedBall y r := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hnorm_x_sub_y : ‖x - y‖ = r := by
          dsimp [x]
          rw [add_sub_cancel_left, norm_smul]
          have h_nonneg : 0 ≤ r / ‖A i‖ := div_nonneg hr (by linarith)
          rw [Real.norm_of_nonneg h_nonneg]
          field_simp [hnorm_ne_zero]
        rw [hnorm_x_sub_y]
      have h_bound : ⟪A i, x⟫_ℝ ≤ b i := h hx_mem i
      dsimp [x] at h_bound
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at h_bound
      have hcalc : (r / ‖A i‖) * ‖A i‖ ^ 2 = r * ‖A i‖ := by
        field_simp [hnorm_ne_zero]
      rw [hcalc] at h_bound
      exact h_bound
  · intro h x hx i
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have hineq : ⟪A i, x⟫_ℝ ≤ b i := by
      calc
        ⟪A i, x⟫_ℝ = ⟪A i, y + (x - y)⟫_ℝ := by rw [add_sub_cancel]
        _ = ⟪A i, y⟫_ℝ + ⟪A i, x - y⟫_ℝ := by rw [inner_add_right]
        _ ≤ ⟪A i, y⟫_ℝ + ‖A i‖ * ‖x - y‖ := by
          gcongr
          exact real_inner_le_norm (A i) (x - y)
        _ ≤ ⟪A i, y⟫_ℝ + ‖A i‖ * r := by
          gcongr
        _ ≤ b i := by
          simpa [mul_comm] using h i
    exact hineq

end AdversarialBco.Bit.Aux_fr_margin_iff
