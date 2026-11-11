/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Cells
public import AdversarialBco.Conj1Lower.Frame

@[expose] public section

/-!
# The dent in the frame: the geometric part of Lemma 9.4

The dent of Dent.lean with the square root `A = frameA w S` of the clipped metric of Frame.lean, on `ℝ^d`: convex
(Lemma D (a)), Lipschitz with the constant `κ r₁ / w` (Lemma D (b) and (F1)), between `0` and
`κ (r₁ ‖x - m‖ / w + ε)` (Lemma D (a), `φ(a) ≤ r₁ a + ε` and (F1)), and `0` at the tip. With `w = w* = κ r₁ / L`
this is the Lipschitz constant `L` and the range `3L/2 + g` of Lemma 9.4 on the unit ball when `‖m‖ ≤ 1/2`.
-/

open Matrix
open scoped RealInnerProductSpace

namespace AdversarialBco.Lower

theorem dent_frame_convexOn {d : ℕ} (w κ ε r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r₁) (m θ : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (dent (frameA w S) m κ ε r₁ θ) :=
  dent_convexOn _ m κ ε r₁ hκ hε hr θ

theorem dent_frame_lipschitz {d : ℕ} (w κ ε r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian)
    (hw : 0 < w) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (m θ x y : EuclideanSpace ℝ (Fin d)) :
    |dent (frameA w S) m κ ε r₁ θ x - dent (frameA w S) m κ ε r₁ θ y| ≤ κ * r₁ / w * ‖x - y‖ :=
  (dent_lipschitz _ m κ ε r₁ hκ hε hr θ x y).trans
    (mul_le_mul_of_nonneg_right (lipschitz_const_le w κ r₁ S hS hw hκ hr) (norm_nonneg _))

theorem dent_frame_nonneg {d : ℕ} (w κ ε r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r₁) (m θ x : EuclideanSpace ℝ (Fin d)) : 0 ≤ dent (frameA w S) m κ ε r₁ θ x :=
  dent_nonneg _ m κ ε r₁ hκ hε hr θ x

theorem dent_frame_self {d : ℕ} (w κ ε r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r₁) (m θ : EuclideanSpace ℝ (Fin d)) : dent (frameA w S) m κ ε r₁ θ θ = 0 :=
  dent_self _ m κ ε r₁ hκ hε hr θ

theorem dent_frame_le {d : ℕ} (w κ ε r₁ : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) (hw : 0 < w)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hr : 0 ≤ r₁) (m θ x : EuclideanSpace ℝ (Fin d)) :
    dent (frameA w S) m κ ε r₁ θ x ≤ κ * (r₁ * (‖x - m‖ / w) + ε) := by
  refine (dent_le_bowl _ m κ ε r₁ hκ hε hr θ x).trans ?_
  unfold bowl
  refine mul_le_mul_of_nonneg_left ?_ hκ
  refine (huber_le_lin r₁ ε _ (norm_nonneg _)).trans ?_
  have := norm_frameA_apply_le w S hS hw (x - m)
  nlinarith

end AdversarialBco.Lower
