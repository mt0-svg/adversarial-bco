/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.BLLink

@[expose] public section

/-!
# (O3) for `apQ`: clearing the denominators of a call

`clearQ` (Bit/RoutQ.lean) turns a call `D : CallQ d` into the integer problem `EllI d`: each row times `D_i`, the
quadratic constraint times `D_H`, the objective and the accuracy times `D_P` (with `f̂ = D_f D_P f`). Over `ℝ` the
integer problem has the same region, and its objective is `D_P` times the call's objective ("a constraint or the
objective multiplied by a positive integer is the same constraint, the same minimiser").
-/

namespace AdversarialBco.Bit.ApQ

open AdversarialBco.Bit.BLP (CallQ)
open AdversarialBco.Bit.RQ
open AdversarialBco.Poly (oNorm oBall)
open Matrix

variable {d : ℕ}

/-- The region of the integer problem, `{y | α_i·y ≤ β_i, yᵀHy/2 - g·y ≤ ℓ, |y| ≤ R}`, in `ℝ^d`. -/
def regionI (I : EllI d) : Set (Fin d → ℝ) :=
  {y | (∀ i, (fun j => (I.α i j : ℝ)) ⬝ᵥ y ≤ I.β i) ∧
    y ⬝ᵥ (I.H.map ((↑) : ℤ → ℝ) *ᵥ y) / 2 - (fun j => (I.g j : ℝ)) ⬝ᵥ y ≤ I.ℓ ∧ oNorm y ≤ I.R}

/-- The objective of the integer problem, `yᵀPy/2 - (f̂/D_f)·y`. -/
noncomputable def GI (I : EllI d) (y : Fin d → ℝ) : ℝ :=
  y ⬝ᵥ (I.P.map ((↑) : ℤ → ℝ) *ᵥ y) / 2 - (fun j => (I.f j : ℝ) / I.Df) ⬝ᵥ y

theorem clr_eq (D : ℕ) (x : ℚ) (h : x.den ∣ D) : ((clr D x : ℤ) : ℚ) = D * x := by
  obtain ⟨k, hk⟩ := h
  have hk' : D / x.den = k := by rw [hk, Nat.mul_div_cancel_left _ x.den_pos]
  simp only [clr, hk']
  push_cast
  rw [hk]; push_cast
  rw [show ((x.den : ℚ) * k) * x = k * (x * x.den) by ring, Rat.mul_den_eq_num]
  ring

theorem clr_eqR (D : ℕ) (x : ℚ) (h : x.den ∣ D) : ((clr D x : ℤ) : ℝ) = D * (x : ℝ) := by
  have := clr_eq D x h
  have h' : (((clr D x : ℤ) : ℚ) : ℝ) = ((D * x : ℚ) : ℝ) := by rw [this]
  push_cast at h'; exact h'

theorem quadDen_pos (D : CallQ d) : 0 < quadDen D := by
  unfold quadDen; positivity

theorem objDen_pos (D : CallQ d) : 0 < objDen D := by
  unfold objDen; positivity

theorem linDen_pos (D : CallQ d) : 0 < linDen D := by
  unfold linDen; positivity

theorem clearQ_H (D : CallQ d) (i j : Fin d) : (((clearQ D).H i j : ℤ) : ℝ) = quadDen D * ((D.H i j : ℚ) : ℝ) :=
  clr_eqR _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.trans
    (Finset.dvd_prod_of_mem (fun j => (D.H i j).den) (Finset.mem_univ j))
    (Finset.dvd_prod_of_mem (fun i => ∏ j, (D.H i j).den) (Finset.mem_univ i))) _) _)

theorem clearQ_g (D : CallQ d) (j : Fin d) : (((clearQ D).g j : ℤ) : ℝ) = quadDen D * ((D.g j : ℚ) : ℝ) :=
  clr_eqR _ _ (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (Finset.dvd_prod_of_mem (fun j => (D.g j).den) (Finset.mem_univ j)) _) _)

theorem clearQ_ℓ (D : CallQ d) : (((clearQ D).ℓ : ℤ) : ℝ) = quadDen D * ((D.ℓ : ℚ) : ℝ) :=
  clr_eqR _ _ (Dvd.intro_left _ rfl)

theorem clearQ_P (D : CallQ d) (i j : Fin d) : (((clearQ D).P i j : ℤ) : ℝ) = objDen D * ((D.P i j : ℚ) : ℝ) :=
  clr_eqR _ _ (Dvd.dvd.trans (Finset.dvd_prod_of_mem (fun j => (D.P i j).den) (Finset.mem_univ j))
    (Finset.dvd_prod_of_mem (fun i => ∏ j, (D.P i j).den) (Finset.mem_univ i)))

theorem clearQ_f (D : CallQ d) (j : Fin d) :
    (((clearQ D).f j : ℤ) : ℝ) / (clearQ D).Df = objDen D * ((D.f j : ℚ) : ℝ) := by
  have h := clr_eqR (linDen D) (D.f j) (Finset.dvd_prod_of_mem (fun j => (D.f j).den) (Finset.mem_univ j))
  have hl : (0 : ℝ) < linDen D := by exact_mod_cast linDen_pos D
  show ((clr (linDen D) (D.f j) * (objDen D : ℤ) : ℤ) : ℝ) / (linDen D : ℕ) = _
  push_cast; rw [h]; field_simp

theorem clearQ_e (D : CallQ d) : (clearQ D).e = objDen D * D.e := rfl

theorem dot_scale (c : ℝ) (a y : Fin d → ℝ) : (fun j => c * a j) ⬝ᵥ y = c * (a ⬝ᵥ y) := by
  simp only [dotProduct, Finset.mul_sum]; ring_nf

theorem quad_scale (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    y ⬝ᵥ ((c • M) *ᵥ y) = c * (y ⬝ᵥ (M *ᵥ y)) := by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

end AdversarialBco.Bit.ApQ
