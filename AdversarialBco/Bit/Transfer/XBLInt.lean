/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-!
# BL's round over the integers

Pure lemmas between BL's rationals (Bit/BLPure.lean) and the integers the round computes: the scale `pt'`
(`ptQ_int`) and the play (`play_int`) as fractions of integers.
-/

section


/-- `max(1, (bN/bD)/(1 - eN/P))` by cross multiplication. -/
theorem AdversarialBco.Bit.Transfer.BLM.ptQ_int (bN bD eN P : ℤ) (hbD : 0 < bD) (hP : 0 < P) (he : eN < P) :
    max 1 (((bN : ℚ) / bD) / (1 - (eN : ℚ) / P)) =
      if bD * (P - eN) < bN * P then ((bN * P : ℤ) : ℚ) / ((bD * (P - eN) : ℤ) : ℚ) else 1 := by
  have hP_ne : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne.symm
  have hbD_ne : (bD : ℚ) ≠ 0 := by exact_mod_cast hbD.ne.symm
  have hP_sub_eN_pos : 0 < (P : ℚ) - (eN : ℚ) := sub_pos.mpr (by exact_mod_cast he)
  have hP_sub_eN_ne : (P : ℚ) - (eN : ℚ) ≠ 0 := by linarith
  have h_denom_pos : 0 < (bD : ℚ) * ((P : ℚ) - (eN : ℚ)) := mul_pos (by exact_mod_cast hbD) hP_sub_eN_pos
  have h_eq : ((bN : ℚ) / (bD : ℚ)) / (1 - (eN : ℚ) / (P : ℚ)) =
      ((bN : ℚ) * (P : ℚ)) / ((bD : ℚ) * ((P : ℚ) - (eN : ℚ))) := by
    field_simp [hP_ne, hbD_ne, hP_sub_eN_ne]
  rw [h_eq]
  by_cases h : (bD : ℚ) * ((P : ℚ) - (eN : ℚ)) < (bN : ℚ) * (P : ℚ)
  · have h_int : bD * (P - eN) < bN * P := by exact_mod_cast h
    rw [ite_eq_left h_int]
    push_cast
    have h_one_lt_div : 1 < ((bN : ℚ) * (P : ℚ)) / ((bD : ℚ) * ((P : ℚ) - (eN : ℚ))) :=
      (one_lt_div h_denom_pos).mpr h
    exact max_eq_right (le_of_lt h_one_lt_div)
  · have h_not_int : ¬ (bD * (P - eN) < bN * P) := by exact_mod_cast h
    rw [ite_eq_right h_not_int]
    have h_div_le_one : ((bN : ℚ) * (P : ℚ)) / ((bD : ℚ) * ((P : ℚ) - (eN : ℚ))) ≤ 1 :=
      (div_le_one h_denom_pos).mpr (le_of_not_gt h)
    exact max_eq_left h_div_le_one

end

section

open Matrix


/-- BL's play `μ + A (X / pt)` with `μ = μ̂/D_S`, `A = Â/D_S`, `X = X̂/D_X`, `pt = ptN/ptD`, over one common
denominator `D_S D_X ptN`. -/
theorem AdversarialBco.Bit.Transfer.BLM.play_int {d : ℕ} (DS DX ptN ptD : ℤ) (muS : Fin d → ℤ)
    (aS : Fin d → Fin d → ℤ) (xh : Fin d → ℤ) (hDS : 0 < DS) (hDX : 0 < DX) (hN : 0 < ptN) (hD : 0 < ptD)
    (j : Fin d) :
    ((fun j => (muS j : ℚ) / DS) + (Matrix.of fun i k => (aS i k : ℚ) / DS) *ᵥ
        (((ptN : ℚ) / ptD)⁻¹ • fun k => (xh k : ℚ) / DX)) j =
      ((muS j * DX * ptN + (∑ k, aS j k * xh k) * ptD : ℤ) : ℚ) / ((DS * DX * ptN : ℤ) : ℚ) := by
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have hDX' : (DX : ℚ) ≠ 0 := by exact_mod_cast hDX.ne'
  have hN' : (ptN : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hD' : (ptD : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
  push_cast
  simp only [Finset.sum_mul]
  field_simp [hDS', hDX', hN', hD']
  field_simp [hDS', hDX', hN']
  have h_DX_ptN : (DX : ℚ) * (ptN : ℚ) ≠ 0 := mul_ne_zero hDX' hN'
  simp only [mul_add, Finset.mul_sum]
  field_simp [h_DX_ptN]
  simp [mul_comm, mul_assoc]

end

