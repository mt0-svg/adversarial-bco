/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ApQ.Ell

@[expose] public section

/-!
# (O3) for `apQ`

`o3SpecQ_apQ : O3SpecQ apQ` (Bit/BLLink.lean) from `ellRI_spec`, (O3) on the integer problem: Theorems ELL-R and
BIS-R, part (b),. The call `D` and its integer problem `clearQ D` have the same region and
proportional objectives (Bit/ApQ/Clear.lean).
-/

namespace AdversarialBco.Bit.ApQ

open AdversarialBco.Bit.BLP (CallQ O3SpecQ)
open AdversarialBco.Bit.RQ
open AdversarialBco.Poly (oNorm oBall)
open Matrix

variable {d : ℕ}

/-- The point `x / 2^(ellExp I)` over `ℝ`. -/
noncomputable def ptI (I : EllI d) (x : Fin d → ℤ) : Fin d → ℝ := fun j => (x j : ℝ) / 2 ^ ellExp I

/-- (O3) on the integer problem (the projection theorem, part (b)). -/
theorem ellRI_spec (I : EllI d) (a0 : Fin d → ℝ) (hR : 1 ≤ I.R) (hr : 0 < I.r) (hball : oBall a0 I.r ⊆ regionI I)
    (hP : (I.P.map ((↑) : ℤ → ℝ)).PosDef) (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef) (he : 0 < I.e)
    (hDf : 0 < I.Df) :
    ∃ x, ellRI I = some x ∧ ptI I x ∈ regionI I ∧ ∀ y ∈ regionI I, GI I (ptI I x) ≤ GI I y + I.e := by
  obtain ⟨x, hx, hm, hg⟩ := ellRI_spec' I a0 hR hr hball hP hH he hDf
  exact ⟨x, hx, hm, hg⟩

theorem o3SpecQ_apQ : O3SpecQ apQ := by
  intro d D a0 hR hr hball hP hH he
  set I := clearQ D with hI
  have hreg : regionI I = D.region := clearQ_region D
  have hob : (0 : ℝ) < objDen D := by exact_mod_cast objDen_pos D
  have hP' : (I.P.map ((↑) : ℤ → ℝ)).PosDef := by
    have : I.P.map ((↑) : ℤ → ℝ) = (objDen D : ℝ) • D.P.map ((↑) : ℚ → ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_P D i j
    rw [this]; exact hP.smul hob
  have hH' : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef := by
    have : I.H.map ((↑) : ℤ → ℝ) = (quadDen D : ℝ) • D.H.map ((↑) : ℚ → ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_H D i j
    rw [this]; exact hH.smul (by positivity)
  have he' : 0 < I.e := by
    rw [hI, clearQ_e]; have : (0 : ℚ) < objDen D := by exact_mod_cast objDen_pos D
    exact mul_pos this he
  have hDf : 0 < I.Df := linDen_pos D
  obtain ⟨x, hx, hmem, hopt⟩ := ellRI_spec I a0 (by rw [hI, clearQ_R]; exact hR) (by rw [hI, clearQ_r]; exact hr)
    (by rw [hreg]; exact hball) hP' hH' he' hDf
  refine ⟨fun i => (x i : ℚ) / 2 ^ ellExp I, ?_, ?_, ?_⟩
  · simp only [apQ, ← hI, hx, Option.map_some]
  · have : (fun j => (((x j : ℚ) / 2 ^ ellExp I : ℚ) : ℝ)) = ptI I x := by
      funext j; simp only [ptI]; push_cast; rfl
    rw [this, ← hreg]; exact hmem
  · intro y hy
    have : (fun j => (((x j : ℚ) / 2 ^ ellExp I : ℚ) : ℝ)) = ptI I x := by
      funext j; simp only [ptI]; push_cast; rfl
    rw [this]
    have h := hopt y (by rw [hreg]; exact hy)
    rw [clearQ_G, clearQ_G, hI, clearQ_e] at h
    push_cast at h
    have : (objDen D : ℝ) * D.obj (ptI I x) ≤ (objDen D : ℝ) * (D.obj y + D.e) := by linarith
    exact le_of_mul_le_mul_left this hob

end AdversarialBco.Bit.ApQ
