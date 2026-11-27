/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2p
public import AdversarialBco.Bit.Transfer.XBLInt
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# BL's round, R2 PLAYPT in mode `run`: the integers of the machine are BL's rationals

BL's point `X = μ + (1 - λ) A ξ` over one common denominator (`XQ_int`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open Matrix AdversarialBco.BitRAM AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- BL's point `X = μ + (1 - λ) A ξ` with `μ = μ̂/Dμ`, `λ = λ̂/PF`, `A = Â/P`, `ξ = Γ/G`, over the common denominator
`Dμ PF P G`. -/
theorem XQ_int (Dm PF P G lh : ℤ) (muh : Fin d → ℤ)
    (ah : Fin d → Fin d → ℤ) (gam : Fin d → ℤ) (hDm : 0 < Dm) (hPF : 0 < PF) (hP : 0 < P) (hG : 0 < G) (j : Fin d) :
    ((fun j => (muh j : ℚ) / Dm) + (1 - (lh : ℚ) / PF) • ((Matrix.of fun i k => (ah i k : ℚ) / P) *ᵥ
        fun k => (gam k : ℚ) / G)) j =
      ((muh j * PF * P * G + (PF - lh) * (∑ k, ah j k * gam k) * Dm : ℤ) : ℚ) / ((Dm * PF * P * G : ℤ) : ℚ) := by
  have h1 : (Dm : ℚ) ≠ 0 := by exact_mod_cast hDm.ne'
  have h2 : (PF : ℚ) ≠ 0 := by exact_mod_cast hPF.ne'
  have h3 : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne'
  have h4 : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hs : ((Matrix.of fun i k => (ah i k : ℚ) / P) *ᵥ fun k => (gam k : ℚ) / G) j =
      ((∑ k, ah j k * gam k : ℤ) : ℚ) / (P * G) := by
    simp only [mulVec, dotProduct, of_apply]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
  push_cast
  field_simp

end AdversarialBco.Bit.Transfer.BLM
