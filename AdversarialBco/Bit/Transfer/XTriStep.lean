/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriScanLoop

@[expose] public section

/-!
# TRI-M, one draw of the core on the machine: the base point

The expression `ẑ_i := X̂_μ,i 2^{2p} + ẑ_i` of the base point of a draw (`ieZ`) and the bounds of its integers
(`abs_tzZ_le`, `abs_mulVec_le`, `abs_le_mono`).
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `ẑ_i := X̂_μ,i 2^{2p} + ẑ_i`. -/
def ieZ (aXm aZ sP2 nr : ℕ) : IE := .op .add (.op .mul (.arr aXm nr) (.sc sP2)) (.arr aZ nr)

theorem abs_tzZ_le {X : PosZ d} {Y : Fin d → ℤ} {P2 : ℤ} {E : ℕ} (bX1 : ∀ i, |X.1 i| ≤ 2 ^ E)
    (bX2 : ∀ i l, |X.2 i l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E) (bP : |P2| ≤ 2 ^ E) (i : Fin d) :
    |tzZ X Y P2 i| ≤ 2 ^ (2 * E + d + 1) := by
  have h1 : |X.1 i * P2| ≤ 2 ^ (2 * E + d) :=
    (by rw [two_mul]; exact absI_mul_le (bX1 i) bP : |X.1 i * P2| ≤ 2 ^ (2 * E)).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : |∑ l, X.2 i l * Y l| ≤ 2 ^ (2 * E + d) := dot_abs_le (fun l => bX2 i l) bY
  calc |tzZ X Y P2 i| ≤ |X.1 i * P2| + |∑ l, X.2 i l * Y l| := abs_add_le _ _
    _ ≤ 2 ^ (2 * E + d) + 2 ^ (2 * E + d) := add_le_add h1 h2
    _ = 2 ^ (2 * E + d + 1) := by ring

theorem abs_mulVec_le {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} {E : ℕ} (bM : ∀ i l, |M i l| ≤ 2 ^ E)
    (bx : ∀ l, |x l| ≤ 2 ^ E) (i : Fin d) : |(M *ᵥ x) i| ≤ 2 ^ (2 * E + d) :=
  dot_abs_le (fun l => bM i l) bx

theorem abs_le_mono {x : ℤ} {E F : ℕ} (h : |x| ≤ 2 ^ E) (hEF : E ≤ F) : |x| ≤ 2 ^ F :=
  h.trans (pow_le_pow_right₀ (by norm_num) hEF)

end AdversarialBco.Bit.Transfer
