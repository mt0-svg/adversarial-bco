/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOSpec

@[expose] public section

/-!
# BL-O's PARAM in the tail's cells

The facts on PARAM that the tail reads, at `parN ne d n`: the fields on the grid `2^{-pF}` and `1/ê` as the integer
`tlHN ne d n`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

theorem tlN_onG_W (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).W := onG_div_pow _ _

/-- `1/ê` as an integer. -/
def tlHN (ne d n : ℕ) : ℤ := 2 ^ ((parN ne d n).p - 3 * ne.size - 6 * d.size - 64)

theorem tlHN_pos (ne d n : ℕ) : 0 < tlHN ne d n := by unfold tlHN; positivity

theorem tlN_eHat (ne d n : ℕ) : (parN ne d n).eHat = 1 / ((tlHN ne d n : ℤ) : ℚ) := by
  rw [tlHN]; push_cast; rfl

theorem tlHN_eq (ne d n : ℕ) : (((parN ne d n).eHat⁻¹ : ℚ) : ℝ) = ((tlHN ne d n : ℤ) : ℝ) := by
  rw [tlN_eHat, one_div, inv_inv]; push_cast; rfl

theorem NeO_pos {d n : ℕ} (k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ NeO d n k := by
  unfold NeO
  have h1 : 0 < 2 ^ (17 + k) := by positivity
  have h2 : 0 < d ^ 3 := pow_pos (by omega) 3
  have h3 : 0 < n ^ 4 := pow_pos (by omega) 4
  have : 0 < 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := by positivity
  omega

end AdversarialBco.Unified.ProgO
