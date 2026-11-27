/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowT
public import AdversarialBco.Bit.Transfer.XBLRowP
public import AdversarialBco.Bit.Transfer.XTriRow
public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# The row provider of BL, part 2: tactics and a bound

`rwgo`, `rwenv`: the side conditions on the named cells of XBLInv.lean; `abs_sum_mul_lt`: a sum of `k ≤ N` products
of integers at most `2^E` is below `2^ℓ` when `N 2^{2E} < 2^ℓ`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP

variable {d : ℕ}

/-- Side conditions on the named cells of XBLInv.lean: `omega`, after unfolding the names. -/
macro "rwgo" : tactic => `(tactic| first | omega | decide |
  ((simp only [rD, rM, rMk, rOne, rPF, sZ, s2pF, sEps, sDS, aMuS, aAS, rEE, oE, aWE] at *) <;> omega) | fail "rwgo")

/-- `rpenv` with the names of XBLInv.lean unfolded in its side conditions. -/
macro "rwenv" : tactic =>
  `(tactic| (simp (disch := rwgo) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

theorem abs_sum_mul_lt {Xv Yv : ℕ → ℤ} {N E ℓ : ℕ} (bX : ∀ k < N, |Xv k| ≤ 2 ^ E) (bY : ∀ k < N, |Yv k| ≤ 2 ^ E)
    (hℓ : N * 2 ^ (2 * E) < 2 ^ ℓ) : ∀ k ≤ N, |∑ j ∈ Finset.range k, Xv j * Yv j| < 2 ^ ℓ := fun k hk => by
  have bXY : ∀ k < N, |Xv k * Yv k| ≤ ((2 ^ (2 * E) : ℕ) : ℤ) := fun k hk => by
    rw [abs_mul]; push_cast
    calc |Xv k| * |Yv k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bX k hk) (bY k hk) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  have h1 : |∑ j ∈ Finset.range k, Xv j * Yv j| ≤ k * ((2 ^ (2 * E) : ℕ) : ℤ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => |Xv j * Yv j|) ((2 ^ (2 * E) : ℕ) : ℤ)
      (fun j hj => bXY j (by rw [Finset.mem_range] at hj; omega))
    simpa using this
  have h2 : (k : ℤ) * ((2 ^ (2 * E) : ℕ) : ℤ) ≤ N * 2 ^ (2 * E) := by
    push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  have h3 : (N : ℤ) * 2 ^ (2 * E) < 2 ^ ℓ := by exact_mod_cast hℓ
  linarith

end AdversarialBco.Bit.Transfer.BLM.RowM
