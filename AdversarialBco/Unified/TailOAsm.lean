/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOMag
public import AdversarialBco.Unified.MagRun
public import AdversarialBco.Unified.MagExp
public import AdversarialBco.Bit.Transfer.XBLCommit

@[expose] public section

/-!
# The arithmetic of the tail's assembly

The tail of BL-O's round is R5 and R7's scalars (`xR57`), then the run of the tail `xtailO` (R10 to R15 with the two
ELL-O calls). `asm_arith`: the budget of that command below `C (W + E + U + 1)^k`; `asm_E`: the exponent condition of
the round from `Cn (W + E₀ + 1)^kn ≤ E`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

/-- The budget of the tail command and the conditions of `XV.r57` below `C (W + E + U + 1)^k`. -/
theorem asm_arith (Ct kt W E U d : ℕ) (hdW : d ≤ W) :
    r57Units d (2 * E + U + 8) + (2 + (2 + (midUnits d (2 * E + U + 8) +
      Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt))) ≤
        (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    130 * (2 * E + U + 8) + 120 < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    d * d + d < (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) ∧
    Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ (10 ^ 6 + Ct * 400 ^ kt) * (W + E + U + 1) ^ (kt + 2) := by
  set X := W + E + U + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hX2 : X ^ 2 ≤ X ^ (kt + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hXk : X ^ kt ≤ X ^ (kt + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have h9 : d + (2 * E + U + 8) + 1 ≤ 9 * X := by omega
  have h400 : W + (36 * (2 * E + U + 8) + 30) + 1 ≤ 400 * X := by omega
  have h57 := units_r57 d (2 * E + U + 8)
  have hmid : midUnits d (2 * E + U + 8) ≤ 81000 * X ^ 2 := by
    have := (units_mid d (2 * E + U + 8)).trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left h9 2))
    calc midUnits d (2 * E + U + 8) ≤ 1000 * (9 * X) ^ 2 := this
      _ = 81000 * X ^ 2 := by ring
  have hct : Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ Ct * 400 ^ kt * X ^ (kt + 2) := by
    calc Ct * (W + (36 * (2 * E + U + 8) + 30) + 1) ^ kt ≤ Ct * (400 * X) ^ kt :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h400 _)
      _ = Ct * 400 ^ kt * X ^ kt := by rw [mul_pow, mul_assoc]
      _ ≤ Ct * 400 ^ kt * X ^ (kt + 2) := Nat.mul_le_mul_left _ hXk
  have hdd : d * d ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hK : (10 ^ 6 + Ct * 400 ^ kt) * X ^ (kt + 2) = 10 ^ 6 * X ^ (kt + 2) + Ct * 400 ^ kt * X ^ (kt + 2) := by
    ring
  rw [hK]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The exponent condition of the round from `Cn (W + E₀ + 1)^kn ≤ E`. -/
theorem asm_E (Cm km Cx kx W E0 E K d : ℕ) (hdW : d ≤ W) (hKW : K ≤ 528 * W)
    (hE : (Cm + Cx * 5400 ^ kx + 600) * (W + E0 + 1) ^ (km + kx + 1) ≤ E) :
    Cm * (W + E0 + 1) ^ km ≤ E ∧ Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx + K ≤ E ∧ d ≤ E := by
  set Y := W + E0 + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hm : Y ^ km ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have hx : Y ^ kx ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have h1 : Y ≤ Y ^ (km + kx + 1) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (km + kx + 1) := Nat.pow_le_pow_right hY1 (by omega)
  have hb : W + (5 * (2 * K + 10) + 5) + 1 ≤ 5400 * Y := by omega
  have hcx : Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx ≤ Cx * 5400 ^ kx * Y ^ (km + kx + 1) := by
    calc Cx * (W + (5 * (2 * K + 10) + 5) + 1) ^ kx ≤ Cx * (5400 * Y) ^ kx :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
      _ = Cx * 5400 ^ kx * Y ^ kx := by rw [mul_pow, mul_assoc]
      _ ≤ Cx * 5400 ^ kx * Y ^ (km + kx + 1) := Nat.mul_le_mul_left _ hx
  have hcm : Cm * Y ^ km ≤ Cm * Y ^ (km + kx + 1) := Nat.mul_le_mul_left _ hm
  have hK' : (Cm + Cx * 5400 ^ kx + 600) * Y ^ (km + kx + 1) =
      Cm * Y ^ (km + kx + 1) + Cx * 5400 ^ kx * Y ^ (km + kx + 1) + 600 * Y ^ (km + kx + 1) := by ring
  rw [hK'] at hE
  refine ⟨by omega, by omega, by omega⟩

end AdversarialBco.Unified.ProgO
