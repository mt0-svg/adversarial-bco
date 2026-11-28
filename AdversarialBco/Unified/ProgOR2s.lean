/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOR2
public import AdversarialBco.Unified.PrmKLink
public import AdversarialBco.Unified.BLOGeom

@[expose] public section

/-!
# BL-O's R2 in mode `run`, the contract

`specR2 : SpecR2 (fun L => xR2 L) kR2` and `progR2 : ProgR2`: from R1a's end in mode `run st`, `xR2` writes BL-O's play
`playO .. t` into `aPl` (`PostA`), `pt' = ptO orc c (XO c st ξ')` into `sPtN`, `sPtD` and `Â Γ` into `aWv`
(`RunDat`), within `4000 (W + E + 1)^3` units, when `W + E₀ + 1 ≤ E`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open AdversarialBco.Bit (gsm_prec)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The units -/

/-- The constants of R2. -/
def kR2 : BlkK := ⟨4000, 3, 1, 1, 771, 65, 52⟩

theorem tstK_eq (d : ℕ) : tstK d = 10 * d * d + 62 * d + 83 := by unfold tstK cmK; ring
theorem r2xUnits_eq (d : ℕ) : r2xUnits d = 20 * d * d + 41 * d + 19 := by unfold r2xUnits; ring
theorem r2pUnits_eq (d : ℕ) : r2pUnits d = 17 * d + 24 := by unfold r2pUnits; ring

theorem r2K_le {E j x : ℕ} (hd : d ≤ x) (hE : E + 2 ≤ x) (hj : j ≤ 3 * E + 5) :
    (r2xUnits d + (200 * (E + 1) + ((20 * E + 40) + ((13 * d + 10) + 5)))) +
      (gaugeK d j (tstK d) + (1 + (1 + r2pUnits d))) ≤ 4000 * x ^ 3 := by
  rw [r2xUnits_eq, tstK_eq, r2pUnits_eq]
  unfold gaugeK
  have hj1 : j + 1 ≤ 3 * x := by omega
  have hx1 : 1 ≤ x := by omega
  have h1 : d * d ≤ x * x := Nat.mul_le_mul hd hd
  have h2 : (j + 1) * (d * d) ≤ (3 * x) * (x * x) := Nat.mul_le_mul hj1 h1
  have h3 : (j + 1) * d ≤ (3 * x) * x := Nat.mul_le_mul hj1 hd
  have h4 : x ≤ x * x := Nat.le_mul_of_pos_left x hx1
  have h5 : x * x ≤ x * x * x := Nat.le_mul_of_pos_right _ hx1
  have h6 : x ^ 3 = x * x * x := by ring
  rw [h6]
  nlinarith

/-! ## Helpers -/

theorem abs_lt_two_pow_len (z : ℤ) : |z| < 2 ^ len z := by
  rw [Int.abs_eq_natAbs]
  unfold len
  exact_mod_cast Nat.lt_size_self z.natAbs

theorem hnG_pos (z : ℤ) : 0 < hnG z := by unfold hnG; split_ifs with h <;> omega

theorem hnG_le {z : ℤ} {B : ℕ} (hz : z ≤ 2 ^ B) : hnG z ≤ 2 ^ B := by
  unfold hnG; split_ifs with h
  · exact hz
  · exact one_le_pow₀ (by norm_num)

theorem cmcK_le {p G : ℕ} {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (hNG : N ≤ 2 ^ G) : cmcK p N D ≤ p + G + 4 := by
  obtain ⟨h0, h1⟩ := ceil_quot_le hN hD
  have : (0 - (0 - N) / D).toNat ≤ 2 ^ G := by
    have : ((0 - (0 - N) / D).toNat : ℤ) ≤ 2 ^ G := by rw [Int.toNat_of_nonneg h0]; exact h1.trans hNG
    exact_mod_cast this
  have := Nat.clog_le_of_le_pow this
  unfold cmcK; omega

theorem pow_lt_pow_E {a b : ℕ} (h : a < b) : (2 : ℤ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) h
theorem pow_le_pow_E {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

/-- A cell outside a frame of R2. -/
macro "fdec" : tactic => `(tactic| ((try simp only [SPre, NPre, APre, gaugeS, gaugeN, gaugeAr, SP, NP, AP]) <;> decide))

end AdversarialBco.Unified.ProgO
