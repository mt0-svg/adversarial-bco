/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriMag

@[expose] public section

/-!
# The bound of `stK`

`stK d r₀ R₀ = stEEta + stEH + 2 + clog₂ ⌈6 · 2^{L_a} R₀ / r₀²⌉`, the exponent of the gauge's tolerance in the stage
test. Its bound by the bit lengths of `R₀` and `r₀` (`stK_le_len`) and by the work term `W` (`stK_le`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (len)

/-- `6 · 2^{L_a} R₀ / r₀² ≤ 2^{L_a + 3 + len R₀.num + 2 len r₀.den}`. -/
theorem stKArg_le {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (d : ℕ) :
    6 * (triRaQ d : ℚ) * R0 / r0 ^ 2 ≤ 2 ^ (triLa (triSQ d) + 3 + len R0.num + 2 * len (r0.den : ℤ)) := by
  have hR : 0 < R0 := lt_of_lt_of_le h0 h1
  have hRn : (0 : ℚ) < R0.num := by exact_mod_cast Rat.num_pos.2 hR
  have hrn1 : (1 : ℚ) ≤ r0.num := by exact_mod_cast Rat.num_pos.2 h0
  have e1 : (R0.num : ℚ) = R0 * R0.den := (Rat.mul_den_eq_num R0).symm
  have e2 : (r0.num : ℚ) = r0 * r0.den := (Rat.mul_den_eq_num r0).symm
  have hRd : (1 : ℚ) ≤ R0.den := by exact_mod_cast R0.den_pos
  have hrd : (0 : ℚ) < r0.den := by exact_mod_cast r0.den_pos
  have h3 : R0 ≤ (R0.num : ℚ) := by rw [e1]; nlinarith
  have h4 : 1 ≤ (r0 * r0.den) ^ 2 := by rw [← e2]; nlinarith
  have hq : R0 / r0 ^ 2 ≤ (R0.num : ℚ) * (r0.den : ℚ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have e3 : (R0.num : ℚ) * r0.den ^ 2 * r0 ^ 2 = R0.num * (r0 * r0.den) ^ 2 := by ring
    rw [e3]; nlinarith
  have a1 : (R0.num : ℚ) ≤ 2 ^ len R0.num := by
    have h := Nat.lt_size_self R0.num.natAbs
    have hc : ((R0.num.natAbs : ℕ) : ℚ) = R0.num := by rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hRn]
    rw [← hc]; exact_mod_cast h.le
  have a2 : (r0.den : ℚ) ≤ 2 ^ len (r0.den : ℤ) := by
    rw [len_natCast]; exact_mod_cast (Nat.lt_size_self r0.den).le
  have hRa : (triRaQ d : ℚ) = 2 ^ triLa (triSQ d) := by unfold triRaQ; push_cast; rfl
  have hP : (0 : ℚ) < 2 ^ triLa (triSQ d) := by positivity
  have b1 : R0 / r0 ^ 2 ≤ 2 ^ len R0.num * (2 ^ len (r0.den : ℤ)) ^ 2 :=
    hq.trans (mul_le_mul a1 (pow_le_pow_left₀ hrd.le a2 2) (by positivity) (by positivity))
  have hpos : 0 ≤ R0 / r0 ^ 2 := by positivity
  calc 6 * (triRaQ d : ℚ) * R0 / r0 ^ 2 = 6 * 2 ^ triLa (triSQ d) * (R0 / r0 ^ 2) := by rw [hRa]; ring
    _ ≤ 8 * 2 ^ triLa (triSQ d) * (2 ^ len R0.num * (2 ^ len (r0.den : ℤ)) ^ 2) := by
        have := mul_le_mul_of_nonneg_left b1 hP.le; nlinarith
    _ = 2 ^ (triLa (triSQ d) + 3 + len R0.num + 2 * len (r0.den : ℤ)) := by ring

/-- `stK` by the bit lengths of `R₀` and `r₀`. -/
theorem stK_le_len {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) (d : ℕ) :
    stK d r0 R0 ≤ stEEta d + stEH d + 5 + triLa (triSQ d) + len R0.num + 2 * len (r0.den : ℤ) := by
  have := clog_ceil_le (stKArg_le h0 h1 d)
  unfold stK; omega

/-- **`stK ≤ 4096 (W + 1)²`** on the inputs of the statement. -/
theorem stK_le {d n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    stK d r0 R0 ≤ 4096 * (WT d n δ r0 R0 a + 1) ^ 2 := by
  have hd := hI.hd
  have hK := stK_le_len hI.hr0 hI.hR0 d
  have hS : len R0.num + len (r0.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  have hW : d + sizeN δ r0 R0 a ≤ WT d n δ r0 R0 a := by simp only [WT, wU]; omega
  have hLa := triLa_le_lin hd
  have hE1 := triE1Q_le hd
  have hEt := triETauQ_le hd
  have hEH := stEH_le hd
  have hEta : stEEta d = triETauQ d + (triE1Q d + 1) + 11 + 3 * d * (triETauQ d + 4) := rfl
  have m1 : d * triETauQ d ≤ 367 * d + 51 * (d * d) := by nlinarith
  have q2 : 3 * d * (triETauQ d + 4) = 3 * (d * triETauQ d) + 12 * d := by ring
  have T : stK d r0 R0 ≤ 718 + 1209 * d + 153 * (d * d) + 2 * sizeN δ r0 R0 a := by
    rw [hEta, q2] at hK; omega
  refine T.trans ?_
  generalize sizeN δ r0 R0 a = S at hW ⊢
  generalize WT d n δ r0 R0 a = W at hW ⊢
  nlinarith

end AdversarialBco.Unified.ProgO.TriO
