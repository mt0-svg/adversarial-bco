/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriEval
public import AdversarialBco.Unified.ProgOTriStK

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the magnitudes of the core step

* SEP's vector is below `2^{b_v + 1 + E}` when the values are below `2^{b_v}` (`sepE_G_le`); the stage field `gvO` is
  below `2^{stJ + 1 + stE}` (`gvO_le`), its values being gauge counters below `2^{stJ}` (`stEv_le`).
* `stZ`, one bound `Z` of every exponent of the core step, of `d`, `W`, `B`, `j` and `stK` (`zok_of`), below
  `2^{171} (W + B + 1)^{21}` (`stZ_le`).
* The units of the core step below `2^{60} Z^5` (`stepK_le`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## SEP's vector -/

theorem sepE_G_le {evN : (Fin d → ℤ) → ℤ} {Y0 : Fin d → ℤ} {E e1 eτ eL eu bv : ℕ} {Y G : Fin d → ℤ}
    (h : sepE evN Y0 E e1 eτ eL eu = some (Y, G)) (hv : ∀ X, |evN X| ≤ 2 ^ bv) (i : Fin d) :
    |G i| ≤ 2 ^ (bv + 1 + E) := by
  unfold sepE sepZ at h
  cases hc : sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) d with
  | none => rw [hc] at h; simp at h
  | some st =>
    rw [hc] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have h1 : |evN (st.1 + st.2.2 i • eZ i) - evN (st.1 - st.2.2 i • eZ i)| ≤ 2 ^ (bv + 1) := by
      calc _ ≤ |evN (st.1 + st.2.2 i • eZ i)| + |evN (st.1 - st.2.2 i • eZ i)| := abs_sub _ _
        _ ≤ 2 ^ bv + 2 ^ bv := add_le_add (hv _) (hv _)
        _ = 2 ^ (bv + 1) := by ring
    have h2 : |(2 : ℤ) ^ E / st.2.2 i| ≤ 2 ^ E :=
      (Int.abs_ediv_le_abs _ _).trans (by rw [abs_of_pos (by positivity)])
    rw [abs_mul, pow_add]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

theorem stEv_le (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d)
    (X : Fin d → ℤ) : |stEv orc a r0 R0 j P X| ≤ 2 ^ stJ d := by
  unfold stEv
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast (gaugeIt_le _ _ _ _ _ (stJ d) le_rfl).2

theorem gvO_le (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d)
    (z : Fin d → ℤ) (i : Fin d) : |gvO orc a r0 R0 ℓ j P z i| ≤ 2 ^ (stJ d + 1 + stE d) := by
  unfold gvO sepGZ
  rcases h : sepE (stEv orc a r0 R0 j (posZ P)) (rndZ (stE d) (tKZ d ℓ) z) (stE d) (stE1 d) (triETauQ d) 0
    (stEu d) with _ | ⟨Y, G⟩
  · simp only [h, Pi.zero_apply, abs_zero]; positivity
  · simp only [h]; exact sepE_G_le h (stEv_le orc a r0 R0 j (posZ P)) i

/-! ## One bound of the exponents -/

/-- One bound of the exponents of the core step. -/
def stZ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (B : ℕ) : ℕ :=
  2 ^ 170 * (WT d n δ r0 R0 a + 1) ^ 21 + 4096 * (WT d n δ r0 R0 a + 1) ^ 2 + WT d n δ r0 R0 a + B + 1

/-- What `stZ` bounds. -/
structure ZOK (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (B Z : ℕ) : Prop where
  one : 1 ≤ Z
  dZ : d ≤ Z
  wZ : WT d n δ r0 R0 a ≤ Z
  bZ : B ≤ Z
  mst : triMstQ r0 R0 ≤ WT d n δ r0 R0 a
  kZ : stK d r0 R0 ≤ Z
  laZ : triLa (triSQ d) + tGT d (ellO d n δ r0 R0) ≤ Z
  pZ : 2 * tzP d ≤ Z
  eZ : stE d ≤ Z
  tauZ : triETauQ d ≤ Z
  jZ : stJ d ≤ Z
  uZ : stEu d + 1 ≤ Z
  bvZ : triBvQ d ≤ Z
  jaZ : triJaQ d ≤ Z
  kzZ : tKZ d (ellO d n δ r0 R0) ≤ Z
  hZ : stEH d ≤ stJ d
  e1E : stE1 d ≤ stE d
  dW : d ≤ WT d n δ r0 R0 a

theorem zok_of {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (B : ℕ) (hI : InU d n δ r0 R0) :
    ZOK d n δ r0 R0 a B (stZ d n δ r0 R0 a B) := by
  have hS := triExpS d n δ r0 R0 a hI
  have hK := stK_le a hI
  have hm := mst_le_wU a hI
  have hdW : d ≤ WT d n δ r0 R0 a := by simp only [WT, wU]; omega
  have hGc : tGT d (ellO d n δ r0 R0) ≤ tGcT d (ellO d n δ r0 R0) := by unfold tGcT; omega
  have hKZ : tKZ d (ellO d n δ r0 R0) = tGT d (ellO d n δ r0 R0) + 2 * tzP d := rfl
  have hH : stEH d ≤ stJ d := by unfold stJ; omega
  have hE1 : stE1 d ≤ stE d := by unfold stE; omega
  unfold stZ
  generalize 2 ^ 170 * (WT d n δ r0 R0 a + 1) ^ 21 = A at hS ⊢
  generalize 4096 * (WT d n δ r0 R0 a + 1) ^ 2 = A' at hK ⊢
  exact ⟨by omega, by omega, by omega, by omega, hm, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, hH, hE1, hdW⟩

theorem stZ_le (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (B : ℕ) :
    stZ d n δ r0 R0 a B ≤ 2 ^ 171 * (WT d n δ r0 R0 a + B + 1) ^ 21 := by
  unfold stZ
  generalize WT d n δ r0 R0 a = W
  have hV : 1 ≤ W + B + 1 := by omega
  have h1 : (W + 1) ^ 21 ≤ (W + B + 1) ^ 21 := Nat.pow_le_pow_left (by omega) 21
  have h2 : (W + 1) ^ 2 ≤ (W + B + 1) ^ 21 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right hV (by norm_num))
  have h3 : W + B + 1 ≤ (W + B + 1) ^ 21 := by
    calc W + B + 1 = (W + B + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + B + 1) ^ 21 := Nat.pow_le_pow_right hV (by norm_num)
  generalize (W + B + 1) ^ 21 = V at h1 h2 h3
  have : (2 : ℕ) ^ 171 = 2 ^ 170 + 2 ^ 170 := by norm_num
  rw [this]
  have h4 : 4096 ≤ 2 ^ 170 := by norm_num
  nlinarith

/-! ## The units -/

theorem tstTK_le {d Z : ℕ} (hd : d ≤ Z) (hZ : 1 ≤ Z) : tstTK d ≤ 200 * Z ^ 2 := by
  simp only [tstTK, cubeK, cubeBK, cmK, ieMapT, IE.units]
  nlinarith [Nat.mul_le_mul hd hd]

theorem zOK_le {d Z : ℕ} (hd : d ≤ Z) (hZ : 1 ≤ Z) : zOK d ≤ 100 * Z ^ 2 := by
  simp only [zOK]
  nlinarith [Nat.mul_le_mul hd hd]

/-- The units of the core step after the base point: SEP, the fill on failure, the update. -/
abbrev stepRK (d J Jt : ℕ) : ℕ :=
  sepK d (0 + J + 3) (gaugeK d Jt (tstTK d)) + ((1 + (d * (1 + 6) + 3)) + 2 +
    ((d * (11 + (4 + 2) + 3) + 3) + (d * (d * (44 + 3) + 3 + 3) + 3)))

theorem stepK_le {d J Jt Z : ℕ} (hZ : 1 ≤ Z) (hd : d ≤ Z) (hJ : J ≤ Z) (hJt : Jt ≤ Z) :
    zOK d + stepRK d J Jt ≤ 2 ^ 60 * Z ^ 5 := by
  have ht := tstTK_le hd hZ
  have hz := zOK_le hd hZ
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ (by norm_num)
  have hZ5 : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ (by norm_num)
  have hg : gaugeK d Jt (tstTK d) ≤ 1184 * Z ^ 3 := by
    unfold gaugeK
    calc 2 * (Jt + 1) * (tstTK d + 32 * d + 64) ≤ 2 * (2 * Z) * (200 * Z ^ 2 + 96 * Z ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by nlinarith)
      _ = 1184 * Z ^ 3 := by ring
  have hs : sepK d (0 + J + 3) (gaugeK d Jt (tstTK d)) ≤ 240640 * Z ^ 5 := by
    unfold sepK
    calc 16 * (d + 1) * (0 + J + 3 + 1) * (gaugeK d Jt (tstTK d) + 64 * d + 256) ≤
          16 * (2 * Z) * (5 * Z) * (1184 * Z ^ 3 + 320 * Z ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 (by omega)) (by omega)) (by nlinarith)
      _ = 240640 * Z ^ 5 := by ring
  have hr : (1 + (d * (1 + 6) + 3)) + 2 + ((d * (11 + (4 + 2) + 3) + 3) + (d * (d * (44 + 3) + 3 + 3) + 3)) ≤
      100 * Z ^ 2 := by nlinarith [Nat.mul_le_mul hd hd]
  simp only [stepRK]
  have h60 : (240640 : ℕ) + 200 ≤ 2 ^ 60 := by norm_num
  nlinarith

end AdversarialBco.Unified.ProgO.TriO
