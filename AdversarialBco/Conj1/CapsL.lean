/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2Caps

@[expose] public section

/-!
# The caps of AP with `n` only inside the logarithm

`df2Cap_le` and `df2Caps_bound` of MachDf2Caps.lean with `Λ = 2 d L`, `L = log (2dn/δ)`, in place of `Λ = 2 d n L`:
`kAPcap_poly` reads `Λ` only through `1 ≤ Λ`, `d ≤ Λ` and `L ≤ Λ`, which hold with `n` left out; the rest of the proof
is that of `df2Cap_le`.
-/
namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.Poly

theorem df2Cap_leL (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (df2Cap1 d n δ : ℝ) ≤ 2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * Real.log (2 * d * n / δ))) ^ 3)) ^ 5 ∧
    (df2Cap2 d n δ : ℝ) ≤ 2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * Real.log (2 * d * n / δ))) ^ 3)) ^ 5 := by
  unfold df2Cap1 df2Cap2 apCap1 apCap2
  obtain ⟨hdnX, hdX, hnX, hX⟩ := df2_X_bounds d n hd hn δ hδ hδ1
  obtain ⟨hR0, hR⟩ := df2oPar_R_bound d n hd δ
  have hR1 := df2oPar_R_ge_one d n hd δ
  obtain ⟨he0, -, he⟩ := df2oPar_δe_bounds d n hd hn δ hδ hδ1
  obtain ⟨hs0, -, hs⟩ := df2oPar_sb_bounds d n hd hn δ hδ hδ1
  obtain ⟨heta0, heta⟩ := df2oPar_eta_le d n hd hn δ hδ
  have hLe0 : 0 ≤ (df2oPar d n δ).Le := by linarith [df2oPar_Le_ge d n hd hn δ hδ]
  have hLe := df2oPar_Le_le d n hd hn δ hδ hδ1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdX' : (d : ℝ) ≤ 2 * d * n / δ := by linarith
  have hR' : (df2oPar d n δ).R ≤ 268 * (2 * d * n / δ) ^ 2 := by
    have : (d : ℝ) ^ 2 ≤ (2 * d * n / δ) ^ 2 := pow_le_pow_left₀ (by positivity) hdX' 2
    linarith
  have cR := capin_R hX hR'
  have cRb := capin_rb hX hR1 hR' he0 he hs0 hs
  have cT := capin_T hX hdX he0 he
  have cW1 := capin_W1 hX hR1 hR' he0 he
  have cW2 := capin_W2 hX hd1 hn1 hdX hdnX hR' he0 he heta hLe0 hLe
  have ce2 := capin_e2 hX hd1 hn1 hdX hnX hR1 hR' he0 he
  have hL := df2_log_ge d n hd hn δ hδ hδ1
  have hL0 : 0 ≤ Real.log (2 * d * n / δ) := by linarith
  have hdn1 : (1 : ℝ) ≤ d * n := one_le_mul_of_one_le_of_one_le hd1 hn1
  have hΛ1 : 1 ≤ 2 * ((d : ℝ) * Real.log (2 * d * n / δ)) := by nlinarith
  have hdΛ : (d : ℝ) ≤ 2 * ((d : ℝ) * Real.log (2 * d * n / δ)) := by nlinarith
  have hLΛ : Real.log (2 * d * n / δ) ≤ 2 * ((d : ℝ) * Real.log (2 * d * n / δ)) := by nlinarith
  have hT0 : 0 < (d : ℝ) / (df2oPar d n δ).δe := div_pos (by linarith) he0
  have hrb : 0 < (df2oPar d n δ).sb / 2 := by linarith
  constructor
  · refine kAPcap_poly hd (kMemR_le d) hX (by norm_num) hdX' hΛ1 hdΛ hLΛ hrb hR0 hT0 (by positivity) one_pos
      cR cRb cT cW1 ?_
    rw [div_one]; linarith
  · have hW : 0 ≤ (df2oPar d n δ).R + (df2oPar d n δ).eta *
        Real.sqrt (16 * d * n * (df2oPar d n δ).Le / (df2oPar d n δ).δe) := by positivity
    have heb : 0 < 1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * (df2oPar d n δ).R ^ 2 * ((d : ℝ) / (df2oPar d n δ).δe))) :=
      one_div_pos.2 (mul_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _)))
    exact kAPcap_poly hd (kMemR_le d) hX (by norm_num) hdX' hΛ1 hdΛ hLΛ hrb hR0 hT0 hW heb cR cRb cT cW2 ce2

/-- The caps of the two calls of AP in DF2-O are polynomial in `d log(2dn/δ)`. -/
theorem df2Caps_boundL : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ((df2Cap1 d n δ + df2Cap2 d n δ : ℕ) : ℝ) ≤ C * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k := by
  refine ⟨2 * 2536 * (2 * (8 * capA (10 ^ 18) 14 + 300)) ^ 5 * 2 ^ 15, 15, fun d n hd hn δ hδ hδ1 => ?_⟩
  obtain ⟨h1, h2⟩ := df2Cap_leL d n hd hn δ hδ hδ1
  push_cast
  calc _ ≤ 2 * (2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * Real.log (2 * d * n / δ))) ^ 3)) ^ 5) := by linarith
    _ = _ := by ring


end AdversarialBco.Poly.Mach.VL
