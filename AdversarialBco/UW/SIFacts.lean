/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetPar
public import AdversarialBco.Poly.Df2SIFactsProof

@[expose] public section

/-!
# Proposition sifacts at T4U

`sifactsUW : SIFactsUW`. The proof of the facts of SI (Poly/Df2SIFactsProof.lean) reads the parameter record only
through `SIF.ParOK p d n`; `parOK_parW` gives it at `parW d n u` for `d, n ≥ 1`, `u ≥ 1`, from the floor
`δ_0 = 1/N_0`, `N_0 = 15 · 2^17 d³ n⁴`: `δ_0 ≤ 1/n`, `128 δ_0 ≤ 1`, `L = 36 log N_0 ≥ 36 · 14 = 504`
(`e^14 ≤ 3 · 2^19 ≤ N_0`), `log(2d + 2) ≤ log N_0`, and `1/ε ≤ √n ≤ n` since `ε √n = 14500 d^{3/2} L⁵ √u ≥ 1`.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Unified.BLO

variable {d : ℕ}

/-- `N_0 = 15 · 2^17 d³ n⁴` as a real number. -/
theorem n0W_cast (d n : ℕ) : (n0W d n : ℝ) = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
  simp only [n0W, NeO, add_zero]
  push_cast
  ring

/-- `e^14 ≤ 15 · 2^17`. -/
theorem exp14_le : Real.exp 14 ≤ 15 * 2 ^ 17 := by
  have h := Real.exp_one_lt_d9
  have h14 : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h14]
  calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 := by gcongr
    _ ≤ 15 * 2 ^ 17 := by norm_num

/-- `N_0 ≥ 15 · 2^17`, and the bounds of the floor that the facts of SI read. -/
theorem n0W_bounds {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (15 * 2 ^ 17 : ℝ) ≤ n0W d n ∧ (n : ℝ) ≤ n0W d n ∧ 2 * (d : ℝ) + 2 ≤ n0W d n ∧ Real.exp 14 ≤ n0W d n := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := le_self_pow₀ hd1 (by norm_num)
  have hn4 : (n : ℝ) ≤ (n : ℝ) ^ 4 := le_self_pow₀ hn1 (by norm_num)
  have h1d3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  have h1n4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have hdn : (d : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by nlinarith
  have hnd : (n : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by nlinarith
  have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le h1d3 h1n4
  have he := exp14_le
  rw [n0W_cast, mul_assoc]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **The facts of `parW d n u` that the proof of the facts of SI reads.** -/
theorem parOK_parW {n : ℕ} {u : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hu : 1 ≤ u) : SIF.ParOK (parW d n u) d n := by
  obtain ⟨hN, hnN, hdN, heN⟩ := n0W_bounds hd hn
  set N : ℝ := (n0W d n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hde : (parW d n u).δe = 1 / N := rfl
  have hLeN : (parW d n u).Le = 36 * Real.log N := by
    show df2C0 * Real.log (1 / (1 / N)) = _
    rw [df2C0, one_div_one_div]
  have hlog14 : 14 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]; exact heN
  have hLe : 504 ≤ (parW d n u).Le := by rw [hLeN]; linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd1
  have hsu : 1 ≤ Real.sqrt u := by rw [Real.one_le_sqrt]; exact hu
  have heps : (parW d n u).eps =
      20 * df2oClam * (d * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u / Real.sqrt n := rfl
  have hepsn : 1 / Real.sqrt n ≤ (parW d n u).eps := by
    rw [heps, df2oClam]
    have hL5 : 1 ≤ (parW d n u).Le ^ 5 := one_le_pow₀ (by linarith)
    have hdd : 1 ≤ (d : ℝ) * Real.sqrt d := one_le_mul_of_one_le_of_one_le hd1 hsd
    have hnum : 1 ≤ 20 * 725 * ((d : ℝ) * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u := by
      have h0 : 1 ≤ ((d : ℝ) * Real.sqrt d) * (parW d n u).Le ^ 5 := one_le_mul_of_one_le_of_one_le hdd hL5
      have h2 : 1 ≤ ((d : ℝ) * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u :=
        one_le_mul_of_one_le_of_one_le h0 hsu
      nlinarith
    exact div_le_div_of_nonneg_right hnum hsn.le
  have heps0 : 0 < (parW d n u).eps := lt_of_lt_of_le (by positivity) hepsn
  refine ⟨?_, ?_, ?_, ?_, hLe, ?_, ?_, rfl, heps0, ?_, rfl, ?_⟩
  · rw [hde]; positivity
  · rw [hde, div_le_one hN0]; linarith
  · rw [hde, mul_one_div, div_le_one hN0]; exact hnN
  · rw [hde, mul_one_div, div_le_one hN0]; linarith
  · rw [hLeN, hde, one_div_one_div]
  · rfl
  · calc 1 / (parW d n u).eps ≤ 1 / (1 / Real.sqrt n) := one_div_le_one_div_of_le (by positivity) hepsn
      _ = Real.sqrt n := one_div_one_div _
      _ ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  · rw [hLeN, mul_div_cancel_left₀ _ (by norm_num : (36 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) hdN

/-- **Proposition sifacts at T4U.** -/
theorem sifactsUW : SIFactsUW := fun _ _ _ Kt g hd hn hu heps hbody hadm =>
  SIF.df2SIAt_holds _ Kt g hd hn (parOK_parW hd hn hu) heps hbody hadm

end AdversarialBco.UW
