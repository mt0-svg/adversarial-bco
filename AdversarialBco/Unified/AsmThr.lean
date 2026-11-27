/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmMain
public import AdversarialBco.Unified.BLOParam

@[expose] public section

/-!
# The arithmetic of the assembly at BL-O's confidence (`ThrO`)

`thrO : ThrO`. With `δ_BL = dBL d n δ = 2^{-19-k_δ}/(d n)³` (`DeltaO`: `δ_BL ≤ 2^{-19} δ/(d n)³` and
`log(2dn/δ_BL) ≤ 22 log(2dn/δ)`):

* `0 < δ_BL ≤ 2^{-19} δ < 1`;
* `δ_ref = n (149/168) δe + δe/7 ≤ δ1 ≤ δ_BL/3` (`δe = 4 δ1/(5 n)`), so `δ_ref ≤ δ/2` (`deltaRef_le`);
* in the run case Lemma thr (`comp_thresh` with `rowHyp_of`) gives `B_n + 1 ≤ 10^22 d^{3/2} √n log(2dn/δ_BL)^5`,
  and `10^22 · 22^5 ≤ 10^29` (`thr_scale`);
* off it, `ε > 1/4` gives `n ≤ 10^22 d^{3/2} √n log(2dn/δ_BL)^5` (`n_le_thr_gen`, at any `δ ∈ (0, 1)`).
-/

namespace AdversarialBco.Unified.Asm

open AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl AdversarialBco.Unified.BLO

/-- `0 < δ_BL`. -/
theorem dBL_pos {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℚ) : 0 < dBL d n δ := by
  unfold dBL deltaO
  have h1 : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- `δ_ref ≤ δ1 ≤ δ'/3`. -/
theorem deltaRef_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {δ' : ℝ} (hδ' : 0 < δ') : deltaRef d n δ' ≤ δ' / 3 := by
  unfold deltaRef
  have h1 : (df2oPar d n δ').δ1 ≤ δ' / 3 := par_δ1_le d n δ'
  have h0 : 0 < (df2oPar d n δ').δ1 := par_δ1_pos d n δ' hd hn hδ'
  have he : (df2oPar d n δ').δe = 4 * (df2oPar d n δ').δ1 / (5 * n) := rfl
  rw [he]
  set x := (df2oPar d n δ').δ1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have e1 : (n : ℝ) * (149 / 168 * (4 * x / (5 * n))) = 149 / 210 * x := by field_simp; ring
  have e2 : 4 * x / (5 * n) / 7 ≤ 4 * x / 35 := by
    rw [div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
  linarith

/-- The scale of the threshold: `10^22 d^{3/2} √n Λ'^5 ≤ thrU d n δ` for `0 ≤ Λ' ≤ 22 log(2dn/δ)`. -/
theorem thr_scale {d n : ℕ} {δ : ℚ} {Λ' : ℝ} (h0 : 0 ≤ Λ') (h : Λ' ≤ 22 * Real.log (2 * d * n / (δ : ℝ))) :
    10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Λ' ^ 5 ≤ thrU d n δ := by
  unfold thrU
  set L := Real.log (2 * d * n / (δ : ℝ))
  have hA : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by positivity
  have hL : 0 ≤ L := by linarith
  have hp : Λ' ^ 5 ≤ 22 ^ 5 * L ^ 5 := by
    calc Λ' ^ 5 ≤ (22 * L) ^ 5 := pow_le_pow_left₀ h0 h 5
      _ = 22 ^ 5 * L ^ 5 := by ring
  have hL5 : 0 ≤ L ^ 5 := pow_nonneg hL 5
  calc 10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Λ' ^ 5
      = 10 ^ 22 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n) * Λ' ^ 5 := by ring
    _ ≤ 10 ^ 22 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n) * (22 ^ 5 * L ^ 5) := by gcongr
    _ ≤ 10 ^ 29 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n) * L ^ 5 := by nlinarith [mul_nonneg hA hL5]
    _ = 10 ^ 29 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 := by ring

/-- Off the run case, at any `δ' ∈ (0, 1)`: `n ≤ 10^22 d^{3/2} √n log(2dn/δ')^5`. -/
theorem n_le_thr_gen {d n : ℕ} {δ' : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ') (hδ1 : δ' < 1)
    (h : 1 / 4 < (df2oPar d n δ').eps) :
    (n : ℝ) ≤ 10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ') ^ 5 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨-, hle⟩ := log_inv_de_le d n δ' hd1 hn1 hδ0 hδ1
  set L := (df2oPar d n δ').Le with hL
  have hLdef : L = 36 * Real.log (1 / (4 * min (δ' / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) / (5 * n))) := by
    rw [hL]; simp only [df2oPar, df2C0]
  have hpos := (log_inv_de_le d n δ' hd1 hn1 hδ0 hδ1).1
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hLΛ : L ≤ 900 * Real.log (2 * d * n / δ') := by rw [hLdef]; linarith
  have heps : (df2oPar d n δ').eps = 20 * 725 * (d * Real.sqrt d) * L ^ 5 / Real.sqrt n := by
    rw [hL]; simp only [df2oPar, df2oClam]
  rw [heps] at h
  exact Bit.Asm.quarter_bound df2Trivial_holds d n L _ hd1 hn1 hL0 hLΛ h

/-- **The arithmetic of the assembly at BL-O's confidence.** -/
theorem thrO : ThrO := by
  intro d n δ hd hn hδ0 hδ1
  obtain ⟨-, -, hle3, -, hlog, -⟩ := deltaO_holds d n δ hd hn hδ0 hδ1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hpos : 0 < dBL d n δ := dBL_pos hd hn δ
  have hdn3 : (1 : ℝ) ≤ ((d : ℝ) * n) ^ 3 := one_le_pow₀ (by nlinarith)
  have hle : dBL d n δ ≤ (2 : ℝ)⁻¹ ^ 19 * δ :=
    le_trans hle3 (div_le_self (by positivity) hdn3)
  have h19 : (2 : ℝ)⁻¹ ^ 19 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hleδ : dBL d n δ ≤ δ := le_trans hle (by nlinarith)
  have hlt : dBL d n δ < 1 := lt_of_le_of_lt hleδ hδ1'
  have hΛ0 : 0 ≤ Real.log (2 * d * n / dBL d n δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hpos]
    nlinarith
  have hΛ : Real.log (2 * d * n / dBL d n δ) ≤ 22 * Real.log (2 * d * n / (δ : ℝ)) := hlog
  refine ⟨hpos, hlt, ?_, fun hc => ?_, fun hc => ?_⟩
  · have := deltaRef_le hd hn hpos
    linarith
  · have hrow := rowHyp_of d n (dBL d n δ) hd hn hpos hlt (hc.trans (by norm_num))
    have hct := comp_thresh (df2oPar d n (dBL d n δ)) d n (dBL d n δ) hrow hpos hlt rfl rfl
    exact le_trans hct (thr_scale hΛ0 hΛ)
  · exact le_trans (n_le_thr_gen hd hn hpos hlt (not_le.mp hc)) (thr_scale hΛ0 hΛ)

end AdversarialBco.Unified.Asm
