/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGBound

@[expose] public section

/-!
# The step bound of PG with `n` only inside the logarithm

`kPG_bound` of MachPGBound.lean with the dominating variable `X = d L (2 + log (R₀/r₀))`, `L = log (2dn/δ)`, in place
of `X = d n L (2 + log (R₀/r₀))`: only `pgb_X` changes (`pgb_XL`); the body of `kPG_boundL` is that of `kPG_bound`
with `X` redefined. `n` enters the step count of PG only through `δ₁` (`pgb_delta1`), inside the logarithm.
-/
open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL

namespace AdversarialBco.Poly.PG

theorem pgb_XL {d n : ℕ} {δ r0 R0 : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h0 : 0 < δ) (h1 : δ < 1)
    (hr0 : 0 < r0) (hr : r0 ≤ R0) :
    let L := Real.log (2 * d * n / δ)
    let Λ := 2 + Real.log (R0 / r0)
    let X := (d : ℝ) * L * Λ
    1 ≤ X ∧ (d : ℝ) ≤ X ∧ 2 * Λ ≤ 3 * X ∧ L ≤ X / 2 ∧ 1 / 2 ≤ L ∧ 2 ≤ Λ := by
  intro L Λ X
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have h2 : (2 : ℝ) ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ h0]; nlinarith
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) h2
  have hl2 := Real.log_two_gt_d9
  have hy : 1 ≤ R0 / r0 := by rw [le_div_iff₀ hr0]; linarith
  have hΛ : 2 ≤ Λ := by have := Real.log_nonneg hy; show 2 ≤ 2 + Real.log (R0 / r0); linarith
  have hL23 : 2 / 3 ≤ L := by linarith
  have hLΛ : 4 / 3 ≤ L * Λ := by nlinarith
  have hX : X = (d : ℝ) * (L * Λ) := by show (d : ℝ) * L * Λ = _; ring
  have hXge : L * Λ ≤ X := by rw [hX]; nlinarith
  refine ⟨by linarith, ?_, ?_, ?_, by linarith, hΛ⟩
  · rw [hX]; nlinarith
  · nlinarith
  · nlinarith

/-- The step count of PG is polynomial in `d log (2dn/δ) (2 + log (R₀/r₀))`. -/
theorem kPG_boundL : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ → δ < 1 →
    (kPG d r0 R0 (df2oPar d n δ).δ1 : ℝ) ≤
      C * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k := by
  refine ⟨kPGpoly 1 1 1 1 1 (kStage 1 1 1 1 1 1 + 8) * (2 * 10 ^ 52) ^ 13, 28 * 13,
    fun d n hd hn r0 R0 δ hr0 hr hδ0 hδ1 => ?_⟩
  obtain ⟨hX1, hdX, hΛX, hLX, hL, hΛ⟩ := pgb_XL hd hn hδ0 hδ1 hr0 hr
  set L := Real.log (2 * d * n / δ) with hLdef
  set Λ := 2 + Real.log (R0 / r0) with hΛdef
  set X := (d : ℝ) * L * Λ with hXdef
  set δ₁ := (df2oPar d n δ).δ1 with hδ₁
  obtain ⟨hd0, hd1, hdlog⟩ := pgb_delta1 hd hn hδ0 hδ1
  rw [← df2oPar_δ1, ← hδ₁] at hd0 hd1 hdlog
  set m := pgStages r0 R0 with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmX : (m : ℝ) ≤ 3 * X := (pgb_stages_le hr0 hr).trans hΛX
  obtain ⟨-, hJ⟩ := pgb_Jr_le hd0 hd1 hm1
  have hMT := pgb_MT_le hd0 hd1 hm1
  have hJX : (pgJr (δ₁ / m) : ℝ) ≤ 45 * X := by nlinarith
  have hMTX : (pgMT (δ₁ / m) : ℝ) ≤ 529 * X := by nlinarith
  set Y := (10 : ℝ) ^ 52 * X ^ 28 with hY
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ X ^ 28 := one_le_pow₀ hX1
    nlinarith
  have toY : ∀ (v : ℕ) (c : ℝ) (j : ℕ), 0 ≤ c → c ≤ 10 ^ 52 → j ≤ 28 → (v : ℝ) ≤ c * X ^ j → v ≤ ⌈Y⌉₊ :=
    fun v c j hc0 hc hj h => Nat.cast_le.1 ((h.trans (pgb_pow_le hX1 hc0 hc hj)).trans (Nat.le_ceil Y))
  have hy : 1 ≤ ⌈Y⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hdy : d ≤ ⌈Y⌉₊ := toY d 1 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hdX)
  have hmy : m ≤ ⌈Y⌉₊ := toY m 3 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hmX)
  have hm0y : ⌈Real.logb 2 (R0 / r0)⌉₊ ≤ ⌈Y⌉₊ := (le_max_right _ _).trans hmy
  have hJy : pgJr (δ₁ / m) ≤ ⌈Y⌉₊ := toY _ 45 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hJX)
  have hMTy : pgMT (δ₁ / m) ≤ ⌈Y⌉₊ := toY _ 529 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hMTX)
  have hst : ∀ i < m, pgJb d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧ pgNs d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧
      pgNT d (pgRhoStage d i) ≤ ⌈Y⌉₊ := by
    intro i _
    obtain ⟨hρ1, hρ2⟩ := pgb_rho_le hd i
    have hdX' : ∀ j : ℕ, (d : ℝ) ^ j ≤ X ^ j := fun j => pow_le_pow_left₀ (by positivity) hdX j
    refine ⟨toY _ (2 ^ 20) 2 (by norm_num) (by norm_num) (by norm_num) ?_,
      toY _ (1.8e11 * 26244 ^ 9) 28 (by norm_num) (by norm_num) (by norm_num) ?_,
      toY _ (3.7e6 * 26244 ^ 3) 11 (by norm_num) (by norm_num) (by norm_num) ?_⟩
    · exact (pgb_Jb_le pgBisectSteps hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 2) (by norm_num))
    · exact (pgb_Ns_le pgNSize hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 28) (by norm_num))
    · exact (pgb_NT_le pgNTSize hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 11) (by norm_num))
  have hk := kPGpoly_le hy hdy hm0y hJy hMTy hmy (kPGStage_le hy hdy hJy hMTy hst)
  rw [kPG_eq]
  have hceil : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y)
    linarith
  calc (kPGpoly d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / m)) (pgMT (δ₁ / m)) m (kPGStage d r0 R0 δ₁) : ℝ)
      ≤ (kPGpoly 1 1 1 1 1 (kStage 1 1 1 1 1 1 + 8) : ℝ) * (⌈Y⌉₊ : ℝ) ^ 13 := by exact_mod_cast hk
    _ ≤ (kPGpoly 1 1 1 1 1 (kStage 1 1 1 1 1 1 + 8) : ℝ) * (2 * Y) ^ 13 := by gcongr
    _ = _ := by rw [hY, ← mul_assoc, mul_pow, ← pow_mul, mul_assoc]

end AdversarialBco.Poly.PG
