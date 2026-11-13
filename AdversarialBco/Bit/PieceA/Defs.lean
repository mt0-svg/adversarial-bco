/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# Piece A of the cut of `RunOK`: the reference constants written out

Piece A is `BudA` of Bit/BLRun.lean: the enclosure lemma and the precision theorem at every `(d, n)` of `RunCase`.
This file writes the reference constants of `Bud` (read off `po d n = df2oPar d n (deltaBL d n)`) as explicit
functions of `(d, n)`: `N = 15 · 2^17 d^3 n^4`, `Le = 36 ln N`, `ε = 14500 d^{3/2} Le^5/n^{1/2}`, ..., and proves
that they are the constants of `Bud`
(`Bud.Le d n = Le d n`, ...). At BL's confidence `δ = 2^{-19}/(dn)^3`, `δ/3 < e^{-14}/(dn)^3`, so `δ₁ = δ/3` and
`δe = 1/N` (`po_de`).
-/

namespace AdversarialBco.Bit.PieceA

open AdversarialBco.Bit.BLP (po par)
open AdversarialBco.Bit.Asm (RunCase deltaBL)

/-- `N = 15 · 2^17 d^3 n^4` as a natural number. -/
def NeN (d n : ℕ) : ℕ := 15 * 2 ^ 17 * d ^ 3 * n ^ 4

/-- `N` as a real number. -/
noncomputable def Ne (d n : ℕ) : ℝ := (NeN d n : ℝ)

/-- `Le = 36 ln N`. -/
noncomputable def Le (d n : ℕ) : ℝ := 36 * Real.log (Ne d n)

/-- `ε = 14500 d^{3/2} Le^5 / n^{1/2}`. -/
noncomputable def eps (d n : ℕ) : ℝ := 14500 * d * Real.sqrt d * Le d n ^ 5 / Real.sqrt n

/-- `λ = 1/(725 d Le²)`. -/
noncomputable def lam (d n : ℕ) : ℝ := 1 / (725 * d * Le d n ^ 2)

/-- `η = d^{1/2}/(Le n^{1/2})`. -/
noncomputable def eta (d n : ℕ) : ℝ := Real.sqrt d / (Le d n * Real.sqrt n)

/-- `ρ = 1450 d² Le³`. -/
noncomputable def rho (d n : ℕ) : ℝ := 1450 * d ^ 2 * Le d n ^ 3

/-- `R = 134 d (ln(2d + 2))^{1/2}`. -/
noncomputable def R (d : ℕ) : ℝ := 134 * d * Real.sqrt (Real.log (2 * d + 2))

/-- `κ_c = η λ/(4 (1 - λ)²)`. -/
noncomputable def kc (d n : ℕ) : ℝ := eta d n * lam d n / (4 * (1 - lam d n) ^ 2)

/-- `Lgb = ln 14 + 5 Le/144`. -/
noncomputable def Lgb (d n : ℕ) : ℝ := Real.log 14 + 5 * Le d n / 144

/-- `ℓe = size N`, the binary length of `N`. -/
def le (d n : ℕ) : ℕ := (NeN d n).size

/-- `ℓd = size d`. -/
def ld (d : ℕ) : ℕ := d.size

/-- The precision `p = 10 ℓe + 16 ℓd + 160`. -/
def pB (d n : ℕ) : ℕ := 10 * le d n + 16 * ld d + 160

/-- `u = 2^{-p}`. -/
noncomputable def u (d n : ℕ) : ℝ := 1 / 2 ^ pB d n

/-- The slack `ê = 2^{-(p - 3ℓe - 6ℓd - 64)}`. -/
noncomputable def eh (d n : ℕ) : ℝ := 1 / 2 ^ (pB d n - 3 * le d n - 6 * ld d - 64)

/-! ## The constants of `Bud` -/

theorem bud_tp (d n : ℕ) : BLP.Bud.tp d n = u d n := rfl

theorem bud_eh (d n : ℕ) : BLP.Bud.eh d n = eh d n := by
  simp only [BLP.Bud.eh, eh, par, pB, le, ld, NeN, BLP.Ne]
  push_cast
  rfl

theorem exp14_le : Real.exp 14 ≤ 3 * 2 ^ 19 := by
  have h1 := Real.exp_one_lt_d9
  have h : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 := by
        gcongr
    _ ≤ 3 * 2 ^ 19 := by norm_num

/-- `δ/3 ≤ e^{-14}/(dn)^3` at BL's `δ = 2^{-19}/(dn)^3`. -/
theorem deltaBL_third_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    deltaBL d n / 3 ≤ Real.exp (-14) / ((d : ℝ) * n) ^ 3 := by
  have hdn : 0 < ((d : ℝ) * n) ^ 3 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h : (2⁻¹ : ℝ) ^ 19 / 3 ≤ Real.exp (-14) := by
    rw [Real.exp_neg]
    have := inv_anti₀ (by positivity) exp14_le
    calc (2⁻¹ : ℝ) ^ 19 / 3 = (3 * 2 ^ 19 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := this
  calc deltaBL d n / 3 = ((2⁻¹ : ℝ) ^ 19 / 3) / ((d : ℝ) * n) ^ 3 := by unfold deltaBL; ring
    _ ≤ _ := div_le_div_of_nonneg_right h hdn.le

theorem po_de (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : (po d n).δe = 1 / Ne d n := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [po, AdversarialBco.Poly.df2oPar]
  rw [min_eq_left (deltaBL_third_le d n hd hn)]
  simp only [deltaBL, Ne, NeN]
  push_cast
  field_simp
  ring

theorem bud_Le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.Le d n = Le d n := by
  have h : (po d n).Le = AdversarialBco.Poly.df2C0 * Real.log (1 / (po d n).δe) := rfl
  rw [BLP.Bud.Le, h, po_de d n hd hn, one_div_one_div, Le, AdversarialBco.Poly.df2C0]

theorem bud_lam (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.lam d n = lam d n := by
  have h : (po d n).lam = 1 / (AdversarialBco.Poly.df2oClam * d * (po d n).Le ^ 2) := rfl
  rw [BLP.Bud.lam, h, ← BLP.Bud.Le, bud_Le d n hd hn, lam, AdversarialBco.Poly.df2oClam]

theorem bud_eta (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.eta d n = eta d n := by
  have h : (po d n).eta = Real.sqrt d / ((po d n).Le * Real.sqrt n) := rfl
  rw [BLP.Bud.eta, h, ← BLP.Bud.Le, bud_Le d n hd hn, eta]

theorem bud_eps (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.eps d n = eps d n := by
  have h : (po d n).eps = 20 * AdversarialBco.Poly.df2oClam * (d * Real.sqrt d) * (po d n).Le ^ 5 / Real.sqrt n := rfl
  rw [BLP.Bud.eps, h, ← BLP.Bud.Le, bud_Le d n hd hn, eps, AdversarialBco.Poly.df2oClam]
  ring

theorem bud_rho (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.rho d n = rho d n := by
  have h : (po d n).rho = 2 * AdversarialBco.Poly.df2oClam * d ^ 2 * (po d n).Le ^ 3 := rfl
  rw [BLP.Bud.rho, h, ← BLP.Bud.Le, bud_Le d n hd hn, rho, AdversarialBco.Poly.df2oClam]
  ring

theorem bud_kc (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.kc d n = kc d n := by
  have hk : (po d n).kap = 1 / 4 := rfl
  have hk0 : (po d n).k0 = ((1 - (po d n).lam) ^ 2)⁻¹ := rfl
  rw [BLP.Bud.kc, hk, hk0, ← BLP.Bud.eta, ← BLP.Bud.lam, bud_eta d n hd hn, bud_lam d n hd hn, kc,
    div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem bud_Lgb (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : BLP.Bud.Lgb d n = Lgb d n := by
  rw [BLP.Bud.Lgb, bud_Le d n hd hn, Lgb]

/-- In `RunCase`, `ε ≤ 1/4`. -/
theorem eps_le_of_runCase (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCase d n) : eps d n ≤ 1 / 4 := by
  rw [← bud_eps d n hd hn]
  exact h

end AdversarialBco.Bit.PieceA
