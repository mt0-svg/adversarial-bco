/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.BudInst
public import AdversarialBco.UW.BudMajO
public import AdversarialBco.Unified.BudA

@[expose] public section

/-!
# Theorem BUD-W

At every `(d, n, k)` and every reference `ρ` in its regime (`RegimeW d n ρ`), the
conditions of Theorem BUD hold at BL-OW's constants `regW d n k ρ` (UW/BudInst.lean), with the terms of Lemma
errors-W: (P1) to (P5), the slack, SEL, VAL, the guards of E18w, DOM-W (`c̄_w (1 + Ξ_{w1}²) ≤ 10^{-33}`), the coins
and the budgets in `δ` at `2^k ≤ N_e`. `BudOKW` has the fields of Theorem U's `BudOK` (Unified/BudDefs.lean) read off
`regW d n k ρ`, except Lemma ENC, which reads PARAM-W (UW/BudEncOK.lean), and the level of event (a) (group A).
-/

namespace AdversarialBco.UW.BudW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.UW

/-- Theorem BUD-W at `(d, n, k, ρ)`: the fields of `BudOK` on `regW d n k ρ`. -/
structure BudOKW (d n k : ℕ) (ρ : RefW) : Prop where
  Le_ge : 17467 ≤ (regW d n k ρ).Le
  Lf_ge : 17467 ≤ (regW d n k ρ).Lf
  /-- DOM-W: `c̄_w (1 + Ξ_{w1}²) ≤ 10^{-33}`. -/
  cb_le : (regW d n k ρ).cbw * (1 + (regW d n k ρ).Xw1 ^ 2) ≤ 1 / 10 ^ 33
  x_le : (regW d n k ρ).x ≤ 1
  V_le : (regW d n k ρ).V ≤ 1
  hb_le : (regW d n k ρ).hb ≤ 1 / 100
  hTr_le : ∀ j ≤ n, (regW d n k ρ).hTr j ≤ (regW d n k ρ).hb
  sel_le : (regW d n k ρ).sel ≤ (regW d n k ρ).selR
  h_le : (regW d n k ρ).h ≤ (regW d n k ρ).rmin / 4
  val_le : (regW d n k ρ).val ≤ (regW d n k ρ).valR
  Xb_le : (regW d n k ρ).Xb ≤ 1 / 16
  reg_le : (regW d n k ρ).reg ≤ 1
  ePhi_le : (regW d n k ρ).ePhi ≤ (regW d n k ρ).eh
  eX_le : (regW d n k ρ).eX ≤ (regW d n k ρ).eh
  gT : (d : ℝ) * (regW d n k ρ).DP ≤ (regW d n k ρ).Lam
  gW : (regW d n k ρ).Dw ≤ (regW d n k ρ).W0
  gA : 11 / 10 ^ 35 + (regW d n k ρ).Dcw * (1 + (regW d n k ρ).Xw1 ^ 2) ≤ 1 / 2
  coins : n * ((d + 1) / 2 + 1 : ℕ) * (1 / 2 ^ ((parK d n k).B / 2) : ℝ) ≤ (regW d n k ρ).dbits
  budget : n * ((regW d n k ρ).dbits + n * (regW d n k ρ).kap0) ≤ 1 / 4
  kap0_nonneg : 0 ≤ (regW d n k ρ).kap0
  regO_le : (regW d n k ρ).regO ≤ 1
  S_le : (regW d n k ρ).S + (regW d n k ρ).band ≤ 1 / 4
  bits_k : (regW d n k ρ).dbits ≤ (2 : ℝ)⁻¹ ^ k / 8
  kap_k : n * ((regW d n k ρ).kapO + (regW d n k ρ).kapO) ≤ (2 : ℝ)⁻¹ ^ k / 8
  kapO_nonneg : 0 ≤ (regW d n k ρ).kapO

/-- **Theorem BUD-W**: at every `(d, n, k)` and every reference in its regime. -/
theorem budW (d n k : ℕ) (ρ : RefW) (hρ : RegimeW d n ρ) : BudOKW d n k ρ := by
  have hR := reg_okW d n k ρ hρ
  obtain ⟨hx, hV, hb⟩ := hR.p1
  obtain ⟨hXb, hreg⟩ := hR.p4
  obtain ⟨hgT, hgW, hgA⟩ := hR.guard
  obtain ⟨hbud, hk0⟩ := hR.budget
  have hK0 : (0 : ℝ) < 2 ^ k := by positivity
  have hK : (2 : ℝ) ^ k ≤ (regW d n k ρ).Ne := two_pow_le_Ne d n k hρ.hd hρ.hn
  have e2 : (2 : ℝ)⁻¹ ^ k / 8 = 1 / 2 ^ k / 8 := by rw [inv_pow, one_div]
  exact
    { Le_ge := hR.hL1
      Lf_ge := hR.hLf1
      cb_le := hR.cbw_dom
      x_le := hx
      V_le := hV
      hb_le := hb
      hTr_le := fun j hj => hR.hTr_le j (by show (j : ℝ) ≤ (n : ℝ); exact_mod_cast hj)
      sel_le := hR.sel_le
      h_le := hR.h_le_rmin
      val_le := hR.val_le
      Xb_le := hXb
      reg_le := hreg
      ePhi_le := hR.ePhi_le_eh
      eX_le := hR.eX_le_eh
      gT := hgT
      gW := hgW
      gA := hgA
      coins := coins_leK d n k
      budget := hbud
      kap0_nonneg := hk0
      regO_le := hR.regO_le
      S_le := hR.S_le
      bits_k := by rw [e2]; exact hR.bits_k hK0 hK
      kap_k := by rw [e2]; exact hR.kap_k hK0 hK
      kapO_nonneg := hR.kapO_bd.1 }

end AdversarialBco.UW.BudW
