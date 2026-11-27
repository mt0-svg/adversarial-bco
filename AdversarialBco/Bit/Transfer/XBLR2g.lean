/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2

@[expose] public section

/-!
# BL's round on the machine, R2 PLAYPT in mode `run`, the gauge: pieces

The rule of a conditional with an empty branch (`XV.ifS_skip`), `omega` on the cell names (`scS`, `scO`), the exponent
of the gauge's pairs (`tG`) and `pow_mono_z`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## Conditionals on slots with an empty branch -/

section Rules

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

theorem XV.ifS_skip (hL : LayOK L d ℓa) {x y : ℕ} {c : XCmd} {σ : Env d} {K : ℕ} {P : Env d → Prop}
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ)
    (ht : σ.sc x < σ.sc y → XRunsB L X ℓa ℓ c σ K P) (hf : ¬ σ.sc x < σ.sc y → P σ) :
    XRunsB L X ℓa ℓ (xifS L x y c .skip) σ (K + 2) P := by
  by_cases h : σ.sc x < σ.sc y
  · exact XV.mono (XV.ifS_t hL hx hy hvx hvy h (ht h)) (by omega) fun _ h => h
  · exact XV.mono (XV.ifS_f hL hx hy hvx hvy h (XV.skip σ)) (by omega) fun σ' e => e ▸ hf h

end Rules

/-! ## The code -/

/-- The cells the gauge changes. -/
def SG (y : ℕ) : Prop := (sBN ≤ y ∧ y ≤ sRQ) ∨ tR ≤ y
def NG (j : ℕ) : Prop := rD1 ≤ j ∧ j ≤ rk
def AG (a _k : ℕ) : Prop := a = aRw

/-- The registers one row changes: the gauge's but the row counter. -/
def NGr (j : ℕ) : Prop := rI ≤ j ∧ j ≤ rk

/-- `omega` after unfolding the cell names in the goal only (the layout bounds normalized beforehand). -/
macro "qomega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst,
  sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu,
  sK, sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0, sEl, aEH, aEg, aEP, aEf, oE, rEE, aWE, rJ, rT, rD2,
  sZeta, aGam, oBM, rD1, rK, rI, rTT, rjj, ri, rr, rk, sDX, sPtN, sPtD, sBN, sBD, sGN, sGD, sC1, sC2, sTa, sRB, sRD,
  sRT, sRN, sRQ, sAcc, tR, aWv, aXh, aYv, aPl, aRw, SR2, NR2, AR2, SG, NG, NGr, AG, ne_eq, not_or, not_and,
  not_not]) <;> omega))

theorem scS (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).sc x = v := by simp

theorem scO (σ : Env d) {x y : ℕ} (h : y ≠ x) (v : ℝ) : (σ.setSc x v).sc y = σ.sc y := by
  simp [Env.setSc_sc, h]


/-! ## One row -/

/-- The exponent of the gauge's pairs. -/
def tG (d E : ℕ) : ℕ := E * d + 10 * E + 2

theorem pow_mono_z {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

end AdversarialBco.Bit.Transfer.BLM
