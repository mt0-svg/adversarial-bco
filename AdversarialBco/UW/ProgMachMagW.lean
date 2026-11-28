/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachMagRun
public import AdversarialBco.UW.ProgMachMagFld

@[expose] public section

/-!
# `magBLW : MagBLW`, the magnitudes of BL-OW's state

The BL-OW copy of BL-O's magnitudes (Unified/MagRun.lean) at the unit `T = 2^{3K}`, `K = pF + 8`: BL-O's level fields
(`Λ`, `R_int`, `B`, `d`, `n`) are bounded at `2^K` by `fld_unit`, PARAM-W's recomputed fields at `d 2^q + 2 ≤ 2^{3K}`
(UW/ProgMachMagFld.lean), the clipped reading at `2^{p + K}`. By `run_bndOW` BL-OW's state in every round `t ≤ n`
in mode `run` has `A', B'` entries at most `T`, `μ'` in the box of radius `R_int` and the sums at most `t T^30`, so
its numerators on the grid `2^{-p}` are at most `T^33 = 2^{99K}` and `99 K ≤ 60000 W` (`Ku_le`).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (Par St Mode init rnd)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (cfgV InU wU)
open AdversarialBco.Unified.MagO (CfgBO)
open AdversarialBco.UW.BLOW (parOW cfgWW modeOW y0OW)
open AdversarialBco.BitRAMO (WorldO)

/-- `X² + X ≤ X³` for `X ≥ 4`. -/
theorem magW_cube {X : ℚ} (h : 4 ≤ X) : X * X + X ≤ X * X * X := by
  nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ X - 4) (mul_self_nonneg X),
    mul_nonneg (by linarith : (0 : ℚ) ≤ X - 4) (by linarith : (0 : ℚ) ≤ X)]

/-- **`magBLW`: the magnitudes of BL-OW's state**, on every input and world. -/
theorem magBLW : MagBLW := by
  refine ⟨60000, 1, ?_⟩
  intro d n E0 δ r0 R0 a hI w _ t st ht hst
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨st0, h0⟩ := modeOW_run0 n δ r0 R0 a w t st hst
  have h0' : mode0O w.orc (cfgWW d n δ r0 R0 a w) = .run st0 := h0
  obtain ⟨heps, -⟩ := Unified.MagO.mode0O_run h0'
  obtain ⟨hT4, hdT, hnT, -, -, -, -, -, -, hLam, -, -, hRint, -, hBT, hpK, -⟩ :=
    Unified.MagO.fld_unit d n (kDel δ) hd hn
  have hKW := Unified.MagO.Ku_le d n δ r0 R0 a hI.hδ0
  have hKe : Unified.MagO.Ku d n (kDel δ) = (parOW d n δ).pF + 8 := rfl
  -- `q ≤ pF`
  have hq : (parOW d n δ).q ≤ (parOW d n δ).pF := by
    have e1 : (parOW d n δ).q = pK d n (kDel δ) + 2 * (leK d n (kDel δ)).size + 24 := rfl
    have e2 : (parOW d n δ).pF = pK d n (kDel δ) + 2 * leK d n (kDel δ) + 4 * Bit.PieceA.ld d + 40 := rfl
    have hs : (leK d n (kDel δ)).size ≤ leK d n (kDel δ) := Nat.size_le.2 Nat.lt_two_pow_self
    omega
  -- the clipped reading: `q_O ≤ p + K`, as for BL-O (same `p`, `n`, `N_e`, `B`)
  have hqO : (cfgWW d n δ r0 R0 a w).qO ≤ (cfgWW d n δ r0 R0 a w).par.p + Unified.MagO.Ku d n (kDel δ) := by
    have h1 := Unified.MagO.qO_le (d := d) (cfgW d n δ r0 R0 a w) d n (kDel δ) hd rfl rfl
    unfold CfgO.qO at h1 ⊢
    exact h1
  generalize Unified.MagO.Ku d n (kDel δ) = K at hT4 hdT hnT hLam hRint hBT hpK hKW hKe hqO
  have hKK : (2 : ℚ) ^ K ≤ 2 ^ (3 * K) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK3 : (2 : ℚ) ^ (3 * K) = 2 ^ K * 2 ^ K * 2 ^ K := by
    rw [show 3 * K = K + K + K by ring, pow_add, pow_add]
  have hKK2 : (2 : ℚ) ^ K * 2 ^ K + 2 ^ K ≤ 2 ^ (3 * K) := hK3 ▸ magW_cube hT4
  have hXX : 4 * 2 ^ K ≤ (2 : ℚ) ^ K * 2 ^ K := mul_le_mul_of_nonneg_right hT4 (by positivity)
  have hpF : (2 : ℚ) ^ (parOW d n δ).pF ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have hqK : (2 : ℚ) ^ (parOW d n δ).q ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (4 : ℚ) ≤ 2 ^ (3 * K) := hT4.trans hKK
  -- PARAM-W's recomputed fields at `2^{3K}`
  have hdq : (d : ℚ) * 2 ^ (parOW d n δ).q + 2 ≤ 2 ^ (3 * K) := by
    have : (d : ℚ) * 2 ^ (parOW d n δ).q ≤ 2 ^ K * 2 ^ K := mul_le_mul hdT hqK (by positivity) (by positivity)
    linarith
  have hq1 : (2 : ℚ) ^ (parOW d n δ).q + 1 ≤ 2 ^ (3 * K) := by linarith
  have hcb : CfgB (2 ^ (3 * K)) (cfgV (cfgWW d n δ r0 R0 a w)) :=
    ⟨h4, hdT.trans hKK, fun i => i.elim0, fun i => i.elim0, (parOW_eps_pos d n δ hd hn).le, heps,
      (fldW_epsI d n δ hd hn).trans (hpF.trans hKK), (fldW_lam d n δ hd hn).trans (by linarith),
      (fldW_kapc d n δ hd hn).trans hdq, (fldW_nu d n δ hd hn).trans (by linarith),
      hLam.trans hKK, (fldW_A0 d n δ hd hn).trans h4, (fldW_B0 d n δ hd hn).trans hq1, hRint.trans hKK⟩
  have hclip : (2 : ℚ) ^ (cfgWW d n δ r0 R0 a w).qO ≤ 2 ^ (cfgWW d n δ r0 R0 a w).par.p * 2 ^ (3 * K) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc : CfgBO (2 ^ (3 * K)) (cfgWW d n δ r0 R0 a w) := ⟨hcb, hclip⟩
  have hBe : (parK d n (kDel δ)).B = 2 * ((parK d n (kDel δ)).p + (n * (d + 2)).size + 2) := rfl
  have hp160 := (Unified.MagO.pF_ge d n (kDel δ)).1
  have hB8 : 8 ≤ (parK d n (kDel δ)).B := by rw [hBe]; omega
  have hs := run_bndOW n δ r0 R0 a w hc (hBT.trans hKK) hB8 (fldW_y0 d n δ hd hn) t st hst
  have hT2 : (2 : ℚ) ≤ 2 ^ (3 * K) := by linarith
  have hT1' : (1 : ℚ) ≤ 2 ^ (3 * K) := by linarith
  have hp : (2 : ℚ) ^ (parOW d n δ).p ≤ 2 ^ (3 * K) :=
    pow_le_pow_right₀ (by norm_num) (by have : (parOW d n δ).p ≤ K := hpK; omega)
  have key : ∀ x : ℚ, |x| ≤ ((2 : ℚ) ^ (3 * K)) ^ 31 →
      |qn (parOW d n δ).p x| ≤ 2 ^ (60000 * (wU d n δ r0 R0 a + E0 + 1) ^ 1) := fun x hx => by
    have h := qn_bnd hT2 hp hx
    have h2 : ((2 : ℚ) ^ (3 * K)) ^ (31 + 2) ≤ 2 ^ (60000 * (wU d n δ r0 R0 a + E0 + 1) ^ 1) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by rw [pow_one]; omega)
    exact_mod_cast h.trans h2
  have hsum : ∀ y : ℚ, |y| ≤ t * ((2 : ℚ) ^ (3 * K)) ^ 30 → |y| ≤ ((2 : ℚ) ^ (3 * K)) ^ 31 := fun y hy => by
    have ht' : (t : ℚ) ≤ 2 ^ (3 * K) := ((by exact_mod_cast ht : (t : ℚ) ≤ n).trans hnT).trans hKK
    have h30 : (0 : ℚ) ≤ ((2 : ℚ) ^ (3 * K)) ^ 30 := by positivity
    calc |y| ≤ t * ((2 : ℚ) ^ (3 * K)) ^ 30 := hy
      _ ≤ 2 ^ (3 * K) * ((2 : ℚ) ^ (3 * K)) ^ 30 := mul_le_mul_of_nonneg_right ht' h30
      _ = ((2 : ℚ) ^ (3 * K)) ^ 31 := by ring
  have hent : ∀ y : ℚ, |y| ≤ 2 ^ (3 * K) → |y| ≤ ((2 : ℚ) ^ (3 * K)) ^ 31 := fun y hy =>
    bnd_up hT1' (pw1 hy) (by norm_num)
  exact ⟨fun i j => key _ (hent _ (hs.A i j)), fun i j => key _ (hent _ (hs.B i j)), fun j => key _ (hsum _ (hs.b j)),
    key _ (hsum _ hs.k), fun j => key _ (hsum _ (hs.G j)), key _ (hsum _ hs.l), hs.mu⟩

end AdversarialBco.UW.ProgW
