/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOT10
public import AdversarialBco.Unified.MagField

@[expose] public section

/-!
# PARAM facts for BL-O's tail

At `parK d n k` (BL-O's PARAM, `parO d n δ = parK d n (kDel δ)`): `ε' > 0` (`eps_posK`, which R5 reads), and the
radius `W` of R13's guard below `2^{2K+10}`, `K = Ku d n k` the unit of MagField.lean (`W_bndK`), which bounds R14's
linear term. `head_wmuO`: the point `w_μ` that the round computes is `wmuOf` at any PARAM.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Unified.BLO
open AdversarialBco.Unified.BudK (parK parK_eps parK_W parK_Le L0 ee)
open AdversarialBco.Bit.BLP (Par sqrtDn sqrtUp up)

theorem eps_posK (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < (parK d n k).eps := by
  obtain ⟨hL1, -, -⟩ := MagO.LeQ_bnd d n k hd hn
  obtain ⟨hr0, -⟩ := MagO.rd_bnd d n k hd
  have hn1 := MagO.rn_ge d n k hn
  have hee : 0 ≤ ee d n k := by unfold ee Bit.BLP.lnErr; positivity
  rw [parK_Le] at hL1
  rw [parK_eps]
  refine lt_of_lt_of_le ?_ (Bit.BLP.le_up _ _)
  have h36 : (0 : ℚ) < 36 * (L0 d n k + ee d n k) := by linarith
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hs : (0 : ℚ) < sqrtDn (parK d n k).q d + 1 / 2 ^ (parK d n k).q := by
    have : (0 : ℚ) < 1 / 2 ^ (parK d n k).q := by positivity
    linarith
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hd') hs) (pow_pos h36 5)) (by linarith)

theorem sqrtUp_pos (q : ℕ) (y : ℚ) : 0 < sqrtUp q y := by unfold sqrtUp; positivity

theorem sqrtUp_le_add (q : ℕ) (hq : 1 ≤ q) (y : ℚ) (hy : 0 ≤ y) : sqrtUp q y ≤ y + 2 := by
  have h := Bit.PieceA.sqrtUp_le q y
  have hq' : (2 : ℝ) / 2 ^ q ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
    linarith
  have hy' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hsq : Real.sqrt ((y : ℚ) : ℝ) ≤ (y : ℝ) + 1 :=
    calc Real.sqrt ((y : ℚ) : ℝ) ≤ Real.sqrt (((y : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (y : ℝ) + 1 := Real.sqrt_sq (by positivity)
  have : ((sqrtUp q y : ℚ) : ℝ) ≤ (y : ℝ) + 2 := by linarith
  exact_mod_cast this

theorem W_arith {W R s X N Le d e : ℚ} (hW : W < R + 4 * d * s + e) (he : e ≤ 1) (hR : R ≤ 1000 * d ^ 2)
    (hs : s ≤ N / Le + 2) (hs0 : 0 < s) (hL : 1 ≤ Le) (hN0 : 0 ≤ N) (hNX : N ≤ X) (hdX : d ≤ X) (hd0 : 0 ≤ d)
    (hX4 : 4 ≤ X) : W ≤ 1024 * (X * X) := by
  have h1 : N / Le ≤ N := div_le_self hN0 hL
  have h2 : s ≤ X + 2 := by linarith
  have h3 : d * s ≤ X * (X + 2) := mul_le_mul hdX h2 hs0.le (by linarith)
  have h4 : d ^ 2 ≤ X * X := by rw [sq]; exact mul_le_mul hdX hdX hd0 (by linarith)
  nlinarith

theorem W_bndK (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    0 ≤ (parK d n k).W ∧ (parK d n k).W ≤ 2 ^ (2 * MagO.Ku d n k + 10) := by
  obtain ⟨hT4, hdT, -, hNeT, -⟩ := MagO.fld_unit d n k hd hn
  obtain ⟨hL1, -, -⟩ := MagO.LeQ_bnd d n k hd hn
  obtain ⟨hR0, hR1⟩ := MagO.R_bnd d n k hd hn
  have hN0 : (0 : ℚ) ≤ (NeO d n k : ℚ) := Nat.cast_nonneg _
  have hy0 : (0 : ℚ) ≤ (NeO d n k : ℚ) / (parK d n k).Le := div_nonneg hN0 (by linarith)
  have hs1 := sqrtUp_le_add (parK d n k).q (MagO.q_ge d n k) _ hy0
  have hs0 := sqrtUp_pos (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le)
  have hup := Bit.BLP.up_lt (parK d n k).pF
    ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le))
  have hlo := Bit.BLP.le_up (parK d n k).pF
    ((parK d n k).R + 4 * d * sqrtUp (parK d n k).q ((NeO d n k : ℚ) / (parK d n k).Le))
  have hp : (1 : ℚ) / 2 ^ (parK d n k).pF ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  have e2 : (2 : ℚ) ^ (2 * MagO.Ku d n k + 10) = 1024 * (2 ^ MagO.Ku d n k * 2 ^ MagO.Ku d n k) := by
    rw [pow_add, mul_comm 2, pow_mul]; ring
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg _
  rw [parK_W, e2]
  refine ⟨le_trans (by positivity) hlo, W_arith hup hp hR1 hs1 hs0 hL1 hN0 hNeT hdT hd0 hT4⟩

/-- The point `w_μ` of the round is `wmuOf` at any PARAM and any draw `ξ` equal to `Γ / 2^{2 gsm_prec B}`. -/
theorem head_wmuO {d : ℕ} (cfg : Bit.BLP.Cfg d) (st : Bit.BLP.St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) (P : Par)
    (s5 : ℤ) (Γ : Fin d → ℤ) (hpar : cfg.par = P)
    (hξ : ξ = fun i => (Γ i : ℚ) / 2 ^ (2 * Bit.gsm_prec cfg.par.B))
    (h5 : Bit.Transfer.BLM.rs5 cfg st ξ ζ obs = (s5 : ℚ) / ((2 ^ cfg.par.p : ℤ) : ℚ)) :
    Bit.Transfer.BLM.rwmu cfg st ξ ζ obs = Bit.Transfer.BLM.wmuOf P st s5 Γ := by
  subst hξ
  rw [Bit.Transfer.BLM.rwmu, h5, Bit.Transfer.BLM.wmuOf, ← hpar]
  push_cast
  rfl

end AdversarialBco.Unified.ProgO
