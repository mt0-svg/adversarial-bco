/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupKs

@[expose] public section

/-!
# BL's setup on the machine: the position it leaves, and its exponent

`setupBL_ok'`: the hypothesis `hsetup` of `prog_ok_frozenR` on every world, with
`Ks = NS + 2 NA + 7 + initUnits`, and one more conjunct: the position `(μ, A)` of the configuration bounded at
`E0 = sT` (`PosBnd`), as TRI leaves it. `setupE_le`: the exponents the setup needs, `75 G + 343`, `sF`, `sT`,
`size M` and `m`, sum to at most `C_E W^{k_E}` with `W = d m (size n + 1)(size M + 1)`,
`C_E = 10^7 + C_f 4^{k_f} + C_t (5 + C_f 4^{k_f})^{k_t} + 1` and `k_E = (k_f + 1)(k_t + 1) + 2`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- **BL's setup meets `hsetup` of `prog_ok_frozenR`, with the position bounded at `sT`.** -/
theorem setupBL_ok' {L : Layout} {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ E : ℕ} {xframe xtri : Layout → PrBlk → XCmd} {Cf kf nSf nNf nAf Ct kt nSt nNt nAt : ℕ}
    (hF : FrameSpec xframe Cf kf nSf nNf nAf) (hT : TriSpec xtri Ct kt nSt nNt nAt) (hL : LayOK L d ℓa)
    (hlay : BLLay L) (hOKf : blkS.OK L nSf nNf nAf) (hOKt : blkS.OK L nSt nNt nAt)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hH : RealRAM.HeightLE A b M) (hM1 : 1 ≤ M)
    (hEG : 75 * parG d n + 343 ≤ E) (hEf : sF Cf kf d m A b ≤ E)
    (hEt : sT Ct kt d n m (sF Cf kf d m A b) A b ≤ E) (hME : M ≤ 2 ^ E) (hmE : m ≤ 2 ^ E)
    (hℓ : 3 * (E * d) + 10 * E + 5 ≤ ℓ) (hℓa : E + 2 * ((d + 1) * m) + 4 < 2 ^ ℓa) (w : BitRAM.World d) :
    ∃ k s1 σ1, k ≤ L.NS + 2 * L.NA + 7 + initUnits d n m (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b) ∧
      XExecB (ctxOf w n m A b) ℓa ℓ (xsetupBL L xframe xtri) zeroState k s1 ∧ Rep L σ1 s1 ∧
      (BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (mode0 (cfgOf RoutinesQ d n m A b w.cs)) 0 σ1 ∧
        σ1.pts = fun _ => 0) ∧
      PosBnd (cfgOf RoutinesQ d n m A b w.cs) (sT Ct kt d n m (sF Cf kf d m A b) A b) := by
  obtain ⟨hS, hN, hA⟩ := id hlay
  simp only [oE, rEE, aWE] at hS hN hA
  have hX0 : (ctxOf w n m A b).inp 0 = d := (BitRAM.Conj1BitSanity.inputMem_small (n := n) A b).1
  have hoff : 1 ≤ (ctxOf w n m A b).off := by show 1 ≤ offOf d m; unfold offOf; omega
  have hdl : (d : ℝ) < 2 ^ ℓ := by
    have h1 : d ≤ 2 ^ parG d n := d_le_G
    have h2 : 2 ^ parG d n < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact_mod_cast h1.trans_lt h2
  obtain ⟨s₁, e₁, r₁⟩ := xsetup_exec (X := ctxOf w n m A b) hL (dv := rD) (by fomega) (by omega) (by omega) hX0 hoff
    hdl
  obtain ⟨k, s₂, σ₂, hk, e₂, r₂, q₂⟩ :=
    XV.initBL (w := w) hF hT hL hlay hOKf hOKt hd hn hH hM1 hEG hEf hEt hME hmE hℓ hℓa s₁ r₁
  exact ⟨_, s₂, σ₂, by omega, XExecB.seq e₁ e₂, r₂, q₂.1, q₂.2⟩

/-- **The exponents of the setup are polynomial** in `W = d m (size n + 1)(size M + 1)`. -/
theorem setupE_le {d n m M : ℕ} (Cf kf Ct kt : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hH : RealRAM.HeightLE A b M) (hM : 1 ≤ M) :
    75 * parG d n + 343 + sF Cf kf d m A b + sT Ct kt d n m (sF Cf kf d m A b) A b + M.size + m ≤
      (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt + 1) * (d * m * (n.size + 1) * (M.size + 1)) ^
        ((kf + 1) * (kt + 1) + 2) := by
  have h1 := initUnits_le Cf kf Ct kt A b hd hn hm hH hM
  have h2 : 75 * parG d n + 343 + sF Cf kf d m A b + sT Ct kt d n m (sF Cf kf d m A b) A b ≤
      initUnits d n m (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b) := by
    unfold initUnits callUnits
    omega
  have h3 : M.size + m ≤ d * m * (n.size + 1) * (M.size + 1) := by
    have e1 : 1 * m * 1 * (M.size + 1) ≤ d * m * (n.size + 1) * (M.size + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hd le_rfl) (by omega)) le_rfl
    have e2 : 1 * M.size ≤ m * M.size := Nat.mul_le_mul_right _ hm
    rw [one_mul, mul_one, Nat.mul_add, mul_one] at e1
    omega
  have h4 : d * m * (n.size + 1) * (M.size + 1) ≤
      (d * m * (n.size + 1) * (M.size + 1)) ^ ((kf + 1) * (kt + 1) + 2) := Nat.le_self_pow (by omega) _
  calc 75 * parG d n + 343 + sF Cf kf d m A b + sT Ct kt d n m (sF Cf kf d m A b) A b + M.size + m
      ≤ initUnits d n m (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b) +
          d * m * (n.size + 1) * (M.size + 1) := by omega
    _ ≤ (10 ^ 7 + Cf * 4 ^ kf + Ct * (5 + Cf * 4 ^ kf) ^ kt) * (d * m * (n.size + 1) * (M.size + 1)) ^
          ((kf + 1) * (kt + 1) + 2) + (d * m * (n.size + 1) * (M.size + 1)) ^ ((kf + 1) * (kt + 1) + 2) :=
        Nat.add_le_add h1 h4
    _ = _ := by ring

end AdversarialBco.Bit.Transfer.BLM
