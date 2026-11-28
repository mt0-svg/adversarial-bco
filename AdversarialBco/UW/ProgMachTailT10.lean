/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailT12
public import AdversarialBco.Unified.TailOT10

@[expose] public section

/-!
# BL-OW's tail, R10 on the machine

The BL-OW copy of BL-O's R10 run (Unified/TailOT10.lean): the same command `xtailO` (R10, its two guards, R11 to R15)
and units, at BL-OW's round `RdW`, under `ParT`, keeping the arrays 0 and 1 (`Keep01`).
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.UW.BLOW (parOW cfgWW)
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

set_option maxHeartbeats 2000000 in
/-- **R10 TRACE of BL-OW on the machine**, then R11 to R15, keeping the arrays 0 and 1. -/
theorem XVO.t10W {xdt xfire xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO}
    {Ct kt Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdt : DTSpecW xdt Ct kt) (hfire : FireSpecW xfire Cf kf) (hdl : DLSpecW xdl Cl kl)
    (hcall : CallSpecW xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {R : RdW d} {E1 : ℕ} {st : St d} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {Xb : ℕ}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hT : TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hX : frob2 Bp ≤ 2 * (R.c.par.Lam : ℚ) → ellExpO (clearO (callTO R.c st Bp bp Gp)) ≤ Xb)
    (hpost : TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
      (tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)))
    (hr1 : 3 * E1 + 1 < R.ℓ) (hr2 : d * d * 2 ^ (2 * E1) < 2 ^ R.ℓ)
    (hℓt : Ct * (d + E1 + 1) ^ kt ≤ R.ℓ) (hℓat : Ct * (d + E1 + 1) ^ kt < 2 ^ R.ℓa)
    (hℓc : Ca * (R.W + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ R.ℓ)
    (hℓac : Ca * (R.W + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka < 2 ^ R.ℓa)
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < R.ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ R.ℓ) (hXa : Xb < 2 ^ R.ℓa)
    (hℓf : Cf * (d + R.E + 1) ^ kf ≤ R.ℓ) (hℓaf : Cf * (d + R.E + 1) ^ kf < 2 ^ R.ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < R.ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < R.ℓ)
    (hℓc' : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ R.ℓ) (hda : d * d + d < 2 ^ R.ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ R.ℓ)
    (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ R.ℓa)
    (hℓ2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ R.ℓ)
    (hℓa2 : Ca * (R.W + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ R.ℓa)
    (hℓ3 : Cc * (d + R.E + 1) ^ kc ≤ R.ℓ) (hℓa3 : Cc * (d + R.E + 1) ^ kc < 2 ^ R.ℓa) :
    R.RunsO (xtailO xdt xcall xfire xdl xcom R.L) σ
      (r10Units d + (u11O Ct kt Cf kf Cl kl Ca ka Cc kc d R.W R.E E1 Xb + 4))
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) (R.t + 1) P0 σ' ∧
        Keep01 σ σ') := by
  have hℓ : 1 ≤ R.ℓ := by omega
  have hP := parT_rd R hIn
  have pE : (2 : ℤ) ^ R.E ≤ 2 ^ E1 := pow_le_pow_right₀ (by norm_num) hT.hE
  obtain ⟨eQ, bQ, -, -, -, -, -, -, eL, bL, -⟩ := tl_constsW hP hT.inv
  set Ah : Matrix (Fin d) (Fin d) ℤ := fun i j => qn R.c.par.p (Ap i j) with hAh
  set Bh : Matrix (Fin d) (Fin d) ℤ := fun i j => qn R.c.par.p (Bp i j) with hBh
  have eA : ∀ k < d * d, σ.arr aAp k = flatM Ah k := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hA i j).1
  have eB : ∀ k < d * d, σ.arr aBp k = flatM Bh k := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hB i j).1
  have bA : ∀ k < d * d, |flatM Ah k| ≤ 2 ^ E1 := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hA i j).2.2
  have bB : ∀ k < d * d, |flatM Bh k| ≤ 2 ^ E1 := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hB i j).2.2
  -- R10's sums
  refine XVO.seq (XVO.ofX (XV.r10 hL hlay (σ := σ) (Q := 2 ^ R.c.par.p) (Lam := R.c.par.Lam) (E := E1)
    (Af := flatM Ah) (Bf := flatM Bh) hT.inv.regs.1 hT.inv.regs.2.2.2.1 hT.inv.consts.1 eQ eL eA eB bA bB
    (bQ.trans pE) (bL.trans pE) hr1 hr2 hda)) fun σ1 ⟨v89, v90, v88, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [tR, nSP] at hy ⊢; omega) (fun j hj => by omega)
    (fun a k hk => hk.elim) d1
  have k1 : Keep01 σ σ1 := Keep01.ofA F1 fun _ => ⟨fun h => h.elim, fun h => h.elim⟩
  have hdB := frob2_flat R.c.par.p R.c.par.Lam Bp (flatM Bh) (fun i j => tl_flat_eq Bh i j)
    (fun i j => (hT.hB i j).2.1)
  have hdA := frob2_flat R.c.par.p R.c.par.Lam Ap (flatM Ah) (fun i j => tl_flat_eq Ah i j)
    (fun i j => (hT.hA i j).2.1)
  obtain ⟨t88, t89⟩ := tl_r10_test_abs d (R.c.par.Lam : ℤ) (2 ^ R.c.par.p) (flatM Bh) E1 R.ℓ (bL.trans pE)
    (bQ.trans pE) bB hr1 hr2
  obtain ⟨-, t90⟩ := tl_r10_test_abs d (R.c.par.Lam : ℤ) (2 ^ R.c.par.p) (flatM Ah) E1 R.ℓ (bL.trans pE)
    (bQ.trans pE) bA hr1 hr2
  have hS := hlay.1
  have s88 : 88 < R.L.NS := by simp only [oE] at hS; omega
  have s89 : 89 < R.L.NS := by simp only [oE] at hS; omega
  have s90 : 90 < R.L.NS := by simp only [oE] at hS; omega
  have r88 : |σ1.sc 88| < 2 ^ R.ℓ := by rw [v88]; exact t88
  by_cases hc1 : σ1.sc 88 < σ1.sc 89
  · -- the trace guard of `B'`
    have h1 : 2 * (R.c.par.Lam : ℚ) < frob2 Bp := by rw [v88, v89, Int.cast_lt] at hc1; exact hdB.2 hc1
    have em : tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) = .guard := by
      unfold tailModeO; simp only [h1, true_or, ↓reduceIte]
    rw [em]
    exact XVO.mono (XVO.ifS_t hL s88 s89 r88 (by rw [v89]; exact t89) hc1
      (XVO.ofX (XV.guardK hL hT1.inv hT1.pts hℓ))) (by omega) fun _ h => ⟨h.1, k1.trans h.2⟩
  · have h1 : ¬ 2 * (R.c.par.Lam : ℚ) < frob2 Bp := fun h => hc1 (by
      rw [v88, v89, Int.cast_lt]; exact hdB.1 h)
    by_cases hc2 : σ1.sc 88 < σ1.sc 90
    · -- the trace guard of `A'`
      have h2 : 2 * (R.c.par.Lam : ℚ) < frob2 Ap := by rw [v88, v90, Int.cast_lt] at hc2; exact hdA.2 hc2
      have em : tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) = .guard := by
        unfold tailModeO; simp only [h1, h2, or_true, ↓reduceIte]
      rw [em]
      exact XVO.mono (XVO.ifS_f hL s88 s89 r88 (by rw [v89]; exact t89) hc1
        (XVO.ifS_t hL s88 s90 r88 (by rw [v90]; exact t90) hc2 (XVO.ofX (XV.guardK hL hT1.inv hT1.pts hℓ))))
        (by omega) fun _ h => ⟨h.1, k1.trans h.2⟩
    · -- R11 to R15
      have h2 : ¬ 2 * (R.c.par.Lam : ℚ) < frob2 Ap := fun h => hc2 (by
        rw [v88, v90, Int.cast_lt]; exact hdA.1 h)
      have em : tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) =
          m11O R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ) := by
        unfold tailModeO; simp only [h1, h2, or_self, ↓reduceIte]
      rw [em] at hpost ⊢
      exact XVO.mono (XVO.ifS_f hL s88 s89 r88 (by rw [v89]; exact t89) hc1
        (XVO.ifS_f hL s88 s90 r88 (by rw [v90]; exact t90) hc2
          (XVO.t11W hdt hfire hdl hcall hcom hIn hL hlay hroom hT1 (hX (not_lt.1 h1)) hpost hℓt hℓat hℓc hℓac hg1
            hg2 hXa hℓf hℓaf hℓa hℓb hℓc' hda hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3))) le_rfl
        fun _ h => ⟨h.1, k1.trans h.2⟩

end AdversarialBco.UW.ProgW
