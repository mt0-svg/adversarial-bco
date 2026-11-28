/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailT10
public import AdversarialBco.UW.ProgMachMagDefs
public import AdversarialBco.Unified.TailOFld

@[expose] public section

/-!
# BL-OW's tail R10 to R15 as one contract

The BL-OW copy of BL-O's tail contract and its proof (Unified/TailOTail.lean): from `TIn` at round `t + 1` (R9's values)
and the bounds `TPostO` of the new state, the tail `xtailO` ends in `RPost` with the mode `tailModeO` at BL-OW's round
`RdW` and keeps the arrays 0 and 1 (`Keep01`), from `ExpBLW` and the sub-block contracts under `ParT`.
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

/-- **R10 to R15 of BL-OW** for one command, within `C (W + E1 + 1)^k`, with room `nS, nN, nA`, keeping the arrays
0 and 1. -/
def TailOKW (xtail : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (R : RdW d) (E1 : ℕ) (st : St d) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (s5 : ℤ) (Γ : Fin d → ℤ) (P0 : ℕ → EuclideanSpace ℝ (Fin d)) (σ : Env d),
    InU d R.n R.δ R.r0 R.R0 → LayOK R.L d R.ℓa → BLLay R.L → RoomO R.L nS nN nA →
    TIn R.L R.n 0 R.K0 R.E E1 (cfgV R.c) st (R.t + 1) P0 Ap Bp bp Gp kp lp s5 Γ σ →
    TPostO R.w.orc R.c R.n R.E Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)
      (tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) →
    C * (R.W + E1 + 1) ^ k ≤ R.ℓ → C * (R.W + E1 + 1) ^ k < 2 ^ R.ℓa →
    R.RunsO (xtail R.L) σ (C * (R.W + E1 + 1) ^ k)
      (fun σ' => RPost R.L R.n 0 R.K0 R.E (cfgV R.c)
        (tailModeO R.w.orc R.c R.n st Ap Bp bp Gp kp lp (wmuOf R.c.par st s5 Γ)) (R.t + 1) P0 σ' ∧ Keep01 σ σ')

theorem d_le_WW {d : ℕ} (R : RdW d) : d ≤ R.W := by
  show d ≤ wU d R.n R.δ R.r0 R.R0 R.a
  unfold wU; omega

set_option maxHeartbeats 4000000 in
/-- **The tail of BL-OW's round (R10 to R15) on the machine.** -/
theorem tailOKW_of (hexp : ExpBLW) {xdt xfire xdl xcom : Layout → XCmd} {xcall : Layout → XCmdO}
    {Ct kt Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdt : DTSpecW xdt Ct kt) (hfire : FireSpecW xfire Cf kf) (hdl : DLSpecW xdl Cl kl)
    (hcall : CallSpecW xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc) :
    ∃ C k : ℕ, TailOKW (xtailO xdt xcall xfire xdl xcom) C k nS nN nA := by
  obtain ⟨Cx, kx, hexp⟩ := hexp
  obtain ⟨C, k, hpoly⟩ := tl_poly Cx kx Ct kt Ca ka Cl kl Cc kc Cf kf
  refine ⟨C * 2 ^ k, k, ?_⟩
  intro d R E1 st Ap Bp bp Gp kp lp s5 Γ P0 σ hIn hL hlay hroom hT hpost hℓ hℓa
  have hdW := d_le_WW R
  have hP := parT_rd R hIn
  set Xb := Cx * (R.W + (2 * E1 + 1) + 1) ^ kx with hXb
  have hZ := hpoly d 0 (R.W - d) (R.W - d) E1 Xb (by rw [show d + (R.W - d) = R.W by omega])
  rw [show d + 0 + (R.W - d) = R.W by omega] at hZ
  have hCk : C * (R.W + (R.W - d) + E1 + 1) ^ k ≤ C * 2 ^ k * (R.W + E1 + 1) ^ k := by
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hZ' := hZ.trans hCk
  have hcm : Cc * (d + R.E + 1) ^ kc ≤ Cc * (d + E1 + 1) ^ kc :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hT.hE; omega) _)
  have hfi : Cf * (d + R.E + 1) ^ kf ≤ Cf * (d + E1 + 1) ^ kf :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hT.hE; omega) _)
  have hpw1 := (tl_pow_req d E1 (4 * E1 + 2 * Xb + 3 * d) R.ℓ).1 (by omega)
  have hpw2 := (tl_pow_req d E1 (4 * E1 + 2 * Xb + 3 * d) R.ℓ).2 (by omega)
  have hpw3 := (tl_pow_req d E1 (8 * E1 + 3 * d + 2) R.ℓ).2 (by omega)
  -- the exponent of R11's point
  have hX : frob2 Bp ≤ 2 * (R.c.par.Lam : ℚ) → ellExpO (clearO (callTO R.c st Bp bp Gp)) ≤ Xb := by
    intro hfr
    have bE := (tl_constsW hP hT.inv).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [callTO_eq]
    refine hexp d R.n (2 * E1 + 1) R.δ R.r0 R.R0 R.a R.c _ _ _ Bp _ _ _ hIn rfl (fun i j => (hT.hB i j).2.1) hfr
      (fun j => tl_wp_grid R.c.par.p R.c.par.pF E1 R.c.par.eta bp Gp hP.eta
        (fun j => (hT.hb j).2.1) (fun j => (hT.hG j).2.1) (bE.trans (pow_le_pow_right₀ (by norm_num) hT.hE))
        (fun j => (hT.hb j).2.2) (fun j => (hT.hG j).2.2) j) ?_
    cases st.first
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.head _
  refine XVO.mono (XVO.t10W hdt hfire hdl hcall hcom hIn hL hlay hroom hT hX hpost (by omega) hpw1
    (by omega) (by omega) (by omega) (by omega) (by omega) hpw2 (by omega) (by omega) (by omega) (by omega)
    (by omega) hpw3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_ fun _ h => h
  rw [r10Units_eq]
  unfold u11O u12O u13O u14O
  rw [r12Units_eq, r13Units_eq]
  omega

end AdversarialBco.UW.ProgW
