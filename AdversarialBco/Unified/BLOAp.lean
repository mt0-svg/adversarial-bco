/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOGeom
public import AdversarialBco.Unified.EllOMain
public import AdversarialBco.Bit.ApQ.Clear

@[expose] public section

/-!
# BL-O: (O3) for the calls of ELL-O in a good position

`apSpecO : ApSpecO`: a call of BL-O (`apO`, R11 and R14) returns a point of `QK ∩ regionC D` within `e` of the
infimum of the call's objective there, `QK = QKs (1 - ε')⁻¹`, from `ellOAcc` (Unified/EllOMain.lean) with
its hypotheses supplied: `QK` convex, closed, bounded by `Rg (1 - ε')`, holding `B̄(0, 1/2)`; the test certifies `QK`
about `0` with the band `6·2^{-(eK + kK)} Rg R0/r0² ≤ 2^{-eK}` (`testCertO`, `band_le`); the integer call `clearO D`
has the region `regionC D` and the objective `objDen D` times the call's (`clearQ`'s lemmas, Bit/ApQ/Clear.lean).
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp AdversarialBco.Uni AdversarialBco.Bit.RQ
open AdversarialBco.Bit.ApQ (clearQ_H clearQ_g clearQ_ℓ clearQ_P clearQ_f objDen_pos quadDen_pos linDen_pos
  dot_scale quad_scale)
open AdversarialBco.Bit.BLP (CallQ)
open AdversarialBco.BitRAM (toE)
open Metric Matrix

variable {d : ℕ}

theorem regionO_clearO (D : CallQ d) : regionO (clearO D) = regionC D := by
  ext y
  have hH : (clearO D).H.map ((↑) : ℤ → ℝ) = (quadDen D : ℝ) • D.H.map ((↑) : ℚ → ℝ) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_H D i j
  have hq : (0 : ℝ) < quadDen D := by exact_mod_cast quadDen_pos D
  have e2 : (fun j => (((clearO D).g j : ℤ) : ℝ)) = fun j => (quadDen D : ℝ) * ((D.g j : ℚ) : ℝ) := by
    funext j; exact clearQ_g D j
  have eℓ : (((clearO D).ℓ : ℤ) : ℝ) = quadDen D * ((D.ℓ : ℚ) : ℝ) := clearQ_ℓ D
  simp only [regionO, regionC, Set.mem_ofPred_eq]
  rw [hH, quad_scale, e2, dot_scale, eℓ]
  apply and_congr _ Iff.rfl
  constructor
  · intro h
    have : (quadDen D : ℝ) * (y ⬝ᵥ (D.H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => ((D.g j : ℚ) : ℝ)) ⬝ᵥ y) ≤
      (quadDen D : ℝ) * ((D.ℓ : ℚ) : ℝ) := by linarith
    exact le_of_mul_le_mul_left this hq
  · intro h
    nlinarith

theorem GO_clearO (D : CallQ d) (y : Fin d → ℝ) : GO (clearO D) y = objDen D * D.obj y := by
  have hP : (clearO D).P.map ((↑) : ℤ → ℝ) = (objDen D : ℝ) • D.P.map ((↑) : ℚ → ℝ) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_P D i j
  have hf : (fun j => (((clearO D).f j : ℤ) : ℝ) / (clearO D).Df) =
      fun j => (objDen D : ℝ) * ((D.f j : ℚ) : ℝ) := by
    funext j; exact clearQ_f D j
  simp only [GO, CallQ.obj]
  rw [hP, quad_scale, hf, dot_scale]
  ring

theorem clearO_c (D : CallQ d) : qR (clearO D).c = 0 := by
  funext i
  simp [EllOI.c, clearO, ptDN, qR]

theorem convex_QKs {K : Set (E d)} (hK : Convex ℝ K) (c : CfgO d) (s : ℚ) : Convex ℝ (QKs K c s) := by
  intro x hx y hy a b ha hb hab
  show WithLp.toLp 2 ((s : ℝ) • (a • x + b • y)) ∈ bodyS K c
  have e : WithLp.toLp 2 ((s : ℝ) • (a • x + b • y)) =
      a • WithLp.toLp 2 ((s : ℝ) • x) + b • WithLp.toLp 2 ((s : ℝ) • y) := by
    simp only [smul_add, WithLp.toLp_add, WithLp.toLp_smul]
    rw [smul_comm (s : ℝ) a, smul_comm (s : ℝ) b]
  rw [e]
  exact convex_posBodyO hK _ _ hx hy ha hb hab

theorem isClosed_QKs {K : Set (E d)} (hK : IsClosed K) (c : CfgO d) (s : ℚ) : IsClosed (QKs K c s) := by
  have h1 : IsClosed (bodyS K c) := hK.preimage (continuous_const.add (pgOp c.S).continuous)
  exact h1.preimage (by fun_prop)

theorem norm_QKs (s : ℚ) (hs : 0 ≤ s) (y : Fin d → ℝ) :
    ‖(WithLp.toLp 2 ((s : ℝ) • y) : E d)‖ = s * oNorm y := by
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hs), oNorm_eq]

theorem apSpecO : ApSpecO := by
  intro d K orc c Rg D a0 hd hF hG hRg hRgR heps0 heps hR hr he hP hH hball
  have hF' := hF
  obtain ⟨hK, hKc, hr0, hrR, -, -, -⟩ := hF
  have hG' := hG
  obtain ⟨hB1, hBR⟩ := hG
  have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
  have hrR' : (c.r0 : ℝ) ≤ c.R0 := by exact_mod_cast hrR
  have hR0 : (0 : ℝ) < c.R0 := lt_of_lt_of_le hr0' hrR'
  set I := clearO D with hI
  set s : ℚ := (1 - c.par.eps)⁻¹ with hsdef
  have h1e : (1 / 2 : ℚ) ≤ 1 - c.par.eps := by linarith
  have hs0 : 0 < s := by rw [hsdef]; apply inv_pos.2; linarith
  have hs2 : s ≤ 2 := by
    rw [hsdef]
    calc (1 - c.par.eps)⁻¹ ≤ (1 / 2 : ℚ)⁻¹ := inv_anti₀ (by norm_num) h1e
      _ = 2 := by norm_num
  have hs0R : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs2R : (s : ℝ) ≤ 2 := by exact_mod_cast hs2
  -- the hypotheses of `ellOAcc`
  have hcert := testCertO d K orc c Rg (I.eK + c.kK) s hF' hG' hRg hs0
  have hband := band_le c (I.eK + c.kK) (by omega) Rg hRgR hr0' hR0.le
  rw [Nat.add_sub_cancel] at hband
  have hη0 : 0 ≤ 6 * (2 : ℝ)⁻¹ ^ (I.eK + c.kK) * Rg * c.R0 / c.r0 ^ 2 := by
    have : (0 : ℝ) ≤ Rg := by linarith
    positivity
  have hQR : QKs K c s ⊆ oBall 0 ((s : ℝ)⁻¹ * Rg) := by
    intro y hy
    have h := hBR hy
    rw [mem_closedBall, dist_zero_right, norm_QKs s hs0.le] at h
    simp only [oBall, Set.mem_ofPred_eq, sub_zero]
    rw [le_inv_mul_iff₀ hs0R]
    exact h
  have hQ1 : oBall (qR I.c) ((2 : ℝ)⁻¹ ^ I.erK) ⊆ QKs K c s := by
    rw [clearO_c]
    intro y hy
    simp only [oBall, Set.mem_ofPred_eq, sub_zero] at hy
    apply hB1
    rw [mem_closedBall, dist_zero_right, norm_QKs s hs0.le]
    have herK : I.erK = 1 := rfl
    rw [herK, pow_one] at hy
    have hy0 : 0 ≤ oNorm y := Real.sqrt_nonneg _
    nlinarith
  have hcI : oNorm (qR I.c) ≤ I.R := by
    rw [clearO_c]
    have : oNorm (0 : Fin d → ℝ) = 0 := by simp [oNorm]
    rw [this]
    have : (1 : ℝ) ≤ D.R := by exact_mod_cast hR
    show (0 : ℝ) ≤ D.R
    linarith
  have hP' : (I.P.map ((↑) : ℤ → ℝ)).PosDef := by
    have hob : (0 : ℝ) < objDen D := by exact_mod_cast objDen_pos D
    have : I.P.map ((↑) : ℤ → ℝ) = (objDen D : ℝ) • D.P.map ((↑) : ℚ → ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_P D i j
    rw [this]; exact hP.smul hob
  have hH' : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef := by
    have : I.H.map ((↑) : ℤ → ℝ) = (quadDen D : ℝ) • D.H.map ((↑) : ℚ → ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]; exact clearQ_H D i j
    rw [this]; exact hH.smul (by positivity)
  have he' : 0 < I.e := by
    show 0 < (objDen D : ℚ) * D.e
    have : (0 : ℚ) < objDen D := by exact_mod_cast objDen_pos D
    exact mul_pos this he
  have hball' : oBall a0 (2 * ((I.r : ℚ) : ℝ)) ⊆ QKs K c s ∩ regionO I := by
    rw [hI, regionO_clearO]
    have e : (2 : ℝ) * (((clearO D).r : ℚ) : ℝ) = D.r := by
      show (2 : ℝ) * (((D.r / 2 : ℚ)) : ℝ) = D.r
      push_cast; ring
    rw [e]
    exact hball
  have hcert' : TestCert (c.T orc (I.eK + c.kK) s) (QKs K c s) (qR I.c)
      (6 * (2 : ℝ)⁻¹ ^ (I.eK + c.kK) * Rg * c.R0 / c.r0 ^ 2) := by
    rw [clearO_c]; exact hcert
  obtain ⟨x, hx, hmem, hopt⟩ := EllO.ellOAcc d I (c.T orc (I.eK + c.kK) s) (QKs K c s) ((s : ℝ)⁻¹ * Rg) _ a0 hd
    (show (1 : ℚ) ≤ D.R from hR) (show (0 : ℚ) < D.r / 2 by linarith) he' (linDen_pos D) hP' hH'
    (convex_QKs hK c s) (isClosed_QKs hKc c s) hQR hQ1 hcI hcert' hη0 hband hball'
  have hpt : (fun j => (((x j : ℚ) / 2 ^ ellExpO I : ℚ) : ℝ)) = fun j => (x j : ℝ) / 2 ^ ellExpO I := by
    funext j; push_cast; rfl
  refine ⟨fun i => (x i : ℚ) / 2 ^ ellExpO I, ?_, ?_, ?_⟩
  · simp only [apO, ← hI, ← hsdef, hx, Option.map_some]
  · rw [hpt, ← regionO_clearO]
    exact hmem
  · intro y hy
    rw [hpt]
    have h := hopt y (by rw [regionO_clearO]; exact hy)
    rw [GO_clearO, GO_clearO] at h
    have hIe : ((I.e : ℚ) : ℝ) = (objDen D : ℝ) * D.e := by
      show (((objDen D : ℚ) * D.e : ℚ) : ℝ) = _
      push_cast; rfl
    rw [hIe] at h
    have hob : (0 : ℝ) < objDen D := by exact_mod_cast objDen_pos D
    have : (objDen D : ℝ) * D.obj (fun j => (x j : ℝ) / 2 ^ ellExpO I) ≤ (objDen D : ℝ) * (D.obj y + D.e) := by
      linarith
    exact le_of_mul_le_mul_left this hob

end AdversarialBco.Unified.BLO
