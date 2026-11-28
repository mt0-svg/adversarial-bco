/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC2a

@[expose] public section

/-!
# Piece C for BL-OW, part C2 (b): the gaps E14 and the two calls

Unified/EngC2b.lean for BL-OW at BUD-W: the Hausdorff gap between P°'s regions `R⁻_s`, `R⁺_s` on the weighted path and
BL-OW's regions `regO` of the test call and of line μ, and BL-OW's two calls through ELL-O's contract `apSpecO`.

The caps are read at the level. The gradient of P°'s quadratic is at most
`R/δ_0² ≤ R/δ_e²` (`grad_cap`), so the gap `h` of BUD-W, written at the level `δ_e`, covers it. The ball the gap
leaves in BL-OW's region has radius `κ s_b(δ_0)(1 - ε)/2 = s_b(δ_0)(1 - ε')/2`, against BL-OW's radius
`s'_b (1 - ε')/2` with `s'_b ≤ s_b(δ_e) ≤ s_b(δ_0)` (`sb_le0`).
-/

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.EngC (callTO fireO wmuO callMO regO regO_callO regO_callO_k)
open AdversarialBco.Unified.Eng.RCHypO (gram_psd)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem kap_props (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    0 < (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps) ∧ (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps) ≤ 1 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  exact ⟨div_pos (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

theorem ePhi0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).ePhi := (H.R.ePhi_bd).1

theorem we0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).we := (H.R.wr_we).2.2.1

theorem eps_we (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (c.par.eps : ℝ) ≤ (rW d c.n δ).eps + (rW d c.n δ).we := by
  have h := H.eps_relH.2
  have e : (rW d c.n δ).eps * (1 + (rW d c.n δ).tp / 16) = (rW d c.n δ).eps + (rW d c.n δ).we := by
    unfold RegW.we; ring
  linarith

/-- `h ≤ R`, and the gap `h` covers the move `(1 - κ) R` of the first round. -/
theorem h_props (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).h ≤ (rW d c.n δ).R ∧
      (1 - (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps)) * (rW d c.n δ).R ≤ (rW d c.n δ).h := by
  have hR1 := H.R_ge
  have hde := H.deL_pos
  have hde1 := H.deL_le_one
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hwe := H.we0
  have hP := H.ePhi0
  have heh := H.R.ePhi_le_eh
  have hwr := H.wr0
  have hR0 : 0 ≤ (rW d c.n δ).R := by linarith
  have hee' := H.eps_we
  constructor
  · have h1 := H.R.h_le_rmin
    have h2 : (rW d c.n δ).rmin ≤ 1 := by
      unfold RegW.rmin
      have hden : 0 < 2 * (rW d c.n δ).R * ((rW d c.n δ).R + 1) :=
        mul_pos (mul_pos two_pos (by linarith)) (by linarith)
      rw [div_le_one hden]
      nlinarith [mul_le_mul hde1 hde1 hde.le zero_le_one]
    linarith
  · have e1 : 1 - (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps) =
        ((c.par.eps : ℝ) - (rW d c.n δ).eps) / (1 - (rW d c.n δ).eps) := by
      have hne : (1 - (rW d c.n δ).eps) ≠ 0 := by linarith
      field_simp; ring
    rw [e1]
    have h1 : ((c.par.eps : ℝ) - (rW d c.n δ).eps) / (1 - (rW d c.n δ).eps) ≤ 2 * (rW d c.n δ).we := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : 0 ≤ (rW d c.n δ).R * ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr) := by
      have : 0 ≤ (rW d c.n δ).eh := by linarith
      exact mul_nonneg hR0 (by linarith)
    have h3 : 0 ≤ 2 * (rW d c.n δ).R ^ 3 * (rW d c.n δ).we / (rW d c.n δ).de ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hR0 3)) hwe) (sq_nonneg _)
    unfold RegW.h
    nlinarith

/-- The drop `D = e_Φ + ê + 8 w_ρ` of the gap is nonnegative. -/
theorem D0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    0 ≤ (rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr := by
  have := H.ePhi0; have := H.R.ePhi_le_eh; have := H.wr0; linarith

/-- The gap at the level: `2R((D + E₁)/2) + (1 - κ) R ≤ h` with `E₁ = (R/δ_e²) R (1 - κ)`. -/
theorem gap_h (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    2 * (rW d c.n δ).R * (((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr +
      (rW d c.n δ).R / (rW d c.n δ).de ^ 2 * (rW d c.n δ).R *
        (1 - (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps))) / 2) +
      (1 - (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps)) * (rW d c.n δ).R ≤ (rW d c.n δ).h := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have := gap_disp (rW d c.n δ).R ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr)
    ((rW d c.n δ).R / (rW d c.n δ).de ^ 2 * (rW d c.n δ).R * (1 - (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps)))
    ((1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps)) (rW d c.n δ).eps (c.par.eps) (rW d c.n δ).we
    (rW d c.n δ).de ((rW d c.n δ).R / (rW d c.n δ).de ^ 2) H.R0 H.D0 H.deL_pos he0 (by linarith) he H.eps_we
    rfl rfl rfl
  unfold RegW.h; linarith

/-- E14 for the test call: BL's test region lies in P°'s `R⁻_s`, every point of `R⁻_s` is within `h` of it, and it
holds a ball of BL's radius. -/
theorem gapT (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (r : RV d) :
    (∀ y ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s, ∃ y' ∈ (regO K c (callTO c st r)),
        oNorm (y - y') ≤ (rW d c.n δ).h) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callTO c st r).r : ℝ) ⊆ (regO K c (callTO c st r))) ∧
      (regO K c (callTO c st r)) ⊆ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hh := H.gap_h
  have hR1 := H.R_ge
  have hRI := H.R_le_Rint
  have hinv := H.sett.inv
  have hfst := H.track.first
  set κ := (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps) with hκ
  by_cases hf : st.first = true
  · have hf' : ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).first = true := hfst ▸ hf
    have hRm : (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s = (ctxOW K c δ ap).Keps := by
      unfold Df2Ctx.Rm; rw [ite_eq_left hf']
    have hcall : callTO c st r = callO c 0 0 0 (1 - c.par.eps)
        (r.B * r.Bᵀ) (r.b - (c.par.eta / 2) • r.G) ((1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8)) := by
      unfold callTO; rw [ite_eq_left hf]
    have hreg : ∀ y, y ∈ (regO K c (callTO c st r)) ↔
        y ∈ QKs K c (1 - c.par.eps)⁻¹ ∧ oNorm y ≤ ((c.par.Rint : ℕ) : ℝ) := by
      intro y
      rw [hcall, regO_callO]
      have e : df2Phi (cM (0 : Matrix (Fin d) (Fin d) ℚ)) (cV 0) 0 y = 0 := by
        unfold df2Phi; rw [cV_zero]; simp [cM]
      rw [e]
      push_cast
      simp only [le_refl, true_and]
    rw [hRm]
    refine ⟨fun y hy => ⟨κ • y, (hreg _).2 ⟨H.QK_of_keps hy, ?_⟩, ?_⟩, ⟨0, fun y hy => ?_⟩,
      fun y hy => H.keps_of_QK ((hreg y).1 hy).1⟩
    · rw [oNorm_smul, abs_of_pos hκ0]
      have := H.keps_norm hy
      have := oNorm_nonneg y
      nlinarith
    · have e : y - κ • y = (1 - κ) • y := by rw [sub_smul, one_smul]
      rw [e, oNorm_smul, abs_of_nonneg (by linarith)]
      have := H.keps_norm hy
      have : (1 - κ) * oNorm y ≤ (1 - κ) * (rW d c.n δ).R := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    · have hr : ((callTO c st r).r : ℝ) = 1 - (c.par.eps : ℝ) := by
        rw [hcall]; simp [callO]
      have hy' : oNorm y ≤ 1 - (c.par.eps : ℝ) := by
        have h0 : oNorm (y - 0) ≤ ((callTO c st r).r : ℝ) := hy
        rwa [sub_zero, hr] at h0
      have hz : κ⁻¹ • y ∈ (ctxOW K c δ ap).Keps := by
        apply H.det.keps.2.2.1
        show oNorm (κ⁻¹ • y - 0) ≤ 1 - (rW d c.n δ).eps
        rw [sub_zero, oNorm_smul, abs_of_pos (inv_pos.2 hκ0), hκ, inv_div, div_mul_eq_mul_div,
          div_le_iff₀ (by linarith)]
        have := oNorm_nonneg y
        nlinarith
      have hrows : y ∈ QKs K c (1 - c.par.eps)⁻¹ := by
        have := H.QK_of_keps hz
        rwa [← hκ, smul_smul, mul_inv_cancel₀ hκ0.ne', one_smul] at this
      refine (hreg y).2 ⟨hrows, ?_⟩
      linarith
  · have hf' : ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).first = false := by
      rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctxOW K c δ ap).tau (pwOW K c δ ap π) (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨pt, hpt, hlev, hP, hb, hk, hrs⟩ := prev_roundW H.det hlt
    have hRm : (ctxOW K c δ ap).Rm (pwOW K c δ ap π) (s0 + 1) = {y | y ∈ (ctxOW K c δ ap).Keps ∧
        df2Phi ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).P
          ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).b
          ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).k y ≤
        ((ctxOW K c δ ap).p.c1 - (ctxOW K c δ ap).p.gam) * (ctxOW K c δ ap).p.rho} := by
      unfold Df2Ctx.Rm; rw [ite_eq_right (by rw [hf']; decide)]
    have hcall : callTO c st r = callO c (st.B * st.Bᵀ) st.b
        (LT c.par - st.k) (rB c.par / 2) (r.B * r.Bᵀ) (r.b - (c.par.eta / 2) • r.G)
        (rB c.par ^ 2 / (c.par.Ne * d * 8)) := by
      unfold callTO; rw [ite_eq_right hf]
    have herr : ∀ y, oNorm y ≤ (rW d c.n δ).R → |df2Phi (cM (st.B * st.Bᵀ)) (cV st.b) st.k y -
        df2Phi ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).P
          ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).b
          ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).k y| ≤ (rW d c.n δ).ePhi := by
      intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_s hy
    have hpsd : ∀ v, 0 ≤ v ⬝ᵥ (((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).P *ᵥ v) :=
      fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd hinv.pd.posSemidef v
    have hgrad : ∀ z, oNorm z ≤ (rW d c.n δ).R →
        oNorm (((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).P *ᵥ z -
          ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).b) ≤ (rW d c.n δ).R / (rW d c.n δ).de ^ 2 := by
      intro z hz; rw [hP, hb]
      exact (H.det.grad_le (s := s0) (by rw [H.tau]; omega) hz).trans H.grad_cap
    obtain ⟨hA, hB⟩ := gap_pack (ctxOW K c δ ap).Keps
      (QKs K c (1 - c.par.eps)⁻¹)
      (regO K c (callTO c st r)) ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).P
      ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).b ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).k
      H.sett.P_sym hpsd
      (rW d c.n δ).R κ (((ctxOW K c δ ap).p.c1 - (ctxOW K c δ ap).p.gam) * (ctxOW K c δ ap).p.rho)
      ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr) _ ((rW d c.n δ).R / (rW d c.n δ).de ^ 2)
      (rW d c.n δ).h pt H.det.keps.1
      (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.QK_of_keps hy) hgrad hpt
      (by rw [hP, hb, hk]; exact hlev) H.D0 rfl hh hhR (by linarith)
      (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.LT_lev.2 hy hΦ)
    have hgood := H.det.good (s0 + 1) H.sett.hs'
    rw [hRm] at hgood ⊢
    refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
    · obtain ⟨c', hc'⟩ := hB _ _ hgood.2.2.le hgood.2.1
      refine ⟨c', fun y hy => hc' ?_⟩
      have hr : ((callTO c st r).r : ℝ) ≤
          κ * ((ctxOW K c δ ap).st (pwOW K c δ ap π) (s0 + 1)).r / 2 := by
        rw [hcall, hrs]
        have e : κ * ((ctxOW K c δ ap).p.sb * (1 - (ctxOW K c δ ap).p.eps)) / 2 =
            (poW d c.n δ).sb * (1 - (c.par.eps : ℝ)) / 2 := by
          rw [hκ]; change _ / (1 - (poW d c.n δ).eps) * ((poW d c.n δ).sb * (1 - (poW d c.n δ).eps)) / 2 = _
          have : 1 - (poW d c.n δ).eps ≠ 0 := by change 1 - (rW d c.n δ).eps ≠ 0; linarith
          field_simp
        rw [e]
        simp only [callO, rB]
        push_cast
        have := H.sb_le0
        have : 0 ≤ 1 - (c.par.eps : ℝ) := by linarith
        nlinarith
      exact le_trans hy hr
    · rw [hcall] at hy
      exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.LT_lev.1 hy

/-- E14 for line μ, at a round that does not fire with P°'s test point `pt`: BL's region of line μ lies in P°'s
`R⁺_s`, every point of `R⁺_s` is within `h` of it, and it holds a ball of BL's radius. -/
theorem gapM (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s)
    (hXi : ¬ (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s pt ≤
      -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho)) :
    (∀ y ∈ (ctxOW K c δ ap).Rp (pwOW K c δ ap π) s, ∃ y' ∈ regO K c (callMO c c.n st ξ'
        (rvHW orc c δ st ξ' ζ' ε f)), oNorm (y - y') ≤ (rW d c.n δ).h) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).r : ℝ) ⊆
        (regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)))) ∧
      (regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f))) ⊆
        (ctxOW K c δ ap).Rp (pwOW K c δ ap π) s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hh := H.gap_h
  have hR1 := H.R_ge
  set κ := (1 - (c.par.eps : ℝ)) / (1 - (rW d c.n δ).eps) with hκ
  set r := rvHW orc c δ st ξ' ζ' ε f with hr
  have hs := H.sett.hs'
  have hcall : callMO c c.n st ξ' r = callO c (r.B * r.Bᵀ) r.b
      (Lmu c.par - r.k) (rB c.par / 2) (r.B * r.Bᵀ) ((r.B * r.Bᵀ) *ᵥ wmuO c st ξ' r)
      (eBL c.par d c.n) := rfl
  have herr : ∀ y, oNorm y ≤ (rW d c.n δ).R → |df2Phi (cM (r.B * r.Bᵀ)) (cV r.b) r.k y -
      df2Phi ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) ((ctxOW K c δ ap).bn (pwOW K c δ ap π) s)
        ((ctxOW K c δ ap).kn (pwOW K c δ ap π) s) y| ≤ (rW d c.n δ).ePhi := by
    intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_n O hy
  have hpsd : ∀ v, 0 ≤ v ⬝ᵥ ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s *ᵥ v) :=
    fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd (H.det.r1_le_tau hs).1.posSemidef v
  have hgrad : ∀ z, oNorm z ≤ (rW d c.n δ).R → oNorm ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s *ᵥ z -
      (ctxOW K c δ ap).bn (pwOW K c δ ap π) s) ≤ (rW d c.n δ).R / (rW d c.n δ).de ^ 2 :=
    fun z hz => (H.det.grad_le hs hz).trans H.grad_cap
  have hP : ∀ u < s, (ctxOW K c δ ap).ProjOK (pwOW K c δ ap π) u :=
    fun u hu => H.det.projOK (by rw [H.tau]; omega)
  have hlev := H.det.ib2_level hs hP hpt hXi
  have hlev' : (ctxOW K c δ ap).PhiN (pwOW K c δ ap π) s pt ≤
      (ctxOW K c δ ap).p.c1 * (ctxOW K c δ ap).p.rho - 2 := by
    have hρ : 0 < (ctxOW K c δ ap).p.rho := H.rho_pos
    have hg := H.det.gam
    have h0 : 0 ≤ (ctxOW K c δ ap).p.gam * (ctxOW K c δ ap).p.rho := by
      rw [hg]; positivity
    linarith
  obtain ⟨hA, hB⟩ := gap_pack (ctxOW K c δ ap).Keps
    (QKs K c (1 - c.par.eps)⁻¹)
    (regO K c (callMO c c.n st ξ' r)) ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s)
    ((ctxOW K c δ ap).bn (pwOW K c δ ap π) s) ((ctxOW K c δ ap).kn (pwOW K c δ ap π) s) H.sett.Pn_sym hpsd
    (rW d c.n δ).R κ ((ctxOW K c δ ap).p.c1 * (ctxOW K c δ ap).p.rho)
    ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr) _ ((rW d c.n δ).R / (rW d c.n δ).de ^ 2)
    (rW d c.n δ).h pt H.det.keps.1
    (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.QK_of_keps hy) hgrad
    (H.det.Rm_sub_reg hs hpt).1 hlev' H.D0 rfl hh hhR (by linarith)
    (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.Lmu_lev.2 hy hΦ)
  have hib := H.det.ib2 hs hP hpt hXi
  refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
  · obtain ⟨c', hc'⟩ := hB _ _ H.det.rad_pos.le (fun y hy => H.det.RmN_sub_Rp s (hib hy))
    refine ⟨c', fun y hy => hc' ?_⟩
    have hr' : ((callMO c c.n st ξ' r).r : ℝ) ≤
        κ * ((ctxOW K c δ ap).p.sb * (1 - (ctxOW K c δ ap).p.eps)) / 2 := by
      have e : κ * ((ctxOW K c δ ap).p.sb * (1 - (ctxOW K c δ ap).p.eps)) / 2 =
          (poW d c.n δ).sb * (1 - (c.par.eps : ℝ)) / 2 := by
        rw [hκ]; change _ / (1 - (poW d c.n δ).eps) * ((poW d c.n δ).sb * (1 - (poW d c.n δ).eps)) / 2 = _
        have : 1 - (poW d c.n δ).eps ≠ 0 := by change 1 - (rW d c.n δ).eps ≠ 0; linarith
        field_simp
      rw [e, hcall]
      simp only [callO, rB]
      push_cast
      have := H.sb_le0
      have : 0 ≤ 1 - (c.par.eps : ℝ) := by linarith
      nlinarith
    exact le_trans hy hr'
  · rw [hcall] at hy
    exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.Lmu_lev.1 hy

theorem par_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    0 < c.par.sb ∧ c.par.eps < 1 ∧ 0 < c.par.Ne ∧ (1 : ℚ) ≤ c.par.Rint ∧ 0 < c.par.R := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hR1 := H.R_ge
  have hde := H.deL_pos
  have hsbL : 0 < (rW d c.n δ).de ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) :=
    div_pos (pow_pos hde 2) (mul_pos (by linarith) (by linarith))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 : |((c.par.sb : ℚ) : ℝ) / ((rW d c.n δ).de ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1))) - 1| ≤
        (rW d c.n δ).tp / 16 := by
      rw [H.par]; exact H.enc.sb_rel
    have h := (abs_le.1 h0).1
    have htp := H.tp_small
    have h1 : 0 < ((c.par.sb : ℚ) : ℝ) / ((rW d c.n δ).de ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1))) := by
      linarith
    have h2 : (0 : ℝ) < c.par.sb := by
      have := mul_pos h1 hsbL; rwa [div_mul_cancel₀ _ hsbL.ne'] at this
    exact_mod_cast h2
  · have : (c.par.eps : ℝ) < 1 := by linarith
    exact_mod_cast this
  · have h1 : (c.par.Ne : ℝ) = (rW d c.n δ).Ne := by rw [H.par]; exact H.enc.Ne_eq
    have h2 : 0 < (rW d c.n δ).Ne := (H.R.pos).2.2.1
    have : (0 : ℝ) < (c.par.Ne : ℝ) := by rw [h1]; exact h2
    exact_mod_cast this
  · have h := H.R_le_Rint
    have : (1 : ℝ) ≤ (c.par.Rint : ℝ) := by
      have e : ((c.par.Rint : ℕ) : ℝ) = (c.par.Rint : ℝ) := rfl
      linarith
    exact_mod_cast this
  · have : (rW d c.n δ).R ≤ ((c.par.R : ℚ) : ℝ) := by rw [H.par]; exact H.enc.R_le
    have : (0 : ℝ) < c.par.R := by linarith
    exact_mod_cast this

/-- BL's `P'_+ = B'_+ B'_+ᵀ` is positive definite: `B'_+ = (I + H^B) P° A°` with `|H^B| < 1`. -/
theorem Pp_posDef (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    (((rvHW orc c δ st ξ' ζ' ε f).B * (rvHW orc c δ st ξ' ζ' ε f).Bᵀ).map ((↑) : ℚ → ℝ)).PosDef := by
  change (cM ((rvHW orc c δ st ξ' ζ' ε f).B * (rvHW orc c δ st ξ' ζ' ε f).Bᵀ)).PosDef
  rw [cM_mul, cM_transpose]
  apply posDef_mul_transpose
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  rw [hB0, Matrix.det_mul, Matrix.det_mul]
  have h1 : (1 + H0).det ≠ 0 := by
    apply det_one_add_ne
    have := H.R.hTr_le (s + 1) (by show ((s + 1 : ℕ) : ℝ) ≤ (c.n : ℝ); exact_mod_cast H.hs)
    have := H.hb_le
    linarith
  have h2 : ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s).det * ((ctxOW K c δ ap).An (pwOW K c δ ap π) s).det ≠ 0 := by
    have h := congrArg Matrix.det H.sett.PnAn_inv
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  exact mul_ne_zero h1 h2

theorem epsQ (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ c.par.eps ∧ c.par.eps ≤ 1 / 2 := by
  refine ⟨by have := H.eps'_pos.le; exact_mod_cast this, ?_⟩
  have h := H.eps'_le
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num] at h
  exact_mod_cast h

/-- (O3) at BL's test call: it returns a point of its region within its accuracy of the least objective. -/
theorem testCall (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    ∃ p', apO orc c (callTO c st (rvHW orc c δ st ξ' ζ' ε f)) = some p' ∧
      cV p' ∈ (regO K c (callTO c st (rvHW orc c δ st ξ' ζ' ε f))) ∧
      ∀ x ∈ (regO K c (callTO c st (rvHW orc c δ st ξ' ζ' ε f))),
        (callTO c st (rvHW orc c δ st ξ' ζ' ε f)).obj (cV p') ≤
          (callTO c st (rvHW orc c δ st ξ' ζ' ε f)).obj x +
            ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapT (rvHW orc c δ st ξ' ζ' ε f)).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have hP : ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).P.map ((↑) : ℚ → ℝ)).PosDef := by
    unfold callTO; split <;> exact H.Pp_posDef O
  have hH : ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).H.map ((↑) : ℚ → ℝ)).PosSemidef := by
    unfold callTO; split
    · show ((0 : Matrix (Fin d) (Fin d) ℚ).map ((↑) : ℚ → ℝ)).PosSemidef
      rw [Matrix.map_zero _ (by simp)]; exact Matrix.PosSemidef.zero
    · exact gram_psd st.B
  have hR : (1 : ℚ) ≤ (callTO c st (rvHW orc c δ st ξ' ζ' ε f)).R := by
    unfold callTO; split <;> exact hRint
  have hr : (0 : ℚ) < (callTO c st (rvHW orc c δ st ξ' ζ' ε f)).r := by
    unfold callTO; split
    · show 0 < 1 - c.par.eps; linarith
    · show 0 < c.par.sb * (1 - c.par.eps) / 2
      have : 0 < 1 - c.par.eps := by linarith
      positivity
  have he : (0 : ℚ) < (callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e := by
    unfold callTO; split
    · show 0 < (1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8)
      have : 0 < 1 - c.par.eps := by linarith
      positivity
    · show 0 < (c.par.sb * (1 - c.par.eps)) ^ 2 / (c.par.Ne * d * 8)
      have : 0 < 1 - c.par.eps := by linarith
      positivity
  obtain ⟨heps0, heps⟩ := H.epsQ
  exact apSpecO d K orc c (poW d c.n δ).R _ c' H.hd H.frame H.goodPos H.one_le_R H.R_le_par heps0 heps hR hr he hP
    hH hball

/-- (O3) at BL's call of line μ, at a round that does not fire with P°'s test point `pt`. -/
theorem muCall (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s)
    (hXi : ¬ (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s pt ≤
      -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho)) :
    ∃ μ', apO orc c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)) = some μ' ∧
      cV μ' ∈ (regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f))) ∧
      ∀ x ∈ (regO K c (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f))),
        (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).obj (cV μ') ≤
          (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).obj x +
            ((callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapM O hpt hXi).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hn : (0 : ℚ) < c.n := by exact_mod_cast H.hn
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have hr : (0 : ℚ) < (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).r := by
    show 0 < c.par.sb * (1 - c.par.eps) / 2
    have : 0 < 1 - c.par.eps := by linarith
    positivity
  have he : (0 : ℚ) < (callMO c c.n st ξ' (rvHW orc c δ st ξ' ζ' ε f)).e := by
    show 0 < 1 / (c.par.Ne * (128 * (c.n : ℚ) ^ 2 * c.par.R ^ 2 * d))
    positivity
  obtain ⟨heps0, heps⟩ := H.epsQ
  exact apSpecO d K orc c (poW d c.n δ).R _ c' H.hd H.frame H.goodPos H.one_le_R H.R_le_par heps0 heps hRint hr he
    (H.Pp_posDef O) (H.Pp_posDef O).posSemidef hball

end AdversarialBco.UW.Eng.RCHypOW
