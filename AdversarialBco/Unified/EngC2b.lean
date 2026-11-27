/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngC2a
public import AdversarialBco.Unified.BLOAp

@[expose] public section

/-!
# Piece C for BL-O, part C2 (b): the gaps E14 and the two calls

Bit/BLRoundC2.lean (E14 and the calls) for BL-O at `k`: the Hausdorff gap between P°'s regions `R⁻_s`, `R⁺_s` and
BL-O's regions `regO` of the test call and of line μ, and BL-O's two calls through ELL-O's contract `apSpecO` (in the
good position at P°'s radius, `ε' ≤ 1/2`, on a ball of the region) in place of `O3SpecQ`.
-/

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem kap_props (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 < (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k) ∧ (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k) ≤ 1 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  exact ⟨div_pos (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

theorem ePhi0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.ePhi d c.n k := by
  have := H.eb0; have := H.ek0; have := H.DP0; have := H.R0; unfold BudK.ePhi; positivity

theorem we0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.we d c.n k := by
  have := H.sett.eps_pos; have := NK.tp_pos d c.n k; unfold BudK.we; positivity

/-- `h ≤ R`, and the gap `h` covers the move `(1 - κ) R` of the first round. -/
theorem h_props (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.h d c.n k ≤ BudK.R d c.n k ∧ (1 - (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k)) * BudK.R d c.n k ≤ BudK.h d c.n k := by
  have hR1 := H.R_ge
  have hde := H.sett.de_pos
  have hde1 := H.det.rows.de_lt
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hwe := H.we0
  have hP := H.ePhi0
  have heh := H.bud.ePhi_le
  have hwr := H.wr0
  have hee' : (c.par.eps : ℝ) ≤ BudK.eps d c.n k + BudK.we d c.n k := by
    have := H.eps_relH.2; unfold BudK.we; nlinarith
  constructor
  · have h1 := H.bud.h_le
    have h2 : BudK.rmin d c.n k ≤ 1 := by
      unfold BudK.rmin
      rw [div_le_one (by positivity)]
      change (poK d c.n k).δe ^ 2 ≤ _
      have hde1 : (poK d c.n k).δe < 1 := H.det.rows.de_lt
      nlinarith
    linarith
  · have e1 : 1 - (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k) =
        ((c.par.eps : ℝ) - BudK.eps d c.n k) / (1 - BudK.eps d c.n k) := by
      have hne : (1 - BudK.eps d c.n k) ≠ 0 := by linarith
      field_simp; ring
    rw [e1]
    have h1 : ((c.par.eps : ℝ) - BudK.eps d c.n k) / (1 - BudK.eps d c.n k) ≤ 2 * BudK.we d c.n k := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : 0 ≤ BudK.R d c.n k * (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k) := by
      have := H.R0; have : 0 ≤ BudK.eh d c.n k := by linarith
      positivity
    have h3 : 0 ≤ 2 * BudK.R d c.n k ^ 3 * BudK.we d c.n k / BudK.de d c.n k ^ 2 := by have := H.R0; positivity
    unfold BudK.h
    nlinarith


/-- E14 for the test call: BL's test region lies in P°'s `R⁻_s`, every point of `R⁻_s` is within `h` of it, and it
holds a ball of BL's radius. -/
theorem gapT (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (r : RV d) :
    (∀ y ∈ (ctxO K c k ap).Rm π s, ∃ y' ∈ (regO K c (callTO c st r)),
        oNorm (y - y') ≤ BudK.h d c.n k) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callTO c st r).r : ℝ) ⊆
        (regO K c (callTO c st r))) ∧
      (regO K c (callTO c st r)) ⊆ (ctxO K c k ap).Rm π s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hR1 := H.R_ge
  have hRI := H.R_le_Rint
  have hinv := H.sett.inv
  have hfst := H.track.first
  set κ := (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k) with hκ
  by_cases hf : st.first = true
  · have hf' : ((ctxO K c k ap).st π s).first = true := hfst ▸ hf
    have hRm : (ctxO K c k ap).Rm π s = (ctxO K c k ap).Keps := by
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
      have : (1 - κ) * oNorm y ≤ (1 - κ) * BudK.R d c.n k := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    · have hr : ((callTO c st r).r : ℝ) = 1 - (c.par.eps : ℝ) := by
        rw [hcall]; simp [callO]
      have hy' : oNorm y ≤ 1 - (c.par.eps : ℝ) := by
        have h0 : oNorm (y - 0) ≤ ((callTO c st r).r : ℝ) := hy
        rwa [sub_zero, hr] at h0
      have hz : κ⁻¹ • y ∈ (ctxO K c k ap).Keps := by
        apply H.det.keps.2.2.1
        show oNorm (κ⁻¹ • y - 0) ≤ 1 - BudK.eps d c.n k
        rw [sub_zero, oNorm_smul, abs_of_pos (inv_pos.2 hκ0), hκ, inv_div, div_mul_eq_mul_div,
          div_le_iff₀ (by linarith)]
        have := oNorm_nonneg y
        nlinarith
      have hrows : y ∈ QKs K c (1 - c.par.eps)⁻¹ := by
        have := H.QK_of_keps hz
        rwa [← hκ, smul_smul, mul_inv_cancel₀ hκ0.ne', one_smul] at this
      refine (hreg y).2 ⟨hrows, ?_⟩
      linarith
  · have hf' : ((ctxO K c k ap).st π s).first = false := by
      rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctxO K c k ap).tau π (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨pt, hpt, hlev, hP, hb, hk, hrs⟩ := prev_round H.det hlt
    have hRm : (ctxO K c k ap).Rm π (s0 + 1) = {y | y ∈ (ctxO K c k ap).Keps ∧
        df2Phi ((ctxO K c k ap).st π (s0 + 1)).P ((ctxO K c k ap).st π (s0 + 1)).b
          ((ctxO K c k ap).st π (s0 + 1)).k y ≤
        ((ctxO K c k ap).p.c1 - (ctxO K c k ap).p.gam) * (ctxO K c k ap).p.rho} := by
      unfold Df2Ctx.Rm; rw [ite_eq_right (by rw [hf']; decide)]
    have hcall : callTO c st r = callO c (st.B * st.Bᵀ) st.b
        (LT c.par - st.k) (rB c.par / 2) (r.B * r.Bᵀ) (r.b - (c.par.eta / 2) • r.G)
        (rB c.par ^ 2 / (c.par.Ne * d * 8)) := by
      unfold callTO; rw [ite_eq_right hf]
    have herr : ∀ y, oNorm y ≤ BudK.R d c.n k → |df2Phi (cM (st.B * st.Bᵀ)) (cV st.b) st.k y -
        df2Phi ((ctxO K c k ap).st π (s0 + 1)).P ((ctxO K c k ap).st π (s0 + 1)).b
          ((ctxO K c k ap).st π (s0 + 1)).k y| ≤ BudK.ePhi d c.n k := by
      intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_s hy
    have hpsd : ∀ v, 0 ≤ v ⬝ᵥ (((ctxO K c k ap).st π (s0 + 1)).P *ᵥ v) :=
      fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd hinv.pd.posSemidef v
    have hgrad : ∀ z, oNorm z ≤ BudK.R d c.n k → oNorm (((ctxO K c k ap).st π (s0 + 1)).P *ᵥ z -
        ((ctxO K c k ap).st π (s0 + 1)).b) ≤ BudK.R d c.n k / BudK.de d c.n k ^ 2 := by
      intro z hz; rw [hP, hb]; exact H.det.grad_le (s := s0) (by rw [H.tau]; omega) hz
    have hD : 0 ≤ BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k := by
      have := H.ePhi0; have := H.bud.ePhi_le; have := H.wr0; linarith
    have hee' : (c.par.eps : ℝ) ≤ BudK.eps d c.n k + BudK.we d c.n k := by
      have := H.eps_relH.2; unfold BudK.we; nlinarith
    have hh : 2 * BudK.R d c.n k * ((BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k +
        BudK.R d c.n k / BudK.de d c.n k ^ 2 * BudK.R d c.n k * (1 - κ)) / 2) + (1 - κ) * BudK.R d c.n k ≤ BudK.h d c.n k := by
      have := gap_disp (BudK.R d c.n k) (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k)
        (BudK.R d c.n k / BudK.de d c.n k ^ 2 * BudK.R d c.n k * (1 - κ)) κ (BudK.eps d c.n k) (c.par.eps) (BudK.we d c.n k)
        (BudK.de d c.n k) (BudK.R d c.n k / BudK.de d c.n k ^ 2) H.R0 hD H.sett.de_pos he0 (by linarith) he hee' rfl rfl rfl
      unfold BudK.h; linarith
    obtain ⟨hA, hB⟩ := gap_pack (ctxO K c k ap).Keps
      (QKs K c (1 - c.par.eps)⁻¹)
      (regO K c (callTO c st r)) ((ctxO K c k ap).st π (s0 + 1)).P
      ((ctxO K c k ap).st π (s0 + 1)).b ((ctxO K c k ap).st π (s0 + 1)).k H.sett.P_sym hpsd
      (BudK.R d c.n k) κ (((ctxO K c k ap).p.c1 - (ctxO K c k ap).p.gam) * (ctxO K c k ap).p.rho)
      (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k) _ (BudK.R d c.n k / BudK.de d c.n k ^ 2) (BudK.h d c.n k) pt H.det.keps.1
      (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.QK_of_keps hy) hgrad hpt
      (by rw [hP, hb, hk]; exact hlev) hD rfl hh hhR (by linarith)
      (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.LT_lev.2 hy hΦ)
    have hgood := H.det.good (s0 + 1) H.sett.hs'
    rw [hRm] at hgood ⊢
    refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
    · obtain ⟨c', hc'⟩ := hB _ _ hgood.2.2.le hgood.2.1
      refine ⟨c', fun y hy => hc' ?_⟩
      have hr : ((callTO c st r).r : ℝ) ≤
          κ * ((ctxO K c k ap).st π (s0 + 1)).r / 2 := by
        rw [hcall, hrs]
        have e : κ * ((ctxO K c k ap).p.sb * (1 - (ctxO K c k ap).p.eps)) / 2 =
            (poK d c.n k).sb * (1 - (c.par.eps : ℝ)) / 2 := by
          rw [hκ]; change _ / (1 - (poK d c.n k).eps) * ((poK d c.n k).sb * (1 - (poK d c.n k).eps)) / 2 = _
          have : 1 - (poK d c.n k).eps ≠ 0 := by change 1 - BudK.eps d c.n k ≠ 0; linarith
          field_simp
        rw [e]
        simp only [callO, rB]
        push_cast
        have : ((c.par.sb : ℚ) : ℝ) ≤ (poK d c.n k).sb := by rw [H.par]; exact H.bud.enc.sb_le
        have : 0 ≤ 1 - (c.par.eps : ℝ) := by linarith
        nlinarith
      exact le_trans hy hr
    · rw [hcall] at hy
      exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.LT_lev.1 hy


/-- E14 for line μ, at a round that does not fire with P°'s test point `pt`: BL's region of line μ lies in P°'s
`R⁺_s`, every point of `R⁺_s` is within `h` of it, and it holds a ball of BL's radius. -/
theorem gapM (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxO K c k ap).Rm π s)
    (hXi : ¬ (ctxO K c k ap).Xi π s pt ≤ -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho)) :
    (∀ y ∈ (ctxO K c k ap).Rp π s, ∃ y' ∈ regO K c (callMO c c.n st ξ'
        (rvH orc c st ξ' ζ' ε f)), oNorm (y - y') ≤ BudK.h d c.n k) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).r : ℝ) ⊆
        (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)))) ∧
      (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f))) ⊆
        (ctxO K c k ap).Rp π s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hR1 := H.R_ge
  set κ := (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k) with hκ
  set r := rvH orc c st ξ' ζ' ε f with hr
  have hs := H.sett.hs'
  have hcall : callMO c c.n st ξ' r = callO c (r.B * r.Bᵀ) r.b
      (Lmu c.par - r.k) (rB c.par / 2) (r.B * r.Bᵀ) ((r.B * r.Bᵀ) *ᵥ wmuO c st ξ' r)
      (eBL c.par d c.n) := rfl
  have herr : ∀ y, oNorm y ≤ BudK.R d c.n k → |df2Phi (cM (r.B * r.Bᵀ)) (cV r.b) r.k y -
      df2Phi ((ctxO K c k ap).Pn π s) ((ctxO K c k ap).bn π s)
        ((ctxO K c k ap).kn π s) y| ≤ BudK.ePhi d c.n k := by
    intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_n O hy
  have hpsd : ∀ v, 0 ≤ v ⬝ᵥ ((ctxO K c k ap).Pn π s *ᵥ v) :=
    fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd (H.det.r1_le_tau hs).1.posSemidef v
  have hgrad : ∀ z, oNorm z ≤ BudK.R d c.n k → oNorm ((ctxO K c k ap).Pn π s *ᵥ z -
      (ctxO K c k ap).bn π s) ≤ BudK.R d c.n k / BudK.de d c.n k ^ 2 := fun z hz => H.det.grad_le hs hz
  have hD : 0 ≤ BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k := by
    have := H.ePhi0; have := H.bud.ePhi_le; have := H.wr0; linarith
  have hee' : (c.par.eps : ℝ) ≤ BudK.eps d c.n k + BudK.we d c.n k := by
    have := H.eps_relH.2; unfold BudK.we; nlinarith
  have hh : 2 * BudK.R d c.n k * ((BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k +
      BudK.R d c.n k / BudK.de d c.n k ^ 2 * BudK.R d c.n k * (1 - κ)) / 2) + (1 - κ) * BudK.R d c.n k ≤ BudK.h d c.n k := by
    have := gap_disp (BudK.R d c.n k) (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k)
      (BudK.R d c.n k / BudK.de d c.n k ^ 2 * BudK.R d c.n k * (1 - κ)) κ (BudK.eps d c.n k) (c.par.eps) (BudK.we d c.n k)
      (BudK.de d c.n k) (BudK.R d c.n k / BudK.de d c.n k ^ 2) H.R0 hD H.sett.de_pos he0 (by linarith) he hee' rfl rfl rfl
    unfold BudK.h; linarith
  have hP : ∀ u < s, (ctxO K c k ap).ProjOK π u := fun u hu => H.det.projOK (by rw [H.tau]; omega)
  have hlev := H.det.ib2_level hs hP hpt hXi
  have hlev' : (ctxO K c k ap).PhiN π s pt ≤
      (ctxO K c k ap).p.c1 * (ctxO K c k ap).p.rho - 2 := by
    have := H.rho_pos; have := H.det.gam
    have h0 : 0 ≤ (ctxO K c k ap).p.gam * (ctxO K c k ap).p.rho := by
      rw [this]; have : 0 < (ctxO K c k ap).p.rho := H.rho_pos; positivity
    linarith
  obtain ⟨hA, hB⟩ := gap_pack (ctxO K c k ap).Keps
    (QKs K c (1 - c.par.eps)⁻¹)
    (regO K c (callMO c c.n st ξ' r)) ((ctxO K c k ap).Pn π s)
    ((ctxO K c k ap).bn π s) ((ctxO K c k ap).kn π s) H.sett.Pn_sym hpsd
    (BudK.R d c.n k) κ ((ctxO K c k ap).p.c1 * (ctxO K c k ap).p.rho)
    (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k) _ (BudK.R d c.n k / BudK.de d c.n k ^ 2) (BudK.h d c.n k) pt H.det.keps.1
    (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.QK_of_keps hy) hgrad
    (H.det.Rm_sub_reg hs hpt).1 hlev' hD rfl hh hhR (by linarith)
    (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.Lmu_lev.2 hy hΦ)
  have hib := H.det.ib2 hs hP hpt hXi
  refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
  · obtain ⟨c', hc'⟩ := hB _ _ H.det.rad_pos.le (fun y hy => H.det.RmN_sub_Rp s (hib hy))
    refine ⟨c', fun y hy => hc' ?_⟩
    have hr' : ((callMO c c.n st ξ' r).r : ℝ) ≤
        κ * ((ctxO K c k ap).p.sb * (1 - (ctxO K c k ap).p.eps)) / 2 := by
      have e : κ * ((ctxO K c k ap).p.sb * (1 - (ctxO K c k ap).p.eps)) / 2 =
          (poK d c.n k).sb * (1 - (c.par.eps : ℝ)) / 2 := by
        rw [hκ]; change _ / (1 - (poK d c.n k).eps) * ((poK d c.n k).sb * (1 - (poK d c.n k).eps)) / 2 = _
        have : 1 - (poK d c.n k).eps ≠ 0 := by change 1 - BudK.eps d c.n k ≠ 0; linarith
        field_simp
      rw [e, hcall]
      simp only [callO, rB]
      push_cast
      have : ((c.par.sb : ℚ) : ℝ) ≤ (poK d c.n k).sb := by rw [H.par]; exact H.bud.enc.sb_le
      have : 0 ≤ 1 - (c.par.eps : ℝ) := by linarith
      nlinarith
    exact le_trans hy hr'
  · rw [hcall] at hy
    exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.Lmu_lev.1 hy


theorem par_pos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 < c.par.sb ∧ c.par.eps < 1 ∧ 0 < c.par.Ne ∧ (1 : ℚ) ≤ c.par.Rint ∧ 0 < c.par.R := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hsb : 0 < (poK d c.n k).sb := by
    have e := H.det.sb
    change (poK d c.n k).sb = (poK d c.n k).δe ^ 2 / ((poK d c.n k).R * ((poK d c.n k).R + 1)) at e
    have := H.sett.de_pos; have : 1 ≤ (poK d c.n k).R := H.R_ge
    rw [e]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 : |((c.par.sb : ℚ) : ℝ) / (poK d c.n k).sb - 1| ≤ BudK.tp d c.n k / 16 := by
      rw [H.par]; exact H.bud.enc.sb_rel
    have h := (abs_le.1 h0).1
    have htp := NK.tp_small d c.n k
    have h1 : 0 < (c.par.sb : ℝ) / (poK d c.n k).sb := by linarith
    have h2 : (0 : ℝ) < c.par.sb := by
      have := mul_pos h1 hsb; rwa [div_mul_cancel₀ _ hsb.ne'] at this
    exact_mod_cast h2
  · have : (c.par.eps : ℝ) < 1 := by linarith
    exact_mod_cast this
  · have h1 : (c.par.Ne : ℝ) = BudK.Ne d c.n k := by rw [H.par]; exact H.bud.enc.Ne_eq
    have h2 := H.bud.enc.de_eq
    have hde : 0 < BudK.de d c.n k := H.sett.de_pos
    rw [h2] at hde
    have : (0 : ℝ) < (c.par.Ne : ℝ) := by rw [h1]; exact one_div_pos.1 hde
    exact_mod_cast this
  · have h := H.R_le_Rint
    have h1 := H.R_ge
    have : (1 : ℝ) ≤ (c.par.Rint : ℝ) := by
      have e : ((c.par.Rint : ℕ) : ℝ) = (c.par.Rint : ℝ) := rfl
      linarith
    exact_mod_cast this
  · have : BudK.R d c.n k ≤ ((c.par.R : ℚ) : ℝ) := by rw [H.par]; exact H.bud.enc.R_le
    have := H.R_ge
    have : (0 : ℝ) < c.par.R := by linarith
    exact_mod_cast this

/-- BL's `P'_+ = B'_+ B'_+ᵀ` is positive definite: `B'_+ = (I + H^B) P° A°` with `|H^B| < 1`. -/
theorem Pp_posDef (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s) :
    (((rvH orc c st ξ' ζ' ε f).B * (rvH orc c st ξ' ζ' ε f).Bᵀ).map ((↑) : ℚ → ℝ)).PosDef := by
  change (cM ((rvH orc c st ξ' ζ' ε f).B * (rvH orc c st ξ' ζ' ε f).Bᵀ)).PosDef
  rw [cM_mul, cM_transpose]
  apply posDef_mul_transpose
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  rw [hB0, Matrix.det_mul, Matrix.det_mul]
  have h1 : (1 + H0).det ≠ 0 := by
    apply det_one_add_ne
    have := H.bud.hTr_le (s + 1) H.hs
    have := H.bud.hb_le
    linarith
  have h2 : ((ctxO K c k ap).Pn π s).det * ((ctxO K c k ap).An π s).det ≠ 0 := by
    have h := congrArg Matrix.det H.sett.PnAn_inv
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  exact mul_ne_zero h1 h2

theorem epsQ (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ c.par.eps ∧ c.par.eps ≤ 1 / 2 := by
  refine ⟨by have := H.eps'_pos.le; exact_mod_cast this, ?_⟩
  have h := H.eps'_le
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num] at h
  exact_mod_cast h

theorem gram_psd (B : Matrix (Fin d) (Fin d) ℚ) : ((B * Bᵀ).map ((↑) : ℚ → ℝ)).PosSemidef := by
  change (cM (B * Bᵀ)).PosSemidef
  rw [cM_mul, cM_transpose, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- (O3) at BL's test call: it returns a point of its region within its accuracy of the least objective. -/
theorem testCall (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    :
    ∃ p', apO orc c (callTO c st (rvH orc c st ξ' ζ' ε f)) = some p' ∧
      cV p' ∈ (regO K c (callTO c st (rvH orc c st ξ' ζ' ε f))) ∧
      ∀ x ∈ (regO K c (callTO c st (rvH orc c st ξ' ζ' ε f))),
        (callTO c st (rvH orc c st ξ' ζ' ε f)).obj (cV p') ≤
          (callTO c st (rvH orc c st ξ' ζ' ε f)).obj x +
            ((callTO c st (rvH orc c st ξ' ζ' ε f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapT (rvH orc c st ξ' ζ' ε f)).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have hP : ((callTO c st (rvH orc c st ξ' ζ' ε f)).P.map ((↑) : ℚ → ℝ)).PosDef := by
    unfold callTO; split <;> exact H.Pp_posDef O
  have hH : ((callTO c st (rvH orc c st ξ' ζ' ε f)).H.map ((↑) : ℚ → ℝ)).PosSemidef := by
    unfold callTO; split
    · show ((0 : Matrix (Fin d) (Fin d) ℚ).map ((↑) : ℚ → ℝ)).PosSemidef
      rw [Matrix.map_zero _ (by simp)]; exact Matrix.PosSemidef.zero
    · exact gram_psd st.B
  have hR : (1 : ℚ) ≤ (callTO c st (rvH orc c st ξ' ζ' ε f)).R := by
    unfold callTO; split <;> exact hRint
  have hr : (0 : ℚ) < (callTO c st (rvH orc c st ξ' ζ' ε f)).r := by
    unfold callTO; split
    · show 0 < 1 - c.par.eps; linarith
    · show 0 < c.par.sb * (1 - c.par.eps) / 2
      have : 0 < 1 - c.par.eps := by linarith
      positivity
  have he : (0 : ℚ) < (callTO c st (rvH orc c st ξ' ζ' ε f)).e := by
    unfold callTO; split
    · show 0 < (1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8)
      have : 0 < 1 - c.par.eps := by linarith
      positivity
    · show 0 < (c.par.sb * (1 - c.par.eps)) ^ 2 / (c.par.Ne * d * 8)
      have : 0 < 1 - c.par.eps := by linarith
      positivity
  obtain ⟨heps0, heps⟩ := H.epsQ
  exact apSpecO d K orc c (poK d c.n k).R _ c' H.hd H.frame H.goodPos H.one_le_R H.R_le_par heps0 heps hR hr he hP
    hH hball

/-- (O3) at BL's call of line μ, at a round that does not fire with P°'s test point `pt`. -/
theorem muCall (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctxO K c k ap).Rm π s)
    (hXi : ¬ (ctxO K c k ap).Xi π s pt ≤ -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho)) :
    ∃ μ', apO orc c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)) = some μ' ∧
      cV μ' ∈ (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f))) ∧
      ∀ x ∈ (regO K c (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f))),
        (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).obj (cV μ') ≤
          (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).obj x +
            ((callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapM O hpt hXi).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hn : (0 : ℚ) < c.n := by exact_mod_cast H.hn
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have hr : (0 : ℚ) < (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).r := by
    show 0 < c.par.sb * (1 - c.par.eps) / 2
    have : 0 < 1 - c.par.eps := by linarith
    positivity
  have he : (0 : ℚ) < (callMO c c.n st ξ' (rvH orc c st ξ' ζ' ε f)).e := by
    show 0 < 1 / (c.par.Ne * (128 * (c.n : ℚ) ^ 2 * c.par.R ^ 2 * d))
    positivity
  obtain ⟨heps0, heps⟩ := H.epsQ
  exact apSpecO d K orc c (poK d c.n k).R _ c' H.hd H.frame H.goodPos H.one_le_R H.R_le_par heps0 heps hRint hr he
    (H.Pp_posDef O) (H.Pp_posDef O).posSemidef hball


end AdversarialBco.Unified.Eng.RCHypO
