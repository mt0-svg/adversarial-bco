/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.DetRound

@[expose] public section

/-!
# DET at T4U with sure ranges: Poly/Df2DetRegion.lean on `DetHypW`
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

namespace DetHypW

variable {d : ℕ} {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

/-! ### Signs of the levels -/

theorem Bn_nonneg (H : DetHypW c π m ρ) : 0 ≤ bnW c.p d c.n ρ.u := by
  have hu0 : 0 ≤ ρ.u := by linarith [H.u_ge]
  have := H.rows.pos_lam; have := H.rows.pos_eps; have : 0 < c.p.Le := by linarith [H.one_le_Le]
  unfold bnW; positivity

theorem b1_nonneg (H : DetHypW c π m ρ) : 0 ≤ b1W c.p d c.n ρ.u := by
  have hu0 : 0 ≤ ρ.u := by linarith [H.u_ge]
  have := H.rows.pos_lam; have := H.rows.pos_eps; unfold b1W; positivity

theorem devP_nonneg (H : DetHypW c π m ρ) : 0 ≤ devPW c.p d c.n ρ.u := by
  have := H.Bn_nonneg; have := H.rows.pos_lam; have := H.rows.pos_eta; have := H.one_le_Le
  unfold devPW; rw [H.kap]; positivity

theorem devK_nonneg (H : DetHypW c π m ρ) : 0 ≤ devKW c.p d c.n ρ.u := by
  have := H.Bn_nonneg; have := H.b1_nonneg; have := H.rows.pos_lam; have := H.one_le_Le
  unfold devKW; positivity

theorem sY_nonneg (H : DetHypW c π m ρ) : 0 ≤ sYW c.n ρ.y0 ρ.δc :=
  le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) H.evY

theorem stab_nonneg (H : DetHypW c π m ρ) : 0 ≤ stabW c.p c.n ρ := by
  have := H.sY_nonneg; have := H.k0_pos; have := H.b0_ge
  unfold stabW; positivity

theorem pri_nonneg (H : DetHypW c π m ρ) : 0 ≤ df2Pri c.p := by
  have := H.rows.pos_sig2; unfold df2Pri; positivity

theorem pri_le_rho (H : DetHypW c π m ρ) : df2Pri c.p ≤ c.p.rho := by
  have := H.r19ow; have := H.rows.pos_eta; have := H.rows.pos_lam; have := H.one_le_Le
  have := H.stab_nonneg; have := H.devK_nonneg
  have : 0 ≤ (d : ℝ) * c.p.Le / c.p.lam := by positivity
  have : 0 ≤ c.p.eta * devKW c.p d c.n ρ.u := by positivity
  linarith

theorem rho_nonneg (H : DetHypW c π m ρ) : 0 ≤ c.p.rho := H.rows.pos_rho.le

/-! ### `K_ε` -/

theorem keps (H : DetHypW c π m ρ) :
    Convex ℝ c.Keps ∧ IsClosed c.Keps ∧ oBall 0 (1 - c.p.eps) ⊆ c.Keps ∧ c.Keps ⊆ oBall 0 c.p.R := by
  obtain ⟨hconv, hcl, hball, hR, -⟩ := H.body
  exact keps_basic c.Kt c.p.eps c.p.R hconv hcl hball hR H.rows.pos_eps.le (by have := H.heps; linarith)

theorem norm_le_of_keps (H : DetHypW c π m ρ) {y : Fin d → ℝ} (hy : y ∈ c.Keps) : oNorm y ≤ c.p.R := by
  have := H.keps.2.2.2 hy; simpa [oBall] using this

/-! ### The quadratics -/

theorem phi_zero (H : DetHypW c π m ρ) (y : Fin d → ℝ) :
    c.Phi π 0 y = 1 / 2 * c.p.sig2⁻¹ * (y ⬝ᵥ y) := by
  have _ := H
  show df2Phi (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 0 y = _
  unfold df2Phi; rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, zero_dotProduct]; ring

/-- `Φ'` of round `s ≤ τ` is `Φ₀ + Ω̂_{s+1}`. -/
theorem PhiN_eq (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.PhiN π s y = c.Phi π 0 y + c.OmH π (s + 1) y := by
  have hI := H.stInv_le_tau s hs
  have h : c.PhiN π s y = c.Phi π s y +
      c.cc π s / 2 * df2Sq (vecMulVec (c.u π s) (c.u π s) - (c.st π s).P) (y - (c.st π s).mu) :=
    phi_update _ hI.pd.isHermitian _ _ _ _ _ _
  rw [h, hI.phi y, Df2Ctx.OmH_succ]
  unfold Df2Ctx.shh
  rw [sq_smul, Df2Ctx.cc_eq]
  ring

theorem phi_eq (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.Phi π s y = c.Phi π 0 y + c.OmH π s y := (H.stInv_le_tau s hs).phi y

/-- For `s < τ`, `Φ_{s+1}` is the quadratic computed in round `s`, and `μ_{s+1}` lies in `R⁺` of round `s`. -/
theorem succ_of_lt (H : DetHypW c π m ρ) {s : ℕ} (hs : s < c.tau π m) :
    (∀ y, c.Phi π (s + 1) y = c.PhiN π s y) ∧ (c.st π (s + 1)).mu ∈ c.Rp π s := by
  have hI := H.stInv_le_tau s hs.le
  obtain ⟨-, -, -, hcont⟩ := H.cond_lt_tau s hs
  obtain ⟨pt, mu', -, -, hmc, -, hst⟩ := c.st_succ_of_cont π s hI.run hcont
  refine ⟨fun y => by unfold Df2Ctx.Phi; rw [hst]; rfl, ?_⟩
  have hsp := (H.hap s (c.Rp π s) ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) c.p.R (c.Pn π s) (c.wmu π s)
    (c.eM π s)).2
  unfold Df2Ctx.mcall at hmc
  rw [hmc] at hsp
  rcases hsp with h | ⟨μ, hμ, hμQ, -⟩
  · cases h
  · rw [hst, Option.some.inj hμ]; exact hμQ

/-! ### Lemma DQ, Lemma MON, Proposition INC2 on the run -/

theorem le_rS_iff (H : DetHypW c π m ρ) (q : ℝ) : q ≤ c.rS ↔ c.p.lam ^ 2 * q ≤ 1 / (2 * c.p.Le) := by
  have hl := H.rows.pos_lam; have hL := H.one_le_Le
  unfold Df2Ctx.rS
  rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

theorem SD_succ (H : DetHypW c π m ρ) (t : ℕ) (y : Fin d → ℝ) : y ∈ c.SD π (t + 1) ↔ y ∈ c.SS π t := by
  unfold Df2Ctx.SD df2S Df2Ctx.SS
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h u hu
    have := h (u + 1) (by omega) (by omega)
    rw [Df2Ctx.PD_succ, Df2Ctx.muD_succ, H.le_rS_iff] at this
    exact this
  · intro h s hs1 hs2
    obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
    rw [Df2Ctx.PD_succ, Df2Ctx.muD_succ, H.le_rS_iff]
    exact h u (by omega)

theorem SD_anti (u t : ℕ) (hut : u ≤ t) : c.SD π t ⊆ c.SD π u := fun _ hy s h1 h2 => hy s h1 (h2.trans hut)

theorem OmT_nonneg (H : DetHypW c π m ρ) {t : ℕ} (ht : t ≤ c.tau π m + 1) (y : Fin d → ℝ) :
    ∀ u ≤ t, 0 ≤ c.OmT π u y := by
  intro u hu
  unfold Df2Ctx.OmT
  have := H.kap_pos
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun v hv => sq_nonneg_of_psd (H.sHess_psd (by
    have := Finset.mem_range.1 hv; omega)) _

theorem OmTc_nonneg (H : DetHypW c π m ρ) (t : ℕ) (y : Fin d → ℝ) : 0 ≤ c.OmTc π (c.tau π m + 1) t y :=
  H.OmT_nonneg (le_refl _) y _ (min_le_right _ _)

theorem OmTc_mono (H : DetHypW c π m ρ) (u t : ℕ) (y : Fin d → ℝ) (hut : u ≤ t) :
    c.OmTc π (c.tau π m + 1) u y ≤ c.OmTc π (c.tau π m + 1) t y := by
  unfold Df2Ctx.OmTc Df2Ctx.OmT
  have := H.kap_pos
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_min_right _ hut))
  intro v hv _
  exact sq_nonneg_of_psd (H.sHess_psd (by
    have := Finset.mem_range.1 hv; have := min_le_right t (c.tau π m + 1); omega)) _

/-- Lemma DQ: `|Ω̂_t - Ω_t| ≤ dev'` on `S_t ∩ B_R` for `t ≤ τ + 1` (DF2 indexing). -/
theorem dq_at (H : DetHypW c π m ρ) {t : ℕ} (ht : t ≤ c.tau π m + 1) {y : Fin d → ℝ} (hy : y ∈ c.SD π t)
    (hR : oNorm y ≤ c.p.R) : |c.OmH π t y - c.OmT π t y| ≤ devPW c.p d c.n ρ.u := by
  rcases t with _ | s
  · simp [Df2Ctx.OmH, Df2Ctx.OmT, H.devP_nonneg]
  have hs : s ≤ c.tau π m := by omega
  have hdq := H.evDQ s hs y hR ((H.SD_succ s y).1 hy)
  have e : c.OmH π (s + 1) y - c.OmT π (s + 1) y = c.p.eta * c.p.kap / 2 * c.GG π s y := by
    unfold Df2Ctx.OmH Df2Ctx.OmT Df2Ctx.GG
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sq_sub]
  rw [e, abs_mul, abs_of_nonneg (by have := H.kap_pos; positivity)]
  have hl := H.rows.pos_lam; have hL := H.one_le_Le
  calc c.p.eta * c.p.kap / 2 * |c.GG π s y| ≤ c.p.eta * c.p.kap / 2 * (bnW c.p d c.n ρ.u / (c.p.Le * c.p.lam ^ 2)) :=
        mul_le_mul_of_nonneg_left hdq (by have := H.kap_pos; positivity)
    _ = devPW c.p d c.n ρ.u := by unfold devPW; field_simp

/-- Lemma MON on the run (DF2 indexing, `u ≤ t ≤ τ + 1`). -/
theorem mon_at (H : DetHypW c π m ρ) {u t : ℕ} (hut : u ≤ t) (ht : t ≤ c.tau π m + 1) {y : Fin d → ℝ}
    (hy : y ∈ c.SD π t) (hR : oNorm y ≤ c.p.R) :
    c.Phi π 0 y + c.OmH π u y ≤ c.Phi π 0 y + c.OmH π t y + 2 * devPW c.p d c.n ρ.u := by
  refine H.mon d (c.Phi π 0) (c.OmTc π (c.tau π m + 1)) (c.OmH π) (c.SD π) (oBall 0 c.p.R) (c.tau π m + 1)
    (devPW c.p d c.n ρ.u) (fun u t h => SD_anti u t h) (fun u t y h => H.OmTc_mono u t y h) ?_ u t hut ht y
    ⟨hy, by simpa [oBall] using hR⟩
  rintro t' ht' y' ⟨hy', hR'⟩
  have : min t' (c.tau π m + 1) = t' := min_eq_left ht'
  unfold Df2Ctx.OmTc; rw [this]
  exact H.dq_at ht' hy' (by simpa [oBall] using hR')

/-- The row of the inclusion: `8 (c₁ ρ + 2 dev') < r` (R21). -/
theorem inc_row (H : DetHypW c π m ρ) : 8 * (c.p.c1 * c.p.rho + 2 * devPW c.p d c.n ρ.u) < c.rS := by
  have hl := H.rows.pos_lam; have hL := H.one_le_Le
  have h := H.r21w
  unfold thnW at h
  unfold Df2Ctx.rS devPW
  rw [lt_div_iff₀ (by positivity), H.kap]
  have e : 8 * (c.p.c1 * c.p.rho + 2 * (c.p.eta * (1 / 4) * bnW c.p d c.n ρ.u / (2 * c.p.Le * c.p.lam ^ 2))) *
      (2 * c.p.Le * c.p.lam ^ 2) = 16 * c.p.c1 * c.p.rho * c.p.Le * c.p.lam ^ 2 + 2 * (2 * c.p.eta * bnW c.p d c.n ρ.u) := by
    field_simp; ring
  rw [e]; exact h

/-- Proposition INC2 on the run: for `t ≤ τ`, `μ_t` is in the region of round `t`, and every point of it is within
`8 (c₁ ρ + 2 dev')` of `μ_v` in `P_v`, `v ≤ t`. -/
theorem inc2_at (H : DetHypW c π m ρ) {t : ℕ} (ht : t ≤ c.tau π m) :
    (c.st π t).mu ∈ c.Reg π t ∧ ∀ y ∈ c.Reg π t, ∀ v ≤ t,
      df2Sq (c.st π v).P (y - (c.st π v).mu) ≤ 8 * (c.p.c1 * c.p.rho + 2 * devPW c.p d c.n ρ.u) := by
  set τ := c.tau π m with hτ
  obtain ⟨hconv, hcl, -, hsub⟩ := H.keps
  have hI0 := H.stInv_le_tau 0 (Nat.zero_le _)
  have hmu0 : (c.st π 0).mu = 0 := rfl
  have hsig := H.rows.pos_sig2
  have h := H.inc2 d c.Keps (oBall 0 c.p.R) (c.muD π) (c.PD π) (c.Phi π 0) (c.OmTc π (τ + 1)) (c.OmH π) (τ + 1)
    c.p.c1 c.p.rho (devPW c.p d c.n ρ.u) (df2Pri c.p) c.rS hconv hcl hsub ?pd ?quad ?self ?nn ?pri ?mu1 ?zero ?proj
    (fun t y => H.OmTc_nonneg t y) (fun u t y h => H.OmTc_mono u t y h) ?dq H.devP_nonneg H.rho_nonneg
    (by rw [H.c1]; norm_num) H.pri_le_rho H.inc_row (t + 1) (by omega) (by omega)
  case pd =>
    intro s h1 h2
    obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
    rw [Df2Ctx.PD_succ]; exact (H.stInv_le_tau u (by omega)).pd
  case quad =>
    intro t ht
    refine ⟨(c.st π t).k, -(c.st π t).b, funext fun y => ?_⟩
    rw [Df2Ctx.PD_succ, ← Df2Ctx.phi_quad, ← H.phi_eq (by omega)]
    rfl
  case self =>
    intro t h1 h2
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    rw [Df2Ctx.muD_succ, Nat.add_sub_cancel, Df2Ctx.OmH_succ_self]
  case nn =>
    intro y; rw [H.phi_zero]; have := dot_self_nonneg y; have := inv_pos.2 hsig; positivity
  case pri =>
    intro y hy
    have hR := H.norm_le_of_keps hy
    have hyy : y ⬝ᵥ y ≤ c.p.R ^ 2 := by
      have h0 := dot_self_nonneg y
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hR 2
      rwa [Real.sq_sqrt h0] at this
    rw [H.phi_zero, Df2Ctx.PD_succ, Df2Ctx.muD_succ, hmu0, sub_zero, Df2Ctx.st_zero]
    show _ ∧ df2Sq (c.p.sig2⁻¹ • 1) y ≤ _
    rw [sq_smul, sq_one]
    unfold df2Pri
    have e : c.p.R ^ 2 / (2 * c.p.sig2) = 1 / 2 * c.p.sig2⁻¹ * c.p.R ^ 2 := by field_simp
    have hsi : 0 < c.p.sig2⁻¹ := inv_pos.2 hsig
    rw [e]
    constructor
    · exact mul_le_mul_of_nonneg_left hyy (by positivity)
    · nlinarith
  case mu1 => rw [Df2Ctx.muD_succ]; exact hI0.mu
  case zero =>
    rw [Df2Ctx.muD_succ, hmu0, H.phi_zero]; simp [Df2Ctx.OmH]
  case proj =>
    intro u h1 h2 _
    obtain ⟨s, rfl⟩ : ∃ s, u = s + 2 := ⟨u - 2, by omega⟩
    have hs : s < τ := by omega
    obtain ⟨-, hmem⟩ := H.succ_of_lt hs
    rw [show s + 2 = (s + 1) + 1 by ring, Df2Ctx.muD_succ]
    refine ⟨hmem.1, ?_⟩
    show c.Phi π 0 _ + c.OmH π (s + 1 + 1 - 1) _ ≤ _
    rw [Nat.add_sub_cancel, ← H.PhiN_eq hs.le]
    exact hmem.2
  case dq =>
    rintro t ht y ⟨hy, hR⟩
    unfold Df2Ctx.OmTc; rw [min_eq_left ht]
    exact H.dq_at ht hy (by simpa [oBall] using hR)
  obtain ⟨ha, hb⟩ := h
  have hreg : df2R c.Keps (fun t y => c.Phi π 0 y + c.OmH π t y) (c.p.c1 * c.p.rho) (t + 1) = c.Reg π t := by
    ext y
    simp only [df2R, Df2Ctx.Reg, Set.mem_ofPred_eq, Nat.add_sub_cancel, H.phi_eq ht]
  rw [hreg, Df2Ctx.muD_succ] at ha
  refine ⟨ha, fun y hy v hv => ?_⟩
  rw [← hreg] at hy
  have := hb y hy (v + 1) (by omega) (by omega)
  rwa [Df2Ctx.PD_succ, Df2Ctx.muD_succ] at this

/-- The region of a round `t ≤ τ` lies in the past ellipsoids and in `B_R`. -/
theorem reg_sub (H : DetHypW c π m ρ) {t : ℕ} (ht : t ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.Reg π t) :
    y ∈ c.SS π t ∧ oNorm y ≤ c.p.R := by
  refine ⟨fun v hv => ?_, H.norm_le_of_keps hy.1⟩
  rw [← H.le_rS_iff]
  exact ((H.inc2_at ht).2 y hy v hv).trans H.inc_row.le

end DetHypW

end AdversarialBco.UW
