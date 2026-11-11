/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetGuard

@[expose] public section

/-!
# DET, the accuracy of the three calls

The induction on the run, rounds `s ≤ τ`: the test call is accurate (its ball lies in
`R⁻_s`: `B(0, 1 - ε) ⊆ K_ε` at the first round, the ball of Lemma D.17 of the round before after it); Lemma D.17 at a
round where the statistic is above `-θ ρ` (`Φ'(pt) ≤ (c₁ - γ) ρ - 2` from the online Newton inequality with defects,
the gradient bound and IB-geo) puts the ball of line μ in `R⁻_{s+1} ⊆ R⁺_s`, so line μ is accurate; and a round `τ`
that does not fire continues the epoch.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- A round from a running mode continues the epoch when it passes the four guards, the test call returns a point
where the statistic is above `-θ ρ` and line μ returns a point. -/
theorem cont_of (s : ℕ) (h : c.mode π s = .run (c.st π s)) (h1 : ¬ c.GdA π s) (h2 : ¬ c.GdT π s)
    (h3 : ¬ c.GdZ π s) {pt : Fin d → ℝ} (htc : c.tcall π s = some pt)
    (h4 : ¬ c.Xi π s pt ≤ -(c.p.theta * c.p.rho)) (h5 : ¬ c.GdW π s) {mu' : Fin d → ℝ}
    (hmc : c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) = some mu') : c.cont π s := by
  refine ⟨c.stNext π s pt mu', ?_, rfl⟩
  unfold GdA GdT GdZ GdW at *
  rw [c.mode_succ_of_run π s h, nextAP_unfold, ite_of_neg h1, ite_of_neg h2, ite_of_neg h3, htc]
  simp only
  rw [ite_of_neg h4, ite_of_neg h5, hmc]

end Df2Ctx

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem eT_pos (H : DetHyp c δ π m) : 0 < c.eT := by
  have := H.rows.pos_rho
  unfold Df2Ctx.eT; rw [H.alpha]
  exact lt_min one_pos (by positivity)

theorem eM_pos (H : DetHyp c δ π m) (s : ℕ) : 0 < c.eM π s := by
  have hn : (0 : ℝ) < c.n := by exact_mod_cast H.hn
  unfold Df2Ctx.eM
  exact one_div_pos.2 (mul_pos (mul_pos (by norm_num) (pow_pos hn 2)) (lt_of_lt_of_le one_pos (le_max_left _ _)))

theorem sb_props (H : DetHyp c δ π m) :
    0 < c.p.sb ∧ c.p.sb ≤ 1 ∧
      c.p.sb * (c.p.R + (1 - c.p.eps)) ≤
        min (2 / (2 * (c.p.R / c.p.δe ^ 2))) (Real.sqrt (2 / c.p.δe⁻¹)) := by
  rw [H.sb]
  exact sb_arith c.p.δe c.p.R (1 - c.p.eps) H.rows.pos_de H.rows.de_lt H.rows.one_le_R
    (by linarith [H.heps]) (by linarith [H.rows.pos_eps])

theorem rad_pos (H : DetHyp c δ π m) : 0 < c.p.sb * (1 - c.p.eps) :=
  mul_pos H.sb_props.1 (by linarith [H.heps])

theorem Pn_le (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - c.Pn π s).PosSemidef := by
  obtain ⟨-, -, h3c, h3d⟩ := H.c3_le_tau hs
  exact psd_trans h3d h3c

theorem phi0_le (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : oNorm y ≤ c.p.R) :
    0 ≤ c.Phi π 0 y ∧ c.Phi π 0 y ≤ df2Pri c.p := by
  have hs := H.rows.pos_sig2
  have h0 := dot_self_nonneg y
  have hyy : y ⬝ᵥ y ≤ c.p.R ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy 2
    rwa [Real.sq_sqrt h0] at this
  rw [H.phi_zero]
  refine ⟨by positivity, ?_⟩
  have e2 : df2Pri c.p = 1 / 2 * c.p.sig2⁻¹ * c.p.R ^ 2 := by unfold df2Pri; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left hyy (by positivity)
/-- The test call of a round `s ≤ τ` whose ball lies in `R⁻_s` is accurate. -/
theorem accT (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m)
    (hb : oBall (c.st π s).ctr (c.st π s).r ⊆ c.Rm π s) (hr : 0 < (c.st π s).r) : c.AccT π s := by
  obtain ⟨hcv, hcl, hsub⟩ := H.Rm_props hs
  obtain ⟨μ, h1, h2, h3⟩ := (H.hap _ _ _ _ _ _ _).1 hcv hcl hr hb hsub (H.r1_le_tau hs).1 H.eT_pos
  exact ⟨μ, h1, h2, h3⟩

/-- Line μ of a round `s ≤ τ` whose ball lies in `R⁻_{s+1}` is accurate. -/
theorem accM (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {pt : Fin d → ℝ}
    (hb : oBall ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) ⊆ c.RmN π s) : c.AccM π s pt := by
  obtain ⟨hcv, hcl, hsub⟩ := H.Rp_props hs
  obtain ⟨μ, h1, h2, h3⟩ := (H.hap _ _ _ _ _ _ _).1 hcv hcl H.rad_pos (hb.trans (H.RmN_sub_Rp s)) hsub
    (H.r1_le_tau hs).1 (H.eM_pos s)
  exact ⟨μ, h1, h2, h3⟩

/-- Lemma D.17 (i): at a round `s ≤ τ` whose earlier points of line μ are accurate, a point of `R⁻_s` where the
statistic is above `-θ ρ` has `Φ'(pt) ≤ (c₁ - γ) ρ - 2` (row R24b). -/
theorem ib2_level (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hP : ∀ u < s, c.ProjOK π u)
    {pt : Fin d → ℝ} (hpt : pt ∈ c.Rm π s) (hXi : ¬ c.Xi π s pt ≤ -(c.p.theta * c.p.rho)) :
    c.PhiN π s pt ≤ (c.p.c1 - c.p.gam) * c.p.rho - 2 := by
  obtain ⟨hSS, hR⟩ := H.reg_sub hs (H.Rm_sub_reg hs hpt)
  have hη := H.rows.pos_eta
  rw [not_le, H.xi_eq hs] at hXi
  have h2 := (abs_le.1 (H.sand_iv hs hSS hR)).2
  have h2' := mul_le_mul_of_nonneg_left h2 hη.le
  rw [mul_sub] at h2'
  have h3 := H.q_part1 hs hSS hR
  have h4 := H.ons hs hP hpt
  have h5 := (abs_le.1 (H.dq_at (t := s + 1) (by omega) ((H.SD_succ s pt).2 hSS) hR)).2
  have h6 := H.PhiN_eq hs pt
  obtain ⟨h00, h01⟩ := H.phi0_le hR
  have r := H.rows.r24b
  have := H.pri_nonneg
  linarith

/-- Lemma D.17 (iii): the ball of line μ lies in `R⁻_{s+1}`. -/
theorem ib2 (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hP : ∀ u < s, c.ProjOK π u)
    {pt : Fin d → ℝ} (hpt : pt ∈ c.Rm π s) (hXi : ¬ c.Xi π s pt ≤ -(c.p.theta * c.p.rho)) :
    oBall ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) ⊆ c.RmN π s := by
  have hreg := H.Rm_sub_reg hs hpt
  have hR := (H.reg_sub hs hreg).2
  have hde := H.rows.pos_de
  have hlev := H.ib2_level hs hP hpt hXi
  obtain ⟨hpd, -, -, -⟩ := H.r1_le_tau hs
  have hnorm : ∀ v, |df2Sq (c.Pn π s) v| ≤ c.p.δe⁻¹ * (v ⬝ᵥ v) := fun v => by
    have h0 := sq_nonneg_of_psd hpd.posSemidef v
    have h1 := sq_le_of_psd (H.Pn_le hs) v
    rw [sq_smul, sq_one] at h1
    have := mul_nonneg (inv_nonneg.2 hde.le) (dot_self_nonneg v)
    exact abs_le.2 ⟨by linarith, h1⟩
  obtain ⟨hs0, hs1, hsr⟩ := H.sb_props
  have hRp : 0 < c.p.R / c.p.δe ^ 2 := by have := H.rows.one_le_R; positivity
  obtain ⟨hball, hphi⟩ := ib_geo c.Keps (1 - c.p.eps) c.p.R (c.Pn π s) (c.bn π s) (c.kn π s)
    ((c.p.c1 - c.p.gam) * c.p.rho) 2 (c.p.R / c.p.δe ^ 2) c.p.δe⁻¹ c.p.sb pt H.keps.1 H.keps.2.2.1 H.keps.2.2.2
    hpd.isHermitian (by linarith [H.heps]) two_pos hRp (inv_pos.2 hde) hreg.1 hlev (H.grad_le hs hR) hnorm
    hs0 hs1 hsr
  exact fun x hx => ⟨hball hx, hphi x hx⟩

/-- The modes of the rounds up to `τ` run. -/
theorem mode_run (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : c.mode π s = .run (c.st π s) :=
  c.mode_run_of_cont π (c.tau π m) (fun u hu => (H.cond_lt_tau u hu).2.2.2) s hs

/-- The induction: for `s ≤ τ`, the points of line μ before `s` are accurate and the ball of the
test call of round `s` lies in `R⁻_s`. -/
theorem good (H : DetHyp c δ π m) : ∀ s ≤ c.tau π m,
    (∀ u < s, c.ProjOK π u) ∧ oBall (c.st π s).ctr (c.st π s).r ⊆ c.Rm π s ∧ 0 < (c.st π s).r := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨fun u hu => absurd hu (Nat.not_lt_zero _), ?_, ?_⟩
    · show oBall 0 (1 - c.p.eps) ⊆ c.Keps
      exact H.keps.2.2.1
    · show 0 < 1 - c.p.eps
      linarith [H.heps]
  | succ s ih =>
    intro hs
    obtain ⟨hP, hb, hr⟩ := ih (by omega)
    have hlt : s < c.tau π m := by omega
    obtain ⟨pt, mu', htc, hXi, hmc, -, hst⟩ :=
      c.st_succ_of_cont π s (H.mode_run (by omega)) (H.cond_lt_tau s hlt).2.2.2
    obtain ⟨pt0, htc0, hpt0, -⟩ := H.accT (by omega) hb hr
    rw [htc] at htc0
    cases htc0
    have hib := H.ib2 (by omega) hP hpt0 hXi
    obtain ⟨mu0, hmc0, -, hmin⟩ := H.accM (by omega) hib
    rw [hmc] at hmc0
    cases hmc0
    refine ⟨fun u hu => ?_, ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | h
      · exact hP u h
      · subst h
        intro x hx
        rw [hst]
        exact hmin x hx
    · rw [H.Rm_succ hlt, hst]
      exact hib
    · rw [hst]
      exact H.rad_pos

theorem projOK (H : DetHyp c δ π m) {u : ℕ} (hu : u < c.tau π m) : c.ProjOK π u :=
  (H.good (c.tau π m) le_rfl).1 u hu

theorem accT_le (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : c.AccT π s :=
  H.accT hs (H.good s hs).2.1 (H.good s hs).2.2

/-- Condition 4 at `τ`: a round `τ` that does not fire continues the epoch. -/
theorem cont_tau (H : DetHyp c δ π m) (hf : ¬ c.fire π (c.tau π m)) : c.cont π (c.tau π m) := by
  have hm := H.mode_run (le_refl (c.tau π m))
  obtain ⟨pt, htc, hpt, -⟩ := H.accT_le (le_refl (c.tau π m))
  have hA := H.not_gdA (le_refl _)
  have hT := H.not_gdT (le_refl _)
  have hZ := H.not_gdZ (le_refl _)
  have hXi : ¬ c.Xi π (c.tau π m) pt ≤ -(c.p.theta * c.p.rho) := fun h =>
    hf ((c.fire_iff π _ hm).2 ⟨hA, hT, hZ, pt, htc, h⟩)
  have hib := H.ib2 (le_refl _) (fun u hu => H.projOK hu) hpt hXi
  obtain ⟨mu', hmc, -, -⟩ := H.accM (le_refl _) hib
  exact c.cont_of π _ hm hA hT hZ htc hXi (H.not_gdW (le_refl _)) hmc

end DetHyp

end AdversarialBco.Poly
