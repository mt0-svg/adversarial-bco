/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetMain

@[expose] public section

/-!
# DET, the states up to the stopping time

`StInv s`: what holds of the state of round `s ≤ τ` by the conditions before `τ` alone (conditions (a),
(b), (d) of the epoch, with Lemma D.2), and the forms of `P`, `b`, `Φ`, `Ĝ`, `l` as sums over the rounds. `SIat s`:
the facts of `Df2SIFacts` at the state of round `s`.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- The invariants of the state of round `s`. -/
structure StInv (s : ℕ) : Prop where
  run : c.mode π s = .run (c.st π s)
  pd : (c.st π s).P.PosDef
  SP : (c.st π s).S * (c.st π s).P = 1
  AA : (c.st π s).A * (c.st π s).Aᵀ = (c.st π s).S
  detA : (c.st π s).A.det ≠ 0
  pbl : ((c.st π s).P - (1 / 2 : ℝ) • c.PBar π s).PosSemidef
  pbh : ((2 : ℝ) • c.PBar π s - (c.st π s).P).PosSemidef
  pbd : ((1 / 2 : ℝ) • c.PBar π s - c.p.δe • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef
  pb2 : (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (2 : ℝ) • c.PBar π s).PosSemidef
  pb0 : (c.PBar π s - c.PBar π 0).PosSemidef
  mu : (c.st π s).mu ∈ c.Keps
  first : (c.st π s).first = true ↔ s = 0
  phi : ∀ y, c.Phi π s y = c.Phi π 0 y + c.OmH π s y
  G : (c.st π s).G = ∑ u ∈ Finset.range s, c.ghat π u
  l : (c.st π s).l = ∑ u ∈ Finset.range s, c.ghat π u ⬝ᵥ (c.st π u).mu
  Pf : (c.st π s).P = (c.st π 0).P + (c.p.eta * c.p.kap) • ∑ u ∈ Finset.range s, c.shh π u
  bf : (c.st π s).b = (c.p.eta * c.p.kap) • ∑ u ∈ Finset.range s, c.shh π u *ᵥ (c.st π u).mu

/-- The facts of `Df2SIFacts` at the state of round `s`. -/
structure SIat (s : ℕ) : Prop where
  ext_convex : ConvexOn ℝ Set.univ (df2Ext c.p c.Kt (π.g s))
  ext_nonneg : ∀ x, 0 ≤ df2Ext c.p c.Kt (π.g s) x
  ext_lip : ∀ x y, |df2Ext c.p c.Kt (π.g s) x - df2Ext c.p c.Kt (π.g s) y| ≤ 8 / c.p.eps * ‖x - y‖
  ext_eq : ∀ y ∈ c.Keps, df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 y) = π.g s (WithLp.toLp 2 y)
  c2 : ContDiff ℝ 2 (c.surr π s)
  convex : ConvexOn ℝ Set.univ (c.surr π s)
  le_ext : ∀ z, c.surr π s z ≤ df2Ext c.p c.Kt (π.g s) z
  bound : ∀ z ∈ c.Keps, -(10 / (c.p.lam * c.p.eps)) ≤ c.surr π s (WithLp.toLp 2 z) ∧
    c.surr π s (WithLp.toLp 2 z) ≤ 1
  lower : (∫ z, df2Ext c.p c.Kt (π.g s)
      (WithLp.toLp 2 (c.st π s).mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A z) ∂(stdGaussian (E d))) -
      c.surr π s (WithLp.toLp 2 (c.st π s).mu) ≤
    2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace + 2 * c.p.δe * d / c.p.lam
  hess2 : ∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (c.surr π s) z) v| ≤
    c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) *
      df2Sq ((c.st π s).A * (c.st π s).Aᵀ)⁻¹ v
  hess1 : ∀ (z : E d) (v : Fin d → ℝ), |df2Sq (df2HessM (c.surr π s) z) v| ≤
    c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (d / c.p.δe) * (v ⬝ᵥ v)
  sc : ∀ x y : Fin d → ℝ, c.p.lam ^ 2 * df2Sq ((c.st π s).A * (c.st π s).Aᵀ)⁻¹ (x - y) ≤ 1 / c.p.Le →
    ((2 : ℝ) • df2HessM (c.surr π s) (WithLp.toLp 2 y) + c.p.δe • ((c.st π s).A * (c.st π s).Aᵀ)⁻¹ -
      df2HessM (c.surr π s) (WithLp.toLp 2 x)).PosSemidef
  qlower : ∀ y : Fin d → ℝ,
    c.p.lam ^ 2 * df2Sq ((c.st π s).A * (c.st π s).Aᵀ)⁻¹ (y - (c.st π s).mu) ≤ 1 / c.p.Le →
    c.surr π s (WithLp.toLp 2 (c.st π s).mu) - c.surr π s (WithLp.toLp 2 y) ≤
      c.sGrad π s ⬝ᵥ ((c.st π s).mu - y) - 1 / 4 * df2Sq (c.sHess π s) (y - (c.st π s).mu) +
        c.p.δe / c.p.lam ^ 2

end Df2Ctx

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- `Df2SIFacts` at the state of a round before the horizon. -/
theorem si (H : DetBase c δ π m) {s : ℕ} (hs : s < m) (hok : c.StOK π s) : c.SIat π s := by
  have h := H.SI d c.n δ c.Kt (π.g s) H.hd H.hn H.hδ0 H.hδ1 (by rw [← H.hp]; exact H.heps)
    (by rw [← H.hp]; exact H.body) (H.adm s hs)
  rw [← H.hp] at h
  obtain ⟨⟨e1, e2, e3, e4⟩, h2⟩ := h
  obtain ⟨⟨s1, s2, s3⟩, s4, s5, s6, s7, s8, s9⟩ := h2 (c.st π s).mu (c.st π s).A hok
  exact ⟨e1, e2, e3, e4, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩

end DetBase

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

theorem st_zero : c.st π 0 = df2Init c.p d := rfl

theorem PBar_zero : c.PBar π 0 = c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := rfl

theorem PBar_succ (s : ℕ) : c.PBar π (s + 1) = c.PBar π s + (c.p.eta * c.p.kap) • c.sHess π s := rfl

theorem cc_eq (s : ℕ) : c.cc π s = c.p.eta * c.p.kap * (c.p.lam * c.p.k0 * c.Y π s) := by
  unfold cc; ring

/-- `P' = P + η κ ŝ''`. -/
theorem Pn_eq (s : ℕ) : c.Pn π s = (c.st π s).P + (c.p.eta * c.p.kap) • c.shh π s := by
  unfold Pn shh aa
  rw [cc_eq]
  module

/-- `b' = b + η κ ŝ'' μ`. -/
theorem bn_eq (s : ℕ) : c.bn π s = (c.st π s).b + (c.p.eta * c.p.kap) • (c.shh π s *ᵥ (c.st π s).mu) := by
  unfold bn shh
  rw [smul_mulVec, sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul, cc_eq]
  module

end Df2Ctx

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- (A5) from the invariants: `A Aᵀ = Σ = P⁻¹`, `P ≥ ½ P̄ ≥ ½ P̄₀ = I/(2σ²)`, `δ I ≤ P ≤ I/δ`. -/
theorem stOK_of_stInv (H : DetBase c δ π m) {s : ℕ} (hI : c.StInv π s) : c.StOK π s := by
  have hs0 := H.rows.pos_sig2
  have hSinv : ((c.st π s).A * (c.st π s).Aᵀ)⁻¹ = (c.st π s).P := by
    rw [hI.AA]; exact Matrix.inv_eq_right_inv hI.SP
  unfold Df2Ctx.StOK Df2StateOK
  refine ⟨hI.mu, hI.detA, ?_, ?_, ?_⟩
  · have h2 : ((1 / 2 : ℝ) • c.PBar π s - (1 / 2 : ℝ) • c.PBar π 0).PosSemidef := by
      rw [← smul_sub]; exact hI.pb0.smul (by norm_num)
    have hlow := psd_trans hI.pbl h2
    rw [Df2Ctx.PBar_zero, smul_smul] at hlow
    have hpos : (((1 / 2 : ℝ) * c.p.sig2⁻¹) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
      Matrix.PosDef.one.smul (by positivity)
    have := inv_antitone _ _ hpos hI.pd hlow
    have e : ((1 / 2 : ℝ) * c.p.sig2⁻¹)⁻¹ = 2 * c.p.sig2 := by rw [mul_inv, inv_inv]; norm_num
    rw [inv_smul_one (by positivity), Matrix.inv_eq_left_inv hI.SP, e] at this
    rw [hI.AA]; exact this
  · rw [hSinv]; exact psd_trans hI.pbl hI.pbd
  · rw [hSinv]; exact psd_trans hI.pb2 hI.pbh

theorem stInv_zero (H : DetBase c δ π m) : c.StInv π 0 := by
  have hs0 := H.rows.pos_sig2
  have hde := H.rows.pos_de
  have hde1 := H.rows.de_lt
  have hc4 := H.rows.c4
  have hr2 := H.rows.r2
  have hsi : 0 < c.p.sig2⁻¹ := inv_pos.2 hs0
  have h2 : 2 ≤ c.p.sig2⁻¹ := by
    rw [show (2 : ℝ) = (1 / 2)⁻¹ by norm_num]; exact inv_anti₀ hs0 (by linarith)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.PosDef.one.smul hsi
  · show (c.p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (c.p.sig2⁻¹ • 1) = 1
    rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hs0.ne', one_smul]
  · show (Real.sqrt c.p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (Real.sqrt c.p.sig2 • 1)ᵀ = c.p.sig2 • 1
    rw [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one, Real.mul_self_sqrt hs0.le]
  · show (Real.sqrt c.p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)).det ≠ 0
    rw [det_smul, det_one, mul_one]
    exact pow_ne_zero _ (Real.sqrt_pos.2 hs0).ne'
  · show (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (1 / 2 : ℝ) • (c.p.sig2⁻¹ • 1)).PosSemidef
    rw [smul_smul]; exact psd_sub_smul_one (by linarith)
  · show ((2 : ℝ) • (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) - c.p.sig2⁻¹ • 1).PosSemidef
    rw [smul_smul]; exact psd_sub_smul_one (by linarith)
  · show ((1 / 2 : ℝ) • (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) - c.p.δe • 1).PosSemidef
    rw [smul_smul]; exact psd_sub_smul_one (by linarith)
  · show (c.p.δe⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (2 : ℝ) • (c.p.sig2⁻¹ • 1)).PosSemidef
    rw [smul_smul]
    refine psd_sub_smul_one ?_
    rw [div_le_one hs0] at hc4
    rw [← div_eq_mul_inv, div_le_iff₀ hs0, ← div_eq_inv_mul, le_div_iff₀ hde]
    linarith
  · rw [sub_self]; exact Matrix.PosSemidef.zero
  · show WithLp.toLp 2 ((1 - c.p.eps)⁻¹ • (0 : Fin d → ℝ)) ∈ c.Kt
    rw [smul_zero]
    exact H.body.2.2.1 (by simp)
  · show true = true ↔ 0 = 0
    simp
  · intro y; simp [Df2Ctx.OmH]
  · show (0 : Fin d → ℝ) = _; simp
  · show (0 : ℝ) = _; simp
  · simp
  · show (0 : Fin d → ℝ) = _; simp

theorem stInv_succ (H : DetBase c δ π m) {s : ℕ} (hs : s < c.tau π m) (hI : c.StInv π s) :
    c.StInv π (s + 1) := by
  have hsm : s < m := hs.trans H.tau_lt
  obtain ⟨-, ⟨ha, hq⟩, ⟨h3a, h3b, h3c, h3d⟩, hcont⟩ := H.cond_lt_tau s hs
  obtain ⟨pt, mu', -, -, hmc, hrun, hst⟩ := c.st_succ_of_cont π s hI.run hcont
  have hR1 : R1Hyp (c.st π s).P (c.st π s).S (c.st π s).A := ⟨hI.pd, hI.AA, hI.SP⟩
  have hii := H.r1ii d _ _ _ (π.xi s) (c.cc π s) hR1 ha hq
  have hiii := H.r1iii d _ _ _ (π.xi s) (c.cc π s) hR1 ha hq
  have hsi := H.si hsm (H.stOK_of_stInv hI)
  have hhess : (c.sHess π s).PosSemidef := hess_psd _ hsi.c2 hsi.convex _
  have hek : 0 < c.p.eta * c.p.kap := mul_pos H.rows.pos_eta (by rw [H.kap]; norm_num)
  have hP : (c.st π (s + 1)).P = c.Pn π s := by rw [hst]; rfl
  have hmu : (c.st π (s + 1)).mu = mu' := by rw [hst]; rfl
  have pbl : ((c.st π (s + 1)).P - (1 / 2 : ℝ) • c.PBar π (s + 1)).PosSemidef := by rw [hP]; exact h3b
  have pbd := h3a
  refine ⟨hrun, posDef_of_sub H.rows.pos_de (psd_trans pbl pbd), ?_, ?_, ?_, pbl, by rw [hP]; exact h3c, pbd, h3d,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]; exact hii.1
  · rw [hst]; exact hiii.2.1
  · rw [hst]; exact hiii.2.2
  · exact psd_of_eq (hI.pb0.add (hhess.smul hek.le)) (by rw [Df2Ctx.PBar_succ]; abel)
  · have hsp := (H.hap (c.Rp π s) ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) c.p.R (c.Pn π s) (c.wmu π s)
      (c.eM π s)).2
    unfold Df2Ctx.mcall at hmc
    rw [hmc] at hsp
    rcases hsp with h | ⟨μ, hμ, hμQ, -⟩
    · cases h
    · rw [hmu, Option.some.inj hμ]; exact hμQ.1
  · rw [hst, Df2Ctx.stNext_first]; simp
  · intro y
    have hphi : c.Phi π (s + 1) y = c.Phi π s y +
        c.cc π s / 2 * df2Sq (vecMulVec (c.u π s) (c.u π s) - (c.st π s).P) (y - (c.st π s).mu) := by
      show df2Phi (c.st π (s + 1)).P (c.st π (s + 1)).b (c.st π (s + 1)).k y = _
      rw [hst]
      exact phi_update _ hI.pd.isHermitian _ _ _ _ _ _
    rw [hphi, hI.phi y]
    unfold Df2Ctx.OmH Df2Ctx.shh
    rw [Finset.sum_range_succ, sq_smul, Df2Ctx.cc_eq]
    ring
  · rw [hst, Finset.sum_range_succ, ← hI.G]; rfl
  · rw [hst, Finset.sum_range_succ, ← hI.l]; rfl
  · rw [hP, Df2Ctx.Pn_eq, hI.Pf, Finset.sum_range_succ, smul_add, add_assoc]
  · rw [show (c.st π (s + 1)).b = c.bn π s by rw [hst]; rfl, Df2Ctx.bn_eq, hI.bf, Finset.sum_range_succ,
      smul_add]

/-- The invariants hold at every round up to `τ`. -/
theorem stInv_le_tau (H : DetBase c δ π m) : ∀ s ≤ c.tau π m, c.StInv π s := by
  intro s hs
  induction s with
  | zero => exact H.stInv_zero
  | succ s ih => exact H.stInv_succ (by omega) (ih (by omega))

end DetBase

end AdversarialBco.Poly
