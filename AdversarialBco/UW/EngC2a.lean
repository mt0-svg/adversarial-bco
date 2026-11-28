/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC1b
public import AdversarialBco.Unified.EngC2d
public import AdversarialBco.UW.DetAcc

@[expose] public section

/-!
# Piece C for BL-OW, part C2 (a): BL-OW's calls, P°'s rounds, E12

Unified/EngC2a.lean for BL-OW at BUD-W. BL-OW's test call and line μ are Theorem U's (`callTO`, `callMO`, `regO` of
Unified/EngC2a.lean, read on BL-OW's values `rvOW`, whose `Y` is the weighted observation); `stepOW` goes through them.
The facts of DET that C2 reads are restated on `DetHypW` (`prev_roundW`, `xi_ellW`, `Pn_lowerW`, `xi_lipW`,
`eT_oneW`). P°'s fields on the weighted path use the sure ranges: `|Y°_u| ≤ y0`, `ĝ_u = 0` where `Y°_u = 0` and
`|ξ_u| ≤ Ξ_w` elsewhere (Lemma WR), so `|Ĝ°| ≤ Ḡ_w` and `|l°| ≤ R Ḡ_w`. E12 at BUD-W, BL-OW's regions against P°'s
`K_ε`, the two levels.
-/

namespace AdversarialBco.UW.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.EngC (callTO fireO wmuO callMO)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.Bit.BLP (refTest)
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## BL-OW's round after R10 -/

theorem testOW_eq (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) (ga : ¬ ((rvOW b0 y0 orc c st ξ ζ obs).a < 1 / 2 ∨ (rvOW b0 y0 orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvOW b0 y0 orc c st ξ ζ obs)) = some p) :
    testOW b0 y0 orc c st ξ ζ obs = some (p, decide (fireO c (rvOW b0 y0 orc c st ξ ζ obs) p)) := by
  unfold testOW
  dsimp only [rvOW, callTO] at ga gt hp ⊢
  rw [ite_eq_right ga, ite_eq_right gt]
  rw [hp]
  rfl

theorem stepOW_fire (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d)
    (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)
    (ga : ¬ ((rvOW b0 y0 orc c st ξ ζ obs).a < 1 / 2 ∨ (rvOW b0 y0 orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvOW b0 y0 orc c st ξ ζ obs)) = some p)
    (hf : fireO c (rvOW b0 y0 orc c st ξ ζ obs) p) :
    stepOW b0 y0 orc c n (.run st) ξ ζ obs = .run (init c.par d) := by
  unfold stepOW
  dsimp only [rvOW, callTO, fireO] at ga gt hp hf ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_left hf]

theorem stepOW_cont (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d)
    (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)
    (ga : ¬ ((rvOW b0 y0 orc c st ξ ζ obs).a < 1 / 2 ∨ (rvOW b0 y0 orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvOW b0 y0 orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvOW b0 y0 orc c st ξ ζ obs)) = some p)
    (hf : ¬ fireO c (rvOW b0 y0 orc c st ξ ζ obs) p)
    (hw : ¬ (2 * c.par.W) ^ 2 < wmuO c st ξ (rvOW b0 y0 orc c st ξ ζ obs) ⬝ᵥ
      wmuO c st ξ (rvOW b0 y0 orc c st ξ ζ obs))
    {mu' : Fin d → ℚ} (hm : apO orc c (callMO c n st ξ (rvOW b0 y0 orc c st ξ ζ obs)) = some mu') :
    stepOW b0 y0 orc c n (.run st) ξ ζ obs = .run ⟨false, mu', (rvOW b0 y0 orc c st ξ ζ obs).A,
      (rvOW b0 y0 orc c st ξ ζ obs).B, (rvOW b0 y0 orc c st ξ ζ obs).b, (rvOW b0 y0 orc c st ξ ζ obs).k,
      (rvOW b0 y0 orc c st ξ ζ obs).G, (rvOW b0 y0 orc c st ξ ζ obs).l⟩ := by
  unfold stepOW
  dsimp only [rvOW, callTO, fireO, wmuO, callMO] at ga gt hp hf hw hm ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_right hf, ite_eq_right hw, hm]

/-! ## The facts of DET that C2 reads, on `DetHypW` -/

section DetFactsW

open AdversarialBco.Poly.Layer2 (sq_le_of_psd sq_smul sq_one sq_nonneg_of_psd mulVec_sq_le)

variable {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {ρ : RefW}

/-- The state of round `s₀ + 1 ≤ τ` is the one `stNext` left at round `s₀`, and P°'s test point of round `s₀` has
`Φ'_{s₀}(pt) ≤ (c₁ - γ) ρ - 2` (Lemma IB2 (i)). -/
theorem prev_roundW (H : DetHypW c π m ρ) {s0 : ℕ} (hs : s0 < c.tau π m) :
    ∃ pt, pt ∈ c.Keps ∧ c.PhiN π s0 pt ≤ (c.p.c1 - c.p.gam) * c.p.rho - 2 ∧
      (c.st π (s0 + 1)).P = c.Pn π s0 ∧ (c.st π (s0 + 1)).b = c.bn π s0 ∧ (c.st π (s0 + 1)).k = c.kn π s0 ∧
      (c.st π (s0 + 1)).r = c.p.sb * (1 - c.p.eps) := by
  obtain ⟨pt, mu', htc, hXi, -, -, hst⟩ := c.st_succ_of_cont π s0 (H.mode_run hs.le) (H.cond_lt_tau s0 hs).2.2.2
  obtain ⟨pt0, htc0, hpt0, -⟩ := H.accT_le hs.le
  rw [htc] at htc0
  have e : pt = pt0 := Option.some.inj htc0
  rw [← e] at hpt0
  have hlev := H.ib2_level hs.le (fun u hu => H.projOK (by omega)) hpt0 hXi
  rw [hst]
  exact ⟨pt, (H.Rm_sub_reg hs.le hpt0).1, hlev, rfl, rfl, rfl, rfl⟩

theorem Pn_zzW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Pn π s *ᵥ c.zz π s = c.bn π s - (c.p.eta / 2) • c.Gn π s := by
  have h := (H.r1_le_tau hs).2.1
  unfold Df2Ctx.zz
  rw [mulVec_mulVec, mul_eq_one_comm.1 h, one_mulVec]

theorem Pn_symmW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) : (c.Pn π s)ᵀ = c.Pn π s :=
  (H.r1_le_tau hs).1.isHermitian.eq

theorem Pn_psdW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (c.Pn π s *ᵥ v) := sq_nonneg_of_psd (H.r1_le_tau hs).1.posSemidef v

/-- `Xi°(y) = C - 2 ellF(P°', z°, y)`. -/
theorem xi_ellW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.Xi π s y = (c.p.eta * c.ln π s - 2 * c.kn π s + c.zz π s ⬝ᵥ (c.Pn π s *ᵥ c.zz π s)) -
      2 * ellF (c.Pn π s) (c.zz π s) y := by
  rw [← refTest_F, refTest_h, refTest_P]
  exact xi_ellF _ (Pn_symmW H hs) _ _ y (Pn_zzW H hs) _

theorem Pn_lowerW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    c.p.δe * (v ⬝ᵥ v) ≤ v ⬝ᵥ (c.Pn π s *ᵥ v) := by
  have h := sq_le_of_psd (H.Sn_props hs).2.2 v
  rw [sq_smul, sq_one] at h
  exact h

theorem Pn_mulVec_leW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    oNorm (c.Pn π s *ᵥ v) ≤ oNorm v / c.p.δe := by
  have hde := H.rows.pos_de
  have hpsd := (H.r1_le_tau hs).1.posSemidef
  have h1 := mulVec_sq_le _ _ hpsd (H.Pn_le hs) v
  have h2 := sq_le_of_psd (H.Pn_le hs) v
  rw [sq_smul, sq_one] at h2
  have h3 : (c.Pn π s *ᵥ v) ⬝ᵥ (c.Pn π s *ᵥ v) ≤ (oNorm v / c.p.δe) ^ 2 := by
    rw [div_pow, oNorm_sq]
    have : c.p.δe⁻¹ * AdversarialBco.Poly.df2Sq (c.Pn π s) v ≤ c.p.δe⁻¹ * (c.p.δe⁻¹ * (v ⬝ᵥ v)) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hde.le)
    calc _ ≤ _ := h1
      _ ≤ _ := this
      _ = (v ⬝ᵥ v) / c.p.δe ^ 2 := by field_simp
  show Real.sqrt _ ≤ _
  have h0 : 0 ≤ oNorm v / c.p.δe := div_nonneg (oNorm_nonneg _) hde.le
  calc Real.sqrt ((c.Pn π s *ᵥ v) ⬝ᵥ (c.Pn π s *ᵥ v)) ≤ Real.sqrt ((oNorm v / c.p.δe) ^ 2) := Real.sqrt_le_sqrt h3
    _ = oNorm v / c.p.δe := Real.sqrt_sq h0

/-- The centre of P°'s test with sure ranges: `|b' - (η/2) Ĝ'| ≤ R/δe²` (the bound inside `not_gdZ`). -/
theorem wn_leW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) :
    oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) ≤ c.p.R / c.p.δe ^ 2 := by
  have hde := H.rows.pos_de
  have hek := H.kap_pos
  have hη := H.rows.pos_eta
  have hR1 := H.rows.one_le_R
  have hb : oNorm (c.bn π s) ≤ c.p.R / (4 * c.p.δe ^ 2) := by
    rw [H.bn_sum hs]
    refine (oNorm_sum_le' _ _).trans ?_
    have hterm : ∀ u ∈ Finset.range (s + 1), oNorm (((c.p.eta * c.p.kap) • c.shh π u) *ᵥ (c.st π u).mu) ≤
        c.p.eta * c.p.kap * moneW c ρ * c.p.R := by
      intro u hu
      have hut : u ≤ c.tau π m := by have := Finset.mem_range.1 hu; omega
      rw [smul_mulVec, oNorm_smul', abs_of_pos hek]
      have h1 := (H.shh_norm hut _).trans (mul_le_mul_of_nonneg_left
        (H.norm_le_of_keps (H.stInv_le_tau u hut).mu) H.moneW_nonneg)
      have := mul_le_mul_of_nonneg_left h1 hek.le
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := H.grad_arith'.1
    have h2 : ((s + 1 : ℕ) : ℝ) ≤ c.n := H.n_ge hs
    have hM := H.moneW_nonneg
    calc ((s + 1 : ℕ) : ℝ) * (c.p.eta * c.p.kap * moneW c ρ * c.p.R)
        ≤ c.n * (c.p.eta * c.p.kap * moneW c ρ) * c.p.R := by
          rw [← mul_assoc, ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ 1 / (4 * c.p.δe ^ 2) * c.p.R := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring
  have hG : c.p.eta / 2 * oNorm (c.Gn π s) ≤ 3 / 4 * c.p.R / c.p.δe ^ 2 := by
    rw [H.Gn_sum hs]
    have h1 : oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u) ≤
        c.n * (ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe)) := by
      refine (oNorm_sum_le' _ _).trans ((Finset.sum_le_sum fun u hu => H.ghat_norm
        (by have := Finset.mem_range.1 hu; omega)).trans ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.y0_nonneg; positivity)
    calc c.p.eta / 2 * oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u)
        ≤ c.p.eta / 2 * (c.n * (ρ.y0 * Real.sqrt c.p.k0 * Real.sqrt ((ρ.b0 + 1) / c.p.δe))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := H.gZ
  refine (oNorm_sub_le' _ _).trans ?_
  rw [oNorm_smul', abs_of_pos (by positivity)]
  have : c.p.R / (4 * c.p.δe ^ 2) + 3 / 4 * c.p.R / c.p.δe ^ 2 = c.p.R / c.p.δe ^ 2 := by field_simp; ring
  linarith

/-- `Xi°` is `4R/δe²`-Lipschitz from a point of `B_R`. -/
theorem xi_lipW (H : DetHypW c π m ρ) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) {y' : Fin d → ℝ}
    (hy' : oNorm y' ≤ c.p.R) : c.Xi π s y ≤ c.Xi π s y' + 4 * c.p.R / c.p.δe ^ 2 * oNorm (y - y') := by
  have hde := H.rows.pos_de
  have hde1 := H.rows.de_lt
  have hR := H.rows.one_le_R
  rw [← refTest_F, ← refTest_F]
  refine (quad_concave_le _ _ _ (fun v => by rw [refTest_P]; exact Pn_psdW H hs v) y y').trans ?_
  have hg : oNorm ((refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.1 -
      ((refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2 + (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2ᵀ) *ᵥ y') ≤
      4 * c.p.R / c.p.δe ^ 2 := by
    rw [refTest_h, refTest_P, Pn_symmW H hs]
    have e : (2 : ℝ) • (c.bn π s - (c.p.eta / 2) • c.Gn π s) - (c.Pn π s + c.Pn π s) *ᵥ y' =
        (2 : ℝ) • ((c.bn π s - (c.p.eta / 2) • c.Gn π s) - c.Pn π s *ᵥ y') := by
      rw [add_mulVec]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, oNorm_smul, abs_two]
    have h1 := oNorm_sub_le (c.bn π s - (c.p.eta / 2) • c.Gn π s) (c.Pn π s *ᵥ y')
    have h2 := wn_leW H hs
    have h3 := Pn_mulVec_leW H hs y'
    have h4 : oNorm y' / c.p.δe ≤ c.p.R / c.p.δe ^ 2 := by
      rw [div_le_div_iff₀ hde (by positivity)]
      have : c.p.δe ^ 2 ≤ c.p.δe := by nlinarith
      nlinarith [oNorm_nonneg y']
    have : 4 * c.p.R / c.p.δe ^ 2 = 2 * (c.p.R / c.p.δe ^ 2 + c.p.R / c.p.δe ^ 2) := by ring
    rw [this]
    linarith
  have := mul_le_mul_of_nonneg_right hg (oNorm_nonneg (y - y'))
  linarith

theorem eT_oneW (H : DetHypW c π m ρ) (hLe : 2 ≤ c.p.Le) : c.eT = 1 := by
  unfold Df2Ctx.eT
  rw [H.alpha]
  apply min_eq_left
  have h1 := H.pri_le_rho
  have hR := H.rows.one_le_R
  unfold df2Pri at h1
  rw [H.sig2] at h1
  have hL : 0 < c.p.Le := by linarith
  have e : c.p.R ^ 2 / (2 * (1 / (8 * c.p.Le))) = 4 * c.p.R ^ 2 * c.p.Le := by field_simp; ring
  rw [e] at h1
  nlinarith

end DetFactsW

/-! ## P°'s rounds `u ≤ s` on the weighted path -/

namespace SettW

variable {n : ℕ} {δ : ℚ} {c : Df2Ctx d} {π πw : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hu' (S : SettW d n δ c π πw s st ξ') {u : ℕ} (hu : u ≤ s) : u ≤ c.tau πw (s + 1) := hu.trans S.hs'

theorem Y_le_u (S : SettW d n δ c π πw s st ξ') {u : ℕ} (hu : u ≤ s) : |c.Y πw u| ≤ (rW d n δ).y0 :=
  S.det.Ybd u (S.hu' hu)

theorem y0_nn (S : SettW d n δ c π πw s st ξ') : 0 ≤ (rW d n δ).y0 := (S.R.y0_bd).1.le

theorem lam_le (S : SettW d n δ c π πw s st ξ') : c.p.lam ≤ 1 / 1000 := by
  rw [S.hp]
  have h := (S.R.lam_bd).2
  have : (1 : ℝ) / (725 * 17467 ^ 2) ≤ 1 / 1000 := by norm_num
  exact h.trans this

theorem opN_PA_u (S : SettW d n δ c π πw s st ξ') {u : ℕ} (hu : u ≤ s) :
    opN ((c.st πw u).P * (c.st πw u).A) ≤ Real.sqrt (rW d n δ).Lam := by
  have hI := S.det.stInv_le_tau u (S.hu' hu)
  have hsym : (c.st πw u).Pᵀ = (c.st πw u).P := by
    have := hI.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPS : (c.st πw u).P * (c.st πw u).S = 1 := mul_eq_one_comm.1 hI.SP
  have hsq : ((c.st πw u).P * (c.st πw u).A) * ((c.st πw u).P * (c.st πw u).A)ᵀ = (c.st πw u).P := by
    rw [Matrix.transpose_mul, hsym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st πw u).A, hI.AA, ← Matrix.mul_assoc,
      hPS, Matrix.one_mul]
  have htr : (c.st πw u).P.trace ≤ (rW d n δ).Lam := by
    have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le (S.hu' hu))
    rw [inv_inv] at this
    have e : (d : ℝ) * c.p.δe⁻¹ = d / c.p.δe := by ring
    linarith [S.de_c]
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [hsq]; exact htr

/-- `|ĝ_u| ≤ 1.01 y0 Λ^{1/2} Ξ_w` for `u ≤ s`: `ĝ_u = 0` where `Y°_u = 0`, and `|ξ_u|² ≤ b0 + 1` elsewhere. -/
theorem ghat_le (S : SettW d n δ c π πw s st ξ') {u : ℕ} (hu : u ≤ s) :
    oNorm (c.ghat πw u) ≤ 101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw := by
  have hl0 : 0 < c.p.lam := by rw [S.hp]; exact S.lam_pos
  have hl1 := S.lam_le
  have h1l : 0 < 1 - c.p.lam := by linarith
  have hy0 := S.y0_nn
  have hXw := (Xw_nonneg S.R).1
  have hsL := Real.sqrt_nonneg (rW d n δ).Lam
  have hR0 : 0 ≤ 101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy0) hsL) hXw
  unfold Df2Ctx.ghat
  rw [oNorm_smul, abs_div, abs_of_pos h1l]
  by_cases hY0 : c.Y πw u = 0
  · rw [hY0, abs_zero, zero_div, zero_mul]; exact hR0
  · have hY := S.Y_le_u hu
    have hun : oNorm (c.u πw u) ≤ Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw := by
      have e : c.u πw u = ((c.st πw u).P * (c.st πw u).A) *ᵥ πw.xi u := by
        unfold Df2Ctx.u Df2Ctx.w; rw [Matrix.mulVec_mulVec]
      rw [e]
      refine (oNorm_mulVec_le _ _).trans (mul_le_mul (S.opN_PA_u hu) ?_ (oNorm_nonneg _) hsL)
      have h := S.det.Ywt u (S.hu' hu) hY0
      have h1 : oNorm (πw.xi u) ≤ Real.sqrt ((rW d n δ).b0 + 1) := by
        unfold oNorm; exact Real.sqrt_le_sqrt h
      exact h1.trans (S.R.Xw_bd).1
    have hinv : 1 / (1 - c.p.lam) ≤ 101 / 100 := by
      rw [div_le_iff₀ h1l]; nlinarith
    have hX0 : 0 ≤ Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw := mul_nonneg hsL hXw
    calc |c.Y πw u| / (1 - c.p.lam) * oNorm (c.u πw u)
        = |c.Y πw u| * (1 / (1 - c.p.lam)) * oNorm (c.u πw u) := by ring
      _ ≤ (rW d n δ).y0 * (101 / 100) * (Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw) :=
          mul_le_mul (mul_le_mul hY hinv (by positivity) hy0) hun (oNorm_nonneg _)
            (mul_nonneg hy0 (by norm_num))
      _ = _ := by ring

/-- E11w: `|Ĝ°_{s+1}| ≤ Ḡ_w`. -/
theorem Gn_le (S : SettW d n δ c π πw s st ξ') : oNorm (c.Gn πw s) ≤ (rW d n δ).Gb := by
  rw [S.det.Gn_sum S.hs']
  refine (AdversarialBco.Poly.oNorm_sum_le' _ _).trans ?_
  refine (Finset.sum_le_sum fun u hu => S.ghat_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have hy0 := S.y0_nn
  have hXw := (Xw_nonneg S.R).1
  have hsL := Real.sqrt_nonneg (rW d n δ).Lam
  have h0 : 0 ≤ 101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy0) hsL) hXw
  have hnr : (rW d n δ).n = (n : ℝ) := rfl
  unfold RegW.Gb
  rw [hnr]
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw)
      ≤ n * (101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw) :=
        mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

/-- E11w: `|l°_{s+1}| ≤ R Ḡ_w`. -/
theorem ln_le (S : SettW d n δ c π πw s st ξ') : |c.ln πw s| ≤ (rW d n δ).R * (rW d n δ).Gb := by
  have hI := S.inv
  have e : c.ln πw s = ∑ u ∈ Finset.range (s + 1), c.ghat πw u ⬝ᵥ (c.st πw u).mu := by
    unfold Df2Ctx.ln; rw [hI.l, Finset.sum_range_succ]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ u ∈ Finset.range (s + 1), |c.ghat πw u ⬝ᵥ (c.st πw u).mu| ≤
      101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw * (rW d n δ).R := by
    intro u hu
    have hu' : u ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    have hmu : oNorm (c.st πw u).mu ≤ (rW d n δ).R := by
      have := S.det.norm_le_of_keps (S.det.stInv_le_tau u (S.hu' hu')).mu
      rw [S.hp] at this; exact this
    exact (abs_dot_le _ _).trans (mul_le_mul (S.ghat_le hu') hmu (oNorm_nonneg _)
      ((oNorm_nonneg _).trans (S.ghat_le hu')))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have hy0 := S.y0_nn
  have hXw := (Xw_nonneg S.R).1
  have hsL := Real.sqrt_nonneg (rW d n δ).Lam
  have hR : 0 ≤ (rW d n δ).R := by linarith [S.R.hR1]
  have h0 : 0 ≤ 101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw * (rW d n δ).R :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy0) hsL) hXw) hR
  have hnr : (rW d n δ).n = (n : ℝ) := rfl
  unfold RegW.Gb
  rw [hnr]
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw * (rW d n δ).R)
      ≤ n * (101 / 100 * (rW d n δ).y0 * Real.sqrt (rW d n δ).Lam * (rW d n δ).Xw * (rW d n δ).R) :=
        mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

end SettW

/-! ## E12: the constant -/

/-- `e_Φ` from its three parts, for `j ≤ n` rounds of the fields. -/
theorem ePhi_geW (r : RegW) (j : ℝ) (hR0 : 0 ≤ r.R) (heb0 : 0 ≤ r.eb) (hek0 : 0 ≤ r.ek) (hj : j ≤ r.n)
    {x y z : ℝ} (hx : x ≤ r.DP) (hy : y ≤ j * r.eb) (hz : z ≤ j * r.ek) :
    r.R ^ 2 / 2 * x + r.R * y + z ≤ r.ePhi := by
  unfold RegW.ePhi
  have h1 : r.R ^ 2 / 2 * x ≤ r.R ^ 2 / 2 * r.DP := mul_le_mul_of_nonneg_left hx (by positivity)
  have h2 : r.R * y ≤ r.R * (r.n * r.eb) :=
    mul_le_mul_of_nonneg_left (hy.trans (mul_le_mul_of_nonneg_right hj heb0)) hR0
  have h3 : z ≤ r.n * r.ek := hz.trans (mul_le_mul_of_nonneg_right hj hek0)
  nlinarith

end AdversarialBco.UW.EngC

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.EngC (callTO fireO wmuO callMO regO regO_callO regO_callO_k)
open AdversarialBco.Unified.Eng.RCHypO (cast_inv_eps)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-! ## The two readings of the caps -/

theorem deL_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 < (rW d c.n δ).de := (H.R.pos).2.2.2.2.2.1

/-- The level `δ_e = 1/N_e` is at most P°'s floor `δ_0`. -/
theorem deL_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).de ≤ (poW d c.n δ).δe := by
  have h := NW.inv_de_le_Ne d c.n δ H.hd H.hn
  have h0 := H.sett.de_pos
  rw [H.R.hde, div_le_iff₀ (lt_of_lt_of_le (one_div_pos.2 h0) h)]
  rw [div_le_iff₀ h0] at h
  linarith

theorem deL_le_one (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).de ≤ 1 :=
  H.deL_le.trans H.det.rows.de_lt.le

/-- The gradient cap at the level: `R/δ_0² ≤ R/δ_e²`. -/
theorem grad_cap (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (poW d c.n δ).R / (poW d c.n δ).δe ^ 2 ≤ (rW d c.n δ).R / (rW d c.n δ).de ^ 2 := by
  have h1 := H.deL_pos
  have h2 := H.deL_le
  have hR : 0 ≤ (rW d c.n δ).R := by linarith [H.R.hR1]
  have h3 : (rW d c.n δ).de ^ 2 ≤ (poW d c.n δ).δe ^ 2 := pow_le_pow_left₀ h1.le h2 2
  exact div_le_div_of_nonneg_left hR (by positivity) h3

/-- BL-OW's `s'_b` is at most P°'s `s_b(δ_0)`: `s'_b ≤ δ_e²/(R(R + 1)) ≤ δ_0²/(R(R + 1))`. -/
theorem sb_le0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ((c.par.sb : ℚ) : ℝ) ≤ (poW d c.n δ).sb := by
  have e := H.det.sb
  change (poW d c.n δ).sb = (poW d c.n δ).δe ^ 2 / ((poW d c.n δ).R * ((poW d c.n δ).R + 1)) at e
  have h1 : ((c.par.sb : ℚ) : ℝ) ≤ (rW d c.n δ).de ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) := by
    rw [H.par]; exact H.enc.sb_le
  have hR : 1 ≤ (rW d c.n δ).R := by linarith [H.R.hR1]
  have h3 : (rW d c.n δ).de ^ 2 ≤ (poW d c.n δ).δe ^ 2 := pow_le_pow_left₀ H.deL_pos.le H.deL_le 2
  have h4 : (rW d c.n δ).de ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) ≤
      (poW d c.n δ).δe ^ 2 / ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) :=
    div_le_div_of_nonneg_right h3 (by positivity)
  rw [e]
  exact h1.trans h4

/-! ## BL-OW's regions against `K_ε` -/

theorem eps_lt (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).eps ≤ ((c.par.eps : ℚ) : ℝ) ∧ ((c.par.eps : ℚ) : ℝ) ≤ 1 / 2 ∧ (rW d c.n δ).eps ≤ 1 / 4 ∧
      0 < (rW d c.n δ).eps :=
  ⟨H.eps_relH.1, H.eps'_le, H.sett.eps_le, H.sett.eps_pos⟩

theorem body_convex (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : Convex ℝ (bodyS K c) :=
  convex_posBodyO H.frame.1 _ _

theorem zero_mem_body (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (0 : E d) ∈ bodyS K c :=
  H.goodPos.1 (Metric.mem_closedBall_self zero_le_one)

/-- BL-OW's K-part `QKs (1 - ε')⁻¹` lies in `K_ε`. -/
theorem keps_of_QK (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ QKs K c (1 - c.par.eps)⁻¹) : y ∈ (ctxOW K c δ ap).Keps := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have h1 : 0 < 1 - (rW d c.n δ).eps := by linarith
  have h1' : 0 < 1 - ((c.par.eps : ℚ) : ℝ) := by linarith
  have hy' : WithLp.toLp 2 ((1 - ((c.par.eps : ℚ) : ℝ))⁻¹ • y) ∈ bodyS K c := by
    have hy2 : WithLp.toLp 2 ((((1 - c.par.eps)⁻¹ : ℚ) : ℝ) • y) ∈ bodyS K c := hy
    rwa [cast_inv_eps] at hy2
  show WithLp.toLp 2 ((1 - (rW d c.n δ).eps)⁻¹ • y) ∈ (ctxOW K c δ ap).Kt
  rw [H.Kt_eq]
  have ht0 : 0 ≤ (1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps) := div_nonneg h1'.le h1.le
  have ht1 : (1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps) ≤ 1 := (div_le_one h1).2 (by linarith)
  have e : WithLp.toLp 2 ((1 - (rW d c.n δ).eps)⁻¹ • y) =
      ((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps)) •
        WithLp.toLp 2 ((1 - ((c.par.eps : ℚ) : ℝ))⁻¹ • y) := by
    rw [← WithLp.toLp_smul, smul_smul]
    congr 2
    field_simp
  rw [e]
  exact H.body_convex.smul_mem_of_zero_mem H.zero_mem_body hy' ⟨ht0, ht1⟩

/-- `κ K_ε` lies in BL-OW's K-part, `κ = (1 - ε')/(1 - ε)`. -/
theorem QK_of_keps (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxOW K c δ ap).Keps) :
    ((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps)) • y ∈ QKs K c (1 - c.par.eps)⁻¹ := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have h1 : 0 < 1 - (rW d c.n δ).eps := by linarith
  have h1' : 0 < 1 - ((c.par.eps : ℚ) : ℝ) := by linarith
  have hy' : WithLp.toLp 2 ((1 - (rW d c.n δ).eps)⁻¹ • y) ∈ bodyS K c := by
    rw [← H.Kt_eq]; exact hy
  show WithLp.toLp 2 ((((1 - c.par.eps)⁻¹ : ℚ) : ℝ) •
    (((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps)) • y)) ∈ bodyS K c
  have e : (((1 - c.par.eps)⁻¹ : ℚ) : ℝ) • (((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - (rW d c.n δ).eps)) • y) =
      (1 - (rW d c.n δ).eps)⁻¹ • y := by
    rw [smul_smul, cast_inv_eps]
    congr 1
    field_simp
  rw [e]; exact hy'

theorem keps_norm (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxOW K c δ ap).Keps) : oNorm y ≤ (rW d c.n δ).R :=
  H.det.norm_le_of_keps hy

theorem R_le_Rint (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).R ≤ (c.par.Rint : ℝ) :=
  H.R_le_par.trans H.parR_le_Rint

theorem R_ge (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 1 ≤ (rW d c.n δ).R := H.one_le_R

/-! ## E12: BL-OW's quadratics against P°'s -/

theorem eb0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).eb := (H.R.eb_ek).1

theorem ek0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).ek := (H.R.eb_ek).2.2.1

/-- E12 at round `s` (BL's state before the round against P°'s `Φ°_s`). -/
theorem phi_err_s (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ} (hy : oNorm y ≤ (rW d c.n δ).R) :
    |df2Phi (cM st.B * (cM st.B)ᵀ) (cV st.b) st.k y -
      df2Phi ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).P ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).b
        ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).k y| ≤ (rW d c.n δ).ePhi := by
  have S := H.sett
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) ≤ (rW d c.n δ).n := by show (s : ℝ) ≤ (c.n : ℝ); exact_mod_cast H.hs.le
  exact ePhi_geW (rW d c.n δ) (s : ℝ) H.R0 H.eb0 H.ek0 hs H.P'_err.1 S.track.errb S.track.errk

/-- BL's `P'_+ = B'_+ B'_+ᵀ` against P°'s `P'`. -/
theorem Pp_err (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    opN (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ -
        (ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) ≤ (rW d c.n δ).DP ∧
      opN (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ) ≤
        10201 / 10000 * (rW d c.n δ).Lam := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  have e : cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ =
      (1 + H0) * cx.Pn πw s * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * (cx.Pn πw s * cx.An πw s) * ((cx.Pn πw s * cx.An πw s)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * ((cx.Pn πw s * cx.An πw s) * (cx.Pn πw s * cx.An πw s)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PnAn_sq]
  have hPn : opN (cx.Pn πw s) ≤ (rW d c.n δ).Lam := by
    have h := opN_mul_le (cx.Pn πw s * cx.An πw s) (cx.Pn πw s * cx.An πw s)ᵀ
    rw [S.PnAn_sq, opN_transpose] at h
    have h2 := S.opN_PnAn
    have h0 := opN_nonneg (cx.Pn πw s * cx.An πw s)
    have : Real.sqrt (rW d c.n δ).Lam * Real.sqrt (rW d c.n δ).Lam = (rW d c.n δ).Lam :=
      Real.mul_self_sqrt S.Lam_pos.le
    nlinarith
  rw [e]
  have hb := H.hb_le
  have hb0 := H.hb0
  have hT : (rW d c.n δ).hTr (s + 1) ≤ (rW d c.n δ).hb :=
    H.R.hTr_le (s + 1) (by show ((s + 1 : ℕ) : ℝ) ≤ (c.n : ℝ); exact_mod_cast H.hs)
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans hT) hPn
  refine ⟨h1.trans (le_of_eq (by unfold RegW.DP; ring)), h2.trans ?_⟩
  have : (1 + (rW d c.n δ).hb) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

/-- E12 at round `s + 1` (BL's new fields against P°'s `Φ'`). -/
theorem phi_err_n (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ (rW d c.n δ).R) :
    |df2Phi (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ)
        (cV (rvHW orc c δ st ξ' ζ' ε f).b) (rvHW orc c δ st ξ' ζ' ε f).k y -
      (ctxOW K c δ ap).PhiN (pwOW K c δ ap π) s y| ≤ (rW d c.n δ).ePhi := by
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) + 1 ≤ (rW d c.n δ).n := by show (s : ℝ) + 1 ≤ (c.n : ℝ); exact_mod_cast H.hs
  exact ePhi_geW (rW d c.n δ) ((s : ℝ) + 1) H.R0 H.eb0 H.ek0 hs (H.Pp_err O).1 O.errb O.errk

theorem rho_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 < (rW d c.n δ).rho := H.det.rows.pos_rho

theorem wr0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).wr := (H.R.wr_we).1

/-- `ρ - w_ρ ≤ ρ' ≤ ρ` (Lemma ENC-W). -/
theorem rho_enc (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (c.par.rho : ℝ) ≤ (rW d c.n δ).rho ∧ (rW d c.n δ).rho - (rW d c.n δ).wr ≤ (c.par.rho : ℝ) := by
  have hρ := H.rho_pos
  have hρne : (rW d c.n δ).rho ≠ 0 := hρ.ne'
  rw [H.par]
  refine ⟨H.enc.rho_le, ?_⟩
  have h := (abs_le.1 H.enc.rho_rel).1
  have e : ((parOW d c.n δ).rho : ℝ) =
      (((parOW d c.n δ).rho : ℝ) / (rW d c.n δ).rho) * (rW d c.n δ).rho := by
    field_simp
  unfold RegW.wr
  rw [e]
  nlinarith

/-- The two levels of the test region: BL's `L_T = 7.99 ρ' - ê` against P°'s `(c₁ - γ) ρ`, with the drop
`D = e_Φ + ê + 8 w_ρ` of the gap. -/
theorem LT_lev (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ((LT c.par : ℚ) : ℝ) + (rW d c.n δ).ePhi ≤
        ((ctxOW K c δ ap).p.c1 - (ctxOW K c δ ap).p.gam) * (ctxOW K c δ ap).p.rho ∧
      ((ctxOW K c δ ap).p.c1 - (ctxOW K c δ ap).p.gam) * (ctxOW K c δ ap).p.rho -
          ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr) + (rW d c.n δ).ePhi ≤
        ((LT c.par : ℚ) : ℝ) := by
  rw [LT_cast, H.det.c1, H.det.gam]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.R.ePhi_le_eh
  have h4 := H.wr0
  have e : ((c.par.eHat : ℚ) : ℝ) = (rW d c.n δ).eh := by rw [H.par]; rfl
  rw [e]
  have e2 : (ctxOW K c δ ap).p.rho = (rW d c.n δ).rho := rfl
  rw [e2]
  constructor <;> nlinarith

/-- The two levels of line μ: BL's `L_μ = 8 ρ' - ê` against P°'s `c₁ ρ`. -/
theorem Lmu_lev (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ((Lmu c.par : ℚ) : ℝ) + (rW d c.n δ).ePhi ≤ (ctxOW K c δ ap).p.c1 * (ctxOW K c δ ap).p.rho ∧
      (ctxOW K c δ ap).p.c1 * (ctxOW K c δ ap).p.rho -
          ((rW d c.n δ).ePhi + (rW d c.n δ).eh + 8 * (rW d c.n δ).wr) + (rW d c.n δ).ePhi ≤
        ((Lmu c.par : ℚ) : ℝ) := by
  rw [Lmu_cast, H.det.c1]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.R.ePhi_le_eh
  have h4 := H.wr0
  have e : ((c.par.eHat : ℚ) : ℝ) = (rW d c.n δ).eh := by rw [H.par]; rfl
  rw [e]
  have e2 : (ctxOW K c δ ap).p.rho = (rW d c.n δ).rho := rfl
  rw [e2]
  constructor <;> nlinarith

/-- A point of BL-OW's region of a call at the level `ℓ₀` is in `K_ε` and under P°'s level `L`. -/
theorem in_of_region (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 kq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ (rW d c.n δ).R →
      |df2Phi (cM Hq) (cV g) kq y - df2Phi Po bo ko y| ≤ (rW d c.n δ).ePhi)
    (L : ℝ) (hL : (ℓ0 : ℝ) + (rW d c.n δ).ePhi ≤ L) {y : Fin d → ℝ}
    (hy : y ∈ regO K c (callO c Hq g (ℓ0 - kq) r P fq e)) :
    y ∈ (ctxOW K c δ ap).Keps ∧ df2Phi Po bo ko y ≤ L := by
  obtain ⟨h1, h2, -⟩ := (regO_callO_k K c _ _ _ _ _ _ _ _ y).1 hy
  have hk := H.keps_of_QK h1
  have := (abs_le.1 (herr y (H.keps_norm hk))).1
  exact ⟨hk, by linarith⟩

/-- A point of BL-OW's K-part under P°'s level `L - D` is in BL-OW's region at the level `ℓ₀`. -/
theorem region_of_in (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 kq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ (rW d c.n δ).R →
      |df2Phi (cM Hq) (cV g) kq y - df2Phi Po bo ko y| ≤ (rW d c.n δ).ePhi)
    (L D : ℝ) (hL : L - D + (rW d c.n δ).ePhi ≤ (ℓ0 : ℝ)) {y : Fin d → ℝ}
    (hy : y ∈ QKs K c (1 - c.par.eps)⁻¹) (hΦ : df2Phi Po bo ko y ≤ L - D) :
    y ∈ regO K c (callO c Hq g (ℓ0 - kq) r P fq e) := by
  have hk := H.keps_of_QK hy
  have hR := H.keps_norm hk
  have := (abs_le.1 (herr y hR)).2
  exact (regO_callO_k K c _ _ _ _ _ _ _ _ y).2 ⟨hy, by linarith, hR.trans H.R_le_Rint⟩

end AdversarialBco.UW.Eng.RCHypOW
