/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundC1
public import AdversarialBco.Bit.BLRoundC2Alg

@[expose] public section

/-!
# Piece C, part C2: the test call, the fire decision and line μ

Lemmas SEL, VAL and GUARD with E12 to E16 and E18, against
P°'s round `s` with the checked advice `advQ`: BL's test call succeeds (`O3SpecQ` on a ball of the shrunk region),
the selection `selT` of BL's test point passes P°'s check at accuracy `eT = 1`, both learners fire or both continue;
in a continued round BL's guard R13 does not act, line μ succeeds and its answer passes P°'s check at `eM`, and
`Track` holds at `s + 1`. Conclusion: `c2 : C2Stmt` and `roundC : RoundC`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Bit.Asm (deltaBL RunCase)
open AdversarialBco.RealRAM (polytope)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Bit.Cpl (apAdv advOK advPick)
open Matrix

variable {d : ℕ}

/-! ## BL's round after R10 -/

/-- BL's test call (R11) from the values `r` of R5 to R9. -/
def callTQ (cfg : Cfg d) (st : St d) (r : RV d) : CallQ d :=
  if st.first then callOf cfg 0 0 0 (1 - cfg.par.eps) (r.B * r.Bᵀ) (r.b - (cfg.par.eta / 2) • r.G)
      ((1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8))
  else callOf cfg (st.B * st.Bᵀ) st.b (LT cfg.par - st.k) (rB cfg.par / 2) (r.B * r.Bᵀ)
      (r.b - (cfg.par.eta / 2) • r.G) (rB cfg.par ^ 2 / (cfg.par.Ne * d * 8))

/-- BL's fire test (R12) at the test point `p`. -/
abbrev fireQ (cfg : Cfg d) (r : RV d) (p : Fin d → ℚ) : Prop :=
  cfg.par.eta * (r.l - r.G ⬝ᵥ p) - 2 * (p ⬝ᵥ ((r.B * r.Bᵀ) *ᵥ p) / 2 - r.b ⬝ᵥ p + r.k) ≤
    -cfg.par.rho + cfg.par.eHat

/-- BL's Newton point of line μ (R13). -/
def wmuQ (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (r : RV d) : Fin d → ℚ :=
  st.mu - rnd cfg.par.p (cfg.par.eta * r.Y * cfg.par.nu / r.q) • (st.A *ᵥ ξ)

/-- BL's call of line μ (R14). -/
def callMQ (cfg : Cfg d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (r : RV d) : CallQ d :=
  callOf cfg (r.B * r.Bᵀ) r.b (Lmu cfg.par - r.k) (rB cfg.par / 2) (r.B * r.Bᵀ)
    ((r.B * r.Bᵀ) *ᵥ wmuQ cfg st ξ r) (eBL cfg.par d n)

theorem testQ_eq (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)
    (ga : ¬ ((rv cfg st ξ ζ obs).a < 1 / 2 ∨ (rv cfg st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).B ∨ 2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : ap (callTQ cfg st (rv cfg st ξ ζ obs)) = some p) :
    testQ ap cfg st ξ ζ obs = some (p, decide (fireQ cfg (rv cfg st ξ ζ obs) p)) := by
  unfold testQ
  dsimp only [rv, callTQ] at ga gt hp ⊢
  rw [ite_eq_right ga, ite_eq_right gt]
  rw [hp]
  rfl

theorem step_fire (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) (ga : ¬ ((rv cfg st ξ ζ obs).a < 1 / 2 ∨ (rv cfg st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).B ∨ 2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : ap (callTQ cfg st (rv cfg st ξ ζ obs)) = some p) (hf : fireQ cfg (rv cfg st ξ ζ obs) p) :
    step ap cfg n (.run st) ξ ζ obs = .run (init cfg.par d) := by
  unfold step
  dsimp only [rv, callTQ, fireQ] at ga gt hp hf ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_left hf]

theorem step_cont (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) (ga : ¬ ((rv cfg st ξ ζ obs).a < 1 / 2 ∨ (rv cfg st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).B ∨ 2 * (cfg.par.Lam : ℚ) < frob2 (rv cfg st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : ap (callTQ cfg st (rv cfg st ξ ζ obs)) = some p) (hf : ¬ fireQ cfg (rv cfg st ξ ζ obs) p)
    (hw : ¬ (2 * cfg.par.W) ^ 2 < wmuQ cfg st ξ (rv cfg st ξ ζ obs) ⬝ᵥ wmuQ cfg st ξ (rv cfg st ξ ζ obs))
    {mu' : Fin d → ℚ} (hm : ap (callMQ cfg n st ξ (rv cfg st ξ ζ obs)) = some mu') :
    step ap cfg n (.run st) ξ ζ obs = .run ⟨false, mu', (rv cfg st ξ ζ obs).A, (rv cfg st ξ ζ obs).B,
      (rv cfg st ξ ζ obs).b, (rv cfg st ξ ζ obs).k, (rv cfg st ξ ζ obs).G, (rv cfg st ξ ζ obs).l⟩ := by
  unfold step
  dsimp only [rv, callTQ, fireQ, wmuQ, callMQ] at ga gt hp hf hw hm ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_right hf, ite_eq_right hw, hm]


/-! ## P°'s rounds `u ≤ s` -/

namespace Sett

variable {n : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hu' (S : Sett d n c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : u ≤ c.tau π (s + 1) := hu.trans S.hs'

theorem Y_le_u (S : Sett d n c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : |c.Y π u| ≤ Bud.Yb d n := by
  obtain ⟨he, hg, -⟩ := S.det.evG u (S.hu' hu)
  have hgv := (S.det.adm u (S.det.le_tau_lt (S.hu' hu))).2 _ (S.det.play_keps u).2
  have hLg := S.bud.Lg_le
  have hLgb := Bud.Lgb_ge d n S.bud
  have h := ybar_real (c.pip π u) (gauge c.Kt (WithLp.toLp 2 (c.X π u))) (π.g u (WithLp.toLp 2 (c.play π u)))
    (π.e u) c.p.Le (Bud.Lgb d n) c.p.eps S.det.rows.pos_eps (by rw [S.hp]; exact S.eps_le) rfl (gauge_nonneg _) hg
    hgv.1 hgv.2 (he.trans (Real.sqrt_le_sqrt (by rw [S.hp, S.hcn]; exact hLg))) hLgb S.det.one_le_Le
  unfold Df2Ctx.Y
  rw [S.hp] at h ⊢
  unfold Bud.Yb Bud.Le Bud.eps
  exact h

theorem xi_le_u (S : Sett d n c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : oNorm (π.xi u) ≤ Bud.Xi d n :=
  xi_norm S.det (S.hu' hu) S.hp S.hcn S.bud

theorem opN_PA_u (S : Sett d n c δ π s st ξ') {u : ℕ} (hu : u ≤ s) :
    opN ((c.st π u).P * (c.st π u).A) ≤ Real.sqrt (Bud.Lam d n) := by
  have hI := S.det.stInv_le_tau u (S.hu' hu)
  have hsym : (c.st π u).Pᵀ = (c.st π u).P := by
    have := hI.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPS : (c.st π u).P * (c.st π u).S = 1 := mul_eq_one_comm.1 hI.SP
  have hsq : ((c.st π u).P * (c.st π u).A) * ((c.st π u).P * (c.st π u).A)ᵀ = (c.st π u).P := by
    rw [Matrix.transpose_mul, hsym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st π u).A, hI.AA, ← Matrix.mul_assoc,
      hPS, Matrix.one_mul]
  have htr : (c.st π u).P.trace ≤ Bud.Lam d n := by
    have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le (S.hu' hu))
    rwa [inv_inv, S.de_c] at this
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [hsq]; exact htr

/-- `|ĝ_u| ≤ 1.01 Ȳ Λ^{1/2} Ξ` for `u ≤ s`. -/
theorem ghat_le (S : Sett d n c δ π s st ξ') {u : ℕ} (hu : u ≤ s) :
    oNorm (c.ghat π u) ≤ 101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n := by
  have hl0 := S.lam_pos; have hl1 := S.lam_small
  have hp : c.p.lam = (po d n).lam := by rw [S.hp]
  have h1l : 0 < 1 - c.p.lam := by rw [hp]; linarith
  have hY := S.Y_le_u hu
  have hun : oNorm (c.u π u) ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi d n := by
    have e : c.u π u = ((c.st π u).P * (c.st π u).A) *ᵥ π.xi u := by
      unfold Df2Ctx.u Df2Ctx.w; rw [Matrix.mulVec_mulVec]
    rw [e]
    exact (oNorm_mulVec_le _ _).trans (mul_le_mul (S.opN_PA_u hu) (S.xi_le_u hu) (oNorm_nonneg _)
      (Real.sqrt_nonneg _))
  unfold Df2Ctx.ghat
  rw [oNorm_smul, abs_div, abs_of_pos h1l]
  have hinv : 1 / (1 - c.p.lam) ≤ 101 / 100 := by
    rw [div_le_iff₀ h1l, hp]; nlinarith
  have hY0 : 0 ≤ Bud.Yb d n := (abs_nonneg _).trans hY
  have hX0 : 0 ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi d n := mul_nonneg (Real.sqrt_nonneg _) (Bud.Xi_nonneg d n)
  calc |c.Y π u| / (1 - c.p.lam) * oNorm (c.u π u)
      = |c.Y π u| * (1 / (1 - c.p.lam)) * oNorm (c.u π u) := by ring
    _ ≤ Bud.Yb d n * (101 / 100) * (Real.sqrt (Bud.Lam d n) * Bud.Xi d n) :=
        mul_le_mul (mul_le_mul hY hinv (by positivity) hY0) hun (oNorm_nonneg _) (by positivity)
    _ = _ := by ring

/-- E11: `|Ĝ°_{s+1}| ≤ Ḡ`. -/
theorem Gn_le (S : Sett d n c δ π s st ξ') : oNorm (c.Gn π s) ≤ Bud.Gb d n := by
  rw [S.det.Gn_sum S.hs']
  refine (AdversarialBco.Poly.oNorm_sum_le' _ _).trans ?_
  refine (Finset.sum_le_sum fun u hu => S.ghat_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have h0 : 0 ≤ 101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n := by
    have := (abs_nonneg _).trans (S.Y_le_u le_rfl)
    have := Bud.Xi_nonneg d n
    positivity
  unfold Bud.Gb
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n)
      ≤ n * (101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n) := mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

/-- E11: `|l°_{s+1}| ≤ R Ḡ`. -/
theorem ln_le (S : Sett d n c δ π s st ξ') : |c.ln π s| ≤ Bud.R d n * Bud.Gb d n := by
  have hI := S.inv
  have e : c.ln π s = ∑ u ∈ Finset.range (s + 1), c.ghat π u ⬝ᵥ (c.st π u).mu := by
    unfold Df2Ctx.ln; rw [hI.l, Finset.sum_range_succ]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ u ∈ Finset.range (s + 1), |c.ghat π u ⬝ᵥ (c.st π u).mu| ≤
      101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n * Bud.R d n := by
    intro u hu
    have hu' : u ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    have hmu : oNorm (c.st π u).mu ≤ Bud.R d n := by
      have := S.det.norm_le_of_keps (S.det.stInv_le_tau u (S.hu' hu')).mu
      rwa [S.hp] at this
    exact (abs_dot_le _ _).trans (mul_le_mul (S.ghat_le hu') hmu (oNorm_nonneg _)
      ((oNorm_nonneg _).trans (S.ghat_le hu')))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have hR : 0 ≤ Bud.R d n := by
    have := S.det.norm_le_of_keps S.inv.mu; rw [S.hp] at this; exact (oNorm_nonneg _).trans this
  have h0 : 0 ≤ 101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n * Bud.R d n := by
    have := (abs_nonneg _).trans (S.Y_le_u le_rfl)
    have := Bud.Xi_nonneg d n
    positivity
  unfold Bud.Gb
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n * Bud.R d n)
      ≤ n * (101 / 100 * Bud.Yb d n * Real.sqrt (Bud.Lam d n) * Bud.Xi d n * Bud.R d n) :=
        mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

end Sett

/-! ## The centre of P°'s test: `|b' - (η/2) Ĝ'| ≤ R/δe²` (the bound inside `not_gdZ`) -/

open AdversarialBco.Poly.Layer2 (z_arith) in
theorem wn_le {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ} (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    oNorm (c.bn π s - (c.p.eta / 2) • c.Gn π s) ≤ c.p.R / c.p.δe ^ 2 := by
  have hde := H.rows.pos_de
  have hek := H.kap_pos
  have hη := H.rows.pos_eta
  have hR1 := H.rows.one_le_R
  have hb : oNorm (c.bn π s) ≤ c.p.R / (4 * c.p.δe ^ 2) := by
    rw [H.bn_sum hs]
    refine (AdversarialBco.Poly.oNorm_sum_le' _ _).trans ?_
    have hterm : ∀ u ∈ Finset.range (s + 1), oNorm (((c.p.eta * c.p.kap) • c.shh π u) *ᵥ (c.st π u).mu) ≤
        c.p.eta * c.p.kap * c.Mone * c.p.R := by
      intro u hu
      have hut : u ≤ c.tau π m := by have := Finset.mem_range.1 hu; omega
      rw [smul_mulVec, AdversarialBco.Poly.oNorm_smul', abs_of_pos hek]
      have h1 := (H.shh_norm hut _).trans (mul_le_mul_of_nonneg_left
        (H.norm_le_of_keps (H.stInv_le_tau u hut).mu) H.Mone_nonneg)
      have := mul_le_mul_of_nonneg_left h1 hek.le
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := H.grad_arith'.1
    have h2 : ((s + 1 : ℕ) : ℝ) ≤ c.n := H.n_ge hs
    have hM := H.Mone_nonneg
    calc ((s + 1 : ℕ) : ℝ) * (c.p.eta * c.p.kap * c.Mone * c.p.R)
        ≤ c.n * (c.p.eta * c.p.kap * c.Mone) * c.p.R := by
          rw [← mul_assoc, ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ 1 / (4 * c.p.δe ^ 2) * c.p.R := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = _ := by ring
  have hG : c.p.eta / 2 * oNorm (c.Gn π s) ≤ 3 / 4 * c.p.R / c.p.δe ^ 2 := by
    rw [H.Gn_sum hs]
    have h1 : oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u) ≤
        c.n * (c.p.Le / (2 * c.p.eps) * Real.sqrt c.p.k0 * Real.sqrt (c.Xg / c.p.δe)) := by
      refine (AdversarialBco.Poly.oNorm_sum_le' _ _).trans ((Finset.sum_le_sum fun u hu => H.ghat_norm
        (by have := Finset.mem_range.1 hu; omega)).trans ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (H.n_ge hs) (by have := H.rows.pos_eps; have := H.Le_pos; positivity)
    have hz := z_arith c.p.eta c.p.Le c.p.eps c.p.k0 c.Xg c.p.δe c.n d (Real.log (1 / c.p.δe)) c.p.R hη
      H.rows.eta_le hR1 H.rows.pos_eps H.rows.r14 (by exact_mod_cast H.hn) (by exact_mod_cast H.hd)
      (by linarith [H.x_ge]) H.k0_pos hde rfl H.Le_eq (by have := H.rows.cz; simp only [df2C0] at this; exact this)
    calc c.p.eta / 2 * oNorm (∑ u ∈ Finset.range (s + 1), c.ghat π u)
        ≤ c.p.eta / 2 * (c.n * (c.p.Le / (2 * c.p.eps) * Real.sqrt c.p.k0 * Real.sqrt (c.Xg / c.p.δe))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := hz
  refine (AdversarialBco.Poly.oNorm_sub_le' _ _).trans ?_
  rw [AdversarialBco.Poly.oNorm_smul', abs_of_pos (by positivity)]
  have : c.p.R / (4 * c.p.δe ^ 2) + 3 / 4 * c.p.R / c.p.δe ^ 2 = c.p.R / c.p.δe ^ 2 := by field_simp; ring
  linarith

/-! ## BL's regions against `K_ε` -/

/-- The region of a call built by `callOf`, read in `ℝ^d`. -/
theorem region_callOf (cfg : Cfg d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (y : Fin d → ℝ) :
    y ∈ (callOf cfg H g ℓ r P f e).region ↔
      (∀ i, cV (cfg.α i) ⬝ᵥ y ≤ (1 - (cfg.par.eps : ℝ)) * cfg.β i) ∧ df2Phi (cM H) (cV g) 0 y ≤ ℓ ∧
        oNorm y ≤ cfg.par.Rint := by
  unfold CallQ.region callOf df2Phi
  simp only [Set.mem_setOf_eq]
  push_cast
  have e1 : y ⬝ᵥ (H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (g j : ℝ)) ⬝ᵥ y =
      1 / 2 * (y ⬝ᵥ (cM H *ᵥ y)) - cV g ⬝ᵥ y + 0 := by unfold cM cV; ring
  rw [e1]; rfl

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

/-- The rows of `K~` lie in `B_R` (`PgGood`). -/
theorem rows_norm (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ}
    (hy : ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (cfgOf R d n m A b cs).β i) : oNorm y ≤ Bud.R d n := by
  have hK := (H.rows y).1 hy
  obtain ⟨P, hP, -, -, hsub, -⟩ := H.pg
  simp only [Option.some.injEq] at hP
  subst hP
  have := hsub (show WithLp.toLp 2 y ∈ posBody (polytope A b) (pgMu (posR R d n m A b cs))
    (pgOp (posR R d n m A b cs)) from hK)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  rw [oNorm_eq]; exact this

theorem eps_lt (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Bud.eps d n ≤ ((par d n).eps : ℝ) ∧ ((par d n).eps : ℝ) ≤ 1 / 2 ∧ Bud.eps d n ≤ 1 / 4 ∧ 0 < Bud.eps d n :=
  ⟨H.bud.enc.eps_le, H.eps'_le, H.sett.eps_le, H.sett.eps_pos⟩

/-- BL's rows at the level `1 - ε'` lie in `K_ε`. -/
theorem keps_of_rows (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ}
    (hy : ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i) :
    y ∈ (ctx R d n m A b cs ap).Keps := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have h1 : 0 < 1 - Bud.eps d n := by linarith
  have hz : ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ ((1 - Bud.eps d n)⁻¹ • y) ≤ (cfgOf R d n m A b cs).β i := by
    intro i
    rw [dotProduct_smul, smul_eq_mul]
    have hb := H.bpos i
    have hbr : (0 : ℝ) < ((cfgOf R d n m A b cs).β i : ℝ) := by exact_mod_cast hb
    rw [inv_mul_le_iff₀ h1]
    refine (hy i).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hbr.le
  show WithLp.toLp 2 ((1 - (ctx R d n m A b cs ap).p.eps)⁻¹ • y) ∈ (ctx R d n m A b cs ap).Kt
  show WithLp.toLp 2 ((1 - Bud.eps d n)⁻¹ • y) ∈ kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)
  rw [kTh_good H.pg]
  refine ⟨(H.rows _).1 hz, ?_⟩
  rw [← oNorm_eq]; exact H.rows_norm hz

/-- `κ K_ε` lies in BL's rows at the level `1 - ε'`, `κ = (1 - ε')/(1 - ε)`. -/
theorem rows_of_keps (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ}
    (hy : y ∈ (ctx R d n m A b cs ap).Keps) (i : Fin (cfgOf R d n m A b cs).m) :
    cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ (((1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n)) • y) ≤
      (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hy' : WithLp.toLp 2 ((1 - Bud.eps d n)⁻¹ • y) ∈
      kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs) := hy
  rw [kTh_good H.pg] at hy'
  have hr := (H.rows _).2 hy'.1 i
  have e : ((1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n)) • y =
      (1 - ((par d n).eps : ℝ)) • ((1 - Bud.eps d n)⁻¹ • y) := by rw [smul_smul, div_eq_mul_inv]
  rw [e, dotProduct_smul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hr (by linarith)

theorem keps_norm (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ}
    (hy : y ∈ (ctx R d n m A b cs ap).Keps) : oNorm y ≤ Bud.R d n :=
  H.det.norm_le_of_keps hy

theorem R_le_Rint (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Bud.R d n ≤ (((cfgOf R d n m A b cs).par.Rint : ℕ) : ℝ) := by
  refine H.bud.enc.R_le.trans ?_
  show (((par d n).R : ℚ) : ℝ) ≤ ((⌈(par d n).R⌉₊ : ℕ) : ℝ)
  have := Nat.le_ceil (par d n).R
  exact_mod_cast this

theorem R_ge (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 1 ≤ Bud.R d n := by
  have := H.det.rows.one_le_R; exact this

end RCHyp

/-! ## E12: BL's quadratics against P°'s -/

/-- `e_Φ` from its three parts, for `k ≤ n` rounds of the fields. -/
theorem ePhi_ge {d n : ℕ} (R DP eb ek a k : ℝ) (hR : R = Bud.R d n) (hR0 : 0 ≤ R) (hDP : DP = Bud.DP d n)
    (heb : eb = Bud.eb d n) (hek : ek = Bud.ek d n) (heb0 : 0 ≤ eb) (hek0 : 0 ≤ ek) (ha : a ≤ k * eb)
    (hk : k ≤ n) (hP : 0 ≤ DP) {x y z : ℝ} (hx : x ≤ DP) (hy : y ≤ a) (hz : z ≤ k * ek) :
    R ^ 2 / 2 * x + R * y + z ≤ Bud.ePhi d n := by
  unfold Bud.ePhi
  rw [← hR, ← hDP, ← heb, ← hek]
  have h1 : R ^ 2 / 2 * x ≤ R ^ 2 / 2 * DP := mul_le_mul_of_nonneg_left hx (by positivity)
  have h2 : R * y ≤ R * (n * eb) := mul_le_mul_of_nonneg_left (hy.trans (ha.trans
    (mul_le_mul_of_nonneg_right hk heb0))) hR0
  have h3 : z ≤ n * ek := hz.trans (mul_le_mul_of_nonneg_right hk hek0)
  nlinarith

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem eb0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.eb d n := by
  have h := H.errb
  have h0 := oNorm_nonneg (cV (rvH R d n m A b cs st ξ' ζ' f).b - (ctx R d n m A b cs ap).bn π s)
  have hs : (0 : ℝ) < s + 1 := by positivity
  by_contra hc; push_neg at hc; nlinarith

theorem ek0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.ek d n := by
  have h := H.errk
  have h0 := abs_nonneg ((((rvH R d n m A b cs st ξ' ζ' f).k : ℚ) : ℝ) - (ctx R d n m A b cs ap).kn π s)
  have hs : (0 : ℝ) < s + 1 := by positivity
  by_contra hc; push_neg at hc; nlinarith

theorem DP0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.DP d n := by
  have := H.hb0; have := H.sett.Lam_pos; unfold Bud.DP; positivity

/-- E12 at round `s` (BL's state before the round against P°'s `Φ°_s`). -/
theorem phi_err_s (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ} (hy : oNorm y ≤ Bud.R d n) :
    |df2Phi (cM st.B * (cM st.B)ᵀ) (cV st.b) st.k y -
      df2Phi ((ctx R d n m A b cs ap).st π s).P ((ctx R d n m A b cs ap).st π s).b
        ((ctx R d n m A b cs ap).st π s).k y| ≤ Bud.ePhi d n := by
  have S := H.sett
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) ≤ n := by exact_mod_cast H.hs.le
  exact ePhi_ge _ _ _ _ _ (s : ℝ) rfl H.R0 rfl rfl rfl H.eb0 H.ek0 le_rfl hs H.DP0 H.P'_err.1 S.track.errb
    S.track.errk

/-- BL's `P'_+ = B'_+ B'_+ᵀ` against P°'s `P'`. -/
theorem Pp_err (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s) :
    opN (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ -
        (ctx R d n m A b cs ap).Pn π s) ≤ Bud.DP d n ∧
      opN (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ) ≤
        10201 / 10000 * Bud.Lam d n := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  set c := ctx R d n m A b cs ap
  have e : cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ =
      (1 + H0) * c.Pn π s * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * (c.Pn π s * c.An π s) * ((c.Pn π s * c.An π s)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * ((c.Pn π s * c.An π s) * (c.Pn π s * c.An π s)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PnAn_sq]
  have hPn : opN (c.Pn π s) ≤ Bud.Lam d n := by
    have h := opN_mul_le (c.Pn π s * c.An π s) (c.Pn π s * c.An π s)ᵀ
    rw [S.PnAn_sq, opN_transpose] at h
    have h2 := S.opN_PnAn
    have h0 := opN_nonneg (c.Pn π s * c.An π s)
    have : Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n) = Bud.Lam d n := Real.mul_self_sqrt S.Lam_pos.le
    nlinarith
  rw [e]
  have hb := H.bud.hb_le
  have hb0 := H.hb0
  have hT : Bud.hTr d n (s + 1) ≤ Bud.hb d n := H.bud.hTr_le (s + 1) H.hs
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans hT) hPn
  refine ⟨h1.trans (le_of_eq (by unfold Bud.DP; ring)), h2.trans ?_⟩
  have : (1 + Bud.hb d n) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

/-- E12 at round `s + 1` (BL's new fields against P°'s `Φ'`). -/
theorem phi_err_n (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ Bud.R d n) :
    |df2Phi (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ)
        (cV (rvH R d n m A b cs st ξ' ζ' f).b) (rvH R d n m A b cs st ξ' ζ' f).k y -
      (ctx R d n m A b cs ap).PhiN π s y| ≤ Bud.ePhi d n := by
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) + 1 ≤ n := by exact_mod_cast H.hs
  exact ePhi_ge _ _ _ _ _ ((s : ℝ) + 1) rfl H.R0 rfl rfl rfl H.eb0 H.ek0 le_rfl hs H.DP0 (H.Pp_err O).1 O.errb O.errk

end RCHyp

/-! ## E14: the Hausdorff gap of a region, packaged -/

/-- The gap for the region `{y ∈ K_ε : Φ°(y) ≤ L}` of P°'s convex quadratic `Φ°`, the anchor
`y₀` at depth `2` and BL's region `Q'`, which holds every point of the shrunk rows where `Φ° ≤ L - D`: every point
of P°'s region is within `h` of `Q'`, and a ball of P°'s region gives one of half its radius times `κ` in `Q'`. -/
theorem gap_pack {d : ℕ} (Ke Ke' Q' : Set (Fin d → ℝ)) (P : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (k : ℝ)
    (hP : Pᵀ = P) (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (P *ᵥ v)) (R κ L D E1 GR h : ℝ) (y0 : Fin d → ℝ)
    (hKe : Convex ℝ Ke) (hR : ∀ y ∈ Ke, oNorm y ≤ R) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hK' : ∀ y ∈ Ke, κ • y ∈ Ke') (hgrad : ∀ z, oNorm z ≤ R → oNorm (P *ᵥ z - b) ≤ GR)
    (hy0 : y0 ∈ Ke) (hΦ0 : df2Phi P b k y0 ≤ L - 2) (hD : 0 ≤ D) (hE1 : E1 = GR * R * (1 - κ))
    (hh : 2 * R * ((D + E1) / 2) + (1 - κ) * R ≤ h) (hhR : h ≤ R) (hR1 : 0 < R)
    (hQ' : ∀ y ∈ Ke', df2Phi P b k y ≤ L - D → y ∈ Q') :
    (∀ y ∈ Ke, df2Phi P b k y ≤ L → ∃ y' ∈ Q', oNorm (y - y') ≤ h) ∧
      ∀ (c : Fin d → ℝ) (r : ℝ), 0 ≤ r → oBall c r ⊆ {y | y ∈ Ke ∧ df2Phi P b k y ≤ L} →
        ∃ c' : Fin d → ℝ, oBall c' (κ * r / 2) ⊆ Q' := by
  have hGR : 0 ≤ GR := by
    have := hgrad 0 (by rw [oNorm_eq]; simp; exact hR1.le)
    exact (oNorm_nonneg _).trans this
  have hE10 : 0 ≤ E1 := by rw [hE1]; have : 0 ≤ 1 - κ := by linarith
                           positivity
  set σ := (D + E1) / 2 with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hσ1 : σ ≤ 1 / 2 := by
    have h1 : 0 ≤ (1 - κ) * R := mul_nonneg (by linarith) hR1.le
    have h2 : 2 * R * σ ≤ R := by linarith
    nlinarith
  have hconv := phi_convexOn P hP hpsd b k Ke hKe
  have hmap := gap_map Ke Ke' Q' (df2Phi P b k) R κ σ L 2 D E1 y0 hKe hR hκ0.le hκ1 hσ0 (by linarith) hK' hconv hy0
    hΦ0 (fun y hy => by rw [hE1]; exact phi_scale P hP hpsd b k R GR κ y hgrad (hR y hy) hκ0.le hκ1) (by
      rw [hσ]; linarith) hQ'
  refine ⟨fun y hy hyL => ⟨_, (hmap y hy hyL).1, (hmap y hy hyL).2.trans hh⟩, fun c r hr hb => ?_⟩
  refine ⟨κ • ((1 - σ) • c + σ • y0), fun x hx => ?_⟩
  refine gap_ball {y | y ∈ Ke ∧ df2Phi P b k y ≤ L} Q' κ σ r c y0 hκ0 (by linarith) hr
    (fun y hy => (hmap y hy.1 hy.2).1) hb ?_
  have hx' : oNorm (x - κ • ((1 - σ) • c + σ • y0)) ≤ κ * r / 2 := hx
  show oNorm (x - κ • ((1 - σ) • c + σ • y0)) ≤ κ * (1 - σ) * r
  refine hx'.trans ?_
  have : 0 ≤ κ * r := mul_nonneg hκ0.le hr
  nlinarith

/-! ## BL's regions at a level against P°'s -/

/-- The region of a call of BL at the level `ℓ₀` for its quadratic `(H, g, k)`. -/
theorem region_callOf_k (cfg : Cfg d) (Hq : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ0 k r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (y : Fin d → ℝ) :
    y ∈ (callOf cfg Hq g (ℓ0 - k) r P f e).region ↔
      (∀ i, cV (cfg.α i) ⬝ᵥ y ≤ (1 - (cfg.par.eps : ℝ)) * cfg.β i) ∧ df2Phi (cM Hq) (cV g) k y ≤ ℓ0 ∧
        oNorm y ≤ cfg.par.Rint := by
  rw [region_callOf]
  unfold df2Phi
  push_cast
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, h3⟩

theorem LT_cast (P : Par) : ((LT P : ℚ) : ℝ) = 799 / 100 * (P.rho : ℝ) - (P.eHat : ℝ) := by
  unfold LT; push_cast; ring

theorem Lmu_cast (P : Par) : ((Lmu P : ℚ) : ℝ) = 8 * (P.rho : ℝ) - (P.eHat : ℝ) := by
  unfold Lmu; push_cast; ring

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem rho_pos (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 < Bud.rho d n := H.det.rows.pos_rho

theorem wr0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.wr d n := by
  have := H.rho_pos; have := Bud.tp_pos d n; unfold Bud.wr; positivity

/-- `ρ - w_ρ ≤ ρ' ≤ ρ` (the enclosure lemma). -/
theorem rho_enc (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ((par d n).rho : ℝ) ≤ Bud.rho d n ∧ Bud.rho d n - Bud.wr d n ≤ ((par d n).rho : ℝ) := by
  have hρ := H.rho_pos
  refine ⟨H.bud.enc.rho_le, ?_⟩
  have h := (abs_le.1 H.bud.enc.rho_rel).1
  have e : ((par d n).rho : ℝ) = (((par d n).rho : ℝ) / Bud.rho d n) * Bud.rho d n := by field_simp
  unfold Bud.wr
  rw [e]
  nlinarith

/-- The two levels of the test region: BL's `L_T = 7.99 ρ' - ê` against P°'s `(c₁ - γ) ρ`, with the drop
`D = e_Φ + ê + 8 w_ρ` of the gap. -/
theorem LT_lev (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ((LT (par d n) : ℚ) : ℝ) + Bud.ePhi d n ≤
        ((ctx R d n m A b cs ap).p.c1 - (ctx R d n m A b cs ap).p.gam) * (ctx R d n m A b cs ap).p.rho ∧
      ((ctx R d n m A b cs ap).p.c1 - (ctx R d n m A b cs ap).p.gam) * (ctx R d n m A b cs ap).p.rho -
          (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n) + Bud.ePhi d n ≤ ((LT (par d n) : ℚ) : ℝ) := by
  rw [LT_cast, H.det.c1, H.det.gam]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.bud.ePhi_le
  have h4 := H.wr0
  have e : ((par d n).eHat : ℝ) = Bud.eh d n := rfl
  rw [e]
  have e2 : (ctx R d n m A b cs ap).p.rho = Bud.rho d n := rfl
  rw [e2]
  constructor <;> nlinarith

/-- The two levels of line μ: BL's `L_μ = 8 ρ' - ê` against P°'s `c₁ ρ`. -/
theorem Lmu_lev (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ((Lmu (par d n) : ℚ) : ℝ) + Bud.ePhi d n ≤ (ctx R d n m A b cs ap).p.c1 * (ctx R d n m A b cs ap).p.rho ∧
      (ctx R d n m A b cs ap).p.c1 * (ctx R d n m A b cs ap).p.rho -
          (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n) + Bud.ePhi d n ≤ ((Lmu (par d n) : ℚ) : ℝ) := by
  rw [Lmu_cast, H.det.c1]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.bud.ePhi_le
  have h4 := H.wr0
  have e : ((par d n).eHat : ℝ) = Bud.eh d n := rfl
  rw [e]
  have e2 : (ctx R d n m A b cs ap).p.rho = Bud.rho d n := rfl
  rw [e2]
  constructor <;> nlinarith

/-- A point of BL's region of a call at the level `ℓ₀` is in `K_ε` and under P°'s level `L`. -/
theorem in_of_region (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 k r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ Bud.R d n → |df2Phi (cM Hq) (cV g) k y - df2Phi Po bo ko y| ≤ Bud.ePhi d n)
    (L : ℝ) (hL : (ℓ0 : ℝ) + Bud.ePhi d n ≤ L) {y : Fin d → ℝ}
    (hy : y ∈ (callOf (cfgOf R d n m A b cs) Hq g (ℓ0 - k) r P fq e).region) :
    y ∈ (ctx R d n m A b cs ap).Keps ∧ df2Phi Po bo ko y ≤ L := by
  obtain ⟨h1, h2, -⟩ := (region_callOf_k _ _ _ _ _ _ _ _ _ y).1 hy
  have hk := H.keps_of_rows h1
  have := (abs_le.1 (herr y (H.keps_norm hk))).1
  exact ⟨hk, by linarith⟩

/-- A point of the shrunk rows `K_ε'` under P°'s level `L - D` is in BL's region at the level `ℓ₀`. -/
theorem region_of_in (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 k r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ Bud.R d n → |df2Phi (cM Hq) (cV g) k y - df2Phi Po bo ko y| ≤ Bud.ePhi d n)
    (L D : ℝ) (hL : L - D + Bud.ePhi d n ≤ (ℓ0 : ℝ)) {y : Fin d → ℝ}
    (hy : ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i)
    (hΦ : df2Phi Po bo ko y ≤ L - D) :
    y ∈ (callOf (cfgOf R d n m A b cs) Hq g (ℓ0 - k) r P fq e).region := by
  have hk := H.keps_of_rows hy
  have hR := H.keps_norm hk
  have := (abs_le.1 (herr y hR)).2
  exact (region_callOf_k _ _ _ _ _ _ _ _ _ y).2 ⟨hy, by linarith, hR.trans H.R_le_Rint⟩

end RCHyp

/-! ## P°'s round after the first: the state and the anchor of the test region -/

/-- The state of round `s₀ + 1 ≤ τ` is the one `stNext` left at round `s₀`, and P°'s test point of round `s₀` has
`Φ'_{s₀}(pt) ≤ (c₁ - γ) ρ - 2` (Lemma IB2 (i)). -/
theorem prev_round {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ} (H : DetHyp c δ π m) {s0 : ℕ}
    (hs : s0 < c.tau π m) :
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

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem kap_props (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 < (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n) ∧ (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n) ≤ 1 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  exact ⟨div_pos (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

theorem ePhi0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.ePhi d n := by
  have := H.eb0; have := H.ek0; have := H.DP0; have := H.R0; unfold Bud.ePhi; positivity

theorem we0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.we d n := by
  have := H.sett.eps_pos; have := Bud.tp_pos d n; unfold Bud.we; positivity

/-- `h ≤ R`, and the gap `h` covers the move `(1 - κ) R` of the first round. -/
theorem h_props (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Bud.h d n ≤ Bud.R d n ∧ (1 - (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n)) * Bud.R d n ≤ Bud.h d n := by
  have hR1 := H.R_ge
  have hde := H.sett.de_pos
  have hde1 := H.det.rows.de_lt
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hwe := H.we0
  have hP := H.ePhi0
  have heh := H.bud.ePhi_le
  have hwr := H.wr0
  have hee' : ((par d n).eps : ℝ) ≤ Bud.eps d n + Bud.we d n := by
    have := H.bud.enc.eps_rel; unfold Bud.we; nlinarith
  constructor
  · have h1 := H.bud.h_le
    have h2 : Bud.rmin d n ≤ 1 := by
      unfold Bud.rmin
      rw [div_le_one (by positivity)]
      change (po d n).δe ^ 2 ≤ _
      have hde1 : (po d n).δe < 1 := H.det.rows.de_lt
      nlinarith
    linarith
  · have e1 : 1 - (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n) =
        (((par d n).eps : ℝ) - Bud.eps d n) / (1 - Bud.eps d n) := by
      have hne : (1 - Bud.eps d n) ≠ 0 := by linarith
      field_simp; ring
    rw [e1]
    have h1 : (((par d n).eps : ℝ) - Bud.eps d n) / (1 - Bud.eps d n) ≤ 2 * Bud.we d n := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : 0 ≤ Bud.R d n * (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n) := by
      have := H.R0; have : 0 ≤ Bud.eh d n := by linarith
      positivity
    have h3 : 0 ≤ 2 * Bud.R d n ^ 3 * Bud.we d n / Bud.de d n ^ 2 := by have := H.R0; positivity
    unfold Bud.h
    nlinarith


/-- E14 for the test call: BL's test region lies in P°'s `R⁻_s`, every point of `R⁻_s` is within `h` of it, and it
holds a ball of BL's radius. -/
theorem gapT (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (r : RV d) :
    (∀ y ∈ (ctx R d n m A b cs ap).Rm π s, ∃ y' ∈ (callTQ (cfgOf R d n m A b cs) st r).region,
        oNorm (y - y') ≤ Bud.h d n) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callTQ (cfgOf R d n m A b cs) st r).r : ℝ) ⊆
        (callTQ (cfgOf R d n m A b cs) st r).region) ∧
      (callTQ (cfgOf R d n m A b cs) st r).region ⊆ (ctx R d n m A b cs ap).Rm π s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hR1 := H.R_ge
  have hRI := H.R_le_Rint
  have hinv := H.sett.inv
  have hfst := H.track.first
  set κ := (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n) with hκ
  by_cases hf : st.first = true
  · have hf' : ((ctx R d n m A b cs ap).st π s).first = true := hfst ▸ hf
    have hRm : (ctx R d n m A b cs ap).Rm π s = (ctx R d n m A b cs ap).Keps := by
      unfold Df2Ctx.Rm; rw [if_pos hf']
    have hcall : callTQ (cfgOf R d n m A b cs) st r = callOf (cfgOf R d n m A b cs) 0 0 0 (1 - (par d n).eps)
        (r.B * r.Bᵀ) (r.b - ((par d n).eta / 2) • r.G) ((1 - (par d n).eps) ^ 2 / ((par d n).Ne * d * 8)) := by
      unfold callTQ; rw [if_pos hf]; rfl
    have hreg : ∀ y, y ∈ (callTQ (cfgOf R d n m A b cs) st r).region ↔
        (∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i) ∧
          oNorm y ≤ (((cfgOf R d n m A b cs).par.Rint : ℕ) : ℝ) := by
      intro y
      rw [hcall, region_callOf]
      have e : df2Phi (cM (0 : Matrix (Fin d) (Fin d) ℚ)) (cV 0) 0 y = 0 := by
        unfold df2Phi; rw [cV_zero]; simp [cM]
      rw [e]
      push_cast
      simp only [le_refl, true_and]
      rfl
    rw [hRm]
    refine ⟨fun y hy => ⟨κ • y, (hreg _).2 ⟨H.rows_of_keps hy, ?_⟩, ?_⟩, ⟨0, fun y hy => ?_⟩,
      fun y hy => H.keps_of_rows ((hreg y).1 hy).1⟩
    · rw [oNorm_smul, abs_of_pos hκ0]
      have := H.keps_norm hy
      have := oNorm_nonneg y
      nlinarith
    · have e : y - κ • y = (1 - κ) • y := by rw [sub_smul, one_smul]
      rw [e, oNorm_smul, abs_of_nonneg (by linarith)]
      have := H.keps_norm hy
      have : (1 - κ) * oNorm y ≤ (1 - κ) * Bud.R d n := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    · have hr : ((callTQ (cfgOf R d n m A b cs) st r).r : ℝ) = 1 - ((par d n).eps : ℝ) := by
        rw [hcall]; simp [callOf]
      have hy' : oNorm y ≤ 1 - ((par d n).eps : ℝ) := by
        have h0 : oNorm (y - 0) ≤ ((callTQ (cfgOf R d n m A b cs) st r).r : ℝ) := hy
        rwa [sub_zero, hr] at h0
      have hz : κ⁻¹ • y ∈ (ctx R d n m A b cs ap).Keps := by
        apply H.det.keps.2.2.1
        show oNorm (κ⁻¹ • y - 0) ≤ 1 - Bud.eps d n
        rw [sub_zero, oNorm_smul, abs_of_pos (inv_pos.2 hκ0), hκ, inv_div, div_mul_eq_mul_div,
          div_le_iff₀ (by linarith)]
        have := oNorm_nonneg y
        nlinarith
      have hrows : ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i := by
        intro i
        have := H.rows_of_keps hz i
        rwa [← hκ, smul_smul, mul_inv_cancel₀ hκ0.ne', one_smul] at this
      refine (hreg y).2 ⟨hrows, ?_⟩
      linarith
  · have hf' : ((ctx R d n m A b cs ap).st π s).first = false := by
      rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctx R d n m A b cs ap).tau π (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨pt, hpt, hlev, hP, hb, hk, hrs⟩ := prev_round H.det hlt
    have hRm : (ctx R d n m A b cs ap).Rm π (s0 + 1) = {y | y ∈ (ctx R d n m A b cs ap).Keps ∧
        df2Phi ((ctx R d n m A b cs ap).st π (s0 + 1)).P ((ctx R d n m A b cs ap).st π (s0 + 1)).b
          ((ctx R d n m A b cs ap).st π (s0 + 1)).k y ≤
        ((ctx R d n m A b cs ap).p.c1 - (ctx R d n m A b cs ap).p.gam) * (ctx R d n m A b cs ap).p.rho} := by
      unfold Df2Ctx.Rm; rw [if_neg (by rw [hf']; decide)]
    have hcall : callTQ (cfgOf R d n m A b cs) st r = callOf (cfgOf R d n m A b cs) (st.B * st.Bᵀ) st.b
        (LT (par d n) - st.k) (rB (par d n) / 2) (r.B * r.Bᵀ) (r.b - ((par d n).eta / 2) • r.G)
        (rB (par d n) ^ 2 / ((par d n).Ne * d * 8)) := by
      unfold callTQ; rw [if_neg hf]; rfl
    have herr : ∀ y, oNorm y ≤ Bud.R d n → |df2Phi (cM (st.B * st.Bᵀ)) (cV st.b) st.k y -
        df2Phi ((ctx R d n m A b cs ap).st π (s0 + 1)).P ((ctx R d n m A b cs ap).st π (s0 + 1)).b
          ((ctx R d n m A b cs ap).st π (s0 + 1)).k y| ≤ Bud.ePhi d n := by
      intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_s hy
    have hpsd : ∀ v, 0 ≤ v ⬝ᵥ (((ctx R d n m A b cs ap).st π (s0 + 1)).P *ᵥ v) :=
      fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd hinv.pd.posSemidef v
    have hgrad : ∀ z, oNorm z ≤ Bud.R d n → oNorm (((ctx R d n m A b cs ap).st π (s0 + 1)).P *ᵥ z -
        ((ctx R d n m A b cs ap).st π (s0 + 1)).b) ≤ Bud.R d n / Bud.de d n ^ 2 := by
      intro z hz; rw [hP, hb]; exact H.det.grad_le (s := s0) (by rw [H.tau]; omega) hz
    have hD : 0 ≤ Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n := by
      have := H.ePhi0; have := H.bud.ePhi_le; have := H.wr0; linarith
    have hee' : ((par d n).eps : ℝ) ≤ Bud.eps d n + Bud.we d n := by
      have := H.bud.enc.eps_rel; unfold Bud.we; nlinarith
    have hh : 2 * Bud.R d n * ((Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n +
        Bud.R d n / Bud.de d n ^ 2 * Bud.R d n * (1 - κ)) / 2) + (1 - κ) * Bud.R d n ≤ Bud.h d n := by
      have := gap_disp (Bud.R d n) (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n)
        (Bud.R d n / Bud.de d n ^ 2 * Bud.R d n * (1 - κ)) κ (Bud.eps d n) ((par d n).eps) (Bud.we d n)
        (Bud.de d n) (Bud.R d n / Bud.de d n ^ 2) H.R0 hD H.sett.de_pos he0 (by linarith) he hee' rfl rfl rfl
      unfold Bud.h; linarith
    obtain ⟨hA, hB⟩ := gap_pack (ctx R d n m A b cs ap).Keps
      {y | ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i}
      (callTQ (cfgOf R d n m A b cs) st r).region ((ctx R d n m A b cs ap).st π (s0 + 1)).P
      ((ctx R d n m A b cs ap).st π (s0 + 1)).b ((ctx R d n m A b cs ap).st π (s0 + 1)).k H.sett.P_sym hpsd
      (Bud.R d n) κ (((ctx R d n m A b cs ap).p.c1 - (ctx R d n m A b cs ap).p.gam) * (ctx R d n m A b cs ap).p.rho)
      (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n) _ (Bud.R d n / Bud.de d n ^ 2) (Bud.h d n) pt H.det.keps.1
      (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.rows_of_keps hy) hgrad hpt
      (by rw [hP, hb, hk]; exact hlev) hD rfl hh hhR (by linarith)
      (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.LT_lev.2 hy hΦ)
    have hgood := H.det.good (s0 + 1) H.sett.hs'
    rw [hRm] at hgood ⊢
    refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
    · obtain ⟨c', hc'⟩ := hB _ _ hgood.2.2.le hgood.2.1
      refine ⟨c', fun y hy => hc' ?_⟩
      have hr : ((callTQ (cfgOf R d n m A b cs) st r).r : ℝ) ≤
          κ * ((ctx R d n m A b cs ap).st π (s0 + 1)).r / 2 := by
        rw [hcall, hrs]
        have e : κ * ((ctx R d n m A b cs ap).p.sb * (1 - (ctx R d n m A b cs ap).p.eps)) / 2 =
            (po d n).sb * (1 - ((par d n).eps : ℝ)) / 2 := by
          rw [hκ]; change _ / (1 - (po d n).eps) * ((po d n).sb * (1 - (po d n).eps)) / 2 = _
          have : 1 - (po d n).eps ≠ 0 := by change 1 - Bud.eps d n ≠ 0; linarith
          field_simp
        rw [e]
        simp only [callOf, rB]
        push_cast
        have := H.bud.enc.sb_le
        have : 0 ≤ 1 - ((par d n).eps : ℝ) := by linarith
        nlinarith
      exact le_trans hy hr
    · rw [hcall] at hy
      exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.LT_lev.1 hy


/-- E14 for line μ, at a round that does not fire with P°'s test point `pt`: BL's region of line μ lies in P°'s
`R⁺_s`, every point of `R⁺_s` is within `h` of it, and it holds a ball of BL's radius. -/
theorem gapM (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctx R d n m A b cs ap).Rm π s)
    (hXi : ¬ (ctx R d n m A b cs ap).Xi π s pt ≤ -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho)) :
    (∀ y ∈ (ctx R d n m A b cs ap).Rp π s, ∃ y' ∈ (callMQ (cfgOf R d n m A b cs) n st ξ'
        (rvH R d n m A b cs st ξ' ζ' f)).region, oNorm (y - y') ≤ Bud.h d n) ∧
      (∃ c' : Fin d → ℝ, oBall c' ((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).r : ℝ) ⊆
        (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region) ∧
      (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region ⊆
        (ctx R d n m A b cs ap).Rp π s := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hκ0, hκ1⟩ := H.kap_props
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hR1 := H.R_ge
  set κ := (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n) with hκ
  set r := rvH R d n m A b cs st ξ' ζ' f with hr
  have hs := H.sett.hs'
  have hcall : callMQ (cfgOf R d n m A b cs) n st ξ' r = callOf (cfgOf R d n m A b cs) (r.B * r.Bᵀ) r.b
      (Lmu (par d n) - r.k) (rB (par d n) / 2) (r.B * r.Bᵀ) ((r.B * r.Bᵀ) *ᵥ wmuQ (cfgOf R d n m A b cs) st ξ' r)
      (eBL (par d n) d n) := rfl
  have herr : ∀ y, oNorm y ≤ Bud.R d n → |df2Phi (cM (r.B * r.Bᵀ)) (cV r.b) r.k y -
      df2Phi ((ctx R d n m A b cs ap).Pn π s) ((ctx R d n m A b cs ap).bn π s)
        ((ctx R d n m A b cs ap).kn π s) y| ≤ Bud.ePhi d n := by
    intro y hy; rw [cM_mul, cM_transpose]; exact H.phi_err_n O hy
  have hpsd : ∀ v, 0 ≤ v ⬝ᵥ ((ctx R d n m A b cs ap).Pn π s *ᵥ v) :=
    fun v => AdversarialBco.Poly.Layer2.sq_nonneg_of_psd (H.det.r1_le_tau hs).1.posSemidef v
  have hgrad : ∀ z, oNorm z ≤ Bud.R d n → oNorm ((ctx R d n m A b cs ap).Pn π s *ᵥ z -
      (ctx R d n m A b cs ap).bn π s) ≤ Bud.R d n / Bud.de d n ^ 2 := fun z hz => H.det.grad_le hs hz
  have hD : 0 ≤ Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n := by
    have := H.ePhi0; have := H.bud.ePhi_le; have := H.wr0; linarith
  have hee' : ((par d n).eps : ℝ) ≤ Bud.eps d n + Bud.we d n := by
    have := H.bud.enc.eps_rel; unfold Bud.we; nlinarith
  have hh : 2 * Bud.R d n * ((Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n +
      Bud.R d n / Bud.de d n ^ 2 * Bud.R d n * (1 - κ)) / 2) + (1 - κ) * Bud.R d n ≤ Bud.h d n := by
    have := gap_disp (Bud.R d n) (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n)
      (Bud.R d n / Bud.de d n ^ 2 * Bud.R d n * (1 - κ)) κ (Bud.eps d n) ((par d n).eps) (Bud.we d n)
      (Bud.de d n) (Bud.R d n / Bud.de d n ^ 2) H.R0 hD H.sett.de_pos he0 (by linarith) he hee' rfl rfl rfl
    unfold Bud.h; linarith
  have hP : ∀ u < s, (ctx R d n m A b cs ap).ProjOK π u := fun u hu => H.det.projOK (by rw [H.tau]; omega)
  have hlev := H.det.ib2_level hs hP hpt hXi
  have hlev' : (ctx R d n m A b cs ap).PhiN π s pt ≤
      (ctx R d n m A b cs ap).p.c1 * (ctx R d n m A b cs ap).p.rho - 2 := by
    have := H.rho_pos; have := H.det.gam
    have h0 : 0 ≤ (ctx R d n m A b cs ap).p.gam * (ctx R d n m A b cs ap).p.rho := by
      rw [this]; have : 0 < (ctx R d n m A b cs ap).p.rho := H.rho_pos; positivity
    linarith
  obtain ⟨hA, hB⟩ := gap_pack (ctx R d n m A b cs ap).Keps
    {y | ∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (1 - ((par d n).eps : ℝ)) * (cfgOf R d n m A b cs).β i}
    (callMQ (cfgOf R d n m A b cs) n st ξ' r).region ((ctx R d n m A b cs ap).Pn π s)
    ((ctx R d n m A b cs ap).bn π s) ((ctx R d n m A b cs ap).kn π s) H.sett.Pn_sym hpsd
    (Bud.R d n) κ ((ctx R d n m A b cs ap).p.c1 * (ctx R d n m A b cs ap).p.rho)
    (Bud.ePhi d n + Bud.eh d n + 8 * Bud.wr d n) _ (Bud.R d n / Bud.de d n ^ 2) (Bud.h d n) pt H.det.keps.1
    (fun y hy => H.keps_norm hy) hκ0 hκ1 (fun y hy => H.rows_of_keps hy) hgrad
    (H.det.Rm_sub_reg hs hpt).1 hlev' hD rfl hh hhR (by linarith)
    (fun y hy hΦ => by rw [hcall]; exact H.region_of_in _ _ _ _ _ _ _ _ _ _ _ herr _ _ H.Lmu_lev.2 hy hΦ)
  have hib := H.det.ib2 hs hP hpt hXi
  refine ⟨fun y hy => hA y hy.1 hy.2, ?_, fun y hy => ?_⟩
  · obtain ⟨c', hc'⟩ := hB _ _ H.det.rad_pos.le (fun y hy => H.det.RmN_sub_Rp s (hib hy))
    refine ⟨c', fun y hy => hc' ?_⟩
    have hr' : ((callMQ (cfgOf R d n m A b cs) n st ξ' r).r : ℝ) ≤
        κ * ((ctx R d n m A b cs ap).p.sb * (1 - (ctx R d n m A b cs ap).p.eps)) / 2 := by
      have e : κ * ((ctx R d n m A b cs ap).p.sb * (1 - (ctx R d n m A b cs ap).p.eps)) / 2 =
          (po d n).sb * (1 - ((par d n).eps : ℝ)) / 2 := by
        rw [hκ]; change _ / (1 - (po d n).eps) * ((po d n).sb * (1 - (po d n).eps)) / 2 = _
        have : 1 - (po d n).eps ≠ 0 := by change 1 - Bud.eps d n ≠ 0; linarith
        field_simp
      rw [e, hcall]
      simp only [callOf, rB]
      push_cast
      have := H.bud.enc.sb_le
      have : 0 ≤ 1 - ((par d n).eps : ℝ) := by linarith
      nlinarith
    exact le_trans hy hr'
  · rw [hcall] at hy
    exact H.in_of_region _ _ _ _ _ _ _ _ _ _ _ herr _ H.Lmu_lev.1 hy


theorem par_pos (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 < (par d n).sb ∧ (par d n).eps < 1 ∧ 0 < (par d n).Ne ∧ (1 : ℚ) ≤ (par d n).Rint ∧ 0 < (par d n).R := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hsb : 0 < (po d n).sb := by
    have e := H.det.sb
    change (po d n).sb = (po d n).δe ^ 2 / ((po d n).R * ((po d n).R + 1)) at e
    have := H.sett.de_pos; have : 1 ≤ (po d n).R := H.R_ge
    rw [e]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := (abs_le.1 H.bud.enc.sb_rel).1
    have htp := Bud.tp_small d n
    have h1 : 0 < ((par d n).sb : ℝ) / (po d n).sb := by linarith
    have h2 : (0 : ℝ) < (par d n).sb := by
      have := mul_pos h1 hsb; rwa [div_mul_cancel₀ _ hsb.ne'] at this
    exact_mod_cast h2
  · have : ((par d n).eps : ℝ) < 1 := by linarith
    exact_mod_cast this
  · have h1 := H.bud.enc.Ne_eq
    have h2 := H.bud.enc.de_eq
    have hde : 0 < Bud.de d n := H.sett.de_pos
    rw [h2] at hde
    have : (0 : ℝ) < ((par d n).Ne : ℝ) := by rw [h1]; exact one_div_pos.1 hde
    exact_mod_cast this
  · have h := H.R_le_Rint
    have h1 := H.R_ge
    have : (1 : ℝ) ≤ ((par d n).Rint : ℝ) := by
      have e : (((cfgOf R d n m A b cs).par.Rint : ℕ) : ℝ) = ((par d n).Rint : ℝ) := rfl
      linarith
    exact_mod_cast this
  · have := H.bud.enc.R_le; have := H.R_ge
    have : (0 : ℝ) < (par d n).R := by linarith
    exact_mod_cast this

/-- BL's `P'_+ = B'_+ B'_+ᵀ` is positive definite: `B'_+ = (I + H^B) P° A°` with `|H^B| < 1`. -/
theorem Pp_posDef (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s) :
    (((rvH R d n m A b cs st ξ' ζ' f).B * (rvH R d n m A b cs st ξ' ζ' f).Bᵀ).map ((↑) : ℚ → ℝ)).PosDef := by
  change (cM ((rvH R d n m A b cs st ξ' ζ' f).B * (rvH R d n m A b cs st ξ' ζ' f).Bᵀ)).PosDef
  rw [cM_mul, cM_transpose]
  apply posDef_mul_transpose
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  rw [hB0, Matrix.det_mul, Matrix.det_mul]
  have h1 : (1 + H0).det ≠ 0 := by
    apply det_one_add_ne
    have := H.bud.hTr_le (s + 1) H.hs
    have := H.bud.hb_le
    linarith
  have h2 : ((ctx R d n m A b cs ap).Pn π s).det * ((ctx R d n m A b cs ap).An π s).det ≠ 0 := by
    have h := congrArg Matrix.det H.sett.PnAn_inv
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  exact mul_ne_zero h1 h2

theorem gram_psd (B : Matrix (Fin d) (Fin d) ℚ) : ((B * Bᵀ).map ((↑) : ℚ → ℝ)).PosSemidef := by
  change (cM (B * Bᵀ)).PosSemidef
  rw [cM_mul, cM_transpose, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- (O3) at BL's test call: it returns a point of its region within its accuracy of the least objective. -/
theorem testCall (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    (hO3 : O3SpecQ R.ap) :
    ∃ p', R.ap (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)) = some p' ∧
      cV p' ∈ (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).region ∧
      ∀ x ∈ (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).region,
        (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).obj (cV p') ≤
          (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).obj x +
            ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapT (rvH R d n m A b cs st ξ' ζ' f)).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < ((par d n).Ne : ℚ) := by exact_mod_cast hNe
  have hP : ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).P.map ((↑) : ℚ → ℝ)).PosDef := by
    unfold callTQ; split <;> exact H.Pp_posDef O
  have hH : ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).H.map ((↑) : ℚ → ℝ)).PosSemidef := by
    unfold callTQ; split
    · show ((0 : Matrix (Fin d) (Fin d) ℚ).map ((↑) : ℚ → ℝ)).PosSemidef
      rw [Matrix.map_zero _ (by simp)]; exact Matrix.PosSemidef.zero
    · exact gram_psd st.B
  have hR : (1 : ℚ) ≤ (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).R := by
    unfold callTQ; split <;> exact hRint
  have hr : (0 : ℚ) < (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).r := by
    unfold callTQ; split
    · show 0 < 1 - (par d n).eps; linarith
    · show 0 < (par d n).sb * (1 - (par d n).eps) / 2
      have : 0 < 1 - (par d n).eps := by linarith
      positivity
  have he : (0 : ℚ) < (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e := by
    unfold callTQ; split
    · show 0 < (1 - (par d n).eps) ^ 2 / ((par d n).Ne * d * 8)
      have : 0 < 1 - (par d n).eps := by linarith
      positivity
    · show 0 < ((par d n).sb * (1 - (par d n).eps)) ^ 2 / ((par d n).Ne * d * 8)
      have : 0 < 1 - (par d n).eps := by linarith
      positivity
  exact hO3 d _ c' hR hr hball hP hH he

/-- (O3) at BL's call of line μ, at a round that does not fire with P°'s test point `pt`. -/
theorem muCall (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    (hO3 : O3SpecQ R.ap) {pt : Fin d → ℝ} (hpt : pt ∈ (ctx R d n m A b cs ap).Rm π s)
    (hXi : ¬ (ctx R d n m A b cs ap).Xi π s pt ≤ -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho)) :
    ∃ μ', R.ap (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)) = some μ' ∧
      cV μ' ∈ (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region ∧
      ∀ x ∈ (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region,
        (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).obj (cV μ') ≤
          (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).obj x +
            ((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) := by
  obtain ⟨c', hball⟩ := (H.gapM O hpt hXi).2.1
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have hNe' : (0 : ℚ) < ((par d n).Ne : ℚ) := by exact_mod_cast hNe
  have hr : (0 : ℚ) < (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).r := by
    show 0 < (par d n).sb * (1 - (par d n).eps) / 2
    have : 0 < 1 - (par d n).eps := by linarith
    positivity
  have he : (0 : ℚ) < (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e := by
    show 0 < 1 / ((par d n).Ne * (128 * (n : ℚ) ^ 2 * (par d n).R ^ 2 * d))
    positivity
  exact hO3 d _ c' hRint hr hball (H.Pp_posDef O) (H.Pp_posDef O).posSemidef he

end RCHyp

/-! ## E13: BL's test statistic against P°'s -/

/-- BL's test statistic `Xi'(y) = η'(l' - G'·y) - 2 Φ'(y)` read in `ℝ`. -/
noncomputable def xiB (cfg : Cfg d) (r : RV d) (y : Fin d → ℝ) : ℝ :=
  (cfg.par.eta : ℝ) * ((r.l : ℝ) - cV r.G ⬝ᵥ y) - 2 * df2Phi (cM r.B * (cM r.B)ᵀ) (cV r.b) r.k y

theorem fireQ_iff (cfg : Cfg d) (r : RV d) (p : Fin d → ℚ) :
    fireQ cfg r p ↔ xiB cfg r (cV p) ≤ -(cfg.par.rho : ℝ) + cfg.par.eHat := by
  unfold fireQ
  rw [← Rat.cast_le (K := ℝ)]
  have e : (((cfg.par.eta * (r.l - r.G ⬝ᵥ p) - 2 * (p ⬝ᵥ ((r.B * r.Bᵀ) *ᵥ p) / 2 - r.b ⬝ᵥ p + r.k)) : ℚ) : ℝ) =
      xiB cfg r (cV p) := by
    unfold xiB df2Phi
    push_cast
    simp only [cV_dot, cM_mulVec, cM_mul, cM_transpose]
    ring
  rw [e]; push_cast; rfl

/-- The objective of BL's test call, `yᵀP'_+y/2 - w'_+·y`. -/
theorem obj_T (cfg : Cfg d) (st : St d) (r : RV d) (y : Fin d → ℝ) :
    (callTQ cfg st r).obj y = y ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ y) / 2 -
      (cV r.b - ((cfg.par.eta : ℝ) / 2) • cV r.G) ⬝ᵥ y := by
  have e : ∀ D : CallQ d, D.P = r.B * r.Bᵀ → D.f = r.b - (cfg.par.eta / 2) • r.G →
      D.obj y = y ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ y) / 2 - (cV r.b - ((cfg.par.eta : ℝ) / 2) • cV r.G) ⬝ᵥ y := by
    intro D hP hf
    unfold CallQ.obj
    rw [hP, hf]
    change y ⬝ᵥ (cM (r.B * r.Bᵀ) *ᵥ y) / 2 - cV (r.b - (cfg.par.eta / 2) • r.G) ⬝ᵥ y = _
    rw [cM_mul, cM_transpose, cV_sub, cV_smul]
    push_cast; rfl
  unfold callTQ; split <;> exact e _ rfl rfl

/-- `Xi'(y) = η' l' - 2 k' - 2 obj(y)` (the expansion of BL's statistic). -/
theorem xiB_obj (cfg : Cfg d) (st : St d) (r : RV d) (y : Fin d → ℝ) :
    xiB cfg r y = (cfg.par.eta : ℝ) * r.l - 2 * r.k - 2 * (callTQ cfg st r).obj y := by
  rw [obj_T]
  unfold xiB df2Phi
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem eta_err (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |((par d n).eta : ℝ) - Bud.eta d n| ≤ Bud.tp d n / 16 * Bud.eta d n := by
  have hη : 0 < Bud.eta d n := H.det.rows.pos_eta
  have h := H.bud.enc.eta_rel
  have e : ((par d n).eta : ℝ) - Bud.eta d n = Bud.eta d n * (((par d n).eta : ℝ) / Bud.eta d n - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hη]
  nlinarith [abs_nonneg (((par d n).eta : ℝ) / Bud.eta d n - 1)]

/-- E13: `|Xi' - Xi°| ≤ e_X` on `B_R`. -/
theorem xi_E13 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ Bud.R d n) :
    |xiB (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) y - (ctx R d n m A b cs ap).Xi π s y| ≤
      Bud.eX d n := by
  have S := H.sett
  have hη : 0 < Bud.eta d n := H.det.rows.pos_eta
  have htp := Bud.tp_small d n
  have htp0 := (Bud.tp_pos d n).le
  have h1 := xi_err (Bud.eta d n) ((par d n).eta : ℝ) (Bud.tp d n) ((ctx R d n m A b cs ap).ln π s)
    ((rvH R d n m A b cs st ξ' ζ' f).l : ℝ) (Bud.R d n) (Bud.Gb d n) ((s + 1) * Bud.el d n) ((s + 1) * Bud.eg d n)
    ((ctx R d n m A b cs ap).Gn π s) (cV (rvH R d n m A b cs st ξ' ζ' f).G) y hη.le H.eta_err htp0 htp H.R0 hy
    S.ln_le S.Gn_le O.errl O.errG
  have h2 := H.phi_err_n O hy
  have hs : (s : ℝ) + 1 ≤ n := by exact_mod_cast H.hs
  have hel : 0 ≤ Bud.el d n := by
    have := O.errl; have := abs_nonneg (((rvH R d n m A b cs st ξ' ζ' f).l : ℝ) - (ctx R d n m A b cs ap).ln π s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push_neg at hc; nlinarith
  have heg : 0 ≤ Bud.eg d n := by
    have := O.errG; have := oNorm_nonneg (cV (rvH R d n m A b cs st ξ' ζ' f).G - (ctx R d n m A b cs ap).Gn π s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push_neg at hc; nlinarith
  have hR := H.R0
  have e : xiB (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) y - (ctx R d n m A b cs ap).Xi π s y =
      (((par d n).eta : ℝ) * (((rvH R d n m A b cs st ξ' ζ' f).l : ℝ) - cV (rvH R d n m A b cs st ξ' ζ' f).G ⬝ᵥ y) -
        Bud.eta d n * ((ctx R d n m A b cs ap).ln π s - (ctx R d n m A b cs ap).Gn π s ⬝ᵥ y)) -
      2 * (df2Phi (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ)
        (cV (rvH R d n m A b cs st ξ' ζ' f).b) (rvH R d n m A b cs st ξ' ζ' f).k y -
        (ctx R d n m A b cs ap).PhiN π s y) := by
    unfold xiB Df2Ctx.Xi
    change ((par d n).eta : ℝ) * _ - 2 * _ - (Bud.eta d n * _ - 2 * _) = _
    ring
  rw [e]
  have hA : (s + 1) * Bud.el d n ≤ n * Bud.el d n := mul_le_mul_of_nonneg_right hs hel
  have hB : Bud.R d n * ((s + 1) * Bud.eg d n) ≤ Bud.R d n * (n * Bud.eg d n) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs heg) hR
  have hAB : Bud.eta d n * (101 / 100) * ((s + 1) * Bud.el d n + Bud.R d n * ((s + 1) * Bud.eg d n)) ≤
      Bud.eta d n * (101 / 100) * (n * Bud.el d n + Bud.R d n * n * Bud.eg d n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  unfold Bud.eX
  have := abs_sub (((par d n).eta : ℝ) * (((rvH R d n m A b cs st ξ' ζ' f).l : ℝ) -
    cV (rvH R d n m A b cs st ξ' ζ' f).G ⬝ᵥ y) - Bud.eta d n * ((ctx R d n m A b cs ap).ln π s -
      (ctx R d n m A b cs ap).Gn π s ⬝ᵥ y))
    (2 * (df2Phi (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ)
      (cV (rvH R d n m A b cs st ξ' ζ' f).b) (rvH R d n m A b cs st ξ' ζ' f).k y - (ctx R d n m A b cs ap).PhiN π s y))
  rw [abs_mul, abs_two] at this
  change _ ≤ Bud.eta d n * (101 / 100) * (n * Bud.el d n + Bud.R d n * n * Bud.eg d n) +
    Bud.eta d n * Bud.tp d n / 16 * (21 / 10) * Bud.R d n * Bud.Gb d n + 2 * Bud.ePhi d n
  linarith

end RCHyp

/-! ## P°'s test statistic: the quadratic of SEL, its Lipschitz bound, the acceptance test -/

theorem refTest_F (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (y : Fin d → ℝ) :
    (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).1 + (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.1 ⬝ᵥ y -
      y ⬝ᵥ ((refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2 *ᵥ y) = c.Xi π s y := by
  show (c.p.eta * c.ln π s - 2 * c.kn π s) + ((2 : ℕ) • c.bn π s - c.p.eta • c.Gn π s) ⬝ᵥ y -
    y ⬝ᵥ (c.Pn π s *ᵥ y) = _
  unfold Df2Ctx.Xi Df2Ctx.PhiN df2Phi
  simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, two_nsmul, smul_eq_mul]
  ring

theorem refTest_h (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) :
    (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.1 = (2 : ℝ) • (c.bn π s - (c.p.eta / 2) • c.Gn π s) := by
  show (2 : ℕ) • c.bn π s - c.p.eta • c.Gn π s = _
  ext i; simp only [two_nsmul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem refTest_P (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) :
    (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2 = c.Pn π s := rfl

section DetFacts

open AdversarialBco.Poly.Layer2 (sq_le_of_psd sq_smul sq_one sq_nonneg_of_psd mulVec_sq_le)

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem Pn_zz (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.Pn π s *ᵥ c.zz π s = c.bn π s - (c.p.eta / 2) • c.Gn π s := by
  have h := (H.r1_le_tau hs).2.1
  unfold Df2Ctx.zz
  rw [mulVec_mulVec, mul_eq_one_comm.1 h, one_mulVec]

theorem Pn_symm (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : (c.Pn π s)ᵀ = c.Pn π s :=
  (H.r1_le_tau hs).1.isHermitian.eq

theorem Pn_psd (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (c.Pn π s *ᵥ v) := sq_nonneg_of_psd (H.r1_le_tau hs).1.posSemidef v

/-- `Xi°(y) = C - 2 ellF(P°', z°, y)`. -/
theorem xi_ell (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.Xi π s y = (c.p.eta * c.ln π s - 2 * c.kn π s + c.zz π s ⬝ᵥ (c.Pn π s *ᵥ c.zz π s)) -
      2 * ellF (c.Pn π s) (c.zz π s) y := by
  rw [← refTest_F, refTest_h, refTest_P]
  exact xi_ellF _ (Pn_symm H hs) _ _ y (Pn_zz H hs) _

theorem Pn_lower (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
    c.p.δe * (v ⬝ᵥ v) ≤ v ⬝ᵥ (c.Pn π s *ᵥ v) := by
  have h := sq_le_of_psd (H.Sn_props hs).2.2 v
  rw [sq_smul, sq_one] at h
  exact h

theorem Pn_mulVec_le (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (v : Fin d → ℝ) :
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

/-- `Xi°` is `4R/δe²`-Lipschitz from a point of `B_R` (the gradient `2 (w° - P°' y)` with `|w°| ≤ R/δe²`). -/
theorem xi_lip (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) {y' : Fin d → ℝ}
    (hy' : oNorm y' ≤ c.p.R) : c.Xi π s y ≤ c.Xi π s y' + 4 * c.p.R / c.p.δe ^ 2 * oNorm (y - y') := by
  have hde := H.rows.pos_de
  have hde1 := H.rows.de_lt
  have hR := H.rows.one_le_R
  rw [← refTest_F, ← refTest_F]
  refine (quad_concave_le _ _ _ (fun v => by rw [refTest_P]; exact Pn_psd H hs v) y y').trans ?_
  have hg : oNorm ((refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.1 -
      ((refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2 + (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2ᵀ) *ᵥ y') ≤
      4 * c.p.R / c.p.δe ^ 2 := by
    rw [refTest_h, refTest_P, Pn_symm H hs]
    have e : (2 : ℝ) • (c.bn π s - (c.p.eta / 2) • c.Gn π s) - (c.Pn π s + c.Pn π s) *ᵥ y' =
        (2 : ℝ) • ((c.bn π s - (c.p.eta / 2) • c.Gn π s) - c.Pn π s *ᵥ y') := by
      rw [add_mulVec]; ext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, oNorm_smul, abs_two]
    have h1 := oNorm_sub_le (c.bn π s - (c.p.eta / 2) • c.Gn π s) (c.Pn π s *ᵥ y')
    have h2 := wn_le H hs
    have h3 := Pn_mulVec_le H hs y'
    have h4 : oNorm y' / c.p.δe ≤ c.p.R / c.p.δe ^ 2 := by
      rw [div_le_div_iff₀ hde (by positivity)]
      have : c.p.δe ^ 2 ≤ c.p.δe := by nlinarith
      nlinarith [oNorm_nonneg y']
    have : 4 * c.p.R / c.p.δe ^ 2 = 2 * (c.p.R / c.p.δe ^ 2 + c.p.R / c.p.δe ^ 2) := by ring
    rw [this]
    linarith
  have := mul_le_mul_of_nonneg_right hg (oNorm_nonneg (y - y'))
  linarith

theorem eT_one (H : DetHyp c δ π m) (hLe : 2 ≤ c.p.Le) : c.eT = 1 := by
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

end DetFacts

/-! ## E15: the selection lemma at BL's test point, and P°'s test call -/

theorem aT_arith (x r Ne de dd : ℝ) (hx : 0 ≤ x) (hxr : x ≤ r) (hNe : Ne = 1 / de) (hde : 0 < de) (hd : 0 < dd) :
    2 * (x ^ 2 / (Ne * dd * 8)) ≤ de / dd * r ^ 2 / 4 := by
  rw [hNe]
  have h1 : x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hx hxr 2
  have e : 2 * (x ^ 2 / (1 / de * dd * 8)) = de / dd * x ^ 2 / 4 := by field_simp; ring
  rw [e]
  have : 0 ≤ de / dd := by positivity
  have := mul_le_mul_of_nonneg_left h1 this
  linarith

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

/-- P°'s radius of round `s`: `1 - ε` at the first round, `s_b (1 - ε)` after. -/
theorem r_cases (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (st.first = true ∧ ((ctx R d n m A b cs ap).st π s).r = 1 - Bud.eps d n) ∨
      (st.first = false ∧ ((ctx R d n m A b cs ap).st π s).r = (po d n).sb * (1 - Bud.eps d n)) := by
  have hinv := H.sett.inv
  have hfst := H.track.first
  by_cases hf : st.first = true
  · have hs0 : s = 0 := hinv.first.1 (hfst ▸ hf)
    subst hs0
    exact Or.inl ⟨hf, rfl⟩
  · have hf' : ((ctx R d n m A b cs ap).st π s).first = false := by rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctx R d n m A b cs ap).tau π (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨-, -, -, -, -, -, hrs⟩ := prev_round H.det hlt
    exact Or.inr ⟨by simpa using hf, hrs⟩

theorem sb_props' (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 < (po d n).sb ∧ Bud.rmin d n ≤ (po d n).sb * (1 - Bud.eps d n) ∧ (po d n).sb ≤ 1 := by
  have e := H.det.sb
  change (po d n).sb = (po d n).δe ^ 2 / ((po d n).R * ((po d n).R + 1)) at e
  have hde := H.sett.de_pos
  have hde1 : (po d n).δe < 1 := H.det.rows.de_lt
  have hR : 1 ≤ (po d n).R := H.R_ge
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  rw [e]
  refine ⟨by positivity, ?_, ?_⟩
  · unfold Bud.rmin
    change (po d n).δe ^ 2 / (2 * (po d n).R * ((po d n).R + 1)) ≤ _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (po d n).δe ^ 2 * ((po d n).R * ((po d n).R + 1)) := by positivity
    nlinarith
  · rw [div_le_one (by positivity)]; nlinarith

/-- `r_min ≤ r_s ≤ 1` and BL's accuracy of the test call is at most `(δe/d) r_s²/8`. -/
theorem r_props (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (r : RV d) :
    Bud.rmin d n ≤ ((ctx R d n m A b cs ap).st π s).r ∧ ((ctx R d n m A b cs ap).st π s).r ≤ 1 ∧
      2 * ((callTQ (cfgOf R d n m A b cs) st r).e : ℝ) ≤
        (ctx R d n m A b cs ap).p.δe / d * ((ctx R d n m A b cs ap).st π s).r ^ 2 / 4 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hsb0, hsbm, hsb1⟩ := H.sb_props'
  have hde := H.sett.de_pos
  have hde1 : (po d n).δe < 1 := H.det.rows.de_lt
  have hR : 1 ≤ (po d n).R := H.R_ge
  have hd : (0 : ℝ) < d := by exact_mod_cast H.hd
  have hNe : (((par d n).Ne : ℕ) : ℝ) = 1 / (po d n).δe := by
    rw [H.bud.enc.Ne_eq]
    have := H.bud.enc.de_eq
    change (po d n).δe = 1 / Bud.Ne d n at this
    rw [this, one_div_one_div]
  have hrmin : Bud.rmin d n ≤ 1 / 2 := by
    unfold Bud.rmin
    change (po d n).δe ^ 2 / (2 * (po d n).R * ((po d n).R + 1)) ≤ _
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases H.r_cases with ⟨hf, hr⟩ | ⟨hf, hr⟩
  · rw [hr]
    refine ⟨by linarith, by linarith, ?_⟩
    have e : ((callTQ (cfgOf R d n m A b cs) st r).e : ℝ) =
        (1 - ((par d n).eps : ℝ)) ^ 2 / ((((par d n).Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTQ; rw [if_pos hf]; simp only [callOf]; push_cast; rfl
    rw [e]
    exact aT_arith _ _ _ _ _ (by linarith) (by linarith) hNe hde hd
  · rw [hr]
    refine ⟨hsbm, ?_, ?_⟩
    · have : 0 ≤ (po d n).sb * Bud.eps d n := by positivity
      nlinarith
    have hf' : ¬ st.first = true := by simp [hf]
    have e : ((callTQ (cfgOf R d n m A b cs) st r).e : ℝ) =
        (((par d n).sb : ℝ) * (1 - ((par d n).eps : ℝ))) ^ 2 / ((((par d n).Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTQ; rw [if_neg hf']; simp only [callOf, rB]; push_cast; rfl
    rw [e]
    have hsb' : (0 : ℝ) < (par d n).sb := by exact_mod_cast H.par_pos.1
    have := H.bud.enc.sb_le
    have hx0 : (0 : ℝ) ≤ ((par d n).sb : ℝ) * (1 - ((par d n).eps : ℝ)) := mul_nonneg hsb'.le (by linarith)
    refine aT_arith _ _ _ _ _ hx0 ?_ hNe hde hd
    have h1 : ((par d n).sb : ℝ) * (1 - ((par d n).eps : ℝ)) ≤ (po d n).sb * (1 - ((par d n).eps : ℝ)) :=
      mul_le_mul_of_nonneg_right this (by linarith)
    have h2 : (po d n).sb * (1 - ((par d n).eps : ℝ)) ≤ (po d n).sb * (1 - Bud.eps d n) :=
      mul_le_mul_of_nonneg_left (by linarith) hsb0.le
    exact h1.trans h2


theorem callT_e_pos (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (r : RV d) :
    (0 : ℚ) < (callTQ (cfgOf R d n m A b cs) st r).e := by
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < ((par d n).Ne : ℚ) := by exact_mod_cast hNe
  have : 0 < 1 - (par d n).eps := by linarith
  unfold callTQ; split
  · show 0 < (1 - (par d n).eps) ^ 2 / ((par d n).Ne * d * 8); positivity
  · show 0 < ((par d n).sb * (1 - (par d n).eps)) ^ 2 / ((par d n).Ne * d * 8); positivity

end RCHyp

/-- P°'s test point from BL's: the selection of the selection lemma for P°'s statistic of round `s`. -/
noncomputable abbrev selV (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (p : Fin d → ℝ) (fire : Bool) : Fin d → ℝ :=
  selT (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).1 (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.1
    (refTest c.p (c.st π s) (π.xi s) (c.Y π s)).2.2 (-(c.p.theta * c.p.rho)) (c.st π s).ctr (c.st π s).r p fire

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

/-- E15, the selection lemma at BL's test point `p'`: P°'s point `v₁ = selV(p', β)` is in `R⁻_s`, within `1` of the
largest
statistic there, has statistic at most `-θ ρ` exactly when BL fires, and is `p'` when BL does not fire. -/
theorem sel (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    (hO3 : O3SpecQ R.ap) :
    ∃ p', R.ap (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)) = some p' ∧
      selV (ctx R d n m A b cs ap) π s (cV p') (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))
        ∈ (ctx R d n m A b cs ap).Rm π s ∧
      (∀ y ∈ (ctx R d n m A b cs ap).Rm π s, (ctx R d n m A b cs ap).Xi π s y ≤
        (ctx R d n m A b cs ap).Xi π s (selV (ctx R d n m A b cs ap) π s (cV p')
          (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))) + 1) ∧
      ((ctx R d n m A b cs ap).Xi π s (selV (ctx R d n m A b cs ap) π s (cV p')
          (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))) ≤
          -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho) ↔
        fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p') ∧
      (¬ fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p' →
        selV (ctx R d n m A b cs ap) π s (cV p')
          (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hpreg, hpmin⟩ := H.testCall O hO3
  refine ⟨p', hp', ?_⟩
  obtain ⟨hgA, -, hgC⟩ := H.gapT (rvH R d n m A b cs st ξ' ζ' f)
  have hRmR : ∀ y ∈ (ctx R d n m A b cs ap).Rm π s, oNorm y ≤ (ctx R d n m A b cs ap).p.R := fun y hy => by
    have h := (H.det.Rm_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctx R d n m A b cs ap).p.R := h
    rwa [sub_zero] at h'
  have hpRm : cV p' ∈ (ctx R d n m A b cs ap).Rm π s := hgC hpreg
  have hpR := hRmR _ hpRm
  obtain ⟨hrmin, hr1, haT⟩ := H.r_props (rvH R d n m A b cs st ξ' ζ' f)
  have hgood := H.det.good s hs
  have hθ : (ctx R d n m A b cs ap).p.theta = 1 := H.det.theta
  obtain ⟨hρ1, hρ2⟩ := H.rho_enc
  have eρ : (ctx R d n m A b cs ap).p.rho = Bud.rho d n := rfl
  have heX := H.bud.eX_le
  have hePhi := H.bud.ePhi_le
  have hwr := H.wr0
  have hsel := H.bud.sel_le
  have hde : 0 < (ctx R d n m A b cs ap).p.δe := H.sett.de_pos
  have hde1 : (ctx R d n m A b cs ap).p.δe < 1 := H.det.rows.de_lt
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hκ1 := H.kap_props.2
  have hR0 := H.R0
  have hh0 : 0 ≤ Bud.h d n := by
    have : 0 ≤ (1 - (1 - ((par d n).eps : ℝ)) / (1 - Bud.eps d n)) * Bud.R d n :=
      mul_nonneg (by linarith) hR0
    linarith
  have heX0 : 0 ≤ Bud.eX d n := by
    have h0 : oNorm (0 : Fin d → ℝ) ≤ Bud.R d n := by
      show Real.sqrt _ ≤ _; simp only [dotProduct_zero, Real.sqrt_zero]; exact hR0
    exact (abs_nonneg _).trans (H.xi_E13 O h0)
  have haT0 : (0 : ℝ) ≤ ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) := by
    exact_mod_cast (H.callT_e_pos _).le
  have eLip : Bud.LipF d n = 4 * (ctx R d n m A b cs ap).p.R / (ctx R d n m A b cs ap).p.δe ^ 2 := rfl
  have hLip0 : 0 ≤ Bud.LipF d n := by rw [eLip]; positivity
  have hrmin0 : 0 ≤ Bud.rmin d n := by
    unfold Bud.rmin; have : 0 ≤ Bud.R d n := hR0; positivity
  -- (H1)
  have hH1 : ∀ y ∈ (ctx R d n m A b cs ap).Rm π s,
      (ctx R d n m A b cs ap).Xi π s y ≤ (ctx R d n m A b cs ap).Xi π s (cV p') +
        (2 * ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) + 2 * Bud.eX d n +
          Bud.LipF d n * Bud.h d n) := by
    intro y hy
    obtain ⟨y', hy'Q, hyy'⟩ := hgA y hy
    have hy'R := hRmR y' (hgC hy'Q)
    have h1 := xi_lip H.det hs y hy'R
    have h2 := abs_le.1 (H.xi_E13 O hy'R)
    have h3 := abs_le.1 (H.xi_E13 O hpR)
    have h4 := hpmin y' hy'Q
    have h5 := xiB_obj (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f) y'
    have h6 := xiB_obj (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f) (cV p')
    have h7 : 4 * (ctx R d n m A b cs ap).p.R / (ctx R d n m A b cs ap).p.δe ^ 2 * oNorm (y - y') ≤
        Bud.LipF d n * Bud.h d n := by
      rw [eLip]; exact mul_le_mul_of_nonneg_left hyy' (by positivity)
    linarith
  -- (H3) and the size of the margin
  have hH3 : (2 * ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) + 2 * Bud.eX d n +
      Bud.LipF d n * Bud.h d n) + (2 * Bud.eh d n + Bud.wr d n) ≤
      (ctx R d n m A b cs ap).p.δe / d * ((ctx R d n m A b cs ap).st π s).r ^ 2 := by
    have h1 : Bud.rmin d n ^ 2 ≤ ((ctx R d n m A b cs ap).st π s).r ^ 2 := pow_le_pow_left₀ hrmin0 hrmin 2
    have h2 : (ctx R d n m A b cs ap).p.δe / d * Bud.rmin d n ^ 2 ≤
        (ctx R d n m A b cs ap).p.δe / d * ((ctx R d n m A b cs ap).st π s).r ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e1 : Bud.selR d n = 3 / 4 * ((ctx R d n m A b cs ap).p.δe / d * Bud.rmin d n ^ 2) := by
      unfold Bud.selR; change 3 / 4 * (ctx R d n m A b cs ap).p.δe / d * _ = _; ring
    unfold Bud.sel at hsel
    rw [e1] at hsel
    linarith
  have hmarg : (ctx R d n m A b cs ap).p.δe / d * ((ctx R d n m A b cs ap).st π s).r ^ 2 ≤ 1 := by
    have h1 : ((ctx R d n m A b cs ap).st π s).r ^ 2 ≤ 1 := by
      have := hgood.2.2; nlinarith
    have h2 : (ctx R d n m A b cs ap).p.δe / d ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h3 : 0 ≤ ((ctx R d n m A b cs ap).st π s).r ^ 2 := sq_nonneg _
    nlinarith
  have hLh : 0 ≤ Bud.LipF d n * Bud.h d n := mul_nonneg hLip0 hh0
  have heh0 : 0 ≤ Bud.eh d n := by have := H.ePhi0; linarith
  have hspec := selT_spec H.hd (refTest (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s)
      ((ctx R d n m A b cs ap).Y π s)).1
    (refTest (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)).2.1
    (refTest (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)).2.2
    (-((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho)) ((ctx R d n m A b cs ap).st π s).ctr
    ((ctx R d n m A b cs ap).st π s).r (cV p')
    (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p')) ((ctx R d n m A b cs ap).Rm π s)
    ((ctx R d n m A b cs ap).p.δe / d)
    (2 * ((callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ) + 2 * Bud.eX d n +
      Bud.LipF d n * Bud.h d n) (2 * Bud.eh d n + Bud.wr d n) (H.det.Rm_props hs).1 hgood.2.1 hgood.2.2
    (fun v => by
      rw [refTest_P]
      have h1 := Pn_lower H.det hs v
      have h2 : 0 ≤ v ⬝ᵥ v := by rw [← oNorm_sq]; positivity
      have h3 : (ctx R d n m A b cs ap).p.δe / d ≤ (ctx R d n m A b cs ap).p.δe := div_le_self hde.le hd1
      nlinarith)
    hpRm
    (fun y hy => by rw [refTest_F, refTest_F]; exact hH1 y hy)
    (fun hf => by
      rw [refTest_F]
      have hnf : ¬ fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p' := by simpa using hf
      rw [fireQ_iff] at hnf
      change ¬ (xiB (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) (cV p') ≤
        -((par d n).rho : ℝ) + Bud.eh d n) at hnf
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    (fun hf => by
      rw [refTest_F]
      have hfq : fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p' := by simpa using hf
      rw [fireQ_iff] at hfq
      change xiB (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) (cV p') ≤
        -((par d n).rho : ℝ) + Bud.eh d n at hfq
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    hH3 (by linarith) (by linarith)
  obtain ⟨hv1Q, hv1max, hv1iff, hv1eq⟩ := hspec
  refine ⟨hv1Q, fun y hy => ?_, ?_, fun hnf => hv1eq (by simpa using hnf)⟩
  · have := hv1max y hy
    rw [refTest_F, refTest_F] at this
    linarith
  · rw [refTest_F] at hv1iff
    rw [hv1iff, decide_eq_true_iff]


theorem Le2 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 2 ≤ (ctx R d n m A b cs ap).p.Le := by
  have := H.bud.Le_ge; change 17467 ≤ (po d n).Le at this; change 2 ≤ (po d n).Le; linarith

theorem Rm_norm (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) {y : Fin d → ℝ}
    (hy : y ∈ (ctx R d n m A b cs ap).Rm π s) : oNorm y ≤ (ctx R d n m A b cs ap).p.R := by
  have h := (H.det.Rm_props H.sett.hs').2.2 hy
  have h' : oNorm (y - 0) ≤ (ctx R d n m A b cs ap).p.R := h
  rwa [sub_zero] at h'

/-- P°'s test call under the advice returns `v₁ = selV(p', β)` (the checked routine accepts it at `e_T = 1`). -/
theorem tcall_eq (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    (hO3 : O3SpecQ R.ap)
    (hap : ap s = apAdv (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s))) :
    ∃ p', R.ap (callTQ (cfgOf R d n m A b cs) st (rvH R d n m A b cs st ξ' ζ' f)) = some p' ∧
      (ctx R d n m A b cs ap).tcall π s = some (selV (ctx R d n m A b cs ap) π s (cV p')
        (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))) ∧
      selV (ctx R d n m A b cs ap) π s (cV p') (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))
        ∈ (ctx R d n m A b cs ap).Rm π s ∧
      ((ctx R d n m A b cs ap).Xi π s (selV (ctx R d n m A b cs ap) π s (cV p')
          (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))) ≤
          -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho) ↔
        fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p') ∧
      (¬ fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p' →
        selV (ctx R d n m A b cs ap) π s (cV p')
          (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hv1Q, hv1max, hv1iff, hv1eq⟩ := H.sel O hO3
  refine ⟨p', hp', ?_, hv1Q, hv1iff, hv1eq⟩
  have htq := testQ_eq R.ap (cfgOf R d n m A b cs) st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f) O.ga O.gt hp'
  have hv : (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)).1 =
      selV (ctx R d n m A b cs ap) π s (cV p')
        (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p')) := by
    unfold advQ; rw [htq]
  have heT : (ctx R d n m A b cs ap).eT = 1 := eT_one H.det H.Le2
  have hadv : advOK ((ctx R d n m A b cs ap).Rm π s) (ctx R d n m A b cs ap).p.R ((ctx R d n m A b cs ap).Pn π s)
      ((ctx R d n m A b cs ap).zz π s) (ctx R d n m A b cs ap).eT
      (selV (ctx R d n m A b cs ap) π s (cV p')
        (decide (fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'))) := by
    refine ⟨hv1Q, H.Rm_norm hv1Q, fun q hq => ?_⟩
    have h1 := hv1max _ hq
    rw [xi_ell H.det hs, xi_ell H.det hs] at h1
    rw [heT]; linarith
  have hpick : advPick (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s))
      (ctx R d n m A b cs ap).eT = (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)).1 := by
    unfold advPick; rw [heT]; exact if_pos (by norm_num)
  unfold Df2Ctx.tcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick, hv]
  exact if_pos hadv


/-! ### E16: the Newton point of line μ -/

theorem qq_ge (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 999 / 1000 ≤ (ctx R d n m A b cs ap).qq π s := by
  have S := H.sett
  rw [H.qq_eq]
  have h1 := S.cc_le
  have h2 := S.xi_le1
  have hx : π.xi s ⬝ᵥ π.xi s ≤ Bud.Xi1 d n ^ 2 := by
    rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h2 2
  have hx0 : 0 ≤ π.xi s ⬝ᵥ π.xi s := by rw [← oNorm_sq]; positivity
  have h3 := H.bud.cb_le
  have hcb := H.cb0
  have h4 : |(ctx R d n m A b cs ap).cc π s * (π.xi s ⬝ᵥ π.xi s - 1)| ≤ Bud.cb d n * (1 + Bud.Xi1 d n ^ 2) := by
    rw [abs_mul]
    apply mul_le_mul h1 _ (abs_nonneg _) hcb
    rw [abs_le]; constructor <;> nlinarith
  have := (abs_le.1 h4).1
  nlinarith

theorem Dq_small (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : Bud.Dq d n ≤ 1 / 1000 := by
  have S := H.sett
  have h1 := Bud.Dc_small H.bud S.eps_pos S.eps_le H.kc_pos.le
  have h2 := H.bud.cb_le
  have hcb := H.cb0
  have hX := Bud.Xi1_pos d n
  have hexi := S.exi_le_one
  have hexi0 : 0 ≤ Bud.exi d n := by unfold Bud.exi; positivity
  have h3 : Bud.cb d n * Bud.Xi1 d n ≤ Bud.cb d n * (1 + Bud.Xi1 d n ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hcb
  have h4 : Bud.cb d n * Bud.Xi1 d n * Bud.exi d n ≤ Bud.cb d n * Bud.Xi1 d n :=
    by have : 0 ≤ Bud.cb d n * Bud.Xi1 d n := by positivity
       nlinarith
  unfold Bud.Dq
  nlinarith

theorem eY_small (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : Bud.eY d n ≤ Bud.Yb d n / 1000 := by
  have S := H.sett
  have h1 := Bud.ezt_le H.hd H.hn H.bud
  have h2 := Bud.Yb_ge H.bud S.eps_pos S.eps_le
  have h3 := Bud.sqrtLe_ge H.bud
  have h4 := Bud.tp_small d n
  have h5 := (Bud.tp_pos d n).le
  have h6 : 0 ≤ Bud.ezt d n := by unfold Bud.ezt; positivity
  unfold Bud.eY Bud.Pb
  nlinarith

theorem tp_eta (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Bud.tp d n ≤ 1 / 100 * Bud.eta d n * Bud.Yb d n := by
  have S := H.sett
  have hNe : 0 < Bud.Ne d n := by
    have h := H.bud.enc.de_eq
    have hde : 0 < Bud.de d n := S.de_pos
    rw [h] at hde; exact one_div_pos.1 hde
  have hLe := H.bud.Le_ge
  have hLeNe := Le_le_Ne (Bud.Ne d n) (Bud.Le d n) hNe H.bud.enc.Le_eq hLe
  have htp0 := (Bud.tp_pos d n).le
  have hx := H.bud.x_le
  have heN : Bud.tp d n ≤ Bud.eN d n := by
    have hDc := Bud.Dc_nonneg H.bud S.eps_pos S.eps_le H.kc_pos.le
    have hcb := H.cb0
    have hexi0 : 0 ≤ Bud.exi d n := by unfold Bud.exi; positivity
    have hX := Bud.Xi1_pos d n
    unfold Bud.eN
    have : 0 ≤ 143 / 100 * (1 + Bud.Xi1 d n ^ 2) * Bud.Dc d n := by positivity
    have : 0 ≤ 285 / 100 * Bud.cb d n * Bud.Xi1 d n * Bud.exi d n := by positivity
    have : Bud.tp d n ≤ Bud.tp d n * (1001 / 1000 + 51 / 100 * Bud.Xi1 d n ^ 2) := by nlinarith
    linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have htp : (n : ℝ) * (d * Bud.Ne d n) * Bud.tp d n ≤ 1 := by
    unfold Bud.x Bud.Lam at hx
    have : (n : ℝ) * (d * Bud.Ne d n) * Bud.tp d n ≤ n * (d * Bud.Ne d n) * Bud.eN d n :=
      mul_le_mul_of_nonneg_left heN (by positivity)
    linarith
  exact tp_small_gen (Bud.tp d n) n d (Bud.Ne d n) (Bud.Le d n) (Bud.eta d n) (Bud.Yb d n) hn hd hNe (by linarith)
    hLeNe htp htp0 rfl (Bud.Yb_ge H.bud S.eps_pos S.eps_le)

/-- E16: `|w'_μ - w°_μ| ≤ Δ_w`. -/
theorem wmu_err (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s) :
    oNorm (cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)) -
      (ctx R d n m A b cs ap).wmu π s) ≤ Bud.Dw d n := by
  have S := H.sett
  have hη : 0 < Bud.eta d n := H.det.rows.pos_eta
  have htp := Bud.tp_small d n
  have htp0 := (Bud.tp_pos d n).le
  have hq0 := H.qq_ge
  have hq : 99 / 100 ≤ (ctx R d n m A b cs ap).qq π s := by linarith
  have hDq := H.Dq_small
  have hq' : 99 / 100 ≤ (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) := by
    have := (abs_le.1 O.eq).1; linarith
  set x : ℚ := (par d n).eta * (rvH R d n m A b cs st ξ' ζ' f).Y * (par d n).nu / (rvH R d n m A b cs st ξ' ζ' f).q
    with hx
  set a' : ℚ := rnd (par d n).p x with ha'
  set a : ℝ := Bud.eta d n * (ctx R d n m A b cs ap).Y π s / ((1 - Bud.lam d n) * (ctx R d n m A b cs ap).qq π s)
    with ha
  have hs5 := s5_err (Bud.eta d n) ((par d n).eta : ℝ) ((ctx R d n m A b cs ap).Y π s)
    (((rvH R d n m A b cs st ξ' ζ' f).Y : ℚ) : ℝ) ((par d n).nu : ℝ) (Bud.lam d n) ((ctx R d n m A b cs ap).qq π s)
    (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) (Bud.tp d n) (Bud.eY d n) (Bud.Yb d n) (Bud.Dq d n) hη.le H.eta_err
    H.bud.enc.nu_rel S.lam_pos.le S.lam_small htp0 htp S.Y_le O.eY hq hq' O.eq
  have hrnd := rnd_err_real (par d n).p x
  have htpe : (1 : ℝ) / 2 ^ ((par d n).p + 1) = Bud.tp d n / 2 := by unfold Bud.tp; rw [pow_succ]; ring
  rw [htpe] at hrnd
  have hxc : ((x : ℚ) : ℝ) = ((par d n).eta : ℝ) * (((rvH R d n m A b cs st ξ' ζ' f).Y : ℚ) : ℝ) *
      ((par d n).nu : ℝ) / (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) := by rw [hx]; push_cast; ring
  rw [hxc] at hrnd
  have hda : |(a' : ℝ) - a| ≤ Bud.Ds5 d n := by
    have := abs_sub_le (a' : ℝ) (((par d n).eta : ℝ) * (((rvH R d n m A b cs st ξ' ζ' f).Y : ℚ) : ℝ) *
      ((par d n).nu : ℝ) / (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ)) a
    unfold Bud.Ds5; linarith
  have hA1 := s5_abs (Bud.eta d n) ((ctx R d n m A b cs ap).Y π s) (Bud.Yb d n) (Bud.lam d n)
    ((ctx R d n m A b cs ap).qq π s) a (a' : ℝ) (Bud.Ds5 d n) (Bud.tp d n) (Bud.eY d n) (Bud.Dq d n) hη.le S.Y_le
    S.lam_pos.le S.lam_small hq rfl hda rfl htp0 H.tp_eta H.eY_small hDq htp
  have hw : oNorm ((ctx R d n m A b cs ap).w π s) ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi d n := by
    refine (oNorm_mulVec_le _ _).trans ?_
    exact mul_le_mul S.opN_A0 S.xi_le (oNorm_nonneg _) (Real.sqrt_nonneg _)
  have h := dw_err ((ctx R d n m A b cs ap).st π s).mu ((ctx R d n m A b cs ap).w π s) (cV (st.A *ᵥ ξ')) a (a' : ℝ)
    (Bud.Ds5 d n) (Bud.Du d n) (Real.sqrt (Bud.Lam d n) * Bud.Xi d n) (103 / 100 * Bud.eta d n * Bud.Yb d n)
    hda hA1 hw O.ew
  have e1 : cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)) =
      ((ctx R d n m A b cs ap).st π s).mu - (a' : ℝ) • cV (st.A *ᵥ ξ') := by
    unfold wmuQ; rw [cV_sub, cV_smul, H.track.mu]; rfl
  have e2 : (ctx R d n m A b cs ap).wmu π s = ((ctx R d n m A b cs ap).st π s).mu - a • (ctx R d n m A b cs ap).w π s := rfl
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  unfold Bud.Dw; ring


theorem opN_Pn (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    opN ((ctx R d n m A b cs ap).Pn π s) ≤ Bud.Lam d n := by
  have S := H.sett
  have h := opN_mul_le ((ctx R d n m A b cs ap).Pn π s * (ctx R d n m A b cs ap).An π s)
    ((ctx R d n m A b cs ap).Pn π s * (ctx R d n m A b cs ap).An π s)ᵀ
  rw [S.PnAn_sq, opN_transpose] at h
  have h2 := S.opN_PnAn
  have h0 := opN_nonneg ((ctx R d n m A b cs ap).Pn π s * (ctx R d n m A b cs ap).An π s)
  have : Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n) = Bud.Lam d n := Real.mul_self_sqrt S.Lam_pos.le
  nlinarith

/-- `|w°_μ| ≤ W° = R + 4d (N_e/Le)^{1/2}` (the guard W of P° does not act, `not_gdW`). -/
theorem wmu0_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm ((ctx R d n m A b cs ap).wmu π s) ≤ Bud.W0 d n := by
  have S := H.sett
  have h := H.det.not_gdW S.hs'
  unfold Df2Ctx.GdW at h
  rw [not_lt] at h
  have hNe : 0 < Bud.Ne d n := by
    have h := H.bud.enc.de_eq
    have hde : 0 < Bud.de d n := S.de_pos
    rw [h] at hde; exact one_div_pos.1 hde
  have hLe : 0 < Bud.Le d n := by have := H.bud.Le_ge; linarith
  have e := w0_eq (Bud.eta d n) d n (Bud.Le d n) (Bud.de d n) (Bud.Ne d n) (by exact_mod_cast H.hd)
    (by exact_mod_cast H.hn) hLe hNe H.bud.enc.de_eq rfl
  change oNorm _ ≤ Bud.R d n + Bud.eta d n * Real.sqrt (16 * d * n * Bud.Le d n / Bud.de d n) at h
  rw [e] at h
  exact h

/-- E18, BL's guard of line μ does not act: `|w'_μ| ≤ W° + Δ_w ≤ 2 W'`. -/
theorem guardW (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s) :
    ¬ (2 * (cfgOf R d n m A b cs).par.W) ^ 2 < wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) ⬝ᵥ
      wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) := by
  rw [not_lt]
  have h1 := H.wmu_err O
  have h2 := H.wmu0_le
  have h3 := H.bud.gW
  have h4 := H.bud.enc.W_le
  have h5 : oNorm (cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f))) ≤
      2 * ((par d n).W : ℝ) := by
    have := oNorm_add_le (cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)) -
      (ctx R d n m A b cs ap).wmu π s) ((ctx R d n m A b cs ap).wmu π s)
    rw [sub_add_cancel] at this
    linarith
  have h6 : cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)) ⬝ᵥ
      cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)) ≤ (2 * ((par d n).W : ℝ)) ^ 2 := by
    rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h5 2
  rw [← cV_dot] at h6
  exact_mod_cast h6

/-- The objective of BL's line μ, `ellF(P'_+, w'_μ, ·)` up to a constant. -/
theorem obj_M (cfg : Cfg d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (r : RV d) (y : Fin d → ℝ) :
    (callMQ cfg n st ξ r).obj y = ellF (cM r.B * (cM r.B)ᵀ) (cV (wmuQ cfg st ξ r)) y -
      cV (wmuQ cfg st ξ r) ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ cV (wmuQ cfg st ξ r)) / 2 := by
  have hs : (cM r.B * (cM r.B)ᵀ)ᵀ = cM r.B * (cM r.B)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [← obj_ellF _ hs]
  unfold CallQ.obj
  change y ⬝ᵥ (cM (r.B * r.Bᵀ) *ᵥ y) / 2 - cV ((r.B * r.Bᵀ) *ᵥ wmuQ cfg st ξ r) ⬝ᵥ y = _
  rw [cM_mulVec, cM_mul, cM_transpose]

/-- E16, the lemma of validity of the mean, and P°'s line μ under the advice: it returns BL's point `μ'`. -/
theorem mcall_eq (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f)
    (O : C1Out d n (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f) (ctx R d n m A b cs ap) π s)
    (hap : ap s = apAdv (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s)))
    {mu' : Fin d → ℚ}
    (hmreg : cV mu' ∈ (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region)
    (hmmin : ∀ x ∈ (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).region,
        (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).obj (cV mu') ≤
          (callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).obj x +
            ((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e : ℝ))
    {pt : Fin d → ℝ} (hpt : pt ∈ (ctx R d n m A b cs ap).Rm π s)
    (hXi : ¬ (ctx R d n m A b cs ap).Xi π s pt ≤ -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho))
    (hmuOf : muOf (step R.ap (cfgOf R d n m A b cs) n (.run st) ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)) = mu') :
    (ctx R d n m A b cs ap).mcall π s ((1 - (ctx R d n m A b cs ap).p.sb) • pt)
      ((ctx R d n m A b cs ap).p.sb * (1 - (ctx R d n m A b cs ap).p.eps)) = some (cV mu') := by
  have S := H.sett
  have hs := S.hs'
  obtain ⟨hgA, -, hgC⟩ := H.gapM O hpt hXi
  have hRpR : ∀ y ∈ (ctx R d n m A b cs ap).Rp π s, oNorm y ≤ (ctx R d n m A b cs ap).p.R := fun y hy => by
    have h := (H.det.Rp_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctx R d n m A b cs ap).p.R := h
    rwa [sub_zero] at h'
  have hmRp := hgC hmreg
  have hmR := hRpR _ hmRp
  have hR1 := H.R_ge
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hde := S.de_pos
  have hde1 : (po d n).δe < 1 := H.det.rows.de_lt
  have hLam := H.opN_Pn
  have hw0 := H.wmu0_le
  have hDw : oNorm ((ctx R d n m A b cs ap).wmu π s -
      cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f))) ≤ Bud.Dw d n := by
    rw [oNorm_sub_comm]; exact H.wmu_err O
  have hPp := (H.Pp_err O).1
  have hW00 : 0 ≤ Bud.W0 d n := (oNorm_nonneg _).trans hw0
  -- the accuracy: `e_BL + 2 Δ_F + L_F h ≤ e_M`
  have hacc : (((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e : ℚ) : ℝ) +
      Bud.val d n ≤ (ctx R d n m A b cs ap).eM π s := by
    have h1 := H.bud.val_le
    have hNe : (((par d n).Ne : ℕ) : ℝ) = 1 / (po d n).δe := by
      rw [H.bud.enc.Ne_eq]
      have := H.bud.enc.de_eq
      change (po d n).δe = 1 / Bud.Ne d n at this
      rw [this, one_div_one_div]
    have hR' : Bud.R d n ≤ ((par d n).R : ℝ) := H.bud.enc.R_le
    have h2 : (((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e : ℚ) : ℝ) ≤ Bud.valR d n := by
      have e : (((callMQ (cfgOf R d n m A b cs) n st ξ' (rvH R d n m A b cs st ξ' ζ' f)).e : ℚ) : ℝ) =
          1 / ((((par d n).Ne : ℕ) : ℝ) * (128 * (n : ℝ) ^ 2 * ((par d n).R : ℝ) ^ 2 * d)) := by
        show ((eBL (par d n) d n : ℚ) : ℝ) = _
        unfold eBL; push_cast; ring
      rw [e, hNe]
      unfold Bud.valR
      change _ ≤ (po d n).δe / (128 * (n : ℝ) ^ 2 * Bud.R d n ^ 2 * d)
      have hRR : Bud.R d n ^ 2 ≤ ((par d n).R : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hR' 2
      have hX : 0 < 128 * (n : ℝ) ^ 2 * Bud.R d n ^ 2 * d := by positivity
      have e2 : 1 / (1 / (po d n).δe * (128 * (n : ℝ) ^ 2 * ((par d n).R : ℝ) ^ 2 * d)) =
          (po d n).δe / (128 * (n : ℝ) ^ 2 * ((par d n).R : ℝ) ^ 2 * d) := by
        have : 0 < ((par d n).R : ℝ) := by linarith
        field_simp
      rw [e2]
      apply div_le_div_of_nonneg_left hde.le hX
      have : 0 ≤ (n : ℝ) ^ 2 * d := by positivity
      nlinarith
    have h3 := eM_ge n (Bud.R d n) ((ctx R d n m A b cs ap).Pn π s).trace d (po d n).δe hn1 hR1 hd1 hde hde1.le
      ((H.det.r1_le_tau hs).1.posSemidef.trace_nonneg) (by have hdc := S.de_c; change (d : ℝ) / (po d n).δe = _ at hdc; rw [hdc]; exact S.trn.1)
    have e : (ctx R d n m A b cs ap).eM π s =
        1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * Bud.R d n ^ 2 * ((ctx R d n m A b cs ap).Pn π s).trace)) := rfl
    rw [e]
    have e2 : (po d n).δe / (64 * (n : ℝ) ^ 2 * Bud.R d n ^ 2 * d) = 2 * Bud.valR d n := by
      unfold Bud.valR; change _ = 2 * ((po d n).δe / _); field_simp; ring
    linarith
  have hval : advOK ((ctx R d n m A b cs ap).Rp π s) (ctx R d n m A b cs ap).p.R ((ctx R d n m A b cs ap).Pn π s)
      ((ctx R d n m A b cs ap).wmu π s) ((ctx R d n m A b cs ap).eM π s) (cV mu') := by
    refine ⟨hmRp, hmR, fun q0 hq => ?_⟩
    set q : Fin d → ℝ := fun i => (q0 i : ℝ) with hqdef
    obtain ⟨y', hy'Q, hqy'⟩ := hgA _ hq
    have hy'R := hRpR _ (hgC hy'Q)
    have hm := hmmin y' hy'Q
    rw [obj_M, obj_M] at hm
    have E1 := abs_le.1 (ellF_err ((ctx R d n m A b cs ap).Pn π s)
      (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ)
      ((ctx R d n m A b cs ap).wmu π s) (cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)))
      (cV mu') (Bud.DP d n) (Bud.Dw d n) (Bud.Lam d n) (Bud.R d n) (Bud.W0 d n) hPp hDw hLam hmR hw0)
    have E2 := abs_le.1 (ellF_err ((ctx R d n m A b cs ap).Pn π s)
      (cM (rvH R d n m A b cs st ξ' ζ' f).B * (cM (rvH R d n m A b cs st ξ' ζ' f).B)ᵀ)
      ((ctx R d n m A b cs ap).wmu π s) (cV (wmuQ (cfgOf R d n m A b cs) st ξ' (rvH R d n m A b cs st ξ' ζ' f)))
      y' (Bud.DP d n) (Bud.Dw d n) (Bud.Lam d n) (Bud.R d n) (Bud.W0 d n) hPp hDw hLam hy'R hw0)
    have E3 := ellF_lip ((ctx R d n m A b cs ap).Pn π s) (Pn_symm H.det hs) (Pn_psd H.det hs)
      ((ctx R d n m A b cs ap).wmu π s) q y'
    have hL : oNorm ((ctx R d n m A b cs ap).Pn π s *ᵥ (y' - (ctx R d n m A b cs ap).wmu π s)) ≤ Bud.LF d n := by
      refine (oNorm_mulVec_le _ _).trans ?_
      have := oNorm_sub_le y' ((ctx R d n m A b cs ap).wmu π s)
      have hy'R' : oNorm y' ≤ Bud.R d n := hy'R
      unfold Bud.LF
      exact mul_le_mul hLam (by linarith) (oNorm_nonneg _) (by have := S.Lam_pos; linarith)
    have hh : oNorm (y' - q) ≤ Bud.h d n := by rw [oNorm_sub_comm]; exact hqy'
    have hLF0 : 0 ≤ Bud.LF d n := (oNorm_nonneg _).trans hL
    have E4 : oNorm ((ctx R d n m A b cs ap).Pn π s *ᵥ (y' - (ctx R d n m A b cs ap).wmu π s)) * oNorm (y' - q) ≤
        Bud.LF d n * Bud.h d n := mul_le_mul hL hh (oNorm_nonneg _) hLF0
    have e5 : Bud.val d n = 2 * Bud.DF d n + Bud.LF d n * Bud.h d n := rfl
    unfold Bud.DF at e5
    obtain ⟨E1a, E1b⟩ := E1
    obtain ⟨E2a, E2b⟩ := E2
    linarith
  have heM : (ctx R d n m A b cs ap).eM π s < 1 / 2 := by
    have := H.det.eM_pos s
    have e : (ctx R d n m A b cs ap).eM π s =
        1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * Bud.R d n ^ 2 * ((ctx R d n m A b cs ap).Pn π s).trace)) := rfl
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ max 1 (4 * Bud.R d n ^ 2 * ((ctx R d n m A b cs ap).Pn π s).trace) := le_max_left _ _
    nlinarith
  have hpick : advPick (advQ R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)
      (ctx R d n m A b cs ap).p ((ctx R d n m A b cs ap).st π s) (π.xi s) ((ctx R d n m A b cs ap).Y π s))
      ((ctx R d n m A b cs ap).eM π s) = cV mu' := by
    unfold advPick
    rw [if_neg (by linarith)]
    show cV (muOf (step R.ap (cfgOf R d n m A b cs) n (.run st) ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f))) = _
    rw [hmuOf]
  unfold Df2Ctx.mcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick]
  exact if_pos hval


end RCHyp

/-! ## C2 and piece C -/

open RCHyp in
/-- C2: one round of BL against P°'s round `s`, from C1's conclusions. -/
theorem c2 : C2Stmt := by
  intro R d n m A b cs ap π s st ξ' ζ' Z f hO3 H hap O
  have hs := H.sett.hs'
  have hm := H.det.mode_run hs
  obtain ⟨p', hp', htc, hv1Q, hiff, heq⟩ := H.tcall_eq O hO3 hap
  have hA := H.det.not_gdA hs
  have hT := H.det.not_gdT hs
  have hZ := H.det.not_gdZ hs
  by_cases hf : fireQ (cfgOf R d n m A b cs) (rvH R d n m A b cs st ξ' ζ' f) p'
  · left
    exact ⟨step_fire R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f) O.ga O.gt hp' hf,
      ((ctx R d n m A b cs ap).fire_iff π s hm).2 ⟨hA, hT, hZ, _, htc, hiff.2 hf⟩⟩
  · right
    have hv1 := heq hf
    rw [hv1] at htc hv1Q hiff
    have hXi : ¬ (ctx R d n m A b cs ap).Xi π s (cV p') ≤
        -((ctx R d n m A b cs ap).p.theta * (ctx R d n m A b cs ap).p.rho) := fun h => hf (hiff.1 h)
    obtain ⟨mu', hmu', hmreg, hmmin⟩ := H.muCall O hO3 hv1Q hXi
    have hstep := step_cont R.ap (cfgOf R d n m A b cs) n st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f) O.ga O.gt
      hp' hf (H.guardW O) hmu'
    have hmc := H.mcall_eq O hap hmreg hmmin hv1Q hXi (by rw [hstep]; rfl)
    have hcont := (ctx R d n m A b cs ap).cont_of π s hm hA hT hZ htc hXi (H.det.not_gdW hs) hmc
    refine ⟨_, hstep, hcont, ?_⟩
    obtain ⟨pt, mu'', htc'', -, hmc'', -, hst⟩ := (ctx R d n m A b cs ap).st_succ_of_cont π s hm hcont
    rw [htc] at htc''
    have e1 : cV p' = pt := Option.some.inj htc''
    rw [← e1, hmc] at hmc''
    have e2 : cV mu' = mu'' := Option.some.inj hmc''
    rw [hst, ← e1, ← e2]
    have hr1 := H.det.r1_le_tau hs
    refine ⟨rfl, rfl, hr1.2.2.1.symm, mul_eq_one_comm.1 hr1.2.1, O.hA, O.hB, ?_, ?_, ?_, ?_⟩
    · have := O.errb; push_cast; exact this
    · have := O.errk; push_cast; exact this
    · have := O.errG; push_cast; exact this
    · have := O.errl; push_cast; exact this

/-- Piece C, the round (`RoundC` of Bit/BLRun.lean). -/
theorem roundC : RoundC := roundC_of c1 c2

end AdversarialBco.Bit.BLP.RC
