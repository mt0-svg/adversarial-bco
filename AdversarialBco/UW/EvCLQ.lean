/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCLQPath
public import AdversarialBco.Poly.CoverProof

@[expose] public section

/-!
# Event (c) of Theorem UW

`evLQPropUW_of : SIFactsUW → RowsUW → EvNeedsUW → EvLQPropUW`: event (c), LQ, at T4U on the weighted path fails with
probability at most `δc/21`. The proof is Theorem U's (Poly/Df2EvSILQ.lean) with three changes:

* the increments are the weighted and clipped observation times the direction, both truncated to the good states
  (`EtrE`, `PtrE`, `DtrE`), so that Lemma U applies through `lemmaU_setW` with the levels `lvVc`, `lvRc`;
* their conditional mean is Lemma UB's mean `⟨s'_s, c - μ_s⟩` up to the bias of Lemma SK' (`biasE`), at most `lvBc`
  per round since `(E_z φ_L⁴)^{1/4} ≤ 2 κ₀^{1/2} lvQ^{1/2}` (`lq_d4E`);
* the range and the discretization read the sure ranges of the weighted path (`lq_rangeE`, `lq_disc_pathE`) in place
  of event (a).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The direction of (c) -/

/-- The growth constant of `phiLE y` on the bound condition. -/
noncomputable def KphiLE (p : Df2OPar) (M : ℝ) (y : Fin d → ℝ) : ℝ :=
  M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) / (1 - p.lam)

theorem KphiLE_nonneg {p : Df2OPar} {M : ℝ} (hM : 0 ≤ M) (hl1 : p.lam < 1) (y : Fin d → ℝ) :
    0 ≤ KphiLE p M y := by
  unfold KphiLE
  have : 0 < 1 - p.lam := by linarith
  positivity

theorem sqrt_dot_sub_leE (a b : Fin d → ℝ) :
    Real.sqrt ((a - b) ⬝ᵥ (a - b)) ≤ Real.sqrt (a ⬝ᵥ a) + Real.sqrt (b ⬝ᵥ b) := by
  rw [← EvSI.norm_toLp, ← EvSI.norm_toLp, ← EvSI.norm_toLp, WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- `|φ_L(y)| ≤ KphiLE (1 + |z|)²` on the bound condition. -/
theorem phiLE_growth {p : Df2OPar} {M : ℝ} (hM : 0 ≤ M) (hl1 : p.lam < 1) (y : Fin d → ℝ)
    {st : Df2St d} (hst : EvSI.stB M st) (z : Fin d → ℝ) : |phiLE p y st z| ≤ KphiLE p M y * (1 + ‖z‖) ^ 2 := by
  have h1 : 0 < 1 - p.lam := by linarith
  have hA := EvSI.bdSet_apply hst.2.1 hM z
  have hP := EvSI.bdSet_apply hst.2.2 hM (st.A *ᵥ z)
  have hz := EvSI.sqrt_dot_le z
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt hst.1
  have hh := sqrt_dot_sub_leE y st.mu
  have hsM := Real.sqrt_nonneg M
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have hu : Real.sqrt ((st.P *ᵥ (st.A *ᵥ z)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ z))) ≤ M * (Real.sqrt d * ‖z‖) := by
    calc _ ≤ Real.sqrt M * (Real.sqrt M * Real.sqrt (z ⬝ᵥ z)) := hP.trans (mul_le_mul_of_nonneg_left hA hsM)
      _ = M * Real.sqrt (z ⬝ᵥ z) := by rw [← mul_assoc, hMM]
      _ ≤ M * (Real.sqrt d * ‖z‖) := mul_le_mul_of_nonneg_left hz hM
  have hl : |EvSI.lin st (y - st.mu) z| ≤ M * (Real.sqrt d * ‖z‖) * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) := by
    unfold EvSI.lin
    exact (EvSI.abs_dot_le _ _).trans (mul_le_mul hu (hh.trans (by linarith)) (Real.sqrt_nonneg _) (by positivity))
  have hzz : ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  unfold phiLE KphiLE
  rw [abs_div, abs_of_pos h1, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ h1.le
  calc |EvSI.lin st (y - st.mu) z| ≤ M * (Real.sqrt d * ‖z‖) * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) := hl
    _ = M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) * ‖z‖ := by ring
    _ ≤ M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) * (1 + ‖z‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hzz (by positivity)

theorem measurable_phiLE (p : Df2OPar) (y : Fin d → ℝ) :
    Measurable fun x : Df2St d × (Fin d → ℝ) => phiLE p y x.1 x.2 := by
  have h1 : Measurable fun x : Df2St d × (Fin d → ℝ) => (x.1, y - x.1.mu, x.2) :=
    measurable_fst.prodMk ((measurable_const.sub (ApMeas.measurable_st_mu.comp measurable_fst)).prodMk
      measurable_snd)
  have h := (EvSI.measurable_lin.comp h1).div_const (1 - p.lam)
  exact h

/-! ## On a path -/

section path

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- The fourth moment of the direction of (c): `(E_z φ_L(w)⁴)^{1/4} ≤ 2 κ₀^{1/2} lvQ^{1/2}`. -/
theorem lq_d4E (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {w : Fin d → ℝ}
    (hq : df2Sq (c.st π s).P (w - (c.st π s).mu) ≤ lvQ c.p) :
    (∫ z, phiLE c.p w (c.st π s) z ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
      2 * Real.sqrt c.p.k0 * Real.sqrt (lvQ c.p) := by
  have hI := H.stInv_le_tau s hs
  set st := c.st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (w - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (w - st.mu) := EvSI.dir_sq st hI.AA hI.SP _
  have hphi : ∀ z, phiLE c.p w st z ^ 4 = (z ⬝ᵥ b) ^ 4 * Real.sqrt c.p.k0 ^ 4 := by
    intro z
    unfold phiLE; rw [EvSI.lin_eq_dot st (EvSI.P_symm hI), sqrt_k0E H, ← hb]; ring
  have hq0 := lvQ_nonnegE H
  have hb0 : 0 ≤ b ⬝ᵥ b := EvSI.dot_self_nonneg' b
  have e1 : ∫ z, phiLE c.p w st z ^ 4 ∂(EvSI.gam d) = ∫ z, (z ⬝ᵥ b) ^ 4 * Real.sqrt c.p.k0 ^ 4 ∂(EvSI.gam d) :=
    integral_congr_ae (Filter.Eventually.of_forall hphi)
  have h105 : Real.sqrt 105 ≤ 16 := by
    rw [show (16 : ℝ) = Real.sqrt (16 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hbq : (b ⬝ᵥ b) ^ 2 ≤ lvQ c.p ^ 2 := pow_le_pow_left₀ hb0 (hbb ▸ hq) 2
  have hsq : Real.sqrt (lvQ c.p) ^ 4 = lvQ c.p ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hq0]
  have hint : ∫ z, phiLE c.p w st z ^ 4 ∂(EvSI.gam d) ≤ (2 * Real.sqrt c.p.k0 * Real.sqrt (lvQ c.p)) ^ 4 := by
    rw [e1, integral_mul_const]
    calc (∫ z, (z ⬝ᵥ b) ^ 4 ∂(EvSI.gam d)) * Real.sqrt c.p.k0 ^ 4
        ≤ (Real.sqrt 105 * (b ⬝ᵥ b) ^ 2) * Real.sqrt c.p.k0 ^ 4 :=
          mul_le_mul_of_nonneg_right (SKp.int_dot_pow_four b) (by positivity)
      _ ≤ (16 * lvQ c.p ^ 2) * Real.sqrt c.p.k0 ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h105 hbq (by positivity) (by norm_num)) (by positivity)
      _ = (2 * Real.sqrt c.p.k0 * Real.sqrt (lvQ c.p)) ^ 4 := by rw [mul_pow, mul_pow, hsq]; ring
  have hI0 : 0 ≤ ∫ z, phiLE c.p w st z ^ 4 ∂(EvSI.gam d) :=
    integral_nonneg fun z => (by positivity : (0 : ℝ) ≤ phiLE c.p w st z ^ 4)
  calc _ ≤ ((2 * Real.sqrt c.p.k0 * Real.sqrt (lvQ c.p)) ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hI0 hint (by norm_num)
    _ = _ := pow_four_rpow (by positivity)

/-- The centred increment of (c) at a point `w` of the ball is at most `lvRc` in absolute value up to `τ`, for any
value `cm` within `lvBc` of the mean `⟨s'_s, w - μ_s⟩`. -/
theorem lq_range_fullE {b0 y0 : ℝ} (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) {w : Fin d → ℝ}
    (hq : df2Sq (c.st (pathW c b0 y0 π) s).P (w - (c.st (pathW c b0 y0 π) s).mu) ≤ lvQ c.p)
    (hwR : w ⬝ᵥ w ≤ c.p.R ^ 2) {cm : ℝ}
    (hcm : |cm - c.sGrad (pathW c b0 y0 π) s ⬝ᵥ (w - (c.st (pathW c b0 y0 π) s).mu)| ≤ lvBc c.p d) :
    |c.Y (pathW c b0 y0 π) s * phiLE c.p w (c.st (pathW c b0 y0 π) s) (π.xi s) - cm| ≤ lvRc c.p d b0 y0 := by
  set πw := pathW c b0 y0 π with hπw
  have hI := H.stInv_le_tau s hs
  have h1 := lq_rangeE hy0 H hs hq
  have hR0 : 0 ≤ c.p.R := by linarith [H.rows.one_le_R]
  have hmu : Real.sqrt ((c.st πw s).mu ⬝ᵥ (c.st πw s).mu) ≤ c.p.R := by
    rw [← Real.sqrt_sq hR0]; exact Real.sqrt_le_sqrt (EvSI.mu_sq_le H hI)
  have hw : Real.sqrt (w ⬝ᵥ w) ≤ c.p.R := by
    rw [← Real.sqrt_sq hR0]; exact Real.sqrt_le_sqrt hwR
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have h8 : 0 ≤ 8 / c.p.eps := div_nonneg (by norm_num) he0.le
  have h2 : |c.sGrad πw s ⬝ᵥ (w - (c.st πw s).mu)| ≤ 8 / c.p.eps * (2 * c.p.R) := by
    refine (sGrad_dotE H hs _).trans (mul_le_mul_of_nonneg_left ?_ h8)
    have := sqrt_dot_sub_leE w (c.st πw s).mu
    linarith
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 hcm
  unfold lvRc
  exact abs_le.2 ⟨by linarith, by linarith⟩

end path

/-- `μ S ≤ μ U` when almost every point of `S` lies in `U`. -/
theorem measure_le_of_ae_memE {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {S U : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ S → ω ∈ U) : μ S ≤ μ U :=
  measure_mono_ae (h.mono fun _ hω => hω)

/-! ## Event (c) -/

/-- **Event (c) of Theorem UW**: LQ at T4U on the weighted path fails with probability at most `δc/21`, from the
rows, the facts of SI and the needs of the events. -/
theorem evLQPropUW_of (hS : SIFactsUW) (hR : RowsUW) (hN : EvNeedsUW) : EvLQPropUW := by
  intro d n m ρ hreg hm1 hmn Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  have N := (hN d n ρ hreg).needC
  have rows : Df2Rows (parW d n ρ.u) d n := (hR d n ρ hreg).base
  set p := parW d n ρ.u with hpdef
  -- the parameters
  have hd : 1 ≤ d := hreg.hd
  have hn : 1 ≤ n := hreg.hn
  have hfix : Df2ParFix p := df2ParFix_parW d n ρ.u
  have hde0 : 0 < p.δe := rows.pos_de
  have hde1 : p.δe < 1 := rows.de_lt
  have he0 : 0 < p.eps := rows.pos_eps
  have heps4 : p.eps ≤ 1 / 4 := hreg.heps
  have heps : p.eps ≤ 1 / 2 := by linarith
  have hl0 : 0 < p.lam := rows.pos_lam
  have hl1 : p.lam < 1 := by have := rows.lam_le; linarith
  have hR1 : 1 ≤ p.R := rows.one_le_R
  have hRp : 0 < p.R := by linarith
  have hx14 : 14 ≤ Real.log (1 / p.δe) := by
    have h := rows.cx
    have : 0 ≤ Real.log ((d : ℝ) * n) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) (by exact_mod_cast hn))
    linarith
  have hLx : p.Le = 36 * Real.log (1 / p.δe) := by rw [hfix.Le]; rfl
  have hLe0 : 0 < p.Le := by rw [hLx]; linarith
  have hLlam : p.Le = 36 * lam0 d n := by
    rw [hLx]
    congr 1
    show Real.log (1 / (1 / (n0W d n : ℝ))) = lam0 d n
    rw [one_div_one_div]
    rfl
  have hp : SKPar p := ⟨he0, heps, hl0.le, hl1.le, by rw [hLx]; linarith, hfix.sig2, hLx, hde0, hde1.le⟩
  set M := EvSI.M0 p with hMdef
  have hM0 : 0 ≤ M := EvSI.M0_nonneg p
  have hb0 : 2 * d + p.Le + 2 ≤ ρ.b0 := by rw [hLlam]; exact hreg.b0_lo
  have hy0 : 10 + 18 / p.eps + 10 * Real.sqrt (p.Le / 3) ≤ ρ.y0 := by
    rw [hLlam, show 36 * lam0 d n / 3 = 12 * lam0 d n by ring]; exact hreg.y0_lo
  have hy00 : 0 ≤ ρ.y0 := by
    have : 0 ≤ 18 / p.eps := div_nonneg (by norm_num) he0.le
    have := Real.sqrt_nonneg (p.Le / 3)
    linarith
  have hdc0 : 0 < ρ.δc := hreg.dc_pos
  have hdc1 : ρ.δc ≤ p.δe := hreg.dc_le
  -- the levels
  have hC0 : 0 ≤ 1 + 2 / p.eps := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) he0.le; linarith
  have hk0 : 0 ≤ p.k0 := by rw [hfix.k0]; positivity
  have hQ0 : 0 ≤ lvQ p := by unfold lvQ; positivity
  have hX0 : 0 ≤ lvX p := by unfold lvX; linarith
  have hB0 : 0 ≤ lvBias p d := by unfold lvBias; positivity
  have hBc0 : 0 ≤ lvBc p d := by unfold lvBc; positivity
  have hV0 : 0 ≤ lvVc p d n := by unfold lvVc; positivity
  have hRc : 0 < lvRc p d ρ.b0 ρ.y0 := by
    unfold lvRc
    have h1 : 0 ≤ ρ.y0 * Real.sqrt p.k0 * Real.sqrt ((ρ.b0 + 1) * lvQ p) := by positivity
    have h2 : 0 < 8 / p.eps * (2 * p.R) := by positivity
    linarith
  -- the net of the ball
  obtain ⟨C, hCball, -, hCnet, hCcard⟩ := existsNet d p.R (p.δe ^ 4) hRp.le (pow_pos hde0 4)
  -- the state process and the increments
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → Ω → Θ × Df2St d, σ = sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e := ⟨_, rfl⟩
  have hσm : ∀ s < m, Measurable[𝒢 s] (σ s) := fun s hs => by
    rw [hσdef]
    exact measurable_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas hs.le
  obtain ⟨X, hXdef⟩ : ∃ X : E d → ℕ → Ω → ℝ, X = fun c s ω => if s < m then
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiLE p (WithLp.ofLp c)) (σ s ω, ξ s ω) else 0 := ⟨_, rfl⟩
  have hXlt : ∀ c s, s < m → X c s = fun ω =>
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiLE p (WithLp.ofLp c)) (σ s ω, ξ s ω) := by
    intro c s hs; rw [hXdef]; funext ω; simp only [hs, ↓reduceIte]
  have hXpt : ∀ c s, s < m → ∀ ω, X c s ω =
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiLE p (WithLp.ofLp c)) (σ s ω, ξ s ω) := fun c s hs ω => by rw [hXlt c s hs]
  -- Lemma U
  have hgr : ∀ (c : E d) (s : ℕ), s < m →
      (∀ x, |EtrE p Kθ gθ M s x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiLE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |PtrE p Kθ M x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiLE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |DtrE p Kθ M (phiLE p (WithLp.ofLp c)) x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiLE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) :=
    fun c s hs => trunc_growth (φ := phiLE p (WithLp.ofLp c)) hp hbody (fun q => hadm q s hs)
      (KphiLE_nonneg hM0 hl1 _) (fun st hst z => phiLE_growth hM0 hl1 _ hst z)
  have hU := lemmaU_setW (d := d) μ 𝒢 C m n hmn σ ξ e hσm hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int
    hE.e_mean hE.e_exp (EtrE p Kθ gθ M) (fun _ => PtrE p Kθ M) (fun c _ => DtrE p Kθ M (phiLE p (WithLp.ofLp c)))
    (fun s hs => measurable_EtrE hmeas.1 (hmeas.2.1 s hs)) (fun _ _ => measurable_PtrE hmeas.1)
    (fun _ _ _ => measurable_DtrE hmeas.1 (measurable_phiLE p _))
    (fun c => (1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiLE p M (WithLp.ofLp c)) 2
    (fun c => add_nonneg (mul_nonneg hC0 (by positivity)) (KphiLE_nonneg hM0 hl1 _))
    (fun c s hs => (hgr c s hs).1) (fun c s hs => (hgr c s hs).2.1) (fun c s hs => (hgr c s hs).2.2)
    (obsW ρ.b0 ρ.y0) (measurable_obsW_uncurry ρ.b0 ρ.y0) (fun x y => (obsW_sure hy00 ρ.b0 x y).2.1)
    (lvRc p d ρ.b0 ρ.y0)⁻¹ (ρ.δc / 21) (inv_pos.2 hRc) (by positivity) (by linarith)
    (fun _ _ _ => lvVc p d n) (fun _ _ _ => lvRc p d ρ.b0 ρ.y0) X (fun c s => by subst hXdef; rfl)
  -- the bias of each round, outside a null set (Lemma SK')
  have hbias : ∀ᵐ ω ∂μ, ∀ c ∈ C, ∀ s ∈ Finset.range m,
      |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) * DtrE p Kθ M (phiLE p (WithLp.ofLp c)) (σ s ω, z)
          ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiLE p (WithLp.ofLp c)) (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := by
    refine (Filter.eventually_all_finset C).2 fun c _ => (Filter.eventually_all_finset _).2 fun s hs => ?_
    have hs' : s < m := Finset.mem_range.1 hs
    rw [hXlt c s hs']
    exact biasE hd hp hbody (fun q => hadm q s hs') hmeas.1 (hmeas.2.1 s hs') hb0 hy0
      (measurable_phiLE p (WithLp.ofLp c)) (KphiLE_nonneg hM0 hl1 _) (fun st hst z => phiLE_growth hM0 hl1 _ hst z)
      (𝒢 s) μ (𝒢.le s) (σ s) (ξ s) (e s) (hσm s hs') ((hE.xi_meas s).mono (𝒢.le _) le_rfl)
      ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.xi_law s) (hE.xi_indep s) (hE.e_int s) (hE.e_mean s) (hE.e_exp s)
  refine le_trans (measure_le_of_ae_memE ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  filter_upwards [hbias] with ω hb hbad
  -- the epoch at `ω`
  set cx := ctxE d n ρ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω)) with hcx
  set π0 : Df2Path d := ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ with hπ0
  set πw := pathW cx ρ.b0 ρ.y0 π0 with hπw
  have H : DetBase cx (1 / 2) πw m := detBaseE hS hR hreg hm1 hmn hbody hadm hap ψ hK ξ e ω
  unfold EvLQW at hbad
  push Not at hbad
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hbad
  have hlt' : b1W p d n ρ.u <
      |∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (y - (cx.st πw s).mu)| := hlt
  have htm : t < m := lt_of_le_of_lt ht H.tau_lt
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 p.R := by
    rw [mem_closedBall_zero_iff, EvSI.norm_toLp]; exact hyR
  obtain ⟨c, hcC, hdist⟩ := hCnet _ hyball
  set c' : Fin d → ℝ := WithLp.ofLp c with hc'
  have hyc : Real.sqrt ((y - c') ⬝ᵥ (y - c')) ≤ p.δe ^ 4 := by
    rw [← EvSI.norm_toLp, WithLp.toLp_sub, hc', WithLp.toLp_ofLp, ← dist_eq_norm]; exact hdist
  have hc8 : (c' - y) ⬝ᵥ (c' - y) ≤ p.δe ^ 8 := by
    have e1 : (c' - y) ⬝ᵥ (c' - y) = (y - c') ⬝ᵥ (y - c') := by
      rw [← neg_sub y c', neg_dotProduct, dotProduct_neg, neg_neg]
    rw [e1, ← Real.sq_sqrt (EvSI.dot_self_nonneg' (y - c')), show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hyc 2
  have hcR : c' ⬝ᵥ c' ≤ p.R ^ 2 := by
    have h1 : Real.sqrt (c' ⬝ᵥ c') ≤ p.R := by
      rw [← EvSI.norm_toLp, hc', WithLp.toLp_ofLp]; exact mem_closedBall_zero_iff.1 (hCball hcC)
    rw [← Real.sq_sqrt (EvSI.dot_self_nonneg' c')]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  -- the states up to `t` are good
  have hσω : ∀ s, σ s ω = (θ s ω, cx.st πw s) := fun s => by rw [hσdef]; rfl
  have hgood : ∀ s ≤ t, goodE p Kθ M (σ s ω) := by
    intro s hs
    have hI := H.stInv_le_tau s (hs.trans ht)
    rw [hσω s]
    unfold goodE
    refine ⟨EvSI.stB_of H hI, fun w => EvGY.LInv.A_sq_le cx πw (EvSI.lpar_of H) (EvSI.linv_of H hI) w, ?_⟩
    show gauge (Kθ (θ s ω)) (WithLp.toLp 2 (cx.st πw s).mu) ≤ 1 - p.eps
    rw [hK s ω]
    exact EvGY.gauge_le_of_keps _ _ (by linarith) _ hI.mu
  -- the increment at `c` is `Y φ_L(c)`
  have hXv : ∀ s ≤ t, X c s ω = cx.Y πw s * phiLE cx.p c' (cx.st πw s) (π0.xi s) := by
    intro s hs
    have hI := H.stInv_le_tau s (hs.trans ht)
    have hg := hgood s hs
    rw [hXpt c s (lt_of_le_of_lt hs htm) ω, EtrE_of (x := (σ s ω, ξ s ω)) hg, PtrE_of (x := (σ s ω, ξ s ω)) hg,
      DtrE_of (x := (σ s ω, ξ s ω)) hg, hσdef, ← Y_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s _ hI.run]
    rfl
  -- the conditional mean is Lemma UB's mean up to the bias
  have hbiasω : ∀ s ≤ t,
      |μ[X c s | 𝒢 s] ω - cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu)| ≤ lvBc p d := by
    intro s hs
    have hs' := hs.trans ht
    have hsm : s < m := lt_of_le_of_lt hs htm
    have hg := hgood s hs
    have h1 : |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) * DtrE p Kθ M (phiLE p c') (σ s ω, z)
          ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiLE p c') (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) :=
      hb c hcC s (Finset.mem_range.2 hsm)
    have hq : df2Sq (cx.st πw s).P (c' - (cx.st πw s).mu) ≤ lvQ cx.p := lq_qE H ht hyS hc8 hs
    have hmean : ∫ z, EtrE p Kθ gθ M s (σ s ω, z) * DtrE p Kθ M (phiLE p c') (σ s ω, z) ∂(EvSI.gam d) =
        cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu) := by
      rw [← mean_LE H hs' c']
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      rw [EtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
        fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
      rfl
    have hD4 : (∫ z, DtrE p Kθ M (phiLE p c') (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
        2 * Real.sqrt p.k0 * Real.sqrt (lvQ p) := by
      have e1 : ∫ z, DtrE p Kθ M (phiLE p c') (σ s ω, z) ^ 4 ∂(EvSI.gam d) =
          ∫ z, phiLE cx.p c' (cx.st πw s) z ^ 4 ∂(EvSI.gam d) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        beta_reduce
        rw [DtrE_of (x := (σ s ω, z)) hg, hσω s]
        rfl
      rw [e1]
      exact lq_d4E H hs' hq
    rw [hmean] at h1
    calc _ ≤ lvBias p d * (∫ z, DtrE p Kθ M (phiLE p c') (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := h1
      _ ≤ lvBias p d * (2 * Real.sqrt p.k0 * Real.sqrt (lvQ p)) := mul_le_mul_of_nonneg_left hD4 hB0
      _ = lvBc p d := rfl
  -- the variance
  have hvar : ∑ s ∈ Finset.range (t + 1), ∫ z, (EtrE p Kθ gθ M s (σ s ω, z) ^ 2 + PtrE p Kθ M (σ s ω, z) ^ 2) *
      DtrE p Kθ M (phiLE p c') (σ s ω, z) ^ 2 ∂(EvSI.gam d) ≤ lvVc p d n := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (lq_varE H ht hyS hc8)
    have hg := hgood s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [EtrE_of (x := (σ s ω, z)) hg, PtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
      fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z, fPE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
    rfl
  -- the deviation
  have hsumX : ∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω) =
      ∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (c' - (cx.st πw s).mu) -
      ∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hXv s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sub_dotProduct, ghat_dotE,
      show πw.xi s = π0.xi s from rfl]
    ring
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : t + 1 ≤ n)
  have hbsum : |∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu))| ≤
      n * lvBc p d := by
    calc _ ≤ ∑ s ∈ Finset.range (t + 1), |μ[X c s | 𝒢 s] ω - cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ Finset.range (t + 1), lvBc p d :=
          Finset.sum_le_sum fun s hs => hbiasω s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
      _ = ((t + 1 : ℕ) : ℝ) * lvBc p d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * lvBc p d := mul_le_mul_of_nonneg_right htn hBc0
  have hdisc : |∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (y - (cx.st πw s).mu) -
      ∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (c' - (cx.st πw s).mu)| ≤
      n * lvGc p ρ.b0 ρ.y0 * p.δe ^ 4 := lq_disc_pathE hy00 H ht hyc
  have hC1 : (1 : ℝ) ≤ C.card := by
    have h : 1 ≤ C.card := Finset.card_pos.2 ⟨c, hcC⟩
    exact_mod_cast h
  have hNc := N (C.card : ℝ) hC1 hCcard
  have key : 3 * Real.sqrt (lvVc p d n * lvLogC p d n ρ.b0 ρ.y0 ρ.δc C.card) +
      2 * lvRc p d ρ.b0 ρ.y0 * lvLogC p d n ρ.b0 ρ.y0 ρ.δc C.card <
      |∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω)| := by
    rw [hsumX]
    set A := ∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (y - (cx.st πw s).mu) with hA
    set B := ∑ s ∈ Finset.range (t + 1), (cx.ghat πw s - cx.sGrad πw s) ⬝ᵥ (c' - (cx.st πw s).mu) with hB
    set Bs := ∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - cx.sGrad πw s ⬝ᵥ (c' - (cx.st πw s).mu)) with hBs
    have h2 := abs_sub_abs_le_abs_sub A B
    have h3 : |B| - |B - Bs| ≤ |Bs| := by
      have := abs_sub_abs_le_abs_sub B (B - Bs)
      rwa [sub_sub_cancel] at this
    linarith
  refine ⟨c, hcC, t, htm, hV0, ?_, hvar, ?_, key⟩
  · show 1 ≤ (lvRc p d ρ.b0 ρ.y0)⁻¹ * lvRc p d ρ.b0 ρ.y0
    rw [inv_mul_cancel₀ hRc.ne']
  · intro s hs
    rw [hXv s hs]
    exact lq_range_fullE hy00 H (hs.trans ht) (lq_qE H ht hyS hc8 hs) hcR (hbiasω s hs)

end AdversarialBco.UW
