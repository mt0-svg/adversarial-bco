/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCProc
public import AdversarialBco.Poly.Df2EvSIRoundV
public import AdversarialBco.UW.DetPar

@[expose] public section

/-!
# One round up to the stopping time, at any parameter record

Theorem U's `Df2EvSIRound.lean` and the concrete section of `Df2EvVSum.lean` are stated at the contexts
`df2CtxAt d n δ Kt ap`, whose record is `df2oPar d n δ`. Their proofs read the record only through `DetBase`, the
rows and the closed forms `Df2ParFix` (DetBase after the pin, Poly/Df2DetMain.lean). This file states them on any
context `c` with `DetBase c δ π m`, so they hold at the table T4U of Theorem UW. With `eRE`, `pRE` the extension and
the gauge factor at the point `X(z) = μ + (1 - λ) A z` of a state, and `yRE = eRE² + pRE²`:

* `vsum_le_quarterE`, `vsum_leE`: `∑_{s ≤ t} E (pip_s - 1)² ≤ n ε²/4` for `t ≤ τ`;
* `sumY_leE`: `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` for `t ≤ τ`; `intY2_leE`: `E[(e_s² + pip_s²)²] ≤ W̄`;
* `mean_LE`, `mean_HE` (Lemma UB' along the directions of the events), `var_LE`, `var_HE` (Lemma TR).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The functions of a round -/

/-- The extension of a round at the draw `z` from the state `st`. -/
noncomputable def eRE (p : Df2OPar) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Ext p K g (WithLp.toLp 2 (xOfE p st z))

/-- The gauge factor of a round at the draw `z` from the state `st`. -/
noncomputable def pRE (p : Df2OPar) (K : Set (E d)) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Pip p K (WithLp.toLp 2 (xOfE p st z))

/-- `e² + pip²`. -/
noncomputable def yRE (p : Df2OPar) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  eRE p K g st z ^ 2 + pRE p K st z ^ 2

theorem continuous_xOfE (p : Df2OPar) (st : Df2St d) :
    Continuous fun z => (WithLp.toLp 2 (xOfE p st z) : E d) := by
  unfold xOfE
  have h : Continuous fun z : Fin d → ℝ => st.A *ᵥ z := (Matrix.mulVecLin st.A).continuous_of_finiteDimensional
  have h2 : Continuous fun z : Fin d → ℝ => st.mu + (1 - p.lam) • (st.A *ᵥ z) :=
    continuous_const.add (Continuous.const_smul h (1 - p.lam))
  exact (PiLp.continuous_toLp 2 _).comp h2

theorem continuous_eRE (p : Df2OPar) (K : Set (E d)) (g : E d → ℝ) (L : ℝ)
    (hL : ∀ x y, |df2Ext p K g x - df2Ext p K g y| ≤ L * ‖x - y‖) (st : Df2St d) : Continuous (eRE p K g st) :=
  (EvSI.continuous_of_lip _ L hL).comp (continuous_xOfE p st)

theorem continuous_pRE (p : Df2OPar) (K : Set (E d)) (hK : Convex ℝ K) (hball : Metric.closedBall 0 1 ⊆ K)
    (st : Df2St d) : Continuous (pRE p K st) := by
  have hn : K ∈ nhds (0 : E d) := Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball
  have hg : Continuous (gauge K) := continuous_gauge hK hn
  unfold pRE df2Pip
  exact continuous_const.max ((hg.comp (continuous_xOfE p st)).div_const _)

theorem yRE_nonneg (p : Df2OPar) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) :
    0 ≤ yRE p K g st z := by
  unfold yRE; positivity

/-! ## Pointwise bounds -/

/-- `|X| ≤ √M (1 + √d ‖z‖)` on the bound condition. -/
theorem normX_leE (p : Df2OPar) {M : ℝ} (hM : 0 ≤ M) {st : Df2St d} (hst : EvSI.stB M st) (hl0 : 0 ≤ p.lam)
    (hl1 : p.lam ≤ 1) (z : Fin d → ℝ) :
    ‖(WithLp.toLp 2 (xOfE p st z) : E d)‖ ≤ Real.sqrt M * (1 + Real.sqrt d * ‖z‖) := by
  rw [EvSI.norm_toLp]
  unfold xOfE
  obtain ⟨h1, h2, -⟩ := hst
  have t := (oNorm_tri st.mu ((1 - p.lam) • (st.A *ᵥ z)) 0 ∅ fun _ => 0)
  have ta := (oNorm_tri (st.A *ᵥ z) 0 (1 - p.lam) ∅ fun _ => 0).2.1
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt h1
  have hA := EvSI.bdSet_apply h2 hM z
  have hz := EvSI.sqrt_dot_le z
  have hab : |1 - p.lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs0 := Real.sqrt_nonneg M
  have hsA := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
  calc Real.sqrt ((st.mu + (1 - p.lam) • (st.A *ᵥ z)) ⬝ᵥ (st.mu + (1 - p.lam) • (st.A *ᵥ z)))
      ≤ Real.sqrt (st.mu ⬝ᵥ st.mu) + |1 - p.lam| * Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) := by
        rw [← ta]; exact t.1
    _ ≤ Real.sqrt M + 1 * (Real.sqrt M * (Real.sqrt d * ‖z‖)) := by
        gcongr
        exact hA.trans (mul_le_mul_of_nonneg_left hz hs0)
    _ = Real.sqrt M * (1 + Real.sqrt d * ‖z‖) := by ring

/-- The constant of the growth of the extension and of the gauge factor on the bound condition. -/
noncomputable def kFE (d : ℕ) (p : Df2OPar) (M : ℝ) : ℝ :=
  (1 + 2 / p.eps) * (1 + 2 * Real.sqrt M) * (1 + Real.sqrt d)

theorem kFE_nonneg (p : Df2OPar) (M : ℝ) (he0 : 0 < p.eps) : 0 ≤ kFE d p M := by
  unfold kFE; positivity

/-- `0 ≤ e(x) ≤ pip(x) + 2 (pip(x) - 1)/ε`, `1 ≤ pip(x) ≤ 1 + 2 ‖x‖`, and the play `x/pip(x)` lies in `K`. -/
theorem ext_pip_boundsE (p : Df2OPar) {R : ℝ} (K : Set (E d)) (hK : Df2Body d R K) (g : E d → ℝ)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (x : E d) :
    0 ≤ df2Ext p K g x ∧ df2Ext p K g x ≤ df2Pip p K x + 2 * (df2Pip p K x - 1) / p.eps ∧
      1 ≤ df2Pip p K x ∧ df2Pip p K x ≤ 1 + 2 * ‖x‖ ∧ (df2Pip p K x)⁻¹ • x ∈ K := by
  obtain ⟨hconv, hcl, hball, -, -⟩ := hK
  set ε := p.eps
  have hε1 : ε < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  set q := df2Pip p K x with hq
  have hq1 : 1 ≤ q := le_max_left _ _
  have hq0 : 0 < q := by linarith
  have hpm := play_mem K ε hconv hcl hball he0 hε1 x
  have h0 : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
  have hplay : q⁻¹ • x ∈ K := by
    have := hconv.smul_mem_of_zero_mem h0 hpm (t := 1 - ε) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ h1ε.ne', one_smul] at this
  obtain ⟨hg0, hg1⟩ := hg.2 _ hplay
  have hgauge := EvSI.gauge_le_norm' K hball x
  have hqle : q ≤ 1 + 2 * ‖x‖ := by
    rw [hq]; unfold df2Pip
    refine max_le (by linarith [norm_nonneg x]) ?_
    rw [div_le_iff₀ h1ε]
    nlinarith [norm_nonneg x, gauge_nonneg (s := K) x]
  refine ⟨?_, ?_, hq1, hqle, hplay⟩
  · show 0 ≤ q * g (q⁻¹ • x) + 2 * (q - 1) / ε
    have h1 := mul_nonneg hq0.le hg0
    have h2 : 0 ≤ 2 * (q - 1) / ε := by apply div_nonneg <;> linarith
    linarith
  · show q * g (q⁻¹ • x) + 2 * (q - 1) / ε ≤ q + 2 * (q - 1) / ε
    have := mul_le_mul_of_nonneg_left hg1 hq0.le; linarith

theorem eRE_pRE_le (p : Df2OPar) {R : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d R K)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1) {M : ℝ}
    (hM : 0 ≤ M) {st : Df2St d} (hst : EvSI.stB M st) (z : Fin d → ℝ) :
    |eRE p K g st z| ≤ kFE d p M * (1 + ‖z‖) ∧ |pRE p K st z| ≤ kFE d p M * (1 + ‖z‖) := by
  obtain ⟨hF0, hF1, hP1, hP2, -⟩ := ext_pip_boundsE p K hbody g hg he0 he1 (WithLp.toLp 2 (xOfE p st z))
  have hX := normX_leE p hM hst hl0 hl1 z
  set ε := p.eps
  set q := df2Pip p K (WithLp.toLp 2 (xOfE p st z))
  set N := ‖(WithLp.toLp 2 (xOfE p st z) : E d)‖
  have hsM := Real.sqrt_nonneg M
  have hsd := Real.sqrt_nonneg (d : ℝ)
  have hz := norm_nonneg z
  have hN0 : 0 ≤ N := norm_nonneg _
  have hN : 1 + 2 * N ≤ (1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖z‖) := by
    have : N ≤ Real.sqrt M * (1 + Real.sqrt d * ‖z‖) := hX
    nlinarith [mul_nonneg hsM hsd, mul_nonneg (mul_nonneg hsM hsd) hz, mul_nonneg hsM hz, mul_nonneg hsd hz]
  have hc0 : 0 ≤ 2 / ε := by positivity
  constructor
  · show |df2Ext p K g _| ≤ _
    rw [abs_of_nonneg hF0]
    calc df2Ext p K g _ ≤ q + 2 * (q - 1) / ε := hF1
      _ ≤ (1 + 2 / ε) * q := by
        have : 2 * (q - 1) / ε ≤ 2 / ε * q := by
          rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ he0.le; linarith
        linarith
      _ ≤ (1 + 2 / ε) * (1 + 2 * N) := by gcongr
      _ ≤ (1 + 2 / ε) * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖z‖)) := by gcongr
      _ = kFE d p M * (1 + ‖z‖) := by unfold kFE; ring
  · show |q| ≤ _
    rw [abs_of_nonneg (by linarith)]
    calc q ≤ 1 + 2 * N := hP2
      _ ≤ 1 * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖z‖)) := by linarith
      _ ≤ (1 + 2 / ε) * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖z‖)) := by
        gcongr; linarith
      _ = kFE d p M * (1 + ‖z‖) := by unfold kFE; ring

theorem yRE_abs_le (p : Df2OPar) {R : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d R K)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1) {M : ℝ}
    (hM : 0 ≤ M) {st : Df2St d} (hst : EvSI.stB M st) (z : Fin d → ℝ) :
    |yRE p K g st z| ≤ 2 * kFE d p M ^ 2 * (1 + ‖z‖) ^ 2 := by
  obtain ⟨h1, h2⟩ := eRE_pRE_le p hbody hg he0 he1 hl0 hl1 hM hst z
  rw [abs_of_nonneg (yRE_nonneg p K g st z)]
  unfold yRE
  have a1 : eRE p K g st z ^ 2 ≤ (kFE d p M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : pRE p K st z ^ 2 ≤ (kFE d p M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith

/-- `e² + pip² ≤ 6 + 10 (pip - 1)²/ε²`. -/
theorem yRE_le (p : Df2OPar) {R : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d R K)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (st : Df2St d) (z : Fin d → ℝ) :
    yRE p K g st z ≤ 6 + 10 * (pRE p K st z - 1) ^ 2 / p.eps ^ 2 := by
  obtain ⟨hF0, hF1, hP1, -, -⟩ := ext_pip_boundsE p K hbody g hg he0 he1 (WithLp.toLp 2 (xOfE p st z))
  unfold yRE
  change df2Ext p K g _ ^ 2 + df2Pip p K _ ^ 2 ≤ 6 + 10 * (df2Pip p K _ - 1) ^ 2 / p.eps ^ 2
  set ε := p.eps
  set q := df2Pip p K (WithLp.toLp 2 (xOfE p st z))
  set F := df2Ext p K g (WithLp.toLp 2 (xOfE p st z))
  set u := (q - 1) / ε with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) he0.le
  have hqu : q - 1 = ε * u := by rw [hu]; field_simp
  have hq : q ≤ 1 + u / 2 := by nlinarith
  have hF : F ≤ 1 + 5 / 2 * u := by
    have : F ≤ q + 2 * u := by rw [hu]; linarith [show 2 * (q - 1) / ε = 2 * ((q - 1) / ε) by ring]
    linarith
  have e10 : 10 * (q - 1) ^ 2 / ε ^ 2 = 10 * u ^ 2 := by rw [hqu]; field_simp
  rw [e10]
  have hF2 : F ^ 2 ≤ (1 + 5 / 2 * u) ^ 2 := pow_le_pow_left₀ hF0 hF 2
  have hq2 : q ^ 2 ≤ (1 + u / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hq 2
  nlinarith [sq_nonneg (3 / 2 * u - 2)]

/-- `pip - 1 ≤ 2 (|μ| + |z|)` when `|A w| ≤ |w|`. -/
theorem pRE_sub_le (p : Df2OPar) {R : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d R K)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1)
    (st : Df2St d) (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    0 ≤ pRE p K st z - 1 ∧ pRE p K st z - 1 ≤ 2 * (Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z)) := by
  obtain ⟨-, -, hP1, hP2, -⟩ := ext_pip_boundsE p K hbody g hg he0 he1 (WithLp.toLp 2 (xOfE p st z))
  refine ⟨by unfold pRE; linarith, ?_⟩
  have hX : ‖(WithLp.toLp 2 (xOfE p st z) : E d)‖ ≤ Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z) := by
    rw [EvSI.norm_toLp]
    unfold xOfE
    have t := (oNorm_tri st.mu ((1 - p.lam) • (st.A *ᵥ z)) 0 ∅ fun _ => 0).1
    have ta := (oNorm_tri (st.A *ᵥ z) 0 (1 - p.lam) ∅ fun _ => 0).2.1
    have hab : |1 - p.lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hAz : Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) ≤ Real.sqrt (z ⬝ᵥ z) := Real.sqrt_le_sqrt (hA z)
    rw [ta] at t
    have h0 := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
    nlinarith [abs_nonneg (1 - p.lam)]
  unfold pRE; linarith

/-- `e² + pip² ≤ 6 + 80 (|μ|² + |z|²)/ε²`. -/
theorem yRE_le_poly (p : Df2OPar) {R : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d R K)
    (hg : AdmLoss K g) (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1)
    (st : Df2St d) (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    yRE p K g st z ≤ 6 + 80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / p.eps ^ 2 := by
  have h1 := yRE_le p hbody hg he0 he1 st z
  obtain ⟨h0, h2⟩ := pRE_sub_le p hbody hg he0 he1 hl0 hl1 st hA z
  have hm := Real.sq_sqrt (EvSI.dot_self_nonneg' st.mu)
  have hz := Real.sq_sqrt (EvSI.dot_self_nonneg' z)
  have h3 : (pRE p K st z - 1) ^ 2 ≤ 8 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) := by
    have := pow_le_pow_left₀ h0 h2 2
    nlinarith [sq_nonneg (Real.sqrt (st.mu ⬝ᵥ st.mu) - Real.sqrt (z ⬝ᵥ z))]
  have he2 : 0 < p.eps ^ 2 := by positivity
  have h4 : 10 * (pRE p K st z - 1) ^ 2 / p.eps ^ 2 ≤ 80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / p.eps ^ 2 := by
    apply div_le_div_of_nonneg_right _ he2.le; linarith
  linarith

/-! ## The sum of the second moments of `pip - 1` (Theorem U's `Df2EvVSum.lean`, concrete section) -/

section VSum

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem L504E (H : DetBase c δ π m) : 504 ≤ c.p.Le := by
  have h1 := H.Le_eq
  have h2 := H.x_ge
  rw [h1]; linarith

/-- `‖(1 - λ) A_s‖ ≤ 1/(2 √L)` for `s ≤ τ`. -/
theorem playT_norm_leE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    ‖EvGY.playT c π s‖ ≤ 1 / (2 * Real.sqrt c.p.Le) := by
  have hL := L504E H
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  have hp : EvGY.LPar c π :=
    ⟨H.rows.pos_sig2, H.rows.pos_de, H.kap_pos.le, heps1, H.body.2.2.1 (Metric.mem_closedBall_self zero_le_one),
      rfl⟩
  have hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v := fun u hu v =>
    EvGY.sHess_nonneg c π u H.body (H.adm u (by have := H.tau_lt; omega)) H.rows.pos_eps heps1 H.rows.pos_lam v
  have hI := EvGY.linv_le_tau c π hp H.hap hH s hs
  have hA : ∀ w, ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) ≤ 2 * c.p.sig2 * (w ⬝ᵥ w) :=
    fun w => hI.A_sq_le c π hp w
  have hN := EvGY.toEuclideanCLM_norm_le (c.st π s).A (2 * c.p.sig2) (by have := H.rows.pos_sig2; positivity) hA
  rw [H.sig2, EvGY.sqrt_two_sig2 _ (by linarith)] at hN
  have hl0 := H.rows.pos_lam
  have hl1 := H.rows.lam_le
  unfold EvGY.playT
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h0 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A‖ := norm_nonneg _
  nlinarith

/-- The crude bound at a round `s ≤ τ`: `E v² ≤ d/L`. -/
theorem vmom_crudeE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    EvGY.vmom c π s ≤ d / c.p.Le := by
  have hL := L504E H
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, -⟩ := H.body
  have hmu := EvGY.gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  rw [EvGY.vmom_eq]
  refine (EvGY.v_sq_crude c.Kt hK hKc hball c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu _).trans ?_
  have hT := playT_norm_leE H hs
  have hsL := Real.sq_sqrt (show (0 : ℝ) ≤ c.p.Le by linarith)
  have hsp := Real.sqrt_pos.2 (show (0 : ℝ) < c.p.Le by linarith)
  have hT2 : ‖EvGY.playT c π s‖ ^ 2 ≤ 1 / (4 * c.p.Le) := by
    calc ‖EvGY.playT c π s‖ ^ 2 ≤ (1 / (2 * Real.sqrt c.p.Le)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ = 1 / (4 * c.p.Le) := by rw [div_pow, mul_pow, hsL]; norm_num
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc 4 * ‖EvGY.playT c π s‖ ^ 2 * d ≤ 4 * (1 / (4 * c.p.Le)) * d := by gcongr
    _ = d / c.p.Le := by field_simp

/-- The fine bound at a round `s ≤ τ`: `E v² ≤ 2 L ε ((2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ) + e^{-L}`. -/
theorem vmom_fineE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    EvGY.vmom c π s ≤
      2 * c.p.Le * (c.p.eps * (2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace +
        2 * c.p.δe * d / c.p.lam)) + Real.exp (-c.p.Le) := by
  have hL := L504E H
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, hMw⟩ := H.body
  have hmu := EvGY.gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  have hadm := H.adm s (H.le_tau_lt hs)
  have h1 := EvGY.v_sq_le H.hd c.Kt hK hKc hball hMw c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu (EvGY.playT c π s)
    c.p.Le hL (playT_norm_leE H hs) (EvGY.par_exp H).1
  have h2 := EvGY.v_mean_le c.Kt hK hKc hball (π.g s) hadm.1 hadm.2 c.p.eps H.rows.pos_eps heps1 _ hmu
    (EvGY.playT c π s)
  have h3 := EvGY.round_lower H hs
  have he : ∫ g, EvGY.extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu + EvGY.playT c π s g)
      ∂(stdGaussian (E d)) = c.ebar π s := by
    unfold Df2Ctx.ebar
    rw [EvGY.df2Ext_eq]
    rfl
  have he2 : EvGY.extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu) =
      df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 (c.st π s).mu) := by rw [EvGY.df2Ext_eq]
  rw [he, he2] at h2
  rw [EvGY.vmom_eq]
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 H.rows.pos_eps.le)
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr

/-- The sum of the second moments up to `t ≤ τ` is at most `n ε²/4`. -/
theorem vsum_le_quarterE (H : DetBase c δ π m) (t : ℕ) (ht : t ≤ c.tau π m) :
    ∑ s ∈ Finset.range (t + 1), EvGY.vmom c π s ≤ 1 / 4 * c.n * c.p.eps ^ 2 := by
  have hd : 1 ≤ d := H.hd
  have hn : 1 ≤ c.n := H.hn
  have hmn : m ≤ c.n := H.hmn
  set τ := c.tau π m with hτ
  have hτn : τ < c.n := lt_of_lt_of_le H.tau_lt hmn
  have hsub : ∑ s ∈ Finset.range (t + 1), EvGY.vmom c π s ≤ ∑ s ∈ Finset.range (τ + 1), EvGY.vmom c π s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.succ_le_succ ht))
      (fun s _ _ => EvGY.vmom_nonneg c π s)
  refine hsub.trans ?_
  rw [Finset.sum_range_succ]
  set L := c.p.Le with hLdef
  set ε := c.p.eps with hεdef
  set lam := c.p.lam with hlamdef
  set de := c.p.δe with hdedef
  set a : ℕ → ℝ := fun u => 2 / lam * (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace with ha
  set b : ℝ := 2 * de * d / lam with hb
  have hfine : ∑ s ∈ Finset.range τ, EvGY.vmom c π s ≤
      ∑ s ∈ Finset.range τ, (2 * L * (ε * (a s + b)) + Real.exp (-L)) :=
    Finset.sum_le_sum fun s hs => vmom_fineE H (Finset.mem_range.1 hs).le
  have hsum : ∀ k : ℕ, ∑ s ∈ Finset.range k, (2 * L * (ε * (a s + b)) + Real.exp (-L)) =
      2 * L * ε * ∑ s ∈ Finset.range k, a s + k * (2 * L * ε * b + Real.exp (-L)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; push_cast; ring
  have htr : ∑ s ∈ Finset.range τ, a s ≤ d * L / (lam * c.p.eta) := EvGY.trace_sum_lt H
  have hcr := vmom_crudeE H (le_refl τ)
  have hL := L504E H
  have hε0 : 0 < ε := H.rows.pos_eps
  have hl0 : 0 < lam := H.rows.pos_lam
  have hde : 0 < de := H.rows.pos_de
  have hb0 : 0 ≤ 2 * L * ε * b + Real.exp (-L) := by positivity
  have hτn' : (τ : ℝ) ≤ c.n := by exact_mod_cast hτn.le
  have h2 : ∑ s ∈ Finset.range τ, EvGY.vmom c π s ≤
      2 * L * ε * (d * L / (lam * c.p.eta)) + c.n * (2 * L * ε * b + Real.exp (-L)) := by
    rw [hsum] at hfine
    have h2Le : 0 ≤ 2 * L * ε := by positivity
    calc _ ≤ _ := hfine
      _ ≤ _ := by gcongr
  have hr5p := H.rows.r5p
  rw [show df2C0 = 36 from rfl] at hr5p
  have harith := EvGY.vsum_arith d c.n L ε lam c.p.eta de (by exact_mod_cast hd) (by exact_mod_cast hn) hL
    hε0 H.rows.eps_le hl0 H.rows.pos_eta hde hr5p H.rows.r7 H.rows.r8 H.rows.c2dl (EvGY.par_exp H).2
  linarith

/-- The sum of the second moments of `pip - 1` under the plays, up to `t ≤ τ`. -/
theorem vsum_leE (H : DetBase c δ π m) (t : ℕ) (ht : t ≤ c.tau π m) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, (pRE c.p c.Kt (c.st π s) z - 1) ^ 2 ∂(EvSI.gam d) ≤
      3 / 10 * c.n * c.p.eps ^ 2 := by
  have h := vsum_le_quarterE H t ht
  have h0 : (0 : ℝ) ≤ c.n * c.p.eps ^ 2 := by positivity
  exact h.trans (by nlinarith)

end VSum

/-! ## A round of a context, up to `τ` -/

section ctx

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

theorem lam_ltE (H : DetBase c δ π m) : c.p.lam < 1 := by
  have : c.p.lam ≤ 1 / 2 := H.rows.lam_le
  linarith

theorem continuous_yRE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (st : Df2St d) :
    Continuous (yRE c.p c.Kt (π.g s) st) := by
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv (H.stInv_le_tau s hs))
  have h1 := continuous_eRE c.p c.Kt (π.g s) _ hsi.ext_lip st
  have h2 := continuous_pRE c.p c.Kt H.body.1 H.body.2.2.1 st
  unfold yRE
  exact (h1.pow 2).add (h2.pow 2)

theorem memLp_yRE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    MemLp (yRE c.p c.Kt (π.g s) (c.st π s)) 2 (EvSI.gam d) := by
  have hI := H.stInv_le_tau s hs
  exact EvSI.memLp_two_of_poly (continuous_yRE H hs _).aestronglyMeasurable _ 2
    (yRE_abs_le c.p H.body (H.adm s (H.le_tau_lt hs)) H.rows.pos_eps H.heps H.rows.pos_lam.le (lam_ltE H).le
      (EvSI.M0_nonneg _) (EvSI.stB_of H hI))

theorem integrable_yRE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    Integrable (yRE c.p c.Kt (π.g s) (c.st π s)) (EvSI.gam d) :=
  (memLp_yRE H hs).integrable one_le_two

/-- Lemma UB' for the direction of event (c). -/
theorem mean_LE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    ∫ z, eRE c.p c.Kt (π.g s) (c.st π s) z * phiLE c.p y (c.st π s) z ∂(EvSI.gam d) =
      c.sGrad π s ⬝ᵥ (y - (c.st π s).mu) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hl1 := lam_ltE H
  have hm := EvSI.mean_lin (df2Ext c.p c.Kt (π.g s)) (8 / c.p.eps) hsi.ext_lip (c.st π s).mu (c.st π s).A
    (c.st π s).P (EvSI.P_mul_S hI) _ hl0 hl1 (y - (c.st π s).mu)
  have h1 : (1 - c.p.lam) ≠ 0 := by linarith
  have e1 : (fun z => eRE c.p c.Kt (π.g s) (c.st π s) z * phiLE c.p y (c.st π s) z) = fun z =>
      df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 ((c.st π s).mu + (1 - c.p.lam) • ((c.st π s).A *ᵥ z))) *
        (((c.st π s).P *ᵥ ((c.st π s).A *ᵥ z)) ⬝ᵥ (y - (c.st π s).mu)) / (1 - c.p.lam) := by
    funext z; unfold eRE phiLE EvSI.lin xOfE; ring
  rw [e1, integral_div, hm, mul_div_cancel_left₀ _ h1]
  rfl

/-- Lemma UB' for the direction of the Hessian. -/
theorem mean_HE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hf : Df2St d → Fin d → ℝ) :
    ∫ z, eRE c.p c.Kt (π.g s) (c.st π s) z * phiHE c.p hf (c.st π s) z ∂(EvSI.gam d) =
      df2Sq (c.sHess π s) (hf (c.st π s)) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hl1 := lam_ltE H
  have hm := EvSI.mean_quad (df2Ext c.p c.Kt (π.g s)) (8 / c.p.eps) hsi.ext_lip (c.st π s).mu (c.st π s).A
    (c.st π s).P (EvSI.P_mul_S hI) _ hl0 hl1 (hf (c.st π s))
  have e1 : (fun z => eRE c.p c.Kt (π.g s) (c.st π s) z * phiHE c.p hf (c.st π s) z) = fun z =>
      c.p.lam * c.p.k0 *
      (df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 ((c.st π s).mu + (1 - c.p.lam) • ((c.st π s).A *ᵥ z))) *
        ((((c.st π s).P *ᵥ ((c.st π s).A *ᵥ z)) ⬝ᵥ hf (c.st π s)) ^ 2 - df2Sq (c.st π s).P (hf (c.st π s)))) := by
    funext z; unfold eRE phiHE EvSI.lin xOfE; ring
  rw [e1, integral_const_mul, hm, H.k0]
  have key : ∀ X : ℝ, c.p.lam * ((1 - c.p.lam) ^ 2)⁻¹ * ((1 - c.p.lam) ^ 2 / c.p.lam * X) = X := by
    intro X
    have h1 : (1 - c.p.lam) ≠ 0 := by linarith
    field_simp
  exact key _

/-- Lemma TR for the direction of event (c): `E[(e² + pip²) (⟨P A z, h⟩/(1 - λ))²]`. -/
theorem var_LE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (h : Fin d → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z * (EvSI.lin (c.st π s) h z / (1 - c.p.lam)) ^ 2 ∂(EvSI.gam d) ≤
      c.p.k0 * (df2Sq (c.st π s).P h *
        (T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
          Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) *
            Real.sqrt (Real.sqrt 105 * Real.exp (-T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  have hl1 := lam_ltE H
  have h1 : (1 - c.p.lam) ≠ 0 := by linarith
  have hk0 : 0 ≤ c.p.k0 := by rw [H.k0]; positivity
  have e1 : (fun z => yRE c.p c.Kt (π.g s) (c.st π s) z * (EvSI.lin (c.st π s) h z / (1 - c.p.lam)) ^ 2) =
      fun z => c.p.k0 * (yRE c.p c.Kt (π.g s) (c.st π s) z *
        (z ⬝ᵥ ((c.st π s).Aᵀ *ᵥ ((c.st π s).P *ᵥ h))) ^ 2) := by
    funext z; rw [EvSI.lin_eq_dot _ (EvSI.P_symm hI), H.k0]; field_simp
  rw [e1, integral_const_mul]
  have htr := EvSI.tr_dot (yRE c.p c.Kt (π.g s) (c.st π s)) (yRE_nonneg c.p c.Kt (π.g s) _) (memLp_yRE H hs)
    ((c.st π s).Aᵀ *ᵥ ((c.st π s).P *ᵥ h)) T hT
  rw [EvSI.dir_sq _ hI.AA hI.SP h] at htr
  exact mul_le_mul_of_nonneg_left htr hk0

/-- Lemma TR for the direction of the Hessian. -/
theorem var_HE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hf : Df2St d → Fin d → ℝ) (T : ℝ)
    (hT : 1 ≤ T) :
    ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z * phiHE c.p hf (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      (c.p.lam * c.p.k0) ^ 2 * (df2Sq (c.st π s).P (hf (c.st π s)) ^ 2 *
        (T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
          Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) *
            Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)))) := by
  have hI := H.stInv_le_tau s hs
  set b := (c.st π s).Aᵀ *ᵥ ((c.st π s).P *ᵥ hf (c.st π s)) with hb
  have hbb : b ⬝ᵥ b = df2Sq (c.st π s).P (hf (c.st π s)) := EvSI.dir_sq _ hI.AA hI.SP _
  have e1 : (fun z => yRE c.p c.Kt (π.g s) (c.st π s) z * phiHE c.p hf (c.st π s) z ^ 2) =
      fun z => (c.p.lam * c.p.k0) ^ 2 * (yRE c.p c.Kt (π.g s) (c.st π s) z * ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 2) := by
    funext z; unfold phiHE; rw [EvSI.lin_eq_dot _ (EvSI.P_symm hI), ← hb, hbb]; ring
  rw [e1, integral_const_mul]
  have htr := EvSI.tr_quad (yRE c.p c.Kt (π.g s) (c.st π s)) (yRE_nonneg c.p c.Kt (π.g s) _) (memLp_yRE H hs)
    b T hT
  rw [← hbb]
  exact mul_le_mul_of_nonneg_left htr (sq_nonneg _)

/-- `∑_{s ≤ t} E[e_s² + pip_s²] ≤ 9 n` for `t ≤ τ`. -/
theorem sumY_leE (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤ 9 * c.n := by
  have hv := vsum_leE H t ht
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have he2 : 0 < c.p.eps ^ 2 := by positivity
  have hpt : ∀ s ≤ t, ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤
      6 + 10 / c.p.eps ^ 2 * ∫ z, (pRE c.p c.Kt (c.st π s) z - 1) ^ 2 ∂(EvSI.gam d) := by
    intro s hst
    have hs : s ≤ c.tau π m := hst.trans ht
    have hI := H.stInv_le_tau s hs
    have hc := continuous_pRE c.p c.Kt H.body.1 H.body.2.2.1 (c.st π s)
    have hb : ∀ z, |(pRE c.p c.Kt (c.st π s) z - 1) ^ 2| ≤ (kFE d c.p (EvSI.M0 c.p) + 1) ^ 2 * (1 + ‖z‖) ^ 2 := by
      intro z
      have h2 : |pRE c.p c.Kt (c.st π s) z| ≤ kFE d c.p (EvSI.M0 c.p) * (1 + ‖z‖) :=
        (eRE_pRE_le c.p H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_ltE H).le
          (EvSI.M0_nonneg _) (EvSI.stB_of H hI) z).2
      have hz : 0 ≤ ‖z‖ := norm_nonneg z
      have hk := kFE_nonneg (d := d) c.p (EvSI.M0 c.p) he0
      rw [abs_of_nonneg (sq_nonneg _)]
      have h3 : |pRE c.p c.Kt (c.st π s) z - 1| ≤ (kFE d c.p (EvSI.M0 c.p) + 1) * (1 + ‖z‖) := by
        have := abs_sub (pRE c.p c.Kt (c.st π s) z) 1
        rw [abs_one] at this
        nlinarith
      calc _ = |pRE c.p c.Kt (c.st π s) z - 1| ^ 2 := (sq_abs _).symm
        _ ≤ ((kFE d c.p (EvSI.M0 c.p) + 1) * (1 + ‖z‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = _ := by ring
    have hi2 : Integrable (fun z => (pRE c.p c.Kt (c.st π s) z - 1) ^ 2) (EvSI.gam d) :=
      EvSI.integrable_of_poly ((hc.sub continuous_const).pow 2).aestronglyMeasurable _ 2 hb
    have hi3 : Integrable (fun z => 6 + 10 / c.p.eps ^ 2 * (pRE c.p c.Kt (c.st π s) z - 1) ^ 2) (EvSI.gam d) :=
      (integrable_const 6).add (hi2.const_mul _)
    have hmono : ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤
        ∫ z, (6 + 10 / c.p.eps ^ 2 * (pRE c.p c.Kt (c.st π s) z - 1) ^ 2) ∂(EvSI.gam d) := by
      refine integral_mono (integrable_yRE H hs) hi3 fun z => ?_
      have : yRE c.p c.Kt (π.g s) (c.st π s) z ≤ 6 + 10 * (pRE c.p c.Kt (c.st π s) z - 1) ^ 2 / c.p.eps ^ 2 :=
        yRE_le c.p H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps (c.st π s) z
      show yRE c.p c.Kt (π.g s) (c.st π s) z ≤ 6 + 10 / c.p.eps ^ 2 * (pRE c.p c.Kt (c.st π s) z - 1) ^ 2
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [integral_add (integrable_const 6) (hi2.const_mul _), integral_const_mul, integral_const] at hmono
    simpa using hmono
  have hsum := Finset.sum_le_sum fun s hs => hpt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range] at hsum
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ c.n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ c.n)
  have h3 : 10 / c.p.eps ^ 2 * ∑ s ∈ Finset.range (t + 1),
      ∫ z, (pRE c.p c.Kt (c.st π s) z - 1) ^ 2 ∂(EvSI.gam d) ≤ 3 * c.n := by
    calc _ ≤ 10 / c.p.eps ^ 2 * (3 / 10 * c.n * c.p.eps ^ 2) := by gcongr
      _ = 3 * c.n := by field_simp
  simp only [nsmul_eq_mul] at hsum
  linarith

/-- `E[(e² + pip²)²] ≤ 72 + 25600 (R⁴ + 3 d²)/ε⁴` for `s ≤ τ`. -/
theorem intY2_leE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      72 + 25600 * (c.p.R ^ 4 + 3 * (d : ℝ) ^ 2) / c.p.eps ^ 4 := by
  have hI := H.stInv_le_tau s hs
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hR : (c.st π s).mu ⬝ᵥ (c.st π s).mu ≤ c.p.R ^ 2 := EvSI.mu_sq_le H hI
  set ε := c.p.eps
  set R := c.p.R
  have hpt : ∀ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ≤
      (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2 := by
    intro z
    have h1 := yRE_le_poly c.p H.body (H.adm s (H.le_tau_lt hs)) he0 H.heps H.rows.pos_lam.le (lam_ltE H).le
      (c.st π s) (EvSI.A_sq_le H hI) z
    have h0 := yRE_nonneg c.p c.Kt (π.g s) (c.st π s) z
    have hz := EvSI.dot_self_nonneg' z
    set u := (c.st π s).mu ⬝ᵥ (c.st π s).mu
    have hu := EvSI.dot_self_nonneg' (c.st π s).mu
    have hc80 : 0 ≤ 80 / ε ^ 2 := by positivity
    have h2 : yRE c.p c.Kt (π.g s) (c.st π s) z ≤ 6 + 80 / ε ^ 2 * (R ^ 2 + z ⬝ᵥ z) := by
      calc _ ≤ 6 + 80 * (u + z ⬝ᵥ z) / ε ^ 2 := h1
        _ = 6 + 80 / ε ^ 2 * (u + z ⬝ᵥ z) := by ring
        _ ≤ 6 + 80 / ε ^ 2 * (R ^ 2 + z ⬝ᵥ z) := by
          have : u + z ⬝ᵥ z ≤ R ^ 2 + z ⬝ᵥ z := by linarith
          nlinarith [mul_le_mul_of_nonneg_left this hc80]
    have h3 := pow_le_pow_left₀ h0 h2 2
    set a := 80 / ε ^ 2
    have ha : a ^ 2 = 6400 / ε ^ 4 := by rw [show a = 80 / ε ^ 2 from rfl]; ring
    have e1 : 25600 / ε ^ 4 = 4 * a ^ 2 := by rw [ha]; ring
    rw [e1]
    have hR2 := sq_nonneg (R ^ 2 - z ⬝ᵥ z)
    have hb := sq_nonneg (6 - a * (R ^ 2 + z ⬝ᵥ z))
    nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) hR2]
  have hc := continuous_yRE H hs (c.st π s)
  have hzz : Continuous fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2 := by
    have : Continuous fun z : Fin d → ℝ => z ⬝ᵥ z := by
      unfold dotProduct; fun_prop
    exact this.pow 2
  have hbz : ∀ z : Fin d → ℝ, |(z ⬝ᵥ z) ^ 2| ≤ (d : ℝ) ^ 2 * (1 + ‖z‖) ^ 4 := by
    intro z
    have h1 := EvSI.dot_self_le z
    have hz := EvSI.dot_self_nonneg' z
    have hn := norm_nonneg z
    rw [abs_of_nonneg (sq_nonneg _)]
    have h2 : z ⬝ᵥ z ≤ d * (1 + ‖z‖) ^ 2 := h1.trans (by gcongr; nlinarith)
    calc (z ⬝ᵥ z) ^ 2 ≤ (d * (1 + ‖z‖) ^ 2) ^ 2 := pow_le_pow_left₀ hz h2 2
      _ = _ := by ring
  have hi1 : Integrable (fun z : Fin d → ℝ => (z ⬝ᵥ z) ^ 2) (EvSI.gam d) :=
    EvSI.integrable_of_poly hzz.aestronglyMeasurable _ 4 hbz
  have hi0 : Integrable (fun z => yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2) (EvSI.gam d) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).1 (memLp_yRE H hs)
  have hi3 : Integrable (fun z : Fin d → ℝ => (72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2)
      (EvSI.gam d) := (integrable_const _).add (hi1.const_mul _)
  have hmono : ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      ∫ z, ((72 + 25600 / ε ^ 4 * R ^ 4) + 25600 / ε ^ 4 * (z ⬝ᵥ z) ^ 2) ∂(EvSI.gam d) :=
    integral_mono hi0 hi3 hpt
  rw [integral_add (integrable_const _) (hi1.const_mul _), integral_const_mul, integral_const] at hmono
  have h4 := EvSI.integral_dot_self_sq_le (d := d)
  have he4 : 0 ≤ 25600 / ε ^ 4 := by positivity
  rw [show (EvSI.gam d).real Set.univ = 1 by simp, one_smul] at hmono
  have h5 : 25600 / ε ^ 4 * ∫ z, (z ⬝ᵥ z) ^ 2 ∂(EvSI.gam d) ≤ 25600 / ε ^ 4 * (3 * (d : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left h4 he4
  calc _ ≤ _ := hmono
    _ ≤ 72 + 25600 / ε ^ 4 * R ^ 4 + 25600 / ε ^ 4 * (3 * (d : ℝ) ^ 2) := by linarith
    _ = _ := by ring

end ctx


/-! ## `DetBase` on an instance of setting (E) at T4U -/

/-- `DetBase` at every point of an instance of `UWOnSetE`, on the weighted path, from the rows and the facts of SI
at T4U (`detBaseW`; the confidence `1/2` is read by no lemma). -/
theorem detBaseE (hS : SIFactsUW) (hR : RowsUW) {n m : ℕ} {ρ : RefW} (R : RegimeW d n ρ) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) {Θ V : Type} {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ} {apθ : V → ApFun d}
    (hbody : ∀ q, Df2Body d (parW d n ρ.u).R (Kθ q)) (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q))
    (hap : ∀ v, ApSpec (apθ v)) {Ω : Type} {θ : ℕ → Ω → Θ} (ψ : ℕ → Ω → V)
    (hK : ∀ s ω, Kθ (θ s ω) = Kθ (θ 0 ω)) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (ω : Ω) :
    DetBase (ctxE d n ρ (Kθ (θ 0 ω)) fun s => apθ (ψ s ω)) (1 / 2)
      (pathW (ctxE d n ρ (Kθ (θ 0 ω)) fun s => apθ (ψ s ω)) ρ.b0 ρ.y0
        ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩) m := by
  have heps : (parW d n ρ.u).eps ≤ 1 / 2 := by linarith [R.heps]
  refine detBaseW (u := ρ.u) rfl R.hd R.hn heps (hR d n ρ R).base
    (fun g hg => hS d n ρ.u _ g R.hd R.hn R.hu heps (hbody _) hg) hm1 hmn (hbody _) (fun s => hap _) ?_
  intro s hs
  have h := hadm (θ s ω) s hs
  rw [hK s ω] at h
  exact h

end AdversarialBco.UW
