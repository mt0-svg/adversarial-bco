/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIU
public import AdversarialBco.Poly.Df2EvMeas
public import AdversarialBco.Poly.Df2DetTools
public import AdversarialBco.Poly.Df2DetProof

@[expose] public section

/-!
# The increments of the events LQ, S-DF and DQ on setting (E)

The state process `sig s = (θ, st_s)`, measurable in `𝒢 s` for `s ≤ m`; the extension `fF` and the gauge factor `fP`
at the point `X = μ + (1 - λ) A z` of a state; the directions `phiL` (LQ) and `phiH` (S-DF, DQ); the coefficients
`aOf = I fF φ`, `bOf = I fP φ` of `EvSI.cond_incr`, with `I` the bound condition `stB M` on the state (`|μ|² ≤ M`,
`|A w|² ≤ M |w|²`, `|P w|² ≤ M |w|²`). They are measurable for `s < m` and of polynomial growth in `z` uniformly in
the state, which is what `lemmaU_setE` asks.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open ApMeas Layer2

variable {d : ℕ}

/-! ## A bound condition on the state -/

/-- `|A w|² ≤ k |w|²` for every `w`. -/
def bdSet (k : ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) := {A | ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)}

theorem isClosed_bdSet (k : ℝ) : IsClosed (bdSet (d := d) k) := by
  have : bdSet (d := d) k = ⋂ w, {A | (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)} := by ext A; simp [bdSet]
  rw [this]
  refine isClosed_iInter fun w => isClosed_le ?_ continuous_const
  have h : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => A *ᵥ w :=
    Continuous.matrix_mulVec continuous_id continuous_const
  exact h.dotProduct h

/-- The bound condition on a state. -/
def stB (M : ℝ) (st : Df2St d) : Prop := st.mu ⬝ᵥ st.mu ≤ M ∧ st.A ∈ bdSet M ∧ st.P ∈ bdSet M

theorem measurableSet_stB (M : ℝ) : MeasurableSet {st : Df2St d | stB M st} := by
  have h1 : MeasurableSet {st : Df2St d | st.mu ⬝ᵥ st.mu ≤ M} :=
    measurableSet_le ((continuous_id.dotProduct continuous_id).measurable.comp measurable_st_mu) measurable_const
  have h2 : MeasurableSet {st : Df2St d | st.A ∈ bdSet M} := measurable_st_A (isClosed_bdSet M).measurableSet
  have h3 : MeasurableSet {st : Df2St d | st.P ∈ bdSet M} := measurable_st_P (isClosed_bdSet M).measurableSet
  exact h1.inter (h2.inter h3)

/-! ## Elementary bounds in the coordinates -/

theorem dot_self_nonneg' (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem abs_dot_le (x y : Fin d → ℝ) : |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have h := sq_cauchy (1 : Matrix (Fin d) (Fin d) ℝ) Matrix.PosSemidef.one x y
  simp only [df2Sq, Matrix.one_mulVec] at h
  rw [← Real.sqrt_mul (dot_self_nonneg' x)]
  exact Real.abs_le_sqrt h

/-- `v ⬝ᵥ v ≤ d ‖v‖²` (sup norm). -/
theorem dot_self_le (v : Fin d → ℝ) : v ⬝ᵥ v ≤ d * ‖v‖ ^ 2 := by
  have h : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := fun i => by
    have := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (v i), abs_mul_abs_self (v i)]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = d * ‖v‖ ^ 2 := by simp

theorem sqrt_dot_le (v : Fin d → ℝ) : Real.sqrt (v ⬝ᵥ v) ≤ Real.sqrt d * ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg d)]
  exact Real.sqrt_le_sqrt (dot_self_le v)

theorem bdSet_apply {k : ℝ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ∈ bdSet k) (hk : 0 ≤ k) (w : Fin d → ℝ) :
    Real.sqrt ((A *ᵥ w) ⬝ᵥ (A *ᵥ w)) ≤ Real.sqrt k * Real.sqrt (w ⬝ᵥ w) := by
  rw [← Real.sqrt_mul hk]; exact Real.sqrt_le_sqrt (hA w)

/-! ## The coefficients -/

variable (n : ℕ) (δ : ℝ) {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ)

/-- The extension of round `s` at the point `X = μ + (1 - λ) A z` of the state. -/
noncomputable def fF (s : ℕ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  df2Ext (df2oPar d n δ) (Kθ x.1.1) (gθ s x.1.1) (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2))

/-- The gauge factor `pip` at the point `X = μ + (1 - λ) A z` of the state. -/
noncomputable def fP (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  df2Pip (df2oPar d n δ) (Kθ x.1.1) (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2))

/-- `⟨P A z, h⟩`. -/
noncomputable def lin (st : Df2St d) (h z : Fin d → ℝ) : ℝ := (st.P *ᵥ (st.A *ᵥ z)) ⬝ᵥ h

/-- The direction of LQ at the point `y`: `⟨P A z, y - μ⟩/(1 - λ)`, so that `⟨ĝ, y - μ⟩ = Y phiL`. -/
noncomputable def phiL (y : Fin d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  lin st (y - st.mu) z / (1 - (df2oPar d n δ).lam)

/-- The Hessian direction along `h st`: `λ κ₀ (⟨P A z, h⟩² - hᵀ P h)`, so that `hᵀ ŝ'' h = Y phiH`. -/
noncomputable def phiH (h : Df2St d → Fin d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  (df2oPar d n δ).lam * (df2oPar d n δ).k0 * (lin st (h st) z ^ 2 - df2Sq st.P (h st))

open Classical in
/-- `A = I fF φ`. -/
noncomputable def aOf (M : ℝ) (s : ℕ) (φ : Df2St d → (Fin d → ℝ) → ℝ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  if stB M x.1.2 then fF n δ Kθ gθ s x * φ x.1.2 x.2 else 0

open Classical in
/-- `B = I fP φ`. -/
noncomputable def bOf (M : ℝ) (φ : Df2St d → (Fin d → ℝ) → ℝ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  if stB M x.1.2 then fP n δ Kθ x * φ x.1.2 x.2 else 0

/-! ## Measurability -/

theorem measurable_lin : Measurable fun x : Df2St d × (Fin d → ℝ) × (Fin d → ℝ) => lin x.1 x.2.1 x.2.2 := by
  have hP : Measurable fun x : Df2St d × (Fin d → ℝ) × (Fin d → ℝ) => x.1.P := measurable_st_P.comp measurable_fst
  have hA : Measurable fun x : Df2St d × (Fin d → ℝ) × (Fin d → ℝ) => x.1.A := measurable_st_A.comp measurable_fst
  have h1 : Measurable fun x : Df2St d × (Fin d → ℝ) × (Fin d → ℝ) => x.1.A *ᵥ x.2.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hA.prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable fun x : Df2St d × (Fin d → ℝ) × (Fin d → ℝ) => x.1.P *ᵥ (x.1.A *ᵥ x.2.2) :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hP.prodMk h1)
  exact (continuous_fst.dotProduct continuous_snd).measurable.comp (h2.prodMk (measurable_fst.comp measurable_snd))

theorem measurable_fF [MeasurableSpace Θ] {m : ℕ} (ap : ApFun d)
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {s : ℕ} (hs : s < m) : Measurable (fF n δ Kθ gθ s) := by
  have hX : Measurable fun x : (Θ × Df2St d) × (Fin d → ℝ) => (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2) : E d) :=
    (WithLp.measurable_toLp 2 _).comp
      ((EvGY.measurable_xOf n δ).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := (hmeas.2.1 s hs).comp ((measurable_fst.comp measurable_fst).prodMk hX)
  exact h

theorem measurable_fP [MeasurableSpace Θ] {m : ℕ} (ap : ApFun d)
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) : Measurable (fP n δ Kθ) := by
  have hX : Measurable fun x : (Θ × Df2St d) × (Fin d → ℝ) => (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2) : E d) :=
    (WithLp.measurable_toLp 2 _).comp
      ((EvGY.measurable_xOf n δ).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := (measurable_const : Measurable fun _ : (Θ × Df2St d) × (Fin d → ℝ) => (1 : ℝ)).max
    ((hmeas.1.comp ((measurable_fst.comp measurable_fst).prodMk hX)).div_const (1 - (df2oPar d n δ).eps))
  exact h

theorem measurable_phiL (y : Fin d → ℝ) : Measurable fun x : Df2St d × (Fin d → ℝ) => phiL n δ y x.1 x.2 := by
  have h1 : Measurable fun x : Df2St d × (Fin d → ℝ) => (x.1, y - x.1.mu, x.2) :=
    measurable_fst.prodMk ((measurable_const.sub (measurable_st_mu.comp measurable_fst)).prodMk measurable_snd)
  have h := (measurable_lin.comp h1).div_const (1 - (df2oPar d n δ).lam)
  exact h

theorem measurable_phiH (h : Df2St d → Fin d → ℝ) (hh : Measurable h) :
    Measurable fun x : Df2St d × (Fin d → ℝ) => phiH n δ h x.1 x.2 := by
  unfold phiH
  have hl : Measurable fun x : Df2St d × (Fin d → ℝ) => lin x.1 (h x.1) x.2 := by
    have := measurable_lin.comp (measurable_fst.prodMk ((hh.comp measurable_fst).prodMk measurable_snd))
    exact this
  have hq : Measurable fun x : Df2St d × (Fin d → ℝ) => df2Sq x.1.P (h x.1) := by
    unfold df2Sq
    have hPh : Measurable fun x : Df2St d × (Fin d → ℝ) => x.1.P *ᵥ h x.1 :=
      (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
        ((measurable_st_P.comp measurable_fst).prodMk (hh.comp measurable_fst))
    exact (continuous_fst.dotProduct continuous_snd).measurable.comp ((hh.comp measurable_fst).prodMk hPh)
  have h := ((hl.pow_const 2).sub hq).const_mul ((df2oPar d n δ).lam * (df2oPar d n δ).k0)
  exact h

theorem measurable_aOf [MeasurableSpace Θ] {m : ℕ} (ap : ApFun d)
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {s : ℕ} (hs : s < m) (M : ℝ)
    (φ : Df2St d → (Fin d → ℝ) → ℝ) (hφ : Measurable fun x : Df2St d × (Fin d → ℝ) => φ x.1 x.2) :
    Measurable (aOf n δ Kθ gθ M s φ) := by
  unfold aOf
  exact Measurable.ite ((measurable_snd.comp measurable_fst) (measurableSet_stB M))
    ((measurable_fF n δ Kθ gθ ap hmeas hs).mul (hφ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    measurable_const

theorem measurable_bOf [MeasurableSpace Θ] {m : ℕ} (ap : ApFun d)
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (M : ℝ)
    (φ : Df2St d → (Fin d → ℝ) → ℝ) (hφ : Measurable fun x : Df2St d × (Fin d → ℝ) => φ x.1 x.2) :
    Measurable (bOf n δ Kθ M φ) := by
  unfold bOf
  exact Measurable.ite ((measurable_snd.comp measurable_fst) (measurableSet_stB M))
    ((measurable_fP n δ Kθ gθ ap hmeas).mul (hφ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    measurable_const

/-! ## Growth -/

theorem norm_toLp (v : Fin d → ℝ) : ‖(WithLp.toLp 2 v : E d)‖ = Real.sqrt (v ⬝ᵥ v) := by
  rw [← (df2Carriers_holds d 1 1 v ∅).2.2.2.2.1, Real.sqrt_sq (norm_nonneg _)]

theorem gauge_le_norm' (K : Set (E d)) (hball : Metric.closedBall 0 1 ⊆ K) (x : E d) : gauge K x ≤ ‖x‖ := by
  have habsB : Absorbent ℝ (Metric.closedBall (0 : E d) 1) :=
    (absorbent_ball_zero zero_lt_one).mono Metric.ball_subset_closedBall
  calc gauge K x ≤ gauge (Metric.closedBall (0 : E d) 1) x := gauge_mono habsB hball x
    _ = ‖x‖ := by rw [gauge_closedBall zero_le_one, div_one]

/-- `|X| ≤ √M (1 + √d ‖z‖)` on the bound condition. -/
theorem normX_le {M : ℝ} (hM : 0 ≤ M) {st : Df2St d} (hst : stB M st) (hl0 : 0 ≤ (df2oPar d n δ).lam)
    (hl1 : (df2oPar d n δ).lam ≤ 1) (z : Fin d → ℝ) :
    ‖(WithLp.toLp 2 (EvGY.xOf n δ st z) : E d)‖ ≤ Real.sqrt M * (1 + Real.sqrt d * ‖z‖) := by
  rw [norm_toLp]
  unfold EvGY.xOf
  obtain ⟨h1, h2, -⟩ := hst
  have t := (oNorm_tri st.mu ((1 - (df2oPar d n δ).lam) • (st.A *ᵥ z)) 0 ∅ fun _ => 0)
  have ta := (oNorm_tri (st.A *ᵥ z) 0 (1 - (df2oPar d n δ).lam) ∅ fun _ => 0).2.1
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt h1
  have hA := bdSet_apply h2 hM z
  have hz := sqrt_dot_le z
  have hab : |1 - (df2oPar d n δ).lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs0 := Real.sqrt_nonneg M
  have hsA := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
  calc Real.sqrt ((st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ z)) ⬝ᵥ
        (st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ z)))
      ≤ Real.sqrt (st.mu ⬝ᵥ st.mu) + |1 - (df2oPar d n δ).lam| * Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) := by
        rw [← ta]; exact t.1
    _ ≤ Real.sqrt M + 1 * (Real.sqrt M * (Real.sqrt d * ‖z‖)) := by
        gcongr
        exact hA.trans (mul_le_mul_of_nonneg_left hz hs0)
    _ = Real.sqrt M * (1 + Real.sqrt d * ‖z‖) := by ring

/-- The constant of the growth of `fF` and `fP`. -/
noncomputable def kF (d n : ℕ) (δ M : ℝ) : ℝ := (1 + 2 / (df2oPar d n δ).eps) * (1 + 2 * Real.sqrt M) * (1 + Real.sqrt d)

theorem kF_nonneg (M : ℝ) (he0 : 0 < (df2oPar d n δ).eps) : 0 ≤ kF d n δ M := by
  unfold kF; positivity

/-- `0 ≤ e(x) ≤ pip(x) + 2 (pip(x) - 1)/ε`, `1 ≤ pip(x) ≤ 1 + 2 ‖x‖`. -/
theorem ext_pip_bounds (K : Set (E d)) (hK : Df2Body d (df2oPar d n δ).R K) (g : E d → ℝ) (hg : AdmLoss K g)
    (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2) (x : E d) :
    0 ≤ df2Ext (df2oPar d n δ) K g x ∧
      df2Ext (df2oPar d n δ) K g x ≤
        df2Pip (df2oPar d n δ) K x + 2 * (df2Pip (df2oPar d n δ) K x - 1) / (df2oPar d n δ).eps ∧
      1 ≤ df2Pip (df2oPar d n δ) K x ∧ df2Pip (df2oPar d n δ) K x ≤ 1 + 2 * ‖x‖ := by
  obtain ⟨hconv, hcl, hball, -, -⟩ := hK
  set ε := (df2oPar d n δ).eps
  have hε1 : ε < 1 := by linarith
  have h1ε : 0 < 1 - ε := by linarith
  set q := df2Pip (df2oPar d n δ) K x with hq
  have hq1 : 1 ≤ q := le_max_left _ _
  have hq0 : 0 < q := by linarith
  have hpm := play_mem K ε hconv hcl hball he0 hε1 x
  have h0 : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self zero_le_one)
  have hplay : q⁻¹ • x ∈ K := by
    have := hconv.smul_mem_of_zero_mem h0 hpm (t := 1 - ε) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ h1ε.ne', one_smul] at this
  obtain ⟨hg0, hg1⟩ := hg.2 _ hplay
  have hgauge := gauge_le_norm' K hball x
  have hqle : q ≤ 1 + 2 * ‖x‖ := by
    rw [hq]; unfold df2Pip
    refine max_le (by linarith [norm_nonneg x]) ?_
    rw [div_le_iff₀ h1ε]
    nlinarith [norm_nonneg x, gauge_nonneg (s := K) x]
  refine ⟨?_, ?_, hq1, hqle⟩
  · show 0 ≤ q * g (q⁻¹ • x) + 2 * (q - 1) / ε
    have h1 := mul_nonneg hq0.le hg0
    have h2 : 0 ≤ 2 * (q - 1) / ε := by apply div_nonneg <;> linarith
    linarith
  · show q * g (q⁻¹ • x) + 2 * (q - 1) / ε ≤ q + 2 * (q - 1) / ε
    have := mul_le_mul_of_nonneg_left hg1 hq0.le; linarith

theorem fF_fP_le {m : ℕ} (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q))
    (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) (he0 : 0 < (df2oPar d n δ).eps)
    (he1 : (df2oPar d n δ).eps ≤ 1 / 2) (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) {s : ℕ} (hs : s < m) (x : (Θ × Df2St d) × (Fin d → ℝ)) (hst : stB M x.1.2) :
    |fF n δ Kθ gθ s x| ≤ kF d n δ M * (1 + ‖x.2‖) ∧ |fP n δ Kθ x| ≤ kF d n δ M * (1 + ‖x.2‖) := by
  obtain ⟨hF0, hF1, hP1, hP2⟩ := ext_pip_bounds n δ (Kθ x.1.1) (hbody x.1.1) (gθ s x.1.1) (hadm x.1.1 s hs) he0
    he1 (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2))
  have hX := normX_le n δ hM hst hl0 hl1 x.2
  set ε := (df2oPar d n δ).eps
  set q := df2Pip (df2oPar d n δ) (Kθ x.1.1) (WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2))
  set N := ‖(WithLp.toLp 2 (EvGY.xOf n δ x.1.2 x.2) : E d)‖
  have hsM := Real.sqrt_nonneg M
  have hsd := Real.sqrt_nonneg (d : ℝ)
  have hz := norm_nonneg x.2
  have hN0 : 0 ≤ N := norm_nonneg _
  have hN : 1 + 2 * N ≤ (1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖x.2‖) := by
    have : N ≤ Real.sqrt M * (1 + Real.sqrt d * ‖x.2‖) := hX
    nlinarith [mul_nonneg hsM hsd, mul_nonneg (mul_nonneg hsM hsd) hz, mul_nonneg hsM hz, mul_nonneg hsd hz]
  have hc0 : 0 ≤ 2 / ε := by positivity
  have hqN : q ≤ 1 + 2 * N := hP2
  constructor
  · show |df2Ext (df2oPar d n δ) (Kθ x.1.1) (gθ s x.1.1) _| ≤ _
    rw [abs_of_nonneg hF0]
    calc df2Ext (df2oPar d n δ) (Kθ x.1.1) (gθ s x.1.1) _ ≤ q + 2 * (q - 1) / ε := hF1
      _ ≤ (1 + 2 / ε) * q := by
        have : 2 * (q - 1) / ε ≤ 2 / ε * q := by
          rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ he0.le; linarith
        linarith
      _ ≤ (1 + 2 / ε) * (1 + 2 * N) := by gcongr
      _ ≤ (1 + 2 / ε) * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖x.2‖)) := by gcongr
      _ = kF d n δ M * (1 + ‖x.2‖) := by unfold kF; ring
  · show |q| ≤ _
    rw [abs_of_nonneg (by linarith)]
    calc q ≤ 1 + 2 * N := hqN
      _ ≤ 1 * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖x.2‖)) := by linarith
      _ ≤ (1 + 2 / ε) * ((1 + 2 * Real.sqrt M) * (1 + Real.sqrt d) * (1 + ‖x.2‖)) := by
        gcongr; linarith
      _ = kF d n δ M * (1 + ‖x.2‖) := by unfold kF; ring

theorem aOf_bOf_le {m : ℕ} (hbody : ∀ q, Df2Body d (df2oPar d n δ).R (Kθ q))
    (hadm : ∀ q, ∀ s < m, AdmLoss (Kθ q) (gθ s q)) (he0 : 0 < (df2oPar d n δ).eps)
    (he1 : (df2oPar d n δ).eps ≤ 1 / 2) (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) {s : ℕ} (hs : s < m) (φ : Df2St d → (Fin d → ℝ) → ℝ) (Kφ : ℝ) (hKφ : 0 ≤ Kφ)
    (hφ : ∀ st, stB M st → ∀ z, |φ st z| ≤ Kφ * (1 + ‖z‖) ^ 2) (x : (Θ × Df2St d) × (Fin d → ℝ)) :
    |aOf n δ Kθ gθ M s φ x| ≤ kF d n δ M * Kφ * (1 + ‖x.2‖) ^ 3 ∧
      |bOf n δ Kθ M φ x| ≤ kF d n δ M * Kφ * (1 + ‖x.2‖) ^ 3 := by
  have hk := kF_nonneg n δ M he0
  have hz : 0 ≤ 1 + ‖x.2‖ := by linarith [norm_nonneg x.2]
  unfold aOf bOf
  split_ifs with hst
  · obtain ⟨hF, hP⟩ := fF_fP_le n δ Kθ gθ hbody hadm he0 he1 hl0 hl1 hM hs x hst
    have hφx := hφ x.1.2 hst x.2
    have e3 : kF d n δ M * Kφ * (1 + ‖x.2‖) ^ 3 = (kF d n δ M * (1 + ‖x.2‖)) * (Kφ * (1 + ‖x.2‖) ^ 2) := by ring
    rw [e3, abs_mul, abs_mul]
    exact ⟨mul_le_mul hF hφx (abs_nonneg _) (by positivity), mul_le_mul hP hφx (abs_nonneg _) (by positivity)⟩
  · simp only [abs_zero]
    exact ⟨by positivity, by positivity⟩

/-! ## The state process -/

theorem stOr_eq (M : Df2Mode d) (dflt : Df2St d) : M.stOr dflt = if M.code.1 = 2 then M.code.2 else dflt := by
  cases M <;> simp [Df2Mode.stOr, Df2Mode.code]

theorem measurable_stOr (dflt : Df2St d) : Measurable fun M : Df2Mode d => M.stOr dflt := by
  have he : (fun M : Df2Mode d => M.stOr dflt) = fun M => if M.code.1 = 2 then M.code.2 else dflt :=
    funext fun M => stOr_eq M dflt
  rw [he]
  exact Measurable.ite ((measurable_fst.comp measurable_mode_code) (measurableSet_singleton 2))
    (measurable_snd.comp measurable_mode_code) measurable_const

variable (ap : ApFun d) {Ω : Type} (θ : Ω → Θ) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)

/-- The parameter and the state before round `s`. -/
noncomputable def sig (s : ℕ) (ω : Ω) : Θ × Df2St d :=
  (θ ω, (EvGY.ctxW n δ Kθ ap θ ω).st (EvGY.pathW gθ θ ξ e ω) s)

theorem measurable_sig [MeasurableSpace Θ] {m : ℕ} [m0 : MeasurableSpace Ω] (𝒢 : Filtration ℕ m0)
    (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) (hθ : Measurable[𝒢 0] θ)
    (hξ : ∀ s, Measurable[𝒢 (s + 1)] (ξ s)) (he : ∀ s, Measurable[𝒢 (s + 1)] (e s)) {s : ℕ} (hs : s ≤ m) :
    Measurable[𝒢 s] (sig n δ Kθ gθ ap θ ξ e s) := by
  have hM := EvGY.measurable_mode n δ Kθ gθ ap hmeas 𝒢 θ ξ e hθ hξ he s hs
  have hst : Measurable[𝒢 s] fun ω =>
      ((EvGY.ctxW n δ Kθ ap θ ω).mode (EvGY.pathW gθ θ ξ e ω) s).stOr (df2Init (df2oPar d n δ) d) :=
    (measurable_stOr _).comp hM
  exact (hθ.mono (𝒢.mono (Nat.zero_le s)) le_rfl).prodMk hst

/-! ## The observation and the estimators on the path -/

section path

variable (ω : Ω) (s : ℕ)

theorem Y_eq : (EvGY.ctxW n δ Kθ ap θ ω).Y (EvGY.pathW gθ θ ξ e ω) s =
    fF n δ Kθ gθ s (sig n δ Kθ gθ ap θ ξ e s ω, ξ s ω) + fP n δ Kθ (sig n δ Kθ gθ ap θ ξ e s ω, ξ s ω) * e s ω := by
  simp only [Df2Ctx.Y, Df2Ctx.pip, Df2Ctx.play, Df2Ctx.X, Df2Ctx.w, fF, fP, sig, EvGY.xOf, df2Ext, EvGY.ctxW,
    EvGY.pathW, df2CtxAt, WithLp.toLp_smul]
  ring

theorem ghat_dot (y : Fin d → ℝ) :
    (EvGY.ctxW n δ Kθ ap θ ω).ghat (EvGY.pathW gθ θ ξ e ω) s ⬝ᵥ
        (y - ((EvGY.ctxW n δ Kθ ap θ ω).st (EvGY.pathW gθ θ ξ e ω) s).mu) =
      (EvGY.ctxW n δ Kθ ap θ ω).Y (EvGY.pathW gθ θ ξ e ω) s * phiL n δ y (sig n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.ghat, Df2Ctx.u, Df2Ctx.w, phiL, lin, sig, smul_dotProduct, smul_eq_mul, EvGY.ctxW,
    EvGY.pathW, df2CtxAt]
  ring

theorem shh_sq (hf : Df2St d → Fin d → ℝ) :
    df2Sq ((EvGY.ctxW n δ Kθ ap θ ω).shh (EvGY.pathW gθ θ ξ e ω) s)
        (hf ((EvGY.ctxW n δ Kθ ap θ ω).st (EvGY.pathW gθ θ ξ e ω) s)) =
      (EvGY.ctxW n δ Kθ ap θ ω).Y (EvGY.pathW gθ θ ξ e ω) s * phiH n δ hf (sig n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) := by
  simp only [Df2Ctx.shh, sq_smul, sq_sub, phiH, lin, sig, Df2Ctx.u, Df2Ctx.w, EvGY.ctxW, EvGY.pathW, df2CtxAt]
  have hv : ∀ (u v : Fin d → ℝ), df2Sq (vecMulVec u u) v = (u ⬝ᵥ v) ^ 2 := fun u v => by
    simp only [df2Sq, vecMulVec_mulVec]
    rw [op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u]; ring
  rw [hv]
  ring

end path

/-! ## The increments on the path -/

/-- Under the bound condition, the mean of `aOf` is the Gaussian integral of `fF φ`. -/
theorem mean_aOf (M : ℝ) (s : ℕ) (φ : Df2St d → (Fin d → ℝ) → ℝ) (σ : Θ × Df2St d) (hst : stB M σ.2) :
    mean (aOf n δ Kθ gθ M s φ) σ = ∫ z, fF n δ Kθ gθ s (σ, z) * φ σ.2 z ∂(gam d) := by
  unfold mean aOf
  simp only [hst, ↓reduceIte]

theorem zSeq_eq {ι : Type*} {m : ℕ} (M : ℝ) (φ : ι → Df2St d → (Fin d → ℝ) → ℝ) (c : ι) (ω : Ω) {s : ℕ}
    (hs : s < m) (hst : stB M (sig n δ Kθ gθ ap θ ξ e s ω).2) :
    zSeq m (fun c s => aOf n δ Kθ gθ M s (φ c)) (fun c _ => bOf n δ Kθ M (φ c)) (sig n δ Kθ gθ ap θ ξ e) ξ e c s ω =
      (EvGY.ctxW n δ Kθ ap θ ω).Y (EvGY.pathW gθ θ ξ e ω) s * φ c (sig n δ Kθ gθ ap θ ξ e s ω).2 (ξ s ω) -
        ∫ z, fF n δ Kθ gθ s (sig n δ Kθ gθ ap θ ξ e s ω, z) * φ c (sig n δ Kθ gθ ap θ ξ e s ω).2 z ∂(gam d) := by
  rw [zSeq_of_lt _ _ _ _ _ _ hs]
  unfold incr
  rw [mean_aOf n δ Kθ gθ M s (φ c) _ hst, Y_eq n δ Kθ gθ ap θ ξ e ω s]
  unfold aOf bOf
  simp only [hst, ↓reduceIte]
  ring

/-- Under the bound condition, `A² + B² ≤ (fF² + fP²) φ²`. -/
theorem sq_aOf_bOf_le (M : ℝ) (s : ℕ) (φ : Df2St d → (Fin d → ℝ) → ℝ) (x : (Θ × Df2St d) × (Fin d → ℝ)) :
    aOf n δ Kθ gθ M s φ x ^ 2 + bOf n δ Kθ M φ x ^ 2 ≤
      (fF n δ Kθ gθ s x ^ 2 + fP n δ Kθ x ^ 2) * φ x.1.2 x.2 ^ 2 := by
  unfold aOf bOf
  split_ifs
  · ring_nf; rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    positivity

end AdversarialBco.Poly.EvSI
