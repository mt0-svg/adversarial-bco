/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIPath
public import AdversarialBco.Poly.Df2EvSIMat

@[expose] public section

/-!
# One round up to the stopping time: the functions of a round

At a round of the context at the parameters, with `X(z) = μ_s + (1 - λ) A_s z`: the extension `eR` and the gauge
factor `pR` at the draw `z`, and `yR = e² + pip²`; their continuity, the integrability and the `L²` membership of a
function of polynomial growth under the Gaussian (`integrable_of_poly`, `memLp_two_of_poly`), and the pointwise
bounds on a body of the analysis (`eR_pR_le`, `yR_le`, `pR_sub_le`, `yR_le_poly`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

/-! ## The functions of a round -/

/-- The extension of a round at the draw `z` from the state `st`. -/
noncomputable def eR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Ext (df2oPar d n δ) K g (WithLp.toLp 2 (EvGY.xOf n δ st z))

/-- The gauge factor of a round at the draw `z` from the state `st`. -/
noncomputable def pR (n : ℕ) (δ : ℝ) (K : Set (E d)) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  df2Pip (df2oPar d n δ) K (WithLp.toLp 2 (EvGY.xOf n δ st z))

/-- `e² + pip²`. -/
noncomputable def yR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) : ℝ :=
  eR n δ K g st z ^ 2 + pR n δ K st z ^ 2

theorem continuous_xOf (n : ℕ) (δ : ℝ) (st : Df2St d) :
    Continuous fun z => (WithLp.toLp 2 (EvGY.xOf n δ st z) : E d) := by
  unfold EvGY.xOf
  have h : Continuous fun z : Fin d → ℝ => st.A *ᵥ z := (Matrix.mulVecLin st.A).continuous_of_finiteDimensional
  have h2 : Continuous fun z : Fin d → ℝ => st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ z) :=
    continuous_const.add (Continuous.const_smul h (1 - (df2oPar d n δ).lam))
  exact (PiLp.continuous_toLp 2 _).comp h2

theorem continuous_eR (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (L : ℝ)
    (hL : ∀ x y, |df2Ext (df2oPar d n δ) K g x - df2Ext (df2oPar d n δ) K g y| ≤ L * ‖x - y‖) (st : Df2St d) :
    Continuous (eR n δ K g st) :=
  (continuous_of_lip _ L hL).comp (continuous_xOf n δ st)

theorem continuous_pR (n : ℕ) (δ : ℝ) (K : Set (E d)) (hK : Convex ℝ K) (hball : Metric.closedBall 0 1 ⊆ K)
    (st : Df2St d) : Continuous (pR n δ K st) := by
  have hn : K ∈ nhds (0 : E d) := Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball
  have hg : Continuous (gauge K) := continuous_gauge hK hn
  unfold pR df2Pip
  exact continuous_const.max ((hg.comp (continuous_xOf n δ st)).div_const _)

/-! ## Integrability -/

theorem integrable_of_poly {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gam d)) (K : ℝ) (k : ℕ)
    (hb : ∀ z, |f z| ≤ K * (1 + ‖z‖) ^ k) : Integrable f (gam d) :=
  ((integrable_poly_gam k).const_mul K).mono' hf
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)

theorem memLp_two_of_poly {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gam d)) (K : ℝ) (k : ℕ)
    (hb : ∀ z, |f z| ≤ K * (1 + ‖z‖) ^ k) : MemLp f 2 (gam d) := by
  rw [memLp_two_iff_integrable_sq hf]
  refine integrable_of_poly (hf.pow 2) (K ^ 2) (k * 2) fun z => ?_
  rw [abs_pow, pow_mul]
  calc |f z| ^ 2 ≤ (K * (1 + ‖z‖) ^ k) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb z) 2
    _ = K ^ 2 * ((1 + ‖z‖) ^ k) ^ 2 := by ring

/-! ## Pointwise bounds -/

theorem eR_pR_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) {M : ℝ} (hM : 0 ≤ M) {st : Df2St d}
    (hst : stB M st) (z : Fin d → ℝ) :
    |eR n δ K g st z| ≤ kF d n δ M * (1 + ‖z‖) ∧ |pR n δ K st z| ≤ kF d n δ M * (1 + ‖z‖) :=
  fF_fP_le n δ (fun _ : Unit => K) (fun _ _ => g) (m := 1) (fun _ => hbody) (fun _ _ _ => hg) he0 he1 hl0 hl1 hM
    (s := 0) Nat.zero_lt_one (((), st), z) hst

theorem yR_nonneg (n : ℕ) (δ : ℝ) (K : Set (E d)) (g : E d → ℝ) (st : Df2St d) (z : Fin d → ℝ) :
    0 ≤ yR n δ K g st z := by
  unfold yR; positivity

theorem yR_abs_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) {M : ℝ} (hM : 0 ≤ M) {st : Df2St d}
    (hst : stB M st) (z : Fin d → ℝ) :
    |yR n δ K g st z| ≤ 2 * kF d n δ M ^ 2 * (1 + ‖z‖) ^ 2 := by
  obtain ⟨h1, h2⟩ := eR_pR_le hbody hg he0 he1 hl0 hl1 hM hst z
  rw [abs_of_nonneg (yR_nonneg n δ K g st z)]
  unfold yR
  have a1 : eR n δ K g st z ^ 2 ≤ (kF d n δ M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : pR n δ K st z ^ 2 ≤ (kF d n δ M * (1 + ‖z‖)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith

/-- `e² + pip² ≤ 6 + 10 (pip - 1)²/ε²`. -/
theorem yR_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2) (st : Df2St d)
    (z : Fin d → ℝ) :
    yR n δ K g st z ≤ 6 + 10 * (pR n δ K st z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 := by
  obtain ⟨hF0, hF1, hP1, -⟩ := ext_pip_bounds n δ K hbody g hg he0 he1 (WithLp.toLp 2 (EvGY.xOf n δ st z))
  unfold yR
  change df2Ext (df2oPar d n δ) K g _ ^ 2 + df2Pip (df2oPar d n δ) K _ ^ 2 ≤
    6 + 10 * (df2Pip (df2oPar d n δ) K _ - 1) ^ 2 / (df2oPar d n δ).eps ^ 2
  set ε := (df2oPar d n δ).eps
  set q := df2Pip (df2oPar d n δ) K (WithLp.toLp 2 (EvGY.xOf n δ st z))
  set F := df2Ext (df2oPar d n δ) K g (WithLp.toLp 2 (EvGY.xOf n δ st z))
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
theorem pR_sub_le {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) (st : Df2St d)
    (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    0 ≤ pR n δ K st z - 1 ∧
      pR n δ K st z - 1 ≤ 2 * (Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z)) := by
  obtain ⟨-, -, hP1, hP2⟩ := ext_pip_bounds n δ K hbody g hg he0 he1 (WithLp.toLp 2 (EvGY.xOf n δ st z))
  refine ⟨by unfold pR; linarith, ?_⟩
  have hX : ‖(WithLp.toLp 2 (EvGY.xOf n δ st z) : E d)‖ ≤ Real.sqrt (st.mu ⬝ᵥ st.mu) + Real.sqrt (z ⬝ᵥ z) := by
    rw [norm_toLp]
    unfold EvGY.xOf
    have t := (oNorm_tri st.mu ((1 - (df2oPar d n δ).lam) • (st.A *ᵥ z)) 0 ∅ fun _ => 0).1
    have ta := (oNorm_tri (st.A *ᵥ z) 0 (1 - (df2oPar d n δ).lam) ∅ fun _ => 0).2.1
    have hab : |1 - (df2oPar d n δ).lam| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hAz : Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) ≤ Real.sqrt (z ⬝ᵥ z) := Real.sqrt_le_sqrt (hA z)
    rw [ta] at t
    have h0 := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
    nlinarith [abs_nonneg (1 - (df2oPar d n δ).lam)]
  unfold pR; linarith

/-- `e² + pip² ≤ 6 + 80 (|μ|² + |z|²)/ε²`. -/
theorem yR_le_poly {n : ℕ} {δ : ℝ} {K : Set (E d)} {g : E d → ℝ} (hbody : Df2Body d (df2oPar d n δ).R K)
    (hg : AdmLoss K g) (he0 : 0 < (df2oPar d n δ).eps) (he1 : (df2oPar d n δ).eps ≤ 1 / 2)
    (hl0 : 0 ≤ (df2oPar d n δ).lam) (hl1 : (df2oPar d n δ).lam ≤ 1) (st : Df2St d)
    (hA : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ w ⬝ᵥ w) (z : Fin d → ℝ) :
    yR n δ K g st z ≤ 6 + 80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / (df2oPar d n δ).eps ^ 2 := by
  have h1 := yR_le hbody hg he0 he1 st z
  obtain ⟨h0, h2⟩ := pR_sub_le hbody hg he0 he1 hl0 hl1 st hA z
  have hm := Real.sq_sqrt (dot_self_nonneg' st.mu)
  have hz := Real.sq_sqrt (dot_self_nonneg' z)
  have h3 : (pR n δ K st z - 1) ^ 2 ≤ 8 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) := by
    have := pow_le_pow_left₀ h0 h2 2
    nlinarith [sq_nonneg (Real.sqrt (st.mu ⬝ᵥ st.mu) - Real.sqrt (z ⬝ᵥ z))]
  have he2 : 0 < (df2oPar d n δ).eps ^ 2 := by positivity
  have h4 : 10 * (pR n δ K st z - 1) ^ 2 / (df2oPar d n δ).eps ^ 2 ≤
      80 * (st.mu ⬝ᵥ st.mu + z ⬝ᵥ z) / (df2oPar d n δ).eps ^ 2 := by
    apply div_le_div_of_nonneg_right _ he2.le; linarith
  linarith

end AdversarialBco.Poly.EvSI
