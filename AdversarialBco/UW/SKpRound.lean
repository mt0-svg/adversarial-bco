/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCRound
public import AdversarialBco.UW.SKpCond
public import AdversarialBco.UW.EvCNeeds

@[expose] public section

/-!
# Lemma SK' in a round of the epoch

The coefficients of a round, truncated to the good states (`goodE`: bounded, of spread at most `2σ²`, centre in
`K_ε`), are what Lemma U with sure ranges (`LemmaUSetW`) and the bias (`bias_round`) read: `EtrE` (the extension),
`PtrE` (the gauge factor), `DtrE φ` (a direction). On a good state:

* `ptr_le`: `pip(X(z)) ≤ 1 + |z|₂`; `etr_abs_le`: `|e(X)| ≤ (1 + 2/ε) pip(X)`;
* `ptr_tail`: `γ(pip(X) > 10) ≤ e^{-18 L}`, the gauge tail at the threshold `5 ≥ 10 (1 - ε)`;
* `ptr_off`: `pip ≤ 10`, `|y| ≤ t0` give `|e + pip y| ≤ 10 + 18/ε + 10 t0`.

`biasE` (Lemma SK' (ii) to (iv) at the table): when `b0 ≥ 2d + L + 2`, `y0 ≥ 10 + 18/ε + 10 (L/3)^{1/2}` and
`L = 36 log(1/δ_e)`, the conditional mean of `obsW(ξ, E + P e) D` is `∫ E D dγ` up to `lvBias (E_z D⁴)^{1/4}`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

section Trunc

variable (p : Df2OPar) {Θ : Type} (Kθ : Θ → Set (E d)) (gθ : ℕ → Θ → E d → ℝ) (M : ℝ)

/-- The good states of a round: `stB M`, the spread `A Aᵀ ≤ 2σ²` and the centre in `K_ε`. -/
def goodE (x : Θ × Df2St d) : Prop :=
  EvSI.stB M x.2 ∧ x.2.A ∈ EvSI.bdSet (2 * p.sig2) ∧ gauge (Kθ x.1) (WithLp.toLp 2 x.2.mu) ≤ 1 - p.eps

open Classical in
/-- The extension of round `s` on the good states, `0` elsewhere. -/
noncomputable def EtrE (s : ℕ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  if goodE p Kθ M x.1 then fFE p Kθ gθ s x else 0

open Classical in
/-- The gauge factor on the good states, `0` elsewhere. -/
noncomputable def PtrE (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  if goodE p Kθ M x.1 then fPE p Kθ x else 0

open Classical in
/-- A direction on the good states, `0` elsewhere. -/
noncomputable def DtrE (φ : Df2St d → (Fin d → ℝ) → ℝ) (x : (Θ × Df2St d) × (Fin d → ℝ)) : ℝ :=
  if goodE p Kθ M x.1 then φ x.1.2 x.2 else 0

variable {p Kθ gθ M}

theorem EtrE_of {s : ℕ} {x : (Θ × Df2St d) × (Fin d → ℝ)} (h : goodE p Kθ M x.1) :
    EtrE p Kθ gθ M s x = fFE p Kθ gθ s x := by
  simp only [EtrE, h, ↓reduceIte]

theorem PtrE_of {x : (Θ × Df2St d) × (Fin d → ℝ)} (h : goodE p Kθ M x.1) : PtrE p Kθ M x = fPE p Kθ x := by
  simp only [PtrE, h, ↓reduceIte]

theorem DtrE_of {φ : Df2St d → (Fin d → ℝ) → ℝ} {x : (Θ × Df2St d) × (Fin d → ℝ)} (h : goodE p Kθ M x.1) :
    DtrE p Kθ M φ x = φ x.1.2 x.2 := by
  simp only [DtrE, h, ↓reduceIte]

/-! ### Measurability -/

theorem measurable_fFE [MeasurableSpace Θ] {s : ℕ}
    (hext : Measurable fun x : Θ × E d => df2Ext p (Kθ x.1) (gθ s x.1) x.2) : Measurable (fFE p Kθ gθ s) := by
  have hX : Measurable fun x : (Θ × Df2St d) × (Fin d → ℝ) => (WithLp.toLp 2 (xOfE p x.1.2 x.2) : E d) :=
    (WithLp.measurable_toLp 2 _).comp
      ((measurable_xOfE p).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := hext.comp ((measurable_fst.comp measurable_fst).prodMk hX)
  exact h

theorem measurable_fPE [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) :
    Measurable (fPE p Kθ) := by
  have hX : Measurable fun x : (Θ × Df2St d) × (Fin d → ℝ) => (WithLp.toLp 2 (xOfE p x.1.2 x.2) : E d) :=
    (WithLp.measurable_toLp 2 _).comp
      ((measurable_xOfE p).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  unfold fPE df2Pip
  exact measurable_const.max ((hg.comp ((measurable_fst.comp measurable_fst).prodMk hX)).div_const _)

theorem measurableSet_goodE [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) :
    MeasurableSet {x : Θ × Df2St d | goodE p Kθ M x} := by
  have h1 : MeasurableSet {x : Θ × Df2St d | EvSI.stB M x.2} := (EvSI.measurableSet_stB M).preimage measurable_snd
  have h2 : MeasurableSet {x : Θ × Df2St d | x.2.A ∈ EvSI.bdSet (2 * p.sig2)} :=
    (EvSI.isClosed_bdSet _).measurableSet.preimage (ApMeas.measurable_st_A.comp measurable_snd)
  have h3 : MeasurableSet {x : Θ × Df2St d | gauge (Kθ x.1) (WithLp.toLp 2 x.2.mu) ≤ 1 - p.eps} :=
    measurableSet_le (hg.comp (measurable_fst.prodMk
      ((WithLp.measurable_toLp 2 _).comp (ApMeas.measurable_st_mu.comp measurable_snd)))) measurable_const
  exact h1.inter (h2.inter h3)

theorem measurable_EtrE [MeasurableSpace Θ] {s : ℕ} (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2)
    (hext : Measurable fun x : Θ × E d => df2Ext p (Kθ x.1) (gθ s x.1) x.2) : Measurable (EtrE p Kθ gθ M s) := by
  unfold EtrE
  exact Measurable.ite ((measurableSet_goodE hg).preimage measurable_fst) (measurable_fFE hext) measurable_const

theorem measurable_PtrE [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2) :
    Measurable (PtrE p Kθ M) := by
  unfold PtrE
  exact Measurable.ite ((measurableSet_goodE hg).preimage measurable_fst) (measurable_fPE hg) measurable_const

theorem measurable_DtrE [MeasurableSpace Θ] (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2)
    {φ : Df2St d → (Fin d → ℝ) → ℝ} (hφ : Measurable fun x : Df2St d × (Fin d → ℝ) => φ x.1 x.2) :
    Measurable (DtrE p Kθ M φ) := by
  unfold DtrE
  exact Measurable.ite ((measurableSet_goodE hg).preimage measurable_fst)
    (hφ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) measurable_const

/-! ### On a good state -/

/-- `|A z|₂ ≤ (2σ²)^{1/2} |z|₂` on `bdSet (2σ²)`. -/
theorem norm_A_le {A : Matrix (Fin d) (Fin d) ℝ} {k : ℝ} (hk : 0 ≤ k) (hA : A ∈ EvSI.bdSet k)
    (z : Fin d → ℝ) : Real.sqrt ((A *ᵥ z) ⬝ᵥ (A *ᵥ z)) ≤ Real.sqrt k * Real.sqrt (z ⬝ᵥ z) := by
  rw [← Real.sqrt_mul hk]
  exact Real.sqrt_le_sqrt (hA z)

/-- On a good state, `pip(X(z)) ≤ 1 + |z|₂`. -/
theorem ptr_le {R : ℝ} {q : Θ} {st : Df2St d} (hK : Df2Body d R (Kθ q)) (he0 : 0 < p.eps)
    (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1) (hL : 1 ≤ p.Le) (hsig : p.sig2 = 1 / (8 * p.Le))
    (hg : goodE p Kθ M (q, st)) (z : Fin d → ℝ) :
    fPE p Kθ ((q, st), z) ≤ 1 + Real.sqrt (z ⬝ᵥ z) := by
  obtain ⟨hKc, -, hball, -, -⟩ := hK
  obtain ⟨-, hA, hmu⟩ := hg
  have habs : Absorbent ℝ (Kθ q) := absorbent_nhds_zero
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) hball)
  have hLp : 0 < p.Le := by linarith
  have hs0 : 0 ≤ 2 * p.sig2 := by rw [hsig]; exact mul_nonneg zero_le_two (div_nonneg zero_le_one (by linarith))
  have h4 : 2 * p.sig2 ≤ 1 / 4 := by
    rw [hsig, mul_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hs1 : Real.sqrt (2 * p.sig2) ≤ 1 / 2 :=
    calc Real.sqrt (2 * p.sig2) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt h4
      _ = 1 / 2 := by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hz := Real.sqrt_nonneg (z ⬝ᵥ z)
  set w : Fin d → ℝ := (1 - p.lam) • (st.A *ᵥ z) with hw
  have hX : (WithLp.toLp 2 (xOfE p st z) : E d) = WithLp.toLp 2 st.mu + WithLp.toLp 2 w := by
    unfold xOfE; rw [WithLp.toLp_add]
  have hw2 : ‖(WithLp.toLp 2 w : E d)‖ ≤ 1 / 2 * Real.sqrt (z ⬝ᵥ z) := by
    rw [EvSI.norm_toLp, hw]
    have e1 : ((1 - p.lam) • (st.A *ᵥ z)) ⬝ᵥ ((1 - p.lam) • (st.A *ᵥ z)) =
        (1 - p.lam) ^ 2 * ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    have h1 := norm_A_le hs0 hA z
    have h2 : 1 - p.lam ≤ 1 := by linarith
    have h3 := Real.sqrt_nonneg ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z))
    calc (1 - p.lam) * Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) ≤ 1 * Real.sqrt ((st.A *ᵥ z) ⬝ᵥ (st.A *ᵥ z)) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ Real.sqrt (2 * p.sig2) * Real.sqrt (z ⬝ᵥ z) := by rw [one_mul]; exact h1
      _ ≤ 1 / 2 * Real.sqrt (z ⬝ᵥ z) := mul_le_mul_of_nonneg_right hs1 hz
  have hgX : gauge (Kθ q) (WithLp.toLp 2 (xOfE p st z)) ≤ 1 - p.eps + 1 / 2 * Real.sqrt (z ⬝ᵥ z) := by
    rw [hX]
    have h1 := gauge_add_le hKc habs (WithLp.toLp 2 st.mu) (WithLp.toLp 2 w)
    have h2 := EvSI.gauge_le_norm' (Kθ q) hball (WithLp.toLp 2 w)
    linarith
  have h1e : 0 < 1 - p.eps := by linarith
  unfold fPE df2Pip
  refine max_le (by linarith) ?_
  rw [div_le_iff₀ h1e]
  nlinarith

/-- On a good state, `|e(X)| ≤ (1 + 2/ε) pip(X)` (and `0 ≤ e(X)`). -/
theorem etr_abs_le {R : ℝ} {q : Θ} {st : Df2St d} {s : ℕ} (hK : Df2Body d R (Kθ q)) (hadm : AdmLoss (Kθ q) (gθ s q))
    (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (z : Fin d → ℝ) :
    0 ≤ fFE p Kθ gθ s ((q, st), z) ∧ |fFE p Kθ gθ s ((q, st), z)| ≤ (1 + 2 / p.eps) * fPE p Kθ ((q, st), z) ∧
      1 ≤ fPE p Kθ ((q, st), z) ∧
      fFE p Kθ gθ s ((q, st), z) ≤ fPE p Kθ ((q, st), z) + 2 * (fPE p Kθ ((q, st), z) - 1) / p.eps := by
  obtain ⟨hF0, hF1, hP1, -, -⟩ := ext_pip_boundsE p (Kθ q) hK (gθ s q) hadm he0 he1
    (WithLp.toLp 2 (xOfE p st z))
  change 0 ≤ df2Ext p (Kθ q) (gθ s q) _ ∧ |df2Ext p (Kθ q) (gθ s q) _| ≤ (1 + 2 / p.eps) * df2Pip p (Kθ q) _ ∧
    1 ≤ df2Pip p (Kθ q) _ ∧ df2Ext p (Kθ q) (gθ s q) _ ≤ df2Pip p (Kθ q) _ + 2 * (df2Pip p (Kθ q) _ - 1) / p.eps
  refine ⟨hF0, ?_, hP1, hF1⟩
  rw [abs_of_nonneg hF0]
  refine hF1.trans ?_
  have h2 : 2 * (df2Pip p (Kθ q) (WithLp.toLp 2 (xOfE p st z)) - 1) / p.eps ≤
      2 / p.eps * df2Pip p (Kθ q) (WithLp.toLp 2 (xOfE p st z)) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right he0]; linarith
  linarith

/-- On a good state, the gauge factor exceeds `10` with probability at most `e^{-18 L}`. -/
theorem ptr_tail (hd : 1 ≤ d) {R : ℝ} {q : Θ} {st : Df2St d} (hK : Df2Body d R (Kθ q)) (he0 : 0 < p.eps)
    (he1 : p.eps ≤ 1 / 2) (hl0 : 0 ≤ p.lam) (hl1 : p.lam ≤ 1) (hL : 1 ≤ p.Le) (hsig : p.sig2 = 1 / (8 * p.Le))
    (hg : goodE p Kθ M (q, st)) :
    EvSI.gam d {z | 10 < fPE p Kθ ((q, st), z)} ≤ ENNReal.ofReal (Real.exp (-(18 * p.Le))) := by
  obtain ⟨hKc, hKcl, hball, -, hMw⟩ := hK
  obtain ⟨-, hA, hmu⟩ := hg
  have hmu1 : gauge (Kθ q) (WithLp.toLp 2 st.mu) ≤ 1 := by linarith
  have hA' : ∀ w, (st.A *ᵥ w) ⬝ᵥ (st.A *ᵥ w) ≤ 2 * (1 / (8 * p.Le)) * (w ⬝ᵥ w) := fun w => by
    rw [← hsig]; exact hA w
  have h := SKp.pi_round_at hd (Kθ q) hKc hKcl hball hMw st.mu hmu1 st.A p.lam hl0 hl1 p.Le hL hA' 5 (by norm_num)
  have e : -(2 * p.Le * (5 - 2) ^ 2) = -(18 * p.Le) := by ring
  rw [e] at h
  refine le_trans (measure_mono fun z hz => ?_) h
  simp only [Set.mem_ofPred_eq] at hz ⊢
  unfold fPE df2Pip at hz
  have h1e : 0 < 1 - p.eps := by linarith
  have h2 : 10 < gauge (Kθ q) (WithLp.toLp 2 (xOfE p st z)) / (1 - p.eps) := by
    rcases lt_max_iff.1 hz with h | h
    · norm_num at h
    · exact h
  rw [lt_div_iff₀ h1e] at h2
  unfold xOfE at h2
  linarith

/-- Off the tails, on a good state, the unweighted value stays below `10 + 18/ε + 10 t0`. -/
theorem ptr_off {R : ℝ} {q : Θ} {st : Df2St d} {s : ℕ} (hK : Df2Body d R (Kθ q)) (hadm : AdmLoss (Kθ q) (gθ s q))
    (he0 : 0 < p.eps) (he1 : p.eps ≤ 1 / 2) (z : Fin d → ℝ) (y t0 : ℝ) (hP : fPE p Kθ ((q, st), z) ≤ 10)
    (hy : |y| ≤ t0) :
    |fFE p Kθ gθ s ((q, st), z) + fPE p Kθ ((q, st), z) * y| ≤ 10 + 18 / p.eps + 10 * t0 := by
  obtain ⟨hF0, -, hP1, hF1⟩ := etr_abs_le (st := st) hK hadm he0 he1 z
  set F := fFE p Kθ gθ s ((q, st), z)
  set P := fPE p Kθ ((q, st), z)
  have h1 : F ≤ 10 + 18 / p.eps := by
    have : 2 * (P - 1) / p.eps ≤ 18 / p.eps := div_le_div_of_nonneg_right (by linarith) he0.le
    linarith
  have h2 : |P * y| ≤ 10 * t0 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    have := abs_nonneg y
    nlinarith
  calc |F + P * y| ≤ |F| + |P * y| := abs_add_le _ _
    _ ≤ (10 + 18 / p.eps) + 10 * t0 := by rw [abs_of_nonneg hF0]; linarith

end Trunc

/-! ## The bias of a round -/

/-- The parameters a round reads for Lemma SK'. -/
structure SKPar (p : Df2OPar) : Prop where
  eps0 : 0 < p.eps
  eps1 : p.eps ≤ 1 / 2
  lam0 : 0 ≤ p.lam
  lam1 : p.lam ≤ 1
  Le1 : 1 ≤ p.Le
  sig : p.sig2 = 1 / (8 * p.Le)
  Lede : p.Le = 36 * Real.log (1 / p.δe)
  de0 : 0 < p.δe
  de1 : p.δe ≤ 1

/-- `exp(-k L/36) = δ_e^k` when `L = 36 log(1/δ_e)`. -/
theorem exp_Le_div {p : Df2OPar} (hp : SKPar p) (k : ℕ) : Real.exp (-(k * (p.Le / 36))) = p.δe ^ k := by
  rw [hp.Lede, show -((k : ℝ) * (36 * Real.log (1 / p.δe) / 36)) = (k : ℝ) * Real.log p.δe by
    rw [one_div, Real.log_inv]; ring, Real.exp_nat_mul, Real.exp_log hp.de0]

/-- `(y⁴)^{1/4} = y` for `y ≥ 0`. -/
theorem pow_four_rpow {y : ℝ} (hy : 0 ≤ y) : (y ^ 4) ^ (1 / 4 : ℝ) = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

section Bias

variable {p : Df2OPar} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ} {M R : ℝ}

omit [MeasurableSpace Θ] in
/-- The truncated coefficients grow at most quadratically, uniformly in the state: the constant
`(1 + 2/ε)(1 + √d) + Kφ`. -/
theorem trunc_growth (hp : SKPar p) (hbody : ∀ q, Df2Body d R (Kθ q)) {s : ℕ}
    (hadm : ∀ q, AdmLoss (Kθ q) (gθ s q)) {φ : Df2St d → (Fin d → ℝ) → ℝ} {Kφ : ℝ} (hKφ : 0 ≤ Kφ)
    (hφb : ∀ st, EvSI.stB M st → ∀ z, |φ st z| ≤ Kφ * (1 + ‖z‖) ^ 2) :
    (∀ x, |EtrE p Kθ gθ M s x| ≤ ((1 + 2 / p.eps) * (1 + Real.sqrt d) + Kφ) * (1 + ‖x.2‖) ^ 2) ∧
    (∀ x, |PtrE p Kθ M x| ≤ ((1 + 2 / p.eps) * (1 + Real.sqrt d) + Kφ) * (1 + ‖x.2‖) ^ 2) ∧
    (∀ x, |DtrE p Kθ M φ x| ≤ ((1 + 2 / p.eps) * (1 + Real.sqrt d) + Kφ) * (1 + ‖x.2‖) ^ 2) := by
  have he0 := hp.eps0
  have he1 := hp.eps1
  have hLe0 : 0 ≤ p.Le := by linarith [hp.Le1]
  set C := 1 + 2 / p.eps with hCdef
  have h2e : 0 ≤ 2 / p.eps := div_nonneg (by norm_num) he0.le
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hsd := Real.sqrt_nonneg (d : ℝ)
  set K := C * (1 + Real.sqrt d) + Kφ with hKdef
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hC0 (by positivity)) hKφ
  have hpow : ∀ z : Fin d → ℝ, 1 + ‖z‖ ≤ (1 + ‖z‖) ^ 2 := fun z => by nlinarith [norm_nonneg z]
  -- the bounds on a good state
  have hPg : ∀ (q : Θ) (st : Df2St d), goodE p Kθ M (q, st) → ∀ z,
      0 ≤ fPE p Kθ ((q, st), z) ∧ fPE p Kθ ((q, st), z) ≤ 1 + Real.sqrt (z ⬝ᵥ z) := fun q st hgd z =>
    ⟨le_trans zero_le_one (etr_abs_le (st := st) (s := s) (hbody q) (hadm q) he0 he1 z).2.2.1,
      ptr_le (hbody q) he0 he1 hp.lam0 hp.lam1 hp.Le1 hp.sig hgd z⟩
  have hEg : ∀ (q : Θ) (st : Df2St d), goodE p Kθ M (q, st) → ∀ z,
      |fFE p Kθ gθ s ((q, st), z)| ≤ C * fPE p Kθ ((q, st), z) := fun q st _ z =>
    (etr_abs_le (st := st) (hbody q) (hadm q) he0 he1 z).2.1
  have hpoly : ∀ z : Fin d → ℝ, 1 + Real.sqrt (z ⬝ᵥ z) ≤ (1 + Real.sqrt d) * (1 + ‖z‖) ^ 2 := by
    intro z
    have h1 := SKp.sqrt_dot_le_poly z
    have h2 := hpow z
    have hn := norm_nonneg z
    nlinarith
  -- growth
  have hEK : ∀ x, |EtrE p Kθ gθ M s x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold EtrE
    split_ifs with hgd
    · have h1 := hEg q st hgd z
      have h2 := (hPg q st hgd z).2
      have h3 := hpoly z
      calc |fFE p Kθ gθ s ((q, st), z)| ≤ C * fPE p Kθ ((q, st), z) := h1
        _ ≤ C * ((1 + Real.sqrt d) * (1 + ‖z‖) ^ 2) := mul_le_mul_of_nonneg_left (h2.trans h3) hC0
        _ ≤ K * (1 + ‖z‖) ^ 2 := by rw [hKdef]; nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  have hPK : ∀ x, |PtrE p Kθ M x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold PtrE
    split_ifs with hgd
    · obtain ⟨h0, h2⟩ := hPg q st hgd z
      have h3 := hpoly z
      rw [abs_of_nonneg h0]
      calc fPE p Kθ ((q, st), z) ≤ (1 + Real.sqrt d) * (1 + ‖z‖) ^ 2 := h2.trans h3
        _ ≤ K * (1 + ‖z‖) ^ 2 := by rw [hKdef]; nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  have hDK : ∀ x, |DtrE p Kθ M φ x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold DtrE
    split_ifs with hgd
    · have h1 := hφb st hgd.1 z
      calc |φ st z| ≤ Kφ * (1 + ‖z‖) ^ 2 := h1
        _ ≤ K * (1 + ‖z‖) ^ 2 := by
          rw [hKdef]; have : 0 ≤ C * (1 + Real.sqrt d) := mul_nonneg hC0 (by positivity)
          nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  exact ⟨hEK, hPK, hDK⟩

/-- **Lemma SK' (ii) to (iv) in a round of the epoch**: the conditional mean of the weighted and clipped increment
`obsW(ξ, E + P e) D` is Lemma ub's mean `∫ E D dγ` up to `lvBias (E_z D⁴)^{1/4}`. -/
theorem biasE (hd : 1 ≤ d) (hp : SKPar p) (hbody : ∀ q, Df2Body d R (Kθ q)) {s : ℕ}
    (hadm : ∀ q, AdmLoss (Kθ q) (gθ s q)) (hg : Measurable fun x : Θ × E d => gauge (Kθ x.1) x.2)
    (hext : Measurable fun x : Θ × E d => df2Ext p (Kθ x.1) (gθ s x.1) x.2) {b0 y0 : ℝ}
    (hb0 : 2 * d + p.Le + 2 ≤ b0) (hy0 : 10 + 18 / p.eps + 10 * Real.sqrt (p.Le / 3) ≤ y0)
    {φ : Df2St d → (Fin d → ℝ) → ℝ} (hφ : Measurable fun x : Df2St d × (Fin d → ℝ) => φ x.1 x.2) {Kφ : ℝ}
    (hKφ : 0 ≤ Kφ) (hφb : ∀ st, EvSI.stB M st → ∀ z, |φ st z| ≤ Kφ * (1 + ‖z‖) ^ 2)
    {Ω : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h𝒢 : 𝒢 ≤ m0) (σ : Ω → Θ × Df2St d) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ) (hσ : Measurable[𝒢] σ)
    (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = EvSI.gam d)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ) (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2) :
    ∀ᵐ ω ∂μ, |μ[fun ω => obsW b0 y0 (ξ ω) (EtrE p Kθ gθ M s (σ ω, ξ ω) + PtrE p Kθ M (σ ω, ξ ω) * e ω) *
          DtrE p Kθ M φ (σ ω, ξ ω) | 𝒢] ω -
        ∫ z, EtrE p Kθ gθ M s (σ ω, z) * DtrE p Kθ M φ (σ ω, z) ∂(EvSI.gam d)| ≤
      lvBias p d * (∫ z, DtrE p Kθ M φ (σ ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := by
  have he0 := hp.eps0
  have he1 := hp.eps1
  have hLe0 : 0 ≤ p.Le := by linarith [hp.Le1]
  set C := 1 + 2 / p.eps with hCdef
  have h2e : 0 ≤ 2 / p.eps := div_nonneg (by norm_num) he0.le
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hsd := Real.sqrt_nonneg (d : ℝ)
  set K := C * (1 + Real.sqrt d) + Kφ with hKdef
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hC0 (by positivity)) hKφ
  have hpow : ∀ z : Fin d → ℝ, 1 + ‖z‖ ≤ (1 + ‖z‖) ^ 2 := fun z => by nlinarith [norm_nonneg z]
  -- the bounds on a good state
  have hPg : ∀ (q : Θ) (st : Df2St d), goodE p Kθ M (q, st) → ∀ z,
      0 ≤ fPE p Kθ ((q, st), z) ∧ fPE p Kθ ((q, st), z) ≤ 1 + Real.sqrt (z ⬝ᵥ z) := fun q st hgd z =>
    ⟨le_trans zero_le_one (etr_abs_le (st := st) (s := s) (hbody q) (hadm q) he0 he1 z).2.2.1,
      ptr_le (hbody q) he0 he1 hp.lam0 hp.lam1 hp.Le1 hp.sig hgd z⟩
  have hEg : ∀ (q : Θ) (st : Df2St d), goodE p Kθ M (q, st) → ∀ z,
      |fFE p Kθ gθ s ((q, st), z)| ≤ C * fPE p Kθ ((q, st), z) := fun q st _ z =>
    (etr_abs_le (st := st) (hbody q) (hadm q) he0 he1 z).2.1
  have hpoly : ∀ z : Fin d → ℝ, 1 + Real.sqrt (z ⬝ᵥ z) ≤ (1 + Real.sqrt d) * (1 + ‖z‖) ^ 2 := by
    intro z
    have h1 := SKp.sqrt_dot_le_poly z
    have h2 := hpow z
    have hn := norm_nonneg z
    nlinarith
  -- growth
  have hEK : ∀ x, |EtrE p Kθ gθ M s x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold EtrE
    split_ifs with hgd
    · have h1 := hEg q st hgd z
      have h2 := (hPg q st hgd z).2
      have h3 := hpoly z
      calc |fFE p Kθ gθ s ((q, st), z)| ≤ C * fPE p Kθ ((q, st), z) := h1
        _ ≤ C * ((1 + Real.sqrt d) * (1 + ‖z‖) ^ 2) := mul_le_mul_of_nonneg_left (h2.trans h3) hC0
        _ ≤ K * (1 + ‖z‖) ^ 2 := by rw [hKdef]; nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  have hPK : ∀ x, |PtrE p Kθ M x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold PtrE
    split_ifs with hgd
    · obtain ⟨h0, h2⟩ := hPg q st hgd z
      have h3 := hpoly z
      rw [abs_of_nonneg h0]
      calc fPE p Kθ ((q, st), z) ≤ (1 + Real.sqrt d) * (1 + ‖z‖) ^ 2 := h2.trans h3
        _ ≤ K * (1 + ‖z‖) ^ 2 := by rw [hKdef]; nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  have hDK : ∀ x, |DtrE p Kθ M φ x| ≤ K * (1 + ‖x.2‖) ^ 2 := by
    rintro ⟨⟨q, st⟩, z⟩
    unfold DtrE
    split_ifs with hgd
    · have h1 := hφb st hgd.1 z
      calc |φ st z| ≤ Kφ * (1 + ‖z‖) ^ 2 := h1
        _ ≤ K * (1 + ‖z‖) ^ 2 := by
          rw [hKdef]; have : 0 ≤ C * (1 + Real.sqrt d) := mul_nonneg hC0 (by positivity)
          nlinarith [sq_nonneg (1 + ‖z‖)]
    · rw [abs_zero]; exact mul_nonneg hK0 (by positivity)
  -- the value
  have hYb : ∀ x y, |EtrE p Kθ gθ M s x + PtrE p Kθ M x * y| ≤
      C * (1 + Real.sqrt (x.2 ⬝ᵥ x.2)) * (1 + |y|) := by
    rintro ⟨⟨q, st⟩, z⟩ y
    have hz := Real.sqrt_nonneg (z ⬝ᵥ z)
    unfold EtrE PtrE
    split_ifs with hgd
    · have h1 := hEg q st hgd z
      obtain ⟨h0, h2⟩ := hPg q st hgd z
      have hy := abs_nonneg y
      calc |fFE p Kθ gθ s ((q, st), z) + fPE p Kθ ((q, st), z) * y|
          ≤ |fFE p Kθ gθ s ((q, st), z)| + |fPE p Kθ ((q, st), z) * y| := abs_add_le _ _
        _ ≤ C * fPE p Kθ ((q, st), z) + fPE p Kθ ((q, st), z) * |y| := by
            rw [abs_mul, abs_of_nonneg h0]; linarith
        _ ≤ C * fPE p Kθ ((q, st), z) * (1 + |y|) := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hC1) h0) hy]
        _ ≤ C * (1 + Real.sqrt (z ⬝ᵥ z)) * (1 + |y|) := by
            have : 0 ≤ 1 + |y| := by linarith
            gcongr
    · rw [zero_mul, add_zero, abs_zero]; exact mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)
  -- the tails
  have hb0' : 2 * d + (p.Le + 2) ≤ b0 := by linarith
  have h1 : EvSI.gam d {z | b0 < z ⬝ᵥ z} ≤ ENNReal.ofReal (p.δe ^ 9) := by
    refine (SKp.chi2_tail_b0 hd (p.Le + 2) b0 (by linarith) hb0').trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← exp_Le_div hp 9]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have h2 : ∀ x : Θ × Df2St d, EvSI.gam d {z | 10 < PtrE p Kθ M (x, z)} ≤ ENNReal.ofReal (p.δe ^ 9) := by
    rintro ⟨q, st⟩
    by_cases hgd : goodE p Kθ M (q, st)
    · have e : {z | 10 < PtrE p Kθ M ((q, st), z)} = {z | 10 < fPE p Kθ ((q, st), z)} := by
        ext z; simp only [Set.mem_ofPred_eq, PtrE, hgd, ↓reduceIte]
      rw [e]
      refine (ptr_tail hd (hbody q) he0 he1 hp.lam0 hp.lam1 hp.Le1 hp.sig hgd).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [← exp_Le_div hp 9]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    · have e : {z | 10 < PtrE p Kθ M ((q, st), z)} = ∅ := by
        ext z; simp only [Set.mem_ofPred_eq, PtrE, hgd, ↓reduceIte, Set.mem_empty_iff_false, iff_false]; norm_num
      rw [e, measure_empty]; exact zero_le
  set t0 := Real.sqrt (p.Le / 3) with ht0def
  have ht0 : 0 ≤ t0 := Real.sqrt_nonneg _
  have hy00 : 0 ≤ y0 := by
    have : 0 ≤ 18 / p.eps := div_nonneg (by norm_num) he0.le
    linarith
  have hoff : ∀ x y, x.2 ⬝ᵥ x.2 ≤ b0 → PtrE p Kθ M x ≤ 10 → |y| ≤ t0 →
      |EtrE p Kθ gθ M s x + PtrE p Kθ M x * y| ≤ y0 := by
    rintro ⟨⟨q, st⟩, z⟩ y _ hP hy
    unfold EtrE
    unfold PtrE at hP ⊢
    split_ifs at hP ⊢ with hgd
    · exact (ptr_off (hbody q) (hadm q) he0 he1 z y t0 hP hy).trans hy0
    · rw [zero_mul, add_zero, abs_zero]; exact hy00
  have hB := SKp.bias_round hd 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee (EtrE p Kθ gθ M s) (PtrE p Kθ M)
    (DtrE p Kθ M φ) (measurable_EtrE hg hext) (measurable_PtrE hg) (measurable_DtrE hg hφ) K 2 hK0 hEK hPK hDK
    C hC0 hYb b0 y0 t0 (p.δe ^ 9) (p.δe ^ 9) hy00 ht0 (pow_nonneg hp.de0.le 9) (pow_nonneg hp.de0.le 9) h1
    (fun x => h2 x) hoff
  -- the constants
  have hA : (1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) ≤ 7 * C * Real.sqrt d := by
    have hy : 0 ≤ 7 * C * Real.sqrt d := mul_nonneg (mul_nonneg (by norm_num) hC0) hsd
    rw [← pow_four_rpow hy]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have hs2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
    have e : (7 * C * Real.sqrt d) ^ 4 = 2401 * C ^ 4 * (Real.sqrt d ^ 2) ^ 2 := by ring
    rw [e, hs2]
    nlinarith [pow_nonneg hC0 4, sq_nonneg (d : ℝ)]
  have hT : (p.δe ^ 9 + p.δe ^ 9 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt (p.δe ^ 9) := by
    have et : Real.exp (-t0 ^ 2) = p.δe ^ 12 := by
      rw [ht0def, Real.sq_sqrt (by linarith), ← exp_Le_div hp 12]
      congr 1; push_cast; ring
    have h12 : p.δe ^ 12 ≤ p.δe ^ 9 := pow_le_pow_of_le_one hp.de0.le hp.de1 (by norm_num)
    rw [et, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (p.δe ^ 9 + p.δe ^ 9 + 2 * p.δe ^ 12) ≤ Real.sqrt (4 * p.δe ^ 9) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (p.δe ^ 9) := by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hy7 : 0 ≤ 7 * C * Real.sqrt d := mul_nonneg (mul_nonneg (by norm_num) hC0) hsd
  have hc0 : 0 ≤ p.δe ^ 9 + p.δe ^ 9 + 2 * Real.exp (-t0 ^ 2) := by
    have := pow_nonneg hp.de0.le 9
    have := Real.exp_pos (-t0 ^ 2)
    linarith
  filter_upwards [hB] with ω hB
  set D4 := (∫ z, DtrE p Kθ M φ (σ ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) with hD4def
  have hD4 : 0 ≤ D4 := Real.rpow_nonneg (integral_nonneg fun z => by positivity) _
  have hT0 : 0 ≤ (p.δe ^ 9 + p.δe ^ 9 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc0 _
  have hsq := Real.sqrt_nonneg (p.δe ^ 9)
  refine hB.trans ?_
  calc 2 * (1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) * D4 *
        (p.δe ^ 9 + p.δe ^ 9 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ)
      = (2 * D4) * ((1536 * C ^ 4 * (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) *
        (p.δe ^ 9 + p.δe ^ 9 + 2 * Real.exp (-t0 ^ 2)) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ (2 * D4) * ((7 * C * Real.sqrt d) * (2 * Real.sqrt (p.δe ^ 9))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hT hT0 hy7) (by linarith)
    _ ≤ lvBias p d * D4 := by
        show (2 * D4) * ((7 * C * Real.sqrt d) * (2 * Real.sqrt (p.δe ^ 9))) ≤
          52 * Real.sqrt d * C * Real.sqrt (p.δe ^ 9) * D4
        have hX : 0 ≤ C * Real.sqrt d * Real.sqrt (p.δe ^ 9) * D4 :=
          mul_nonneg (mul_nonneg (mul_nonneg hC0 hsd) hsq) hD4
        nlinarith

end Bias

end AdversarialBco.UW
