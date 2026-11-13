/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvMeas
public import AdversarialBco.Poly.Df2EvGTools

@[expose] public section

/-!
# The budget of Noise, Pi and Gauss: the parts

The parts of the budget: the surrogate of an admissible loss is convex and the Hessian forms on the path are
nonnegative (`surr_convex`, `sHess_nonneg`); a point of `K_ε` has gauge at most `1` (`gauge_le_one_of_keps`); the
facts of the parameters the budget reads (`evGPar`); and Pi in one round: at a good state (`π(μ_s) ≤ 1`,
`|A_s w|² ≤ 2σ²|w|²`, `spreadSet`), the event Pi is a set of the parameter, the mode and the draw (`piSet`),
measurable under (L1) (`measurableSet_piSet`), to which freezing applies with the Gaussian bound `pi_round_law`.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly

open Layer2 ApMeas

namespace EvGY

variable {d : ℕ}

/-! ## The Hessian forms on the path -/

/-- The surrogate of the extension of an admissible loss is convex. -/
theorem surr_convex {R : ℝ} (Kt : Set (E d)) (hbody : Df2Body d R Kt) (g : E d → ℝ) (hg : AdmLoss Kt g)
    (p : Df2OPar) (hε0 : 0 < p.eps) (hε1 : p.eps < 1) (hlam : 0 < p.lam) (mu : E d) (A : E d →L[ℝ] E d) :
    ConvexOn ℝ Set.univ (df2Surr (df2Ext p Kt g) mu A p.lam) := by
  obtain ⟨hK, hKc, hball, -, -⟩ := hbody
  have hc : (1 - p.eps) / p.eps ≤ 2 / p.eps := div_le_div_of_nonneg_right (by linarith) hε0.le
  have hconv : ConvexOn ℝ Set.univ (df2Ext p Kt g) := by
    rw [df2Ext_eq]
    exact extOf_convex Kt hK hKc hball g hg.1 hg.2 p.eps hε0 hε1 _ hc
  refine df2Surr_convex _ hconv (continuous_of_convexOn_univ _ hconv) (1 + 2 / p.eps)
    ((1 + 2 / p.eps) / (1 - p.eps)) ?_ mu A p.lam hlam
  intro x
  rw [df2Ext_eq]
  exact extOf_abs_le Kt hK hKc hball g hg.2 p.eps hε0 hε1 _ (by positivity) x

/-- The Hessian of the surrogate of round `s` has a nonnegative form. -/
theorem sHess_nonneg {R : ℝ} (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) (hbody : Df2Body d R c.Kt)
    (hg : AdmLoss c.Kt (π.g s)) (hε0 : 0 < c.p.eps) (hε1 : c.p.eps < 1) (hlam : 0 < c.p.lam) (v : Fin d → ℝ) :
    0 ≤ df2Sq (c.sHess π s) v := by
  unfold Df2Ctx.sHess
  rw [(gradM_hessM _ _ v).2]
  exact fderiv_fderiv_nonneg_of_convex _ (surr_convex c.Kt hbody (π.g s) hg c.p hε0 hε1 hlam _ _) _ _

/-- A point of `K_ε` has gauge at most `1`. -/
theorem gauge_le_one_of_keps (Kt : Set (E d)) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (mu : Fin d → ℝ)
    (hmu : mu ∈ df2KepsOf Kt ε) : gauge Kt (WithLp.toLp 2 mu) ≤ 1 := by
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  have heq : WithLp.toLp 2 mu = (1 - ε) • WithLp.toLp 2 ((1 - ε)⁻¹ • mu) := by
    rw [← WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]
  rw [heq, gauge_smul_of_nonneg h1.le, smul_eq_mul]
  have := gauge_le_one_of_mem (s := Kt) hmu
  have h0 : 0 ≤ gauge Kt (WithLp.toLp 2 ((1 - ε)⁻¹ • mu)) := gauge_nonneg _
  nlinarith

/-! ## The parameters -/

/-- The parameters the budget reads. -/
structure EvGPar (d n : ℕ) (δ : ℝ) : Prop where
  de : 0 < (df2oPar d n δ).δe
  L504 : 504 ≤ (df2oPar d n δ).Le
  Lg0 : 0 ≤ df2Lg (df2oPar d n δ) n
  LgLe : df2Lg (df2oPar d n δ) n ≤ (df2oPar d n δ).Le
  lam0 : 0 < (df2oPar d n δ).lam
  lam1 : (df2oPar d n δ).lam < 1
  eps0 : 0 < (df2oPar d n δ).eps
  sig2 : (df2oPar d n δ).sig2 = 1 / (8 * (df2oPar d n δ).Le)
  ek : 0 ≤ (df2oPar d n δ).eta * (df2oPar d n δ).kap

theorem evGPar (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) : EvGPar d n δ := by
  obtain ⟨hde, -, -⟩ := par_de d n δ hd hn hδ0
  obtain ⟨hL, hLg0, hLgL⟩ := par_Le d n δ hd hn hδ0
  obtain ⟨hl0, hl1, he0, hs, hek⟩ := par_misc d n δ hd hn hδ0
  exact ⟨hde, hL, hLg0, hLgL, hl0, hl1, he0, hs, hek⟩

/-! ## Pi in one round, on setting (E) -/

section Round

variable {n : ℕ} {δ : ℝ} {Θ : Type} [MeasurableSpace Θ] {Kθ : Θ → Set (E d)} {gθ : ℕ → Θ → E d → ℝ}
  {ap : ApFun d}

/-- The states of spread at most `k`. -/
def spreadSet (k : ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) := {A | ∀ w, (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ k * (w ⬝ᵥ w)}

variable (n δ Kθ) in
/-- The event of Pi at a good state, as a set of `((θ, mode), ξ)`. -/
def piSet : Set ((Θ × Df2Mode d) × (Fin d → ℝ)) :=
  {x | x.1.2.code.1 = 2 ∧ gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1 ∧
    x.1.2.code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2) ∧
    Real.sqrt (df2oPar d n δ).Le < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2))}

theorem measurableSet_piSet {m : ℕ} (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) :
    MeasurableSet (piSet n δ Kθ) := by
  have hcode : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code :=
    measurable_mode_code.comp (measurable_snd.comp measurable_fst)
  have hst : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.2.code.2 := measurable_snd.comp hcode
  have hq : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => x.1.1 := measurable_fst.comp measurable_fst
  have h1 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) | x.1.2.code.1 = 2} :=
    (measurable_fst.comp hcode) (measurableSet_singleton 2)
  have hmu : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => (x.1.1, (WithLp.toLp 2 x.1.2.code.2.mu : E d)) :=
    hq.prodMk ((WithLp.measurable_toLp 2 _).comp (measurable_st_mu.comp hst))
  have hg2 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) := by
    have h := hmeas.1.comp hmu
    exact h
  have h2 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      gauge (Kθ x.1.1) (WithLp.toLp 2 x.1.2.code.2.mu) ≤ 1} := measurableSet_le hg2 measurable_const
  have h3 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      x.1.2.code.2.A ∈ spreadSet (2 * (df2oPar d n δ).sig2)} :=
    (measurable_st_A.comp hst) (isClosed_spread _).measurableSet
  have hX : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      (x.1.1, (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2) : E d)) := by
    have hx : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) => (x.1.2.code.2, x.2) := hst.prodMk measurable_snd
    have h := (measurable_xOf n δ).comp hx
    exact hq.prodMk ((WithLp.measurable_toLp 2 _).comp h)
  have hg4 : Measurable fun x : (Θ × Df2Mode d) × (Fin d → ℝ) =>
      gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2)) := by
    have h := hmeas.1.comp hX
    exact h
  have h4 : MeasurableSet {x : (Θ × Df2Mode d) × (Fin d → ℝ) |
      Real.sqrt (df2oPar d n δ).Le < gauge (Kθ x.1.1) (WithLp.toLp 2 (xOf n δ x.1.2.code.2 x.2))} :=
    measurableSet_lt measurable_const hg4
  exact h1.inter (h2.inter (h3.inter h4))

end Round

end EvGY

end AdversarialBco.Poly
