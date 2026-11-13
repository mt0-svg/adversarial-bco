/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetRun
public import AdversarialBco.Poly.Df2DetTools
public import AdversarialBco.Poly.Df2R1Proof
public import AdversarialBco.Poly.Df2EvTools

@[expose] public section

/-!
# The states of an epoch up to the stopping time, without the SI facts

`LInv s`: what holds of the state of round `s ≤ τ` by the conditions before `τ` and the rank-one round lemma alone, once
the
Hessians of the surrogates of the rounds before `s` have a nonnegative quadratic form (`hH`): the mode runs, `P` is
positive definite, `S P = 1`, `A Aᵀ = S`, `P ≥ ½ P̄`, `P̄ ≥ P̄₀` as quadratic forms, `μ ∈ K_ε`.
Consequences: `|A w|² ≤ 2 σ² |w|²` and `π(μ) ≤ 1 - ε`.

The nonnegativity of the Hessian forms is not taken from `Df2SIFacts`: the extension is convex (`EvGY.extOf_convex`), so the surrogate is convex, so its second derivative is nonnegative in every direction at every
point (`EvGY.fderiv_fderiv_nonneg_of_convex`, which reads Mathlib's junk value `0` where `fderiv` is not
differentiable).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

namespace EvGY

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-! ## The stopping time -/

open Classical in
theorem tau_lt {m : ℕ} (hm : 1 ≤ m) : c.tau π m < m := by
  unfold Df2Ctx.tau
  split_ifs with h
  · exact (Nat.find_spec h).1
  · omega

open Classical in
theorem cond_of_lt_tau {m : ℕ} : ∀ s < c.tau π m, c.Cond π s := by
  intro s hs
  unfold Df2Ctx.tau at hs
  split_ifs at hs with h
  · by_contra hc
    exact Nat.find_min h hs ⟨by have := (Nat.find_spec h).1; omega, hc⟩
  · by_contra hc
    exact h ⟨s, by omega, hc⟩

theorem pbar_zero : c.PBar π 0 = c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) := rfl

theorem pbar_succ (s : ℕ) : c.PBar π (s + 1) = c.PBar π s + (c.p.eta * c.p.kap) • c.sHess π s := rfl

/-! ## The light invariant -/

/-- The invariants of the state of round `s` that need no SI fact. -/
structure LInv (s : ℕ) : Prop where
  run : c.mode π s = .run (c.st π s)
  pd : (c.st π s).P.PosDef
  SP : (c.st π s).S * (c.st π s).P = 1
  AA : (c.st π s).A * (c.st π s).Aᵀ = (c.st π s).S
  pbl : ((c.st π s).P - (1 / 2 : ℝ) • c.PBar π s).PosSemidef
  pb0 : ∀ v, df2Sq (c.PBar π 0) v ≤ df2Sq (c.PBar π s) v
  mu : (c.st π s).mu ∈ c.Keps

/-- The parameters an epoch reads for the light invariant. -/
structure LPar : Prop where
  sig2 : 0 < c.p.sig2
  de : 0 < c.p.δe
  ek : 0 ≤ c.p.eta * c.p.kap
  eps1 : c.p.eps < 1
  zero_mem : (0 : E d) ∈ c.Kt
  init : c.st π 0 = df2Init c.p d

theorem linv_zero (hp : LPar c π) : LInv c π 0 := by
  have hs0 := hp.sig2
  have hsi : 0 < c.p.sig2⁻¹ := inv_pos.2 hs0
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun v => le_rfl, ?_⟩
  · show (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef
    exact Matrix.PosDef.one.smul hsi
  · show (c.p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (c.p.sig2⁻¹ • 1) = 1
    rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hs0.ne', one_smul]
  · show (Real.sqrt c.p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (Real.sqrt c.p.sig2 • 1)ᵀ = c.p.sig2 • 1
    rw [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one, Real.mul_self_sqrt hs0.le]
  · show (c.p.sig2⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) - (1 / 2 : ℝ) • (c.p.sig2⁻¹ • 1)).PosSemidef
    rw [smul_smul]; exact psd_sub_smul_one (by linarith)
  · show WithLp.toLp 2 ((1 - c.p.eps)⁻¹ • (0 : Fin d → ℝ)) ∈ c.Kt
    rw [smul_zero]
    exact hp.zero_mem

theorem linv_succ (hp : LPar c π) (hap : ∀ s, ApSpec (c.ap s)) {m s : ℕ} (hs : s < c.tau π m) (hI : LInv c π s)
    (hH : ∀ v, 0 ≤ df2Sq (c.sHess π s) v) : LInv c π (s + 1) := by
  obtain ⟨-, ⟨ha, hq⟩, ⟨h3a, h3b, -, -⟩, hcont⟩ := cond_of_lt_tau c π s hs
  obtain ⟨pt, mu', -, -, hmc, hrun, hst⟩ := c.st_succ_of_cont π s hI.run hcont
  have hR1 : R1Hyp (c.st π s).P (c.st π s).S (c.st π s).A := ⟨hI.pd, hI.AA, hI.SP⟩
  have hii := lemmaR1ii d _ _ _ (π.xi s) (c.cc π s) hR1 ha hq
  have hiii := lemmaR1iii d _ _ _ (π.xi s) (c.cc π s) hR1 ha hq
  have hP : (c.st π (s + 1)).P = c.Pn π s := by rw [hst]; rfl
  have hmu : (c.st π (s + 1)).mu = mu' := by rw [hst]; rfl
  have pbl : ((c.st π (s + 1)).P - (1 / 2 : ℝ) • c.PBar π (s + 1)).PosSemidef := by rw [hP]; exact h3b
  refine ⟨hrun, posDef_of_sub hp.de (psd_trans pbl h3a), ?_, ?_, pbl, ?_, ?_⟩
  · rw [hst]; exact hii.1
  · rw [hst]; exact hiii.2.1
  · intro v
    rw [pbar_succ, sq_add, sq_smul]
    have := hI.pb0 v
    have := mul_nonneg hp.ek (hH v)
    linarith
  · have hsp := (hap s (c.Rp π s) ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) c.p.R (c.Pn π s) (c.wmu π s)
      (c.eM π s)).2
    unfold Df2Ctx.mcall at hmc
    rw [hmc] at hsp
    rcases hsp with h | ⟨μ, hμ, hμQ, -⟩
    · cases h
    · rw [hmu, Option.some.inj hμ]; exact hμQ.1

/-- The light invariant at every round up to `τ`. -/
theorem linv_le_tau (hp : LPar c π) (hap : ∀ s, ApSpec (c.ap s)) {m : ℕ}
    (hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v) : ∀ s ≤ c.tau π m, LInv c π s := by
  intro s hs
  induction s with
  | zero => exact linv_zero c π hp
  | succ s ih => exact linv_succ c π hp hap (m := m) (by omega) (ih (by omega)) (hH s (by omega))

/-! ## Consequences -/

/-- `|v|²/(2σ²) ≤ vᵀ P v`. -/
theorem LInv.P_lower (hp : LPar c π) {s : ℕ} (hI : LInv c π s) (v : Fin d → ℝ) :
    c.p.sig2⁻¹ / 2 * (v ⬝ᵥ v) ≤ df2Sq (c.st π s).P v := by
  have h1 := sq_le_of_psd (P := (1 / 2 : ℝ) • c.PBar π s) (Q := (c.st π s).P) hI.pbl v
  have h2 := hI.pb0 v
  rw [sq_smul] at h1
  rw [pbar_zero, sq_smul, sq_one] at h2
  linarith

/-- `Aᵀ P A = 1`. -/
theorem LInv.ATPA {s : ℕ} (hI : LInv c π s) : (c.st π s).Aᵀ * (c.st π s).P * (c.st π s).A = 1 := by
  have h : (c.st π s).A * ((c.st π s).Aᵀ * (c.st π s).P) = 1 := by
    rw [← Matrix.mul_assoc, hI.AA, hI.SP]
  exact mul_eq_one_comm.1 h

/-- `|A w|² ≤ 2 σ² |w|²`. -/
theorem LInv.A_sq_le (hp : LPar c π) {s : ℕ} (hI : LInv c π s) (w : Fin d → ℝ) :
    ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) ≤ 2 * c.p.sig2 * (w ⬝ᵥ w) := by
  have h1 := hI.P_lower c π hp ((c.st π s).A *ᵥ w)
  have h2 : df2Sq (c.st π s).P ((c.st π s).A *ᵥ w) = w ⬝ᵥ w := by
    unfold df2Sq
    rw [Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hI.ATPA, Matrix.one_mulVec]
  have hs := hp.sig2
  rw [h2] at h1
  have : c.p.sig2⁻¹ / 2 * (((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w)) * (2 * c.p.sig2) =
      ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * c.p.sig2)]

end EvGY

end AdversarialBco.Poly
