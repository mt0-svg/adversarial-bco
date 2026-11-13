/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetW1
public import AdversarialBco.Poly.Df2DetProof
public import AdversarialBco.Poly.Df2PlayProof
public import AdversarialBco.Poly.Df2R1Proof
public import AdversarialBco.Poly.WrapperProof
public import AdversarialBco.Poly.Df2RowsProof
public import AdversarialBco.Poly.Df2EvYTools
public import AdversarialBco.Poly.Df2EvGProof

@[expose] public section

/-!
# The second moments of `v = pip - 1` under the plays: the parts

The parts of the paper's bound `∑_{s ≤ t} E_z (pip(μ_s + (1 - λ) A_s z) - 1)² ≤ (3/10) n ε²` on every path for every
`t ≤ τ`, `z` standard Gaussian on `Fin d → ℝ`: the second moment of `pip - 1` under the play of round `s` (`vmom`) and
the spread of the play (`playT`); `ē_s - e_s(μ_s) ≤ (2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ` for `s ≤ τ` from the play shift,
`s ≤ e` (X7) and prop:lower (X3) (`round_lower`); the log-determinant lemma summed over `u < τ`, whose top
`P̄_τ ≤ I/(2 δ_e)` is condition (3) at `τ - 1` (`trace_sum_lt`); and `d ≤ e^L`, `n e^{-L} ≤ 1` (`par_exp`). Also the
inputs of layer one, all proved (`layerOne`).
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly.EvGY

open Layer2

variable {d : ℕ}

/-- The inputs of layer one, all proved. -/
theorem layerOne : Df2LayerOne :=
  ⟨lemmaDFI_holds, lemmaMON_holds, propINC2_holds, lemmaD2_holds, lemmaONS2Core_holds, lemmaZCore_holds,
    df2RowZ_holds, playShift_holds, lemmaUBPrime_holds, playHess_holds, df2Trivial_holds, df2Carriers_holds,
    lemmaR1i, lemmaR1ii, lemmaR1iii, lemmaR1iv, lemmaR1v⟩

/-- A point of `K_ε` has gauge at most `1 - ε`. -/
theorem gauge_le_of_keps (Kt : Set (E d)) (ε : ℝ) (hε1 : ε < 1) (mu : Fin d → ℝ) (hmu : mu ∈ df2KepsOf Kt ε) :
    gauge Kt (WithLp.toLp 2 mu) ≤ 1 - ε := by
  have h1 : (0 : ℝ) < 1 - ε := by linarith
  have heq : WithLp.toLp 2 mu = (1 - ε) • WithLp.toLp 2 ((1 - ε)⁻¹ • mu) := by
    rw [← WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h1.ne', one_smul]
  rw [heq, gauge_smul_of_nonneg h1.le, smul_eq_mul]
  calc (1 - ε) * gauge Kt (WithLp.toLp 2 ((1 - ε)⁻¹ • mu)) ≤ (1 - ε) * 1 :=
        mul_le_mul_of_nonneg_left (gauge_le_one_of_mem (s := Kt) hmu) h1.le
    _ = 1 - ε := mul_one _

/-- `√(2 σ²) = 1/(2 √L)` at `σ² = 1/(8 L)`. -/
theorem sqrt_two_sig2 (L : ℝ) (hL : 0 < L) : Real.sqrt (2 * (1 / (8 * L))) = 1 / (2 * Real.sqrt L) := by
  have hs := Real.sq_sqrt hL.le
  have hpos := Real.sqrt_pos.2 hL
  rw [show 2 * (1 / (8 * L)) = (1 / (2 * Real.sqrt L)) ^ 2 by rw [div_pow, mul_pow, hs]; field_simp; ring]
  exact Real.sqrt_sq (by positivity)

/-- The second moment of `pip - 1` under the play of round `s`, in the coordinates of the budgets. -/
noncomputable def vmom (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : ℝ :=
  ∫ z, (df2Pip c.p c.Kt (WithLp.toLp 2 ((c.st π s).mu + (1 - c.p.lam) • ((c.st π s).A *ᵥ z))) - 1) ^ 2
    ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)

/-- The spread of the play of round `s`, as a map of `E d`. -/
noncomputable def playT (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : E d →L[ℝ] E d :=
  (1 - c.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A

theorem vmom_eq (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) :
    vmom c π s = ∫ g, (pipOf c.Kt c.p.eps (WithLp.toLp 2 (c.st π s).mu + playT c π s g) - 1) ^ 2
      ∂(stdGaussian (E d)) := by
  rw [← integral_pi_eq (fun g => (pipOf c.Kt c.p.eps (WithLp.toLp 2 (c.st π s).mu + playT c π s g) - 1) ^ 2)]
  rfl

theorem vmom_nonneg (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : 0 ≤ vmom c π s :=
  integral_nonneg fun _ => sq_nonneg _

section Base

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- `ē_s - e_s(μ_s) ≤ (2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ` for `s ≤ τ`: the play shift, X3 and X7 (the round of (W1)
at `x = μ_s`, on the hypotheses without the events). -/
theorem round_lower (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.ebar π s - df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 (c.st π s).mu) ≤
      2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace + 2 * c.p.δe * d / c.p.lam := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si_at hs
  have hl := H.rows.pos_lam
  have hl2 := H.rows.lam_le
  have hsh : c.ebar π s - c.surr π s (WithLp.toLp 2 (c.st π s).mu) =
      (1 - c.p.lam) * ((∫ z, df2Ext c.p c.Kt (π.g s)
        (WithLp.toLp 2 (c.st π s).mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A z) ∂(stdGaussian (E d))) -
        c.surr π s (WithLp.toLp 2 (c.st π s).mu)) :=
    H.shift d (df2Ext c.p c.Kt (π.g s)) (WithLp.toLp 2 (c.st π s).mu)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A) c.p.lam hl (by linarith)
  have hlo := hsi.lower
  have hle := hsi.le_ext (WithLp.toLp 2 (c.st π s).mu)
  have hR0 : 0 ≤ 2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace + 2 * c.p.δe * d / c.p.lam := by
    have hS : ((c.st π s).A * (c.st π s).Aᵀ).PosSemidef := by
      rw [hI.AA, ← (Matrix.inv_eq_left_inv hI.SP)]
      exact hI.pd.inv.posSemidef
    have := trace_mul_nonneg _ _ (H.sHess_psd hs) hS
    have := H.rows.pos_de
    positivity
  have h1 := mul_le_mul_of_nonneg_left hlo (by linarith : (0 : ℝ) ≤ 1 - c.p.lam)
  have h2 : (1 - c.p.lam) * (2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace +
      2 * c.p.δe * d / c.p.lam) ≤ 2 / c.p.lam * (c.sHess π s * ((c.st π s).A * (c.st π s).Aᵀ)).trace +
      2 * c.p.δe * d / c.p.lam := by nlinarith
  linarith

/-- The log-determinant lemma over the rounds `u < τ`: `∑_{u < τ} (2/λ) tr(s''_u Σ_u) ≤ d L/(λ η)`. The top
`P̄_τ ≤ I/(2 δ_e)` is
condition (3) at `τ - 1`, so no event is read. -/
theorem trace_sum_lt (H : DetBase c δ π m) :
    ∑ u ∈ Finset.range (c.tau π m), 2 / c.p.lam * (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace ≤
      d * c.p.Le / (c.p.lam * c.p.eta) := by
  have hl := H.rows.pos_lam
  have hη := H.rows.pos_eta
  have hde := H.rows.pos_de
  have hek := H.kap_pos
  obtain hτ | ⟨T, hT⟩ : c.tau π m = 0 ∨ ∃ T, c.tau π m = T + 1 := by
    rcases Nat.eq_zero_or_pos (c.tau π m) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨c.tau π m - 1, by omega⟩
  · rw [hτ, Finset.sum_range_zero]
    have hL0 : 0 ≤ c.p.Le := by rw [H.Le_eq]; have := H.x_ge; positivity
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) (by positivity)
  have htop : ((1 / (2 * c.p.δe)) • (1 : Matrix (Fin d) (Fin d) ℝ) - c.PBar π (T + 1)).PosSemidef := by
    have h := (H.cond_lt_tau T (by omega)).2.2.1.2.2.2
    refine psd_of_eq (h.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)) ?_
    rw [smul_sub, smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp
    · norm_num
  have hld := ld_core (c.PBar π) (fun u => (c.p.eta * c.p.kap) • c.sHess π u) T c.p.sig2 (1 / (2 * c.p.δe))
    H.rows.pos_sig2 (by positivity) (c.PBar_zero π) (fun u _ => c.PBar_succ π u)
    (fun u hu => (H.sHess_psd (by omega)).smul hek.le) (fun u hu => H.H_le_PBar (by omega)) htop
  beta_reduce at hld
  have e : ∀ u, ((c.PBar π u)⁻¹ * ((c.p.eta * c.p.kap) • c.sHess π u)).trace =
      c.p.eta * c.p.kap * (c.sHess π u * (c.PBar π u)⁻¹).trace := fun u => by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
  simp only [e] at hld
  rw [← Finset.mul_sum] at hld
  have hσ1 : 2 * c.p.sig2 ≤ 1 := H.rows.r2
  have hσδ : 4 * c.p.δe ≤ c.p.sig2 := by
    have := H.rows.c4; rwa [div_le_iff₀ H.rows.pos_sig2, one_mul] at this
  obtain ⟨hlog, harith⟩ := w1_arith c.p.lam c.p.eta d c.p.δe c.p.sig2 c.p.Le hl hη (Nat.cast_nonneg d)
    H.rows.pos_de H.rows.de_lt H.rows.pos_sig2 hσ1 hσδ H.Le_eq
  rw [hT]
  have h1 : ∑ u ∈ Finset.range (T + 1), (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace ≤
      2 * ∑ u ∈ Finset.range (T + 1), (c.sHess π u * (c.PBar π u)⁻¹).trace := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u hu => H.trace_S_le (by have := Finset.mem_range.1 hu; omega)
  have h2 : 2 * ∑ u ∈ Finset.range (T + 1), (c.sHess π u * (c.PBar π u)⁻¹).trace ≤
      2 / (c.p.eta * (1 / 4)) * (2 * d * Real.log (1 / (2 * c.p.δe) * c.p.sig2)) := by
    rw [← H.kap]
    rw [div_mul_eq_mul_div, le_div_iff₀ hek]
    nlinarith
  rw [← Finset.mul_sum]
  calc 2 / c.p.lam * ∑ u ∈ Finset.range (T + 1), (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace
      ≤ 2 / c.p.lam * (2 / (c.p.eta * (1 / 4)) * (2 * d * Real.log (1 / (2 * c.p.δe) * c.p.sig2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ ≤ _ := harith

/-- `d ≤ e^L` and `n e^{-L} ≤ 1`, from the condition cx. -/
theorem par_exp (H : DetBase c δ π m) : (d : ℝ) ≤ Real.exp c.p.Le ∧ (c.n : ℝ) * Real.exp (-c.p.Le) ≤ 1 := by
  have hcx := H.rows.cx
  have hL := H.Le_eq
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ c.n := by exact_mod_cast H.hn
  have hdn : (1 : ℝ) ≤ d * c.n := by nlinarith
  have hlogdn : 0 ≤ Real.log (d * c.n) := Real.log_nonneg hdn
  have hlogd : Real.log d ≤ Real.log (d * c.n) := Real.log_le_log (by positivity) (by nlinarith)
  have hlogn : Real.log c.n ≤ Real.log (d * c.n) := Real.log_le_log (by positivity) (by nlinarith)
  constructor
  · calc (d : ℝ) = Real.exp (Real.log d) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp c.p.Le := Real.exp_le_exp.2 (by linarith)
  · rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
    calc (c.n : ℝ) = Real.exp (Real.log c.n) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp c.p.Le := Real.exp_le_exp.2 (by linarith)

end Base

end AdversarialBco.Poly.EvGY
