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
# The second moments of `v = pip - 1` under the plays, summed up to the stopping time

Appendix D.4 of the paper, in the form both event budgets read: on every path, for every `t ≤ τ`,
`∑_{s ≤ t} E_z (pip(μ_s + (1 - λ) A_s z) - 1)² ≤ (3/10) n ε²`, `z` standard Gaussian on `Fin d → ℝ`. No event and no
probability: the states up to `τ` satisfy the conditions of the stopping time, and each term is a Gaussian integral of
the state.

Route: for `s < τ`, `E v² ≤ 2 L E v + e^{-L}` (truncation at `2 L`, the Gaussian tail of
the gauge); `E v ≤ ε (ē_s - e_s(μ_s))` (`e = h + v/ε`, `h` the convex extension at `1/ε`, Jensen); the play shift,
`s ≤ e` (X7) and prop:lower (X3) give `ē_s - e_s(μ_s) ≤ (2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ`; Lemma D.12 summed over
`u < τ`, whose top `P̄_τ ≤ I/(2 δ_e)` is condition (3) at `τ - 1`. The last round `s = τ` takes the crude
`E v² ≤ 4 ‖(1 - λ) A_τ‖² d ≤ d/L`. The rows R5p, R7, R8, c2dl close the sum at `n ε²/4`.
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

/-- The hypotheses of DET without the events, on the hypotheses of the budgets. -/
theorem detBase (hSI : Df2SIFacts) {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ApFun d} {π : Df2Path d} {m : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ApSpec ap) (hadm : ∀ s < m, AdmLoss Kt (π.g s)) :
    DetBase (df2CtxAt d n δ Kt ap) δ π m :=
  ⟨layerOne, lemmaW, hSI, hd, hn, hδ0, hδ1, rfl, heps, df2RowsHold d n δ hd hn hδ0 hδ1 heps, hm1, hmn, hbody, hap,
    hadm⟩

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

/-- Lemma D.12 over the rounds `u < τ`: `∑_{u < τ} (2/λ) tr(s''_u Σ_u) ≤ d L/(λ η)`. The top `P̄_τ ≤ I/(2 δ_e)` is
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

section Concrete

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ApFun d} {π : Df2Path d} {m : ℕ}

/-- `‖(1 - λ) A_s‖ ≤ 1/(2 √L)` for `s ≤ τ`: the light invariant gives `|A_s w|² ≤ 2 σ² |w|²`, `σ² = 1/(8 L)`. -/
theorem playT_norm_le (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ‖playT (df2CtxAt d n δ Kt ap) π s‖ ≤ 1 / (2 * Real.sqrt (df2oPar d n δ).Le) := by
  set c := df2CtxAt d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  have hp : LPar c π :=
    ⟨H.rows.pos_sig2, H.rows.pos_de, H.kap_pos.le, heps1, H.body.2.2.1 (Metric.mem_closedBall_self zero_le_one),
      rfl⟩
  have hH : ∀ u < c.tau π m, ∀ v, 0 ≤ df2Sq (c.sHess π u) v := fun u hu v =>
    sHess_nonneg c π u H.body (H.adm u (by have := H.tau_lt; omega)) H.rows.pos_eps heps1 H.rows.pos_lam v
  have hI := linv_le_tau c π hp H.hap hH s hs
  have hA : ∀ w, ((c.st π s).A *ᵥ w) ⬝ᵥ ((c.st π s).A *ᵥ w) ≤ 2 * c.p.sig2 * (w ⬝ᵥ w) :=
    fun w => hI.A_sq_le c π hp w
  have hN := toEuclideanCLM_norm_le (c.st π s).A (2 * c.p.sig2) (by have := H.rows.pos_sig2; positivity) hA
  have hsig : c.p.sig2 = 1 / (8 * (df2oPar d n δ).Le) := hP.sig2
  rw [hsig, sqrt_two_sig2 _ (by linarith [hP.L504])] at hN
  have hl0 := H.rows.pos_lam
  have hl1 := H.rows.lam_le
  unfold playT
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h0 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (c.st π s).A‖ := norm_nonneg _
  nlinarith

/-- The crude bound at a round `s ≤ τ`: `E v² ≤ 4 ‖(1 - λ) A_s‖² d ≤ d/L`. -/
theorem vmom_crude (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    vmom (df2CtxAt d n δ Kt ap) π s ≤ d / (df2oPar d n δ).Le := by
  set c := df2CtxAt d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, -⟩ := H.body
  have hmu := gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  rw [vmom_eq]
  refine (v_sq_crude c.Kt hK hKc hball c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu _).trans ?_
  have hT := playT_norm_le H hs
  have hL := hP.L504
  have hsL := Real.sq_sqrt (show (0 : ℝ) ≤ (df2oPar d n δ).Le by linarith)
  have hsp := Real.sqrt_pos.2 (show (0 : ℝ) < (df2oPar d n δ).Le by linarith)
  have hT2 : ‖playT c π s‖ ^ 2 ≤ 1 / (4 * (df2oPar d n δ).Le) := by
    calc ‖playT c π s‖ ^ 2 ≤ (1 / (2 * Real.sqrt (df2oPar d n δ).Le)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ = 1 / (4 * (df2oPar d n δ).Le) := by rw [div_pow, mul_pow, hsL]; norm_num
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc 4 * ‖playT c π s‖ ^ 2 * d ≤ 4 * (1 / (4 * (df2oPar d n δ).Le)) * d := by gcongr
    _ = d / (df2oPar d n δ).Le := by field_simp

/-- The fine bound at a round `s ≤ τ`: `E v² ≤ 2 L ε ((2/λ) tr(s''_s Σ_s) + 2 δ_e d/λ) + e^{-L}`. -/
theorem vmom_fine (H : DetBase (df2CtxAt d n δ Kt ap) δ π m) {s : ℕ}
    (hs : s ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    vmom (df2CtxAt d n δ Kt ap) π s ≤
      2 * (df2oPar d n δ).Le * ((df2oPar d n δ).eps *
        (2 / (df2oPar d n δ).lam * ((df2CtxAt d n δ Kt ap).sHess π s *
          (((df2CtxAt d n δ Kt ap).st π s).A * ((df2CtxAt d n δ Kt ap).st π s).Aᵀ)).trace +
          2 * (df2oPar d n δ).δe * d / (df2oPar d n δ).lam)) + Real.exp (-(df2oPar d n δ).Le) := by
  set c := df2CtxAt d n δ Kt ap with hc
  have hP := evGPar d n δ H.hd H.hn H.hδ0
  have heps1 : c.p.eps < 1 := by have := H.rows.eps_le; linarith
  obtain ⟨hK, hKc, hball, -, hMw⟩ := H.body
  have hmu := gauge_le_of_keps c.Kt c.p.eps heps1 _ (H.stInv_le_tau s hs).mu
  have hadm := H.adm s (H.le_tau_lt hs)
  have h1 := v_sq_le H.hd c.Kt hK hKc hball hMw c.p.eps H.rows.pos_eps H.rows.eps_le _ hmu (playT c π s)
    (df2oPar d n δ).Le hP.L504 (playT_norm_le H hs) (par_exp H).1
  have h2 := v_mean_le c.Kt hK hKc hball (π.g s) hadm.1 hadm.2 c.p.eps H.rows.pos_eps heps1 _ hmu (playT c π s)
  have h3 := round_lower H hs
  have he : ∫ g, extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu + playT c π s g)
      ∂(stdGaussian (E d)) = c.ebar π s := by
    unfold Df2Ctx.ebar
    rw [df2Ext_eq]
    rfl
  have he2 : extOf c.Kt c.p.eps (2 / c.p.eps) (π.g s) (WithLp.toLp 2 (c.st π s).mu) =
      df2Ext c.p c.Kt (π.g s) (WithLp.toLp 2 (c.st π s).mu) := by rw [df2Ext_eq]
  rw [he, he2] at h2
  rw [vmom_eq]
  have hL0 : (0 : ℝ) ≤ 2 * (df2oPar d n δ).Le := by linarith [hP.L504]
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 H.rows.pos_eps.le)
  calc _ ≤ _ := h1
    _ ≤ _ := by gcongr; exact h4

/-- The sum of the second moments up to `t ≤ τ` is at most `n ε²/4`. -/
theorem vsum_le_quarter (hSI : Df2SIFacts) (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ApFun d) (π : Df2Path d)
    (m : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2)
    (hm1 : 1 ≤ m) (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ApSpec ap)
    (hadm : ∀ s < m, AdmLoss Kt (π.g s)) (t : ℕ) (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1), vmom (df2CtxAt d n δ Kt ap) π s ≤ 1 / 4 * n * (df2oPar d n δ).eps ^ 2 := by
  have H := detBase (π := π) hSI hd hn hδ0 hδ1 heps hm1 hmn hbody hap hadm
  set c := df2CtxAt d n δ Kt ap with hc
  set τ := c.tau π m with hτ
  have hP := evGPar d n δ hd hn hδ0
  have hτn : τ < n := lt_of_lt_of_le H.tau_lt hmn
  have hsub : ∑ s ∈ Finset.range (t + 1), vmom c π s ≤ ∑ s ∈ Finset.range (τ + 1), vmom c π s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.succ_le_succ ht))
      (fun s _ _ => vmom_nonneg c π s)
  refine hsub.trans ?_
  rw [Finset.sum_range_succ]
  set L := (df2oPar d n δ).Le with hLdef
  set ε := (df2oPar d n δ).eps with hεdef
  set lam := (df2oPar d n δ).lam with hlamdef
  set de := (df2oPar d n δ).δe with hdedef
  set a : ℕ → ℝ := fun u => 2 / lam * (c.sHess π u * ((c.st π u).A * (c.st π u).Aᵀ)).trace with ha
  set b : ℝ := 2 * de * d / lam with hb
  have hfine : ∑ s ∈ Finset.range τ, vmom c π s ≤ ∑ s ∈ Finset.range τ, (2 * L * (ε * (a s + b)) + Real.exp (-L)) :=
    Finset.sum_le_sum fun s hs => vmom_fine H (Finset.mem_range.1 hs).le
  have hsum : ∀ k : ℕ, ∑ s ∈ Finset.range k, (2 * L * (ε * (a s + b)) + Real.exp (-L)) =
      2 * L * ε * ∑ s ∈ Finset.range k, a s + k * (2 * L * ε * b + Real.exp (-L)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; push_cast; ring
  have htr : ∑ s ∈ Finset.range τ, a s ≤ d * L / (lam * (df2oPar d n δ).eta) := trace_sum_lt H
  have hcr := vmom_crude H (le_refl τ)
  have hL := hP.L504
  have hε0 : 0 < ε := H.rows.pos_eps
  have hl0 : 0 < lam := H.rows.pos_lam
  have hde : 0 < de := H.rows.pos_de
  have hb0 : 0 ≤ 2 * L * ε * b + Real.exp (-L) := by positivity
  have hτn' : (τ : ℝ) ≤ n := by exact_mod_cast hτn.le
  have h2 : ∑ s ∈ Finset.range τ, vmom c π s ≤
      2 * L * ε * (d * L / (lam * (df2oPar d n δ).eta)) + n * (2 * L * ε * b + Real.exp (-L)) := by
    rw [hsum] at hfine
    have h2Le : 0 ≤ 2 * L * ε := by positivity
    calc _ ≤ _ := hfine
      _ ≤ _ := by gcongr
  have hr5p := H.rows.r5p
  rw [show df2C0 = 36 from rfl] at hr5p
  have harith := vsum_arith d n L ε lam (df2oPar d n δ).eta de (by exact_mod_cast hd) (by exact_mod_cast hn) hL
    hε0 H.rows.eps_le hl0 H.rows.pos_eta hde hr5p H.rows.r7 H.rows.r8 H.rows.c2dl (par_exp H).2
  linarith

/-- The sum of the second moments of `pip - 1` under the plays, up to `t ≤ τ`. -/
theorem vsum_le (hSI : Df2SIFacts) (d n : ℕ) (δ : ℝ) (Kt : Set (E d)) (ap : ApFun d) (π : Df2Path d) (m : ℕ)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ApSpec ap) (hadm : ∀ s < m, AdmLoss Kt (π.g s))
    (t : ℕ) (ht : t ≤ (df2CtxAt d n δ Kt ap).tau π m) :
    ∑ s ∈ Finset.range (t + 1),
        ∫ z, (df2Pip (df2oPar d n δ) Kt (WithLp.toLp 2 (((df2CtxAt d n δ Kt ap).st π s).mu +
          (1 - (df2oPar d n δ).lam) • (((df2CtxAt d n δ Kt ap).st π s).A *ᵥ z))) - 1) ^ 2
          ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤
      3 / 10 * n * (df2oPar d n δ).eps ^ 2 := by
  have h := vsum_le_quarter hSI d n δ Kt ap π m hd hn hδ0 hδ1 heps hm1 hmn hbody hap hadm t ht
  have h0 : (0 : ℝ) ≤ n * (df2oPar d n δ).eps ^ 2 := by positivity
  exact h.trans (by nlinarith)

end Concrete

end AdversarialBco.Poly.EvGY
