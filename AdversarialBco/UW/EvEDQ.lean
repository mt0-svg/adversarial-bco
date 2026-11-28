/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCLQ
public import AdversarialBco.Poly.Df2EvSIDQ

@[expose] public section

/-!
# Event (e) of Theorem UW

`evDQPropUW_of : SIFactsUW → RowsUW → EvNeedsUW → EvDQPropUW`: event (e), DQ, at T4U on the weighted path fails with
probability at most `δc/8`. The proof is Theorem U's (Poly/Df2EvSIDQ.lean) with the changes of event (c)
(UW/EvCLQ.lean): the truncated increments of Lemma U, the bias of
Lemma SK' (at most `lvBe` per round since `(E_z φ_H⁴)^{1/4} ≤ 7 λ κ₀ lvQ`, `dq_d4E`), and the sure ranges of the
weighted path in the range (`dq_rangeE`) and the discretization (`dq_quadE`, `dq_disc_pathE`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The direction of (e) -/

/-- The growth constant of `phiHE (y - ·)` on the bound condition. -/
noncomputable def KphiHE (p : Df2OPar) (M : ℝ) (y : Fin d → ℝ) : ℝ :=
  p.lam * p.k0 * ((M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M)) ^ 2 +
    Real.sqrt M * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) ^ 2)

theorem KphiHE_nonneg {p : Df2OPar} {M : ℝ} (hl0 : 0 ≤ p.lam) (hk0 : 0 ≤ p.k0) (y : Fin d → ℝ) :
    0 ≤ KphiHE p M y := by
  unfold KphiHE; positivity

/-- `|φ_H(y)| ≤ KphiHE (1 + |z|)²` on the bound condition. -/
theorem phiHE_growth {p : Df2OPar} {M : ℝ} (hM : 0 ≤ M) (hl0 : 0 ≤ p.lam) (hk0 : 0 ≤ p.k0) (y : Fin d → ℝ)
    {st : Df2St d} (hst : EvSI.stB M st) (z : Fin d → ℝ) :
    |phiHE p (fun st => y - st.mu) st z| ≤ KphiHE p M y * (1 + ‖z‖) ^ 2 := by
  have hA := EvSI.bdSet_apply hst.2.1 hM z
  have hP := EvSI.bdSet_apply hst.2.2 hM (st.A *ᵥ z)
  have hz := EvSI.sqrt_dot_le z
  have hmu : Real.sqrt (st.mu ⬝ᵥ st.mu) ≤ Real.sqrt M := Real.sqrt_le_sqrt hst.1
  have hh := sqrt_dot_sub_leE y st.mu
  have hsM := Real.sqrt_nonneg M
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  set a := M * Real.sqrt d * (Real.sqrt (y ⬝ᵥ y) + Real.sqrt M) with ha
  set r := Real.sqrt (y ⬝ᵥ y) + Real.sqrt M with hr
  have hr0 : 0 ≤ r := by positivity
  have hhr : Real.sqrt ((y - st.mu) ⬝ᵥ (y - st.mu)) ≤ r := hh.trans (by linarith)
  have hu : Real.sqrt ((st.P *ᵥ (st.A *ᵥ z)) ⬝ᵥ (st.P *ᵥ (st.A *ᵥ z))) ≤ M * (Real.sqrt d * ‖z‖) := by
    calc _ ≤ Real.sqrt M * (Real.sqrt M * Real.sqrt (z ⬝ᵥ z)) := hP.trans (mul_le_mul_of_nonneg_left hA hsM)
      _ = M * Real.sqrt (z ⬝ᵥ z) := by rw [← mul_assoc, hMM]
      _ ≤ M * (Real.sqrt d * ‖z‖) := mul_le_mul_of_nonneg_left hz hM
  have hl : |EvSI.lin st (y - st.mu) z| ≤ a * ‖z‖ := by
    unfold EvSI.lin
    refine (EvSI.abs_dot_le _ _).trans ((mul_le_mul hu hhr (Real.sqrt_nonneg _) (by positivity)).trans
      (le_of_eq ?_))
    rw [ha, hr]; ring
  have hq : |df2Sq st.P (y - st.mu)| ≤ Real.sqrt M * r ^ 2 := by
    unfold df2Sq
    have h1 := EvSI.bdSet_apply hst.2.2 hM (y - st.mu)
    calc _ ≤ Real.sqrt ((y - st.mu) ⬝ᵥ (y - st.mu)) *
          Real.sqrt ((st.P *ᵥ (y - st.mu)) ⬝ᵥ (st.P *ᵥ (y - st.mu))) := EvSI.abs_dot_le _ _
      _ ≤ r * (Real.sqrt M * r) :=
        mul_le_mul hhr (h1.trans (mul_le_mul_of_nonneg_left hhr hsM)) (Real.sqrt_nonneg _) hr0
      _ = Real.sqrt M * r ^ 2 := by ring
  have hz0 := norm_nonneg z
  have hl2 : EvSI.lin st (y - st.mu) z ^ 2 ≤ a ^ 2 * ‖z‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have hzz : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ hz0 (by linarith) 2
  have h1z : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  have hlk : 0 ≤ p.lam * p.k0 := mul_nonneg hl0 hk0
  unfold KphiHE
  rw [← ha, ← hr]
  show |p.lam * p.k0 * (EvSI.lin st (y - st.mu) z ^ 2 - df2Sq st.P (y - st.mu))| ≤
    p.lam * p.k0 * (a ^ 2 + Real.sqrt M * r ^ 2) * (1 + ‖z‖) ^ 2
  rw [abs_mul, abs_of_nonneg hlk, mul_assoc _ (a ^ 2 + _)]
  refine mul_le_mul_of_nonneg_left ?_ hlk
  have hsq0 := sq_nonneg (EvSI.lin st (y - st.mu) z)
  have hab : |EvSI.lin st (y - st.mu) z ^ 2 - df2Sq st.P (y - st.mu)| ≤
      EvSI.lin st (y - st.mu) z ^ 2 + |df2Sq st.P (y - st.mu)| := by
    have := abs_sub (EvSI.lin st (y - st.mu) z ^ 2) (df2Sq st.P (y - st.mu))
    rwa [abs_of_nonneg hsq0] at this
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
  have hmr : 0 ≤ Real.sqrt M * r ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hzz ha2, mul_le_mul_of_nonneg_left h1z hmr]

theorem measurable_phiHE (p : Df2OPar) (h : Df2St d → Fin d → ℝ) (hh : Measurable h) :
    Measurable fun x : Df2St d × (Fin d → ℝ) => phiHE p h x.1 x.2 := by
  unfold phiHE
  have hl : Measurable fun x : Df2St d × (Fin d → ℝ) => EvSI.lin x.1 (h x.1) x.2 := by
    have := EvSI.measurable_lin.comp (measurable_fst.prodMk ((hh.comp measurable_fst).prodMk measurable_snd))
    exact this
  have hq : Measurable fun x : Df2St d × (Fin d → ℝ) => df2Sq x.1.P (h x.1) := by
    unfold df2Sq
    have hPh : Measurable fun x : Df2St d × (Fin d → ℝ) => x.1.P *ᵥ h x.1 :=
      (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
        ((ApMeas.measurable_st_P.comp measurable_fst).prodMk (hh.comp measurable_fst))
    exact (continuous_fst.dotProduct continuous_snd).measurable.comp ((hh.comp measurable_fst).prodMk hPh)
  have h := ((hl.pow_const 2).sub hq).const_mul (p.lam * p.k0)
  exact h

/-! ## On a path -/

section path

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- The fourth moment of a Hessian direction: `(E_z φ_H⁴)^{1/4} ≤ 7 λ κ₀ hᵀ P_s h`. -/
theorem phiHE_d4E (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hf : Df2St d → Fin d → ℝ) :
    (∫ z, phiHE c.p hf (c.st π s) z ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
      7 * (c.p.lam * c.p.k0) * df2Sq (c.st π s).P (hf (c.st π s)) := by
  have hI := H.stInv_le_tau s hs
  set st := c.st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ hf st) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (hf st) := EvSI.dir_sq st hI.AA hI.SP _
  have hphi : ∀ z, phiHE c.p hf st z ^ 4 = ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 4 * (c.p.lam * c.p.k0) ^ 4 := by
    intro z
    show (c.p.lam * c.p.k0 * (EvSI.lin st (hf st) z ^ 2 - df2Sq st.P (hf st))) ^ 4 = _
    rw [EvSI.lin_eq_dot st (EvSI.P_symm hI), ← hb, ← hbb]; ring
  have hlk : 0 ≤ c.p.lam * c.p.k0 := mul_nonneg H.rows.pos_lam.le (k0_nonnegE H)
  have hb0 : 0 ≤ b ⬝ᵥ b := EvSI.dot_self_nonneg' b
  have e1 : ∫ z, phiHE c.p hf st z ^ 4 ∂(EvSI.gam d) =
      ∫ z, ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 4 * (c.p.lam * c.p.k0) ^ 4 ∂(EvSI.gam d) :=
    integral_congr_ae (Filter.Eventually.of_forall hphi)
  have hK : Real.sqrt 2027025 + 1 ≤ 7 ^ 4 := by
    have : Real.sqrt 2027025 ≤ 2400 := by
      rw [show (2400 : ℝ) = Real.sqrt (2400 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hint : ∫ z, phiHE c.p hf st z ^ 4 ∂(EvSI.gam d) ≤ (7 * (c.p.lam * c.p.k0) * (b ⬝ᵥ b)) ^ 4 := by
    rw [e1, integral_mul_const]
    calc (∫ z, ((z ⬝ᵥ b) ^ 2 - b ⬝ᵥ b) ^ 4 ∂(EvSI.gam d)) * (c.p.lam * c.p.k0) ^ 4
        ≤ ((Real.sqrt 2027025 + 1) * (b ⬝ᵥ b) ^ 4) * (c.p.lam * c.p.k0) ^ 4 :=
          mul_le_mul_of_nonneg_right (SKp.int_dot_sq_sub_pow_four b) (by positivity)
      _ ≤ (7 ^ 4 * (b ⬝ᵥ b) ^ 4) * (c.p.lam * c.p.k0) ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (by positivity)
      _ = (7 * (c.p.lam * c.p.k0) * (b ⬝ᵥ b)) ^ 4 := by ring
  have hI0 : 0 ≤ ∫ z, phiHE c.p hf st z ^ 4 ∂(EvSI.gam d) :=
    integral_nonneg fun z => (by positivity : (0 : ℝ) ≤ phiHE c.p hf st z ^ 4)
  rw [← hbb]
  calc _ ≤ ((7 * (c.p.lam * c.p.k0) * (b ⬝ᵥ b)) ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hI0 hint (by norm_num)
    _ = _ := pow_four_rpow (mul_nonneg (mul_nonneg (by norm_num) hlk) hb0)

/-- The fourth moment of the direction of (e): `(E_z φ_H(w)⁴)^{1/4} ≤ 7 λ κ₀ lvQ`. -/
theorem dq_d4E (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {w : Fin d → ℝ}
    (hq : df2Sq (c.st π s).P (w - (c.st π s).mu) ≤ lvQ c.p) :
    (∫ z, phiHE c.p (fun st => w - st.mu) (c.st π s) z ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
      7 * (c.p.lam * c.p.k0) * lvQ c.p := by
  have hlk : 0 ≤ c.p.lam * c.p.k0 := mul_nonneg H.rows.pos_lam.le (k0_nonnegE H)
  exact (phiHE_d4E H hs (fun st => w - st.mu)).trans (mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) hlk))

/-- The second moments of the increments of (e) at `w` sum to at most `lvVe` up to `t ≤ τ`. -/
theorem dq_varE (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) {y w : Fin d → ℝ} (hy : y ∈ c.SS π t)
    (hc : (w - y) ⬝ᵥ (w - y) ≤ c.p.δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
      phiHE c.p (fun st => w - st.mu) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤ lvVe c.p d c.n := by
  have hx := H.x_ge
  set T := (16 * lvX c.p) ^ 2 with hTdef
  have hT : 1 ≤ T := by rw [hTdef, lvX]; nlinarith
  have hk0 := k0_nonnegE H
  have hq := lvQ_nonnegE H
  set τ0 := Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
      phiHE c.p (fun st => w - st.mu) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      (c.p.lam * c.p.k0) ^ 2 * (lvQ c.p ^ 2 *
        (T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) + Real.sqrt (lvWb c.p d) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_HE H (hs'.trans ht) (fun st => w - st.mu) T hT
    have hqs := lq_qE H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) :=
      integral_nonneg fun z => yRE_nonneg c.p c.Kt (π.g s) _ z
    have hY2 := intY2_leE H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) ≤ Real.sqrt (lvWb c.p d) :=
      Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
        Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) * τ0 := by
      have : 0 ≤ T := by linarith
      positivity
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef (w - (c.st π s).mu)
    have hq2 : df2Sq (c.st π s).P (w - (c.st π s).mu) ^ 2 ≤ lvQ c.p ^ 2 := pow_le_pow_left₀ hP0 hqs 2
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    refine mul_le_mul hq2 ?_ hinner (sq_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hτ0n)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsum := sumY_leE H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ c.n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ c.n)
  have hW : 0 ≤ Real.sqrt (lvWb c.p d) * τ0 := by positivity
  unfold lvVe
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (sq_nonneg _)
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤
      T * (9 * c.n) := mul_le_mul_of_nonneg_left hsum (by linarith)
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (lvWb c.p d) * τ0) ≤ c.n * (Real.sqrt (lvWb c.p d) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

/-- `ŝ''_s - s''_s(μ_s)` is symmetric up to `τ`. -/
theorem dq_symmE (H : DetBase c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    (c.shh π s - c.sHess π s)ᵀ = c.shh π s - c.sHess π s := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have h1 : (c.sHess π s)ᵀ = c.sHess π s := EvSI.hessM_transpose _ hsi.c2 _
  have h2 : (c.shh π s)ᵀ = c.shh π s := by
    unfold Df2Ctx.shh
    rw [transpose_smul, transpose_sub, transpose_vecMulVec, EvSI.P_symm hI]
  rw [transpose_sub, h1, h2]

theorem lvKe_nonnegE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ π m) :
    0 ≤ lvKe c.p d b0 y0 := by
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hde : 0 < c.p.δe := H.rows.pos_de
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hl1 : 0 < 1 - c.p.lam := by have := lam_ltE H; linarith
  have hk0 := k0_nonnegE H
  unfold lvKe
  positivity

/-- `|vᵀ (ŝ''_s - s''_s(μ_s)) v| ≤ lvKe |v|²` up to `τ`, under the sure ranges. -/
theorem dq_quadE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) (v : Fin d → ℝ) :
    |v ⬝ᵥ ((c.shh (pathW c b0 y0 π) s - c.sHess (pathW c b0 y0 π) s) *ᵥ v)| ≤ lvKe c.p d b0 y0 * (v ⬝ᵥ v) := by
  set πw := pathW c b0 y0 π with hπw
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hde : 0 < c.p.δe := H.rows.pos_de
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hk0 := k0_nonnegE H
  have hlk : 0 ≤ c.p.lam * c.p.k0 := mul_nonneg hl0.le hk0
  set st := c.st πw s with hstdef
  obtain ⟨hY, hYξ⟩ := Y_sure c b0 y0 π s hy0 hI.run
  have hvv := EvSI.dot_self_nonneg' v
  have hPv : df2Sq st.P v ≤ c.p.δe⁻¹ * (v ⬝ᵥ v) := EvSI.quad_le_of_psd (EvSI.P_upper H hI) v
  have hP0 : 0 ≤ df2Sq st.P v := sq_nonneg_of_psd hI.pd.posSemidef v
  have hshh : |df2Sq (c.shh πw s) v| ≤ c.p.lam * c.p.k0 * y0 * ((b0 + 2) / c.p.δe) * (v ⬝ᵥ v) := by
    change |df2Sq ((c.p.lam * c.p.k0 * c.Y πw s) • (vecMulVec (c.u πw s) (c.u πw s) - st.P)) v| ≤ _
    rw [EvSI.df2Sq_rank_one, abs_mul, abs_mul, abs_mul, abs_of_pos hl0, abs_of_nonneg hk0]
    by_cases hY0 : c.Y πw s = 0
    · rw [hY0, abs_zero, mul_zero, zero_mul]; positivity
    have hξ := hYξ hY0
    have hu : c.u πw s ⬝ᵥ c.u πw s ≤ (b0 + 1) / c.p.δe :=
      (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (EvSI.P_upper H hI)).trans
        (div_le_div_of_nonneg_right hξ hde.le)
    have huv : (c.u πw s ⬝ᵥ v) ^ 2 ≤ (b0 + 1) / c.p.δe * (v ⬝ᵥ v) := by
      have h1 := EvSI.abs_dot_le (c.u πw s) v
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (EvSI.dot_self_nonneg' _), Real.sq_sqrt hvv] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right hu hvv)
    have hsq := sq_nonneg (c.u πw s ⬝ᵥ v)
    have hsplit : (b0 + 2) / c.p.δe * (v ⬝ᵥ v) = (b0 + 1) / c.p.δe * (v ⬝ᵥ v) + c.p.δe⁻¹ * (v ⬝ᵥ v) := by ring
    have hK1 : 0 ≤ (b0 + 1) / c.p.δe * (v ⬝ᵥ v) := mul_nonneg (div_nonneg (by linarith) hde.le) hvv
    have hK2 : 0 ≤ c.p.δe⁻¹ * (v ⬝ᵥ v) := mul_nonneg (inv_nonneg.2 hde.le) hvv
    have hab : |(c.u πw s ⬝ᵥ v) ^ 2 - df2Sq st.P v| ≤ (b0 + 2) / c.p.δe * (v ⬝ᵥ v) := by
      rw [abs_le, hsplit]; constructor <;> linarith
    calc c.p.lam * c.p.k0 * |c.Y πw s| * |(c.u πw s ⬝ᵥ v) ^ 2 - df2Sq st.P v| ≤
          c.p.lam * c.p.k0 * y0 * ((b0 + 2) / c.p.δe * (v ⬝ᵥ v)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hY hlk) hab (abs_nonneg _) (mul_nonneg hlk hy0)
      _ = _ := by ring
  have hH : |df2Sq (c.sHess πw s) v| ≤
      c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (d / c.p.δe) * (v ⬝ᵥ v) :=
    hsi.hess1 (WithLp.toLp 2 st.mu) v
  have e1 : v ⬝ᵥ ((c.shh πw s - c.sHess πw s) *ᵥ v) = df2Sq (c.shh πw s) v - df2Sq (c.sHess πw s) v :=
    EvSI.df2Sq_sub _ _ v
  rw [e1]
  unfold lvKe
  calc _ ≤ |df2Sq (c.shh πw s) v| + |df2Sq (c.sHess πw s) v| := abs_sub _ _
    _ ≤ _ := add_le_add hshh hH
    _ = _ := by ring

/-- The centred increment of (e) at `w` is at most `lvRe` in absolute value up to `τ`, for any value `cm` within
`lvBe` of the mean `(w - μ_s)ᵀ s''_s (w - μ_s)`. -/
theorem dq_rangeE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) {w : Fin d → ℝ}
    (hq : df2Sq (c.st (pathW c b0 y0 π) s).P (w - (c.st (pathW c b0 y0 π) s).mu) ≤ lvQ c.p) {cm : ℝ}
    (hcm : |cm - df2Sq (c.sHess (pathW c b0 y0 π) s) (w - (c.st (pathW c b0 y0 π) s).mu)| ≤ lvBe c.p d) :
    |c.Y (pathW c b0 y0 π) s * phiHE c.p (fun st => w - st.mu) (c.st (pathW c b0 y0 π) s) (π.xi s) - cm| ≤
      lvRe c.p d b0 y0 := by
  set πw := pathW c b0 y0 π with hπw
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hl1 := lam_ltE H
  have hk0 := k0_nonnegE H
  have hlk : 0 ≤ c.p.lam * c.p.k0 := mul_nonneg hl0.le hk0
  have hq0 := lvQ_nonnegE H
  set st := c.st πw s with hstdef
  obtain ⟨hY, hYξ⟩ := Y_sure c b0 y0 π s hy0 hI.run
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (w - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (w - st.mu) := EvSI.dir_sq st hI.AA hI.SP _
  have hP0 : 0 ≤ df2Sq st.P (w - st.mu) := sq_nonneg_of_psd hI.pd.posSemidef _
  have h1 : |c.Y πw s * phiHE c.p (fun st => w - st.mu) st (π.xi s)| ≤
      y0 * (c.p.lam * c.p.k0) * ((b0 + 2) * lvQ c.p) := by
    by_cases hY0 : c.Y πw s = 0
    · rw [hY0, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg hy0 hlk) (mul_nonneg (by linarith) hq0)
    have hξ := hYξ hY0
    have hb1 : 0 ≤ b0 + 1 := le_trans (EvSI.dot_self_nonneg' _) hξ
    have hlin : EvSI.lin st (w - st.mu) (π.xi s) = π.xi s ⬝ᵥ b := by
      rw [EvSI.lin_eq_dot st (EvSI.P_symm hI), ← hb]
    have hl2 : EvSI.lin st (w - st.mu) (π.xi s) ^ 2 ≤ (b0 + 1) * lvQ c.p := by
      rw [hlin]
      have h1 := EvSI.abs_dot_le (π.xi s) b
      have h2 : |π.xi s ⬝ᵥ b| ^ 2 ≤ (Real.sqrt (π.xi s ⬝ᵥ π.xi s) * Real.sqrt (b ⬝ᵥ b)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (EvSI.dot_self_nonneg' _), Real.sq_sqrt (EvSI.dot_self_nonneg' _),
        hbb] at h2
      exact h2.trans (mul_le_mul hξ hq hP0 hb1)
    have hph : |phiHE c.p (fun st => w - st.mu) st (π.xi s)| ≤ c.p.lam * c.p.k0 * ((b0 + 2) * lvQ c.p) := by
      show |c.p.lam * c.p.k0 * (EvSI.lin st (w - st.mu) (π.xi s) ^ 2 - df2Sq st.P (w - st.mu))| ≤ _
      rw [abs_mul, abs_of_nonneg hlk]
      refine mul_le_mul_of_nonneg_left ?_ hlk
      have hsq := sq_nonneg (EvSI.lin st (w - st.mu) (π.xi s))
      rw [abs_le]; constructor <;> nlinarith
    rw [abs_mul]
    calc |c.Y πw s| * |phiHE c.p (fun st => w - st.mu) st (π.xi s)| ≤
          y0 * (c.p.lam * c.p.k0 * ((b0 + 2) * lvQ c.p)) := mul_le_mul hY hph (abs_nonneg _) hy0
      _ = _ := by ring
  have hS : (st.A * st.Aᵀ)⁻¹ = st.P := by rw [hI.AA]; exact Matrix.inv_eq_right_inv hI.SP
  have h2 : |df2Sq (c.sHess πw s) (w - st.mu)| ≤
      c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) * lvQ c.p := by
    have h := hsi.hess2 (WithLp.toLp 2 st.mu) (w - st.mu)
    rw [hS] at h
    have hK : 0 ≤ c.p.lam * (8 / c.p.eps) / (1 - c.p.lam) * Real.sqrt (2 * d * c.p.sig2) := by
      have : 0 < 1 - c.p.lam := by linarith
      positivity
    exact h.trans (mul_le_mul_of_nonneg_left hq hK)
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨c1, c2⟩ := abs_le.1 hcm
  unfold lvRe
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- `G_t(y)` and `G_t(w)` differ by at most `n lvKe δ_e⁴ 4R` up to `τ`, under the sure ranges. -/
theorem dq_disc_pathE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {t : ℕ}
    (ht : t ≤ c.tau (pathW c b0 y0 π) m) {y w : Fin d → ℝ} (hyR : y ⬝ᵥ y ≤ c.p.R ^ 2) (hwR : w ⬝ᵥ w ≤ c.p.R ^ 2)
    (hyw : Real.sqrt ((y - w) ⬝ᵥ (y - w)) ≤ c.p.δe ^ 4) :
    |c.GG (pathW c b0 y0 π) t y - c.GG (pathW c b0 y0 π) t w| ≤
      c.n * lvKe c.p d b0 y0 * (c.p.δe ^ 4 * (4 * c.p.R)) := by
  set πw := pathW c b0 y0 π with hπw
  have hR0 : 0 ≤ c.p.R := by linarith [H.rows.one_le_R]
  have hK0 : 0 ≤ lvKe c.p d b0 y0 := lvKe_nonnegE hb0 hy0 H
  have hde : 0 < c.p.δe := H.rows.pos_de
  have hterm : ∀ s ≤ t, |df2Sq (c.shh πw s - c.sHess πw s) (y - (c.st πw s).mu) -
      df2Sq (c.shh πw s - c.sHess πw s) (w - (c.st πw s).mu)| ≤ lvKe c.p d b0 y0 * (c.p.δe ^ 4 * (4 * c.p.R)) := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := c.st πw s
    rw [EvSI.sq_sub_sq _ (dq_symmE H hs)]
    have h1 := EvSI.bilin_le_of_quad _ (dq_symmE H hs) (lvKe c.p d b0 y0) (dq_quadE hb0 hy0 H hs)
      ((y - st.mu) - (w - st.mu)) ((y - st.mu) + (w - st.mu))
    have e1 : (y - st.mu) - (w - st.mu) = y - w := by abel
    rw [e1] at h1 ⊢
    have hmu := EvSI.sqrt_dot_le_of hR0 (EvSI.mu_sq_le H hI)
    have hy1 := EvSI.sqrt_dot_le_of hR0 hyR
    have hc1 := EvSI.sqrt_dot_le_of hR0 hwR
    have hy2 := sqrt_dot_sub_leE y st.mu
    have hc2 := sqrt_dot_sub_leE w st.mu
    have h2 : Real.sqrt (((y - st.mu) + (w - st.mu)) ⬝ᵥ ((y - st.mu) + (w - st.mu))) ≤ 4 * c.p.R :=
      (EvSI.sqrt_dot_add_le _ _).trans (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul hyw h2 (Real.sqrt_nonneg _) (by positivity)) hK0)
  unfold Df2Ctx.GG
  rw [← Finset.sum_sub_distrib]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ c.n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ c.n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |df2Sq (c.shh πw s - c.sHess πw s) (y - (c.st πw s).mu) -
        df2Sq (c.shh πw s - c.sHess πw s) (w - (c.st πw s).mu)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), lvKe c.p d b0 y0 * (c.p.δe ^ 4 * (4 * c.p.R)) :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (lvKe c.p d b0 y0 * (c.p.δe ^ 4 * (4 * c.p.R))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ c.n * (lvKe c.p d b0 y0 * (c.p.δe ^ 4 * (4 * c.p.R))) :=
      mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

end path

/-! ## Event (e) -/

/-- **Event (e) of Theorem UW**: DQ at T4U on the weighted path fails with probability at most `δc/8`, from the
rows, the facts of SI and the needs of the events. -/
theorem evDQPropUW_of (hS : SIFactsUW) (hR : RowsUW) (hN : EvNeedsUW) : EvDQPropUW := by
  intro d n m ρ hreg hm1 hmn Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  have N := (hN d n ρ hreg).needE
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
  have hl1' : 0 < 1 - p.lam := by linarith
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
  have hb0' : 0 ≤ ρ.b0 := by
    have : (0 : ℝ) ≤ 2 * d := by positivity
    linarith
  have hy0 : 10 + 18 / p.eps + 10 * Real.sqrt (p.Le / 3) ≤ ρ.y0 := by
    rw [hLlam, show 36 * lam0 d n / 3 = 12 * lam0 d n by ring]; exact hreg.y0_lo
  have hy0p : 0 < ρ.y0 := by
    have : 0 ≤ 18 / p.eps := div_nonneg (by norm_num) he0.le
    have := Real.sqrt_nonneg (p.Le / 3)
    linarith
  have hy00 : 0 ≤ ρ.y0 := hy0p.le
  have hdc0 : 0 < ρ.δc := hreg.dc_pos
  have hdc1 : ρ.δc ≤ p.δe := hreg.dc_le
  -- the levels
  have hC0 : 0 ≤ 1 + 2 / p.eps := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) he0.le; linarith
  have hk0p : 0 < p.k0 := by rw [hfix.k0]; positivity
  have hk0 : 0 ≤ p.k0 := hk0p.le
  have hQp : 0 < lvQ p := by unfold lvQ; positivity
  have hQ0 : 0 ≤ lvQ p := hQp.le
  have hB0 : 0 ≤ lvBias p d := by unfold lvBias; positivity
  have hBe0 : 0 ≤ lvBe p d := by unfold lvBe; positivity
  have hV0 : 0 ≤ lvVe p d n := by unfold lvVe; positivity
  have hRe : 0 < lvRe p d ρ.b0 ρ.y0 := by
    unfold lvRe
    have h1 : 0 < ρ.y0 * (p.lam * p.k0) * ((ρ.b0 + 2) * lvQ p) := by positivity
    have h2 : 0 ≤ p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2) * lvQ p := by positivity
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
        DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) (σ s ω, ξ s ω) else 0 := ⟨_, rfl⟩
  have hXlt : ∀ c s, s < m → X c s = fun ω =>
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) (σ s ω, ξ s ω) := by
    intro c s hs; rw [hXdef]; funext ω; simp only [hs, ↓reduceIte]
  have hXpt : ∀ c s, s < m → ∀ ω, X c s ω =
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) (σ s ω, ξ s ω) :=
    fun c s hs ω => by rw [hXlt c s hs]
  have hφm : ∀ c : E d, Measurable fun x : Df2St d × (Fin d → ℝ) =>
      phiHE p (fun st => WithLp.ofLp c - st.mu) x.1 x.2 :=
    fun c => measurable_phiHE p _ (measurable_const.sub ApMeas.measurable_st_mu)
  -- Lemma U
  have hgr : ∀ (c : E d) (s : ℕ), s < m →
      (∀ x, |EtrE p Kθ gθ M s x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiHE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |PtrE p Kθ M x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiHE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiHE p M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) :=
    fun c s hs => trunc_growth (φ := phiHE p (fun st => WithLp.ofLp c - st.mu)) hp hbody (fun q => hadm q s hs)
      (KphiHE_nonneg hl0.le hk0 _) (fun st hst z => phiHE_growth hM0 hl0.le hk0 _ hst z)
  have hU := lemmaU_setW (d := d) μ 𝒢 C m n hmn σ ξ e hσm hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int
    hE.e_mean hE.e_exp (EtrE p Kθ gθ M) (fun _ => PtrE p Kθ M)
    (fun c _ => DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)))
    (fun s hs => measurable_EtrE hmeas.1 (hmeas.2.1 s hs)) (fun _ _ => measurable_PtrE hmeas.1)
    (fun c _ _ => measurable_DtrE hmeas.1 (hφm c))
    (fun c => (1 + 2 / p.eps) * (1 + Real.sqrt d) + KphiHE p M (WithLp.ofLp c)) 2
    (fun c => add_nonneg (mul_nonneg hC0 (by positivity)) (KphiHE_nonneg hl0.le hk0 _))
    (fun c s hs => (hgr c s hs).1) (fun c s hs => (hgr c s hs).2.1) (fun c s hs => (hgr c s hs).2.2)
    (obsW ρ.b0 ρ.y0) (measurable_obsW_uncurry ρ.b0 ρ.y0) (fun x y => (obsW_sure hy00 ρ.b0 x y).2.1)
    (lvRe p d ρ.b0 ρ.y0)⁻¹ (ρ.δc / 8) (inv_pos.2 hRe) (by positivity) (by linarith)
    (fun _ _ _ => lvVe p d n) (fun _ _ _ => lvRe p d ρ.b0 ρ.y0) X (fun c s => by subst hXdef; rfl)
  -- the bias of each round, outside a null set (Lemma SK')
  have hbias : ∀ᵐ ω ∂μ, ∀ c ∈ C, ∀ s ∈ Finset.range m,
      |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) *
          DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) (σ s ω, z) ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun st => WithLp.ofLp c - st.mu)) (σ s ω, z) ^ 4
          ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := by
    refine (Filter.eventually_all_finset C).2 fun c _ => (Filter.eventually_all_finset _).2 fun s hs => ?_
    have hs' : s < m := Finset.mem_range.1 hs
    rw [hXlt c s hs']
    exact biasE hd hp hbody (fun q => hadm q s hs') hmeas.1 (hmeas.2.1 s hs') hb0 hy0 (hφm c)
      (KphiHE_nonneg hl0.le hk0 _) (fun st hst z => phiHE_growth hM0 hl0.le hk0 _ hst z)
      (𝒢 s) μ (𝒢.le s) (σ s) (ξ s) (e s) (hσm s hs') ((hE.xi_meas s).mono (𝒢.le _) le_rfl)
      ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.xi_law s) (hE.xi_indep s) (hE.e_int s) (hE.e_mean s) (hE.e_exp s)
  refine le_trans (measure_le_of_ae_memE ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  filter_upwards [hbias] with ω hb hbad
  -- the epoch at `ω`
  set cx := ctxE d n ρ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω)) with hcx
  set π0 : Df2Path d := ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ with hπ0
  set πw := pathW cx ρ.b0 ρ.y0 π0 with hπw
  have H : DetBase cx (1 / 2) πw m := detBaseE hS hR hreg hm1 hmn hbody hadm hap ψ hK ξ e ω
  unfold EvDQW at hbad
  push Not at hbad
  obtain ⟨t, ht, y, hyR, hyS, hlt⟩ := hbad
  have hlt' : bnW p d n ρ.u / (p.Le * p.lam ^ 2) < |cx.GG πw t y| := hlt
  have htm : t < m := lt_of_le_of_lt ht H.tau_lt
  -- the point of the net
  have hyball : (WithLp.toLp 2 y : E d) ∈ Metric.closedBall 0 p.R := by
    rw [mem_closedBall_zero_iff, EvSI.norm_toLp]; exact hyR
  have hyR2 : y ⬝ᵥ y ≤ p.R ^ 2 := by
    have h1 : Real.sqrt (y ⬝ᵥ y) ≤ p.R := hyR
    rw [← Real.sq_sqrt (EvSI.dot_self_nonneg' y)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
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
  -- the increment at `c` is `Y φ_H(c)`
  have hXv : ∀ s ≤ t, X c s ω = cx.Y πw s * phiHE cx.p (fun st => c' - st.mu) (cx.st πw s) (π0.xi s) := by
    intro s hs
    have hI := H.stInv_le_tau s (hs.trans ht)
    have hg := hgood s hs
    rw [hXpt c s (lt_of_le_of_lt hs htm) ω, EtrE_of (x := (σ s ω, ξ s ω)) hg, PtrE_of (x := (σ s ω, ξ s ω)) hg,
      DtrE_of (x := (σ s ω, ξ s ω)) hg, hσdef, ← Y_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s _ hI.run]
    rfl
  -- the conditional mean is Lemma UB's mean up to the bias
  have hbiasω : ∀ s ≤ t,
      |μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu)| ≤ lvBe p d := by
    intro s hs
    have hs' := hs.trans ht
    have hsm : s < m := lt_of_le_of_lt hs htm
    have hg := hgood s hs
    have h1 : |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) *
          DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ^ 4
          ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) :=
      hb c hcC s (Finset.mem_range.2 hsm)
    have hq : df2Sq (cx.st πw s).P (c' - (cx.st πw s).mu) ≤ lvQ cx.p := lq_qE H ht hyS hc8 hs
    have hm := mean_HE H hs' (fun st => c' - st.mu)
    have hmean : ∫ z, EtrE p Kθ gθ M s (σ s ω, z) * DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z)
        ∂(EvSI.gam d) = df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu) := by
      rw [← hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      rw [EtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
        fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
      rfl
    have hD4 : (∫ z, DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
        7 * (p.lam * p.k0) * lvQ p := by
      have e1 : ∫ z, DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ^ 4 ∂(EvSI.gam d) =
          ∫ z, phiHE cx.p (fun st => c' - st.mu) (cx.st πw s) z ^ 4 ∂(EvSI.gam d) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        beta_reduce
        rw [DtrE_of (x := (σ s ω, z)) hg, hσω s]
        rfl
      rw [e1]
      exact dq_d4E H hs' hq
    rw [hmean] at h1
    calc _ ≤ lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ^ 4
            ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := h1
      _ ≤ lvBias p d * (7 * (p.lam * p.k0) * lvQ p) := mul_le_mul_of_nonneg_left hD4 hB0
      _ = lvBe p d := rfl
  -- the variance
  have hvar : ∑ s ∈ Finset.range (t + 1), ∫ z, (EtrE p Kθ gθ M s (σ s ω, z) ^ 2 + PtrE p Kθ M (σ s ω, z) ^ 2) *
      DtrE p Kθ M (phiHE p (fun st => c' - st.mu)) (σ s ω, z) ^ 2 ∂(EvSI.gam d) ≤ lvVe p d n := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (dq_varE H ht hyS hc8)
    have hg := hgood s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [EtrE_of (x := (σ s ω, z)) hg, PtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
      fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z, fPE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
    rfl
  -- the deviation
  have hsumX : ∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω) =
      cx.GG πw t c' -
      ∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu)) := by
    unfold Df2Ctx.GG
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsh := shh_sqE cx πw s (fun st => c' - st.mu)
    rw [hXv s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), EvSI.df2Sq_sub, hsh,
      show πw.xi s = π0.xi s from rfl]
    ring
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : t + 1 ≤ n)
  have hbsum : |∑ s ∈ Finset.range (t + 1),
      (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu))| ≤ n * lvBe p d := by
    calc _ ≤ ∑ s ∈ Finset.range (t + 1), |μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ Finset.range (t + 1), lvBe p d :=
          Finset.sum_le_sum fun s hs => hbiasω s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
      _ = ((t + 1 : ℕ) : ℝ) * lvBe p d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * lvBe p d := mul_le_mul_of_nonneg_right htn hBe0
  have hdisc : |cx.GG πw t y - cx.GG πw t c'| ≤ n * lvKe p d ρ.b0 ρ.y0 * (p.δe ^ 4 * (4 * p.R)) :=
    dq_disc_pathE hb0' hy00 H ht hyR2 hcR hyc
  have hC1 : (1 : ℝ) ≤ C.card := by
    have h : 1 ≤ C.card := Finset.card_pos.2 ⟨c, hcC⟩
    exact_mod_cast h
  have hNc := N (C.card : ℝ) hC1 hCcard
  have key : 3 * Real.sqrt (lvVe p d n * lvLogE p d n ρ.b0 ρ.y0 ρ.δc C.card) +
      2 * lvRe p d ρ.b0 ρ.y0 * lvLogE p d n ρ.b0 ρ.y0 ρ.δc C.card <
      |∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω)| := by
    rw [hsumX]
    set A := cx.GG πw t y with hA
    set B := cx.GG πw t c' with hB
    set Bs := ∑ s ∈ Finset.range (t + 1),
      (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) (c' - (cx.st πw s).mu)) with hBs
    have h2 := abs_sub_abs_le_abs_sub A B
    have h3 : |B| - |B - Bs| ≤ |Bs| := by
      have := abs_sub_abs_le_abs_sub B (B - Bs)
      rwa [sub_sub_cancel] at this
    linarith
  refine ⟨c, hcC, t, htm, hV0, ?_, hvar, ?_, key⟩
  · show 1 ≤ (lvRe p d ρ.b0 ρ.y0)⁻¹ * lvRe p d ρ.b0 ρ.y0
    rw [inv_mul_cancel₀ hRe.ne']
  · intro s hs
    rw [hXv s hs]
    exact dq_rangeE hb0' hy00 H (hs.trans ht) (lq_qE H ht hyS hc8 hs) (hbiasω s hs)

end AdversarialBco.UW
