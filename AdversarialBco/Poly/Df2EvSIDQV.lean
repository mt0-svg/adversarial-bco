/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSIDQ
public import AdversarialBco.Poly.Df2EvSILQV

@[expose] public section

/-!
# The event DQ on a path, with a routine per round

At the context `df2CtxAtF d n δ Kt ap` with a routine `ap s` in round `s` (`ap : ℕ → ApFun d`), on a path with the
hypotheses of DET without the events (`DetBase`), up to `τ`: the second moments of the increments at a net point `c`
sum to at most `VD` (`dq_varV`), the increments are at most `RD` on G (`dq_rangeV`), `ŝ''_s - s''_s(μ_s)` is symmetric
(`dq_symmV`) with `|vᵀ (ŝ''_s - s''_s(μ_s)) v| ≤ KD |v|²` on G (`dq_quadV`), and the sums at `y` and at `c` differ by
at most `n KD δ⁴ 4R` on G (`dq_disc_pathV`). The levels are those of Df2EvSIDQ.lean.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix

namespace AdversarialBco.Poly.EvSI

open Layer2

variable {d : ℕ}

section path

variable {n : ℕ} {δ : ℝ} {Kt : Set (E d)} {ap : ℕ → ApFun d} {π : Df2Path d} {m : ℕ}

/-- The second moments of the increments at `c` sum to at most `VD`. -/
theorem dq_varV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {t : ℕ} (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m)
    {y c : Fin d → ℝ} (hy : y ∈ (df2CtxAtF d n δ Kt ap).SS π t)
    (hc : (c - y) ⬝ᵥ (c - y) ≤ (df2oPar d n δ).δe ^ 8) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
      phiH n δ (fun st => c - st.mu) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤ VD d n δ := by
  have hx := xq_posV H
  set T := (16 * xq d n δ) ^ 2 with hTdef
  have hT : 1 ≤ T := by rw [hTdef]; nlinarith
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eqV H]; positivity
  have hq : 0 ≤ qL d n δ := qL_nonneg H.hd H.hn H.rows
  set τ0 := Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z *
      phiH n δ (fun st => c - st.mu) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d) ≤
      ((df2oPar d n δ).lam * (df2oPar d n δ).k0) ^ 2 * (qL d n δ ^ 2 *
        (T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) + Real.sqrt (WbL d n δ) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_HV H (hs'.trans ht) (fun st => c - st.mu) T hT
    have hqs := lq_qV H ht hy hc hs'
    have hY0 : 0 ≤ ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) :=
      integral_nonneg fun z => yR_nonneg n δ Kt (π.g s) _ z
    have hY2 := intY2_leV H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) ≤
        Real.sqrt (WbL d n δ) := Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) +
        Real.sqrt (∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ^ 2 ∂(gam d)) * τ0 := by
      have : 0 ≤ T := by linarith
      positivity
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef
      (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)
    have hq2 : df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) ^ 2 ≤
        qL d n δ ^ 2 := pow_le_pow_left₀ hP0 hqs 2
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    refine mul_le_mul hq2 ?_ hinner (sq_nonneg _)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsq hτ0n)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hsum := sumY_leV H ht
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  have hW : 0 ≤ Real.sqrt (WbL d n δ) * τ0 := by positivity
  unfold VD tailD
  rw [← hTdef, ← hτ0]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (sq_nonneg _)
  have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yR n δ Kt (π.g s) ((df2CtxAtF d n δ Kt ap).st π s) z ∂(gam d) ≤
      T * (9 * n) := mul_le_mul_of_nonneg_left hsum (by linarith)
  have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (WbL d n δ) * τ0) ≤ n * (Real.sqrt (WbL d n δ) * τ0) :=
    mul_le_mul_of_nonneg_right htn hW
  push_cast at h2 ⊢
  linarith

theorem inv_S_eqV (_H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hI : (df2CtxAtF d n δ Kt ap).StInv π s) :
    (((df2CtxAtF d n δ Kt ap).st π s).A * ((df2CtxAtF d n δ Kt ap).st π s).Aᵀ)⁻¹ =
      ((df2CtxAtF d n δ Kt ap).st π s).P := by
  rw [hI.AA]; exact Matrix.inv_eq_right_inv hI.SP

/-- The increments at `c` are at most `RD` up to `τ`, on G. -/
theorem dq_rangeV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) (hG : (df2CtxAtF d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) {c : Fin d → ℝ}
    (hq : df2Sq ((df2CtxAtF d n δ Kt ap).st π s).P (c - ((df2CtxAtF d n δ Kt ap).st π s).mu) ≤ qL d n δ) :
    |(df2CtxAtF d n δ Kt ap).Y π s * phiH n δ (fun st => c - st.mu) ((df2CtxAtF d n δ Kt ap).st π s) (π.xi s) -
      df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)| ≤ RD d n δ := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_ltV H
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eqV H]; positivity
  set st := (df2CtxAtF d n δ Kt ap).st π s with hstdef
  set b := st.Aᵀ *ᵥ (st.P *ᵥ (c - st.mu)) with hb
  have hbb : b ⬝ᵥ b = df2Sq st.P (c - st.mu) := dir_sq st hI.AA hI.SP _
  have hP0 : 0 ≤ df2Sq st.P (c - st.mu) := sq_nonneg_of_psd hI.pd.posSemidef _
  have hY : |(df2CtxAtF d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hlin : lin st (c - st.mu) (π.xi s) = π.xi s ⬝ᵥ b := by
    rw [lin_eq_dot st (P_symm hI), ← hb]
  have hl2 : lin st (c - st.mu) (π.xi s) ^ 2 ≤ 32 / 9 * d * xq d n δ * qL d n δ := by
    rw [hlin]
    have h1 := abs_dot_le (π.xi s) b
    have h2 : |π.xi s ⬝ᵥ b| ^ 2 ≤ (Real.sqrt (π.xi s ⬝ᵥ π.xi s) * Real.sqrt (b ⬝ᵥ b)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (dot_self_nonneg' _), Real.sq_sqrt (dot_self_nonneg' _), hbb] at h2
    exact h2.trans (mul_le_mul hξ hq hP0 (by have := xq_posV H; positivity))
  have hph : |phiH n δ (fun st => c - st.mu) st (π.xi s)| ≤
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 * (qL d n δ * (32 / 9 * d * xq d n δ + 1)) := by
    unfold phiH
    have hlk : 0 ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 := mul_nonneg hl0.le hk0
    rw [abs_mul, abs_of_nonneg hlk]
    refine mul_le_mul_of_nonneg_left ?_ hlk
    have hsq := sq_nonneg (lin st (c - st.mu) (π.xi s))
    rw [abs_le]; constructor <;> nlinarith
  have hH : |df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) (c - st.mu)| ≤
      (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ := by
    have h := hsi.hess2 (WithLp.toLp 2 st.mu) (c - st.mu)
    rw [inv_S_eqV H hI] at h
    have hK : 0 ≤ (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (2 * d * (df2oPar d n δ).sig2) := by
      have : 0 < 1 - (df2oPar d n δ).lam := by linarith
      positivity
    exact h.trans (mul_le_mul_of_nonneg_left hq hK)
  have hLe : 0 ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := by positivity
  unfold RD
  calc _ ≤ |(df2CtxAtF d n δ Kt ap).Y π s * phiH n δ (fun st => c - st.mu) st (π.xi s)| +
        |df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) (c - st.mu)| := abs_sub _ _
    _ ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) *
          ((df2oPar d n δ).lam * (df2oPar d n δ).k0 * (qL d n δ * (32 / 9 * d * xq d n δ + 1))) +
        (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
          Real.sqrt (2 * d * (df2oPar d n δ).sig2) * qL d n δ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hY hph (abs_nonneg _) hLe) hH
    _ = _ := by ring

/-- `|vᵀ (ŝ''_s - s''_s(μ_s)) v| ≤ KD |v|²` up to `τ`, on G. -/
theorem dq_quadV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) (hG : (df2CtxAtF d n δ Kt ap).EvG π m) {s : ℕ}
    (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) (v : Fin d → ℝ) :
    |v ⬝ᵥ (((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s) *ᵥ v)| ≤ KD d n δ * (v ⬝ᵥ v) := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have he0 : 0 < (df2oPar d n δ).eps := H.rows.pos_eps
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hl0 : 0 < (df2oPar d n δ).lam := H.rows.pos_lam
  have hl1 := lam_ltV H
  have hL : 1 ≤ (df2oPar d n δ).Le := H.one_le_Le
  have hk0 : 0 ≤ (df2oPar d n δ).k0 := by rw [k0_eqV H]; positivity
  have hx := xq_posV H
  set st := (df2CtxAtF d n δ Kt ap).st π s with hstdef
  have hY : |(df2CtxAtF d n δ Kt ap).Y π s| ≤ (df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps) := ybd_G H hG hs
  have hξ : π.xi s ⬝ᵥ π.xi s ≤ 32 / 9 * d * xq d n δ := xibd_G H hG hs
  have hvv := dot_self_nonneg' v
  have hu : (df2CtxAtF d n δ Kt ap).u π s ⬝ᵥ (df2CtxAtF d n δ Kt ap).u π s ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe :=
    (u_norm st.P st.S st.A (π.xi s) _ hde hI.pd.posSemidef hI.AA hI.SP (P_upper H hI)).trans
      (div_le_div_of_nonneg_right hξ hde.le)
  have huv : ((df2CtxAtF d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 ≤ 32 / 9 * d * xq d n δ / (df2oPar d n δ).δe * (v ⬝ᵥ v) := by
    have h1 := abs_dot_le ((df2CtxAtF d n δ Kt ap).u π s) v
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (dot_self_nonneg' _), Real.sq_sqrt hvv] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hu hvv)
  have hPv : df2Sq st.P v ≤ (df2oPar d n δ).δe⁻¹ * (v ⬝ᵥ v) := quad_le_of_psd (P_upper H hI) v
  have hP0 : 0 ≤ df2Sq st.P v := sq_nonneg_of_psd hI.pd.posSemidef v
  have hshh : |df2Sq ((df2CtxAtF d n δ Kt ap).shh π s) v| ≤
      (df2oPar d n δ).lam * (df2oPar d n δ).k0 * ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) *
        ((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v) := by
    change |df2Sq (((df2oPar d n δ).lam * (df2oPar d n δ).k0 * (df2CtxAtF d n δ Kt ap).Y π s) •
      (vecMulVec ((df2CtxAtF d n δ Kt ap).u π s) ((df2CtxAtF d n δ Kt ap).u π s) - st.P)) v| ≤ _
    rw [df2Sq_rank_one, abs_mul, abs_mul, abs_mul, abs_of_pos hl0, abs_of_nonneg hk0]
    have hsq := sq_nonneg ((df2CtxAtF d n δ Kt ap).u π s ⬝ᵥ v)
    have hab : |((df2CtxAtF d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 - df2Sq st.P v| ≤
        ((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v) := by
      rw [abs_le]; constructor <;> nlinarith
    have hlk : 0 ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 := mul_nonneg hl0.le hk0
    calc _ = (df2oPar d n δ).lam * (df2oPar d n δ).k0 * |(df2CtxAtF d n δ Kt ap).Y π s| *
          |((df2CtxAtF d n δ Kt ap).u π s ⬝ᵥ v) ^ 2 - df2Sq st.P v| := by ring
      _ ≤ (df2oPar d n δ).lam * (df2oPar d n δ).k0 * ((df2oPar d n δ).Le / (2 * (df2oPar d n δ).eps)) *
          (((32 / 9 * d * xq d n δ) / (df2oPar d n δ).δe + (df2oPar d n δ).δe⁻¹) * (v ⬝ᵥ v)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hY hlk) hab (abs_nonneg _) (mul_nonneg hlk (by positivity))
      _ = _ := by ring
  have hH : |df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) v| ≤
      (df2oPar d n δ).lam * (8 / (df2oPar d n δ).eps) / (1 - (df2oPar d n δ).lam) *
        Real.sqrt (d / (df2oPar d n δ).δe) * (v ⬝ᵥ v) := hsi.hess1 (WithLp.toLp 2 st.mu) v
  have e1 : v ⬝ᵥ (((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s) *ᵥ v) =
      df2Sq ((df2CtxAtF d n δ Kt ap).shh π s) v - df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) v :=
    df2Sq_sub _ _ v
  rw [e1]
  unfold KD
  calc _ ≤ |df2Sq ((df2CtxAtF d n δ Kt ap).shh π s) v| + |df2Sq ((df2CtxAtF d n δ Kt ap).sHess π s) v| := abs_sub _ _
    _ ≤ _ := add_le_add hshh hH
    _ = _ := by ring

/-- `ŝ''_s - s''_s(μ_s)` is symmetric up to `τ`. -/
theorem dq_symmV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) {s : ℕ} (hs : s ≤ (df2CtxAtF d n δ Kt ap).tau π m) :
    ((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s)ᵀ =
      (df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s := by
  have hI := H.stInv_le_tau s hs
  have hsi := H.si (H.le_tau_lt hs) (H.stOK_of_stInv hI)
  have h1 : ((df2CtxAtF d n δ Kt ap).sHess π s)ᵀ = (df2CtxAtF d n δ Kt ap).sHess π s :=
    hessM_transpose _ hsi.c2 _
  have h2 : ((df2CtxAtF d n δ Kt ap).shh π s)ᵀ = (df2CtxAtF d n δ Kt ap).shh π s := by
    unfold Df2Ctx.shh
    rw [transpose_smul, transpose_sub, transpose_vecMulVec, P_symm hI]
  rw [transpose_sub, h1, h2]

/-- `G_t(y)` and `G_t(c)` differ by at most `n KD δ⁴ 4R` up to `τ`, on G. -/
theorem dq_disc_pathV (H : DetBase (df2CtxAtF d n δ Kt ap) δ π m) (hG : (df2CtxAtF d n δ Kt ap).EvG π m) {t : ℕ}
    (ht : t ≤ (df2CtxAtF d n δ Kt ap).tau π m) {y c : Fin d → ℝ} (hyR : y ⬝ᵥ y ≤ (df2oPar d n δ).R ^ 2)
    (hcR : c ⬝ᵥ c ≤ (df2oPar d n δ).R ^ 2)
    (hyc : Real.sqrt ((y - c) ⬝ᵥ (y - c)) ≤ (df2oPar d n δ).δe ^ 4) :
    |(df2CtxAtF d n δ Kt ap).GG π t y - (df2CtxAtF d n δ Kt ap).GG π t c| ≤
      n * KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) := by
  have hR0 : 0 ≤ (df2oPar d n δ).R := by
    have : (1 : ℝ) ≤ (df2oPar d n δ).R := H.rows.one_le_R
    linarith
  have hK0 : 0 ≤ KD d n δ := KD_nonneg H.hd H.hn H.rows
  have hde : 0 < (df2oPar d n δ).δe := H.rows.pos_de
  have hterm : ∀ s ≤ t, |df2Sq ((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s)
        (y - ((df2CtxAtF d n δ Kt ap).st π s).mu) -
      df2Sq ((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s)
        (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)| ≤
      KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) := by
    intro s hst
    have hs := hst.trans ht
    have hI := H.stInv_le_tau s hs
    set st := (df2CtxAtF d n δ Kt ap).st π s
    rw [sq_sub_sq _ (dq_symmV H hs)]
    have h1 := bilin_le_of_quad _ (dq_symmV H hs) (KD d n δ) (dq_quadV H hG hs) ((y - st.mu) - (c - st.mu))
      ((y - st.mu) + (c - st.mu))
    have e1 : (y - st.mu) - (c - st.mu) = y - c := by abel
    rw [e1] at h1 ⊢
    have hmu := sqrt_dot_le_ofV hR0 (mu_sq_le H hI)
    have hy1 := sqrt_dot_le_ofV hR0 hyR
    have hc1 := sqrt_dot_le_ofV hR0 hcR
    have hy2 := sqrt_dot_sub_leV y st.mu
    have hc2 := sqrt_dot_sub_leV c st.mu
    have h2 : Real.sqrt (((y - st.mu) + (c - st.mu)) ⬝ᵥ ((y - st.mu) + (c - st.mu))) ≤ 4 * (df2oPar d n δ).R :=
      (sqrt_dot_add_le _ _).trans (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul hyc h2 (Real.sqrt_nonneg _) (by positivity)) hK0)
  unfold Df2Ctx.GG
  rw [← Finset.sum_sub_distrib]
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by
    have h1 := H.le_tau_lt ht
    have h2 : m ≤ n := H.hmn
    exact_mod_cast (by omega : t + 1 ≤ n)
  calc _ ≤ ∑ s ∈ Finset.range (t + 1), |df2Sq ((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s)
        (y - ((df2CtxAtF d n δ Kt ap).st π s).mu) -
      df2Sq ((df2CtxAtF d n δ Kt ap).shh π s - (df2CtxAtF d n δ Kt ap).sHess π s)
        (c - ((df2CtxAtF d n δ Kt ap).st π s).mu)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range (t + 1), KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R)) :=
      Finset.sum_le_sum fun s hs => hterm s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    _ = ((t + 1 : ℕ) : ℝ) * (KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ n * (KD d n δ * ((df2oPar d n δ).δe ^ 4 * (4 * (df2oPar d n δ).R))) :=
      mul_le_mul_of_nonneg_right htn (by positivity)
    _ = _ := by ring

end path

end AdversarialBco.Poly.EvSI
