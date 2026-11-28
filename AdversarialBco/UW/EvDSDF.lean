/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvEDQ
public import AdversarialBco.Poly.Df2EvSISDF

@[expose] public section

/-!
# Event (d) of Theorem UW

`evSDFPropUW_of : SIFactsUW → RowsUW → EvNeedsUW → EvSDFPropUW`: event (d), S-DF, at T4U on the weighted path fails
with probability at most `δc/7`. The proof is Theorem U's (Poly/Df2EvSISDF.lean) with the changes of events (c) and (e):
the truncated increments of Lemma U at the net points `c` of the unit ball with the direction `φ_H(c)`, the bias of
Lemma SK' (at most `lvBd q` per round, `q = 2 cᵀ P̄_t c`), and the sure ranges of the weighted path in the range
(`round_leE`, `At_quad_leE`). The final inequality `sdf_finalE` is Theorem U's `sdf_final` with the bias `n lvBd q`
carried through the sum.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-- The direction `φ_H(c)` of a constant vector grows at most quadratically on the bound condition. -/
theorem phiHE_const_growth {p : Df2OPar} {M : ℝ} (hM : 0 ≤ M) (v : Fin d → ℝ) {st : Df2St d}
    (hst : EvSI.stB M st) (z : Fin d → ℝ) :
    |phiHE p (fun _ => v) st z| ≤ EvSI.SDF.kPhi p d M v * (1 + ‖z‖) ^ 2 :=
  EvSI.SDF.quad_growth st.P st.A M _ hM hst.2.1 hst.2.2 v z

/-- The arithmetic at the end of event (d): Theorem U's `sdf_final` with the bias `Bs`, `|Bs| ≤ nBd q`. -/
theorem sdf_finalE (Bn Rd Xv lk q qu Au Ac Bs l δ Dq DA nBd : ℝ) (hBn : 0 ≤ Bn) (hlk : 0 ≤ lk) (hq : 0 ≤ q)
    (hAu : 2 * Bn * qu < |Au|) (hA : |Au - Ac| ≤ DA) (hqq : |qu - q| ≤ Dq) (hqu : 4 * δ ≤ qu)
    (hBs : |Bs| ≤ nBd * q) (hmain : 3 * lk * Real.sqrt (Xv * l) + 2 * Rd * l + nBd ≤ Bn)
    (hsmall : Bn * Dq + 2 * δ ^ 2 * l + DA ≤ 4 * δ * Bn) :
    3 * Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) + 2 * (Rd * q + δ ^ 2) * l < |Ac - Bs| := by
  have hsqrt : Real.sqrt (lk ^ 2 * q ^ 2 * Xv * l) = lk * q * Real.sqrt (Xv * l) := by
    rw [show lk ^ 2 * q ^ 2 * Xv * l = (lk * q) ^ 2 * (Xv * l) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg hlk hq)]
  rw [hsqrt]
  have h1 : 3 * (lk * q * Real.sqrt (Xv * l)) + 2 * (Rd * q + δ ^ 2) * l + nBd * q =
      q * (3 * lk * Real.sqrt (Xv * l) + 2 * Rd * l + nBd) + 2 * δ ^ 2 * l := by ring
  have h2 : q * (3 * lk * Real.sqrt (Xv * l) + 2 * Rd * l + nBd) ≤ q * Bn := mul_le_mul_of_nonneg_left hmain hq
  have h3 : q ≤ qu + Dq := by
    have := le_abs_self (q - qu)
    rw [abs_sub_comm] at this
    linarith
  have h4 : q * Bn ≤ (qu + Dq) * Bn := mul_le_mul_of_nonneg_right h3 hBn
  have h5 : 4 * δ * Bn ≤ qu * Bn := mul_le_mul_of_nonneg_right hqu hBn
  have h6 : |Au| - DA ≤ |Ac| := by
    have := abs_sub_abs_le_abs_sub Au Ac
    linarith
  have h7 : |Ac| - |Bs| ≤ |Ac - Bs| := abs_sub_abs_le_abs_sub Ac Bs
  nlinarith

/-! ## On a path -/

section path

variable {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- `|vᵀ ŝ''_s v| ≤ λ κ₀ y0 (b0 + 2) vᵀ P_s v` up to `τ`, under the sure ranges. -/
theorem shh_quad_leE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) (w : Fin d → ℝ) :
    |df2Sq (c.shh (pathW c b0 y0 π) s) w| ≤
      c.p.lam * c.p.k0 * y0 * (b0 + 2) * df2Sq (c.st (pathW c b0 y0 π) s).P w := by
  set πw := pathW c b0 y0 π with hπw
  have hI := H.stInv_le_tau s hs
  have g := EvSI.SDF.shh_quad_generic (c.st πw s).P (c.st πw s).A (c.st πw s).S hI.pd.posSemidef hI.AA hI.SP
    (c.p.lam * c.p.k0 * c.Y πw s) (πw.xi s) w
  rw [EvSI.SDF.shh_quad]
  refine g.trans ?_
  obtain ⟨hY, hYξ⟩ := Y_sure c b0 y0 π s hy0 hI.run
  have hl := H.rows.pos_lam
  have hk := k0_nonnegE H
  have hlk : 0 ≤ c.p.lam * c.p.k0 := mul_nonneg hl.le hk
  have hP0 : 0 ≤ w ⬝ᵥ ((c.st πw s).P *ᵥ w) := sq_nonneg_of_psd hI.pd.posSemidef w
  have key : |c.p.lam * c.p.k0 * c.Y πw s| * (πw.xi s ⬝ᵥ πw.xi s + 1) ≤ c.p.lam * c.p.k0 * y0 * (b0 + 2) := by
    by_cases hY0 : c.Y πw s = 0
    · rw [hY0, mul_zero, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hlk hy0) (by linarith)
    have hξ : πw.xi s ⬝ᵥ πw.xi s ≤ b0 + 1 := hYξ hY0
    rw [abs_mul, abs_of_nonneg hlk]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hY hlk) (by linarith)
      (by linarith [EvSI.dot_self_nonneg' (πw.xi s)]) (mul_nonneg hlk hy0)
  exact mul_le_mul_of_nonneg_right key hP0

theorem lvRd0_nonnegE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ π m) :
    0 ≤ lvRd0 c.p d b0 y0 := by
  have he0 : 0 < c.p.eps := H.rows.pos_eps
  have hl0 : 0 < c.p.lam := H.rows.pos_lam
  have hl1 : 0 < 1 - c.p.lam := by have := lam_ltE H; linarith
  have hk0 := k0_nonnegE H
  have hs : 0 ≤ c.p.sig2 := H.rows.pos_sig2.le
  unfold lvRd0
  positivity

/-- `|vᵀ ŝ''_s v| + |vᵀ s''_s(μ_s) v| ≤ lvRd0 vᵀ P_s v` up to `τ`, under the sure ranges. -/
theorem round_leE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {s : ℕ}
    (hs : s ≤ c.tau (pathW c b0 y0 π) m) (w : Fin d → ℝ) :
    |df2Sq (c.shh (pathW c b0 y0 π) s) w| + |df2Sq (c.sHess (pathW c b0 y0 π) s) w| ≤
      lvRd0 c.p d b0 y0 * df2Sq (c.st (pathW c b0 y0 π) s).P w := by
  have h1 := shh_quad_leE hb0 hy0 H hs w
  have h2 := EvSI.SDF.sHess_quad_le H hs w
  unfold lvRd0
  linarith

/-- `|vᵀ A_t v| ≤ (n lvRd0/δ_e) |v|²` for `t ≤ τ`, under the sure ranges. -/
theorem At_quad_leE {b0 y0 : ℝ} (hb0 : 0 ≤ b0) (hy0 : 0 ≤ y0) (H : DetBase c δ (pathW c b0 y0 π) m) {t : ℕ}
    (ht : t ≤ c.tau (pathW c b0 y0 π) m) (w : Fin d → ℝ) :
    |df2Sq (EvSI.SDF.At c (pathW c b0 y0 π) t) w| ≤ c.n * lvRd0 c.p d b0 y0 / c.p.δe * (w ⬝ᵥ w) := by
  set πw := pathW c b0 y0 π with hπw
  have hR := lvRd0_nonnegE hb0 hy0 H
  have hde := H.rows.pos_de
  have hw := EvSI.dot_self_nonneg' w
  unfold EvSI.SDF.At
  rw [sq_sum]
  have hpt : ∀ u ∈ Finset.range (t + 1), |df2Sq (c.shh πw u - c.sHess πw u) w| ≤
      lvRd0 c.p d b0 y0 * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := by
    intro u hu
    have hut : u ≤ c.tau πw m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)).trans ht
    have hI := H.stInv_le_tau u hut
    rw [sq_sub]
    have h1 := round_leE hb0 hy0 H hut w
    have h2 := EvSI.quad_le_of_psd (EvSI.P_upper H hI) w
    calc |df2Sq (c.shh πw u) w - df2Sq (c.sHess πw u) w| ≤ |df2Sq (c.shh πw u) w| + |df2Sq (c.sHess πw u) w| :=
          abs_sub _ _
      _ ≤ lvRd0 c.p d b0 y0 * df2Sq (c.st πw u).P w := h1
      _ ≤ lvRd0 c.p d b0 y0 * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left h2 hR
  have htn : ((t + 1 : ℕ) : ℝ) ≤ c.n := by
    have := H.le_tau_lt ht; have := H.hmn; exact_mod_cast (by omega : t + 1 ≤ c.n)
  calc |∑ u ∈ Finset.range (t + 1), df2Sq (c.shh πw u - c.sHess πw u) w|
      ≤ ∑ u ∈ Finset.range (t + 1), |df2Sq (c.shh πw u - c.sHess πw u) w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ Finset.range (t + 1), lvRd0 c.p d b0 y0 * (c.p.δe⁻¹ * (w ⬝ᵥ w)) := Finset.sum_le_sum hpt
    _ = ((t + 1 : ℕ) : ℝ) * (lvRd0 c.p d b0 y0 * (c.p.δe⁻¹ * (w ⬝ᵥ w))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ c.n * (lvRd0 c.p d b0 y0 * (c.p.δe⁻¹ * (w ⬝ᵥ w))) := by
        apply mul_le_mul_of_nonneg_right htn; positivity
    _ = c.n * lvRd0 c.p d b0 y0 / c.p.δe * (w ⬝ᵥ w) := by rw [div_eq_mul_inv]; ring

/-- The variance cap of (d): `∑_{s ≤ t} E[(e_s² + pip_s²) φ_H(v)²] ≤ (λ κ₀)² (2 vᵀ P̄_t v)² lvXv` for `t ≤ τ`. -/
theorem vsum_phiHE_le (H : DetBase c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) (v : Fin d → ℝ) :
    ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
        phiHE c.p (fun _ => v) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      (c.p.lam * c.p.k0) ^ 2 * (2 * df2Sq (c.PBar π t) v) ^ 2 * lvXv c.p d c.n := by
  have hx := H.x_ge
  set T := (16 * lvX c.p) ^ 2 with hTdef
  have hT : 1 ≤ T := by rw [hTdef, lvX]; nlinarith
  set q := 2 * df2Sq (c.PBar π t) v with hq
  set τ0 := Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt T / 4)) with hτ0
  have hτ0n : 0 ≤ τ0 := Real.sqrt_nonneg _
  have hstep : ∀ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z *
      phiHE c.p (fun _ => v) (c.st π s) z ^ 2 ∂(EvSI.gam d) ≤
      (c.p.lam * c.p.k0) ^ 2 * (q ^ 2 *
        (T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) + Real.sqrt (lvWb c.p d) * τ0)) := by
    intro s hs
    have hs' : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    have hv := var_HE H (hs'.trans ht) (fun _ => v) T hT
    have hP0 := sq_nonneg_of_psd (H.stInv_le_tau s (hs'.trans ht)).pd.posSemidef v
    have hPq : df2Sq (c.st π s).P v ≤ q := EvSI.SDF.P_quad_le H hs' ht v
    have hP2 : df2Sq (c.st π s).P v ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hP0 hPq 2
    have hY0 : 0 ≤ ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) :=
      integral_nonneg fun z => yRE_nonneg c.p c.Kt (π.g s) _ z
    have hY2 := intY2_leE H (hs'.trans ht)
    have hsq : Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) ≤ Real.sqrt (lvWb c.p d) :=
      Real.sqrt_le_sqrt hY2
    have hinner : 0 ≤ T * ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
        Real.sqrt (∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ^ 2 ∂(EvSI.gam d)) * τ0 := by
      have : 0 ≤ T := by linarith
      positivity
    refine hv.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    refine mul_le_mul hP2 ?_ hinner (sq_nonneg _)
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
  have hX : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) +
      ((t + 1 : ℕ) : ℝ) * (Real.sqrt (lvWb c.p d) * τ0) ≤ lvXv c.p d c.n := by
    unfold lvXv
    rw [← hTdef, ← hτ0]
    have h1 : T * ∑ s ∈ Finset.range (t + 1), ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) ≤
        T * (9 * c.n) := mul_le_mul_of_nonneg_left hsum (by linarith)
    have h2 : ((t + 1 : ℕ) : ℝ) * (Real.sqrt (lvWb c.p d) * τ0) ≤ c.n * (Real.sqrt (lvWb c.p d) * τ0) :=
      mul_le_mul_of_nonneg_right htn hW
    linarith
  calc (c.p.lam * c.p.k0) ^ 2 * (q ^ 2 * (T * ∑ s ∈ Finset.range (t + 1),
        ∫ z, yRE c.p c.Kt (π.g s) (c.st π s) z ∂(EvSI.gam d) + ((t + 1 : ℕ) : ℝ) * (Real.sqrt (lvWb c.p d) * τ0)))
      ≤ (c.p.lam * c.p.k0) ^ 2 * (q ^ 2 * lvXv c.p d c.n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

end path

/-! ## The budget of (d) -/

/-- **Event (d), S-DF, of Theorem UW**: on every instance of setting (E) at T4U with sure ranges, S-DF fails on the
weighted path with probability at most `δc/7`. -/
theorem evSDFPropUW_of (hS : SIFactsUW) (hR : RowsUW) (hN : EvNeedsUW) : EvSDFPropUW := by
  intro d n m ρ hreg hm1 hmn Θ _ V _ Kθ gθ apθ hbody hadm hap hmeas Ω m0 μ hμ 𝒢 θ ψ ξ e hθ hψ hK hE
  have N := (hN d n ρ hreg).needD
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
  have hx14 : 14 ≤ Real.log (1 / p.δe) := by
    have h := rows.cx
    have : 0 ≤ Real.log ((d : ℝ) * n) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) (by exact_mod_cast hn))
    linarith
  have hLx : p.Le = 36 * Real.log (1 / p.δe) := by rw [hfix.Le]; rfl
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
    have : 0 ≤ p.Le := by rw [hLx]; linarith
    linarith
  have hy0 : 10 + 18 / p.eps + 10 * Real.sqrt (p.Le / 3) ≤ ρ.y0 := by
    rw [hLlam, show 36 * lam0 d n / 3 = 12 * lam0 d n by ring]; exact hreg.y0_lo
  have hy00 : 0 ≤ ρ.y0 := by
    have : 0 ≤ 18 / p.eps := div_nonneg (by norm_num) he0.le
    have := Real.sqrt_nonneg (p.Le / 3)
    linarith
  have hdc0 : 0 < ρ.δc := hreg.dc_pos
  have hdc1 : ρ.δc ≤ p.δe := hreg.dc_le
  -- the levels
  have hC0 : 0 ≤ 1 + 2 / p.eps := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) he0.le; linarith
  have hk0 : 0 ≤ p.k0 := by rw [hfix.k0]; positivity
  have hlk : 0 ≤ p.lam * p.k0 := mul_nonneg hl0.le hk0
  have hB0 : 0 ≤ lvBias p d := by unfold lvBias; positivity
  have hBd0 : 0 ≤ lvBd p d := mul_nonneg hB0 (mul_nonneg (by norm_num) hlk)
  have hXv0 : 0 ≤ lvXv p d n := by unfold lvXv; positivity
  have hRd00 : 0 ≤ lvRd0 p d ρ.b0 ρ.y0 := by
    unfold lvRd0
    have h1 : 0 ≤ p.lam * p.k0 * ρ.y0 * (ρ.b0 + 2) := mul_nonneg (mul_nonneg hlk hy00) (by linarith)
    have h2 : 0 ≤ p.lam * (8 / p.eps) / (1 - p.lam) * Real.sqrt (2 * d * p.sig2) :=
      mul_nonneg (div_nonneg (mul_nonneg hl0.le (div_nonneg (by norm_num) he0.le)) hl1'.le) (Real.sqrt_nonneg _)
    linarith
  have hRd0 : 0 ≤ lvRd p d ρ.b0 ρ.y0 := by unfold lvRd; linarith
  -- the net of the unit ball
  obtain ⟨C, hCb, -, hCn, hCc⟩ := existsNet d 1 (p.δe ^ 4) zero_le_one (pow_pos hde0 4)
  -- the state process, the increments and the level `q`
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → Ω → Θ × Df2St d, σ = sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e := ⟨_, rfl⟩
  have hσm : ∀ s < m, Measurable[𝒢 s] (σ s) := fun s hs => by
    rw [hσdef]
    exact measurable_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hmeas 𝒢 hK hθ hψ hE.xi_meas hE.e_meas hs.le
  obtain ⟨X, hXdef⟩ : ∃ X : E d → ℕ → Ω → ℝ, X = fun c s ω => if s < m then
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) (σ s ω, ξ s ω) else 0 := ⟨_, rfl⟩
  have hXlt : ∀ c s, s < m → X c s = fun ω =>
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) (σ s ω, ξ s ω) := by
    intro c s hs; rw [hXdef]; funext ω; simp only [hs, ↓reduceIte]
  have hXpt : ∀ c s, s < m → ∀ ω, X c s ω =
      obsW ρ.b0 ρ.y0 (ξ s ω) (EtrE p Kθ gθ M s (σ s ω, ξ s ω) + PtrE p Kθ M (σ s ω, ξ s ω) * e s ω) *
        DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) (σ s ω, ξ s ω) :=
    fun c s hs ω => by rw [hXlt c s hs]
  have hφm : ∀ c : E d, Measurable fun x : Df2St d × (Fin d → ℝ) =>
      phiHE p (fun _ => WithLp.ofLp c) x.1 x.2 :=
    fun c => measurable_phiHE p _ measurable_const
  obtain ⟨qf, hqfdef⟩ : ∃ qf : E d → ℕ → Ω → ℝ, qf = fun c t ω =>
      2 * df2Sq ((ctxE d n ρ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))).PBar
        (pathW (ctxE d n ρ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω))) ρ.b0 ρ.y0
          ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩) t) (WithLp.ofLp c) := ⟨_, rfl⟩
  -- Lemma U
  have hgr : ∀ (c : E d) (s : ℕ), s < m →
      (∀ x, |EtrE p Kθ gθ M s x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + EvSI.SDF.kPhi p d M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |PtrE p Kθ M x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + EvSI.SDF.kPhi p d M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) ∧
      (∀ x, |DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) x| ≤
        ((1 + 2 / p.eps) * (1 + Real.sqrt d) + EvSI.SDF.kPhi p d M (WithLp.ofLp c)) * (1 + ‖x.2‖) ^ 2) :=
    fun c s hs => trunc_growth (φ := phiHE p (fun _ => WithLp.ofLp c)) hp hbody (fun q => hadm q s hs)
      (EvSI.SDF.kPhi_nonneg p d M _) (fun st hst z => phiHE_const_growth hM0 _ hst z)
  have hU := lemmaU_setW (d := d) μ 𝒢 C m n hmn σ ξ e hσm hE.xi_meas hE.xi_law hE.xi_indep hE.e_meas hE.e_int
    hE.e_mean hE.e_exp (EtrE p Kθ gθ M) (fun _ => PtrE p Kθ M)
    (fun c _ => DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)))
    (fun s hs => measurable_EtrE hmeas.1 (hmeas.2.1 s hs)) (fun _ _ => measurable_PtrE hmeas.1)
    (fun c _ _ => measurable_DtrE hmeas.1 (hφm c))
    (fun c => (1 + 2 / p.eps) * (1 + Real.sqrt d) + EvSI.SDF.kPhi p d M (WithLp.ofLp c)) 2
    (fun c => add_nonneg (mul_nonneg hC0 (by positivity)) (EvSI.SDF.kPhi_nonneg p d M _))
    (fun c s hs => (hgr c s hs).1) (fun c s hs => (hgr c s hs).2.1) (fun c s hs => (hgr c s hs).2.2)
    (obsW ρ.b0 ρ.y0) (measurable_obsW_uncurry ρ.b0 ρ.y0) (fun x y => (obsW_sure hy00 ρ.b0 x y).2.1)
    (p.δe ^ 2)⁻¹ (ρ.δc / 7) (by positivity) (by positivity) (by linarith)
    (fun c t ω => (p.lam * p.k0) ^ 2 * qf c t ω ^ 2 * lvXv p d n)
    (fun c t ω => lvRd p d ρ.b0 ρ.y0 * qf c t ω + p.δe ^ 2) X (fun c s => by subst hXdef; rfl)
  -- the bias of each round, outside a null set (Lemma SK')
  have hbias : ∀ᵐ ω ∂μ, ∀ c ∈ C, ∀ s ∈ Finset.range m,
      |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) *
          DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) (σ s ω, z) ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun _ => WithLp.ofLp c)) (σ s ω, z) ^ 4
          ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := by
    refine (Filter.eventually_all_finset C).2 fun c _ => (Filter.eventually_all_finset _).2 fun s hs => ?_
    have hs' : s < m := Finset.mem_range.1 hs
    rw [hXlt c s hs']
    exact biasE hd hp hbody (fun q => hadm q s hs') hmeas.1 (hmeas.2.1 s hs') hb0 hy0 (hφm c)
      (EvSI.SDF.kPhi_nonneg p d M _) (fun st hst z => phiHE_const_growth hM0 _ hst z)
      (𝒢 s) μ (𝒢.le s) (σ s) (ξ s) (e s) (hσm s hs') ((hE.xi_meas s).mono (𝒢.le _) le_rfl)
      ((hE.e_meas s).mono (𝒢.le _) le_rfl) (hE.xi_law s) (hE.xi_indep s) (hE.e_int s) (hE.e_mean s) (hE.e_exp s)
  refine le_trans (measure_le_of_ae_memE ?_) (hU.trans (le_of_eq (by congr 1; ring)))
  filter_upwards [hbias] with ω hb hbad
  -- the epoch at `ω`
  set cx := ctxE d n ρ (Kθ (θ 0 ω)) (fun s => apθ (ψ s ω)) with hcx
  set π0 : Df2Path d := ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩ with hπ0
  set πw := pathW cx ρ.b0 ρ.y0 π0 with hπw
  have H : DetBase cx (1 / 2) πw m := detBaseE hS hR hreg hm1 hmn hbody hadm hap ψ hK ξ e ω
  unfold EvSDFW at hbad
  push Not at hbad
  obtain ⟨t, ht, v, hv⟩ := hbad
  have htm : t < m := lt_of_le_of_lt ht H.tau_lt
  rw [EvSI.SDF.Pn_sub_PBar H ht, sq_smul, abs_mul, abs_of_pos H.kap_pos] at hv
  have hkap : p.kap = 1 / 4 := H.kap
  have heta : 0 < p.eta := rows.pos_eta
  set Bn := bnW p d n ρ.u with hBn
  have hv' : 4 * Bn * df2Sq (cx.PBar πw t) v < |df2Sq (EvSI.SDF.At cx πw t) v| := by
    have h2 : 4 * p.kap * p.eta * Bn * df2Sq (cx.PBar πw t) v <
        p.eta * p.kap * |df2Sq (EvSI.SDF.At cx πw t) v| := hv
    rw [hkap] at h2
    have h1 : p.eta * (4 * Bn * df2Sq (cx.PBar πw t) v) < p.eta * |df2Sq (EvSI.SDF.At cx πw t) v| := by
      linarith
    exact lt_of_mul_lt_mul_left h1 heta.le
  -- the unit direction
  have hvv : v ⬝ᵥ v ≠ 0 := by
    intro h0
    rw [EvSI.dot_self_eq_zero h0] at hv'
    simp [df2Sq] at hv'
  set r := Real.sqrt (v ⬝ᵥ v) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (lt_of_le_of_ne (EvSI.dot_self_nonneg' v) (Ne.symm hvv))
  set u := r⁻¹ • v with hu
  have huu : u ⬝ᵥ u = 1 := by
    rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      ← Real.sq_sqrt (EvSI.dot_self_nonneg' v), ← hr, inv_pow, inv_mul_cancel₀ (by positivity)]
  have hAu : 4 * Bn * df2Sq (cx.PBar πw t) u < |df2Sq (EvSI.SDF.At cx πw t) u| := by
    rw [hu, sq_smul_arg, sq_smul_arg, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have : 0 < r⁻¹ ^ 2 := by positivity
    nlinarith
  -- the net point
  have huB : (WithLp.toLp 2 u : E d) ∈ Metric.closedBall (0 : E d) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, EvSI.norm_toLp, huu, Real.sqrt_one]
  obtain ⟨c, hcC, hdc⟩ := hCn _ huB
  set vc := WithLp.ofLp c with hvc
  have hcv : c = WithLp.toLp 2 vc := (WithLp.toLp_ofLp 2 c).symm
  have hvc1 : vc ⬝ᵥ vc ≤ 1 := by
    have h := hCb hcC
    rw [Metric.mem_closedBall, dist_zero_right, hcv, EvSI.norm_toLp] at h
    have h0 := EvSI.dot_self_nonneg' vc
    rw [← Real.sqrt_one] at h
    exact (Real.sqrt_le_sqrt_iff zero_le_one).1 h
  have hdu : Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) ≤ p.δe ^ 4 := by
    rw [hcv, dist_eq_norm, ← WithLp.toLp_sub, EvSI.norm_toLp] at hdc
    exact hdc
  have hsu : Real.sqrt ((u + vc) ⬝ᵥ (u + vc)) ≤ 2 := by
    have h := (oNorm_tri u vc 0 ∅ fun _ => 0).1
    have h1 : Real.sqrt (u ⬝ᵥ u) = 1 := by rw [huu, Real.sqrt_one]
    have h2 : Real.sqrt (vc ⬝ᵥ vc) ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hvc1
    linarith
  have hdu0 := Real.sqrt_nonneg ((u - vc) ⬝ᵥ (u - vc))
  have hsu0 := Real.sqrt_nonneg ((u + vc) ⬝ᵥ (u + vc))
  -- the level `q` at the net point
  set q := qf c t ω with hq
  have hqe : q = 2 * df2Sq (cx.PBar πw t) vc := by subst hqfdef; rfl
  have hPq : 0 ≤ df2Sq (cx.PBar πw t) vc := sq_nonneg_of_psd (H.PBar_psd ht) vc
  have hq0 : 0 ≤ q := by rw [hqe]; linarith
  have hqδ : q * p.δe ≤ 1 := by
    have h' : 2 * df2Sq (cx.PBar πw t) vc ≤ p.δe⁻¹ * (vc ⬝ᵥ vc) := EvSI.SDF.PBar_quad_upper H ht vc
    rw [hqe]
    calc 2 * df2Sq (cx.PBar πw t) vc * p.δe ≤ p.δe⁻¹ * (vc ⬝ᵥ vc) * p.δe :=
          mul_le_mul_of_nonneg_right h' hde0.le
      _ = vc ⬝ᵥ vc := by field_simp
      _ ≤ 1 := hvc1
  have hC1 : (1 : ℝ) ≤ C.card := by
    have h : 1 ≤ C.card := Finset.card_pos.2 ⟨c, hcC⟩
    exact_mod_cast h
  obtain ⟨hlg0, hmain, hsmall⟩ := N (C.card : ℝ) q hC1 hCc hq0 hqδ
  have hBn0 : 0 ≤ Bn := by
    have h1 : 0 ≤ 3 * (p.lam * p.k0) * Real.sqrt (lvXv p d n * lvLogD p d n ρ.b0 ρ.y0 ρ.δc C.card q) :=
      mul_nonneg (mul_nonneg (by norm_num) hlk) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ 2 * lvRd p d ρ.b0 ρ.y0 * lvLogD p d n ρ.b0 ρ.y0 ρ.δc C.card q :=
      mul_nonneg (mul_nonneg (by norm_num) hRd0) hlg0
    have h3 : 0 ≤ (n : ℝ) * lvBd p d := mul_nonneg (Nat.cast_nonneg n) hBd0
    linarith
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
  -- the increment at `c` is `cᵀ ŝ''_s c`
  have hXv : ∀ s ≤ t, X c s ω = cx.Y πw s * phiHE cx.p (fun _ => vc) (cx.st πw s) (π0.xi s) := by
    intro s hs
    have hI := H.stInv_le_tau s (hs.trans ht)
    have hg := hgood s hs
    rw [hXpt c s (lt_of_le_of_lt hs htm) ω, EtrE_of (x := (σ s ω, ξ s ω)) hg, PtrE_of (x := (σ s ω, ξ s ω)) hg,
      DtrE_of (x := (σ s ω, ξ s ω)) hg, hσdef, ← Y_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s _ hI.run]
    rfl
  have hXq : ∀ s ≤ t, X c s ω = df2Sq (cx.shh πw s) vc := by
    intro s hs
    rw [hXv s hs]
    exact (shh_sqE cx πw s (fun _ => vc)).symm
  -- the conditional mean is `cᵀ s''_s(μ_s) c` up to the bias
  have hbiasω : ∀ s ≤ t, |μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc| ≤ lvBd p d * q := by
    intro s hs
    have hs' := hs.trans ht
    have hsm : s < m := lt_of_le_of_lt hs htm
    have hg := hgood s hs
    have h1 : |μ[X c s | 𝒢 s] ω - ∫ z, EtrE p Kθ gθ M s (σ s ω, z) *
          DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ∂(EvSI.gam d)| ≤
        lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ^ 4
          ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) :=
      hb c hcC s (Finset.mem_range.2 hsm)
    have hm := mean_HE H hs' (fun _ => vc)
    have hmean : ∫ z, EtrE p Kθ gθ M s (σ s ω, z) * DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z)
        ∂(EvSI.gam d) = df2Sq (cx.sHess πw s) vc := by
      rw [← hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      rw [EtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
        fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
      rfl
    have hD4 : (∫ z, DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ^ 4 ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) ≤
        7 * (p.lam * p.k0) * df2Sq (cx.st πw s).P vc := by
      have e1 : ∫ z, DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ^ 4 ∂(EvSI.gam d) =
          ∫ z, phiHE cx.p (fun _ => vc) (cx.st πw s) z ^ 4 ∂(EvSI.gam d) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        beta_reduce
        rw [DtrE_of (x := (σ s ω, z)) hg, hσω s]
        rfl
      rw [e1]
      exact phiHE_d4E H hs' (fun _ => vc)
    have hPs : df2Sq (cx.st πw s).P vc ≤ q := by rw [hqe]; exact EvSI.SDF.P_quad_le H hs ht vc
    have hlk7 : 0 ≤ lvBias p d * (7 * (p.lam * p.k0)) := hBd0
    rw [hmean] at h1
    calc _ ≤ lvBias p d * (∫ z, DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ^ 4
            ∂(EvSI.gam d)) ^ (1 / 4 : ℝ) := h1
      _ ≤ lvBias p d * (7 * (p.lam * p.k0) * df2Sq (cx.st πw s).P vc) := mul_le_mul_of_nonneg_left hD4 hB0
      _ = lvBias p d * (7 * (p.lam * p.k0)) * df2Sq (cx.st πw s).P vc := by ring
      _ ≤ lvBias p d * (7 * (p.lam * p.k0)) * q := mul_le_mul_of_nonneg_left hPs hlk7
      _ = lvBd p d * q := rfl
  -- the range of a round
  have hrange : ∀ s ≤ t, |X c s ω - μ[X c s | 𝒢 s] ω| ≤ lvRd p d ρ.b0 ρ.y0 * q + p.δe ^ 2 := by
    intro s hs
    rw [hXq s hs]
    have h1 : |df2Sq (cx.shh πw s) vc| + |df2Sq (cx.sHess πw s) vc| ≤
        lvRd0 p d ρ.b0 ρ.y0 * df2Sq (cx.st πw s).P vc := round_leE hb0' hy00 H (hs.trans ht) vc
    have h2 := hbiasω s hs
    have hPs : df2Sq (cx.st πw s).P vc ≤ q := by rw [hqe]; exact EvSI.SDF.P_quad_le H hs ht vc
    have h3 : lvRd0 p d ρ.b0 ρ.y0 * df2Sq (cx.st πw s).P vc ≤ lvRd0 p d ρ.b0 ρ.y0 * q :=
      mul_le_mul_of_nonneg_left hPs hRd00
    have h4 := abs_sub_le (df2Sq (cx.shh πw s) vc) (df2Sq (cx.sHess πw s) vc) (μ[X c s | 𝒢 s] ω)
    have h5 := abs_sub (df2Sq (cx.shh πw s) vc) (df2Sq (cx.sHess πw s) vc)
    have h6 : |df2Sq (cx.sHess πw s) vc - μ[X c s | 𝒢 s] ω| =
        |μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc| := abs_sub_comm _ _
    have h7 : lvRd p d ρ.b0 ρ.y0 * q = lvRd0 p d ρ.b0 ρ.y0 * q + lvBd p d * q := by unfold lvRd; ring
    have h8 := sq_nonneg p.δe
    linarith
  -- the variance
  have hvar : ∑ s ∈ Finset.range (t + 1), ∫ z, (EtrE p Kθ gθ M s (σ s ω, z) ^ 2 + PtrE p Kθ M (σ s ω, z) ^ 2) *
      DtrE p Kθ M (phiHE p (fun _ => vc)) (σ s ω, z) ^ 2 ∂(EvSI.gam d) ≤ (p.lam * p.k0) ^ 2 * q ^ 2 * lvXv p d n := by
    rw [hqe]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun s hs => ?_)) (vsum_phiHE_le H ht vc)
    have hg := hgood s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [EtrE_of (x := (σ s ω, z)) hg, PtrE_of (x := (σ s ω, z)) hg, DtrE_of (x := (σ s ω, z)) hg, hσdef,
      fFE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z, fPE_sigE p n ρ.b0 ρ.y0 Kθ gθ apθ θ ψ ξ e hK ω s z]
    rfl
  -- the deviation
  have hsumX : ∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω) =
      df2Sq (EvSI.SDF.At cx πw t) vc -
      ∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc) := by
    unfold EvSI.SDF.At
    rw [sq_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hXq s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)), sq_sub]
    ring
  have htn : ((t + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : t + 1 ≤ n)
  have hbsum : |∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc)| ≤
      n * lvBd p d * q := by
    calc _ ≤ ∑ s ∈ Finset.range (t + 1), |μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ Finset.range (t + 1), lvBd p d * q :=
          Finset.sum_le_sum fun s hs => hbiasω s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))
      _ = ((t + 1 : ℕ) : ℝ) * (lvBd p d * q) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * (lvBd p d * q) := mul_le_mul_of_nonneg_right htn (mul_nonneg hBd0 hq0)
      _ = n * lvBd p d * q := by ring
  -- the discretization
  have hKA : 0 ≤ (n : ℝ) * lvRd0 p d ρ.b0 ρ.y0 / p.δe :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) hRd00) hde0.le
  have hA : |df2Sq (EvSI.SDF.At cx πw t) u - df2Sq (EvSI.SDF.At cx πw t) vc| ≤
      2 * n * lvRd0 p d ρ.b0 ρ.y0 * p.δe ^ 3 := by
    have h := EvSI.SDF.quad_sub_le (EvSI.SDF.At cx πw t) (EvSI.SDF.At_symm H ht)
      ((n : ℝ) * lvRd0 p d ρ.b0 ρ.y0 / p.δe) (fun w => At_quad_leE hb0' hy00 H ht w) u vc
    calc _ ≤ (n : ℝ) * lvRd0 p d ρ.b0 ρ.y0 / p.δe *
          (Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) * Real.sqrt ((u + vc) ⬝ᵥ (u + vc))) := h
      _ ≤ (n : ℝ) * lvRd0 p d ρ.b0 ρ.y0 / p.δe * (p.δe ^ 4 * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hdu hsu hsu0 (by positivity)) hKA
      _ = 2 * n * lvRd0 p d ρ.b0 ρ.y0 * p.δe ^ 3 := by
          rw [div_mul_eq_mul_div, div_eq_iff hde0.ne']; ring
  have hqq : |2 * df2Sq (cx.PBar πw t) u - q| ≤ 2 * p.δe ^ 3 := by
    have hKq : ∀ w, |df2Sq (cx.PBar πw t) w| ≤ p.δe⁻¹ / 2 * (w ⬝ᵥ w) := fun w => by
      rw [abs_of_nonneg (sq_nonneg_of_psd (H.PBar_psd ht) w)]
      have h : 2 * df2Sq (cx.PBar πw t) w ≤ p.δe⁻¹ * (w ⬝ᵥ w) := EvSI.SDF.PBar_quad_upper H ht w
      linarith
    have h := EvSI.SDF.quad_sub_le (cx.PBar πw t) (EvSI.SDF.PBar_symm H ht) (p.δe⁻¹ / 2) hKq u vc
    rw [hqe, ← mul_sub, abs_mul, abs_two]
    have hK0 : 0 ≤ p.δe⁻¹ / 2 := by positivity
    calc 2 * |df2Sq (cx.PBar πw t) u - df2Sq (cx.PBar πw t) vc|
        ≤ 2 * (p.δe⁻¹ / 2 * (Real.sqrt ((u - vc) ⬝ᵥ (u - vc)) * Real.sqrt ((u + vc) ⬝ᵥ (u + vc)))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 2 * (p.δe⁻¹ / 2 * (p.δe ^ 4 * 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul hdu hsu hsu0 (by positivity)) hK0)
            (by norm_num)
      _ = 2 * p.δe ^ 3 := by field_simp
  have hqu : 4 * p.δe ≤ 2 * df2Sq (cx.PBar πw t) u := by
    have h : 2 * p.δe * (u ⬝ᵥ u) ≤ df2Sq (cx.PBar πw t) u := EvSI.SDF.PBar_quad_lower H ht u
    rw [huu] at h
    linarith
  have hAu' : 2 * Bn * (2 * df2Sq (cx.PBar πw t) u) < |df2Sq (EvSI.SDF.At cx πw t) u| := by linarith [hAu]
  have hfin := sdf_finalE Bn (lvRd p d ρ.b0 ρ.y0) (lvXv p d n) (p.lam * p.k0) q (2 * df2Sq (cx.PBar πw t) u)
    (df2Sq (EvSI.SDF.At cx πw t) u) (df2Sq (EvSI.SDF.At cx πw t) vc)
    (∑ s ∈ Finset.range (t + 1), (μ[X c s | 𝒢 s] ω - df2Sq (cx.sHess πw s) vc))
    (lvLogD p d n ρ.b0 ρ.y0 ρ.δc C.card q) p.δe (2 * p.δe ^ 3) (2 * n * lvRd0 p d ρ.b0 ρ.y0 * p.δe ^ 3)
    (n * lvBd p d) hBn0 hlk hq0 hAu' hA hqq hqu hbsum hmain hsmall
  have key : 3 * Real.sqrt ((p.lam * p.k0) ^ 2 * q ^ 2 * lvXv p d n * lvLogD p d n ρ.b0 ρ.y0 ρ.δc C.card q) +
      2 * (lvRd p d ρ.b0 ρ.y0 * q + p.δe ^ 2) * lvLogD p d n ρ.b0 ρ.y0 ρ.δc C.card q <
      |∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω)| := by
    rw [hsumX]; exact hfin
  refine ⟨c, hcC, t, htm, ?_, ?_, hvar, hrange, key⟩
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hXv0
  · show 1 ≤ (p.δe ^ 2)⁻¹ * (lvRd p d ρ.b0 ρ.y0 * q + p.δe ^ 2)
    rw [mul_add, inv_mul_cancel₀ (by positivity)]
    have : 0 ≤ (p.δe ^ 2)⁻¹ * (lvRd p d ρ.b0 ρ.y0 * q) := mul_nonneg (by positivity) (mul_nonneg hRd0 hq0)
    linarith

end AdversarialBco.UW
