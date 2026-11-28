/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC2b

@[expose] public section

/-!
# Piece C for BL-OW, part C2 (w): the small constants of E16w and GUARD-W at the level

The facts of Unified/EngC2d.lean before E16 for BL-OW at BUD-W: `ν'`, `q° ≥ 0.999` (`c° = 0` on an unweighted round,
`|ξ| ≤ Ξ_w` on a weighted one), `Δ_q ≤ 10^{-3}`, `e^w_Y ≤ y0/1000`, `2^{-p} ≤ η y0/100` (from `u ≤ n` and
`y0 ≥ 10`), `|P°'| ≤ Λ`, and GUARD-W read at the level: P°'s guard W at the floor,
`|w°_μ| ≤ R + η (16 d n L_f/δ_0)^{1/2} = R + 4d (N_0/(L_f u))^{1/2}`, is at most `W° = R + 4d (N_e/L_e)^{1/2}`,
since `u ≥ 1` and `x/ln x` increases on `[e, ∞)` (`w_cap`).
-/

namespace AdversarialBco.UW.EngC

open AdversarialBco AdversarialBco.UW.BudW
open AdversarialBco.Bit.BLP.RC (w0_eq)

/-- GUARD-W at the level: `η (16 d n L_f/δ_0)^{1/2} ≤ 4 d (N_e/L_e)^{1/2}`, `δ_0 = 1/N_0`,
`N_0 = 15 · 2^17 d³ n⁴`. -/
theorem w_cap (r : RegW) (h : r.OK) :
    r.eta * Real.sqrt (16 * r.d * r.n * r.Lf / (1 / (15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4))) ≤
      4 * r.d * Real.sqrt (r.Ne / r.Le) := by
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 := ⟨_, rfl⟩
  rw [← hN0]
  obtain ⟨hd0, hn0, hNe0, hLe0, -, -, -, -⟩ := h.pos
  have hd1 := h.hd
  have hn1 := h.hn
  have hu := h.hu
  have hLf1 := h.hLf1
  have hLf0 : 0 < r.Lf := by linarith
  have hN0ge : 3 ≤ N0 := by
    have a : (1 : ℝ) ≤ r.d ^ 3 := one_le_pow₀ hd1
    have b : (1 : ℝ) ≤ r.n ^ 4 := one_le_pow₀ hn1
    have ab : (1 : ℝ) ≤ r.d ^ 3 * r.n ^ 4 := one_le_mul_of_one_le_of_one_le a b
    rw [hN0]; nlinarith
  have hN0pos : 0 < N0 := by linarith
  have hN0Ne : N0 ≤ r.Ne := by rw [hN0]; exact h.hNe
  have hsn : 0 < Real.sqrt r.n := Real.sqrt_pos.2 hn0
  have hsu : 1 ≤ Real.sqrt r.uu := by
    have h1 := Real.sqrt_le_sqrt hu; rwa [Real.sqrt_one] at h1
  have heta : r.eta ≤ Real.sqrt r.d / (r.Lf * Real.sqrt r.n) := by
    rw [h.heta, Real.sqrt_mul hn0.le]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (mul_pos hLf0 hsn)
    have : Real.sqrt r.n ≤ Real.sqrt r.n * Real.sqrt r.uu := le_mul_of_one_le_right hsn.le hsu
    exact mul_le_mul_of_nonneg_left this hLf0.le
  have hw := w0_eq (Real.sqrt r.d / (r.Lf * Real.sqrt r.n)) r.d r.n r.Lf (1 / N0) N0 hd1 hn1 hLf0 hN0pos rfl rfl
  have hX0 : 0 ≤ Real.sqrt (16 * r.d * r.n * r.Lf / (1 / N0)) := Real.sqrt_nonneg _
  have hcap : N0 / r.Lf ≤ r.Ne / r.Le := by
    have hLf : r.Lf = 36 * Real.log N0 := by rw [hN0]; exact h.hLf
    have hLe : r.Le = 36 * Real.log r.Ne := h.hLe
    have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    have he : Real.exp 1 ≤ N0 := he3.trans hN0ge
    have hmono : Real.log r.Ne / r.Ne ≤ Real.log N0 / N0 :=
      Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hN0Ne)) hN0Ne
    have hlogN0 : 0 < Real.log N0 := Real.log_pos (by linarith)
    have hlogNe : 0 < Real.log r.Ne := Real.log_pos (by linarith)
    rw [div_le_div_iff₀ hNe0 hN0pos] at hmono
    rw [hLf, hLe, div_le_div_iff₀ (mul_pos (by norm_num) hlogN0) (mul_pos (by norm_num) hlogNe)]
    linarith
  calc r.eta * Real.sqrt (16 * r.d * r.n * r.Lf / (1 / N0))
      ≤ Real.sqrt r.d / (r.Lf * Real.sqrt r.n) * Real.sqrt (16 * r.d * r.n * r.Lf / (1 / N0)) :=
        mul_le_mul_of_nonneg_right heta hX0
    _ = 4 * r.d * Real.sqrt (N0 / r.Lf) := hw
    _ ≤ 4 * r.d * Real.sqrt (r.Ne / r.Le) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcap) (by linarith)

end AdversarialBco.UW.EngC

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem nu_relH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |((c.par.nu : ℚ) : ℝ) * (1 - (rW d c.n δ).lam) - 1| ≤ (rW d c.n δ).tp / 16 := by
  rw [H.par]; exact H.enc.nu_rel

/-- `q° ≥ 0.999`: `c° = 0` on an unweighted round of P°, `|c°| ≤ c̄_w` and `|ξ| ≤ Ξ_w` on a weighted one. -/
theorem qq_ge (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    999 / 1000 ≤ (ctxOW K c δ ap).qq (pwOW K c δ ap π) s := by
  have S := H.sett
  rw [H.qq_eq]
  have h1 := S.cc_le
  have hcd := H.R.cbw_dom
  have hcb := H.cbw0
  have hX1 : 0 ≤ (rW d c.n δ).Xw1 := (Xw_nonneg H.R).2
  by_cases hY : (ctxOW K c δ ap).Y (pwOW K c δ ap π) s = 0
  · have h0 : (ctxOW K c δ ap).cc (pwOW K c δ ap π) s = 0 := by rw [S.cc_eq, hY, mul_zero]
    rw [h0]; norm_num
  · have h2 := S.xi_w hY
    have hX := (H.R.Xw_bd).2.2.1
    have hx : π.xi s ⬝ᵥ π.xi s ≤ (rW d c.n δ).Xw1 ^ 2 := by
      rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) (h2.trans hX) 2
    have hx0 : 0 ≤ π.xi s ⬝ᵥ π.xi s := by rw [← oNorm_sq]; positivity
    have hXX : 0 ≤ (rW d c.n δ).Xw1 ^ 2 := sq_nonneg _
    have h4 : |(ctxOW K c δ ap).cc (pwOW K c δ ap π) s * (π.xi s ⬝ᵥ π.xi s - 1)| ≤
        (rW d c.n δ).cbw * (1 + (rW d c.n δ).Xw1 ^ 2) := by
      rw [abs_mul]
      refine mul_le_mul h1 ?_ (abs_nonneg _) hcb
      rw [abs_le]; constructor <;> linarith
    have := (abs_le.1 h4).1
    linarith

theorem Dq_small (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).Dq ≤ 1 / 1000 := by
  have h1 := H.Dcw_small
  have h2 := (H.R.cbw_small).1
  have hexi := H.sett.exi_le_one
  have hcX : 0 ≤ (rW d c.n δ).cbw * (rW d c.n δ).Xw1 := mul_nonneg H.cbw0 (Xw_nonneg H.R).2
  have h4 : (rW d c.n δ).cbw * (rW d c.n δ).Xw1 * (rW d c.n δ).exi ≤ (rW d c.n δ).cbw * (rW d c.n δ).Xw1 :=
    mul_le_of_le_one_right hcX hexi
  unfold RegW.Dq
  linarith

/-- `y0 ≥ 10`, from the regime of the reference. -/
theorem y0_ge10 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 10 ≤ (rW d c.n δ).y0 := by
  have h := H.reg.y0_lo
  have he : 0 < (parW d c.n (refW d c.n δ).u).eps := H.sett.eps_pos
  have h1 : 0 ≤ 18 / (parW d c.n (refW d c.n δ).u).eps := div_nonneg (by norm_num) he.le
  have h2 := Real.sqrt_nonneg (12 * lam0 d c.n)
  show 10 ≤ (refW d c.n δ).y0
  linarith

theorem eY_small (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).eYw ≤ (rW d c.n δ).y0 / 1000 := by
  have hR := H.R
  obtain ⟨-, heY⟩ := hR.eYw_le
  have hy10 := H.y0_ge10
  have htp0 := hR.htp0
  obtain ⟨-, hQLe, -, -, -, -⟩ := hR.Q_bd
  have hL1 := hR.hL1
  have hsL : Real.sqrt (rW d c.n δ).Le ≤ (rW d c.n δ).Le := by
    have h := Real.sqrt_le_sqrt (show (rW d c.n δ).Le ≤ (rW d c.n δ).Le ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hXw := hR.Xw_bd
  have hX1 : (rW d c.n δ).Xw ≤ (rW d c.n δ).d * (rW d c.n δ).Q := hXw.2.2.1.trans hXw.2.2.2.2
  have ht1 := hR.tiny 0 1 (by norm_num) (by norm_num)
  have ht2 := hR.tiny 1 1 (by norm_num) (by norm_num)
  simp only [pow_zero, one_mul, pow_one] at ht1 ht2
  have hc : (1 : ℝ) / 2 ^ 160 ≤ 1 / 10 ^ 6 := by norm_num
  have hA : 119 / 100 * Real.sqrt (rW d c.n δ).Le * (rW d c.n δ).tp ≤ (rW d c.n δ).y0 / 2000 := by
    have h1 : Real.sqrt (rW d c.n δ).Le * (rW d c.n δ).tp ≤ (rW d c.n δ).Q * (rW d c.n δ).tp :=
      mul_le_mul_of_nonneg_right (by linarith) htp0.le
    linarith
  have hB : (rW d c.n δ).y0 * (rW d c.n δ).Xw * (rW d c.n δ).tp ≤ (rW d c.n δ).y0 / 2000 := by
    have h1 : (rW d c.n δ).Xw * (rW d c.n δ).tp ≤ (rW d c.n δ).d * (rW d c.n δ).Q * (rW d c.n δ).tp :=
      mul_le_mul_of_nonneg_right hX1 htp0.le
    have h2 : (rW d c.n δ).Xw * (rW d c.n δ).tp ≤ 1 / 2000 := by linarith
    have hy0 : 0 ≤ (rW d c.n δ).y0 := by linarith
    calc (rW d c.n δ).y0 * (rW d c.n δ).Xw * (rW d c.n δ).tp = (rW d c.n δ).y0 * ((rW d c.n δ).Xw * (rW d c.n δ).tp) := by
          ring
      _ ≤ (rW d c.n δ).y0 * (1 / 2000) := mul_le_mul_of_nonneg_left h2 hy0
      _ = (rW d c.n δ).y0 / 2000 := by ring
  calc (rW d c.n δ).eYw ≤ (119 / 100 * Real.sqrt (rW d c.n δ).Le + (rW d c.n δ).y0 * (rW d c.n δ).Xw) *
        (rW d c.n δ).tp := heY
    _ = 119 / 100 * Real.sqrt (rW d c.n δ).Le * (rW d c.n δ).tp +
        (rW d c.n δ).y0 * (rW d c.n δ).Xw * (rW d c.n δ).tp := by ring
    _ ≤ (rW d c.n δ).y0 / 2000 + (rW d c.n δ).y0 / 2000 := add_le_add hA hB
    _ = (rW d c.n δ).y0 / 1000 := by ring

/-- `2^{-p} ≤ η y0/100`: `η = d^{1/2}/(L_f (n u)^{1/2}) ≥ 1/(L_f n)` since `u ≤ n`, `y0 ≥ 10`, and
`10 L_f n 2^{-p} ≤ Q^{11} 2^{-p} ≤ 1`. -/
theorem tp_eta (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).tp ≤ 1 / 100 * (rW d c.n δ).eta * (rW d c.n δ).y0 := by
  have hR := H.R
  obtain ⟨hd0, hn0, -, -, -, -, htp0, -⟩ := hR.pos
  have hLf := hR.hLf1
  have hLfLe := hR.hLfLe
  obtain ⟨-, hQLe, hQn, -, -, -⟩ := hR.Q_bd
  have hu := hR.hu
  have hnge := hR.hnge
  have hy10 := H.y0_ge10
  have ht := hR.tiny 0 11 (by norm_num) (by norm_num)
  simp only [pow_zero, one_mul] at ht
  have hLf0 : 0 < (rW d c.n δ).Lf := by linarith
  have hun : (rW d c.n δ).uu ≤ (rW d c.n δ).n := by
    have h1 : (1 : ℝ) ≤ 58000 ^ 2 * (rW d c.n δ).d ^ 3 * (rW d c.n δ).Lf ^ 10 := by
      have a : (1 : ℝ) ≤ (rW d c.n δ).d ^ 3 := one_le_pow₀ hR.hd
      have b : (1 : ℝ) ≤ (rW d c.n δ).Lf ^ 10 := one_le_pow₀ (by linarith)
      have ab : (1 : ℝ) ≤ (rW d c.n δ).d ^ 3 * (rW d c.n δ).Lf ^ 10 := one_le_mul_of_one_le_of_one_le a b
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (rW d c.n δ).uu by linarith)
    linarith
  have hsnu : 0 < Real.sqrt ((rW d c.n δ).n * (rW d c.n δ).uu) := Real.sqrt_pos.2 (mul_pos hn0 (by linarith))
  have hs : Real.sqrt ((rW d c.n δ).n * (rW d c.n δ).uu) ≤ (rW d c.n δ).n :=
    calc Real.sqrt ((rW d c.n δ).n * (rW d c.n δ).uu) ≤ Real.sqrt ((rW d c.n δ).n * (rW d c.n δ).n) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hun hn0.le)
      _ = (rW d c.n δ).n := Real.sqrt_mul_self hn0.le
  have hLn : 0 < (rW d c.n δ).Lf * (rW d c.n δ).n := mul_pos hLf0 hn0
  have heta : 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) ≤ (rW d c.n δ).eta := by
    rw [hR.heta]
    have hsd := (hR.sqrt_d_le).1
    rw [div_le_div_iff₀ hLn (mul_pos hLf0 hsnu)]
    have h1 := mul_le_mul_of_nonneg_left hs hLf0.le
    have h2 : (rW d c.n δ).Lf * (rW d c.n δ).n ≤ Real.sqrt (rW d c.n δ).d * ((rW d c.n δ).Lf * (rW d c.n δ).n) :=
      le_mul_of_one_le_left hLn.le hsd
    linarith
  have hA : 10 * (rW d c.n δ).Lf * (rW d c.n δ).n * (rW d c.n δ).tp ≤ 1 := by
    have h1 : 10 * (rW d c.n δ).Lf ≤ (rW d c.n δ).Q := by linarith
    have h2 : (rW d c.n δ).n ≤ (rW d c.n δ).Q ^ 10 := by linarith
    have hQ0 : 0 ≤ (rW d c.n δ).Q := hR.hQ0.le
    calc 10 * (rW d c.n δ).Lf * (rW d c.n δ).n * (rW d c.n δ).tp
        ≤ (rW d c.n δ).Q * (rW d c.n δ).Q ^ 10 * (rW d c.n δ).tp :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 hn0.le hQ0) htp0.le
      _ = (rW d c.n δ).Q ^ 11 * (rW d c.n δ).tp := by ring
      _ ≤ 1 / 2 ^ 160 := ht
      _ ≤ 1 := by norm_num
  have hx0 : 0 ≤ 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) := (one_div_pos.2 hLn).le
  have hx : 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) * ((rW d c.n δ).Lf * (rW d c.n δ).n) = 1 :=
    one_div_mul_cancel hLn.ne'
  have h6 : (rW d c.n δ).tp * ((rW d c.n δ).Lf * (rW d c.n δ).n) ≤ 1 / 10 := by linarith
  have h7 : 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) * ((rW d c.n δ).tp * ((rW d c.n δ).Lf * (rW d c.n δ).n)) =
      (rW d c.n δ).tp := by
    rw [show 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) * ((rW d c.n δ).tp * ((rW d c.n δ).Lf * (rW d c.n δ).n)) =
      (rW d c.n δ).tp * (1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) * ((rW d c.n δ).Lf * (rW d c.n δ).n)) by ring,
      hx, mul_one]
  have h8 := mul_le_mul_of_nonneg_left h6 hx0
  rw [h7] at h8
  have h5 : 1 / ((rW d c.n δ).Lf * (rW d c.n δ).n) * 10 ≤ (rW d c.n δ).eta * (rW d c.n δ).y0 :=
    mul_le_mul heta hy10 (by norm_num) (hR.eta_bd).1.le
  linarith

theorem opN_Pn (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    opN ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Lam := by
  have S := H.sett
  have h := opN_mul_le ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s * (ctxOW K c δ ap).An (pwOW K c δ ap π) s)
    ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s * (ctxOW K c δ ap).An (pwOW K c δ ap π) s)ᵀ
  rw [S.PnAn_sq, opN_transpose] at h
  have h2 := S.opN_PnAn
  have h0 := opN_nonneg ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s * (ctxOW K c δ ap).An (pwOW K c δ ap π) s)
  have : Real.sqrt (rW d c.n δ).Lam * Real.sqrt (rW d c.n δ).Lam = (rW d c.n δ).Lam :=
    Real.mul_self_sqrt S.Lam_pos.le
  have h3 := mul_le_mul h2 h2 h0 (Real.sqrt_nonneg _)
  linarith

/-- GUARD-W at the level: `|w°_μ| ≤ W° = R + 4d (N_e/L_e)^{1/2}` (P°'s guard W at the floor does not act, and
`w_cap`). -/
theorem wmu0_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    oNorm ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) ≤ (rW d c.n δ).W0 := by
  have S := H.sett
  have h := H.det.not_gdW S.hs'
  unfold Df2Ctx.GdW at h
  rw [not_lt] at h
  have hLe : (ctxOW K c δ ap).p.Le = (rW d c.n δ).Lf := parW_Le d c.n _
  have hde : (ctxOW K c δ ap).p.δe =
      1 / (15 * 2 ^ 17 * (rW d c.n δ).d ^ 3 * (rW d c.n δ).n ^ 4) := by
    show 1 / ((n0W d c.n : ℕ) : ℝ) = 1 / (15 * 2 ^ 17 * (d : ℝ) ^ 3 * (c.n : ℝ) ^ 4)
    congr 1
    show (((15 * 2 ^ (17 + 0) * d ^ 3 * c.n ^ 4 : ℕ)) : ℝ) = _
    push_cast; ring
  rw [hLe, hde] at h
  have h' : oNorm ((ctxOW K c δ ap).wmu (pwOW K c δ ap π) s) ≤ (rW d c.n δ).R + (rW d c.n δ).eta *
      Real.sqrt (16 * (rW d c.n δ).d * (rW d c.n δ).n * (rW d c.n δ).Lf /
        (1 / (15 * 2 ^ 17 * (rW d c.n δ).d ^ 3 * (rW d c.n δ).n ^ 4))) := h
  have hw := w_cap (rW d c.n δ) H.R
  unfold RegW.W0
  linarith

end AdversarialBco.UW.Eng.RCHypOW
