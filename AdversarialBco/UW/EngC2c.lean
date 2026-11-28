/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC2b

@[expose] public section

/-!
# Piece C for BL-OW, part C2 (c): E13, Lemma SEL and P°'s test call

Unified/EngC2c.lean for BL-OW at BUD-W: BL-OW's test statistic `Xi'` against P°'s `Xi°` on the weighted path on
`B_R` (E13), Lemma SEL at BL-OW's test point, and P°'s test call under the advice `advCW`. The caps are read at the
level: P°'s radius is at least `r_min` at the level `δ_e ≤ δ_0`, BL-OW's accuracy of the
test call `r'²/(8 d N_e)` is at most `(δ_0/d) r_s²/8` since `1/δ_0 ≤ N_e`, and P°'s Lipschitz constant `4R/δ_0²` is at
most the level's `Lip_F = 4R/δ_e²`.
-/

namespace AdversarialBco.UW.EngC

/-- `aT_arith` with `1/δ ≤ N` in place of `N = 1/δ`. -/
theorem aT_arith_le (x r Ne de dd : ℝ) (hx : 0 ≤ x) (hxr : x ≤ r) (hNe : 1 / de ≤ Ne) (hde : 0 < de)
    (hd : 0 < dd) : 2 * (x ^ 2 / (Ne * dd * 8)) ≤ de / dd * r ^ 2 / 4 := by
  have h := Bit.BLP.RC.aT_arith x r (1 / de) de dd hx hxr rfl hde hd
  have h0 : 0 < 1 / de * dd * 8 := by positivity
  have h1 : 1 / de * dd * 8 ≤ Ne * dd * 8 := by
    have := mul_le_mul_of_nonneg_right hNe hd.le
    linarith
  have h2 : x ^ 2 / (Ne * dd * 8) ≤ x ^ 2 / (1 / de * dd * 8) :=
    div_le_div_of_nonneg_left (sq_nonneg x) h0 h1
  linarith

end AdversarialBco.UW.EngC

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.EngC (callTO fireO wmuO callMO regO xiBO fireO_iff obj_T xiB_obj)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.Bit.BLP (refTest selT muOf)
open AdversarialBco.Bit.Cpl (apAdv advOK advPick)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem eHat_eq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : ((c.par.eHat : ℚ) : ℝ) = (rW d c.n δ).eh := by
  rw [H.par]; rfl

theorem eta_err (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(c.par.eta : ℝ) - (rW d c.n δ).eta| ≤ (rW d c.n δ).tp / 16 * (rW d c.n δ).eta := by
  have hη : 0 < (rW d c.n δ).eta := H.det.rows.pos_eta
  have h : |((c.par.eta : ℚ) : ℝ) / (rW d c.n δ).eta - 1| ≤ (rW d c.n δ).tp / 16 := by
    rw [H.par]; exact H.enc.eta_rel
  have e : (c.par.eta : ℝ) - (rW d c.n δ).eta = (rW d c.n δ).eta * ((c.par.eta : ℝ) / (rW d c.n δ).eta - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hη]
  nlinarith [abs_nonneg ((c.par.eta : ℝ) / (rW d c.n δ).eta - 1)]

/-- E13: `|Xi' - Xi°| ≤ e_X` on `B_R`. -/
theorem xi_E13 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ (rW d c.n δ).R) :
    |xiBO c (rvHW orc c δ st ξ' ζ' ε f) y - (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s y| ≤ (rW d c.n δ).eX := by
  have S := H.sett
  have hη : 0 < (rW d c.n δ).eta := H.det.rows.pos_eta
  have htp := H.tp_small
  have htp0 := H.tp0
  have h1 := xi_err (rW d c.n δ).eta (c.par.eta : ℝ) (rW d c.n δ).tp
    ((ctxOW K c δ ap).ln (pwOW K c δ ap π) s) ((rvHW orc c δ st ξ' ζ' ε f).l : ℝ) (rW d c.n δ).R (rW d c.n δ).Gb
    ((s + 1) * (rW d c.n δ).el) ((s + 1) * (rW d c.n δ).eg) ((ctxOW K c δ ap).Gn (pwOW K c δ ap π) s)
    (cV (rvHW orc c δ st ξ' ζ' ε f).G) y hη.le H.eta_err htp0 htp H.R0 hy S.ln_le S.Gn_le O.errl O.errG
  have h2 := H.phi_err_n O hy
  have hs : (s : ℝ) + 1 ≤ c.n := by exact_mod_cast H.hs
  have hel : 0 ≤ (rW d c.n δ).el := by
    have := O.errl
    have := abs_nonneg (((rvHW orc c δ st ξ' ζ' ε f).l : ℝ) - (ctxOW K c δ ap).ln (pwOW K c δ ap π) s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push_neg at hc; nlinarith
  have heg : 0 ≤ (rW d c.n δ).eg := by
    have := O.errG
    have := oNorm_nonneg (cV (rvHW orc c δ st ξ' ζ' ε f).G - (ctxOW K c δ ap).Gn (pwOW K c δ ap π) s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push_neg at hc; nlinarith
  have hR := H.R0
  have e : xiBO c (rvHW orc c δ st ξ' ζ' ε f) y - (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s y =
      ((c.par.eta : ℝ) * (((rvHW orc c δ st ξ' ζ' ε f).l : ℝ) - cV (rvHW orc c δ st ξ' ζ' ε f).G ⬝ᵥ y) -
        (rW d c.n δ).eta * ((ctxOW K c δ ap).ln (pwOW K c δ ap π) s -
          (ctxOW K c δ ap).Gn (pwOW K c δ ap π) s ⬝ᵥ y)) -
      2 * (df2Phi (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ)
        (cV (rvHW orc c δ st ξ' ζ' ε f).b) (rvHW orc c δ st ξ' ζ' ε f).k y -
        (ctxOW K c δ ap).PhiN (pwOW K c δ ap π) s y) := by
    unfold xiBO Df2Ctx.Xi
    change (c.par.eta : ℝ) * _ - 2 * _ - ((rW d c.n δ).eta * _ - 2 * _) = _
    ring
  rw [e]
  have hA : (s + 1) * (rW d c.n δ).el ≤ c.n * (rW d c.n δ).el := mul_le_mul_of_nonneg_right hs hel
  have hB : (rW d c.n δ).R * ((s + 1) * (rW d c.n δ).eg) ≤ (rW d c.n δ).R * (c.n * (rW d c.n δ).eg) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs heg) hR
  have hAB : (rW d c.n δ).eta * (101 / 100) * ((s + 1) * (rW d c.n δ).el +
        (rW d c.n δ).R * ((s + 1) * (rW d c.n δ).eg)) ≤
      (rW d c.n δ).eta * (101 / 100) * (c.n * (rW d c.n δ).el + (rW d c.n δ).R * c.n * (rW d c.n δ).eg) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  have := abs_sub ((c.par.eta : ℝ) * (((rvHW orc c δ st ξ' ζ' ε f).l : ℝ) -
    cV (rvHW orc c δ st ξ' ζ' ε f).G ⬝ᵥ y) - (rW d c.n δ).eta * ((ctxOW K c δ ap).ln (pwOW K c δ ap π) s -
      (ctxOW K c δ ap).Gn (pwOW K c δ ap π) s ⬝ᵥ y))
    (2 * (df2Phi (cM (rvHW orc c δ st ξ' ζ' ε f).B * (cM (rvHW orc c δ st ξ' ζ' ε f).B)ᵀ)
      (cV (rvHW orc c δ st ξ' ζ' ε f).b) (rvHW orc c δ st ξ' ζ' ε f).k y -
        (ctxOW K c δ ap).PhiN (pwOW K c δ ap π) s y))
  rw [abs_mul, abs_two] at this
  unfold RegW.eX
  change _ ≤ (rW d c.n δ).eta * (101 / 100) * ((c.n : ℝ) * (rW d c.n δ).el +
      (rW d c.n δ).R * (c.n : ℝ) * (rW d c.n δ).eg) +
    (rW d c.n δ).eta * (rW d c.n δ).tp / 16 * (21 / 10) * (rW d c.n δ).R * (rW d c.n δ).Gb +
      2 * (rW d c.n δ).ePhi
  linarith

/-- P°'s radius of round `s`: `1 - ε` at the first round, `s_b (1 - ε)` after (at the floor `δ_0`). -/
theorem r_cases (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (st.first = true ∧ ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r = 1 - (rW d c.n δ).eps) ∨
      (st.first = false ∧
        ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r = (poW d c.n δ).sb * (1 - (rW d c.n δ).eps)) := by
  have hinv := H.sett.inv
  have hfst := H.track.first
  by_cases hf : st.first = true
  · have hs0 : s = 0 := hinv.first.1 (hfst ▸ hf)
    subst hs0
    exact Or.inl ⟨hf, rfl⟩
  · have hf' : ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).first = false := by rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctxOW K c δ ap).tau (pwOW K c δ ap π) (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨-, -, -, -, -, -, hrs⟩ := prev_roundW H.det hlt
    exact Or.inr ⟨by simpa using hf, hrs⟩

/-- `r_min ≤ s_b (1 - ε)` with `r_min` at the level and `s_b` at the floor. -/
theorem sb_props' (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    0 < (poW d c.n δ).sb ∧ (rW d c.n δ).rmin ≤ (poW d c.n δ).sb * (1 - (rW d c.n δ).eps) ∧
      (poW d c.n δ).sb ≤ 1 := by
  have e := H.det.sb
  change (poW d c.n δ).sb = (poW d c.n δ).δe ^ 2 / ((poW d c.n δ).R * ((poW d c.n δ).R + 1)) at e
  have hde := H.sett.de_pos
  have hde1 : (poW d c.n δ).δe < 1 := H.det.rows.de_lt
  have hR : 1 ≤ (rW d c.n δ).R := H.R_ge
  have eR : (poW d c.n δ).R = (rW d c.n δ).R := rfl
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have hL0 := H.deL_pos
  have hL := H.deL_le
  rw [e, eR]
  have hX : 0 < (rW d c.n δ).R * ((rW d c.n δ).R + 1) := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · unfold RegW.rmin
    have h1 : (rW d c.n δ).de ^ 2 ≤ (poW d c.n δ).δe ^ 2 := pow_le_pow_left₀ hL0.le hL 2
    have h2 : (rW d c.n δ).de ^ 2 * ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) ≤
        (poW d c.n δ).δe ^ 2 * ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) := mul_le_mul_of_nonneg_right h1 hX.le
    have h3 : 0 ≤ (poW d c.n δ).δe ^ 2 * ((rW d c.n δ).R * ((rW d c.n δ).R + 1)) * (1 - 2 * (rW d c.n δ).eps) :=
      mul_nonneg (by positivity) (by linarith)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hX]
    nlinarith
  · rw [div_le_one hX]; nlinarith

/-- `r_min ≤ r_s ≤ 1` and BL-OW's accuracy of the test call is at most `(δ_0/d) r_s²/8`. -/
theorem r_props (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (r : RV d) :
    (rW d c.n δ).rmin ≤ ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ∧
      ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ≤ 1 ∧
      2 * ((callTO c st r).e : ℝ) ≤
        (ctxOW K c δ ap).p.δe / d * ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 / 4 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hsb0, hsbm, hsb1⟩ := H.sb_props'
  have hde := H.sett.de_pos
  have hR : 1 ≤ (rW d c.n δ).R := H.R_ge
  have hd : (0 : ℝ) < d := by exact_mod_cast H.hd
  have hNe : 1 / (poW d c.n δ).δe ≤ ((c.par.Ne : ℕ) : ℝ) := by
    rw [show ((c.par.Ne : ℕ) : ℝ) = (rW d c.n δ).Ne by rw [H.par]; exact H.enc.Ne_eq]
    exact NW.inv_de_le_Ne d c.n δ H.hd H.hn
  have hrmin : (rW d c.n δ).rmin ≤ 1 / 2 := by
    have hL0 := H.deL_pos
    have hL1 := H.deL_le_one
    unfold RegW.rmin
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases H.r_cases with ⟨hf, hr⟩ | ⟨hf, hr⟩
  · rw [hr]
    refine ⟨by linarith, by linarith, ?_⟩
    have e : ((callTO c st r).e : ℝ) = (1 - (c.par.eps : ℝ)) ^ 2 / (((c.par.Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTO; rw [ite_eq_left hf]; simp only [callO]; push_cast; rfl
    rw [e]
    exact aT_arith_le _ _ _ _ _ (by linarith) (by linarith) hNe hde hd
  · rw [hr]
    refine ⟨hsbm, ?_, ?_⟩
    · have : 0 ≤ (poW d c.n δ).sb * (rW d c.n δ).eps := by positivity
      nlinarith
    have hf' : ¬ st.first = true := by simp [hf]
    have e : ((callTO c st r).e : ℝ) =
        ((c.par.sb : ℝ) * (1 - (c.par.eps : ℝ))) ^ 2 / (((c.par.Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTO; rw [ite_eq_right hf']; simp only [callO, rB]; push_cast; rfl
    rw [e]
    have hsb' : (0 : ℝ) < c.par.sb := by exact_mod_cast H.par_pos.1
    have hsbl : ((c.par.sb : ℚ) : ℝ) ≤ (poW d c.n δ).sb := H.sb_le0
    have hx0 : (0 : ℝ) ≤ (c.par.sb : ℝ) * (1 - (c.par.eps : ℝ)) := mul_nonneg hsb'.le (by linarith)
    refine aT_arith_le _ _ _ _ _ hx0 ?_ hNe hde hd
    have h1 : (c.par.sb : ℝ) * (1 - (c.par.eps : ℝ)) ≤ (poW d c.n δ).sb * (1 - (c.par.eps : ℝ)) :=
      mul_le_mul_of_nonneg_right hsbl (by linarith)
    have h2 : (poW d c.n δ).sb * (1 - (c.par.eps : ℝ)) ≤ (poW d c.n δ).sb * (1 - (rW d c.n δ).eps) :=
      mul_le_mul_of_nonneg_left (by linarith) hsb0.le
    exact h1.trans h2

theorem callT_e_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (r : RV d) :
    (0 : ℚ) < (callTO c st r).e := by
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have : 0 < 1 - c.par.eps := by linarith
  unfold callTO; split
  · show 0 < (1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8); positivity
  · show 0 < (c.par.sb * (1 - c.par.eps)) ^ 2 / (c.par.Ne * d * 8); positivity

/-- P°'s Lipschitz constant of `Xi°` at the floor is at most the level's `Lip_F`. -/
theorem lip_cap (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    4 * (ctxOW K c δ ap).p.R / (ctxOW K c δ ap).p.δe ^ 2 ≤ (rW d c.n δ).LipF := by
  have h := H.grad_cap
  unfold RegW.LipF
  change 4 * (poW d c.n δ).R / (poW d c.n δ).δe ^ 2 ≤ _
  rw [mul_div_assoc, mul_div_assoc]
  linarith

/-- E15, Lemma SEL at BL-OW's test point `p'`: P°'s point `v₁ = selV(p', β)` is in `R⁻_s`, within `1` of the
largest statistic there, has statistic at most `-θ ρ` exactly when BL-OW fires, and is `p'` when BL-OW does not
fire. -/
theorem sel (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s) :
    ∃ p', apO orc c (callTO c st (rvHW orc c δ st ξ' ζ' ε f)) = some p' ∧
      selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p') (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))
        ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s ∧
      (∀ y ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s, (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s y ≤
        (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s (selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
          (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))) + 1) ∧
      ((ctxOW K c δ ap).Xi (pwOW K c δ ap π) s (selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
          (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))) ≤
          -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho) ↔
        fireO c (rvHW orc c δ st ξ' ζ' ε f) p') ∧
      (¬ fireO c (rvHW orc c δ st ξ' ζ' ε f) p' →
        selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
          (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hpreg, hpmin⟩ := H.testCall O
  refine ⟨p', hp', ?_⟩
  obtain ⟨hgA, -, hgC⟩ := H.gapT (rvHW orc c δ st ξ' ζ' ε f)
  have hRmR : ∀ y ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s, oNorm y ≤ (ctxOW K c δ ap).p.R := fun y hy => by
    have h := (H.det.Rm_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctxOW K c δ ap).p.R := h
    rwa [sub_zero] at h'
  have hpRm : cV p' ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s := hgC hpreg
  have hpR := hRmR _ hpRm
  obtain ⟨hrmin, hr1, haT⟩ := H.r_props (rvHW orc c δ st ξ' ζ' ε f)
  have hgood := H.det.good s hs
  have hθ : (ctxOW K c δ ap).p.theta = 1 := H.det.theta
  obtain ⟨hρ1, hρ2⟩ := H.rho_enc
  have eρ : (ctxOW K c δ ap).p.rho = (rW d c.n δ).rho := rfl
  have heX := H.R.eX_le_eh
  have hwr := H.wr0
  have hsel := H.R.sel_le
  have hde : 0 < (ctxOW K c δ ap).p.δe := H.sett.de_pos
  have hde1 : (ctxOW K c δ ap).p.δe < 1 := H.det.rows.de_lt
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hL0 := H.deL_pos
  have hLd : (rW d c.n δ).de ≤ (ctxOW K c δ ap).p.δe := H.deL_le
  have hh0 : 0 ≤ (rW d c.n δ).h := (H.R.h_bd).1
  have hR0 := H.R0
  have heX0 : 0 ≤ (rW d c.n δ).eX := (H.R.eX_bd).1
  have haT0 : (0 : ℝ) ≤ ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) := by
    exact_mod_cast (H.callT_e_pos _).le
  have hLip0 : 0 ≤ (rW d c.n δ).LipF := by unfold RegW.LipF; positivity
  have hLip := H.lip_cap
  have hrmin0 : 0 ≤ (rW d c.n δ).rmin := by unfold RegW.rmin; positivity
  -- (H1)
  have hH1 : ∀ y ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s,
      (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s y ≤ (ctxOW K c δ ap).Xi (pwOW K c δ ap π) s (cV p') +
        (2 * ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) + 2 * (rW d c.n δ).eX +
          (rW d c.n δ).LipF * (rW d c.n δ).h) := by
    intro y hy
    obtain ⟨y', hy'Q, hyy'⟩ := hgA y hy
    have hy'R := hRmR y' (hgC hy'Q)
    have h1 := xi_lipW H.det hs y hy'R
    have h2 := abs_le.1 (H.xi_E13 O hy'R)
    have h3 := abs_le.1 (H.xi_E13 O hpR)
    have h4 := hpmin y' hy'Q
    have h5 := xiB_obj c st (rvHW orc c δ st ξ' ζ' ε f) y'
    have h6 := xiB_obj c st (rvHW orc c δ st ξ' ζ' ε f) (cV p')
    have h7 : 4 * (ctxOW K c δ ap).p.R / (ctxOW K c δ ap).p.δe ^ 2 * oNorm (y - y') ≤
        (rW d c.n δ).LipF * (rW d c.n δ).h :=
      mul_le_mul hLip hyy' (oNorm_nonneg _) hLip0
    linarith
  -- (H3) and the size of the margin
  have hH3 : (2 * ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) + 2 * (rW d c.n δ).eX +
      (rW d c.n δ).LipF * (rW d c.n δ).h) + (2 * (rW d c.n δ).eh + (rW d c.n δ).wr) ≤
      (ctxOW K c δ ap).p.δe / d * ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 := by
    have h1 : (rW d c.n δ).rmin ^ 2 ≤ ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 :=
      pow_le_pow_left₀ hrmin0 hrmin 2
    have hdd : (rW d c.n δ).de / d ≤ (ctxOW K c δ ap).p.δe / d :=
      div_le_div_of_nonneg_right hLd (by linarith)
    have h2 : (rW d c.n δ).de / d * (rW d c.n δ).rmin ^ 2 ≤
        (ctxOW K c δ ap).p.δe / d * ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 :=
      mul_le_mul hdd h1 (by positivity) (by positivity)
    have e1 : (rW d c.n δ).selR = 3 / 4 * ((rW d c.n δ).de / d * (rW d c.n δ).rmin ^ 2) := by
      unfold RegW.selR; change 3 / 4 * (rW d c.n δ).de / (d : ℝ) * _ = _; ring
    unfold RegW.sel at hsel
    rw [e1] at hsel
    linarith
  have hmarg : (ctxOW K c δ ap).p.δe / d * ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 ≤ 1 := by
    have h1 : ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 ≤ 1 := by
      have := hgood.2.2; nlinarith
    have h2 : (ctxOW K c δ ap).p.δe / d ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h3 : 0 ≤ ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r ^ 2 := sq_nonneg _
    nlinarith
  have hLh : 0 ≤ (rW d c.n δ).LipF * (rW d c.n δ).h := mul_nonneg hLip0 hh0
  have heh0 : 0 ≤ (rW d c.n δ).eh := (H.R.pos).2.2.2.2.2.2.2.le
  have hspec := selT_spec H.hd
    (refTest (ctxOW K c δ ap).p ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) ((pwOW K c δ ap π).xi s)
      ((ctxOW K c δ ap).Y (pwOW K c δ ap π) s)).1
    (refTest (ctxOW K c δ ap).p ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) ((pwOW K c δ ap π).xi s)
      ((ctxOW K c δ ap).Y (pwOW K c δ ap π) s)).2.1
    (refTest (ctxOW K c δ ap).p ((ctxOW K c δ ap).st (pwOW K c δ ap π) s) ((pwOW K c δ ap π).xi s)
      ((ctxOW K c δ ap).Y (pwOW K c δ ap π) s)).2.2
    (-((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho)) ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).ctr
    ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).r (cV p')
    (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p')) ((ctxOW K c δ ap).Rm (pwOW K c δ ap π) s)
    ((ctxOW K c δ ap).p.δe / d)
    (2 * ((callTO c st (rvHW orc c δ st ξ' ζ' ε f)).e : ℝ) + 2 * (rW d c.n δ).eX +
      (rW d c.n δ).LipF * (rW d c.n δ).h) (2 * (rW d c.n δ).eh + (rW d c.n δ).wr) (H.det.Rm_props hs).1
    hgood.2.1 hgood.2.2
    (fun v => by
      rw [refTest_P]
      have h1 := Pn_lowerW H.det hs v
      have h2 : 0 ≤ v ⬝ᵥ v := by rw [← oNorm_sq]; positivity
      have h3 : (ctxOW K c δ ap).p.δe / d ≤ (ctxOW K c δ ap).p.δe := div_le_self hde.le hd1
      nlinarith)
    hpRm
    (fun y hy => by rw [refTest_F, refTest_F]; exact hH1 y hy)
    (fun hf => by
      rw [refTest_F]
      have hnf : ¬ fireO c (rvHW orc c δ st ξ' ζ' ε f) p' := by simpa using hf
      rw [fireO_iff] at hnf
      rw [H.eHat_eq] at hnf
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    (fun hf => by
      rw [refTest_F]
      have hfq : fireO c (rvHW orc c δ st ξ' ζ' ε f) p' := by simpa using hf
      rw [fireO_iff] at hfq
      rw [H.eHat_eq] at hfq
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    hH3 (by linarith) (by linarith)
  obtain ⟨hv1Q, hv1max, hv1iff, hv1eq⟩ := hspec
  refine ⟨hv1Q, fun y hy => ?_, ?_, fun hnf => hv1eq (by simpa using hnf)⟩
  · have := hv1max y hy
    rw [refTest_F, refTest_F] at this
    linarith
  · rw [refTest_F] at hv1iff
    rw [hv1iff, decide_eq_true_iff]

theorem Le2 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 2 ≤ (ctxOW K c δ ap).p.Le := by
  have := H.R.hLf1
  change 2 ≤ (poW d c.n δ).Le
  rw [show (poW d c.n δ).Le = (rW d c.n δ).Lf from parW_Le d c.n _]
  linarith

theorem Rm_norm (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s) : oNorm y ≤ (ctxOW K c δ ap).p.R := by
  have h := (H.det.Rm_props H.sett.hs').2.2 hy
  have h' : oNorm (y - 0) ≤ (ctxOW K c δ ap).p.R := h
  rwa [sub_zero] at h'

/-- P°'s test call under the advice returns `v₁ = selV(p', β)` (the checked routine accepts it at `e_T = 1`); the
advice reads P°'s observation `Y°_s = obsW(ξ_s, Ỹ_s)` through the weight. -/
theorem tcall_eq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (O : C1OutW d c.n δ c.par st ξ' (rvHW orc c δ st ξ' ζ' ε f) (ctxOW K c δ ap) (pwOW K c δ ap π) s)
    (hap : ap s = apAdv (advCW K orc c δ ap π s st ξ' ζ' Z ε f)) :
    ∃ p', apO orc c (callTO c st (rvHW orc c δ st ξ' ζ' ε f)) = some p' ∧
      (ctxOW K c δ ap).tcall (pwOW K c δ ap π) s = some (selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
        (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))) ∧
      selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p') (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))
        ∈ (ctxOW K c δ ap).Rm (pwOW K c δ ap π) s ∧
      ((ctxOW K c δ ap).Xi (pwOW K c δ ap π) s (selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
          (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))) ≤
          -((ctxOW K c δ ap).p.theta * (ctxOW K c δ ap).p.rho) ↔
        fireO c (rvHW orc c δ st ξ' ζ' ε f) p') ∧
      (¬ fireO c (rvHW orc c δ st ξ' ζ' ε f) p' →
        selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
          (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hv1Q, hv1max, hv1iff, hv1eq⟩ := H.sel O
  refine ⟨p', hp', ?_, hv1Q, hv1iff, hv1eq⟩
  have htq := testOW_eq (b0OW d c.n δ) (y0OW d c.n δ) orc c st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt hp'
  have hY : obsW ((b0OW d c.n δ : ℚ) : ℝ) ((y0OW d c.n δ : ℚ) : ℝ) (π.xi s) (YcO orc c st ξ' Z ε f) =
      (ctxOW K c δ ap).Y (pwOW K c δ ap π) s := H.Y.symm
  have hv : (advCW K orc c δ ap π s st ξ' ζ' Z ε f).1 =
      selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
        (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p')) := by
    unfold advCW advQOW
    rw [htq]
    dsimp only
    rw [hY]
    rfl
  have heT : (ctxOW K c δ ap).eT = 1 := eT_oneW H.det H.Le2
  have hadv : advOK ((ctxOW K c δ ap).Rm (pwOW K c δ ap π) s) (ctxOW K c δ ap).p.R
      ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s) ((ctxOW K c δ ap).zz (pwOW K c δ ap π) s) (ctxOW K c δ ap).eT
      (selV (ctxOW K c δ ap) (pwOW K c δ ap π) s (cV p')
        (decide (fireO c (rvHW orc c δ st ξ' ζ' ε f) p'))) := by
    refine ⟨hv1Q, H.Rm_norm hv1Q, fun q hq => ?_⟩
    have h1 := hv1max _ hq
    rw [xi_ellW H.det hs, xi_ellW H.det hs] at h1
    rw [heT]; linarith
  have hpick : advPick (advCW K orc c δ ap π s st ξ' ζ' Z ε f) (ctxOW K c δ ap).eT =
      (advCW K orc c δ ap π s st ξ' ζ' Z ε f).1 := by
    unfold advPick; rw [heT]; exact ite_eq_left (by norm_num)
  unfold Df2Ctx.tcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick, hv]
  exact ite_eq_left hadv

end AdversarialBco.UW.Eng.RCHypOW
