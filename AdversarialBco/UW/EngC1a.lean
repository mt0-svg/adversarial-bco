/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngPlay
public import AdversarialBco.Unified.EngC1a

@[expose] public section

/-!
# Piece C for BL-OW, part C1 (a): the observation and the factor

Unified/EngC1a.lean for BL-OW at BUD-W: BL-OW's values of R5 to R9 (`rvOW`, the `let`s of `stepOW`), E2w (the
weighted observation), Lemma WR, E3w (the factor) with E16w's `Δ_q` and the guard R7, against P°'s update of round
`s` on the weighted path. Against Theorem U:

* E2w (`eYw`): `Y' = rnd_p(φ(|ξ'|²) clip(Y'_0, y0))` and `Y° = φ(|ξ|²) clip(Ỹ, y0)`; the map is `y0`-Lipschitz in
  `|ξ|²` and `1`-Lipschitz in the reading (`obsW_lip`), and it vanishes when both draws are past `b0 + 1`, so
  `|Y' - Y°| ≤ 2^{-p-1} + y0 e_ξ (2 (b0 + 1)^{1/2} + e_ξ) + e_Y` (`obsW_diff`);
* Lemma WR (`wr`): on a weighted round (`Y' ≠ 0` or `Y° ≠ 0`) `|ξ| ≤ Ξ_w` and `|ξ'| ≤ Ξ_{w1}`; on the other rounds
  `c' = c° = 0`;
* E3w, E16w and R7 read `Ξ_{w1}`, `c̄_w`, `Δ^w_c` on the weighted rounds; on the unweighted ones both factors are the
  identity up to BL's root of `1`.
-/

namespace AdversarialBco.UW.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## BL-OW's values, line by line -/

section rv

variable (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)

theorem rvOW_Y : (rvOW b0 y0 orc c st ξ ζ obs).Y = ywQ c.par.p b0 y0 ξ (rvO orc c st ξ ζ obs).Y := rfl
theorem rvOW_c : (rvOW b0 y0 orc c st ξ ζ obs).c = c.par.kapc * (rvOW b0 y0 orc c st ξ ζ obs).Y := rfl
theorem rvOW_a : (rvOW b0 y0 orc c st ξ ζ obs).a = 1 - (rvOW b0 y0 orc c st ξ ζ obs).c := rfl
theorem rvOW_q : (rvOW b0 y0 orc c st ξ ζ obs).q =
    (rvOW b0 y0 orc c st ξ ζ obs).a + (rvOW b0 y0 orc c st ξ ζ obs).c * (ξ ⬝ᵥ ξ) := rfl
theorem rvOW_s2 : (rvOW b0 y0 orc c st ξ ζ obs).s2 = rnd c.par.p ((rvOW b0 y0 orc c st ξ ζ obs).c /
    ((rvOW b0 y0 orc c st ξ ζ obs).s3 * (rvOW b0 y0 orc c st ξ ζ obs).rq *
      ((rvOW b0 y0 orc c st ξ ζ obs).s3 + (rvOW b0 y0 orc c st ξ ζ obs).rq))) := rfl
theorem rvOW_s4 : (rvOW b0 y0 orc c st ξ ζ obs).s4 = rnd c.par.p ((rvOW b0 y0 orc c st ξ ζ obs).c /
    ((rvOW b0 y0 orc c st ξ ζ obs).s3 + (rvOW b0 y0 orc c st ξ ζ obs).rq)) := rfl
theorem rvOW_G : (rvOW b0 y0 orc c st ξ ζ obs).G = st.G + (rvOW b0 y0 orc c st ξ ζ obs).g := rfl

end rv

/-- BL-OW's values of round `s` in the setting of `RCHypOW`. -/
noncomputable abbrev rvHW (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (δ : ℚ) (st : St d) (ξ' : Fin d → ℚ)
    (ζ' : ℚ) (ε : ℝ) (f : E d → ℝ) : RV d :=
  rvOW (b0OW d c.n δ) (y0OW d c.n δ) orc c st ξ' ζ' (obsO orc c st ξ' f ε)

theorem rnd_zero (p : ℕ) : rnd p 0 = 0 := by
  unfold Bit.BLP.rnd
  have : ⌊(0 : ℚ) * 2 ^ p + 1 / 2⌋ = 0 := by
    rw [zero_mul, zero_add, Int.floor_eq_zero_iff]; norm_num
  rw [this]; simp

/-- The weighted reading of R5w in `ℝ`. -/
theorem ywQ_cast (b0 y0 : ℚ) (ξ : Fin d → ℚ) (Y : ℚ) :
    ((min 1 (max 0 (b0 + 1 - ξ ⬝ᵥ ξ)) * max (-y0) (min y0 Y) : ℚ) : ℝ) =
      obsW (b0 : ℝ) (y0 : ℝ) (cV ξ) (Y : ℝ) := by
  unfold obsW wgt clipW
  push_cast
  rw [cV_dot]

/-- R5w vanishes when `|ξ'|² ≥ b0 + 1`. -/
theorem ywQ_zero (p : ℕ) (b0 y0 : ℚ) (ξ : Fin d → ℚ) (Y : ℚ) (h : b0 + 1 ≤ ξ ⬝ᵥ ξ) : ywQ p b0 y0 ξ Y = 0 := by
  unfold ywQ
  rw [max_eq_left (by linarith), min_eq_right zero_le_one, zero_mul, rnd_zero]

/-- **E2w, the map** (Lemma E2w): `|φ(|ξ'|²) clip(Y') - φ(|ξ|²) clip(Y)| ≤ y0 e (2 (b0 + 1)^{1/2} + e) + |Y' - Y|`
when `|ξ' - ξ| ≤ e`. -/
theorem obsW_diff {y0 : ℝ} (hy0 : 0 ≤ y0) {b0 : ℝ} (hb0 : 0 ≤ b0 + 1) (ξ ξ' : Fin d → ℝ) (Y Y' e : ℝ)
    (he : oNorm (ξ' - ξ) ≤ e) :
    |obsW b0 y0 ξ' Y' - obsW b0 y0 ξ Y| ≤ y0 * (e * (2 * Real.sqrt (b0 + 1) + e)) + |Y' - Y| := by
  have he0 : 0 ≤ e := (oNorm_nonneg _).trans he
  have hs0 := Real.sqrt_nonneg (b0 + 1)
  have hR : 0 ≤ y0 * (e * (2 * Real.sqrt (b0 + 1) + e)) := by positivity
  by_cases hb : b0 + 1 ≤ ξ' ⬝ᵥ ξ' ∧ b0 + 1 ≤ ξ ⬝ᵥ ξ
  · rw [(obsW_sure hy0 b0 ξ' Y').2.2.1 hb.1, (obsW_sure hy0 b0 ξ Y).2.2.1 hb.2, sub_zero, abs_zero]
    exact add_nonneg hR (abs_nonneg _)
  · have hl := obsW_lip hy0 b0 ξ ξ' Y Y'
    have hsum : oNorm ξ' + oNorm ξ ≤ 2 * Real.sqrt (b0 + 1) + e := by
      have t1 := oNorm_add_le ξ (ξ' - ξ)
      rw [add_sub_cancel] at t1
      have t2 := oNorm_add_le ξ' (ξ - ξ')
      rw [add_sub_cancel, oNorm_sub_comm] at t2
      rcases not_and_or.1 hb with h | h
      · have : oNorm ξ' ≤ Real.sqrt (b0 + 1) := by
          unfold oNorm; exact Real.sqrt_le_sqrt (le_of_lt (not_le.1 h))
        linarith
      · have : oNorm ξ ≤ Real.sqrt (b0 + 1) := by
          unfold oNorm; exact Real.sqrt_le_sqrt (le_of_lt (not_le.1 h))
        linarith
    have hd := dot_sq_diff ξ' ξ
    have h2 : |ξ' ⬝ᵥ ξ' - ξ ⬝ᵥ ξ| ≤ e * (2 * Real.sqrt (b0 + 1) + e) := by
      refine hd.trans ?_
      rw [mul_comm e]
      exact mul_le_mul hsum he (oNorm_nonneg _) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left h2 hy0
    linarith

/-! ## The constants of E3w to E11w -/

theorem Xw_nonneg {r : RegW} (h : r.OK) : 0 ≤ r.Xw ∧ 0 ≤ r.Xw1 := by
  obtain ⟨-, h2, h3, -⟩ := h.Xw_bd
  constructor <;> linarith

/-- The constant `e^w_N` of E3w bounds the error of the factor on a weighted round. -/
theorem eN_geW {r : RegW} (h : r.OK) :
    (r.tp + r.Dcw) + (51 / 100 * r.tp + r.Dcw + r.cbw * r.Dq) * r.Xw1 ^ 2 + r.cbw * (2 * r.Xw1) * r.exi ≤ r.eN := by
  have hcd := h.cbw_dom
  have hcb := (h.cbw_le).1
  have hDc : 0 ≤ r.Dcw := (h.Dcw_le).1
  have htp := h.htp0.le
  have hx : 0 ≤ r.Xw1 := (Xw_nonneg h).2
  have hexi : 0 ≤ r.exi := (h.ezt_exi).2.2.1
  have hX2 : 0 ≤ r.Xw1 ^ 2 := sq_nonneg _
  have hcX : r.cbw * r.Xw1 ^ 2 ≤ 1 / 10 ^ 33 := by nlinarith
  unfold RegW.eN RegW.Dq
  have a1 : r.cbw * (r.Dcw * (1 + r.Xw1 ^ 2) + 202 / 100 * r.cbw * r.Xw1 * r.exi) * r.Xw1 ^ 2 ≤
      1 / 10 ^ 33 * (r.Dcw * (1 + r.Xw1 ^ 2)) + 1 / 10 ^ 33 * (202 / 100 * r.cbw * r.Xw1 * r.exi) := by
    have : r.cbw * (r.Dcw * (1 + r.Xw1 ^ 2) + 202 / 100 * r.cbw * r.Xw1 * r.exi) * r.Xw1 ^ 2 =
        (r.cbw * r.Xw1 ^ 2) * (r.Dcw * (1 + r.Xw1 ^ 2) + 202 / 100 * r.cbw * r.Xw1 * r.exi) := by ring
    rw [this, ← mul_add]
    exact mul_le_mul_of_nonneg_right hcX (by positivity)
  nlinarith [mul_nonneg hDc hX2, mul_nonneg (mul_nonneg hcb hx) hexi, mul_nonneg htp hX2]

/-- The step of TRACK in numbers: `h + (1 + h)|A0||N' - N||Ai| + |ρ||Ai| ≤ hTr (s + 1)`. -/
theorem track_numW {r : RegW} (s : ℕ) (h a1 a2 n1 q : ℝ) (hh0 : 0 ≤ h) (hh : h ≤ r.hTr s) (ha1 : 0 ≤ a1)
    (ha1' : a1 ≤ Real.sqrt r.Lam) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ Real.sqrt r.Lam) (hn1 : 0 ≤ n1)
    (hn1' : n1 ≤ r.eN) (hq : 0 ≤ q) (hq' : q ≤ r.nu) (hL : 0 ≤ r.Lam) :
    h + (1 + h) * a1 * n1 * a2 + q * a2 ≤ r.hTr (s + 1) := by
  have hsq : Real.sqrt r.Lam * Real.sqrt r.Lam = r.Lam := Real.mul_self_sqrt hL
  have heN : 0 ≤ r.eN := hn1.trans hn1'
  have hnu : 0 ≤ r.nu := hq.trans hq'
  have hs0 := Real.sqrt_nonneg r.Lam
  have t1 : a1 * n1 * a2 ≤ r.Lam * r.eN := by
    calc a1 * n1 * a2 ≤ Real.sqrt r.Lam * r.eN * Real.sqrt r.Lam :=
          mul_le_mul (mul_le_mul ha1' hn1' hn1 hs0) ha2' ha2 (by positivity)
      _ = r.Lam * r.eN := by
        rw [show Real.sqrt r.Lam * r.eN * Real.sqrt r.Lam = (Real.sqrt r.Lam * Real.sqrt r.Lam) * r.eN by ring, hsq]
  have t2 : q * a2 ≤ Real.sqrt r.Lam * r.nu := by
    rw [mul_comm (Real.sqrt _)]; exact mul_le_mul hq' ha2' ha2 hnu
  have hT0 : 0 ≤ r.hTr s := hh0.trans hh
  have step := hTr_step r.ha (r.Lam * r.eN) (Real.sqrt r.Lam * r.nu) (r.hTr s) s (by positivity) (by positivity) hT0
    (le_of_eq (by unfold RegW.hTr; ring))
  have e : r.hTr (s + 1) = (1 + r.ha + ((s + 1 : ℕ) : ℝ) * (Real.sqrt r.Lam * r.nu)) *
      (1 + r.Lam * r.eN) ^ (s + 1) - 1 := by unfold RegW.hTr; push_cast; ring
  rw [e]
  have t3 : (1 + h) * a1 * n1 * a2 ≤ (1 + r.hTr s) * (r.Lam * r.eN) := by
    rw [mul_assoc, mul_assoc]
    rw [← mul_assoc a1]
    exact mul_le_mul (by linarith) t1 (by positivity) (by linarith)
  linarith

theorem eb_geW {r : RegW} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = r.Duw) (hL : L = r.Lam) (hsLe : sL = Real.sqrt r.Lam) (hX1 : X1 = r.Xw1)
    (hDc : 0 ≤ r.Dcw) (hR : 0 ≤ r.R) (hcb : 0 ≤ r.cbw) :
    Real.sqrt r.d * r.tp / 2 + (r.Dcw * r.R * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      r.cbw * r.R * ((101 / 100 * sL * X1 + sL * X1) * Du + r.DP)) ≤ r.eb := by
  subst hDuD hL hX1 hsLe
  unfold RegW.eb
  have a1 : (101 / 100 * Real.sqrt r.Lam * r.Xw1) ^ 2 + 10201 / 10000 * r.Lam ≤
      103 / 100 * r.Lam * (r.Xw1 ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt r.Lam * r.Xw1) ^ 2 =
        10201 / 10000 * (Real.sqrt r.Lam * Real.sqrt r.Lam) * r.Xw1 ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ r.Lam := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg r.Xw1)]
  have a2 : (101 / 100 * Real.sqrt r.Lam * r.Xw1 + Real.sqrt r.Lam * r.Xw1) * r.Duw ≤
      203 / 100 * Real.sqrt r.Lam * r.Xw1 * r.Duw := by
    have : 0 ≤ Real.sqrt r.Lam * r.Xw1 * r.Duw := by positivity
    nlinarith
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg hDc hR)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 r.DP) (mul_nonneg hcb hR)
  nlinarith

theorem ek_geW {r : RegW} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = r.Duw) (hL : L = r.Lam) (hsLe : sL = Real.sqrt r.Lam) (hX1 : X1 = r.Xw1)
    (hDc : 0 ≤ r.Dcw) (_hR : 0 ≤ r.R) (hcb : 0 ≤ r.cbw) :
    r.tp / 2 + (r.Dcw / 2 * r.R ^ 2 * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      r.cbw / 2 * r.R ^ 2 * ((101 / 100 * sL * X1 + sL * X1) * Du + r.DP)) ≤ r.ek := by
  subst hDuD hL hX1 hsLe
  unfold RegW.ek
  have a1 : (101 / 100 * Real.sqrt r.Lam * r.Xw1) ^ 2 + 10201 / 10000 * r.Lam ≤
      103 / 100 * r.Lam * (r.Xw1 ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt r.Lam * r.Xw1) ^ 2 =
        10201 / 10000 * (Real.sqrt r.Lam * Real.sqrt r.Lam) * r.Xw1 ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ r.Lam := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg r.Xw1)]
  have a2 : (101 / 100 * Real.sqrt r.Lam * r.Xw1 + Real.sqrt r.Lam * r.Xw1) * r.Duw ≤
      203 / 100 * Real.sqrt r.Lam * r.Xw1 * r.Duw := by
    have : 0 ≤ Real.sqrt r.Lam * r.Xw1 * r.Duw := by positivity
    nlinarith
  have hR2 := sq_nonneg r.R
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg (by positivity : 0 ≤ r.Dcw / 2) hR2)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 r.DP)
    (mul_nonneg (by positivity : 0 ≤ r.cbw / 2) hR2)
  have e : r.Dcw * r.R ^ 2 * (103 / 100) * r.Lam * (r.Xw1 ^ 2 + 1) / 2 =
      r.Dcw / 2 * r.R ^ 2 * (103 / 100 * r.Lam * (r.Xw1 ^ 2 + 1)) := by ring
  nlinarith

/-- The level of event (a)'s gauge bound is BUD-W's `L_e`. -/
theorem leW_eq (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : leW (refW d n δ).δc = (rW d n δ).Le := by
  show df2C0 * Real.log (1 / (1 / ((NeO d n (kDel δ) : ℕ) : ℝ))) = Unified.BudK.Le d n (kDel δ)
  rw [Unified.BudK.Le_eq d n (kDel δ) hd hn, one_div_one_div, df2C0]
  rfl

end AdversarialBco.UW.EngC

/-! ## From `RCHypOW` -/

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem sett (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    SettW d c.n δ (ctxOW K c δ ap) π (pwOW K c δ ap π) s st ξ' :=
  ⟨H.hd, H.hn, H.hc, H.reg, H.bud, H.enc, H.hs, H.det, H.tau, H.evG, rfl, rfl, rfl, H.track,
    by rw [← H.par]; exact H.xi⟩

theorem R (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).OK := H.sett.R

theorem play (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (XO c st ξ') - (ctxOW K c δ ap).X (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Xb :=
  playCOW d K c δ ap π s st ξ' H.hd H.hn H.par H.hc H.reg H.bud H.enc H.pg H.hs H.det H.tau H.evG H.track H.xi

/-! ### The precision `p` of `c` -/

theorem tpH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (1 : ℝ) / 2 ^ c.par.p = (rW d c.n δ).tp := by
  rw [H.par]; rfl

theorem tp_halfH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (1 : ℝ) / 2 ^ (c.par.p + 1) = (rW d c.n δ).tp / 2 := by
  rw [← H.tpH, pow_succ]; field_simp

theorem rnd_errH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (x : ℚ) :
    |((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)| ≤ (rW d c.n δ).tp / 2 := by
  rw [← H.tp_halfH]; exact rnd_err_real _ x

theorem rndV_errH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (v : Fin d → ℚ) :
    oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * (rW d c.n δ).tp / 2 := by
  have := rndV_err c.par.p v; rw [H.tp_halfH] at this; linarith

theorem nu_eqH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (d : ℝ) * (1 / 2 ^ (c.par.p + 1)) = (rW d c.n δ).nu := by
  rw [H.tp_halfH]; show (d : ℝ) * ((rW d c.n δ).tp / 2) = (d : ℝ) * (rW d c.n δ).tp / 2; ring

theorem tp_small (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).tp ≤ 1 / 1000 := H.R.tp_small

theorem tp0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).tp := H.R.htp0.le

/-! ### `ε'` and the radii -/

theorem eps_relH (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).eps ≤ ((c.par.eps : ℚ) : ℝ) ∧
      ((c.par.eps : ℚ) : ℝ) ≤ (rW d c.n δ).eps * (1 + (rW d c.n δ).tp / 16) := by
  rw [H.par]; exact ⟨H.enc.eps_le, H.enc.eps_rel⟩

theorem eps'_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : ((c.par.eps : ℚ) : ℝ) ≤ 1 / 2 := by
  have h1 := H.eps_relH.2
  have h2 := H.sett.eps_le
  have h3 := H.tp_small
  have h0 := H.sett.eps_pos
  nlinarith

theorem eps'_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 < ((c.par.eps : ℚ) : ℝ) :=
  H.sett.eps_pos.trans_le H.eps_relH.1

/-- The position of `c` is good at P°'s radius (`PgGood`). -/
theorem goodPos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : GoodPos K c (poW d c.n δ).R := by
  obtain ⟨P, hP, -, h1, h2, -⟩ := H.pg
  simp only [Option.some.injEq] at hP
  subst hP
  exact ⟨h1, h2⟩

theorem one_le_R (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 1 ≤ (poW d c.n δ).R := H.det.rows.one_le_R

theorem R_le_par (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (poW d c.n δ).R ≤ ((c.par.R : ℚ) : ℝ) := by
  rw [H.par]; exact H.enc.R_le

theorem parR_le_Rint (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : ((c.par.R : ℚ) : ℝ) ≤ (c.par.Rint : ℝ) := by
  rw [H.par]
  have e : (parOW d c.n δ).Rint = ⌈(parOW d c.n δ).R⌉₊ := rfl
  rw [e]
  exact_mod_cast Nat.le_ceil (parOW d c.n δ).R

/-- P°'s body is the body `S(K)` of the position of `c` (`PgGood`: `S(K) ⊆ B̄(0, R)`). -/
theorem Kt_eq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (ctxOW K c δ ap).Kt = bodyS K c := by
  show kTh c.n (refW d c.n δ).δc K c.S = bodyS K c
  rw [kTh_good (n := c.n) (δ := (refW d c.n δ).δc) H.pg]
  ext y
  simp only [df2Kp, bodyS, posBody, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := H.goodPos.2 h
    rwa [Metric.mem_closedBall, dist_zero_right] at this

/-! ### E2w: the gauge play and the observation -/

theorem kc_pos (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 < (rW d c.n δ).kc := H.sett.kc_pos

theorem cbw0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).cbw := (H.R.cbw_le).1

theorem exi0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).exi := (H.R.ezt_exi).2.2.1

theorem y00 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).y0 := (H.R.y0_bd).1.le

/-- `2^{-p} L_e^{1/2} ≤ 1/100`, from `h_a ≤ ℏ ≤ 1/100`. -/
theorem tp_sqrtLe (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).tp * Real.sqrt (rW d c.n δ).Le ≤ 1 / 100 := by
  have R := H.R
  have hha := (R.ha_le).1
  have hb := (R.p1).2.2
  have hV := (R.V_bd).1
  have hx := (R.x_bd).1
  have hha0 : 0 ≤ (rW d c.n δ).ha := le_trans H.tp0 hha
  have hhb : (rW d c.n δ).ha ≤ (rW d c.n δ).hb := by
    unfold RegW.hb; nlinarith
  have hLe : 0 ≤ (rW d c.n δ).Le := by have := R.hL1; linarith
  have hs : Real.sqrt (rW d c.n δ).Le ≤ Real.sqrt (8 * (rW d c.n δ).Le) := Real.sqrt_le_sqrt (by linarith)
  have htp := H.tp0
  have h1 : (rW d c.n δ).tp * Real.sqrt (8 * (rW d c.n δ).Le) ≤ (rW d c.n δ).ha := by
    unfold RegW.ha; nlinarith
  have h2 := mul_le_mul_of_nonneg_left hs htp
  linarith

/-- E2: `1 ≤ pt' ≤ P̄`, from GAUGE (b) (`gaugeBandO`), the Lipschitz gauge, event (a)'s `gauge(X°) ≤ L_e^{1/2}` at
the level, `|X' - X°| ≤ X̄ ≤ 1/16`, `ε' ≤ 1/2`. -/
theorem pt_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (1 : ℝ) ≤ ((ptO orc c (XO c st ξ') : ℚ) : ℝ) ∧ ((ptO orc c (XO c st ξ') : ℚ) : ℝ) ≤ (rW d c.n δ).Pb := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  have hX := H.play
  have hXb := (H.R.p4).1
  obtain ⟨-, hg, -⟩ := S.evG s S.hs'
  rw [leW_eq d c.n δ H.hd H.hn] at hg
  obtain ⟨hconv, -, hball, -, -⟩ := S.det.body
  have hlip := AdversarialBco.Bit.BLP.EngL.gauge_lip1 cx.Kt hconv hball (WithLp.toLp 2 (cV (XO c st ξ')))
    (WithLp.toLp 2 (cx.X πw s))
  rw [← WithLp.toLp_sub, ← oNorm_eq] at hlip
  have hgb : gauge cx.Kt (WithLp.toLp 2 (cV (XO c st ξ'))) ≤ Real.sqrt (rW d c.n δ).Le + 1 / 16 := by
    have := (abs_le.1 hlip).2
    linarith
  obtain ⟨-, hband⟩ := gaugeBandO d K orc c (poW d c.n δ).R (XO c st ξ') H.hd H.frame H.goodPos H.one_le_R
    H.R_le_par H.parR_le_Rint
  have hKt : gauge (bodyS K c) (toE (XO c st ξ')) = gauge cx.Kt (WithLp.toLp 2 (cV (XO c st ξ'))) := by
    rw [H.Kt_eq]; rfl
  rw [hKt] at hband
  have hu : (2 : ℝ)⁻¹ ^ (c.par.p + 2) = (rW d c.n δ).tp / 4 := by
    rw [← H.tpH, inv_pow, pow_add]; field_simp; norm_num
  rw [hu] at hband
  have htp := H.tp_small
  have htp0 := H.R.htp0
  have hga : ((gaugeP orc c (XO c st ξ') : ℚ) : ℝ) ≤
      (1 + (rW d c.n δ).tp / 4) * (Real.sqrt (rW d c.n δ).Le + 1 / 16) :=
    hband.trans (mul_le_mul_of_nonneg_left hgb (by positivity))
  have he := H.eps'_le
  have he0 := H.eps'_pos
  have hs : 1 ≤ Real.sqrt (rW d c.n δ).Le := le_trans (by norm_num) H.R.sqrtL_ge
  have htL := H.tp_sqrtLe
  unfold ptO
  push_cast
  refine ⟨le_max_left _ _, max_le (by unfold RegW.Pb; linarith) ?_⟩
  rw [div_le_iff₀ (by linarith)]
  unfold RegW.Pb
  have hm : 0 ≤ (2 * Real.sqrt (rW d c.n δ).Le + 1) * (1 / 2 - ((c.par.eps : ℚ) : ℝ)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- In mode `run` the play of BL-OW is in `K` (`play_int`; the cross check passes by `crossOKO`). -/
theorem play_mem (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : xO orc c st ξ' ∈ K := by
  obtain ⟨hK, -, hr0, -, hball, -, horc⟩ := H.frame
  have hcross : crossOK orc c :=
    crossOKO d K orc c (poW d c.n δ).R H.frame H.goodPos H.one_le_R H.R_le_par
  have heps0 : 0 ≤ c.par.eps := by have := H.eps'_pos.le; exact_mod_cast this
  have heps : c.par.eps ≤ 1 / 2 := by
    have h := H.eps'_le
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num] at h
    exact_mod_cast h
  exact interior_subset (play_int hK H.hd (by exact_mod_cast hr0) hball horc hcross heps0 heps (XO c st ξ'))

/-- UNI-OBS on the round: the reading `clip q ⌊2^p (f(x') + ε)⌋` is not clipped and is within `2^{-p}`. -/
theorem obs_eq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    obsO orc c st ξ' f ε = ⌊(2 : ℝ) ^ c.par.p * (f (xO orc c st ξ') + ε)⌋ ∧
      |((obsO orc c st ξ' f ε : ℤ) : ℝ) / 2 ^ c.par.p - (f (xO orc c st ξ') + ε)| ≤ (rW d c.n δ).tp := by
  have hf := H.adm.2 _ H.play_mem
  have hNe : 1 ≤ c.par.Ne := by
    rw [H.par]; exact Unified.BudK.NeO_pos d c.n (kDel δ) H.hd H.hn
  have hb : |f (xO orc c st ξ') + ε| ≤
      4 + 4 * Real.sqrt (Real.log (14 * c.n * c.par.Ne)) + Real.sqrt (2 * c.par.B) := by
    have hnz := abs_le.1 H.nz
    have hs := Real.sqrt_nonneg (2 * (c.par.B : ℝ))
    rw [abs_le]
    constructor <;> linarith [hf.1, hf.2, hnz.1, hnz.2]
  obtain ⟨h1, h2⟩ := obsClipO d c (f (xO orc c st ξ') + ε) H.hn hNe hb
  have e : obsO orc c st ξ' f ε = ⌊(2 : ℝ) ^ c.par.p * (f (xO orc c st ξ') + ε)⌋ := h1
  refine ⟨e, ?_⟩
  rw [e]
  have : (2 : ℝ)⁻¹ ^ c.par.p = (rW d c.n δ).tp := by rw [← H.tpH, inv_pow, one_div]
  rw [← this]; exact h2

/-- E2 for the unweighted reading `Y'_0` (R5) against BL-OW's exact observation `Ỹ`: `|Y'_0 - Ỹ| ≤ e_Y`. -/
theorem eY0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)).Y : ℚ) : ℝ) - YcO orc c st ξ' Z ε f| ≤ (rW d c.n δ).eY := by
  unfold YcO
  have hobs := H.obs_eq.2
  set pt : ℝ := ((ptO orc c (XO c st ξ') : ℚ) : ℝ)
  set F := f (xO orc c st ξ') + ε
  set obs := obsO orc c st ξ' f ε
  have hpt := H.pt_le
  have hrnd := H.rnd_errH (ptO orc c (XO c st ξ') * ((obs : ℚ) / 2 ^ c.par.p + ζ') / 2 +
    2 * (ptO orc c (XO c st ξ') - 1) / c.par.eps)
  rw [← Unified.EngC.rvO_Y] at hrnd
  push_cast at hrnd
  have hz : |(ζ' : ℝ) - Z / 2| ≤ (rW d c.n δ).ezt := by
    have := H.zt
    rw [H.par] at this
    exact this
  have e : (((rvO orc c st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * (F + Z / 2) / 2 + 2 * (pt - 1) / (c.par.eps : ℝ)) =
      ((((rvO orc c st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * ((obs : ℝ) / 2 ^ c.par.p + (ζ' : ℝ)) / 2 +
        2 * (pt - 1) / (c.par.eps : ℝ))) + pt / 2 * (((obs : ℝ) / 2 ^ c.par.p - F) + ((ζ' : ℝ) - Z / 2)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith [hpt.1] : (0 : ℝ) < pt / 2)]
  have h3 : |(obs : ℝ) / 2 ^ c.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤ (rW d c.n δ).tp + (rW d c.n δ).ezt :=
    (abs_add_le _ _).trans (add_le_add hobs hz)
  have h4 : pt / 2 * |(obs : ℝ) / 2 ^ c.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤
      (rW d c.n δ).Pb / 2 * ((rW d c.n δ).tp + (rW d c.n δ).ezt) :=
    mul_le_mul (by linarith [hpt.2]) h3 (abs_nonneg _) (by linarith [hpt.1, hpt.2])
  unfold RegW.eY
  linarith

/-- **E2w**: `|Y'^w - Y°| ≤ e^w_Y`. -/
theorem eY (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) - (ctxOW K c δ ap).Y (pwOW K c δ ap π) s| ≤ (rW d c.n δ).eYw := by
  have S := H.sett
  rw [H.Y]
  set Y0 := (rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)).Y
  set W : ℚ := min 1 (max 0 (b0OW d c.n δ + 1 - ξ' ⬝ᵥ ξ')) * max (-y0OW d c.n δ) (min (y0OW d c.n δ) Y0)
  have hY : (rvHW orc c δ st ξ' ζ' ε f).Y = rnd c.par.p W := rfl
  have h1 := H.rnd_errH W
  rw [← hY] at h1
  have hW : ((W : ℚ) : ℝ) = obsW (rW d c.n δ).b0 (rW d c.n δ).y0 (cV ξ') (Y0 : ℝ) :=
    ywQ_cast (b0OW d c.n δ) (y0OW d c.n δ) ξ' Y0
  have hB : obsW (refW d c.n δ).b0 (refW d c.n δ).y0 (π.xi s) (YcO orc c st ξ' Z ε f) =
      obsW (rW d c.n δ).b0 (rW d c.n δ).y0 (π.xi s) (YcO orc c st ξ' Z ε f) := rfl
  rw [hB]
  have hb0 : 0 ≤ (rW d c.n δ).b0 + 1 := by have := (H.R).hb0; have := H.R.hd; linarith
  have h2 := obsW_diff H.y00 hb0 (π.xi s) (cV ξ') (YcO orc c st ξ' Z ε f) (Y0 : ℝ) (rW d c.n δ).exi S.dxi_le
  have h3 := H.eY0
  have e : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) -
      obsW (rW d c.n δ).b0 (rW d c.n δ).y0 (π.xi s) (YcO orc c st ξ' Z ε f) =
      ((((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) - ((W : ℚ) : ℝ)) +
        (obsW (rW d c.n δ).b0 (rW d c.n δ).y0 (cV ξ') (Y0 : ℝ) -
          obsW (rW d c.n δ).b0 (rW d c.n δ).y0 (π.xi s) (YcO orc c st ξ' Z ε f)) := by
    rw [hW]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  unfold RegW.eYw
  have h4 : (rW d c.n δ).y0 * ((rW d c.n δ).exi * (2 * Real.sqrt ((rW d c.n δ).b0 + 1) + (rW d c.n δ).exi)) =
      (rW d c.n δ).y0 * (rW d c.n δ).exi * (2 * Real.sqrt ((rW d c.n δ).b0 + 1) + (rW d c.n δ).exi) := by ring
  linarith

/-! ### Lemma WR -/

/-- **Lemma WR** (i): on a round with `|ξ'|² ≥ b0 + 1` BL-OW's weighted observation vanishes. -/
theorem Y_zero_of (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (h : (rW d c.n δ).b0 + 1 ≤ cV ξ' ⬝ᵥ cV ξ') : (rvHW orc c δ st ξ' ζ' ε f).Y = 0 := by
  rw [rvOW_Y]
  apply ywQ_zero
  have : (((b0OW d c.n δ + 1 : ℚ)) : ℝ) ≤ ((ξ' ⬝ᵥ ξ' : ℚ) : ℝ) := by
    rw [cV_dot]; push_cast; exact h
  exact_mod_cast this

/-- **Lemma WR** (ii): on a weighted round, `|ξ| ≤ Ξ_w` and `|ξ'| ≤ Ξ_{w1}`. -/
theorem wr (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0) :
    oNorm (π.xi s) ≤ (rW d c.n δ).Xw ∧ oNorm (cV ξ') ≤ (rW d c.n δ).Xw1 := by
  have S := H.sett
  have hdx := S.dxi_le
  have hexi := S.exi_le
  have hex1 := S.exi_le_one
  have htp := H.R.htp0
  have t1 := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
  rw [add_sub_cancel] at t1
  have t2 := oNorm_add_le (cV ξ') (π.xi s - cV ξ')
  rw [add_sub_cancel, oNorm_sub_comm] at t2
  rcases hw with hY | hY
  · have hlt : cV ξ' ⬝ᵥ cV ξ' < (rW d c.n δ).b0 + 1 := by
      by_contra hc
      push_neg at hc
      exact hY (by rw [H.Y_zero_of hc]; simp)
    have h1 : oNorm (cV ξ') ≤ Real.sqrt ((rW d c.n δ).b0 + 1) := by
      unfold oNorm; exact Real.sqrt_le_sqrt hlt.le
    unfold RegW.Xw1 RegW.Xw
    constructor <;> linarith
  · have h1 := S.xi_w hY
    unfold RegW.Xw1
    constructor <;> linarith

/-- Lemma WR (iii): on an unweighted round both factors' coefficients vanish. -/
theorem c_zero (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (hw : ¬ ((((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0)) :
    (rvHW orc c δ st ξ' ζ' ε f).c = 0 ∧ (ctxOW K c δ ap).cc (pwOW K c δ ap π) s = 0 := by
  rw [not_or, not_not, not_not] at hw
  have hY : (rvHW orc c δ st ξ' ζ' ε f).Y = 0 := by exact_mod_cast hw.1
  refine ⟨?_, ?_⟩
  · rw [rvOW_c, hY, mul_zero]
  · rw [H.sett.cc_eq, hw.2, mul_zero]

/-! ### E3w -/

theorem Dcw0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).Dcw := (H.R.Dcw_le).1

theorem cbw_small (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).cbw * (1 + (rW d c.n δ).Xw1 ^ 2) ≤ 1 / 10 ^ 30 :=
  (H.R.cbw_dom).trans (by norm_num)

theorem Dcw_small (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).Dcw * (1 + (rW d c.n δ).Xw1 ^ 2) ≤ 1 / 10 ^ 30 := by
  have h := H.R.Dcw_dom
  have h1 := (H.R.sqrt_dLe).1
  have h2 := (H.R.sqrt_dLe).2
  have h3 := H.R.tiny 1 1 (by norm_num) (by norm_num)
  have htp := H.tp0
  rw [pow_one, pow_one] at h3
  have h4 : Real.sqrt ((rW d c.n δ).d * (rW d c.n δ).Le) * (rW d c.n δ).tp ≤ 1 :=
    calc Real.sqrt ((rW d c.n δ).d * (rW d c.n δ).Le) * (rW d c.n δ).tp
        ≤ (rW d c.n δ).d * (rW d c.n δ).Q * (rW d c.n δ).tp :=
          mul_le_mul_of_nonneg_right (h1.trans h2) htp
      _ ≤ 1 / 2 ^ 160 := h3
      _ ≤ 1 := by norm_num
  rw [mul_comm]
  calc (1 + (rW d c.n δ).Xw1 ^ 2) * (rW d c.n δ).Dcw ≤ Real.sqrt ((rW d c.n δ).d * (rW d c.n δ).Le) *
        (rW d c.n δ).tp / 10 ^ 30 := h
    _ ≤ 1 / 10 ^ 30 := by
        rw [div_le_div_iff_of_pos_right (by norm_num)]; exact h4

/-- E3w (i): `|c' - c°| ≤ Δ^w_c`. -/
theorem dc (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) - (ctxOW K c δ ap).cc (pwOW K c δ ap π) s| ≤ (rW d c.n δ).Dcw := by
  have S := H.sett
  rw [S.cc_eq, rvOW_c]
  push_cast
  have hk : |((c.par.kapc : ℚ) : ℝ) / (rW d c.n δ).kc - 1| ≤ (rW d c.n δ).tp / 16 := by
    rw [H.par]; exact H.enc.kapc_rel
  have h := dc_real _ _ _ _ _ _ _ H.kc_pos hk H.eY S.Y_le
  refine h.trans (le_of_eq ?_)
  unfold RegW.Dcw; ring

theorem c'_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ)| ≤ (rW d c.n δ).cbw + (rW d c.n δ).Dcw := by
  have h1 := H.dc; have h2 := H.sett.cc_le
  have := abs_add_le ((((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) - (ctxOW K c δ ap).cc (pwOW K c δ ap π) s)
    ((ctxOW K c δ ap).cc (pwOW K c δ ap π) s)
  rw [sub_add_cancel] at this; linarith

theorem q_cast (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) = 1 - (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) +
      (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) * (cV ξ' ⬝ᵥ cV ξ') := by
  rw [rvOW_q, rvOW_a]; push_cast; rw [cV_dot]

theorem qq_eq (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (ctxOW K c δ ap).qq (pwOW K c δ ap π) s = 1 - (ctxOW K c δ ap).cc (pwOW K c δ ap π) s +
      (ctxOW K c δ ap).cc (pwOW K c δ ap π) s * (π.xi s ⬝ᵥ π.xi s) := rfl

/-- On a weighted round, `0 ≤ |ξ'|², |ξ|² ≤ Ξ_{w1}²` and `||ξ'|² - |ξ|²| ≤ 2 Ξ_{w1} e_ξ`. -/
theorem xx_w (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0) :
    (0 ≤ cV ξ' ⬝ᵥ cV ξ' ∧ cV ξ' ⬝ᵥ cV ξ' ≤ (rW d c.n δ).Xw1 ^ 2) ∧
      (0 ≤ π.xi s ⬝ᵥ π.xi s ∧ π.xi s ⬝ᵥ π.xi s ≤ (rW d c.n δ).Xw1 ^ 2) ∧
      |cV ξ' ⬝ᵥ cV ξ' - π.xi s ⬝ᵥ π.xi s| ≤ 2 * (rW d c.n δ).Xw1 * (rW d c.n δ).exi := by
  obtain ⟨h1, h2⟩ := H.wr hw
  have hX := (H.R.Xw_bd).2.2.1
  have h1' : oNorm (π.xi s) ≤ (rW d c.n δ).Xw1 := h1.trans hX
  refine ⟨⟨by rw [← oNorm_sq]; positivity, ?_⟩, ⟨by rw [← oNorm_sq]; positivity, ?_⟩, ?_⟩
  · rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h2 2
  · rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h1' 2
  · refine (dot_sq_diff _ _).trans ?_
    have hx : 0 ≤ (rW d c.n δ).Xw1 := (oNorm_nonneg _).trans h2
    exact mul_le_mul (by linarith) H.sett.dxi_le (oNorm_nonneg _) (by positivity)

/-- E16w: `|q' - q°| ≤ Δ_q`. -/
theorem dq (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) - (ctxOW K c δ ap).qq (pwOW K c δ ap π) s| ≤ (rW d c.n δ).Dq := by
  have hcb := H.cbw0
  have hx := H.exi0
  have hD0 := H.Dcw0
  have hX : 0 ≤ (rW d c.n δ).Xw1 := (Xw_nonneg H.R).2
  have hDq0 : 0 ≤ (rW d c.n δ).Dq := by unfold RegW.Dq; positivity
  rw [H.q_cast, H.qq_eq]
  by_cases hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0
  · obtain ⟨hxx, -, hdxx⟩ := H.xx_w hw
    have h := q_diff _ _ _ _ _ (π.xi s ⬝ᵥ π.xi s) _ H.sett.cc_le H.dc hxx.1 hxx.2
    refine h.trans ?_
    unfold RegW.Dq
    have := mul_le_mul_of_nonneg_left hdxx hcb
    have : 0 ≤ (rW d c.n δ).cbw * (rW d c.n δ).Xw1 * (rW d c.n δ).exi := by positivity
    nlinarith
  · obtain ⟨h1, h2⟩ := H.c_zero hw
    rw [h1, h2]
    simpa using hDq0

/-- GUARD (E18), R7: `a', q' ≥ 1/2`. -/
theorem ga (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ¬ ((rvHW orc c δ st ξ' ζ' ε f).a < 1 / 2 ∨ (rvHW orc c δ st ξ' ζ' ε f).q < 1 / 2) := by
  have hc := H.c'_le
  have h1 := H.cbw_small
  have h2 := H.Dcw_small
  have hX := sq_nonneg (rW d c.n δ).Xw1
  have hpos : 0 ≤ (rW d c.n δ).cbw + (rW d c.n δ).Dcw := le_trans (abs_nonneg _) hc
  have hcX : ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * (1 + (rW d c.n δ).Xw1 ^ 2) ≤ 2 / 10 ^ 30 := by
    rw [add_mul]; linarith
  have hcX2 : ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * (rW d c.n δ).Xw1 ^ 2 ≤
      ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * (1 + (rW d c.n δ).Xw1 ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos
  have hcb1 : (rW d c.n δ).cbw + (rW d c.n δ).Dcw ≤ 2 / 10 ^ 30 := by
    have : ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * 1 ≤
        ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * (1 + (rW d c.n δ).Xw1 ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hpos
    linarith
  set c' := (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ)
  have ha : (1 / 2 : ℝ) ≤ (((rvHW orc c δ st ξ' ζ' ε f).a : ℚ) : ℝ) := by
    rw [rvOW_a]; push_cast
    have := (abs_le.1 hc).2; linarith
  have hcx : |c' * (cV ξ' ⬝ᵥ cV ξ')| ≤ 2 / 10 ^ 30 := by
    by_cases hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0
    · obtain ⟨hxx, -, -⟩ := H.xx_w hw
      have : |c' * (cV ξ' ⬝ᵥ cV ξ')| ≤ ((rW d c.n δ).cbw + (rW d c.n δ).Dcw) * (rW d c.n δ).Xw1 ^ 2 := by
        rw [abs_mul, abs_of_nonneg hxx.1]; exact mul_le_mul hc hxx.2 hxx.1 (by linarith [abs_nonneg c'])
      linarith
    · have h0 : c' = 0 := by
        show (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) = 0
        rw [(H.c_zero hw).1]; simp
      rw [h0, zero_mul, abs_zero]; norm_num
  have hq : (1 / 2 : ℝ) ≤ (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) := by
    rw [H.q_cast]
    have := (abs_le.1 hcx).1; have := (abs_le.1 hc).2
    linarith
  rw [not_or, not_lt, not_lt]
  constructor
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact ha)
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact hq)

theorem a_ge (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (1 / 2 : ℝ) ≤ (((rvHW orc c δ st ξ' ζ' ε f).a : ℚ) : ℝ) ∧
      (1 / 2 : ℝ) ≤ (((rvHW orc c δ st ξ' ζ' ε f).q : ℚ) : ℝ) := by
  have h := H.ga
  rw [not_or, not_lt, not_lt] at h
  refine ⟨?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 h.1; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h.2; push_cast at this; exact this

theorem sqrt_hyp (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtDn c.par.p x : ℚ) : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Real.sqrt (x : ℝ) < ((sqrtDn c.par.p x : ℚ) : ℝ) + (rW d c.n δ).tp := by
  rw [← H.tpH]; exact sqrtDn_err _ hx

/-- The real scalars of E3 (ii): BL's roots and quotients against their exact values at BL's inputs. -/
theorem scal (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    let r := rvHW orc c δ st ξ' ζ' ε f
    let c' : ℝ := ((r.c : ℚ) : ℝ)
    let xx' := cV ξ' ⬝ᵥ cV ξ'
    ((r.s1 : ℝ) ≤ Real.sqrt (1 / (1 - c')) ∧ Real.sqrt (1 / (1 - c')) < (r.s1 : ℝ) + (rW d c.n δ).tp) ∧
    ((r.s3 : ℝ) ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < (r.s3 : ℝ) + (rW d c.n δ).tp) ∧
    ((r.rq : ℝ) ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < (r.rq : ℝ) + (rW d c.n δ).tp) ∧
    |(r.s2 : ℝ) - c' / ((r.s3 : ℝ) * (r.rq : ℝ) * ((r.s3 : ℝ) + (r.rq : ℝ)))| ≤ (rW d c.n δ).tp / 2 ∧
    |(r.s4 : ℝ) - c' / ((r.s3 : ℝ) + (r.rq : ℝ))| ≤ (rW d c.n δ).tp / 2 := by
  intro r c' xx'
  have ha := H.a_ge
  have ha0 : (0 : ℚ) ≤ r.a := by exact_mod_cast (by linarith [ha.1] : (0 : ℝ) ≤ (r.a : ℝ))
  have hq0 : (0 : ℚ) ≤ r.q := by exact_mod_cast (by linarith [ha.2] : (0 : ℝ) ≤ (r.q : ℝ))
  have h1 := H.sqrt_hyp (1 / r.a) (by positivity)
  have h3 := H.sqrt_hyp r.a ha0
  have h4 := H.sqrt_hyp r.q hq0
  have e1 : (((1 / r.a : ℚ)) : ℝ) = 1 / (1 - c') := by rw [rvOW_a]; push_cast; rfl
  have e3 : ((r.a : ℚ) : ℝ) = 1 - c' := by rw [rvOW_a]; push_cast; rfl
  have e4 : ((r.q : ℚ) : ℝ) = 1 - c' + c' * xx' := H.q_cast
  rw [e1] at h1; rw [e3] at h3; rw [e4] at h4
  refine ⟨h1, h3, h4, ?_, ?_⟩
  · have := H.rnd_errH (r.c / (r.s3 * r.rq * (r.s3 + r.rq)))
    rw [← rvOW_s2] at this
    push_cast at this; exact this
  · have := H.rnd_errH (r.c / (r.s3 + r.rq))
    rw [← rvOW_s4] at this
    push_cast at this; exact this

/-- On an unweighted round BL's coefficients `s2', s4'` vanish. -/
theorem s24_zero (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f)
    (hw : ¬ ((((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0)) :
    (rvHW orc c δ st ξ' ζ' ε f).s2 = 0 ∧ (rvHW orc c δ st ξ' ζ' ε f).s4 = 0 := by
  have h0 := (H.c_zero hw).1
  rw [rvOW_s2, rvOW_s4, h0, zero_div, zero_div, rnd_zero]
  exact ⟨rfl, rfl⟩

open AdversarialBco.Unified.Eng.RCHypO (phi psi) in
/-- E3w: `|N' - N°| ≤ e^w_N` for the factor of `A`. -/
theorem e3A (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    opN ((((rvHW orc c δ st ξ' ζ' ε f).s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-(((rvHW orc c δ st ξ' ζ' ε f).s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ') -
      ((Real.sqrt ((ctxOW K c δ ap).aa (pwOW K c δ ap π) s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-phi (ctxOW K c δ ap) (pwOW K c δ ap π) s) • vecMulVec (π.xi s) (π.xi s))) ≤ (rW d c.n δ).eN := by
  have S := H.sett
  obtain ⟨h1, h3, h4, h2, -⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.cbw_small
  have hΔ := H.Dcw_small
  have htp0 := H.tp0
  have htp := H.tp_small
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have hge := eN_geW H.R
  by_cases hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0
  · obtain ⟨hxx, hxx0, -⟩ := H.xx_w hw
    obtain ⟨hξ, hξ'⟩ := H.wr hw
    have hξ1 : oNorm (π.xi s) ≤ (rW d c.n δ).Xw1 := hξ.trans (H.R.Xw_bd).2.2.1
    have i1 := e3_scal_inv _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h1
    have i2 := e3_scal_phi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h2
    have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).1
    have h := e3_mat (π.xi s) (cV ξ') _ (-(((rvHW orc c δ st ξ' ζ' ε f).s2 : ℚ) : ℝ)) _
      (-phi (ctxOW K c δ ap) (pwOW K c δ ap π) s) (rW d c.n δ).Xw1 (rW d c.n δ).exi
      ((rW d c.n δ).tp + (rW d c.n δ).Dcw)
      (51 / 100 * (rW d c.n δ).tp + (rW d c.n δ).Dcw + (rW d c.n δ).cbw * (rW d c.n δ).Dq) (rW d c.n δ).cbw
      hξ1 hξ' S.dxi_le i1 (by rw [neg_sub_neg, abs_sub_comm]; exact i2) (by rw [abs_neg]; exact i3)
    exact h.trans hge
  · obtain ⟨hc0, hcc0⟩ := H.c_zero hw
    obtain ⟨hs2, -⟩ := H.s24_zero hw
    have hc0' : (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) = 0 := by rw [hc0]; simp
    have hphi : phi (ctxOW K c δ ap) (pwOW K c δ ap π) s = 0 := by
      unfold phi; rw [hcc0, zero_div]
    have i1 := e3_scal_inv 0 0 0 0 0 (rW d c.n δ).tp _ (by simp) (by simp) (by norm_num) (by norm_num) htp0 htp
      (by rw [hc0'] at h1; exact h1)
    have haa : (ctxOW K c δ ap).aa (pwOW K c δ ap π) s = 1 - 0 := by
      show 1 - (ctxOW K c δ ap).cc (pwOW K c δ ap π) s = 1 - 0; rw [hcc0]
    have h := e3_mat (π.xi s) (cV ξ') (((rvHW orc c δ st ξ' ζ' ε f).s1 : ℚ) : ℝ)
      (-(((rvHW orc c δ st ξ' ζ' ε f).s2 : ℚ) : ℝ)) (Real.sqrt ((ctxOW K c δ ap).aa (pwOW K c δ ap π) s))⁻¹
      (-phi (ctxOW K c δ ap) (pwOW K c δ ap π) s) (rW d c.n δ).Xi1 (rW d c.n δ).exi
      ((rW d c.n δ).tp + 0) 0 0 S.xi_le1 S.xi'_le S.dxi_le (by rw [haa]; exact i1)
      (by rw [hs2, hphi]; simp) (by rw [hphi]; simp)
    refine h.trans ?_
    have hD0 := H.Dcw0
    have hcb0 := H.cbw0
    have hx0 := H.exi0
    have hX : 0 ≤ (rW d c.n δ).Xw1 := (Xw_nonneg H.R).2
    have hDq : 0 ≤ (rW d c.n δ).Dq := by unfold RegW.Dq; positivity
    have : 0 ≤ (51 / 100 * (rW d c.n δ).tp + (rW d c.n δ).Dcw + (rW d c.n δ).cbw * (rW d c.n δ).Dq) *
        (rW d c.n δ).Xw1 ^ 2 + (rW d c.n δ).cbw * (2 * (rW d c.n δ).Xw1) * (rW d c.n δ).exi := by positivity
    simp only [zero_mul, add_zero, mul_zero]
    linarith

open AdversarialBco.Unified.Eng.RCHypO (phi psi) in
/-- E3w: `|N'^{inv} - (N°)^{-1}| ≤ e^w_N` for the factor of `B`. -/
theorem e3B (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    opN ((((rvHW orc c δ st ξ' ζ' ε f).s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (((rvHW orc c δ st ξ' ζ' ε f).s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ') -
      (Real.sqrt ((ctxOW K c δ ap).aa (pwOW K c δ ap π) s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        psi (ctxOW K c δ ap) (pwOW K c δ ap π) s • vecMulVec (π.xi s) (π.xi s))) ≤ (rW d c.n δ).eN := by
  have S := H.sett
  obtain ⟨-, h3, h4, -, h5⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.cbw_small
  have hΔ := H.Dcw_small
  have htp0 := H.tp0
  have htp := H.tp_small
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have hge := eN_geW H.R
  by_cases hw : (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0
  · obtain ⟨hxx, hxx0, -⟩ := H.xx_w hw
    obtain ⟨hξ, hξ'⟩ := H.wr hw
    have hξ1 : oNorm (π.xi s) ≤ (rW d c.n δ).Xw1 := hξ.trans (H.R.Xw_bd).2.2.1
    have i1 := e3_scal_sqrt _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h3
    have i2 := e3_scal_psi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h5
    have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).2
    have h := e3_mat (π.xi s) (cV ξ') _ _ _ (psi (ctxOW K c δ ap) (pwOW K c δ ap π) s) (rW d c.n δ).Xw1
      (rW d c.n δ).exi ((rW d c.n δ).tp + (rW d c.n δ).Dcw)
      (51 / 100 * (rW d c.n δ).tp + (rW d c.n δ).Dcw + (rW d c.n δ).cbw * (rW d c.n δ).Dq) (rW d c.n δ).cbw
      hξ1 hξ' S.dxi_le i1 i2 i3
    exact h.trans hge
  · obtain ⟨hc0, hcc0⟩ := H.c_zero hw
    obtain ⟨-, hs4⟩ := H.s24_zero hw
    have hc0' : (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) = 0 := by rw [hc0]; simp
    have hpsi : psi (ctxOW K c δ ap) (pwOW K c δ ap π) s = 0 := by
      unfold psi; rw [hcc0, zero_div]
    have i1 := e3_scal_sqrt 0 0 0 0 0 (rW d c.n δ).tp _ (by simp) (by simp) (by norm_num) (by norm_num) htp0 htp
      (by rw [hc0'] at h3; exact h3)
    have haa : (ctxOW K c δ ap).aa (pwOW K c δ ap π) s = 1 - 0 := by
      show 1 - (ctxOW K c δ ap).cc (pwOW K c δ ap π) s = 1 - 0; rw [hcc0]
    have h := e3_mat (π.xi s) (cV ξ') (((rvHW orc c δ st ξ' ζ' ε f).s3 : ℚ) : ℝ)
      (((rvHW orc c δ st ξ' ζ' ε f).s4 : ℚ) : ℝ) (Real.sqrt ((ctxOW K c δ ap).aa (pwOW K c δ ap π) s))
      (psi (ctxOW K c δ ap) (pwOW K c δ ap π) s) (rW d c.n δ).Xi1
      (rW d c.n δ).exi ((rW d c.n δ).tp + 0) 0 0 S.xi_le1 S.xi'_le S.dxi_le (by rw [haa]; exact i1)
      (by rw [hs4, hpsi]; simp) (by rw [hpsi]; simp)
    refine h.trans ?_
    have hD0 := H.Dcw0
    have hcb0 := H.cbw0
    have hx0 := H.exi0
    have hX : 0 ≤ (rW d c.n δ).Xw1 := (Xw_nonneg H.R).2
    have hDq : 0 ≤ (rW d c.n δ).Dq := by unfold RegW.Dq; positivity
    have : 0 ≤ (51 / 100 * (rW d c.n δ).tp + (rW d c.n δ).Dcw + (rW d c.n δ).cbw * (rW d c.n δ).Dq) *
        (rW d c.n δ).Xw1 ^ 2 + (rW d c.n δ).cbw * (2 * (rW d c.n δ).Xw1) * (rW d c.n δ).exi := by positivity
    simp only [zero_mul, add_zero, mul_zero]
    linarith

end AdversarialBco.UW.Eng.RCHypOW
