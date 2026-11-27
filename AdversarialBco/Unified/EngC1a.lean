/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngPlay
public import AdversarialBco.Unified.BLOGeom
public import AdversarialBco.Bit.BLRoundC1

@[expose] public section

/-!
# Piece C for BL-O, part C1 (a): the observation and the factor

Bit/BLRoundC1.lean (first half) for BL-O at `k`: BL-O's values of R5 to R9 (`rvO`, the `let`s of `stepO`), E2 (the
observation) and E3 (the factor) with E16's `Δ_q` and the guard R7, against P°'s update of round `s`. Two changes
against v2.1:

* `pt_le` (`1 ≤ pt' ≤ P̄`): the gauge play `ptO` is within `1 + 2^{-p-2}` of the gauge of `S(K)` (`gaugeBandO`, in
  the good position at P°'s radius), and `S(K) = K~` is P°'s body on `PgGood`;
* `eY` (`|Y' - Y°| ≤ e_Y`): the reading is `clip q ⌊2^p (f(x') + ε)⌋`; the play is in `K` (`play_int`, the cross
  check passes by `crossOKO`), so `f(x') ∈ [0, 1]`, and `|f(x') + ε|` is within the no-clip bound, so the clip does
  not act and the reading is within `2^{-p}` (`obsClipO`).
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## BL-O's values, line by line -/

section rv

variable (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)

theorem rvO_Y : (rvO orc c st ξ ζ obs).Y = rnd c.par.p (ptO orc c (XO c st ξ) * ((obs : ℚ) / 2 ^ c.par.p + ζ) / 2 +
    2 * (ptO orc c (XO c st ξ) - 1) / c.par.eps) := rfl
theorem rvO_c : (rvO orc c st ξ ζ obs).c = c.par.kapc * (rvO orc c st ξ ζ obs).Y := rfl
theorem rvO_a : (rvO orc c st ξ ζ obs).a = 1 - (rvO orc c st ξ ζ obs).c := rfl
theorem rvO_q : (rvO orc c st ξ ζ obs).q = (rvO orc c st ξ ζ obs).a + (rvO orc c st ξ ζ obs).c * (ξ ⬝ᵥ ξ) := rfl
theorem rvO_s2 : (rvO orc c st ξ ζ obs).s2 = rnd c.par.p ((rvO orc c st ξ ζ obs).c /
    ((rvO orc c st ξ ζ obs).s3 * (rvO orc c st ξ ζ obs).rq * ((rvO orc c st ξ ζ obs).s3 + (rvO orc c st ξ ζ obs).rq))) :=
  rfl
theorem rvO_s4 : (rvO orc c st ξ ζ obs).s4 = rnd c.par.p ((rvO orc c st ξ ζ obs).c /
    ((rvO orc c st ξ ζ obs).s3 + (rvO orc c st ξ ζ obs).rq)) := rfl
theorem rvO_G : (rvO orc c st ξ ζ obs).G = st.G + (rvO orc c st ξ ζ obs).g := rfl

end rv

/-- BL-O's values of round `s` in the setting of `RCHypO`. -/
noncomputable abbrev rvH (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (ε : ℝ)
    (f : E d → ℝ) : Bit.BLP.RC.RV d :=
  rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)

/-! ## The constants of E3 to E11 at `k` -/

/-- The constant `e_N` of E3 bounds the error of the factor. -/
theorem eN_geK {d n k : ℕ} (h : BudK.BudOK d n k) (hDc : 0 ≤ BudK.Dc d n k) (hcb : 0 ≤ BudK.cb d n k) :
    (BudK.tp d n k + BudK.Dc d n k) + (51 / 100 * BudK.tp d n k + BudK.Dc d n k + BudK.cb d n k * BudK.Dq d n k) * BudK.Xi1 d n k ^ 2 +
      BudK.cb d n k * (2 * BudK.Xi1 d n k) * BudK.exi d n k ≤ BudK.eN d n k := by
  have hc := h.cb_le
  have htp := (NK.tp_pos d n k).le
  have hx := (NK.Xi1_pos d n k).le
  have hexi : 0 ≤ BudK.exi d n k := by unfold BudK.exi; positivity
  have hX2 : 0 ≤ BudK.Xi1 d n k ^ 2 := sq_nonneg _
  have hcX : BudK.cb d n k * BudK.Xi1 d n k ^ 2 ≤ 1 / 10 ^ 30 := by nlinarith
  unfold BudK.eN BudK.Dq
  have a1 : BudK.cb d n k * (BudK.Dc d n k * (1 + BudK.Xi1 d n k ^ 2) + 202 / 100 * BudK.cb d n k * BudK.Xi1 d n k * BudK.exi d n k) *
      BudK.Xi1 d n k ^ 2 ≤ 1 / 10 ^ 30 * (BudK.Dc d n k * (1 + BudK.Xi1 d n k ^ 2)) +
        1 / 10 ^ 30 * (202 / 100 * BudK.cb d n k * BudK.Xi1 d n k * BudK.exi d n k) := by
    have : BudK.cb d n k * (BudK.Dc d n k * (1 + BudK.Xi1 d n k ^ 2) + 202 / 100 * BudK.cb d n k * BudK.Xi1 d n k * BudK.exi d n k) *
        BudK.Xi1 d n k ^ 2 = (BudK.cb d n k * BudK.Xi1 d n k ^ 2) *
          (BudK.Dc d n k * (1 + BudK.Xi1 d n k ^ 2) + 202 / 100 * BudK.cb d n k * BudK.Xi1 d n k * BudK.exi d n k) := by ring
    rw [this, ← mul_add]
    exact mul_le_mul_of_nonneg_right hcX (by positivity)
  nlinarith [mul_nonneg hDc hX2, mul_nonneg (mul_nonneg hcb hx) hexi, mul_nonneg htp hX2]

theorem eN_nonnegK {d n k : ℕ} (hDc : 0 ≤ BudK.Dc d n k) (hcb : 0 ≤ BudK.cb d n k) : 0 ≤ BudK.eN d n k := by
  have := (NK.tp_pos d n k).le; have := (NK.Xi1_pos d n k).le
  have : 0 ≤ BudK.exi d n k := by unfold BudK.exi; positivity
  unfold BudK.eN; positivity

/-- The step of TRACK in numbers: `h + (1 + h)|A0||N' - N||Ai| + |ρ||Ai| ≤ hTr (s + 1)`. -/
theorem track_numK {d n k : ℕ} (s : ℕ) (h a1 a2 n1 r : ℝ) (hh0 : 0 ≤ h) (hh : h ≤ BudK.hTr d n k s) (ha1 : 0 ≤ a1)
    (ha1' : a1 ≤ Real.sqrt (BudK.Lam d n k)) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ Real.sqrt (BudK.Lam d n k)) (hn1 : 0 ≤ n1)
    (hn1' : n1 ≤ BudK.eN d n k) (hr : 0 ≤ r) (hr' : r ≤ BudK.nu d n k) (hL : 0 ≤ BudK.Lam d n k) :
    h + (1 + h) * a1 * n1 * a2 + r * a2 ≤ BudK.hTr d n k (s + 1) := by
  have hsq : Real.sqrt (BudK.Lam d n k) * Real.sqrt (BudK.Lam d n k) = BudK.Lam d n k := Real.mul_self_sqrt hL
  have heN : 0 ≤ BudK.eN d n k := hn1.trans hn1'
  have hnu : 0 ≤ BudK.nu d n k := hr.trans hr'
  have hs0 := Real.sqrt_nonneg (BudK.Lam d n k)
  have t1 : a1 * n1 * a2 ≤ BudK.Lam d n k * BudK.eN d n k := by
    calc a1 * n1 * a2 ≤ Real.sqrt (BudK.Lam d n k) * BudK.eN d n k * Real.sqrt (BudK.Lam d n k) :=
          mul_le_mul (mul_le_mul ha1' hn1' hn1 hs0) ha2' ha2 (by positivity)
      _ = BudK.Lam d n k * BudK.eN d n k := by
        rw [show Real.sqrt (BudK.Lam d n k) * BudK.eN d n k * Real.sqrt (BudK.Lam d n k) =
          (Real.sqrt (BudK.Lam d n k) * Real.sqrt (BudK.Lam d n k)) * BudK.eN d n k by ring, hsq]
  have t2 : r * a2 ≤ Real.sqrt (BudK.Lam d n k) * BudK.nu d n k := by
    rw [mul_comm (Real.sqrt _)]; exact mul_le_mul hr' ha2' ha2 hnu
  have hT0 : 0 ≤ BudK.hTr d n k s := hh0.trans hh
  have step := hTr_step (BudK.ha d n k) (BudK.Lam d n k * BudK.eN d n k) (Real.sqrt (BudK.Lam d n k) * BudK.nu d n k)
    (BudK.hTr d n k s) s (by positivity) (by positivity) hT0 (le_of_eq (by unfold BudK.hTr; ring))
  have e : BudK.hTr d n k (s + 1) = (1 + BudK.ha d n k + ((s + 1 : ℕ) : ℝ) * (Real.sqrt (BudK.Lam d n k) * BudK.nu d n k)) *
      (1 + BudK.Lam d n k * BudK.eN d n k) ^ (s + 1) - 1 := by unfold BudK.hTr; ring
  rw [e]
  have t3 : (1 + h) * a1 * n1 * a2 ≤ (1 + BudK.hTr d n k s) * (BudK.Lam d n k * BudK.eN d n k) := by
    rw [mul_assoc, mul_assoc]
    rw [← mul_assoc a1]
    exact mul_le_mul (by linarith) t1 (by positivity) (by linarith)
  linarith

theorem eb_geK {d n k : ℕ} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = BudK.Du d n k) (hL : L = BudK.Lam d n k) (hsLe : sL = Real.sqrt (BudK.Lam d n k)) (hX1 : X1 = BudK.Xi1 d n k)
    (hDc : 0 ≤ BudK.Dc d n k) (hR : 0 ≤ BudK.R d n k) (hcb : 0 ≤ BudK.cb d n k) :
    Real.sqrt d * BudK.tp d n k / 2 + (BudK.Dc d n k * BudK.R d n k * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      BudK.cb d n k * BudK.R d n k * ((101 / 100 * sL * X1 + sL * X1) * Du + BudK.DP d n k)) ≤ BudK.eb d n k := by
  subst hDuD hL hX1 hsLe
  unfold BudK.eb
  have a1 : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) ^ 2 + 10201 / 10000 * BudK.Lam d n k ≤
      103 / 100 * BudK.Lam d n k * (BudK.Xi1 d n k ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) ^ 2 =
        10201 / 10000 * (Real.sqrt (BudK.Lam d n k) * Real.sqrt (BudK.Lam d n k)) * BudK.Xi1 d n k ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ BudK.Lam d n k := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg (BudK.Xi1 d n k))]
  have a2 : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k + Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) * BudK.Du d n k ≤
      203 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k * BudK.Du d n k := by
    have : 0 ≤ Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k * BudK.Du d n k := by positivity
    nlinarith
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg hDc hR)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 (BudK.DP d n k)) (mul_nonneg hcb hR)
  nlinarith

theorem ek_geK {d n k : ℕ} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = BudK.Du d n k) (hL : L = BudK.Lam d n k) (hsLe : sL = Real.sqrt (BudK.Lam d n k)) (hX1 : X1 = BudK.Xi1 d n k)
    (hDc : 0 ≤ BudK.Dc d n k) (_hR : 0 ≤ BudK.R d n k) (hcb : 0 ≤ BudK.cb d n k) :
    BudK.tp d n k / 2 + (BudK.Dc d n k / 2 * BudK.R d n k ^ 2 * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      BudK.cb d n k / 2 * BudK.R d n k ^ 2 * ((101 / 100 * sL * X1 + sL * X1) * Du + BudK.DP d n k)) ≤ BudK.ek d n k := by
  subst hDuD hL hX1 hsLe
  unfold BudK.ek
  have a1 : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) ^ 2 + 10201 / 10000 * BudK.Lam d n k ≤
      103 / 100 * BudK.Lam d n k * (BudK.Xi1 d n k ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) ^ 2 =
        10201 / 10000 * (Real.sqrt (BudK.Lam d n k) * Real.sqrt (BudK.Lam d n k)) * BudK.Xi1 d n k ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ BudK.Lam d n k := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg (BudK.Xi1 d n k))]
  have a2 : (101 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k + Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k) * BudK.Du d n k ≤
      203 / 100 * Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k * BudK.Du d n k := by
    have : 0 ≤ Real.sqrt (BudK.Lam d n k) * BudK.Xi1 d n k * BudK.Du d n k := by positivity
    nlinarith
  have hR2 := sq_nonneg (BudK.R d n k)
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg (by positivity : 0 ≤ BudK.Dc d n k / 2) hR2)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 (BudK.DP d n k))
    (mul_nonneg (by positivity : 0 ≤ BudK.cb d n k / 2) hR2)
  have e : BudK.Dc d n k * BudK.R d n k ^ 2 * (103 / 100) * BudK.Lam d n k * (BudK.Xi1 d n k ^ 2 + 1) / 2 =
      BudK.Dc d n k / 2 * BudK.R d n k ^ 2 * (103 / 100 * BudK.Lam d n k * (BudK.Xi1 d n k ^ 2 + 1)) := by ring
  nlinarith


end AdversarialBco.Unified.EngC

/-! ## From `RCHypO` -/

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (clip)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem sett (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    SettK d c.n k (ctxO K c k ap) (deltaO d c.n k) π s st ξ' :=
  ⟨H.hd, H.hn, H.hc, H.bud, H.hs, H.det, H.tau, rfl, rfl, H.track, by rw [← H.par]; exact H.xi⟩

theorem play (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (XO c st ξ') - (ctxO K c k ap).X π s) ≤ BudK.Xb d c.n k :=
  playCO d K c k ap π s st ξ' H.hd H.hn H.par H.hc H.bud H.pg H.hs H.det H.tau H.track H.xi

/-! ### The precision `p` of `c` -/

theorem tpH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : (1 : ℝ) / 2 ^ c.par.p = BudK.tp d c.n k := by
  rw [H.par]; rfl

theorem tp_halfH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (1 : ℝ) / 2 ^ (c.par.p + 1) = BudK.tp d c.n k / 2 := by
  rw [← H.tpH, pow_succ]; field_simp

theorem rnd_errH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (x : ℚ) :
    |((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)| ≤ BudK.tp d c.n k / 2 := by
  rw [← H.tp_halfH]; exact rnd_err_real _ x

theorem rndV_errH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (v : Fin d → ℚ) :
    oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * BudK.tp d c.n k / 2 := by
  have := rndV_err c.par.p v; rw [H.tp_halfH] at this; linarith

theorem nu_eqH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (d : ℝ) * (1 / 2 ^ (c.par.p + 1)) = BudK.nu d c.n k := by
  rw [H.tp_halfH]; unfold BudK.nu; ring

/-! ### `ε'` and the radii -/

theorem eps_relH (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.eps d c.n k ≤ ((c.par.eps : ℚ) : ℝ) ∧
      ((c.par.eps : ℚ) : ℝ) ≤ BudK.eps d c.n k * (1 + BudK.tp d c.n k / 16) := by
  rw [H.par]; exact ⟨H.bud.enc.eps_le, H.bud.enc.eps_rel⟩

theorem eps'_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : ((c.par.eps : ℚ) : ℝ) ≤ 1 / 2 := by
  have h1 := H.eps_relH.2
  have h2 := H.sett.eps_le
  have h3 := NK.tp_small d c.n k
  have h0 := H.sett.eps_pos
  nlinarith

theorem eps'_pos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 < ((c.par.eps : ℚ) : ℝ) :=
  H.sett.eps_pos.trans_le H.eps_relH.1

/-- The position of `c` is good at P°'s radius (`PgGood`). -/
theorem goodPos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : GoodPos K c (poK d c.n k).R := by
  obtain ⟨P, hP, -, h1, h2, -⟩ := H.pg
  simp only [Option.some.injEq] at hP
  subst hP
  exact ⟨h1, h2⟩

theorem one_le_R (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 1 ≤ (poK d c.n k).R := H.det.rows.one_le_R

theorem R_le_par (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : (poK d c.n k).R ≤ ((c.par.R : ℚ) : ℝ) := by
  rw [H.par]; exact H.bud.enc.R_le

theorem parR_le_Rint (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : ((c.par.R : ℚ) : ℝ) ≤ (c.par.Rint : ℝ) := by
  rw [H.par]
  have e : (parK d c.n k).Rint = ⌈(parK d c.n k).R⌉₊ := rfl
  rw [e]
  exact_mod_cast Nat.le_ceil (parK d c.n k).R

/-- P°'s body is the body `S(K)` of the position of `c` (`PgGood`: `S(K) ⊆ B̄(0, R)`). -/
theorem Kt_eq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : (ctxO K c k ap).Kt = bodyS K c := by
  show kTh c.n (deltaO d c.n k) K c.S = bodyS K c
  rw [kTh_good H.pg]
  ext y
  simp only [df2Kp, bodyS, posBody, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := H.goodPos.2 h
    rwa [Metric.mem_closedBall, dist_zero_right] at this

/-! ### E2: the gauge play and the observation -/

theorem kc_pos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 < BudK.kc d c.n k := H.sett.kc_pos

theorem cb0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.cb d c.n k :=
  NK.cb_nonneg H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

theorem Dc0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.Dc d c.n k :=
  NK.Dc_nonneg H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

/-- `2^{-p} Le^{1/2} ≤ 1/100`, from `h_a ≤ ℏ ≤ 1/100`. -/
theorem tp_sqrtLe (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.tp d c.n k * Real.sqrt (BudK.Le d c.n k) ≤ 1 / 100 := by
  have S := H.sett
  have hx0 : 0 ≤ BudK.x d c.n k := by
    unfold BudK.x; have := eN_nonnegK H.Dc0 H.cb0; have := S.Lam_pos; positivity
  have hV0 : 0 ≤ BudK.V d c.n k := by
    unfold BudK.V BudK.nu; have := NK.tp_pos d c.n k; positivity
  have hha0 := NK.ha_nonneg d c.n k
  have hhb : BudK.ha d c.n k ≤ BudK.hb d c.n k := by
    unfold BudK.hb; nlinarith
  have hb := H.bud.hb_le
  have hLe := (NK.Le_pos H.bud).le
  have hs : Real.sqrt (BudK.Le d c.n k) ≤ Real.sqrt (8 * BudK.Le d c.n k) := Real.sqrt_le_sqrt (by linarith)
  have htp := (NK.tp_pos d c.n k).le
  have h1 : BudK.tp d c.n k * Real.sqrt (8 * BudK.Le d c.n k) ≤ BudK.ha d c.n k := by
    unfold BudK.ha; nlinarith
  have h2 := mul_le_mul_of_nonneg_left hs htp
  linarith

/-- E2 for BL-O: `1 ≤ pt' ≤ P̄`, from GAUGE (b) (`gaugeBandO`: `π̃(X') ≤ (1 + 2^{-p-2}) π(X')`), the Lipschitz gauge,
`gauge(X°) ≤ Le^{1/2}`, `|X' - X°| ≤ X̄ ≤ 1/16`, `ε' ≤ 1/2`. -/
theorem pt_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (1 : ℝ) ≤ ((ptO orc c (XO c st ξ') : ℚ) : ℝ) ∧ ((ptO orc c (XO c st ξ') : ℚ) : ℝ) ≤ BudK.Pb d c.n k := by
  have S := H.sett
  set cx := ctxO K c k ap
  have hX := H.play
  have hXb := H.bud.Xb_le
  obtain ⟨-, hg, -⟩ := S.det.evG s S.hs'
  obtain ⟨hconv, -, hball, -, -⟩ := S.det.body
  have hlip := AdversarialBco.Bit.BLP.EngL.gauge_lip1 cx.Kt hconv hball (WithLp.toLp 2 (cV (XO c st ξ')))
    (WithLp.toLp 2 (cx.X π s))
  rw [← WithLp.toLp_sub, ← oNorm_eq] at hlip
  have hgb : gauge cx.Kt (WithLp.toLp 2 (cV (XO c st ξ'))) ≤ Real.sqrt (BudK.Le d c.n k) + 1 / 16 := by
    have : cx.p.Le = BudK.Le d c.n k := rfl
    rw [this] at hg
    have := (abs_le.1 hlip).2
    linarith
  obtain ⟨-, hband⟩ := gaugeBandO d K orc c (poK d c.n k).R (XO c st ξ') H.hd H.frame H.goodPos H.one_le_R
    H.R_le_par H.parR_le_Rint
  have hKt : gauge (bodyS K c) (toE (XO c st ξ')) = gauge cx.Kt (WithLp.toLp 2 (cV (XO c st ξ'))) := by
    rw [H.Kt_eq]; rfl
  rw [hKt] at hband
  have hu : (2 : ℝ)⁻¹ ^ (c.par.p + 2) = BudK.tp d c.n k / 4 := by
    rw [← H.tpH, inv_pow, pow_add]; field_simp; norm_num
  rw [hu] at hband
  have htp := NK.tp_small d c.n k
  have htp0 := NK.tp_pos d c.n k
  have hga : ((gaugeP orc c (XO c st ξ') : ℚ) : ℝ) ≤
      (1 + BudK.tp d c.n k / 4) * (Real.sqrt (BudK.Le d c.n k) + 1 / 16) :=
    hband.trans (mul_le_mul_of_nonneg_left hgb (by positivity))
  have he := H.eps'_le
  have he0 := H.eps'_pos
  have hs := NK.sqrtLe_ge H.bud
  have htL := H.tp_sqrtLe
  unfold ptO
  push_cast
  refine ⟨le_max_left _ _, max_le (by unfold BudK.Pb; linarith) ?_⟩
  rw [div_le_iff₀ (by linarith)]
  unfold BudK.Pb
  have hm : 0 ≤ (2 * Real.sqrt (BudK.Le d c.n k) + 1) * (1 / 2 - ((c.par.eps : ℚ) : ℝ)) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- In mode `run` the play of BL-O is in `K` (`play_int`; the cross check passes by `crossOKO`). -/
theorem play_mem (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : xO orc c st ξ' ∈ K := by
  obtain ⟨hK, -, hr0, -, hball, -, horc⟩ := H.frame
  have hcross : crossOK orc c :=
    crossOKO d K orc c (poK d c.n k).R H.frame H.goodPos H.one_le_R H.R_le_par
  have heps0 : 0 ≤ c.par.eps := by have := H.eps'_pos.le; exact_mod_cast this
  have heps : c.par.eps ≤ 1 / 2 := by
    have h := H.eps'_le
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num] at h
    exact_mod_cast h
  exact interior_subset (play_int hK H.hd (by exact_mod_cast hr0) hball horc hcross heps0 heps (XO c st ξ'))

/-- UNI-OBS on the round: the reading `clip q ⌊2^p (f(x') + ε)⌋` is not clipped and is within `2^{-p}`. -/
theorem obs_eq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    obsO orc c st ξ' f ε = ⌊(2 : ℝ) ^ c.par.p * (f (xO orc c st ξ') + ε)⌋ ∧
      |((obsO orc c st ξ' f ε : ℤ) : ℝ) / 2 ^ c.par.p - (f (xO orc c st ξ') + ε)| ≤ BudK.tp d c.n k := by
  have hf := H.adm.2 _ H.play_mem
  have hNe : 1 ≤ c.par.Ne := by
    rw [H.par]; exact BudK.NeO_pos d c.n k H.hd H.hn
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
  have : (2 : ℝ)⁻¹ ^ c.par.p = BudK.tp d c.n k := by rw [← H.tpH, inv_pow, one_div]
  rw [← this]; exact h2

/-- E2: `|Y' - Y°| ≤ e_Y`, with the noisy reading. -/
theorem eY (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).Y : ℚ) : ℝ) - (ctxO K c k ap).Y π s| ≤ BudK.eY d c.n k := by
  show |(((rvO orc c st ξ' ζ' (obsO orc c st ξ' f ε)).Y : ℚ) : ℝ) - (ctxO K c k ap).Y π s| ≤ BudK.eY d c.n k
  rw [H.Y]
  have hobs := H.obs_eq.2
  set pt : ℝ := ((ptO orc c (XO c st ξ') : ℚ) : ℝ)
  set F := f (xO orc c st ξ') + ε
  set obs := obsO orc c st ξ' f ε
  have hpt := H.pt_le
  have hrnd := H.rnd_errH (ptO orc c (XO c st ξ') * ((obs : ℚ) / 2 ^ c.par.p + ζ') / 2 +
    2 * (ptO orc c (XO c st ξ') - 1) / c.par.eps)
  rw [← rvO_Y] at hrnd
  push_cast at hrnd
  have hz : |(ζ' : ℝ) - Z / 2| ≤ BudK.ezt d c.n k := by
    unfold BudK.ezt; rw [← H.par]; exact H.zt
  have e : (((rvO orc c st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * (F + Z / 2) / 2 + 2 * (pt - 1) / (c.par.eps : ℝ)) =
      ((((rvO orc c st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * ((obs : ℝ) / 2 ^ c.par.p + (ζ' : ℝ)) / 2 +
        2 * (pt - 1) / (c.par.eps : ℝ))) + pt / 2 * (((obs : ℝ) / 2 ^ c.par.p - F) + ((ζ' : ℝ) - Z / 2)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith [hpt.1] : (0 : ℝ) < pt / 2)]
  have h3 : |(obs : ℝ) / 2 ^ c.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤ BudK.tp d c.n k + BudK.ezt d c.n k :=
    (abs_add_le _ _).trans (add_le_add hobs hz)
  have h4 : pt / 2 * |(obs : ℝ) / 2 ^ c.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤
      BudK.Pb d c.n k / 2 * (BudK.tp d c.n k + BudK.ezt d c.n k) :=
    mul_le_mul (by linarith [hpt.2]) h3 (abs_nonneg _) (by unfold BudK.Pb; positivity)
  unfold BudK.eY
  linarith

theorem Dc_small (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : BudK.Dc d c.n k * (1 + BudK.Xi1 d c.n k ^ 2) ≤ 1 / 10 ^ 30 :=
  NK.Dc_small H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

/-- E3 (i): `|c' - c°| ≤ Δ_c`. -/
theorem dc (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ) - (ctxO K c k ap).cc π s| ≤ BudK.Dc d c.n k := by
  have S := H.sett
  rw [S.cc_eq, rvO_c]
  push_cast
  have hk : |((c.par.kapc : ℚ) : ℝ) / BudK.kc d c.n k - 1| ≤ BudK.tp d c.n k / 16 := by
    rw [H.par]; exact H.bud.enc.kapc_rel
  have h := dc_real _ _ _ _ _ _ _ H.kc_pos hk H.eY S.Y_le
  refine h.trans ?_
  have hY0 := NK.Yb_pos H.bud S.eps_pos S.eps_le
  have htp := NK.tp_small d c.n k
  have htp0 := NK.tp_pos d c.n k
  have hz := NK.ezt_le H.hd H.hn H.bud
  have hPb : 0 ≤ BudK.Pb d c.n k := by unfold BudK.Pb; positivity
  have hkc := H.kc_pos
  have heY : (1 + BudK.tp d c.n k / 16) * BudK.eY d c.n k ≤ 11 / 10 * BudK.tp d c.n k * (BudK.Pb d c.n k + 1) := by
    unfold BudK.eY
    have h5 : BudK.tp d c.n k / 2 + BudK.Pb d c.n k / 2 * (BudK.tp d c.n k + BudK.ezt d c.n k) ≤
        BudK.tp d c.n k * (1 / 2 + 3 / 4 * BudK.Pb d c.n k) := by
      have : BudK.Pb d c.n k / 2 * (BudK.tp d c.n k + BudK.ezt d c.n k) ≤ BudK.Pb d c.n k / 2 * (3 / 2 * BudK.tp d c.n k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 1 + BudK.tp d c.n k / 16)
    have h7 : (1 + BudK.tp d c.n k / 16) * (1 / 2 + 3 / 4 * BudK.Pb d c.n k) ≤ 11 / 10 * (BudK.Pb d c.n k + 1) := by nlinarith
    have h8 := mul_le_mul_of_nonneg_left h7 htp0.le
    nlinarith
  have e : BudK.Dc d c.n k = BudK.kc d c.n k * (11 / 10 * BudK.tp d c.n k * (BudK.Pb d c.n k + 1)) +
      BudK.kc d c.n k * (BudK.tp d c.n k / 16) * BudK.Yb d c.n k := by
    unfold BudK.Dc BudK.cb; field_simp
  rw [e]
  have : BudK.kc d c.n k * (1 + BudK.tp d c.n k / 16) * BudK.eY d c.n k ≤ BudK.kc d c.n k * (11 / 10 * BudK.tp d c.n k * (BudK.Pb d c.n k + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left heY hkc.le
  linarith

theorem xx_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 ≤ cV ξ' ⬝ᵥ cV ξ' ∧ cV ξ' ⬝ᵥ cV ξ' ≤ BudK.Xi1 d c.n k ^ 2 := by
  have h := H.sett.xi'_le
  refine ⟨by rw [← oNorm_sq]; positivity, ?_⟩
  rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h 2

theorem xx0_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 ≤ π.xi s ⬝ᵥ π.xi s ∧ π.xi s ⬝ᵥ π.xi s ≤ BudK.Xi1 d c.n k ^ 2 := by
  have h := H.sett.xi_le1
  refine ⟨?_, ?_⟩
  · rw [← oNorm_sq]; positivity
  · rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h 2

theorem dxx (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |cV ξ' ⬝ᵥ cV ξ' - π.xi s ⬝ᵥ π.xi s| ≤ 2 * BudK.Xi1 d c.n k * BudK.exi d c.n k := by
  have S := H.sett
  refine (dot_sq_diff _ _).trans ?_
  have hx := (NK.Xi1_pos d c.n k).le
  exact mul_le_mul (by linarith [S.xi'_le, S.xi_le1]) S.dxi_le (oNorm_nonneg _) (by positivity)

theorem q_cast (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) = 1 - (((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ) +
      (((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ) * (cV ξ' ⬝ᵥ cV ξ') := by
  rw [rvO_q, rvO_a]; push_cast; rw [cV_dot]

theorem qq_eq (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (ctxO K c k ap).qq π s = 1 - (ctxO K c k ap).cc π s +
      (ctxO K c k ap).cc π s * (π.xi s ⬝ᵥ π.xi s) := rfl

/-- E16: `|q' - q°| ≤ Δ_q`. -/
theorem dq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) - (ctxO K c k ap).qq π s| ≤ BudK.Dq d c.n k := by
  rw [H.q_cast, H.qq_eq]
  have h := q_diff _ _ _ _ _ (π.xi s ⬝ᵥ π.xi s) _ H.sett.cc_le H.dc H.xx_le.1 H.xx_le.2
  refine h.trans ?_
  unfold BudK.Dq
  have := mul_le_mul_of_nonneg_left H.dxx H.cb0
  have hexi : 0 ≤ BudK.exi d c.n k := by unfold BudK.exi; positivity
  have : 0 ≤ BudK.cb d c.n k * BudK.Xi1 d c.n k * BudK.exi d c.n k := by have := (NK.Xi1_pos d c.n k).le; have := H.cb0; positivity
  nlinarith

theorem c'_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ)| ≤ BudK.cb d c.n k + BudK.Dc d c.n k := by
  have h1 := H.dc; have h2 := H.sett.cc_le
  have := abs_add_le ((((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ) - (ctxO K c k ap).cc π s)
    ((ctxO K c k ap).cc π s)
  rw [sub_add_cancel] at this; linarith

/-- GUARD (E18), R7: `a', q' ≥ 1/2`. -/
theorem ga (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ¬ ((rvH orc c st ξ' ζ' ε f).a < 1 / 2 ∨ (rvH orc c st ξ' ζ' ε f).q < 1 / 2) := by
  have hc := H.c'_le
  have h1 := H.bud.cb_le
  have h2 := H.Dc_small
  have hxx := H.xx_le
  have hX := sq_nonneg (BudK.Xi1 d c.n k)
  have hcX : (BudK.cb d c.n k + BudK.Dc d c.n k) * (1 + BudK.Xi1 d c.n k ^ 2) ≤ 2 / 10 ^ 30 := by nlinarith
  have hcb1 : BudK.cb d c.n k + BudK.Dc d c.n k ≤ 2 / 10 ^ 30 := by nlinarith
  set c' := (((rvH orc c st ξ' ζ' ε f).c : ℚ) : ℝ)
  have ha : (1 / 2 : ℝ) ≤ (((rvH orc c st ξ' ζ' ε f).a : ℚ) : ℝ) := by
    rw [rvO_a]; push_cast
    have := (abs_le.1 hc).2; linarith
  have hq : (1 / 2 : ℝ) ≤ (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) := by
    rw [H.q_cast]
    have hcx : |c' * (cV ξ' ⬝ᵥ cV ξ')| ≤ (BudK.cb d c.n k + BudK.Dc d c.n k) * BudK.Xi1 d c.n k ^ 2 := by
      rw [abs_mul, abs_of_nonneg hxx.1]; exact mul_le_mul hc hxx.2 hxx.1 (by linarith [abs_nonneg c'])
    have := (abs_le.1 hcx).1; have := (abs_le.1 hc).2
    nlinarith
  rw [not_or, not_lt, not_lt]
  constructor
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact ha)
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact hq)


theorem a_ge (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (1 / 2 : ℝ) ≤ (((rvH orc c st ξ' ζ' ε f).a : ℚ) : ℝ) ∧
      (1 / 2 : ℝ) ≤ (((rvH orc c st ξ' ζ' ε f).q : ℚ) : ℝ) := by
  have h := H.ga
  rw [not_or, not_lt, not_lt] at h
  refine ⟨?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 h.1; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h.2; push_cast at this; exact this

theorem sqrt_hyp (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtDn c.par.p x : ℚ) : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Real.sqrt (x : ℝ) < ((sqrtDn c.par.p x : ℚ) : ℝ) + BudK.tp d c.n k := by
  rw [← H.tpH]; exact sqrtDn_err _ hx

/-- The real scalars of E3 (ii): BL's roots and quotients against their exact values at BL's inputs. -/
theorem scal (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    let r := rvH orc c st ξ' ζ' ε f
    let c' : ℝ := ((r.c : ℚ) : ℝ)
    let xx' := cV ξ' ⬝ᵥ cV ξ'
    ((r.s1 : ℝ) ≤ Real.sqrt (1 / (1 - c')) ∧ Real.sqrt (1 / (1 - c')) < (r.s1 : ℝ) + BudK.tp d c.n k) ∧
    ((r.s3 : ℝ) ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < (r.s3 : ℝ) + BudK.tp d c.n k) ∧
    ((r.rq : ℝ) ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < (r.rq : ℝ) + BudK.tp d c.n k) ∧
    |(r.s2 : ℝ) - c' / ((r.s3 : ℝ) * (r.rq : ℝ) * ((r.s3 : ℝ) + (r.rq : ℝ)))| ≤ BudK.tp d c.n k / 2 ∧
    |(r.s4 : ℝ) - c' / ((r.s3 : ℝ) + (r.rq : ℝ))| ≤ BudK.tp d c.n k / 2 := by
  intro r c' xx'
  have ha := H.a_ge
  have ha0 : (0 : ℚ) ≤ r.a := by exact_mod_cast (by linarith [ha.1] : (0 : ℝ) ≤ (r.a : ℝ))
  have hq0 : (0 : ℚ) ≤ r.q := by exact_mod_cast (by linarith [ha.2] : (0 : ℝ) ≤ (r.q : ℝ))
  have h1 := H.sqrt_hyp (1 / r.a) (by positivity)
  have h3 := H.sqrt_hyp r.a ha0
  have h4 := H.sqrt_hyp r.q hq0
  have e1 : (((1 / r.a : ℚ)) : ℝ) = 1 / (1 - c') := by rw [rvO_a]; push_cast; rfl
  have e3 : ((r.a : ℚ) : ℝ) = 1 - c' := by rw [rvO_a]; push_cast; rfl
  have e4 : ((r.q : ℚ) : ℝ) = 1 - c' + c' * xx' := H.q_cast
  rw [e1] at h1; rw [e3] at h3; rw [e4] at h4
  refine ⟨h1, h3, h4, ?_, ?_⟩
  · have := H.rnd_errH (r.c / (r.s3 * r.rq * (r.s3 + r.rq)))
    rw [← rvO_s2] at this
    push_cast at this; exact this
  · have := H.rnd_errH (r.c / (r.s3 + r.rq))
    rw [← rvO_s4] at this
    push_cast at this; exact this

/-- P°'s coefficient `φ = c/((a q)^{1/2}(a^{1/2} + q^{1/2}))` and `ψ = c/(a^{1/2} + q^{1/2})` of round `s`. -/
noncomputable def phi (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : ℝ :=
  c.cc π s / (Real.sqrt (c.aa π s) * Real.sqrt (c.qq π s) * (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s)))

noncomputable def psi (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : ℝ :=
  c.cc π s / (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))

/-- E3: `|N' - N°| ≤ e_N` for the factor of `A`. -/
theorem e3A (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    opN ((((rvH orc c st ξ' ζ' ε f).s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-(((rvH orc c st ξ' ζ' ε f).s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ') -
      ((Real.sqrt ((ctxO K c k ap).aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-phi (ctxO K c k ap) π s) • vecMulVec (π.xi s) (π.xi s))) ≤ BudK.eN d c.n k := by
  have S := H.sett
  obtain ⟨h1, h3, h4, h2, -⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.bud.cb_le
  have hΔ := H.Dc_small
  have htp0 := (NK.tp_pos d c.n k).le
  have htp := NK.tp_small d c.n k
  have hxx := H.xx_le
  have hxx0 := H.xx0_le
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have i1 := e3_scal_inv _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h1
  have i2 := e3_scal_phi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h2
  have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).1
  have h := e3_mat (π.xi s) (cV ξ') _ (-(((rvH orc c st ξ' ζ' ε f).s2 : ℚ) : ℝ)) _
    (-phi (ctxO K c k ap) π s) (BudK.Xi1 d c.n k) (BudK.exi d c.n k) (BudK.tp d c.n k + BudK.Dc d c.n k)
    (51 / 100 * BudK.tp d c.n k + BudK.Dc d c.n k + BudK.cb d c.n k * BudK.Dq d c.n k) (BudK.cb d c.n k) S.xi_le1 S.xi'_le S.dxi_le i1
    (by rw [neg_sub_neg, abs_sub_comm]; exact i2) (by rw [abs_neg]; exact i3)
  exact h.trans (eN_geK H.bud H.Dc0 H.cb0)

/-- E3: `|N'^{inv} - (N°)^{-1}| ≤ e_N` for the factor of `B`. -/
theorem e3B (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    opN ((((rvH orc c st ξ' ζ' ε f).s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (((rvH orc c st ξ' ζ' ε f).s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ') -
      (Real.sqrt ((ctxO K c k ap).aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        psi (ctxO K c k ap) π s • vecMulVec (π.xi s) (π.xi s))) ≤ BudK.eN d c.n k := by
  have S := H.sett
  obtain ⟨-, h3, h4, -, h5⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.bud.cb_le
  have hΔ := H.Dc_small
  have htp0 := (NK.tp_pos d c.n k).le
  have htp := NK.tp_small d c.n k
  have hxx := H.xx_le
  have hxx0 := H.xx0_le
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have i1 := e3_scal_sqrt _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h3
  have i2 := e3_scal_psi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h5
  have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).2
  have h := e3_mat (π.xi s) (cV ξ') _ _ _ (psi (ctxO K c k ap) π s) (BudK.Xi1 d c.n k) (BudK.exi d c.n k)
    (BudK.tp d c.n k + BudK.Dc d c.n k) (51 / 100 * BudK.tp d c.n k + BudK.Dc d c.n k + BudK.cb d c.n k * BudK.Dq d c.n k) (BudK.cb d c.n k) S.xi_le1 S.xi'_le S.dxi_le
    i1 i2 i3
  exact h.trans (eN_geK H.bud H.Dc0 H.cb0)


end AdversarialBco.Unified.Eng.RCHypO
