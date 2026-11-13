/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundSet
public import AdversarialBco.Bit.BLRoundPlay
public import AdversarialBco.Bit.BLEngLeaves

@[expose] public section

/-!
# Piece C, part C1: BL's round arithmetic against P°'s update

E2 (the observation), E3 (the factor), E4 (the rounding of the pair), the tracking lemma at `s + 1` for `A'` and `B'`,
E7 to E11 (`u`, `P`, the fields `b, k, G, l`), E16's `Δ_q` and the guards R7 and R10, each
against P°'s update of round `s` (`An`, `Pn An`, `bn`, `kn`, `Gn`, `ln`). Conclusion: `c1 : C1Stmt`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh)
open AdversarialBco.Bit.Asm (deltaBL RunCase)
open AdversarialBco.RealRAM (polytope)
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## BL's values, line by line -/

section rv

variable (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)

theorem rv_Y : (rv cfg st ξ ζ obs).Y = rnd cfg.par.p (ptQ cfg (XQ cfg st ξ) * ((obs : ℚ) / 2 ^ cfg.par.p + ζ) / 2 +
    2 * (ptQ cfg (XQ cfg st ξ) - 1) / cfg.par.eps) := rfl
theorem rv_c : (rv cfg st ξ ζ obs).c = cfg.par.kapc * (rv cfg st ξ ζ obs).Y := rfl
theorem rv_a : (rv cfg st ξ ζ obs).a = 1 - (rv cfg st ξ ζ obs).c := rfl
theorem rv_q : (rv cfg st ξ ζ obs).q = (rv cfg st ξ ζ obs).a + (rv cfg st ξ ζ obs).c * (ξ ⬝ᵥ ξ) := rfl
theorem rv_s2 : (rv cfg st ξ ζ obs).s2 = rnd cfg.par.p ((rv cfg st ξ ζ obs).c /
    ((rv cfg st ξ ζ obs).s3 * (rv cfg st ξ ζ obs).rq * ((rv cfg st ξ ζ obs).s3 + (rv cfg st ξ ζ obs).rq))) := rfl
theorem rv_s4 : (rv cfg st ξ ζ obs).s4 = rnd cfg.par.p ((rv cfg st ξ ζ obs).c /
    ((rv cfg st ξ ζ obs).s3 + (rv cfg st ξ ζ obs).rq)) := rfl
theorem rv_G : (rv cfg st ξ ζ obs).G = st.G + (rv cfg st ξ ζ obs).g := rfl

end rv

/-! ## Generic tools -/

theorem tp_eq (d n : ℕ) : (1 : ℝ) / 2 ^ (par d n).p = Bud.tp d n := rfl

theorem tp_half (d n : ℕ) : (1 : ℝ) / 2 ^ ((par d n).p + 1) = Bud.tp d n / 2 := by
  unfold Bud.tp; rw [pow_succ]; field_simp

theorem rnd_err_tp (d n : ℕ) (x : ℚ) : |((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ)| ≤ Bud.tp d n / 2 := by
  rw [← tp_half]; exact rnd_err_real _ x

theorem rndV_err (k : ℕ) (v : Fin d → ℚ) : oNorm (cV (rndV k v) - cV v) ≤ Real.sqrt d * (1 / 2 ^ (k + 1)) :=
  oNorm_le_of_abs_le _ _ fun i => by simpa [cV, rndV] using rnd_err_real k (v i)

theorem rndM_err (k : ℕ) (M : Matrix (Fin d) (Fin d) ℚ) : opN (cM (rndM k M) - cM M) ≤ d * (1 / 2 ^ (k + 1)) :=
  opN_le_of_abs_le _ _ fun i j => by simpa [cM, rndM] using rnd_err_real k (M i j)

theorem fac_mul (A : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) (s1 s2 : ℝ) :
    s1 • A + s2 • vecMulVec (A *ᵥ ξ) ξ = A * (s1 • (1 : Matrix (Fin d) (Fin d) ℝ) + s2 • vecMulVec ξ ξ) := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  congr 2
  ext i j
  simp [vecMulVec_apply, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem dot_sq_diff (x y : Fin d → ℝ) : |x ⬝ᵥ x - y ⬝ᵥ y| ≤ (oNorm x + oNorm y) * oNorm (x - y) := by
  have e : x ⬝ᵥ x - y ⬝ᵥ y = (x - y) ⬝ᵥ (x + y) := by
    simp only [sub_dotProduct, dotProduct_add]; rw [dotProduct_comm y x]; ring
  rw [e]
  refine (abs_dot_le _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (oNorm_add_le x y) (oNorm_nonneg _)

theorem inc_g (y' y0 U Du : ℝ) (u' u0 : Fin d → ℝ) (hu' : oNorm u' ≤ U) (hdu : oNorm (u' - u0) ≤ Du) :
    oNorm (y' • u' - y0 • u0) ≤ |y' - y0| * U + |y0| * Du := by
  have e : y' • u' - y0 • u0 = (y' - y0) • u' + y0 • (u' - u0) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  refine (oNorm_add_le _ _).trans ?_
  rw [oNorm_smul, oNorm_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left hu' (abs_nonneg _)) (mul_le_mul_of_nonneg_left hdu (abs_nonneg _))

/-- `|Y'ν' - Y/(1 - λ)| ≤ 1.01 (e_Y + Ȳ 2^{-p-4})`. -/
theorem ynu (Y' Y ν l eY Yb t : ℝ) (hY : |Y' - Y| ≤ eY) (hYb : |Y| ≤ Yb) (hν : |ν * (1 - l) - 1| ≤ t / 16)
    (hl : 0 < 1 - l) (h1 : (1 + t / 16) / (1 - l) ≤ 101 / 100) (h2 : 1 / (1 - l) ≤ 101 / 100) (ht : 0 ≤ t) :
    |Y' * ν - Y / (1 - l)| ≤ 101 / 100 * (eY + Yb * t / 16) := by
  set δ := ν * (1 - l) - 1 with hδ
  have hνe : ν = (1 + δ) / (1 - l) := by rw [hδ]; field_simp; ring
  have e : Y' * ν - Y / (1 - l) = ((Y' - Y) * (1 + δ) + Y * δ) / (1 - l) := by rw [hνe]; field_simp; ring
  rw [e, abs_div, abs_of_pos hl]
  have hδ1 : |1 + δ| ≤ 1 + t / 16 := by
    calc |1 + δ| ≤ |1| + |δ| := abs_add_le _ _
      _ ≤ 1 + t / 16 := by rw [abs_one]; linarith
  have heY : 0 ≤ eY := (abs_nonneg _).trans hY
  have hYb0 : 0 ≤ Yb := (abs_nonneg _).trans hYb
  have hn : |(Y' - Y) * (1 + δ) + Y * δ| ≤ eY * (1 + t / 16) + Yb * (t / 16) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul hY hδ1 (abs_nonneg _) heY) (mul_le_mul hYb hν (abs_nonneg _) hYb0)
  rw [div_le_iff₀ hl]
  have h1' : 1 + t / 16 ≤ 101 / 100 * (1 - l) := by rwa [div_le_iff₀ hl] at h1
  have h2' : 1 ≤ 101 / 100 * (1 - l) := by rwa [div_le_iff₀ hl] at h2
  have : eY * (1 + t / 16) + Yb * (t / 16) ≤ 101 / 100 * (eY + Yb * t / 16) * (1 - l) := by
    have a1 : eY * (1 + t / 16) ≤ eY * (101 / 100 * (1 - l)) := mul_le_mul_of_nonneg_left h1' heY
    have a2 : Yb * (t / 16) ≤ Yb * (t / 16) * (101 / 100 * (1 - l)) := by
      have : 0 ≤ Yb * (t / 16) := by positivity
      nlinarith
    nlinarith
  linarith

/-! ## From `RCHyp` -/

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem sett (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Sett d n (ctx R d n m A b cs ap) (deltaBL d n) π s st ξ' :=
  ⟨H.hd, H.hn, H.hc, H.bud, H.hs, H.det, H.tau, rfl, rfl, H.track, H.xi⟩

theorem play (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (XQ (cfgOf R d n m A b cs) st ξ') - (ctx R d n m A b cs ap).X π s) ≤ Bud.Xb d n :=
  playC R d n m A b cs ap π s st ξ' H.hd H.hn H.hc H.bud H.pg H.hs H.det H.tau H.track H.xi

theorem eps'_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : (((par d n).eps : ℚ) : ℝ) ≤ 1 / 2 := by
  have h1 := H.bud.enc.eps_rel
  have h2 := H.sett.eps_le
  have h3 := Bud.tp_small d n
  have h0 := H.sett.eps_pos
  nlinarith

theorem eps'_pos (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 < (((par d n).eps : ℚ) : ℝ) :=
  H.sett.eps_pos.trans_le H.bud.enc.eps_le

/-- E2: `1 ≤ pt' ≤ P̄`, from `gauge(X°) ≤ Le^{1/2}`, `|X' - X°| ≤ X̄ ≤ 1/16`, `B̄(0, 1) ⊆ K~`, `ε' ≤ 1/2`. -/
theorem pt_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (1 : ℝ) ≤ ((ptQ (cfgOf R d n m A b cs) (XQ (cfgOf R d n m A b cs) st ξ') : ℚ) : ℝ) ∧
      ((ptQ (cfgOf R d n m A b cs) (XQ (cfgOf R d n m A b cs) st ξ') : ℚ) : ℝ) ≤ Bud.Pb d n := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set cfg := cfgOf R d n m A b cs
  have hX := H.play
  have hXb := H.bud.Xb_le
  obtain ⟨-, hg, -⟩ := S.det.evG s S.hs'
  obtain ⟨hconv, -, hball, -, -⟩ := S.det.body
  have hlip := AdversarialBco.Bit.BLP.EngL.gauge_lip1 c.Kt hconv hball (WithLp.toLp 2 (cV (XQ cfg st ξ')))
    (WithLp.toLp 2 (c.X π s))
  rw [← WithLp.toLp_sub, ← oNorm_eq] at hlip
  have hga : ((gaugeQ cfg (XQ cfg st ξ') : ℚ) : ℝ) ≤ Real.sqrt (Bud.Le d n) + 1 / 16 := by
    rw [H.gauge]
    have : c.p.Le = Bud.Le d n := rfl
    rw [this] at hg
    have := (abs_le.1 hlip).2
    show _root_.gauge c.Kt _ ≤ _
    linarith
  have he := H.eps'_le
  have he0 := H.eps'_pos
  have hs := Bud.sqrtLe_ge H.bud
  unfold ptQ
  push_cast
  refine ⟨le_max_left _ _, max_le (by unfold Bud.Pb; linarith) ?_⟩
  have hcp : (cfg.par.eps : ℝ) = (((par d n).eps : ℚ) : ℝ) := rfl
  rw [hcp, div_le_iff₀ (by linarith)]
  unfold Bud.Pb
  nlinarith

/-- E2: `|Y' - Y°| ≤ e_Y`. -/
theorem eY (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rv (cfgOf R d n m A b cs) st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)).Y : ℚ) : ℝ) -
      (ctx R d n m A b cs ap).Y π s| ≤ Bud.eY d n := by
  rw [H.Y]
  set cfg := cfgOf R d n m A b cs
  set pt : ℝ := ((ptQ cfg (XQ cfg st ξ') : ℚ) : ℝ)
  set F := f (toE (playPt cfg (.run st) ξ'))
  set obs := obsQ cfg st ξ' f
  have hpt := H.pt_le
  have hp : cfg.par.p = (par d n).p := rfl
  have hrnd := rnd_err_tp d n (ptQ cfg (XQ cfg st ξ') * ((obs : ℚ) / 2 ^ cfg.par.p + ζ') / 2 +
    2 * (ptQ cfg (XQ cfg st ξ') - 1) / cfg.par.eps)
  rw [← hp, ← rv_Y] at hrnd
  push_cast at hrnd
  have hobs : |(obs : ℝ) / 2 ^ cfg.par.p - F| ≤ Bud.tp d n := by
    have h1 : (obs : ℝ) ≤ 2 ^ cfg.par.p * F := Int.floor_le ((2 : ℝ) ^ cfg.par.p * F)
    have h2 : 2 ^ cfg.par.p * F < obs + 1 := Int.lt_floor_add_one ((2 : ℝ) ^ cfg.par.p * F)
    have h0 : (0 : ℝ) < 2 ^ cfg.par.p := by positivity
    have e : (obs : ℝ) / 2 ^ cfg.par.p - F = ((obs : ℝ) - 2 ^ cfg.par.p * F) / 2 ^ cfg.par.p := by field_simp
    rw [e, abs_div, abs_of_pos h0]
    unfold Bud.tp; rw [← hp]
    apply div_le_div_of_nonneg_right _ h0.le
    rw [abs_le]; constructor <;> linarith
  have hz := H.zt
  have hzt : eZt0 d n = Bud.ezt d n := rfl
  rw [hzt] at hz
  have e : (((rv cfg st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * (F + Z / 2) / 2 + 2 * (pt - 1) / (cfg.par.eps : ℝ)) =
      ((((rv cfg st ξ' ζ' obs).Y : ℚ) : ℝ) - (pt * ((obs : ℝ) / 2 ^ cfg.par.p + (ζ' : ℝ)) / 2 +
        2 * (pt - 1) / (cfg.par.eps : ℝ))) + pt / 2 * (((obs : ℝ) / 2 ^ cfg.par.p - F) + ((ζ' : ℝ) - Z / 2)) := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith [hpt.1] : (0 : ℝ) < pt / 2)]
  have h3 : |(obs : ℝ) / 2 ^ cfg.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤ Bud.tp d n + Bud.ezt d n :=
    (abs_add_le _ _).trans (add_le_add hobs hz)
  have h4 : pt / 2 * |(obs : ℝ) / 2 ^ cfg.par.p - F + ((ζ' : ℝ) - Z / 2)| ≤ Bud.Pb d n / 2 * (Bud.tp d n + Bud.ezt d n) :=
    mul_le_mul (by linarith [hpt.2]) h3 (abs_nonneg _) (by unfold Bud.Pb; positivity)
  unfold Bud.eY
  linarith


end RCHyp

/-- E3 (i): `|κ_c' Y' - κ_c Y| ≤ κ_c (1 + 2^{-p-4}) e_Y + κ_c 2^{-p-4} Ȳ`. -/
theorem dc_real (k' k Y' Y eY Yb t : ℝ) (hk : 0 < k) (hkr : |k' / k - 1| ≤ t / 16) (hY : |Y' - Y| ≤ eY)
    (hYb : |Y| ≤ Yb) : |k' * Y' - k * Y| ≤ k * (1 + t / 16) * eY + k * (t / 16) * Yb := by
  have e1 : k' - k = k * (k' / k - 1) := by field_simp
  have hkk : |k' - k| ≤ k * (t / 16) := by rw [e1, abs_mul, abs_of_pos hk]; exact mul_le_mul_of_nonneg_left hkr hk.le
  have hk' : |k'| ≤ k * (1 + t / 16) := by
    have : |k'| ≤ |k| + |k' - k| := by
      have := abs_add_le k (k' - k); rwa [add_sub_cancel] at this
    rw [abs_of_pos hk] at this; linarith
  have e : k' * Y' - k * Y = k' * (Y' - Y) + (k' - k) * Y := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have heY : 0 ≤ eY := (abs_nonneg _).trans hY
  have ht : 0 ≤ k * (t / 16) := (abs_nonneg _).trans hkk
  exact add_le_add (mul_le_mul hk' hY (abs_nonneg _) (by linarith [abs_nonneg k']))
    (mul_le_mul hkk hYb (abs_nonneg _) ht)

/-- E16: `|q' - q°| ≤ Δ_c (1 + Ξ₁²) + c̄ |ξ'ᵀξ' - ξᵀξ|`. -/
theorem q_diff (c c' Δ cb X1 xx xx' : ℝ) (hc : |c| ≤ cb) (hcc : |c' - c| ≤ Δ) (hxx' : 0 ≤ xx')
    (hxx1' : xx' ≤ X1 ^ 2) :
    |(1 - c' + c' * xx') - (1 - c + c * xx)| ≤ Δ * (1 + X1 ^ 2) + cb * |xx' - xx| := by
  have e : (1 - c' + c' * xx') - (1 - c + c * xx) = -(c' - c) + (c' - c) * xx' + c * (xx' - xx) := by ring
  rw [e]
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans hcc
  have t1 := abs_add_le (-(c' - c) + (c' - c) * xx') (c * (xx' - xx))
  have t2 := abs_add_le (-(c' - c)) ((c' - c) * xx')
  rw [abs_neg, abs_mul, abs_of_nonneg hxx'] at t2
  rw [abs_mul] at t1
  have h1 : |c' - c| * xx' ≤ Δ * X1 ^ 2 := mul_le_mul hcc hxx1' hxx' hΔ
  have h2 : |c| * |xx' - xx| ≤ cb * |xx' - xx| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  nlinarith

/-- The constant `e_N` of E3 bounds the error of the factor. -/
theorem eN_ge {d n : ℕ} (h : Bud.BudOK d n) (hDc : 0 ≤ Bud.Dc d n) (hcb : 0 ≤ Bud.cb d n) :
    (Bud.tp d n + Bud.Dc d n) + (51 / 100 * Bud.tp d n + Bud.Dc d n + Bud.cb d n * Bud.Dq d n) * Bud.Xi1 d n ^ 2 +
      Bud.cb d n * (2 * Bud.Xi1 d n) * Bud.exi d n ≤ Bud.eN d n := by
  have hc := h.cb_le
  have htp := (Bud.tp_pos d n).le
  have hx := (Bud.Xi1_pos d n).le
  have hexi : 0 ≤ Bud.exi d n := by unfold Bud.exi; positivity
  have hX2 : 0 ≤ Bud.Xi1 d n ^ 2 := sq_nonneg _
  have hcX : Bud.cb d n * Bud.Xi1 d n ^ 2 ≤ 1 / 10 ^ 30 := by nlinarith
  unfold Bud.eN Bud.Dq
  have a1 : Bud.cb d n * (Bud.Dc d n * (1 + Bud.Xi1 d n ^ 2) + 202 / 100 * Bud.cb d n * Bud.Xi1 d n * Bud.exi d n) *
      Bud.Xi1 d n ^ 2 ≤ 1 / 10 ^ 30 * (Bud.Dc d n * (1 + Bud.Xi1 d n ^ 2)) +
        1 / 10 ^ 30 * (202 / 100 * Bud.cb d n * Bud.Xi1 d n * Bud.exi d n) := by
    have : Bud.cb d n * (Bud.Dc d n * (1 + Bud.Xi1 d n ^ 2) + 202 / 100 * Bud.cb d n * Bud.Xi1 d n * Bud.exi d n) *
        Bud.Xi1 d n ^ 2 = (Bud.cb d n * Bud.Xi1 d n ^ 2) *
          (Bud.Dc d n * (1 + Bud.Xi1 d n ^ 2) + 202 / 100 * Bud.cb d n * Bud.Xi1 d n * Bud.exi d n) := by ring
    rw [this, ← mul_add]
    exact mul_le_mul_of_nonneg_right hcX (by positivity)
  nlinarith [mul_nonneg hDc hX2, mul_nonneg (mul_nonneg hcb hx) hexi, mul_nonneg htp hX2]

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

/-- BL's values of round `s` in the setting of `RCHyp`. -/
noncomputable abbrev rvH (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (st : St d) (ξ' : Fin d → ℚ) (ζ' : ℚ) (f : E d → ℝ) : RV d :=
  rv (cfgOf R d n m A b cs) st ξ' ζ' (obsQ (cfgOf R d n m A b cs) st ξ' f)

theorem kc_pos (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 < Bud.kc d n := H.sett.kc_pos

theorem cb0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.cb d n :=
  Bud.cb_nonneg H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

theorem Dc0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.Dc d n :=
  Bud.Dc_nonneg H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

theorem Dc_small (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : Bud.Dc d n * (1 + Bud.Xi1 d n ^ 2) ≤ 1 / 10 ^ 30 :=
  Bud.Dc_small H.bud H.sett.eps_pos H.sett.eps_le H.kc_pos.le

/-- E3 (i): `|c' - c°| ≤ Δ_c`. -/
theorem dc (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ) - (ctx R d n m A b cs ap).cc π s| ≤ Bud.Dc d n := by
  have S := H.sett
  rw [S.cc_eq, rv_c]
  push_cast
  have hk := H.bud.enc.kapc_rel
  have h := dc_real _ _ _ _ _ _ _ H.kc_pos hk H.eY S.Y_le
  refine h.trans ?_
  have hY0 := Bud.Yb_pos H.bud S.eps_pos S.eps_le
  have htp := Bud.tp_small d n
  have htp0 := Bud.tp_pos d n
  have hz := Bud.ezt_le H.hd H.hn H.bud
  have hPb : 0 ≤ Bud.Pb d n := by unfold Bud.Pb; positivity
  have hkc := H.kc_pos
  have heY : (1 + Bud.tp d n / 16) * Bud.eY d n ≤ 11 / 10 * Bud.tp d n * (Bud.Pb d n + 1) := by
    unfold Bud.eY
    have h5 : Bud.tp d n / 2 + Bud.Pb d n / 2 * (Bud.tp d n + Bud.ezt d n) ≤
        Bud.tp d n * (1 / 2 + 3 / 4 * Bud.Pb d n) := by
      have : Bud.Pb d n / 2 * (Bud.tp d n + Bud.ezt d n) ≤ Bud.Pb d n / 2 * (3 / 2 * Bud.tp d n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 1 + Bud.tp d n / 16)
    have h7 : (1 + Bud.tp d n / 16) * (1 / 2 + 3 / 4 * Bud.Pb d n) ≤ 11 / 10 * (Bud.Pb d n + 1) := by nlinarith
    have h8 := mul_le_mul_of_nonneg_left h7 htp0.le
    nlinarith
  have e : Bud.Dc d n = Bud.kc d n * (11 / 10 * Bud.tp d n * (Bud.Pb d n + 1)) +
      Bud.kc d n * (Bud.tp d n / 16) * Bud.Yb d n := by
    unfold Bud.Dc Bud.cb; field_simp
  rw [e]
  have : Bud.kc d n * (1 + Bud.tp d n / 16) * Bud.eY d n ≤ Bud.kc d n * (11 / 10 * Bud.tp d n * (Bud.Pb d n + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left heY hkc.le
  linarith

theorem xx_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 ≤ cV ξ' ⬝ᵥ cV ξ' ∧ cV ξ' ⬝ᵥ cV ξ' ≤ Bud.Xi1 d n ^ 2 := by
  have h := H.sett.xi'_le
  refine ⟨by rw [← oNorm_sq]; positivity, ?_⟩
  rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h 2

theorem xx0_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 ≤ π.xi s ⬝ᵥ π.xi s ∧ π.xi s ⬝ᵥ π.xi s ≤ Bud.Xi1 d n ^ 2 := by
  have h := H.sett.xi_le1
  refine ⟨?_, ?_⟩
  · rw [← oNorm_sq]; positivity
  · rw [← oNorm_sq]; exact pow_le_pow_left₀ (oNorm_nonneg _) h 2

theorem dxx (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |cV ξ' ⬝ᵥ cV ξ' - π.xi s ⬝ᵥ π.xi s| ≤ 2 * Bud.Xi1 d n * Bud.exi d n := by
  have S := H.sett
  refine (dot_sq_diff _ _).trans ?_
  have hx := (Bud.Xi1_pos d n).le
  exact mul_le_mul (by linarith [S.xi'_le, S.xi_le1]) S.dxi_le (oNorm_nonneg _) (by positivity)

theorem q_cast (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) = 1 - (((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ) +
      (((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ) * (cV ξ' ⬝ᵥ cV ξ') := by
  rw [rv_q, rv_a]; push_cast; rw [cV_dot]

theorem qq_eq (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (ctx R d n m A b cs ap).qq π s = 1 - (ctx R d n m A b cs ap).cc π s +
      (ctx R d n m A b cs ap).cc π s * (π.xi s ⬝ᵥ π.xi s) := rfl

/-- E16: `|q' - q°| ≤ Δ_q`. -/
theorem dq (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) - (ctx R d n m A b cs ap).qq π s| ≤ Bud.Dq d n := by
  rw [H.q_cast, H.qq_eq]
  have h := q_diff _ _ _ _ _ (π.xi s ⬝ᵥ π.xi s) _ H.sett.cc_le H.dc H.xx_le.1 H.xx_le.2
  refine h.trans ?_
  unfold Bud.Dq
  have := mul_le_mul_of_nonneg_left H.dxx H.cb0
  have hexi : 0 ≤ Bud.exi d n := by unfold Bud.exi; positivity
  have : 0 ≤ Bud.cb d n * Bud.Xi1 d n * Bud.exi d n := by have := (Bud.Xi1_pos d n).le; have := H.cb0; positivity
  nlinarith

theorem c'_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ)| ≤ Bud.cb d n + Bud.Dc d n := by
  have h1 := H.dc; have h2 := H.sett.cc_le
  have := abs_add_le ((((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ) - (ctx R d n m A b cs ap).cc π s)
    ((ctx R d n m A b cs ap).cc π s)
  rw [sub_add_cancel] at this; linarith

/-- GUARD (E18), R7: `a', q' ≥ 1/2`. -/
theorem ga (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ¬ ((rvH R d n m A b cs st ξ' ζ' f).a < 1 / 2 ∨ (rvH R d n m A b cs st ξ' ζ' f).q < 1 / 2) := by
  have hc := H.c'_le
  have h1 := H.bud.cb_le
  have h2 := H.Dc_small
  have hxx := H.xx_le
  have hX := sq_nonneg (Bud.Xi1 d n)
  have hcX : (Bud.cb d n + Bud.Dc d n) * (1 + Bud.Xi1 d n ^ 2) ≤ 2 / 10 ^ 30 := by nlinarith
  have hcb1 : Bud.cb d n + Bud.Dc d n ≤ 2 / 10 ^ 30 := by nlinarith
  set c' := (((rvH R d n m A b cs st ξ' ζ' f).c : ℚ) : ℝ)
  have ha : (1 / 2 : ℝ) ≤ (((rvH R d n m A b cs st ξ' ζ' f).a : ℚ) : ℝ) := by
    rw [rv_a]; push_cast
    have := (abs_le.1 hc).2; linarith
  have hq : (1 / 2 : ℝ) ≤ (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) := by
    rw [H.q_cast]
    have hcx : |c' * (cV ξ' ⬝ᵥ cV ξ')| ≤ (Bud.cb d n + Bud.Dc d n) * Bud.Xi1 d n ^ 2 := by
      rw [abs_mul, abs_of_nonneg hxx.1]; exact mul_le_mul hc hxx.2 hxx.1 (by linarith [abs_nonneg c'])
    have := (abs_le.1 hcx).1; have := (abs_le.1 hc).2
    nlinarith
  rw [not_or, not_lt, not_lt]
  constructor
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact ha)
  · exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact hq)


theorem a_ge (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (1 / 2 : ℝ) ≤ (((rvH R d n m A b cs st ξ' ζ' f).a : ℚ) : ℝ) ∧
      (1 / 2 : ℝ) ≤ (((rvH R d n m A b cs st ξ' ζ' f).q : ℚ) : ℝ) := by
  have h := H.ga
  rw [not_or, not_lt, not_lt] at h
  refine ⟨?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 h.1; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h.2; push_cast at this; exact this

theorem sqrt_hyp (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (x : ℚ) (hx : 0 ≤ x) :
    ((sqrtDn (par d n).p x : ℚ) : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Real.sqrt (x : ℝ) < ((sqrtDn (par d n).p x : ℚ) : ℝ) + Bud.tp d n := by
  rw [← tp_eq]; exact sqrtDn_err _ hx

/-- The real scalars of E3 (ii): BL's roots and quotients against their exact values at BL's inputs. -/
theorem scal (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    let r := rvH R d n m A b cs st ξ' ζ' f
    let c' : ℝ := ((r.c : ℚ) : ℝ)
    let xx' := cV ξ' ⬝ᵥ cV ξ'
    ((r.s1 : ℝ) ≤ Real.sqrt (1 / (1 - c')) ∧ Real.sqrt (1 / (1 - c')) < (r.s1 : ℝ) + Bud.tp d n) ∧
    ((r.s3 : ℝ) ≤ Real.sqrt (1 - c') ∧ Real.sqrt (1 - c') < (r.s3 : ℝ) + Bud.tp d n) ∧
    ((r.rq : ℝ) ≤ Real.sqrt (1 - c' + c' * xx') ∧ Real.sqrt (1 - c' + c' * xx') < (r.rq : ℝ) + Bud.tp d n) ∧
    |(r.s2 : ℝ) - c' / ((r.s3 : ℝ) * (r.rq : ℝ) * ((r.s3 : ℝ) + (r.rq : ℝ)))| ≤ Bud.tp d n / 2 ∧
    |(r.s4 : ℝ) - c' / ((r.s3 : ℝ) + (r.rq : ℝ))| ≤ Bud.tp d n / 2 := by
  intro r c' xx'
  have ha := H.a_ge
  have ha0 : (0 : ℚ) ≤ r.a := by exact_mod_cast (by linarith [ha.1] : (0 : ℝ) ≤ (r.a : ℝ))
  have hq0 : (0 : ℚ) ≤ r.q := by exact_mod_cast (by linarith [ha.2] : (0 : ℝ) ≤ (r.q : ℝ))
  have h1 := H.sqrt_hyp (1 / r.a) (by positivity)
  have h3 := H.sqrt_hyp r.a ha0
  have h4 := H.sqrt_hyp r.q hq0
  have e1 : (((1 / r.a : ℚ)) : ℝ) = 1 / (1 - c') := by rw [rv_a]; push_cast; rfl
  have e3 : ((r.a : ℚ) : ℝ) = 1 - c' := by rw [rv_a]; push_cast; rfl
  have e4 : ((r.q : ℚ) : ℝ) = 1 - c' + c' * xx' := H.q_cast
  rw [e1] at h1; rw [e3] at h3; rw [e4] at h4
  refine ⟨h1, h3, h4, ?_, ?_⟩
  · have := rnd_err_tp d n (r.c / (r.s3 * r.rq * (r.s3 + r.rq)))
    rw [← show (cfgOf R d n m A b cs).par.p = (par d n).p from rfl, ← rv_s2] at this
    push_cast at this; exact this
  · have := rnd_err_tp d n (r.c / (r.s3 + r.rq))
    rw [← show (cfgOf R d n m A b cs).par.p = (par d n).p from rfl, ← rv_s4] at this
    push_cast at this; exact this

/-- P°'s coefficient `φ = c/((a q)^{1/2}(a^{1/2} + q^{1/2}))` and `ψ = c/(a^{1/2} + q^{1/2})` of round `s`. -/
noncomputable def phi (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : ℝ :=
  c.cc π s / (Real.sqrt (c.aa π s) * Real.sqrt (c.qq π s) * (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s)))

noncomputable def psi (c : Df2Ctx d) (π : Df2Path d) (s : ℕ) : ℝ :=
  c.cc π s / (Real.sqrt (c.aa π s) + Real.sqrt (c.qq π s))

/-- E3: `|N' - N°| ≤ e_N` for the factor of `A`. -/
theorem e3A (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    opN ((((rvH R d n m A b cs st ξ' ζ' f).s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-(((rvH R d n m A b cs st ξ' ζ' f).s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ') -
      ((Real.sqrt ((ctx R d n m A b cs ap).aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (-phi (ctx R d n m A b cs ap) π s) • vecMulVec (π.xi s) (π.xi s))) ≤ Bud.eN d n := by
  have S := H.sett
  obtain ⟨h1, h3, h4, h2, -⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.bud.cb_le
  have hΔ := H.Dc_small
  have htp0 := (Bud.tp_pos d n).le
  have htp := Bud.tp_small d n
  have hxx := H.xx_le
  have hxx0 := H.xx0_le
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have i1 := e3_scal_inv _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h1
  have i2 := e3_scal_phi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h2
  have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).1
  have h := e3_mat (π.xi s) (cV ξ') _ (-(((rvH R d n m A b cs st ξ' ζ' f).s2 : ℚ) : ℝ)) _
    (-phi (ctx R d n m A b cs ap) π s) (Bud.Xi1 d n) (Bud.exi d n) (Bud.tp d n + Bud.Dc d n)
    (51 / 100 * Bud.tp d n + Bud.Dc d n + Bud.cb d n * Bud.Dq d n) (Bud.cb d n) S.xi_le1 S.xi'_le S.dxi_le i1
    (by rw [neg_sub_neg, abs_sub_comm]; exact i2) (by rw [abs_neg]; exact i3)
  exact h.trans (eN_ge H.bud H.Dc0 H.cb0)

/-- E3: `|N'^{inv} - (N°)^{-1}| ≤ e_N` for the factor of `B`. -/
theorem e3B (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    opN ((((rvH R d n m A b cs st ξ' ζ' f).s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (((rvH R d n m A b cs st ξ' ζ' f).s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ') -
      (Real.sqrt ((ctx R d n m A b cs ap).aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
        psi (ctx R d n m A b cs ap) π s • vecMulVec (π.xi s) (π.xi s))) ≤ Bud.eN d n := by
  have S := H.sett
  obtain ⟨-, h3, h4, -, h5⟩ := H.scal
  have hc := S.cc_le
  have hcc := H.dc
  have hcb := H.bud.cb_le
  have hΔ := H.Dc_small
  have htp0 := (Bud.tp_pos d n).le
  have htp := Bud.tp_small d n
  have hxx := H.xx_le
  have hxx0 := H.xx0_le
  have hdq := H.dq
  rw [H.q_cast, H.qq_eq] at hdq
  have i1 := e3_scal_sqrt _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp h3
  have i2 := e3_scal_psi _ _ _ _ _ _ _ _ _ _ _ _ hc hcc hcb hΔ htp0 htp hxx0.1 hxx0.2 hxx.1 hxx.2 hdq h3 h4 h5
  have i3 := (e3_coef_le _ _ _ _ hc hcb hxx0.1 hxx0.2).2
  have h := e3_mat (π.xi s) (cV ξ') _ _ _ (psi (ctx R d n m A b cs ap) π s) (Bud.Xi1 d n) (Bud.exi d n)
    (Bud.tp d n + Bud.Dc d n) (51 / 100 * Bud.tp d n + Bud.Dc d n + Bud.cb d n * Bud.Dq d n) (Bud.cb d n) S.xi_le1 S.xi'_le S.dxi_le
    i1 i2 i3
  exact h.trans (eN_ge H.bud H.Dc0 H.cb0)

end RCHyp

/-! ## The tracking lemma at `s + 1` -/

theorem nu_eq (d n : ℕ) : (d : ℝ) * (1 / 2 ^ ((par d n).p + 1)) = Bud.nu d n := by
  rw [tp_half]; unfold Bud.nu; ring

/-- The step of TRACK in numbers: `h + (1 + h)|A0||N' - N||Ai| + |ρ||Ai| ≤ hTr (s + 1)`. -/
theorem track_num {d n : ℕ} (s : ℕ) (h a1 a2 n1 r : ℝ) (hh0 : 0 ≤ h) (hh : h ≤ Bud.hTr d n s) (ha1 : 0 ≤ a1)
    (ha1' : a1 ≤ Real.sqrt (Bud.Lam d n)) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ Real.sqrt (Bud.Lam d n)) (hn1 : 0 ≤ n1)
    (hn1' : n1 ≤ Bud.eN d n) (hr : 0 ≤ r) (hr' : r ≤ Bud.nu d n) (hL : 0 ≤ Bud.Lam d n) :
    h + (1 + h) * a1 * n1 * a2 + r * a2 ≤ Bud.hTr d n (s + 1) := by
  have hsq : Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n) = Bud.Lam d n := Real.mul_self_sqrt hL
  have heN : 0 ≤ Bud.eN d n := hn1.trans hn1'
  have hnu : 0 ≤ Bud.nu d n := hr.trans hr'
  have hs0 := Real.sqrt_nonneg (Bud.Lam d n)
  have t1 : a1 * n1 * a2 ≤ Bud.Lam d n * Bud.eN d n := by
    calc a1 * n1 * a2 ≤ Real.sqrt (Bud.Lam d n) * Bud.eN d n * Real.sqrt (Bud.Lam d n) :=
          mul_le_mul (mul_le_mul ha1' hn1' hn1 hs0) ha2' ha2 (by positivity)
      _ = Bud.Lam d n * Bud.eN d n := by
        rw [show Real.sqrt (Bud.Lam d n) * Bud.eN d n * Real.sqrt (Bud.Lam d n) =
          (Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n)) * Bud.eN d n by ring, hsq]
  have t2 : r * a2 ≤ Real.sqrt (Bud.Lam d n) * Bud.nu d n := by
    rw [mul_comm (Real.sqrt _)]; exact mul_le_mul hr' ha2' ha2 hnu
  have hT0 : 0 ≤ Bud.hTr d n s := hh0.trans hh
  have step := hTr_step (Bud.ha d n) (Bud.Lam d n * Bud.eN d n) (Real.sqrt (Bud.Lam d n) * Bud.nu d n)
    (Bud.hTr d n s) s (by positivity) (by positivity) hT0 (le_of_eq (by unfold Bud.hTr; ring))
  have e : Bud.hTr d n (s + 1) = (1 + Bud.ha d n + ((s + 1 : ℕ) : ℝ) * (Real.sqrt (Bud.Lam d n) * Bud.nu d n)) *
      (1 + Bud.Lam d n * Bud.eN d n) ^ (s + 1) - 1 := by unfold Bud.hTr; ring
  rw [e]
  have t3 : (1 + h) * a1 * n1 * a2 ≤ (1 + Bud.hTr d n s) * (Bud.Lam d n * Bud.eN d n) := by
    rw [mul_assoc, mul_assoc]
    rw [← mul_assoc a1]
    exact mul_le_mul (by linarith) t1 (by positivity) (by linarith)
  linarith

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem hT (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) (k : ℕ) (hk : k ≤ n) : Bud.hTr d n k ≤ 1 / 100 :=
  (H.bud.hTr_le k hk).trans H.bud.hb_le

/-- E4 and TRACK for `A`: `A'_+ = (I + H') A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackA (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvH R d n m A b cs st ξ' ζ' f).A = (1 + H') * (ctx R d n m A b cs ap).An π s ∧
      opN H' ≤ Bud.hTr d n (s + 1) := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  set M := r.s1 • st.A - r.s2 • vecMulVec (st.A *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-((r.s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := (Real.sqrt (c.aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-phi c π s) • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.A * N' := by
    rw [cM_sub, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, sub_eq_add_neg, ← neg_smul, fac_mul]
  have hr : cM r.A = (1 + H0) * (c.st π s).A * N' + (cM r.A - cM M) := by
    rw [← hA0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm (c.st π s).A (c.An π s) ((c.An π s)ᵀ * c.Pn π s) N0 N' (cM r.A - cM M) H0
    S.An_fac S.An_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.A - cM M) ≤ Bud.nu d n := by
    rw [← nu_eq]; exact rndM_err _ M
  exact track_num s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_A0 (opN_nonneg _) S.opN_AnPn
    (opN_nonneg _) H.e3A (opN_nonneg _) hρ S.Lam_pos.le

/-- E4 and TRACK for `B`: `B'_+ = (I + H') P°_{s+1} A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackB (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvH R d n m A b cs st ξ' ζ' f).B =
      (1 + H') * ((ctx R d n m A b cs ap).Pn π s * (ctx R d n m A b cs ap).An π s) ∧
      opN H' ≤ Bud.hTr d n (s + 1) := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  set M := r.s3 • st.B + r.s4 • vecMulVec (st.B *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    ((r.s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := Real.sqrt (c.aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    psi c π s • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.B * N' := by
    rw [cM_add, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, fac_mul]
  have hr : cM r.B = (1 + H0) * ((c.st π s).P * (c.st π s).A) * N' + (cM r.B - cM M) := by
    rw [← hB0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm ((c.st π s).P * (c.st π s).A) (c.Pn π s * c.An π s) (c.An π s)ᵀ N0 N'
    (cM r.B - cM M) H0 S.PnAn_fac S.PnAn_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.B - cM M) ≤ Bud.nu d n := by
    rw [← nu_eq]; exact rndM_err _ M
  exact track_num s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_PA0 (opN_nonneg _)
    (by rw [opN_transpose]; exact S.opN_An) (opN_nonneg _) H.e3B (opN_nonneg _) hρ S.Lam_pos.le

theorem frob2_cast (M : Matrix (Fin d) (Fin d) ℚ) : ((frob2 M : ℚ) : ℝ) = ∑ i, ∑ j, (cM M i j) ^ 2 := by
  simp [frob2, cM]

/-- GUARD (E18), R10: the traces of `A'_+ A'_+ᵀ` and `B'_+ B'_+ᵀ` are at most `(1 + ℏ)² Λ ≤ 2Λ`. -/
theorem gt (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ¬ (2 * ((cfgOf R d n m A b cs).par.Lam : ℚ) < frob2 (rvH R d n m A b cs st ξ' ζ' f).B ∨
      2 * ((cfgOf R d n m A b cs).par.Lam : ℚ) < frob2 (rvH R d n m A b cs st ξ' ζ' f).A) := by
  have S := H.sett
  have hL : (((cfgOf R d n m A b cs).par.Lam : ℕ) : ℝ) = Bud.Lam d n := H.bud.enc.Lam_eq
  have hb := H.hT (s + 1) H.hs
  have hLp := S.Lam_pos
  have key : ∀ X : Matrix (Fin d) (Fin d) ℚ, ∀ Y : Matrix (Fin d) (Fin d) ℝ,
      (∃ H' : Matrix (Fin d) (Fin d) ℝ, cM X = (1 + H') * Y ∧ opN H' ≤ Bud.hTr d n (s + 1)) →
      (Y * Yᵀ).trace ≤ Bud.Lam d n → ¬ (2 * ((cfgOf R d n m A b cs).par.Lam : ℚ) < frob2 X) := by
    intro X Y ⟨H', e, hH'⟩ hY
    rw [not_lt]
    have h := frob_le_of H' Y _ _ (hH'.trans hb) hY
    rw [← e] at h
    have : ((frob2 X : ℚ) : ℝ) ≤ ((2 * ((cfgOf R d n m A b cs).par.Lam : ℚ) : ℚ) : ℝ) := by
      rw [frob2_cast]; push_cast; rw [hL]; nlinarith
    exact_mod_cast this
  rw [not_or]
  refine ⟨key _ _ H.trackB ?_, key _ _ H.trackA ?_⟩
  · rw [S.PnAn_sq]; exact S.trn.1
  · rw [S.R1.2.2.1]; exact S.trn.2

end RCHyp

/-! ## E7, E8: `u`, `w` and `P` -/

/-- `|(I + H) M x' - M x| ≤ Λ^{1/2}(ℏ Ξ₁ + e_ξ)`. -/
theorem fac_vec_err (M H : Matrix (Fin d) (Fin d) ℝ) (x x' : Fin d → ℝ) (sL X1 ex hb : ℝ) (hM : opN M ≤ sL)
    (hH : opN H ≤ hb) (hx' : oNorm x' ≤ X1) (hdx : oNorm (x' - x) ≤ ex) :
    oNorm (((1 + H) * M) *ᵥ x' - M *ᵥ x) ≤ sL * (hb * X1 + ex) := by
  have e : ((1 + H) * M) *ᵥ x' - M *ᵥ x = H *ᵥ (M *ᵥ x') + M *ᵥ (x' - x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]; abel
  rw [e]
  have h0 := opN_nonneg M
  have hb0 : 0 ≤ hb := (opN_nonneg H).trans hH
  have h1 : oNorm (H *ᵥ (M *ᵥ x')) ≤ hb * (sL * X1) :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hH ((oNorm_mulVec_le _ _).trans
      (mul_le_mul hM hx' (oNorm_nonneg _) (h0.trans hM))) (oNorm_nonneg _) hb0)
  have h2 : oNorm (M *ᵥ (x' - x)) ≤ sL * ex :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hM hdx (oNorm_nonneg _) (h0.trans hM))
  have := oNorm_add_le (H *ᵥ (M *ᵥ x')) (M *ᵥ (x' - x))
  nlinarith

/-- `(I + H) P (I + H)ᵀ - P` in norm: at most `(2h + h²)|P|`. -/
theorem PP_err (P H : Matrix (Fin d) (Fin d) ℝ) (h L : ℝ) (hH : opN H ≤ h) (hP : opN P ≤ L) :
    opN ((1 + H) * P * (1 + H)ᵀ - P) ≤ (2 * h + h ^ 2) * L ∧ opN ((1 + H) * P * (1 + H)ᵀ) ≤ (1 + h) ^ 2 * L := by
  have hh0 : 0 ≤ h := (opN_nonneg H).trans hH
  have hL0 : 0 ≤ L := (opN_nonneg P).trans hP
  have hHt : opN Hᵀ ≤ h := by rw [opN_transpose]; exact hH
  have e : (1 + H) * P * (1 + H)ᵀ - P = H * P + P * Hᵀ + H * P * Hᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have m1 : opN (H * P) ≤ h * L := (opN_mul_le _ _).trans (mul_le_mul hH hP (opN_nonneg _) hh0)
  have m2 : opN (P * Hᵀ) ≤ L * h := (opN_mul_le _ _).trans (mul_le_mul hP hHt (opN_nonneg _) hL0)
  have m3 : opN (H * P * Hᵀ) ≤ h * L * h :=
    (opN_mul_le _ _).trans (mul_le_mul m1 hHt (opN_nonneg _) (by positivity))
  have s1 : opN ((1 + H) * P * (1 + H)ᵀ - P) ≤ (2 * h + h ^ 2) * L := by
    rw [e]
    have := opN_add_le (H * P + P * Hᵀ) (H * P * Hᵀ)
    have := opN_add_le (H * P) (P * Hᵀ)
    nlinarith
  refine ⟨s1, ?_⟩
  have := opN_add_le ((1 + H) * P * (1 + H)ᵀ - P) P
  rw [sub_add_cancel] at this
  nlinarith

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem hb0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.hb d n := Bud.hb_nonneg H.bud

theorem hTs (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : Bud.hTr d n s ≤ Bud.hb d n := H.bud.hTr_le s H.hs.le

/-- E7: `|w' - w°| ≤ Δ_u`. -/
theorem ew (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (st.A *ᵥ ξ') - (ctx R d n m A b cs ap).w π s) ≤ Bud.Du d n := by
  have S := H.sett
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  rw [cM_mulVec, hA0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_A0 (hH0.trans H.hTs) S.xi'_le S.dxi_le

/-- `u' = B'ξ'` as a real vector. -/
theorem u'_eq (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : cV (st.B *ᵥ ξ') = cM st.B *ᵥ cV ξ' := cM_mulVec _ _

theorem u0_eq (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    (ctx R d n m A b cs ap).u π s =
      (((ctx R d n m A b cs ap).st π s).P * ((ctx R d n m A b cs ap).st π s).A) *ᵥ π.xi s := by
  rw [← Matrix.mulVec_mulVec]; rfl

/-- E7: `|u' - u°| ≤ Δ_u`. -/
theorem du (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (st.B *ᵥ ξ') - (ctx R d n m A b cs ap).u π s) ≤ Bud.Du d n := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  rw [H.u'_eq, H.u0_eq, hB0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_PA0 (hH0.trans H.hTs) S.xi'_le S.dxi_le

theorem u0_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm ((ctx R d n m A b cs ap).u π s) ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n := by
  have S := H.sett
  rw [H.u0_eq]
  exact (oNorm_mulVec_le _ _).trans (mul_le_mul S.opN_PA0 S.xi_le1 (oNorm_nonneg _) (Real.sqrt_nonneg _))

theorem Du_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Bud.Du d n ≤ 1 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n + Real.sqrt (Bud.Lam d n) * Bud.exi d n := by
  unfold Bud.Du
  have := H.bud.hb_le; have := (Bud.Xi1_pos d n).le; have := Real.sqrt_nonneg (Bud.Lam d n)
  nlinarith [mul_le_mul_of_nonneg_right H.bud.hb_le (mul_nonneg (Real.sqrt_nonneg (Bud.Lam d n)) (Bud.Xi1_pos d n).le)]

theorem u'_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (st.B *ᵥ ξ')) ≤ 101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n := by
  have S := H.sett
  have h1 := H.du
  have h2 : oNorm ((ctx R d n m A b cs ap).u π s) ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi d n := by
    rw [H.u0_eq]
    exact (oNorm_mulVec_le _ _).trans (mul_le_mul S.opN_PA0 S.xi_le (oNorm_nonneg _) (Real.sqrt_nonneg _))
  have h3 := oNorm_add_le ((ctx R d n m A b cs ap).u π s) (cV (st.B *ᵥ ξ') - (ctx R d n m A b cs ap).u π s)
  rw [add_sub_cancel] at h3
  have h4 := H.Du_le
  have hs := Real.sqrt_nonneg (Bud.Lam d n)
  have h5 : Real.sqrt (Bud.Lam d n) * Bud.Xi d n + Real.sqrt (Bud.Lam d n) * Bud.exi d n ≤
      Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n := by
    rw [← mul_add]; unfold Bud.Xi1; exact mul_le_mul_of_nonneg_left (by linarith [S.exi_le_one]) hs
  linarith

/-- BL's `P' = B'B'ᵀ` of round `s`. -/
theorem P'_err (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    opN (cM st.B * (cM st.B)ᵀ - ((ctx R d n m A b cs ap).st π s).P) ≤ Bud.DP d n ∧
      opN (cM st.B * (cM st.B)ᵀ) ≤ 10201 / 10000 * Bud.Lam d n := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  have e : cM st.B * (cM st.B)ᵀ = (1 + H0) * ((ctx R d n m A b cs ap).st π s).P * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * (((ctx R d n m A b cs ap).st π s).P * ((ctx R d n m A b cs ap).st π s).A) *
          ((((ctx R d n m A b cs ap).st π s).P * ((ctx R d n m A b cs ap).st π s).A)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * ((((ctx R d n m A b cs ap).st π s).P * ((ctx R d n m A b cs ap).st π s).A) *
          (((ctx R d n m A b cs ap).st π s).P * ((ctx R d n m A b cs ap).st π s).A)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PA_sq]
  rw [e]
  have hb := H.bud.hb_le
  have hb0 := H.hb0
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans H.hTs) S.opN_P0
  refine ⟨h1.trans (le_of_eq (by unfold Bud.DP; ring)), h2.trans ?_⟩
  have : (1 + Bud.hb d n) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

theorem P'_mulVec (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    cV (st.B *ᵥ (st.Bᵀ *ᵥ st.mu)) = (cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu := by
  rw [cM_mulVec, cM_mulVec, cM_transpose, Matrix.mulVec_mulVec]

theorem vv_eq (_H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    ((((st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu) : ℚ)) : ℝ) = cV st.mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu) := by
  rw [cV_dot, cM_mulVec, cM_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (cV st.mu),
    ← Matrix.mulVec_transpose]

theorem mu_le (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : oNorm (cV st.mu) ≤ Bud.R d n := by
  have S := H.sett
  rw [S.track.mu]
  exact S.det.norm_le_of_keps S.inv.mu

theorem R0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.R d n := (oNorm_nonneg _).trans H.mu_le

end RCHyp

/-! ## E9 and E11: the fields -/

theorem eb_ge {d n : ℕ} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = Bud.Du d n) (hL : L = Bud.Lam d n) (hsLe : sL = Real.sqrt (Bud.Lam d n)) (hX1 : X1 = Bud.Xi1 d n)
    (hDc : 0 ≤ Bud.Dc d n) (hR : 0 ≤ Bud.R d n) (hcb : 0 ≤ Bud.cb d n) :
    Real.sqrt d * Bud.tp d n / 2 + (Bud.Dc d n * Bud.R d n * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      Bud.cb d n * Bud.R d n * ((101 / 100 * sL * X1 + sL * X1) * Du + Bud.DP d n)) ≤ Bud.eb d n := by
  subst hDuD hL hX1 hsLe
  unfold Bud.eb
  have a1 : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) ^ 2 + 10201 / 10000 * Bud.Lam d n ≤
      103 / 100 * Bud.Lam d n * (Bud.Xi1 d n ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) ^ 2 =
        10201 / 10000 * (Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n)) * Bud.Xi1 d n ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ Bud.Lam d n := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg (Bud.Xi1 d n))]
  have a2 : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n + Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) * Bud.Du d n ≤
      203 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n * Bud.Du d n := by
    have : 0 ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n * Bud.Du d n := by positivity
    nlinarith
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg hDc hR)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 (Bud.DP d n)) (mul_nonneg hcb hR)
  nlinarith

theorem ek_ge {d n : ℕ} (sL L X1 Du : ℝ) (hsL : sL * sL = L) (hsL0 : 0 ≤ sL) (hX : 0 ≤ X1) (hDu : 0 ≤ Du)
    (hDuD : Du = Bud.Du d n) (hL : L = Bud.Lam d n) (hsLe : sL = Real.sqrt (Bud.Lam d n)) (hX1 : X1 = Bud.Xi1 d n)
    (hDc : 0 ≤ Bud.Dc d n) (_hR : 0 ≤ Bud.R d n) (hcb : 0 ≤ Bud.cb d n) :
    Bud.tp d n / 2 + (Bud.Dc d n / 2 * Bud.R d n ^ 2 * ((101 / 100 * sL * X1) ^ 2 + 10201 / 10000 * L) +
      Bud.cb d n / 2 * Bud.R d n ^ 2 * ((101 / 100 * sL * X1 + sL * X1) * Du + Bud.DP d n)) ≤ Bud.ek d n := by
  subst hDuD hL hX1 hsLe
  unfold Bud.ek
  have a1 : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) ^ 2 + 10201 / 10000 * Bud.Lam d n ≤
      103 / 100 * Bud.Lam d n * (Bud.Xi1 d n ^ 2 + 1) := by
    have : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) ^ 2 =
        10201 / 10000 * (Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n)) * Bud.Xi1 d n ^ 2 := by ring
    rw [this, hsL]
    have hL0 : 0 ≤ Bud.Lam d n := by rw [← hsL]; positivity
    nlinarith [mul_nonneg hL0 (sq_nonneg (Bud.Xi1 d n))]
  have a2 : (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n + Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) * Bud.Du d n ≤
      203 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n * Bud.Du d n := by
    have : 0 ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n * Bud.Du d n := by positivity
    nlinarith
  have hR2 := sq_nonneg (Bud.R d n)
  have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg (by positivity : 0 ≤ Bud.Dc d n / 2) hR2)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add_right a2 (Bud.DP d n))
    (mul_nonneg (by positivity : 0 ≤ Bud.cb d n / 2) hR2)
  have e : Bud.Dc d n * Bud.R d n ^ 2 * (103 / 100) * Bud.Lam d n * (Bud.Xi1 d n ^ 2 + 1) / 2 =
      Bud.Dc d n / 2 * Bud.R d n ^ 2 * (103 / 100 * Bud.Lam d n * (Bud.Xi1 d n ^ 2 + 1)) := by ring
  nlinarith

namespace RCHyp

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z : ℝ} {f : E d → ℝ}

theorem Du0 (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) : 0 ≤ Bud.Du d n := (oNorm_nonneg _).trans H.du

theorem sLam (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    Real.sqrt (Bud.Lam d n) * Real.sqrt (Bud.Lam d n) = Bud.Lam d n := Real.mul_self_sqrt H.sett.Lam_pos.le

/-- E9 for `b`. -/
theorem errb (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (rvH R d n m A b cs st ξ' ζ' f).b - (ctx R d n m A b cs ap).bn π s) ≤ (s + 1) * Bud.eb d n := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  set v : Fin d → ℚ := r.c • (((st.B *ᵥ ξ') ⬝ᵥ st.mu) • (st.B *ᵥ ξ') - st.B *ᵥ (st.Bᵀ *ᵥ st.mu))
  have hv : cV v = ((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu) := by
    simp only [v]; rw [cV_smul, cV_sub, cV_smul, cV_dot, H.P'_mulVec, S.track.mu]
  have e : cV r.b - c.bn π s = (cV st.b - (c.st π s).b) + (cV (rndV (par d n).p v) - cV v) +
      (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) • cV (st.B *ᵥ ξ') -
        (cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu) -
        c.cc π s • ((c.u π s ⬝ᵥ (c.st π s).mu) • c.u π s - (c.st π s).P *ᵥ (c.st π s).mu)) := by
    have hb : r.b = st.b + rndV (par d n).p v := rfl
    rw [hb, cV_add, ← hv]; unfold Df2Ctx.bn; abel
  rw [e]
  have h1 := S.track.errb
  have h2 : oNorm (cV (rndV (par d n).p v) - cV v) ≤ Real.sqrt d * Bud.tp d n / 2 := by
    have := rndV_err (par d n).p v; rw [tp_half] at this; linarith
  have hP := H.P'_err
  have h3 := inc_b (cV (st.B *ᵥ ξ')) (c.u π s) (c.st π s).mu (cM st.B * (cM st.B)ᵀ) (c.st π s).P
    ((r.c : ℚ) : ℝ) (c.cc π s) (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n)
    (Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) (Bud.Du d n) (10201 / 10000 * Bud.Lam d n) (Bud.DP d n) (Bud.R d n)
    (Bud.Dc d n) (Bud.cb d n) H.u'_le H.u0_le H.du hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
  have h4 := eb_ge (d := d) (n := n) _ _ _ _ H.sLam (Real.sqrt_nonneg _) (Bud.Xi1_pos d n).le H.Du0 rfl rfl rfl rfl
    H.Dc0 H.R0 H.cb0
  have t1 := oNorm_add_le (cV st.b - (c.st π s).b + (cV (rndV (par d n).p v) - cV v))
    (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu) -
      c.cc π s • ((c.u π s ⬝ᵥ (c.st π s).mu) • c.u π s - (c.st π s).P *ᵥ (c.st π s).mu))
  have t2 := oNorm_add_le (cV st.b - (c.st π s).b) (cV (rndV (par d n).p v) - cV v)
  nlinarith

/-- E9 for `k`. -/
theorem errk (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rvH R d n m A b cs st ξ' ζ' f).k : ℚ) : ℝ) - (ctx R d n m A b cs ap).kn π s| ≤ (s + 1) * Bud.ek d n := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  set x : ℚ := r.c / 2 * (((st.B *ᵥ ξ') ⬝ᵥ st.mu) ^ 2 - (st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu))
  have hx : ((x : ℚ) : ℝ) = ((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) ^ 2 -
      (c.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu)) := by
    simp only [x]; push_cast; rw [cV_dot, H.vv_eq, S.track.mu]
  have e : ((r.k : ℚ) : ℝ) - c.kn π s = ((st.k : ℝ) - (c.st π s).k) + (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ)) +
      (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) ^ 2 -
        (c.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu)) - c.cc π s / 2 * ((c.u π s ⬝ᵥ (c.st π s).mu) ^ 2 -
        (c.st π s).mu ⬝ᵥ ((c.st π s).P *ᵥ (c.st π s).mu))) := by
    have hk : r.k = st.k + rnd (par d n).p x := rfl
    rw [hk, ← hx]; push_cast; unfold Df2Ctx.kn; ring
  rw [e]
  have h1 := S.track.errk
  have h2 := rnd_err_tp d n x
  have hP := H.P'_err
  have h3 := inc_k (cV (st.B *ᵥ ξ')) (c.u π s) (c.st π s).mu (cM st.B * (cM st.B)ᵀ) (c.st π s).P
    ((r.c : ℚ) : ℝ) (c.cc π s) (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n)
    (Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) (Bud.Du d n) (10201 / 10000 * Bud.Lam d n) (Bud.DP d n) (Bud.R d n)
    (Bud.Dc d n) (Bud.cb d n) H.u'_le H.u0_le H.du hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
  have h4 := ek_ge (d := d) (n := n) _ _ _ _ H.sLam (Real.sqrt_nonneg _) (Bud.Xi1_pos d n).le H.Du0 rfl rfl rfl rfl
    H.Dc0 H.R0 H.cb0
  have t1 := abs_add_le (((st.k : ℝ) - (c.st π s).k) + (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ)))
    (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (c.st π s).mu) ^ 2 -
      (c.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (c.st π s).mu)) -
      c.cc π s / 2 * ((c.u π s ⬝ᵥ (c.st π s).mu) ^ 2 - (c.st π s).mu ⬝ᵥ ((c.st π s).P *ᵥ (c.st π s).mu)))
  have t2 := abs_add_le ((st.k : ℝ) - (c.st π s).k) (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ))
  nlinarith


theorem lam_facts (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    0 < 1 - (po d n).lam ∧ (1 + Bud.tp d n / 16) / (1 - (po d n).lam) ≤ 101 / 100 ∧
      1 / (1 - (po d n).lam) ≤ 101 / 100 := by
  have hl := H.sett.lam_small
  have hl0 := H.sett.lam_pos
  have ht := Bud.tp_small d n
  have h1 : 0 < 1 - (po d n).lam := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_iff₀ h1]; nlinarith

/-- E11: BL's increment `g'` of `G` against `ĝ°`. -/
theorem g_err (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (rvH R d n m A b cs st ξ' ζ' f).g - (ctx R d n m A b cs ap).ghat π s) ≤ Bud.eg d n := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  set v : Fin d → ℚ := (r.Y * (par d n).nu) • (st.B *ᵥ ξ')
  have hg : r.g = rndV (par d n).p v := rfl
  have hv : cV v = ((r.Y : ℝ) * ((par d n).nu : ℝ)) • cV (st.B *ᵥ ξ') := by
    simp only [v]; rw [cV_smul]; push_cast; rfl
  have e : cV r.g - c.ghat π s = (cV (rndV (par d n).p v) - cV v) +
      (((r.Y : ℝ) * ((par d n).nu : ℝ)) • cV (st.B *ᵥ ξ') - (c.Y π s / (1 - c.p.lam)) • c.u π s) := by
    rw [hg, ← hv]; unfold Df2Ctx.ghat; abel
  rw [e]
  have h2 : oNorm (cV (rndV (par d n).p v) - cV v) ≤ Real.sqrt d * Bud.tp d n / 2 := by
    have := rndV_err (par d n).p v; rw [tp_half] at this; linarith
  obtain ⟨hl, hl1, hl2⟩ := H.lam_facts
  have hcp : (po d n).lam = c.p.lam := rfl
  rw [hcp] at hl hl1 hl2
  have hnu := H.bud.enc.nu_rel
  have hy := ynu (r.Y : ℝ) (c.Y π s) ((par d n).nu : ℝ) c.p.lam (Bud.eY d n) (Bud.Yb d n) (Bud.tp d n) H.eY
    S.Y_le hnu hl hl1 hl2 (Bud.tp_pos d n).le
  have hy0 : |c.Y π s / (1 - c.p.lam)| ≤ 101 / 100 * Bud.Yb d n := by
    rw [abs_div, abs_of_pos hl, div_eq_mul_one_div]
    have hYb0 : 0 ≤ Bud.Yb d n := (abs_nonneg _).trans S.Y_le
    calc |c.Y π s| * (1 / (1 - c.p.lam)) ≤ Bud.Yb d n * (101 / 100) :=
          mul_le_mul S.Y_le hl2 (by positivity) hYb0
      _ = _ := by ring
  have h3 := inc_g ((r.Y : ℝ) * ((par d n).nu : ℝ)) (c.Y π s / (1 - c.p.lam))
    (101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) (Bud.Du d n) _ _ H.u'_le H.du
  have hU : 0 ≤ 101 / 100 * Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n := by
    have := (Bud.Xi1_pos d n).le; positivity
  have h4 := mul_le_mul_of_nonneg_right hy hU
  have h5 := mul_le_mul_of_nonneg_right hy0 H.Du0
  have t := oNorm_add_le (cV (rndV (par d n).p v) - cV v)
    (((r.Y : ℝ) * ((par d n).nu : ℝ)) • cV (st.B *ᵥ ξ') - (c.Y π s / (1 - c.p.lam)) • c.u π s)
  unfold Bud.eg
  nlinarith

/-- E11 for `G`. -/
theorem errG (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    oNorm (cV (rvH R d n m A b cs st ξ' ζ' f).G - (ctx R d n m A b cs ap).Gn π s) ≤ (s + 1) * Bud.eg d n := by
  have S := H.sett
  have e : cV (rvH R d n m A b cs st ξ' ζ' f).G - (ctx R d n m A b cs ap).Gn π s =
      (cV st.G - ((ctx R d n m A b cs ap).st π s).G) +
        (cV (rvH R d n m A b cs st ξ' ζ' f).g - (ctx R d n m A b cs ap).ghat π s) := by
    rw [rv_G, cV_add]; unfold Df2Ctx.Gn; abel
  rw [e]
  have := oNorm_add_le (cV st.G - ((ctx R d n m A b cs ap).st π s).G)
    (cV (rvH R d n m A b cs st ξ' ζ' f).g - (ctx R d n m A b cs ap).ghat π s)
  have h1 := S.track.errG
  have h2 := H.g_err
  nlinarith

/-- E11 for `l`. -/
theorem errl (H : RCHyp R d n m A b cs ap π s st ξ' ζ' Z f) :
    |(((rvH R d n m A b cs st ξ' ζ' f).l : ℚ) : ℝ) - (ctx R d n m A b cs ap).ln π s| ≤ (s + 1) * Bud.el d n := by
  have S := H.sett
  set c := ctx R d n m A b cs ap
  set r := rvH R d n m A b cs st ξ' ζ' f
  set x : ℚ := r.g ⬝ᵥ st.mu
  have hl : r.l = st.l + rnd (par d n).p x := rfl
  have e : ((r.l : ℚ) : ℝ) - c.ln π s = ((st.l : ℝ) - (c.st π s).l) + (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ)) +
      (cV r.g - c.ghat π s) ⬝ᵥ (c.st π s).mu := by
    rw [hl]; push_cast; simp only [x]; rw [cV_dot, S.track.mu, sub_dotProduct]; unfold Df2Ctx.ln; ring
  rw [e]
  have h1 := S.track.errl
  have h2 := rnd_err_tp d n x
  have h3 : |(cV r.g - c.ghat π s) ⬝ᵥ (c.st π s).mu| ≤ Bud.eg d n * Bud.R d n :=
    (abs_dot_le _ _).trans (mul_le_mul H.g_err (by rw [← S.track.mu]; exact H.mu_le) (oNorm_nonneg _)
      ((oNorm_nonneg _).trans H.g_err))
  have t1 := abs_add_le (((st.l : ℝ) - (c.st π s).l) + (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ)))
    ((cV r.g - c.ghat π s) ⬝ᵥ (c.st π s).mu)
  have t2 := abs_add_le ((st.l : ℝ) - (c.st π s).l) (((rnd (par d n).p x : ℚ) : ℝ) - (x : ℝ))
  have hel : Bud.el d n = Bud.tp d n / 2 + Bud.R d n * Bud.eg d n := rfl
  rw [hel] at h1 ⊢
  nlinarith

end RCHyp

/-! ## C1 -/

open RCHyp in
/-- Piece C, part C1. -/
theorem c1 : C1Stmt := by
  intro R d n m A b cs ap π s st ξ' ζ' Z f H
  exact ⟨H.ga, H.gt, H.trackA, H.trackB, H.errb, H.errk, H.errG, H.errl, H.eY, H.dq, H.ew⟩

end AdversarialBco.Bit.BLP.RC
