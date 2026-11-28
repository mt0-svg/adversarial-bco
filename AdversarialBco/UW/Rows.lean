/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.SIFacts

@[expose] public section

/-!
# UW-ROWS: the rows of Theorem UW

`rowsUW : RowsUW`. The table T4U at the scale `u` is the table at `u = 1` with `η` divided by `√u` and `ε`
multiplied by `√u`; every other field is the same (`parW_eta_u1`, `parW_eps_u1`). So:

* at `u = 1`, T4U meets `RowHyp` (Poly/Df2RowsProof.lean: the closed forms, `L ≥ 504`, `δ_0 (d n)³ n ≤ e^{-14}`, the
  regime `29000 d^{3/2} L⁵ ≤ √n`), and Theorem U's `rows_of` gives every row of `Df2Rows` there;
* every row of `Df2Rows` is monotone in `η` (down), `1/ε` (down) at fixed `η ε` (`ParDom`, `rows_dom`), so the rows
  hold at `u ≥ 1` while `ε(u) ≤ 1/2`;
* the rows at the levels with `u`: `η_u B_n(u) ≤ η_1 B_n(1)` and `η_u b₁(u) ≤ η_1 b₁(1)`, since
  the factors `√u` of the levels cancel those of `η` and `ε` (`etaBnW_le`, `etaB1W_le`); the stability term with the
  sure ranges is below `ρ/10^6` (`stabW_le`), and the rows follow from the comparisons `cmp_*` of Theorem U at `u = 1`;
* the closure rows and event (b) under the clip read `y_0 ≤ (47/2 + 5 L^{1/2})/ε`, `log(7/δ_c) ≤ u (2 + 7 d Λ_0)`
  and `ε_u² n = 14500² d³ L^{10} u` (`y0_le`, `logc_le`).

This replaces 65 majorants for the rows of `RowsW`: the deterministic rows at `u` reduce to
Theorem U's rows at `u = 1`, which `rows_of` proves.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## T4U at `u = 1` meets `RowHyp` -/

/-- `ε` at `u = 1`. -/
theorem parW1_eps (d n : ℕ) :
    (parW d n 1).eps = 20 * 725 * (d * Real.sqrt d) * (parW d n 1).Le ^ 5 / Real.sqrt n := by
  show 20 * df2oClam * _ * _ ^ 5 * Real.sqrt 1 / _ = _
  rw [df2oClam, Real.sqrt_one, mul_one]
  rfl

/-- `η` at `u = 1`. -/
theorem parW1_eta (d n : ℕ) : (parW d n 1).eta = Real.sqrt d / ((parW d n 1).Le * Real.sqrt n) := by
  show _ / (_ * Real.sqrt ((n : ℝ) * 1)) = _
  rw [mul_one]
  rfl

/-- `ε(u) = ε(1) √u`. -/
theorem parW_eps_u1 (d n : ℕ) (u : ℝ) : (parW d n u).eps = (parW d n 1).eps * Real.sqrt u := by
  show _ / _ = _ / _ * _
  rw [Real.sqrt_one, mul_one, div_mul_eq_mul_div]

/-- `η(u) = η(1)/√u` for `u > 0`. -/
theorem parW_eta_u1 (d n : ℕ) {u : ℝ} (hu : 0 < u) : (parW d n u).eta = (parW d n 1).eta / Real.sqrt u := by
  show _ / (_ * Real.sqrt ((n : ℝ) * u)) = _ / (_ * Real.sqrt ((n : ℝ) * 1)) / _
  rw [mul_one, Real.sqrt_mul (Nat.cast_nonneg n), div_div]
  ring

/-- **T4U at `u = 1` in the regime meets `RowHyp`.** -/
theorem rowHyp_parW1 {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (heps : (parW d n 1).eps ≤ 1 / 2) :
    RowHyp (parW d n 1) d n := by
  have hP := parOK_parW (d := d) (n := n) (u := 1) hd hn le_rfl
  obtain ⟨hN, -, hdN, -⟩ := n0W_bounds hd hn
  have hN0 : (0 : ℝ) < n0W d n := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hde : (parW d n 1).δe = 1 / (n0W d n : ℝ) := rfl
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have he14 := exp14_le
  have hdsmall : (parW d n 1).δe * ((d : ℝ) * n) ^ 3 * n ≤ Real.exp (-14) := by
    have h : (parW d n 1).δe * ((d : ℝ) * n) ^ 3 * n = 1 / (15 * 2 ^ 17) := by
      rw [hde, n0W_cast]
      field_simp
    rw [h, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 14) he14
  have hcx : 14 + 3 * Real.log ((d : ℝ) * n) ≤ Real.log (1 / (parW d n 1).δe) := by
    rw [hde, one_div_one_div]
    have hpos : 0 < Real.exp 14 * ((d : ℝ) * n) ^ 3 := by positivity
    have hle : Real.exp 14 * ((d : ℝ) * n) ^ 3 ≤ n0W d n := by
      rw [n0W_cast]
      have hn34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
      have hd3 : 0 ≤ (d : ℝ) ^ 3 := by positivity
      calc Real.exp 14 * ((d : ℝ) * n) ^ 3 = Real.exp 14 * ((d : ℝ) ^ 3 * (n : ℝ) ^ 3) := by ring
        _ ≤ (15 * 2 ^ 17) * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4) :=
          mul_le_mul he14 (mul_le_mul_of_nonneg_left hn34 hd3) (by positivity) (by norm_num)
        _ = _ := by ring
    have := Real.log_le_log hpos hle
    rwa [Real.log_mul (Real.exp_pos 14).ne' (by positivity), Real.log_exp, Real.log_pow] at this
  refine
    { hd := hd
      hn := hn
      de_pos := hP.de0
      de_lt := ?_
      Le := hP.Lede
      L504 := hP.Le
      cx := hcx
      dsmall := hdsmall
      lam := hP.lam
      eta := parW1_eta d n
      sig2 := rfl
      rho := rfl
      eps := parW1_eps d n
      eps_le := heps
      reg := ?_
      kap := rfl
      theta := rfl
      alpha := rfl
      c1 := rfl
      gam := rfl
      k0 := rfl
      R := rfl
      hlog := ?_ }
  · rw [hde, div_lt_one hN0]; linarith
  · have h := heps
    rw [parW1_eps, div_le_iff₀ hsn] at h
    linarith
  · rw [hde, one_div_one_div]
    exact Real.log_le_log (by positivity) hdN

/-! ## The rows are monotone in `η` and `ε` -/

/-- `q` has the fields of `p` that the rows read, with a smaller `η`, a larger `ε` and the same `η ε`. -/
structure ParDom (q p : Df2OPar) : Prop where
  de : q.δe = p.δe
  Le : q.Le = p.Le
  lam : q.lam = p.lam
  sig2 : q.sig2 = p.sig2
  rho : q.rho = p.rho
  kap : q.kap = p.kap
  theta : q.theta = p.theta
  alpha : q.alpha = p.alpha
  c1 : q.c1 = p.c1
  gam : q.gam = p.gam
  k0 : q.k0 = p.k0
  R : q.R = p.R
  eta0 : 0 < q.eta
  eta : q.eta ≤ p.eta
  eps0 : 0 < p.eps
  eps : p.eps ≤ q.eps
  etaeps : q.eta * q.eps = p.eta * p.eps
  Le0 : 0 ≤ p.Le
  kap0 : 0 ≤ p.kap

namespace ParDom

variable {q p : Df2OPar} {n : ℕ}

theorem etap (D : ParDom q p) : 0 < p.eta := D.eta0.trans_le D.eta

theorem eps0q (D : ParDom q p) : 0 < q.eps := D.eps0.trans_le D.eps

theorem eta_div (D : ParDom q p) : q.eta / q.eps ≤ p.eta / p.eps := div_le_div₀ D.etap.le D.eta D.eps0 D.eps

theorem bn_nonneg (p : Df2OPar) (hl : 0 ≤ p.lam) (hL : 0 ≤ p.Le) (he : 0 < p.eps) : 0 ≤ df2Bn p d n := by
  unfold df2Bn; positivity

theorem b1_nonneg (p : Df2OPar) (hl : 0 ≤ p.lam) (hL : 0 ≤ p.Le) (he : 0 < p.eps) : 0 ≤ df2B1 p d n := by
  unfold df2B1; positivity

theorem bn (D : ParDom q p) (hl : 0 ≤ p.lam) : df2Bn q d n ≤ df2Bn p d n := by
  unfold df2Bn
  rw [D.lam, D.Le]
  have hL := D.Le0
  have h : (d : ℝ) ^ 2 * p.Le / q.eps ≤ (d : ℝ) ^ 2 * p.Le / p.eps :=
    div_le_div_of_nonneg_left (by positivity) D.eps0 D.eps
  gcongr

theorem b1 (D : ParDom q p) (hl : 0 < p.lam) : df2B1 q d n ≤ df2B1 p d n := by
  unfold df2B1
  rw [D.lam, D.Le]
  have hL := D.Le0
  have h : 13 / 100 * ((d : ℝ) * Real.sqrt d) * p.Le ^ 2 / q.eps ≤ 13 / 100 * ((d : ℝ) * Real.sqrt d) * p.Le ^ 2 / p.eps :=
    div_le_div_of_nonneg_left (by positivity) D.eps0 D.eps
  gcongr

theorem etaBn (D : ParDom q p) (hl : 0 ≤ p.lam) : q.eta * df2Bn q d n ≤ p.eta * df2Bn p d n :=
  mul_le_mul D.eta (D.bn hl) (bn_nonneg q (D.lam ▸ hl) (D.Le ▸ D.Le0) D.eps0q) D.etap.le

theorem etaB1 (D : ParDom q p) (hl : 0 < p.lam) : q.eta * df2B1 q d n ≤ p.eta * df2B1 p d n :=
  mul_le_mul D.eta (D.b1 hl) (b1_nonneg q (D.lam ▸ hl.le) (D.Le ▸ D.Le0) D.eps0q) D.etap.le

theorem thn (D : ParDom q p) (hl : 0 ≤ p.lam) : df2ThN q d n ≤ df2ThN p d n := by
  unfold df2ThN
  have := D.etaBn (d := d) (n := n) hl
  linarith

theorem etaBnL (D : ParDom q p) (hl : 0 ≤ p.lam) (c : ℝ) (hc : 0 ≤ c) :
    q.eta * df2Bn q d n / (c * q.Le * q.lam ^ 2) ≤ p.eta * df2Bn p d n / (c * p.Le * p.lam ^ 2) := by
  rw [D.Le, D.lam]
  exact div_le_div_of_nonneg_right (D.etaBn hl) (by have := D.Le0; positivity)

theorem devP (D : ParDom q p) (hl : 0 ≤ p.lam) : df2DevP q d n ≤ df2DevP p d n := by
  unfold df2DevP
  rw [D.kap, D.Le, D.lam]
  have h := D.etaBn (d := d) (n := n) hl
  have hk := D.kap0
  have e1 : q.eta * p.kap * df2Bn q d n = p.kap * (q.eta * df2Bn q d n) := by ring
  have e2 : p.eta * p.kap * df2Bn p d n = p.kap * (p.eta * df2Bn p d n) := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hk) (by have := D.Le0; positivity)

theorem etaDevK (D : ParDom q p) (hl : 0 < p.lam) : q.eta * df2DevK q d n ≤ p.eta * df2DevK p d n := by
  unfold df2DevK
  rw [mul_add, mul_add, ← mul_div_assoc, ← mul_div_assoc]
  have h1 := D.etaB1 (d := d) (n := n) hl
  have h2 := D.etaBnL (d := d) (n := n) hl.le 8 (by norm_num)
  linarith

theorem etaDev (D : ParDom q p) (hl : 0 < p.lam) : q.eta * df2Dev q d n ≤ p.eta * df2Dev p d n := by
  unfold df2Dev
  rw [mul_add, mul_add, ← mul_div_assoc, ← mul_div_assoc]
  have h1 := D.etaB1 (d := d) (n := n) hl
  have h2 := D.etaBnL (d := d) (n := n) hl.le 4 (by norm_num)
  linarith

theorem stab (D : ParDom q p) : df2Stab q d n ≤ df2Stab p d n := by
  unfold df2Stab
  rw [D.Le]
  have h2 : q.eta ^ 2 ≤ p.eta ^ 2 := pow_le_pow_left₀ D.eta0.le D.eta 2
  have hL := D.Le0
  have hc : (0 : ℝ) ≤ 2 * df2Cg := by unfold df2Cg; norm_num
  have e1 : 2 * df2Cg * q.eta ^ 2 * d * n * p.Le = 2 * df2Cg * (d * n * p.Le) * q.eta ^ 2 := by ring
  have e2 : 2 * df2Cg * p.eta ^ 2 * d * n * p.Le = 2 * df2Cg * (d * n * p.Le) * p.eta ^ 2 := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem pri (D : ParDom q p) : df2Pri q = df2Pri p := by
  unfold df2Pri; rw [D.R, D.sig2]

theorem ne (D : ParDom q p) (hl : 0 < p.lam) : 10 * q.eta / (q.eps * q.lam) ≤ 10 * p.eta / (p.eps * p.lam) := by
  rw [D.lam]
  have h := D.eta_div
  have e1 : 10 * q.eta / (q.eps * p.lam) = 10 / p.lam * (q.eta / q.eps) := by
    field_simp [D.eps0q.ne', hl.ne']
  have e2 : 10 * p.eta / (p.eps * p.lam) = 10 / p.lam * (p.eta / p.eps) := by
    field_simp [D.eps0.ne', hl.ne']
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end ParDom

/-- **The rows pass to a record with a smaller `η` and a larger `ε` at the same `η ε`**, while `ε ≤ 1/2`. -/
theorem rows_dom {q p : Df2OPar} {n : ℕ} (D : ParDom q p) (H : Df2Rows p d n) (heps : q.eps ≤ 1 / 2) :
    Df2Rows q d n := by
  have hl := H.pos_lam
  have hde := D.de; have hLe := D.Le; have hlam := D.lam; have hsig := D.sig2; have hrho := D.rho
  have hk := D.kap; have hth := D.theta; have hal := D.alpha; have hc1 := D.c1; have hga := D.gam
  have hk0 := D.k0; have hR := D.R
  have hdiv := D.eta_div
  have hep := D.eps0q
  have hpri := D.pri
  have hstab := D.stab (d := d) (n := n)
  have hthn := D.thn (d := d) (n := n) hl.le
  have hdp := D.devP (d := d) (n := n) hl.le
  have hdk := D.etaDevK (d := d) (n := n) hl
  have hdv := D.etaDev (d := d) (n := n) hl
  have hne := D.ne hl
  have heta := D.eta
  refine
    { pos_de := by rw [hde]; exact H.pos_de
      de_lt := by rw [hde]; exact H.de_lt
      pos_lam := by rw [hlam]; exact hl
      lam_le := by rw [hlam]; exact H.lam_le
      pos_eta := D.eta0
      eta_le := heta.trans H.eta_le
      pos_sig2 := by rw [hsig]; exact H.pos_sig2
      pos_rho := by rw [hrho]; exact H.pos_rho
      pos_eps := hep
      eps_le := heps
      one_le_R := by rw [hR]; exact H.one_le_R
      k0_le := by rw [hk0]; exact H.k0_le
      r1 := by rw [hsig]; exact H.r1
      r2 := by rw [hsig]; exact H.r2
      r3 := by rw [hsig, hLe]; exact H.r3
      r4 := by rw [hLe]; exact H.r4
      r5p := ?_
      r6 := ?_
      r6a := ?_
      r6b := ?_
      r7 := ?_
      r8 := ?_
      r11 := by rw [hlam, hLe]; exact H.r11
      r12 := hthn.trans H.r12
      r14 := H.r14.trans D.eps
      r15p := H.r15p
      r17 := by rw [hk]; exact H.r17
      r19o := ?_
      r20 := by rw [hga, hrho]; linarith [H.r20]
      r21 := by rw [hc1, hrho, hLe, hlam]; linarith [H.r21]
      r22 := ?_
      r24o := ?_
      r24b := ?_
      c22 := ?_
      c8 := ?_
      c16 := ?_
      c4 := by rw [hde, hsig]; exact H.c4
      cnu := by rw [hde, hlam]; exact H.cnu
      c2dl := by rw [hde, hlam]; exact H.c2dl
      c500 := by rw [hde, hLe]; exact H.c500
      cx := by rw [hde]; exact H.cx
      clg := by unfold df2Lg; rw [hde]; exact H.clg
      cz := by rw [hk0, hde]; exact H.cz }
  · have e : q.lam * q.eta * q.eps = p.lam * p.eta * p.eps := by rw [mul_assoc, D.etaeps, hlam, ← mul_assoc]
    rw [e, hLe]; exact H.r5p
  · have hs : 0 ≤ Real.sqrt (2 * d * p.sig2) := Real.sqrt_nonneg _
    calc 8 * q.eta * q.lam * Real.sqrt (2 * d * q.sig2) / q.eps
        = 8 * p.lam * Real.sqrt (2 * d * p.sig2) * (q.eta / q.eps) := by rw [hlam, hsig]; ring
      _ ≤ 8 * p.lam * Real.sqrt (2 * d * p.sig2) * (p.eta / p.eps) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 8 * p.eta * p.lam * Real.sqrt (2 * d * p.sig2) / p.eps := by ring
      _ ≤ 1 := H.r6
  · have hL := D.Le0
    calc q.eta * q.lam * q.Le / (2 * q.eps) = p.lam * p.Le / 2 * (q.eta / q.eps) := by rw [hlam, hLe]; ring
      _ ≤ p.lam * p.Le / 2 * (p.eta / p.eps) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = p.eta * p.lam * p.Le / (2 * p.eps) := by ring
      _ ≤ 1 := H.r6a
  · have hL := D.Le0
    calc 2 / df2C0 * q.eta * q.lam * d * q.Le ^ 2 / q.eps
        = 2 / df2C0 * p.lam * d * p.Le ^ 2 * (q.eta / q.eps) := by rw [hlam, hLe]; ring
      _ ≤ 2 / df2C0 * p.lam * d * p.Le ^ 2 * (p.eta / p.eps) :=
        mul_le_mul_of_nonneg_left hdiv (by unfold df2C0; positivity)
      _ = 2 / df2C0 * p.eta * p.lam * d * p.Le ^ 2 / p.eps := by ring
      _ ≤ 1 := H.r6b
  · have hL := D.Le0
    rw [hLe]
    refine le_trans ?_ H.r7
    exact div_le_div_of_nonneg_left (by positivity) (by have := D.eps0; positivity)
      (pow_le_pow_left₀ D.eps0.le D.eps 2)
  · have hL := D.Le0
    rw [hLe]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) D.eps0 D.eps) H.r8
  · have h := H.r19o
    rw [hlam, hLe, hpri, hrho]
    linarith
  · have h := H.r22
    rw [hlam, hLe, hpri, hrho, hth, hal]
    have := D.etap
    have hne2 := hne
    rw [hlam] at hne2
    linarith
  · have h := H.r24o
    rw [hpri, hrho, hth, hc1, hga]
    have := D.etap
    linarith
  · have h := H.r24b
    rw [hpri, hrho, hth, hc1, hga]
    linarith
  · have hL := D.Le0
    rw [hLe, hde]
    refine le_trans ?_ H.c22
    exact div_le_div_of_nonneg_left (by have := H.pos_de; positivity) (by have := D.eps0; positivity)
      (pow_le_pow_left₀ D.eps0.le D.eps 2)
  · rw [hde]
    exact le_trans (div_le_div_of_nonneg_left (by have := H.pos_de; positivity) D.eps0 D.eps) H.c8
  · rw [hlam, hde]
    have hs : 0 ≤ Real.sqrt (d * p.δe) := Real.sqrt_nonneg _
    calc 16 * q.eta * p.lam * n * Real.sqrt (d * p.δe) / q.eps
        = 16 * p.lam * n * Real.sqrt (d * p.δe) * (q.eta / q.eps) := by ring
      _ ≤ 16 * p.lam * n * Real.sqrt (d * p.δe) * (p.eta / p.eps) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 16 * p.eta * p.lam * n * Real.sqrt (d * p.δe) / p.eps := by ring
      _ ≤ 1 := H.c16

end AdversarialBco.UW
