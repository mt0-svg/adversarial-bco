/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Theorem BUD-W: the constants over an abstract record

Unified/BudReg.lean (Theorem U's `Reg`) with the parameters of T4U at the
floor and the sure ranges of the observation, in the level reading of the caps.

`RegW` keeps every base constant of `Reg` at the level `N_e = 2^{k_δ} N_0` (`Ne`, `δe`, `Le = 36 ln N_e`, `tp`, `eh`,
`t2`, `Q = N_e^{1/40}`, `R`), and gains the floor `L_f = 36 ln N_0` (`Lf`), the scaling `u` (`uu`) and the sure
ranges `b0`, `y0`. The parameters read `(L_f, u)` (`RegW.OK`): `λ = 1/(725 d L_f²)`, `η = d^{1/2}/(L_f (n u)^{1/2})`,
`ε = 14500 d^{3/2} L_f^5 u^{1/2}/n^{1/2}`, `ρ = 1450 d² L_f³`, `κ_c = η λ/(4 (1 - λ)²)`. The derived constants are
those of `Reg`, word for word, except the ones Lemma errors-W changes: `Ξ_w`, `Ξ_{w1}`,
`c̄_w = κ_c y0`, `e^w_Y`, `Δ^w_c`, `Δ^w_u`, and `e_N`, `e_b`, `e_k`, `e_g`, `Ḡ`, `Δ_q`, `Δs_5`, `Δ_w` at them. The
level constants of the play (`Lgb`, `Ξ`, `Ξ₁`, `P̄`, `π̄`) and every term of E1, E2, E5, E6, E17 are `Reg`'s.

`RegW.OK` collects the definitions and the regime facts at `ε(u) ≤ 1/4`: the level facts (F1) to (F4) of Theorem U,
which read `N_e` only, and the floor facts `L_f ≥ 17467`, `L_f ≤ Le`, `58000² d³ L_f^{10} u ≤ n`, with the brackets of
`b0`, `y0` that the chain reads. This file depends on Mathlib only.
-/

namespace AdversarialBco.UW.BudW

/-- The base constants of Theorem BUD-W at one input. -/
structure RegW where
  d : ℝ
  n : ℝ
  Ne : ℝ
  de : ℝ
  Le : ℝ
  lam : ℝ
  eta : ℝ
  eps : ℝ
  rho : ℝ
  R : ℝ
  kc : ℝ
  tp : ℝ
  eh : ℝ
  t2 : ℝ
  Q : ℝ
  Lf : ℝ
  uu : ℝ
  b0 : ℝ
  y0 : ℝ

namespace RegW

/-- `Λ = d N_e`. -/
noncomputable def Lam (r : RegW) : ℝ := d r * Ne r
/-- `Lgb = ln 14 + 5 Le/144`. -/
noncomputable def Lgb (r : RegW) : ℝ := Real.log 14 + 5 * Le r / 144
/-- `Ξ = ((8d/3) Lgb)^{1/2}`. -/
noncomputable def Xi (r : RegW) : ℝ := Real.sqrt (8 * d r / 3 * Lgb r)
/-- `Ξ₁ = Ξ + 1`. -/
noncomputable def Xi1 (r : RegW) : ℝ := Xi r + 1
/-- `P̄ = 2 Le^{1/2} + 1`. -/
noncomputable def Pb (r : RegW) : ℝ := 2 * Real.sqrt (Le r) + 1
/-- `π̄ = Le^{1/2} + 1/8`. -/
noncomputable def pib (r : RegW) : ℝ := Real.sqrt (Le r) + 1 / 8
/-- `W° = R + 4d (N_e/Le)^{1/2}`. -/
noncomputable def W0 (r : RegW) : ℝ := R r + 4 * d r * Real.sqrt (Ne r / Le r)
/-- E1: `e_ξ = d^{1/2} 2^{2 - B/2}` (in norm). -/
noncomputable def exi (r : RegW) : ℝ := Real.sqrt (d r) * (4 / t2 r)
/-- E1: `e_ζ = 2^{1 - B/2}`. -/
noncomputable def ezt (r : RegW) : ℝ := 2 / t2 r
/-- E2: `e_Y`. -/
noncomputable def eY (r : RegW) : ℝ := tp r / 2 + Pb r / 2 * (tp r + ezt r)
/-- Lemma WR (ii): `Ξ_w = (b0 + 1)^{1/2} + 2^{-p-1}`. -/
noncomputable def Xw (r : RegW) : ℝ := Real.sqrt (b0 r + 1) + tp r / 2
/-- `Ξ_{w1} = Ξ_w + 1`. -/
noncomputable def Xw1 (r : RegW) : ℝ := Xw r + 1
/-- Lemma WR (iii): `c̄_w = κ_c y0`. -/
noncomputable def cbw (r : RegW) : ℝ := kc r * y0 r
/-- Lemma E2w: `e^w_Y = e_Y + y0 e_ξ (2 (b0 + 1)^{1/2} + e_ξ) + 2^{-p-1}`. -/
noncomputable def eYw (r : RegW) : ℝ := eY r + y0 r * exi r * (2 * Real.sqrt (b0 r + 1) + exi r) + tp r / 2
/-- E3w: `Δ^w_c = κ_c ((1 + 2^{-p-4}) e^w_Y + 2^{-p-4} y0)`. -/
noncomputable def Dcw (r : RegW) : ℝ := kc r * ((1 + tp r / 16) * eYw r + tp r / 16 * y0 r)
/-- E3w: `e^w_N`. -/
noncomputable def eN (r : RegW) : ℝ :=
  tp r * (1001 / 1000 + 51 / 100 * Xw1 r ^ 2) + 143 / 100 * (1 + Xw1 r ^ 2) * Dcw r +
    285 / 100 * cbw r * Xw1 r * exi r
/-- E4: `ν = d 2^{-p-1}`. -/
noncomputable def nu (r : RegW) : ℝ := d r * tp r / 2
/-- E5: `h_a`. -/
noncomputable def ha (r : RegW) : ℝ := tp r * (Real.sqrt (8 * Le r) + 1) + tp r / 16
/-- E5: `x = n Λ e_N`. -/
noncomputable def x (r : RegW) : ℝ := n r * Lam r * eN r
/-- E5: `V = n Λ^{1/2} ν`. -/
noncomputable def V (r : RegW) : ℝ := n r * Real.sqrt (Lam r) * nu r
/-- E5: `ℏ = h_a + V + 2x(2 + h_a)`. -/
noncomputable def hb (r : RegW) : ℝ := ha r + V r + 2 * x r * (2 + ha r)
/-- The bound of Lemma TRACK after `k` rounds of an epoch, `(1 + h_a + k Λ^{1/2} ν)(1 + Λ e_N)^k - 1`. -/
noncomputable def hTr (r : RegW) (k : ℕ) : ℝ :=
  (1 + ha r + k * Real.sqrt (Lam r) * nu r) * (1 + Lam r * eN r) ^ k - 1
/-- E6: `X̄`. -/
noncomputable def Xb (r : RegW) : ℝ :=
  Real.sqrt (Lam r) * (hb r * Xi1 r + exi r) +
    tp r / 16 * lam r * (1 + hb r) * Real.sqrt (Lam r) * Xi1 r
/-- E7: `Δ_u = Λ^{1/2} (ℏ Ξ₁ + e_ξ)`, Theorem U's, the first term of `X̄`. -/
noncomputable def Du (r : RegW) : ℝ := Real.sqrt (Lam r) * (hb r * Xi1 r + exi r)
/-- E7w: `Δ^w_u = Λ^{1/2} (ℏ Ξ_{w1} + e_ξ)`. -/
noncomputable def Duw (r : RegW) : ℝ := Real.sqrt (Lam r) * (hb r * Xw1 r + exi r)
/-- E8: `Δ_P`. -/
noncomputable def DP (r : RegW) : ℝ := (2 * hb r + hb r ^ 2) * Lam r
/-- E9w: `e^w_b`. -/
noncomputable def eb (r : RegW) : ℝ :=
  Real.sqrt (d r) * tp r / 2 + Dcw r * R r * (103 / 100) * Lam r * (Xw1 r ^ 2 + 1) +
    cbw r * R r * (203 / 100 * Real.sqrt (Lam r) * Xw1 r * Duw r + DP r)
/-- E9w: `e^w_k`. -/
noncomputable def ek (r : RegW) : ℝ :=
  tp r / 2 + Dcw r * R r ^ 2 * (103 / 100) * Lam r * (Xw1 r ^ 2 + 1) / 2 +
    cbw r / 2 * R r ^ 2 * (203 / 100 * Real.sqrt (Lam r) * Xw1 r * Duw r + DP r)
/-- E11w: `e^w_g`. -/
noncomputable def eg (r : RegW) : ℝ :=
  Real.sqrt (d r) * tp r / 2 + 101 / 100 * (eYw r + y0 r * tp r / 16) * (101 / 100) * Real.sqrt (Lam r) * Xw1 r +
    101 / 100 * y0 r * Duw r
/-- E11w: `e^w_l`. -/
noncomputable def el (r : RegW) : ℝ := tp r / 2 + R r * eg r
/-- E11w: `Ḡ_w = 1.01 n y0 Λ^{1/2} Ξ_w`. -/
noncomputable def Gb (r : RegW) : ℝ := n r * (101 / 100) * y0 r * Real.sqrt (Lam r) * Xw r
/-- E12: `e_Φ`. -/
noncomputable def ePhi (r : RegW) : ℝ := R r ^ 2 / 2 * DP r + R r * n r * eb r + n r * ek r
/-- E13: `e_X`. -/
noncomputable def eX (r : RegW) : ℝ :=
  eta r * (101 / 100) * (n r * el r + R r * n r * eg r) + eta r * tp r / 16 * (21 / 10) * R r * Gb r +
    2 * ePhi r
/-- `w_ρ = 2^{-p-4} ρ`. -/
noncomputable def wr (r : RegW) : ℝ := tp r / 16 * rho r
/-- `w_ε = 2^{-p-4} ε`. -/
noncomputable def we (r : RegW) : ℝ := tp r / 16 * eps r
/-- E14: the Hausdorff gap `h`. -/
noncomputable def h (r : RegW) : ℝ :=
  R r * (ePhi r + eh r + 8 * wr r) + 2 * R r ^ 3 * we r / de r ^ 2 + 2 * R r * we r
/-- `r_min = δe²/(2R(R + 1))`. -/
noncomputable def rmin (r : RegW) : ℝ := de r ^ 2 / (2 * R r * (R r + 1))
/-- `Lip_F = 4R/δe²`. -/
noncomputable def LipF (r : RegW) : ℝ := 4 * R r / de r ^ 2
/-- E15: the left side of SEL. -/
noncomputable def sel (r : RegW) : ℝ := 4 * eh r + LipF r * h r + wr r
/-- E15: the right side of SEL, `(3/4)(δe/d) r_min²`. -/
noncomputable def selR (r : RegW) : ℝ := 3 / 4 * de r / d r * rmin r ^ 2
/-- E16w: `Δ^w_q = Δ^w_c (1 + Ξ_{w1}²) + 2.02 c̄_w Ξ_{w1} e_ξ`. -/
noncomputable def Dq (r : RegW) : ℝ := Dcw r * (1 + Xw1 r ^ 2) + 202 / 100 * cbw r * Xw1 r * exi r
/-- E16w: `Δs_5`. -/
noncomputable def Ds5 (r : RegW) : ℝ :=
  tp r / 2 + 103 / 100 * eta r * (eYw r + 3 * tp r / 16 * y0 r + y0 r * Dq r)
/-- E16w: `Δ^w_w`. -/
noncomputable def Dw (r : RegW) : ℝ := Ds5 r * Real.sqrt (Lam r) * Xw r + 103 / 100 * eta r * y0 r * Duw r
/-- E16: `Δ_F`. -/
noncomputable def DF (r : RegW) : ℝ :=
  (R r + W0 r + Dw r) ^ 2 / 2 * DP r + Lam r * Dw r * (2 * R r + 2 * W0 r + Dw r) / 2
/-- E16: `L_F`. -/
noncomputable def LF (r : RegW) : ℝ := Lam r * (R r + W0 r)
/-- E16: the left side of VAL. -/
noncomputable def val (r : RegW) : ℝ := 2 * DF r + LF r * h r
/-- E16: the right side of VAL, `δe/(128 n² R² d)`. -/
noncomputable def valR (r : RegW) : ℝ := de r / (128 * n r ^ 2 * R r ^ 2 * d r)
/-- E17: `m_par`. -/
noncomputable def mpar (r : RegW) : ℝ := tp r / 4 * pib r * (R r + 10) / eps r
/-- E17: the regret transfer term. -/
noncomputable def reg (r : RegW) : ℝ := n r / eps r * ((1 + 2 * R r) * Xb r + 4 * R r * pib r * we r)
/-- E17: `κ0 = (4/3)((2 + 16/ε) X̄ + m_par)` (`κ1 = 0`). -/
noncomputable def kap0 (r : RegW) : ℝ := 4 / 3 * ((2 + 16 / eps r) * Xb r + mpar r)
/-- `δbits = 2^{-p-2}` (Lemma BITS). -/
noncomputable def dbits (r : RegW) : ℝ := tp r / 4
/-- BL-O: the gauge band of the play, `2^{-p-1} π̄`. -/
noncomputable def gb (r : RegW) : ℝ := tp r / 2 * pib r
/-- BL-O: the band's share of the shift. -/
noncomputable def band (r : RegW) : ℝ := gb r * (2 + (R r * pib r + 4) / eps r)
/-- BL-O: v2.1's bound of the shift, `(3/4) κ0`. -/
noncomputable def S (r : RegW) : ℝ := (2 + 16 / eps r) * Xb r + mpar r
/-- BL-O: `κ0 = κ1 = 2 (S + band)`. -/
noncomputable def kapO (r : RegW) : ℝ := 2 * (S r + band r)
/-- BL-O: the regret transfer term with the band. -/
noncomputable def regO (r : RegW) : ℝ := n r / eps r * ((1 + 2 * R r) * Xb r + 4 * R r * pib r * we r + R r * gb r)

/-- The definitions of the base constants and the regime facts of Theorem BUD-W. -/
structure OK (r : RegW) : Prop where
  hd : 1 ≤ r.d
  hn : 1 ≤ r.n
  hNe : 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4 ≤ r.Ne
  hde : r.de = 1 / r.Ne
  hLe : r.Le = 36 * Real.log r.Ne
  /-- The floor `L_f = 36 ln N_0`, `N_0 = 15 · 2^17 d³ n⁴`. -/
  hLf : r.Lf = 36 * Real.log (15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4)
  hu : 1 ≤ r.uu
  hlam : r.lam = 1 / (725 * r.d * r.Lf ^ 2)
  heta : r.eta = Real.sqrt r.d / (r.Lf * Real.sqrt (r.n * r.uu))
  heps : r.eps = 14500 * r.d * Real.sqrt r.d * r.Lf ^ 5 * Real.sqrt r.uu / Real.sqrt r.n
  hrho : r.rho = 1450 * r.d ^ 2 * r.Lf ^ 3
  hkc : r.kc = r.eta * r.lam / (4 * (1 - r.lam) ^ 2)
  /-- The case: `ε(u) ≤ 1/4`. -/
  heps4 : r.eps ≤ 1 / 4
  /-- (W-F1): `N_e > 2^700`, `Le ≥ L_f ≥ 17467`. -/
  hN700 : 2 ^ 700 < r.Ne
  hLf1 : 17467 ≤ r.Lf
  hLfLe : r.Lf ≤ r.Le
  /-- (W-F2): `d^15 ≤ N_e`, `32^4 n^4 ≤ N_e`, and `n^{1/2} ≥ 58000 d^{3/2} L_f^5 u^{1/2}`. -/
  hd15 : r.d ^ 15 ≤ r.Ne
  hn4 : 32 ^ 4 * r.n ^ 4 ≤ r.Ne
  hnge : 58000 ^ 2 * r.d ^ 3 * r.Lf ^ 10 * r.uu ≤ r.n
  /-- (W-F3): `(10 Le)^40 ≤ N_e`. -/
  hL40 : (10 * r.Le) ^ 40 ≤ r.Ne
  /-- `Q = N_e^{1/40}`. -/
  hQ0 : 0 < r.Q
  hQ : r.Q ^ 40 = r.Ne
  /-- (W-F4): `u ≤ 2^{-160} N_e^{-10} d^{-16}`, `2^64 d^6 N_e^3 u ≤ ê ≤ 2^73 d^6 N_e^3 u`. -/
  htp0 : 0 < r.tp
  htp : 2 ^ 160 * r.Ne ^ 10 * r.d ^ 16 * r.tp ≤ 1
  heh1 : 2 ^ 64 * r.d ^ 6 * r.Ne ^ 3 * r.tp ≤ r.eh
  heh2 : r.eh ≤ 2 ^ 73 * r.d ^ 6 * r.Ne ^ 3 * r.tp
  /-- `R = 134 d (ln(2d + 2))^{1/2}`: `157 ≤ R`, `R² ≤ 190² d³`. -/
  hR1 : 157 ≤ r.R
  hR2 : r.R ^ 2 ≤ 190 ^ 2 * r.d ^ 3
  /-- `2^{B/2} ≥ 4 n (d + 2) 2^p`. -/
  ht20 : 0 < r.t2
  ht2 : 4 * r.n * (r.d + 2) ≤ r.t2 * r.tp
  /-- H4, the ends of the brackets the chain reads: `b0 ≥ 2d + 2`, `b0 + 1 ≤ 2d + L_f + 4`, `0 < y0 ≤ 11 + 18/ε +
  10 L_f^{1/2}`. -/
  hb0 : 2 * r.d + 2 ≤ r.b0
  hb1 : r.b0 + 1 ≤ 2 * r.d + r.Lf + 4
  hy00 : 0 < r.y0
  hy0 : r.y0 ≤ 11 + 18 / r.eps + 10 * Real.sqrt r.Lf

end RegW

end AdversarialBco.UW.BudW
