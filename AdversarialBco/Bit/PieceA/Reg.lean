/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Piece A: the constants of the precision theorem over an abstract record

`Reg` holds the reference constants of BL at one `(d, n)`, as reals: `d`, `n`, `N_e`, `δe`, `Le`, `λ`, `η`, `ε`, `ρ`,
`R`, `κ_c`, `u = 2^{-p}` (`tp`), the slack `ê` (`eh`), `2^{B/2}` (`t2`), and `Q = N_e^{1/40}`. The derived constants
are the definitions of the namespace `Bud` of Bit/BLRun.lean, word for word, read
off a `Reg` (`Lgb`, `Ξ`, `Ȳ`, `c̄`, the E-terms, `sel`, `val`, `κ0`, ...): at `reg d n` (Bit/PieceA/Inst.lean) each is
the constant of `Bud` by definition. `Reg.OK` collects the definitions of the base constants and the regime facts
that the majorants use. This file depends on Mathlib only.
-/

namespace AdversarialBco.Bit.PieceA

/-- The base constants at one `(d, n)`. -/
structure Reg where
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

namespace Reg

/-- `Λ = d N_e`. -/
noncomputable def Lam (r : Reg) : ℝ := d r * Ne r
/-- `Lgb = ln 14 + 5 Le/144`. -/
noncomputable def Lgb (r : Reg) : ℝ := Real.log 14 + 5 * Le r / 144
/-- `Ξ = ((8d/3) Lgb)^{1/2}`. -/
noncomputable def Xi (r : Reg) : ℝ := Real.sqrt (8 * d r / 3 * Lgb r)
/-- `Ξ₁ = Ξ + 1`. -/
noncomputable def Xi1 (r : Reg) : ℝ := Xi r + 1
/-- `P̄ = 2 Le^{1/2} + 1`. -/
noncomputable def Pb (r : Reg) : ℝ := 2 * Real.sqrt (Le r) + 1
/-- `π̄ = Le^{1/2} + 1/8`. -/
noncomputable def pib (r : Reg) : ℝ := Real.sqrt (Le r) + 1 / 8
/-- `Ȳ = 2 Le^{1/2}(1/2 + Lgb^{1/2}) + 4 Le^{1/2}/ε`. -/
noncomputable def Yb (r : Reg) : ℝ :=
  2 * Real.sqrt (Le r) * (1 / 2 + Real.sqrt (Lgb r)) + 4 * Real.sqrt (Le r) / eps r
/-- `c̄ = κ_c Ȳ`. -/
noncomputable def cb (r : Reg) : ℝ := kc r * Yb r
/-- `W° = R + 4d (N_e/Le)^{1/2}`. -/
noncomputable def W0 (r : Reg) : ℝ := R r + 4 * d r * Real.sqrt (Ne r / Le r)
/-- E1: `e_ξ = d^{1/2} 2^{2 - B/2}` (in norm). -/
noncomputable def exi (r : Reg) : ℝ := Real.sqrt (d r) * (4 / t2 r)
/-- E1: `e_ζ = 2^{1 - B/2}`. -/
noncomputable def ezt (r : Reg) : ℝ := 2 / t2 r
/-- E2: `e_Y`. -/
noncomputable def eY (r : Reg) : ℝ := tp r / 2 + Pb r / 2 * (tp r + ezt r)
/-- E3: `Δ_c`. -/
noncomputable def Dc (r : Reg) : ℝ := cb r * tp r * (11 / 10 * (Pb r + 1) / Yb r + 1 / 16)
/-- E3: `e_N`. -/
noncomputable def eN (r : Reg) : ℝ :=
  tp r * (1001 / 1000 + 51 / 100 * Xi1 r ^ 2) + 143 / 100 * (1 + Xi1 r ^ 2) * Dc r +
    285 / 100 * cb r * Xi1 r * exi r
/-- E4: `ν = d 2^{-p-1}`. -/
noncomputable def nu (r : Reg) : ℝ := d r * tp r / 2
/-- E5: `h_a`. -/
noncomputable def ha (r : Reg) : ℝ := tp r * (Real.sqrt (8 * Le r) + 1) + tp r / 16
/-- E5: `x = n Λ e_N`. -/
noncomputable def x (r : Reg) : ℝ := n r * Lam r * eN r
/-- E5: `V = n Λ^{1/2} ν`. -/
noncomputable def V (r : Reg) : ℝ := n r * Real.sqrt (Lam r) * nu r
/-- E5: `ℏ = h_a + V + 2x(2 + h_a)`. -/
noncomputable def hb (r : Reg) : ℝ := ha r + V r + 2 * x r * (2 + ha r)
/-- The bound of the tracking lemma after `k` rounds of an epoch, `(1 + h_a + k Λ^{1/2} ν)(1 + Λ e_N)^k - 1`. -/
noncomputable def hTr (r : Reg) (k : ℕ) : ℝ :=
  (1 + ha r + k * Real.sqrt (Lam r) * nu r) * (1 + Lam r * eN r) ^ k - 1
/-- E6: `X̄`. -/
noncomputable def Xb (r : Reg) : ℝ :=
  Real.sqrt (Lam r) * (hb r * Xi1 r + exi r) +
    tp r / 16 * lam r * (1 + hb r) * Real.sqrt (Lam r) * Xi1 r
/-- E7: `Δ_u`. -/
noncomputable def Du (r : Reg) : ℝ := Real.sqrt (Lam r) * (hb r * Xi1 r + exi r)
/-- E8: `Δ_P`. -/
noncomputable def DP (r : Reg) : ℝ := (2 * hb r + hb r ^ 2) * Lam r
/-- E9: `e_b`. -/
noncomputable def eb (r : Reg) : ℝ :=
  Real.sqrt (d r) * tp r / 2 + Dc r * R r * (103 / 100) * Lam r * (Xi1 r ^ 2 + 1) +
    cb r * R r * (203 / 100 * Real.sqrt (Lam r) * Xi1 r * Du r + DP r)
/-- E9: `e_k`. -/
noncomputable def ek (r : Reg) : ℝ :=
  tp r / 2 + Dc r * R r ^ 2 * (103 / 100) * Lam r * (Xi1 r ^ 2 + 1) / 2 +
    cb r / 2 * R r ^ 2 * (203 / 100 * Real.sqrt (Lam r) * Xi1 r * Du r + DP r)
/-- E11: `e_g`. -/
noncomputable def eg (r : Reg) : ℝ :=
  Real.sqrt (d r) * tp r / 2 + 101 / 100 * (eY r + Yb r * tp r / 16) * (101 / 100) * Real.sqrt (Lam r) * Xi1 r +
    101 / 100 * Yb r * Du r
/-- E11: `e_l`. -/
noncomputable def el (r : Reg) : ℝ := tp r / 2 + R r * eg r
/-- E11: `Ḡ`. -/
noncomputable def Gb (r : Reg) : ℝ := n r * (101 / 100) * Yb r * Real.sqrt (Lam r) * Xi r
/-- E12: `e_Φ`. -/
noncomputable def ePhi (r : Reg) : ℝ := R r ^ 2 / 2 * DP r + R r * n r * eb r + n r * ek r
/-- E13: `e_X`. -/
noncomputable def eX (r : Reg) : ℝ :=
  eta r * (101 / 100) * (n r * el r + R r * n r * eg r) + eta r * tp r / 16 * (21 / 10) * R r * Gb r +
    2 * ePhi r
/-- `w_ρ = 2^{-p-4} ρ`. -/
noncomputable def wr (r : Reg) : ℝ := tp r / 16 * rho r
/-- `w_ε = 2^{-p-4} ε`. -/
noncomputable def we (r : Reg) : ℝ := tp r / 16 * eps r
/-- E14: the Hausdorff gap `h`. -/
noncomputable def h (r : Reg) : ℝ :=
  R r * (ePhi r + eh r + 8 * wr r) + 2 * R r ^ 3 * we r / de r ^ 2 + 2 * R r * we r
/-- `r_min = δe²/(2R(R + 1))`. -/
noncomputable def rmin (r : Reg) : ℝ := de r ^ 2 / (2 * R r * (R r + 1))
/-- `Lip_F = 4R/δe²`. -/
noncomputable def LipF (r : Reg) : ℝ := 4 * R r / de r ^ 2
/-- E15: the left side of SEL. -/
noncomputable def sel (r : Reg) : ℝ := 4 * eh r + LipF r * h r + wr r
/-- E15: the right side of SEL, `(3/4)(δe/d) r_min²`. -/
noncomputable def selR (r : Reg) : ℝ := 3 / 4 * de r / d r * rmin r ^ 2
/-- E16: `Δ_q`. -/
noncomputable def Dq (r : Reg) : ℝ := Dc r * (1 + Xi1 r ^ 2) + 202 / 100 * cb r * Xi1 r * exi r
/-- E16: `Δs_5`. -/
noncomputable def Ds5 (r : Reg) : ℝ :=
  tp r / 2 + 103 / 100 * eta r * (eY r + 3 * tp r / 16 * Yb r + Yb r * Dq r)
/-- E16: `Δ_w`. -/
noncomputable def Dw (r : Reg) : ℝ := Ds5 r * Real.sqrt (Lam r) * Xi r + 103 / 100 * eta r * Yb r * Du r
/-- E16: `Δ_F`. -/
noncomputable def DF (r : Reg) : ℝ :=
  (R r + W0 r + Dw r) ^ 2 / 2 * DP r + Lam r * Dw r * (2 * R r + 2 * W0 r + Dw r) / 2
/-- E16: `L_F`. -/
noncomputable def LF (r : Reg) : ℝ := Lam r * (R r + W0 r)
/-- E16: the left side of VAL. -/
noncomputable def val (r : Reg) : ℝ := 2 * DF r + LF r * h r
/-- E16: the right side of VAL, `δe/(128 n² R² d)`. -/
noncomputable def valR (r : Reg) : ℝ := de r / (128 * n r ^ 2 * R r ^ 2 * d r)
/-- E17: `m_par`. -/
noncomputable def mpar (r : Reg) : ℝ := tp r / 4 * pib r * (R r + 10) / eps r
/-- E17: the regret transfer term. -/
noncomputable def reg (r : Reg) : ℝ := n r / eps r * ((1 + 2 * R r) * Xb r + 4 * R r * pib r * we r)
/-- E17: `κ0 = (4/3)((2 + 16/ε) X̄ + m_par)` (`κ1 = 0`). -/
noncomputable def kap0 (r : Reg) : ℝ := 4 / 3 * ((2 + 16 / eps r) * Xb r + mpar r)
/-- `δbits = 2^{-p-2}` (the lemma of the draws). -/
noncomputable def dbits (r : Reg) : ℝ := tp r / 4

/-- The definitions of the base constants and the regime facts at `RunCase`. -/
structure OK (r : Reg) : Prop where
  hd : 1 ≤ r.d
  hn : 1 ≤ r.n
  hNe : r.Ne = 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4
  hde : r.de = 1 / r.Ne
  hLe : r.Le = 36 * Real.log r.Ne
  hlam : r.lam = 1 / (725 * r.d * r.Le ^ 2)
  heta : r.eta = Real.sqrt r.d / (r.Le * Real.sqrt r.n)
  heps : r.eps = 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n
  hrho : r.rho = 1450 * r.d ^ 2 * r.Le ^ 3
  hkc : r.kc = r.eta * r.lam / (4 * (1 - r.lam) ^ 2)
  /-- `RunCase`: `ε ≤ 1/4`. -/
  heps4 : r.eps ≤ 1 / 4
  /-- (F1): `N_e > 2^700`, `Le ≥ 17467`. -/
  hN700 : 2 ^ 700 < r.Ne
  hL1 : 17467 ≤ r.Le
  /-- (F2): `d^15 ≤ N_e`, `32^4 n^4 ≤ N_e`, and `n^{1/2} ≥ 29000 d^{3/2} Le^5`. -/
  hd15 : r.d ^ 15 ≤ r.Ne
  hn4 : 32 ^ 4 * r.n ^ 4 ≤ r.Ne
  hnge : 29000 ^ 2 * r.d ^ 3 * r.Le ^ 10 ≤ r.n
  /-- (F3): `(10 Le)^40 ≤ N_e`. -/
  hL40 : (10 * r.Le) ^ 40 ≤ r.Ne
  /-- `Q = N_e^{1/40}`. -/
  hQ0 : 0 < r.Q
  hQ : r.Q ^ 40 = r.Ne
  /-- (F4): `u ≤ 2^{-160} N_e^{-10} d^{-16}`, `2^64 d^6 N_e^3 u ≤ ê ≤ 2^73 d^6 N_e^3 u`. -/
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

end Reg

end AdversarialBco.Bit.PieceA
