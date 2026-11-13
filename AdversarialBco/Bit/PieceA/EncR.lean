/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-!
# Piece A: the enclosure lemma over an abstract record

`EncR` holds, as reals, what Procedure PARAM (`par d n` of Bit/BLPure.lean) computes at one `(d, n)` and the
reference values it encloses (the enclosure lemma). The reference side: `d`, `n`, `N_e`, `Le = 36 ln N_e`,
`la = ln(2d + 2)`, `u = 2^{-p}` (`tp`). The machine side: the working steps `eq = 2^{-q}`, `eF = 2^{-pF}`, the
logarithms `Le'` (`Lp`), `Le_hi` (`Lh`), `l1 = L1 + η_1`, the roots `r_d`, `r_n`, `sqrt_up(l1)` (`sR`),
`sqrt_up(N_e/Le')` (`sW`), `sqrt_up(sig2')` (`sU`), and the fields `ε'`, `λ'`, `η'`, `sig2'`, `ρ'`, `κ_c'`, `ν'`,
`R'`, `s'_b`, `W'`, `A_0`, `B_0`. `EncR.OK` collects the facts of the leaves (the logarithm and root enclosures, the
roundings `up`, `dn`, `rnd` at their grids) and the regime facts used; Bit/PieceA/Enc.lean proves it at `par d n`.
The lemmas of `EncR.OK` are the fields of `Bud.EncOK`. This file depends on Mathlib only.
-/

namespace AdversarialBco.Bit.PieceA

/-- PARAM's values and their references at one `(d, n)`. -/
structure EncR where
  d : ℝ
  n : ℝ
  Ne : ℝ
  Le : ℝ
  la : ℝ
  tp : ℝ
  eq : ℝ
  eF : ℝ
  Lp : ℝ
  Lh : ℝ
  l1 : ℝ
  rd : ℝ
  rn : ℝ
  sR : ℝ
  sW : ℝ
  sU : ℝ
  ep : ℝ
  lm : ℝ
  et : ℝ
  sg : ℝ
  ro : ℝ
  kp : ℝ
  nu : ℝ
  Rp : ℝ
  sb : ℝ
  Wp : ℝ
  A0 : ℝ
  B0 : ℝ

namespace EncR

/-- `ε = 14500 d^{3/2} Le^5/n^{1/2}`. -/
noncomputable def eps (r : EncR) : ℝ := 14500 * r.d * Real.sqrt r.d * r.Le ^ 5 / Real.sqrt r.n
/-- `λ = 1/(725 d Le^2)`. -/
noncomputable def lam (r : EncR) : ℝ := 1 / (725 * r.d * r.Le ^ 2)
/-- `η = d^{1/2}/(Le n^{1/2})`. -/
noncomputable def eta (r : EncR) : ℝ := Real.sqrt r.d / (r.Le * Real.sqrt r.n)
/-- `σ² = 1/(8 Le)`. -/
noncomputable def sig2 (r : EncR) : ℝ := 1 / (8 * r.Le)
/-- `ρ = 1450 d^2 Le^3`. -/
noncomputable def rho (r : EncR) : ℝ := 1450 * r.d ^ 2 * r.Le ^ 3
/-- `κ_c = η λ/(4 (1 - λ)^2)`. -/
noncomputable def kc (r : EncR) : ℝ := eta r * lam r / (4 * (1 - lam r) ^ 2)
/-- `R = 134 d (ln(2d + 2))^{1/2}`. -/
noncomputable def R (r : EncR) : ℝ := 134 * r.d * Real.sqrt r.la
/-- `s_b = δe^2/(R(R + 1))`, `δe = 1/N_e`. -/
noncomputable def sbR (r : EncR) : ℝ := (1 / r.Ne) ^ 2 / (R r * (R r + 1))
/-- `W° = R + 4d (N_e/Le)^{1/2}`. -/
noncomputable def W0 (r : EncR) : ℝ := R r + 4 * r.d * Real.sqrt (r.Ne / r.Le)

/-- The facts of PARAM's leaves and the regime facts that the enclosure lemma uses. -/
structure OK (r : EncR) : Prop where
  hd : 1 ≤ r.d
  hn : 1 ≤ r.n
  hNe : r.Ne = 15 * 2 ^ 17 * r.d ^ 3 * r.n ^ 4
  /-- Regime: `Le ≥ 17467`, `Le^4 d n ≤ N_e`. -/
  hLe : 17467 ≤ r.Le
  hsm : r.Le ^ 4 * r.d * r.n ≤ r.Ne
  /-- `ln(2d + 2) ≥ 1`, `ln(2d + 2) ≤ 2d + 1`. -/
  hla1 : 1 ≤ r.la
  hla2 : r.la ≤ 2 * r.d + 1
  /-- The precisions: `2^{-p} ≤ 2^{-160}`, `2^{-q} (1 + Le) ≤ 2^{-p-18}`, `2^{-pF} 2^40 N_e^2 d^4 ≤ 2^{-p}`. -/
  htp0 : 0 < r.tp
  htp1 : r.tp ≤ 1 / 2 ^ 160
  heq0 : 0 < r.eq
  heq1 : r.eq * (1 + r.Le) ≤ r.tp / 2 ^ 18
  heF0 : 0 < r.eF
  heF1 : r.eF * (2 ^ 40 * r.Ne ^ 2 * r.d ^ 4) ≤ r.tp
  /-- The logarithms: `Le - 2^{-p-9} ≤ Le' ≤ Le ≤ Le_hi ≤ Le + 2^{-p-9}`, `la ≤ l1 ≤ la + 2^{-p-15}`. -/
  hLp1 : r.Le - r.tp / 2 ^ 9 ≤ r.Lp
  hLp2 : r.Lp ≤ r.Le
  hLh1 : r.Le ≤ r.Lh
  hLh2 : r.Lh ≤ r.Le + r.tp / 2 ^ 9
  hl1a : r.la ≤ r.l1
  hl1b : r.l1 ≤ r.la + r.tp / 2 ^ 15
  /-- The roots `r_d`, `r_n` (`ISQRT`), and `sqrt_up`. -/
  hrd0 : 1 ≤ r.rd
  hrd1 : r.rd ≤ Real.sqrt r.d
  hrd2 : Real.sqrt r.d ≤ r.rd + r.eq
  hrn0 : 1 ≤ r.rn
  hrn1 : r.rn ≤ Real.sqrt r.n
  hrn2 : Real.sqrt r.n ≤ r.rn + r.eq
  hsR1 : Real.sqrt r.l1 ≤ r.sR
  hsR2 : r.sR ≤ Real.sqrt r.l1 + 2 * r.eq
  hsW1 : Real.sqrt (r.Ne / r.Lp) ≤ r.sW
  hsW2 : r.sW ≤ Real.sqrt (r.Ne / r.Lp) + 2 * r.eq
  hsU1 : Real.sqrt r.sg ≤ r.sU
  hsU2 : r.sU ≤ Real.sqrt r.sg + 2 * r.eq
  /-- The fields: `up` and `dn` at `2^{-pF}`, `rnd` at `2^{-pF}` and (for `A_0`, `B_0`) at `2^{-p}`. -/
  hep1 : 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn ≤ r.ep
  hep2 : r.ep ≤ 14500 * r.d * (r.rd + r.eq) * r.Lh ^ 5 / r.rn + r.eF
  hlm : |r.lm - 1 / (725 * r.d * r.Lp ^ 2)| ≤ r.eF / 2
  het : |r.et - r.rd / (r.Lp * r.rn)| ≤ r.eF / 2
  hsg : |r.sg - 1 / (8 * r.Lp)| ≤ r.eF / 2
  hro1 : 1450 * r.d ^ 2 * r.Lp ^ 3 - r.eF ≤ r.ro
  hro2 : r.ro ≤ 1450 * r.d ^ 2 * r.Lp ^ 3
  hkp : |r.kp - r.et * r.lm / (4 * (1 - r.lm) ^ 2)| ≤ r.eF / 2
  hnu : |r.nu - 1 / (1 - r.lm)| ≤ r.eF / 2
  hRp1 : 134 * r.d * r.sR ≤ r.Rp
  hRp2 : r.Rp ≤ 134 * r.d * r.sR + r.eF
  hsb1 : 1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1)) - r.eF ≤ r.sb
  hsb2 : r.sb ≤ 1 / (r.Ne ^ 2 * r.Rp * (r.Rp + 1))
  hWp1 : r.Rp + 4 * r.d * r.sW ≤ r.Wp
  hWp2 : r.Wp ≤ r.Rp + 4 * r.d * r.sW + r.eF
  hA0 : |r.A0 - r.sU| ≤ r.tp / 2
  hB0 : |r.B0 - 1 / r.sU| ≤ r.tp / 2

end EncR

end AdversarialBco.Bit.PieceA
