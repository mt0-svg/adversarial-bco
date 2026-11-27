/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOSpec
public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# Theorem BUD of BL-O: the constants at a free `k_δ`

UNI-PLAY, UNI-DELTA, UNI-BUD. BL-O's PARAM `parO d n δ = parN (NeO d n (kDel δ)) d n`, the reference `df2oPar d n δ_BL`,
`δ_BL = deltaO d n (kDel δ)`, read `δ` only through `k = kDel δ`; so every constant here is at a free `k : ℕ`:
`poK d n k = df2oPar d n (deltaO d n k)` and `parK d n k = parN (NeO d n k) d n` (`poO d n δ = poK d n (kDel δ)`,
`parO d n δ = parK d n (kDel δ)` by `rfl`).

The constants of the namespace `Bud` of Bit/BLRun.lean at `(d, n, k)`,
word for word with `po d n` read as `poK d n k` and `par d n` as `parK d n k`; `EncOK` (Lemma ENC) and `BudOK`
(Theorem BUD) with the same fields; and the fields BL-O adds:

* the gauge band of the play (`GaugeBandO`, `η_g = 2^{-p-2}`): `|pt' - pt_{ε'}(X')| ≤ gb = 2^{-p-1} π̄`;
* the shift with the noise (route Sec. 3.6, m5): `|r - 1| + |μ| ≤ S + band`, `S = (2 + 16/ε) X̄ + m_par` (v2.1's
  `(3/4) κ0`), `band = gb (2 + (R π̄ + 4)/ε)`; with `tau_shift` (Unified/BLOParam.lean) the clause of `EngineHypW`
  holds at `κ0 = κ1 = kapO = 2 (S + band)`;
* the regret of a round with the band, `regO`;
* the budgets in `δ`: `2^{-p-2} ≤ 2^{-k}/8`, `n (κ0 + κ1) ≤ 2^{-k}/8`; `2^{-k} < δ` by `DeltaO`.
-/

namespace AdversarialBco.Unified.BudK

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Par)

/-- P°'s parameters at BL-O's confidence `δ_BL = 2^{-19-k}/(d n)³`. -/
noncomputable def poK (d n k : ℕ) : Df2OPar := df2oPar d n (deltaO d n k)

/-- BL-O's PARAM at `k`. -/
def parK (d n k : ℕ) : Par := parN (NeO d n k) d n

/-- The case of the analysis at `k`: `ε ≤ 1/4`. -/
def RunCaseK (d n k : ℕ) : Prop := (poK d n k).eps ≤ 1 / 4


/-- `N_e = 1/δe`. -/
noncomputable def Ne (d n k : ℕ) : ℝ := (NeO d n k : ℝ)
/-- `δe`. -/
noncomputable def de (d n k : ℕ) : ℝ := (poK d n k).δe
/-- `Le`. -/
noncomputable def Le (d n k : ℕ) : ℝ := (poK d n k).Le
/-- `Λ = d N_e`. -/
noncomputable def Lam (d n k : ℕ) : ℝ := d * Ne d n k
/-- `λ`. -/
noncomputable def lam (d n k : ℕ) : ℝ := (poK d n k).lam
/-- `η`. -/
noncomputable def eta (d n k : ℕ) : ℝ := (poK d n k).eta
/-- `ε`. -/
noncomputable def eps (d n k : ℕ) : ℝ := (poK d n k).eps
/-- `ρ`. -/
noncomputable def rho (d n k : ℕ) : ℝ := (poK d n k).rho
/-- `R`. -/
noncomputable def R (d n k : ℕ) : ℝ := (poK d n k).R
/-- `κ_c = η κ λ k0`, so that `c = κ_c Y`. -/
noncomputable def kc (d n k : ℕ) : ℝ := (poK d n k).eta * (poK d n k).kap * (poK d n k).lam * (poK d n k).k0
/-- `Lgb = ln 14 + 5 Le/144`. -/
noncomputable def Lgb (d n k : ℕ) : ℝ := Real.log 14 + 5 * Le d n k / 144
/-- `Ξ = ((8d/3) Lgb)^{1/2}`. -/
noncomputable def Xi (d n k : ℕ) : ℝ := Real.sqrt (8 * d / 3 * Lgb d n k)
/-- `Ξ₁ = Ξ + 1`. -/
noncomputable def Xi1 (d n k : ℕ) : ℝ := Xi d n k + 1
/-- `P̄ = 2 Le^{1/2} + 1`. -/
noncomputable def Pb (d n k : ℕ) : ℝ := 2 * Real.sqrt (Le d n k) + 1
/-- `π̄ = Le^{1/2} + 1/8`. -/
noncomputable def pib (d n k : ℕ) : ℝ := Real.sqrt (Le d n k) + 1 / 8
/-- `Ȳ = 2 Le^{1/2}(1/2 + Lgb^{1/2}) + 4 Le^{1/2}/ε`. -/
noncomputable def Yb (d n k : ℕ) : ℝ :=
  2 * Real.sqrt (Le d n k) * (1 / 2 + Real.sqrt (Lgb d n k)) + 4 * Real.sqrt (Le d n k) / eps d n k
/-- `c̄ = κ_c Ȳ`. -/
noncomputable def cb (d n k : ℕ) : ℝ := kc d n k * Yb d n k
/-- `W° = R + 4d (N_e/Le)^{1/2}`. -/
noncomputable def W0 (d n k : ℕ) : ℝ := R d n k + 4 * d * Real.sqrt (Ne d n k / Le d n k)
/-- `u = 2^{-p}`. -/
noncomputable def tp (d n k : ℕ) : ℝ := 1 / 2 ^ (parK d n k).p
/-- `ê = 2^{-p + 3ℓe + 6ℓd + 64}`. -/
noncomputable def eh (d n k : ℕ) : ℝ := ((parK d n k).eHat : ℝ)
/-- E1: `e_ξ = d^{1/2} 2^{2 - B/2}` (in norm). -/
noncomputable def exi (d n k : ℕ) : ℝ := Real.sqrt d * (4 / 2 ^ ((parK d n k).B / 2))
/-- E1: `e_ζ = 2^{1 - B/2}`. -/
noncomputable def ezt (d n k : ℕ) : ℝ := 2 / 2 ^ ((parK d n k).B / 2)
/-- E2: `e_Y`. -/
noncomputable def eY (d n k : ℕ) : ℝ := tp d n k / 2 + Pb d n k / 2 * (tp d n k + ezt d n k)
/-- E3: `Δ_c`. -/
noncomputable def Dc (d n k : ℕ) : ℝ := cb d n k * tp d n k * (11 / 10 * (Pb d n k + 1) / Yb d n k + 1 / 16)
/-- E3: `e_N`. -/
noncomputable def eN (d n k : ℕ) : ℝ :=
  tp d n k * (1001 / 1000 + 51 / 100 * Xi1 d n k ^ 2) + 143 / 100 * (1 + Xi1 d n k ^ 2) * Dc d n k +
    285 / 100 * cb d n k * Xi1 d n k * exi d n k
/-- E4: `ν = d 2^{-p-1}`. -/
noncomputable def nu (d n k : ℕ) : ℝ := d * tp d n k / 2
/-- E5: `h_a`. -/
noncomputable def ha (d n k : ℕ) : ℝ := tp d n k * (Real.sqrt (8 * Le d n k) + 1) + tp d n k / 16
/-- E5: `x = n Λ e_N`. -/
noncomputable def x (d n k : ℕ) : ℝ := n * Lam d n k * eN d n k
/-- E5: `V = n Λ^{1/2} ν`. -/
noncomputable def V (d n k : ℕ) : ℝ := n * Real.sqrt (Lam d n k) * nu d n k
/-- E5: `ℏ = h_a + V + 2x(2 + h_a)`. -/
noncomputable def hb (d n k : ℕ) : ℝ := ha d n k + V d n k + 2 * x d n k * (2 + ha d n k)
/-- The bound of Lemma TRACK after `j` rounds of an epoch, `(1 + h_a + j Λ^{1/2} ν)(1 + Λ e_N)^j - 1`. -/
noncomputable def hTr (d n k j : ℕ) : ℝ :=
  (1 + ha d n k + j * Real.sqrt (Lam d n k) * nu d n k) * (1 + Lam d n k * eN d n k) ^ j - 1
/-- E6: `X̄`. -/
noncomputable def Xb (d n k : ℕ) : ℝ :=
  Real.sqrt (Lam d n k) * (hb d n k * Xi1 d n k + exi d n k) +
    tp d n k / 16 * lam d n k * (1 + hb d n k) * Real.sqrt (Lam d n k) * Xi1 d n k
/-- E7: `Δ_u`. -/
noncomputable def Du (d n k : ℕ) : ℝ := Real.sqrt (Lam d n k) * (hb d n k * Xi1 d n k + exi d n k)
/-- E8: `Δ_P`. -/
noncomputable def DP (d n k : ℕ) : ℝ := (2 * hb d n k + hb d n k ^ 2) * Lam d n k
/-- E9: `e_b`. -/
noncomputable def eb (d n k : ℕ) : ℝ :=
  Real.sqrt d * tp d n k / 2 + Dc d n k * R d n k * (103 / 100) * Lam d n k * (Xi1 d n k ^ 2 + 1) +
    cb d n k * R d n k * (203 / 100 * Real.sqrt (Lam d n k) * Xi1 d n k * Du d n k + DP d n k)
/-- E9: `e_k`. -/
noncomputable def ek (d n k : ℕ) : ℝ :=
  tp d n k / 2 + Dc d n k * R d n k ^ 2 * (103 / 100) * Lam d n k * (Xi1 d n k ^ 2 + 1) / 2 +
    cb d n k / 2 * R d n k ^ 2 * (203 / 100 * Real.sqrt (Lam d n k) * Xi1 d n k * Du d n k + DP d n k)
/-- E11: `e_g`. -/
noncomputable def eg (d n k : ℕ) : ℝ :=
  Real.sqrt d * tp d n k / 2 + 101 / 100 * (eY d n k + Yb d n k * tp d n k / 16) * (101 / 100) * Real.sqrt (Lam d n k) * Xi1 d n k +
    101 / 100 * Yb d n k * Du d n k
/-- E11: `e_l`. -/
noncomputable def el (d n k : ℕ) : ℝ := tp d n k / 2 + R d n k * eg d n k
/-- E11: `Ḡ`. -/
noncomputable def Gb (d n k : ℕ) : ℝ := n * (101 / 100) * Yb d n k * Real.sqrt (Lam d n k) * Xi d n k
/-- E12: `e_Φ`. -/
noncomputable def ePhi (d n k : ℕ) : ℝ := R d n k ^ 2 / 2 * DP d n k + R d n k * n * eb d n k + n * ek d n k
/-- E13: `e_X`. -/
noncomputable def eX (d n k : ℕ) : ℝ :=
  eta d n k * (101 / 100) * (n * el d n k + R d n k * n * eg d n k) + eta d n k * tp d n k / 16 * (21 / 10) * R d n k * Gb d n k +
    2 * ePhi d n k
/-- `w_ρ = 2^{-p-4} ρ`. -/
noncomputable def wr (d n k : ℕ) : ℝ := tp d n k / 16 * rho d n k
/-- `w_ε = 2^{-p-4} ε`. -/
noncomputable def we (d n k : ℕ) : ℝ := tp d n k / 16 * eps d n k
/-- E14: the Hausdorff gap `h`. -/
noncomputable def h (d n k : ℕ) : ℝ :=
  R d n k * (ePhi d n k + eh d n k + 8 * wr d n k) + 2 * R d n k ^ 3 * we d n k / de d n k ^ 2 + 2 * R d n k * we d n k
/-- `r_min = δe²/(2R(R + 1))`. -/
noncomputable def rmin (d n k : ℕ) : ℝ := de d n k ^ 2 / (2 * R d n k * (R d n k + 1))
/-- `Lip_F = 4R/δe²`. -/
noncomputable def LipF (d n k : ℕ) : ℝ := 4 * R d n k / de d n k ^ 2
/-- E15: the left side of SEL. -/
noncomputable def sel (d n k : ℕ) : ℝ := 4 * eh d n k + LipF d n k * h d n k + wr d n k
/-- E15: the right side of SEL, `(3/4)(δe/d) r_min²`. -/
noncomputable def selR (d n k : ℕ) : ℝ := 3 / 4 * de d n k / d * rmin d n k ^ 2
/-- E16: `Δ_q`. -/
noncomputable def Dq (d n k : ℕ) : ℝ := Dc d n k * (1 + Xi1 d n k ^ 2) + 202 / 100 * cb d n k * Xi1 d n k * exi d n k
/-- E16: `Δs_5`. -/
noncomputable def Ds5 (d n k : ℕ) : ℝ :=
  tp d n k / 2 + 103 / 100 * eta d n k * (eY d n k + 3 * tp d n k / 16 * Yb d n k + Yb d n k * Dq d n k)
/-- E16: `Δ_w`. -/
noncomputable def Dw (d n k : ℕ) : ℝ := Ds5 d n k * Real.sqrt (Lam d n k) * Xi d n k + 103 / 100 * eta d n k * Yb d n k * Du d n k
/-- E16: `Δ_F`. -/
noncomputable def DF (d n k : ℕ) : ℝ :=
  (R d n k + W0 d n k + Dw d n k) ^ 2 / 2 * DP d n k + Lam d n k * Dw d n k * (2 * R d n k + 2 * W0 d n k + Dw d n k) / 2
/-- E16: `L_F`. -/
noncomputable def LF (d n k : ℕ) : ℝ := Lam d n k * (R d n k + W0 d n k)
/-- E16: the left side of VAL. -/
noncomputable def val (d n k : ℕ) : ℝ := 2 * DF d n k + LF d n k * h d n k
/-- E16: the right side of VAL, `δe/(128 n² R² d)`. -/
noncomputable def valR (d n k : ℕ) : ℝ := de d n k / (128 * n ^ 2 * R d n k ^ 2 * d)
/-- E17: `m_par`. -/
noncomputable def mpar (d n k : ℕ) : ℝ := tp d n k / 4 * pib d n k * (R d n k + 10) / eps d n k
/-- E17: the regret transfer term. -/
noncomputable def reg (d n k : ℕ) : ℝ := n / eps d n k * ((1 + 2 * R d n k) * Xb d n k + 4 * R d n k * pib d n k * we d n k)
/-- E17: `κ0 = (4/3)((2 + 16/ε) X̄ + m_par)` (`κ1 = 0`). -/
noncomputable def kap0 (d n k : ℕ) : ℝ := 4 / 3 * ((2 + 16 / eps d n k) * Xb d n k + mpar d n k)
/-- `δbits = 2^{-p-2}` (Lemma BITS). -/
noncomputable def dbits (d n k : ℕ) : ℝ := tp d n k / 4

/-- The enclosures of Lemma ENC: BL's rational parameters `parK d n k` against P°'s `poK d n k`,
relative error `2^{-p-4}` and the stated directions. -/
structure EncOK (d n k : ℕ) : Prop where
  de_eq : de d n k = 1 / Ne d n k
  Le_eq : Le d n k = 36 * Real.log (Ne d n k)
  Le_le : ((parK d n k).Le : ℝ) ≤ Le d n k
  Le_rel : |((parK d n k).Le : ℝ) / Le d n k - 1| ≤ tp d n k / 16
  eps_le : eps d n k ≤ (parK d n k).eps
  eps_rel : ((parK d n k).eps : ℝ) ≤ eps d n k * (1 + tp d n k / 16)
  lam_rel : |((parK d n k).lam : ℝ) / lam d n k - 1| ≤ tp d n k / 16
  eta_rel : |((parK d n k).eta : ℝ) / eta d n k - 1| ≤ tp d n k / 16
  sig2_rel : |((parK d n k).sig2 : ℝ) / (poK d n k).sig2 - 1| ≤ tp d n k / 16
  rho_le : ((parK d n k).rho : ℝ) ≤ rho d n k
  rho_rel : |((parK d n k).rho : ℝ) / rho d n k - 1| ≤ tp d n k / 16
  kapc_rel : |((parK d n k).kapc : ℝ) / kc d n k - 1| ≤ tp d n k / 16
  nu_rel : |((parK d n k).nu : ℝ) * (1 - lam d n k) - 1| ≤ tp d n k / 16
  R_le : R d n k ≤ (parK d n k).R
  R_rel : |((parK d n k).R : ℝ) / R d n k - 1| ≤ tp d n k / 16
  sb_le : ((parK d n k).sb : ℝ) ≤ (poK d n k).sb
  sb_rel : |((parK d n k).sb : ℝ) / (poK d n k).sb - 1| ≤ tp d n k / 16
  W_le : W0 d n k ≤ (parK d n k).W
  W_rel : |((parK d n k).W : ℝ) / W0 d n k - 1| ≤ tp d n k / 16
  A0 : |((parK d n k).A0 : ℝ) / Real.sqrt (poK d n k).sig2 - 1| ≤ tp d n k * Real.sqrt (8 * Le d n k) + tp d n k / 16
  B0 : |((parK d n k).B0 : ℝ) * Real.sqrt (poK d n k).sig2 - 1| ≤ tp d n k + tp d n k / 16
  Lam_eq : ((parK d n k).Lam : ℝ) = Lam d n k
  Ne_eq : ((parK d n k).Ne : ℝ) = Ne d n k
  kap : (poK d n k).kap = 1 / 4
  k0 : (poK d n k).k0 = 1 / (1 - lam d n k) ^ 2
  theta : (poK d n k).theta = 1
  alpha : (poK d n k).alpha = 1 / 4
  c1 : (poK d n k).c1 = 8
  gam : (poK d n k).gam = 1 / 100

/-! ## The terms BL-O adds -/

/-- The gauge band of the play: `|pt' - pt_{ε'}(X')| ≤ 2 η_g π(X') ≤ 2^{-p-1} π̄`. -/
noncomputable def gb (d n k : ℕ) : ℝ := tp d n k / 2 * pib d n k

/-- The band's share of the shift: `gb (2 + (R π̄ + 4)/ε)`. -/
noncomputable def band (d n k : ℕ) : ℝ := gb d n k * (2 + (R d n k * pib d n k + 4) / eps d n k)

/-- v2.1's bound of the shift, `(2 + 16/ε) X̄ + m_par = (3/4) κ0`. -/
noncomputable def S (d n k : ℕ) : ℝ := (2 + 16 / eps d n k) * Xb d n k + mpar d n k

/-- The coefficients of the shift clause: `κ0 = κ1 = 2 (S + band)`. -/
noncomputable def kapO (d n k : ℕ) : ℝ := 2 * (S d n k + band d n k)

/-- The regret transfer term with the band. -/
noncomputable def regO (d n k : ℕ) : ℝ :=
  n / eps d n k * ((1 + 2 * R d n k) * Xb d n k + 4 * R d n k * pib d n k * we d n k + R d n k * gb d n k)

/-- Theorem BUD at `(d, n, k)`, with Lemma ENC and the regime facts of Theorem BUD that the
proofs of pieces C and D read, and the fields BL-O adds. -/
structure BudOK (d n k : ℕ) : Prop where
  enc : EncOK d n k
  /-- Regime: `Le ≥ 17467` (5.1 (F1)). -/
  Le_ge : 17467 ≤ Le d n k
  /-- Regime: `log(14 n/δe) ≤ Lgb` (Lemma DOM (b), fact 1). -/
  Lg_le : df2Lg (poK d n k) n ≤ Lgb d n k
  /-- Regime: Lemma DOM at the bound `c̄`: `c̄ (1 + Ξ₁²) ≤ 10^{-30}`. -/
  cb_le : cb d n k * (1 + Xi1 d n k ^ 2) ≤ 1 / 10 ^ 30
  /-- (P1). -/
  x_le : x d n k ≤ 1
  V_le : V d n k ≤ 1
  hb_le : hb d n k ≤ 1 / 100
  /-- Lemma TRACK's bound stays below `ℏ` over an epoch. -/
  hTr_le : ∀ j ≤ n, hTr d n k j ≤ hb d n k
  /-- (P2) SEL. -/
  sel_le : sel d n k ≤ selR d n k
  /-- (P5). -/
  h_le : h d n k ≤ rmin d n k / 4
  /-- (P3) VAL. -/
  val_le : val d n k ≤ valR d n k
  /-- (P4). -/
  Xb_le : Xb d n k ≤ 1 / 16
  reg_le : reg d n k ≤ 1
  /-- The slack `ê`. -/
  ePhi_le : ePhi d n k ≤ eh d n k
  eX_le : eX d n k ≤ eh d n k
  /-- GUARD (E18). -/
  gT : d * DP d n k ≤ Lam d n k
  gW : Dw d n k ≤ W0 d n k
  gA : 11 / 10 ^ 35 + Dc d n k * (1 + Xi1 d n k ^ 2) ≤ 1 / 2
  /-- The coins: `n (⌈d/2⌉ + 1) 2^{-B/2} ≤ 2^{-p-2}`. -/
  coins : n * ((d + 1) / 2 + 1 : ℕ) * (1 / 2 ^ ((parK d n k).B / 2) : ℝ) ≤ dbits d n k
  /-- The budget of `RunSpec.engine` with `δbits = 2^{-p-2}`, `κ0`, `κ1 = 0`. -/
  budget : n * (dbits d n k + n * kap0 d n k) ≤ 1 / 4
  /-- `κ0 ≥ 0` (asked by piece D: `RunSpec.engine`). -/
  kap0_nonneg : 0 ≤ kap0 d n k

  /-- BL-O: the regret transfer with the band. -/
  regO_le : regO d n k ≤ 1
  /-- BL-O: the shift bound stays below `1/4`, so `r ≥ 3/4`. -/
  S_le : S d n k + band d n k ≤ 1 / 4
  /-- BL-O: the bit budget in `δ`, `2^{-p-2} ≤ 2^{-k}/8`. -/
  bits_k : dbits d n k ≤ (2 : ℝ)⁻¹ ^ k / 8
  /-- BL-O: the engine budget in `δ`, `n (κ0 + κ1) ≤ 2^{-k}/8`. -/
  kap_k : n * (kapO d n k + kapO d n k) ≤ (2 : ℝ)⁻¹ ^ k / 8
  /-- BL-O: `κ0 ≥ 0`. -/
  kapO_nonneg : 0 ≤ kapO d n k

/-- Piece A at `k`: Lemma ENC and Theorem BUD at every `(d, n, k)` of the case. -/
def BudAK : Prop := ∀ d n k : ℕ, 1 ≤ d → 1 ≤ n → RunCaseK d n k → BudOK d n k

end AdversarialBco.Unified.BudK
