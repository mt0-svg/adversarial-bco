/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllSpec
public import AdversarialBco.Unified.PosStage
public import AdversarialBco.Unified.WorldExt
public import AdversarialBco.Bit.BLPosQ

@[expose] public section

/-!
# BL-O as a pure function on `ℚ`, its coin layout, and the contracts of the program and the run

The program BL-O of the paper's section on the program (in full in its appendix on the bit RAM), with UNI-CM,
UNI-GAUGE, UNI-PLAY, UNI-ORDER, UNI-OBS and UNI-DELTA; the analogue of
Bit/BLPure.lean and Bit/RoutQ.lean for the oracle machine of StatementBitRAMO.lean. This file has the definitions and
the statements, as `Prop`s; the proofs are in the modules that import it.

## The pure function

BL-O is BL (Bit/BLPure.lean) with every routine that reads the rows replaced by one that reads the oracle through
UNI-CM (`cmQ`, Unified/SepSpec.lean), the confidence read from the input, the observation read clipped, and the dither
read after the observation.

* **PARAM** (`parO`): BL's `par` with `N_e = 15 · 2^{17 + k_δ} d³ n⁴` (`NeO`), `k_δ` the bit length of
  `⌈1/δ⌉ = ⌈den/num⌉` (`kDel`), so BL-O runs the reference at `δ_BL = 2^{-19-k_δ}/(d n)³`; the precision
  `p = 10 ℓ_e + 16 ℓ_d + 160` with `ℓ_e = len(N_e)`, which now contains `k_δ` (`parN`).
* **The prologue.** The frame is the input `(a, r0, R0)`. The position by TRI-OGD-O (`posO`): TRI-OGD staged of
  Bit/RoutQ.lean with the active row replaced by SEP (`sepE`) on the gauge of the stage body
  `posBody (K ∩ cube(a, 2^{j+1} r0)) P` about `0` (`stSep`): the stage test `stTest` (CM at precision `stK` and the
  cube's rows), the bisection gauge `gaugeIt` with `stJ` steps on `[0, 2^{stEH}]`, SEP at `ℓ₁ = 2^{-(e₁+1)}`,
  `τ = 2^{-e_τ}` (`e₁ = triE1`, `e_τ = triETau`, Unified/PosRow.lean, here in rationals `triE1Q`, `triETauQ`), the base
  point rounded to SEP's grid (`rndPt`), `g = 0` when SEP fails. The cross check (`crossOK`): CM at the precision `kC`
  accepts the `2d` points `μ_S ± A_S e_i/2`. Mode (`mode0O`): `off` if `ε' > 1/2`, else `run` from the epoch start if
  the cross check passes, else `guard`; modes `off` and `guard` play the centre `a`.
* **The round** (`stepO`, `playPtO`). R1a: the draw `ξ'_t` (blocks `0, ..., ⌈d/2⌉ - 1` of round `t`). R2:
  `X' = μ' + (1 - λ') A' ξ'`, the gauge `π̃(X')` by bisection of the CM test at precision `kC` with `jG` steps on
  `[0, 2 |X'|₁]` (`gaugeP`; the upper end `2|X'|₁` is certified by the cross check), `pt' = max(1, π̃/(1 - ε'))`
  (`ptO`), the play `μ_S + A_S X'/pt'`. R3: the reading `clip q ⌊2^p o_t⌋` with `q = qO` (`readO`). R1b: the dither
  `ζ'_t` (the last block of round `t`, read after the observation; its coin indices are BL's). R5 to R15 as in BL, the
  two projections by ELL-O/BIS-O (`apO`, Unified/EllSpec.lean) on the region `{y | μ_S + A_S y/(1 - ε') ∈ K}` ∩ BL's
  quadratic constraint ∩ `B(0, R_int)`, whose K-part is read by CM at the precision `eK + kK` (`CfgO.T`); a call
  with the ball radius `r` passes `r/2` (the ball of (HQ-O) has radius `2r`, Unified/EllSpec.lean `EllOAcc`).
* **The run** (`trajO`, `modeO`, `playO`, `readO`) on a world of the oracle machine (`WorldO`): the losses, the noises,
  the coins and the oracle; the feedback of round `t` is `f_t(x_t) + noise_t`, read by `obsR` as the machine does.

## The coin layout

The prologue reads the coins `0, ..., m_st L' - 1` (`LposO`; stage `j` the coins `j L', ..., j L' + L' - 1`) inside
`P0O` whole blocks of `2B` coins, `K0O = 2 B P0O`. Round `t` reads `nBlk d = ⌈d/2⌉ + 1` blocks of `2B` coins from
`blkStart d K0O B t 0`: the draw blocks before the play, the dither block after the observation. The windows are
`DO t = winL d K0O B t` (the coins read before the blocks of round `t`) and `DO' t = winN d K0O B t` (the coins read at
the play of round `t`), and `SchedOK d K0O B DO DO'` (Unified/WorldGMap.lean) holds (`SchedOKO`).

## The constants of the oracle parts

`kK = ⌈log₂(6 R' R0/r0²)⌉` (`R'` the rational radius of PARAM) is the band factor of UNI-CM in a good position: a
reject of CM at precision `k` at `μ_S + A_S y` puts the gauge of `S(K)` at `y` above `1 - 6·2^{-k} R_g R0/r0²` when
`B̄(0, 1) ⊆ S(K) ⊆ B̄(0, R_g)`, `R_g ≤ R'` (route Sec. 3.1 with the diameter bound `‖A_S^{-1}‖ ≤ R_g/r0`, which gives
`6` in place of the route's `12`). `kC = p + kK + 4` (the play and the cross check: band `≤ 2^{-p-4}`),
`jG = p + 4 + ⌈log₂(2 d R_int)⌉` (the bisection error `2|X'|₁ 2^{-jG} ≤ 2^{-p-4} π(X')`, m4's factor `2√d` included),
the calls at the precision `eK + kK` (band `≤ 2^{-eK}`), `qO = p + ⌈log₂(9 + 4 isqrt(len(14 n N_e)) + isqrt(2B))⌉`
(so `2^{qO} ≥ 2^p (4 + 4 x^{1/2} + (2B)^{1/2})`, `x = ln(14 n N_e)`, route Sec. 3.10).

## The contracts

* For the program text (UNI-PROG, UNI-MACH): `BLOLink P` (the program plays BL-O's pure plays in every round `t < n`,
  on every input and world) and `BLOMachOK P C' k` (the cost, space and coin-window clauses of `TheoremUnified` with
  the windows `DO`, `DO'`).
* For the run (UNI-RUN, the record `RunW` on the extension `extW` of Unified/WorldExt.lean): what the record reads of
  the pure function (`recPos`, `recPlay`, and the mode, configuration, draws, reading and gauge play of round `t`),
  and the facts it consumes: `PlayIntO` (the plays are interior), `SchedOKO` and the locality of the prologue and the
  draws (`PosLocalO`, `DrawLocalO`), `CrossOKO` (the cross check passes in a good position), `TestCertO` (UNI-CM in a
  position), `GaugeBandO` (UNI-GAUGE (b) for the play), `ApSpecO` ((O3) for ELL-O/BIS-O on BL-O's calls),
  `ObsClipO` (UNI-OBS), `DeltaO` (UNI-DELTA), `PosCastO` and `PosSepO`
  (TRI-OGD-O in rationals is `triPosT` of Unified/PosStage.lean, and its field meets `triPosT_bad_sep`'s hypothesis).

## Junk values

`kDel δ` for `δ ≤ 0` is `size ⌈δ⁻¹⌉₊ = 0`; the contracts assume `0 < δ < 1`. `1 - ε'` is positive in mode `run`
(`ε' ≤ 1/2`); in the other modes the play does not read it. The gauge of `0` is `0` (`gaugeP`), so `pt' = 1` there.
A SEP failure in a stage gives the vector `0` (TRI-OGD-O's rule); a SEP failure in a call cuts by `0`, which returns the
kept point (Unified/EllSpec.lean).
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Uni AdversarialBco.Bit.RQ
open AdversarialBco.Bit.BLP (Par St Mode init rnd up dn sqrtDn sqrtUp rndV rndM frob2 lnQ lnErr draw LT Lmu rB eBL
  CallQ)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (clip playedO CostOKO SpaceOKO WeakMemOracle)
open AdversarialBco.Bit (triLay triMst triLa)
open Matrix

variable {d : ℕ}

/-! ## PARAM at the input `δ` (UNI-DELTA) -/

/-- `k_δ`: the bit length of `⌈1/δ⌉ = ⌈den/num⌉` (`kDel_eq` gives the integer form). -/
def kDel (δ : ℚ) : ℕ := (⌈δ⁻¹⌉₊).size

/-- `N_e = 15 · 2^{17 + k} d³ n⁴ = 1/δ_e` at BL-O's confidence `δ_BL = 2^{-19-k}/(d n)³`. -/
def NeO (d n k : ℕ) : ℕ := 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4

/-- BL-O's confidence `δ_BL = 2^{-19-k}/(d n)³`. -/
noncomputable def deltaO (d n k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (19 + k) / ((d : ℝ) * n) ^ 3

/-- Procedure PARAM at `(N_e, d, n)`: BL's `par` (Bit/BLPure.lean) with `N_e` given. -/
def parN (ne d n : ℕ) : Par :=
  let le := ne.size
  let ld := d.size
  let p := 10 * le + 16 * ld + 160
  let q := p + 2 * le.size + 24
  let pF := p + 2 * le + 4 * ld + 40
  let L0 := lnQ q ne
  let ηe := lnErr q ne
  let L1 := lnQ q (2 * d + 2)
  let η1 := lnErr q (2 * d + 2)
  let rn := sqrtDn q n
  let rd := sqrtDn q d
  let Le := 36 * (L0 - ηe)
  let Lehi := 36 * (L0 + ηe)
  let lam := rnd pF (1 / (725 * d * Le ^ 2))
  let eta := rnd pF (rd / (Le * rn))
  let R := up pF (134 * d * sqrtUp q (L1 + η1))
  let s := sqrtUp q (rnd pF (1 / (8 * Le)))
  { p := p
    q := q
    pF := pF
    B := 2 * (p + (n * (d + 2)).size + 2)
    Ne := ne
    Lam := d * ne
    Le := Le
    eps := up pF (14500 * d * (rd + 1 / 2 ^ q) * Lehi ^ 5 / rn)
    lam := lam
    eta := eta
    sig2 := rnd pF (1 / (8 * Le))
    rho := dn pF (1450 * d ^ 2 * Le ^ 3)
    kapc := rnd pF (eta * lam / (4 * (1 - lam) ^ 2))
    nu := rnd pF (1 / (1 - lam))
    R := R
    sb := dn pF (1 / ((ne : ℚ) ^ 2 * R * (R + 1)))
    W := up pF (R + 4 * d * sqrtUp q (ne / Le))
    A0 := rnd p s
    B0 := rnd p (1 / s)
    Rint := ⌈R⌉₊
    eHat := 1 / 2 ^ (p - 3 * le - 6 * ld - 64) }

/-- PARAM of BL-O at the input `(d, n, δ)`. -/
def parO (d n : ℕ) (δ : ℚ) : Par := parN (NeO d n (kDel δ)) d n

/-! ## TRI-OGD-O in rationals (UNI-POS) -/

/-- `triNeT = triNe + 1` (one doubling of `N'`, Unified/PosRow.lean). -/
def triNeTQ (d ℓ : ℕ) : ℕ := triNeQ d ℓ + 1

/-- `triGuT = (65/64) triGu`. -/
def triGuTQ (d : ℕ) : ℚ := triGuQ d + triGuQ d / 64

/-- `triJsT`, the step `2^{-j_s'}` at `G_up'` and the new `N'`. -/
def triJsTQ (d ℓ : ℕ) : ℕ := Nat.clog 4 ⌈(triGuTQ d + triBuQ d) ^ 2 * 2 ^ triNeTQ d ℓ / triD2Q d⌉₊

/-- `triLT`, the coins of one stage: `N'` draws of `2 d B_g` coins. -/
def triLTQ (d ℓ : ℕ) : ℕ := 2 ^ triNeTQ d ℓ * (2 * d * triBgQ d)

/-- `triE1`: `ℓ₁ = 2^{-e₁} ≤ e_lo/64`. -/
def triE1Q (d : ℕ) : ℕ := Nat.clog 2 ⌈64 / triEloQ d⌉₊

/-- `triETau`: `τ = 2^{-e_τ}`. -/
def triETauQ (d : ℕ) : ℕ := Nat.clog 2 ⌈64 * d * (1 + 8 * d * triKgQ d) * (triD2Q d + 1) / triEloQ d⌉₊

/-- A rational majorant of `triRz d`, the radius of the base points: `d r + 8 d² k_g b`. -/
def triRzQ (d : ℕ) : ℚ := d * triRQ d + 8 * d ^ 2 * triKgQ d * triBQ d

/-- A natural majorant of `triRa d = 2^{L} - 1`, the outer radius of a stage body. -/
def triRaQ (d : ℕ) : ℕ := 2 ^ triLa (triSQ d)

/-- SEP's `e₁` in a stage: `ℓ₁ = 2^{-(triE1 + 1)}`, half of TRI-OGD-O's, the other half for rounding the base point. -/
def stE1 (d : ℕ) : ℕ := triE1Q d + 1

/-- SEP's grid exponent in a stage (`e_L = 0`, the gauge of a body with `B̄(0, 1)` inside is `1`-Lipschitz). -/
def stE (d : ℕ) : ℕ := stE1 d + d * (2 * (triETauQ d + 3) + 6 + triETauQ d)

/-- The upper end `2^{stEH} ≥ triRz + 1` of the gauge's bisection on SEP's points. -/
def stEH (d : ℕ) : ℕ := Nat.clog 2 ⌈triRzQ d + 1⌉₊

/-- `η_min ≥ 2^{-stEEta}` (`e_L = 0`, `J + 1 = e_τ + 4`). -/
def stEEta (d : ℕ) : ℕ := triETauQ d + stE1 d + 11 + 3 * d * (triETauQ d + 4)

/-- The bisection steps of the stage gauge. -/
def stJ (d : ℕ) : ℕ := stEEta d + stEH d + 1

/-- The scale of SEP's values in a stage: the counter `u` is the value `u/2^{stEu}`. -/
def stEu (d : ℕ) : ℕ := stEEta d + 1

/-- The CM precision of the stage test: band `6·2^{-k} ρ_a R0/r0² ≤ 2^{-(stEEta + stEH + 2)}`. -/
def stK (d : ℕ) (r0 R0 : ℚ) : ℕ := stEEta d + stEH d + 2 + Nat.clog 2 ⌈6 * triRaQ d * R0 / r0 ^ 2⌉₊

/-- The stage test at stage `j` in the position `P`: CM accepts `μ_P + T_P y` and that point lies in the cube
`|· - a|_∞ ≤ 2^{j+1} r0`. -/
def stTest (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d) (y : Fin d → ℚ) :
    Bool :=
  cmQ orc a r0 (stK d r0 R0) (P.1 + P.2 *ᵥ y) && decide (∀ i, |(P.1 + P.2 *ᵥ y) i - a i| ≤ 2 ^ (j + 1) * r0)

/-- SEP's evaluator in a stage: the counter of `stJ` steps of the bisection gauge of the stage test about `0` at
`X/2^{stE}` on `[0, 2^{stEH}]`. -/
def stEv (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d) (X : Fin d → ℤ) : ℤ :=
  ((gaugeIt (stTest orc a r0 R0 j P) 0 (ptDN (2 ^ stE d) X) ((2 : ℚ) ^ stEH d) (stJ d) (stJ d)).2 : ℤ)

/-- The nearest point of the grid `2^{-E}`, as numerators. -/
def rndPt (E : ℕ) (z : Fin d → ℚ) : Fin d → ℤ := fun i => ⌊z i * 2 ^ E + 1 / 2⌋

/-- **The SEP field of the stages**: SEP on the stage gauge from the base point `z` rounded to the grid, the vector
`G/2^{stEu + 1}`, `0` when SEP fails. -/
def stSep (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d) (z : Fin d → ℚ) :
    Fin d → ℚ :=
  match sepE (stEv orc a r0 R0 j P) (rndPt (stE d) z) (stE d) (stE1 d) (triETauQ d) 0 (stEu d) with
  | none => 0
  | some (_, G) => fun i => (G i : ℚ) / 2 ^ (stEu d + 1)

/-- The core of TRI-OGD-O with the field `u` on the draws `y` (`triCoreOutT` of Unified/PosStage.lean in rationals). -/
def triCoreOutOQ (d ℓ : ℕ) (u : (Fin d → ℚ) → Fin d → ℚ) (y : ℕ → Fin d → ℚ) : PosQ d :=
  triAvgQ (triRQ d) (triAQ d) (triBQ d) (1 / 2 ^ triJsTQ d ℓ) (fun x w => triRoundQ (triBvQ d) (triVQ u x w)) y
    (2 ^ triNeTQ d ℓ)

/-- Stage `j` from the position `P` on the coins `x` of the stage. -/
def triStepOQ (gs : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (ℓ j : ℕ) (P : PosQ d) (x : ℕ → Bool) : PosQ d :=
  pgCompQ P (triCoreOutOQ d ℓ (gs j P) fun t => triDrawQ d (triBgQ d) x t)

/-- The position after the stages `0, ..., j - 1`, from `(c, r0 I)`. -/
def triStageNOQ (gs : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ : ℕ)
    (ω : ℕ → ℕ → Bool) : ℕ → PosQ d
  | 0 => (c, r0 • 1)
  | j + 1 => triStepOQ gs ℓ j (triStageNOQ gs c r0 ℓ ω j) (ω j)

/-- TRI-OGD-O in rationals: stage `j` reads the coins `j L', ..., j L' + L' - 1` of `cs`. -/
def triPosOQ (gs : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (c : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (cs : ℕ → Bool) :
    PosQ d :=
  triStageNOQ gs c r0 ℓ (fun j k => cs (triLay (triMstQ r0 R0) (triLTQ d ℓ) (j, k))) (triMstQ r0 R0)

/-- The confidence integer of the position: `ℓ_pos = ⌈log₂(3 · 2^{19+k} (d n)³ m_st)⌉ ≥ log(m_st/δ₁)`,
`δ₁ = δ_BL/3`. -/
def ellPosO (d n k : ℕ) (r0 R0 : ℚ) : ℕ := Nat.clog 2 (3 * 2 ^ (19 + k) * (d * n) ^ 3 * triMstQ r0 R0)

/-- P2 POS of BL-O: TRI-OGD-O on the frame `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` with the SEP field of the stages. -/
def posO (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs : ℕ → Bool) : PosQ d :=
  triPosOQ (stSep orc a r0 R0) a r0 R0 (ellPosO d n (kDel δ) r0 R0) cs

/-! ## The coin layout -/

/-- The coins of the position: `m_st L'`. -/
def LposO (d n : ℕ) (δ r0 R0 : ℚ) : ℕ := triMstQ r0 R0 * triLTQ d (ellPosO d n (kDel δ) r0 R0)

/-- The prologue blocks: `⌈m_st L'/(2B)⌉`. -/
def P0O (d n : ℕ) (δ r0 R0 : ℚ) : ℕ := (LposO d n δ r0 R0 + 2 * (parO d n δ).B - 1) / (2 * (parO d n δ).B)

/-- The coins of the prologue: `K0 = 2 B P0`, a whole number of blocks. -/
def K0O (d n : ℕ) (δ r0 R0 : ℚ) : ℕ := 2 * (parO d n δ).B * P0O d n δ r0 R0

/-- The loss window `D t`: the coins read before the blocks of round `t`. -/
def DO (d n : ℕ) (δ r0 R0 : ℚ) (_a : Fin d → ℚ) : ℕ → ℕ := World.winL d (K0O d n δ r0 R0) (parO d n δ).B

/-- The noise window `D' t`: the coins read at the play of round `t` (before its dither block). -/
def DO' (d n : ℕ) (δ r0 R0 : ℚ) (_a : Fin d → ℚ) : ℕ → ℕ := World.winN d (K0O d n δ r0 R0) (parO d n δ).B

/-- R1: the draw `ξ'_t` and the dither `ζ'_t` of round `t` on BL's schedule with the prologue `K0O`. -/
def drawO (d n : ℕ) (δ r0 R0 : ℚ) (cs : ℕ → Bool) (t : ℕ) : (Fin d → ℚ) × ℚ :=
  draw cs (K0O d n δ r0 R0) (parO d n δ).B d t

/-! ## The configuration, the gauge play, the calls -/

/-- What BL-O reads after its prologue: the parameters, the horizon, the frame, the position. -/
structure CfgO (d : ℕ) where
  par : Par
  n : ℕ
  a : Fin d → ℚ
  r0 : ℚ
  R0 : ℚ
  μS : Fin d → ℚ
  AS : Matrix (Fin d) (Fin d) ℚ

namespace CfgO

variable (c : CfgO d)

/-- The band factor of UNI-CM in a position: `6 R' R0/r0² ≤ 2^{kK}`. -/
def kK : ℕ := Nat.clog 2 ⌈6 * c.par.R * c.R0 / c.r0 ^ 2⌉₊

/-- The CM precision of the play and of the cross check. -/
def kC : ℕ := c.par.p + c.kK + 4

/-- The bisection steps of the play gauge. -/
def jG : ℕ := c.par.p + 4 + Nat.clog 2 (2 * d * c.par.Rint)

/-- The range of the clipped reading. -/
def qO : ℕ := c.par.p + Nat.clog 2 (9 + 4 * Nat.sqrt (14 * c.n * c.par.Ne).size + Nat.sqrt (2 * c.par.B))

/-- The CM test at the precision `k` and the scale `s`: one query at `cmPt a r0 k (μ_S + A_S (s y))`. -/
def T (orc : (Fin d → ℚ) → ℕ → Bool) (k : ℕ) (s : ℚ) (y : Fin d → ℚ) : Bool :=
  cmQ orc c.a c.r0 k (c.μS + c.AS *ᵥ (s • y))

/-- The position as a point of `PgSp d`. -/
noncomputable def S : PgSp d := castP (c.μS, c.AS)

end CfgO

/-- The cross check: CM at the precision `kC` accepts the `2d` points `μ_S ± A_S e_i/2`. -/
def crossOK (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) : Prop :=
  ∀ i : Fin d, c.T orc c.kC 1 (Pi.single i (1 / 2)) = true ∧ c.T orc c.kC 1 (Pi.single i (-1 / 2)) = true

instance (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) : Decidable (crossOK orc c) := by
  unfold crossOK; infer_instance

/-- `|x|₁`. -/
def l1 (x : Fin d → ℚ) : ℚ := ∑ i, |x i|

/-- R2, the gauge of `X'` by bisection of the CM test on `[0, 2|X'|₁]` (UNI-GAUGE); `0` at `X' = 0`. -/
def gaugeP (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (X : Fin d → ℚ) : ℚ :=
  if X = 0 then 0 else gaugeQ (c.T orc c.kC 1) 0 X (2 * l1 X) c.jG

/-- `pt' = max(1, π̃(X')/(1 - ε'))`. -/
def ptO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (X : Fin d → ℚ) : ℚ := max 1 (gaugeP orc c X / (1 - c.par.eps))

/-- `X' = μ' + (1 - λ') A'ξ'`. -/
def XO (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) : Fin d → ℚ := st.mu + (1 - c.par.lam) • (st.A *ᵥ ξ)

/-- R2, the play: `μ_S + A_S (X'/pt')` in mode `run`, the centre `a` in modes `off` and `guard`. -/
def playPtO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (mo : Mode d) (ξ : Fin d → ℚ) : Fin d → ℚ :=
  match mo with
  | .off => c.a
  | .guard => c.a
  | .run st => c.μS + c.AS *ᵥ ((ptO orc c (XO c st ξ))⁻¹ • XO c st ξ)

/-- A call of BL-O: BL's call data (`CallQ`) with no rows, the radius `R_int`. -/
def callO (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ)
    (f : Fin d → ℚ) (e : ℚ) : CallQ d :=
  ⟨0, Fin.elim0, Fin.elim0, H, g, ℓ, c.par.Rint, r, P, f, e⟩

/-- The integer call of ELL-O: the denominators of the quadratic constraint and of the objective cleared as in
`clearQ`, the radius slot `r/2` (the ball of (HQ-O) has radius `2r`), the K-part's centre `0` with inner radius
`2^{-1}`. -/
def clearO (D : CallQ d) : EllOI d :=
  ⟨(clearQ D).H, (clearQ D).g, (clearQ D).ℓ, (clearQ D).P, (clearQ D).f, (clearQ D).Df, D.R, D.r / 2, (clearQ D).e,
    1, 0, 1⟩

/-- R11, R14: ELL-O/BIS-O on a call, the K-part read by the CM test at the scale `(1 - ε')⁻¹` and the precision
`eK + kK`; the point `x/2^{ellExpO}`. -/
def apO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (D : CallQ d) : Option (Fin d → ℚ) :=
  (ellOI (clearO D) (c.T orc ((clearO D).eK + c.kK) (1 - c.par.eps)⁻¹)).map
    fun x i => (x i : ℚ) / 2 ^ ellExpO (clearO D)

/-- The round after the play (R5 YOBS to R15 COMMIT), from the mode before the round, the draw `ξ'`, the dither `ζ'`
(read after the observation) and the reading `obs`: BL's `step` with the gauge play `ptO` and the calls `apO`. -/
def stepO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (mo : Mode d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ) :
    Mode d :=
  match mo with
  | .off => .off
  | .guard => .guard
  | .run st =>
    let P := c.par
    let w := st.A *ᵥ ξ
    let X := XO c st ξ
    let pt := ptO orc c X
    -- R5 YOBS
    let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
    -- R7 FACTOR
    let cc := P.kapc * Y
    let a := 1 - cc
    let q := a + cc * (ξ ⬝ᵥ ξ)
    if a < 1 / 2 ∨ q < 1 / 2 then .guard else
    let s1 := sqrtDn P.p (1 / a)
    let s3 := sqrtDn P.p a
    let rq := sqrtDn P.p q
    let s2 := rnd P.p (cc / (s3 * rq * (s3 + rq)))
    let s4 := rnd P.p (cc / (s3 + rq))
    -- R8 PAIR
    let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
    let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
    -- R9 INCR
    let u := st.B *ᵥ ξ
    let v := st.Bᵀ *ᵥ st.mu
    let b' := st.b + rndV P.p (cc • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
    let k' := st.k + rnd P.p (cc / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
    let g := rndV P.p ((Y * P.nu) • u)
    let G' := st.G + g
    let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
    -- R10 TRACE
    if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then .guard else
    let Pp := B' * B'ᵀ
    let wp := b' - (P.eta / 2) • G'
    -- R11 TEST
    let callT : CallQ d :=
      if st.first then callO c 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
      else callO c (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
    match apO orc c callT with
    | none => .guard
    | some p' =>
      -- R12 FIRE
      if P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat then
        .run (init P d)
      else
      -- R13 WMU
      let s5 := rnd P.p (P.eta * Y * P.nu / q)
      let wmu := st.mu - s5 • w
      if (2 * P.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else
      -- R14 LINE
      match apO orc c (callO c Pp b' (Lmu P - k') (rB P / 2) Pp (Pp *ᵥ wmu) (eBL P d n)) with
      | none => .guard
      -- R15 COMMIT
      | some mu' => .run ⟨false, mu', A', B', b', k', G', l'⟩

/-! ## The prologue and the run -/

/-- BL-O's configuration on the input `(d, n, δ, r0, R0, a)`, the oracle `orc` and the coins `cs`. -/
def cfgO (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs : ℕ → Bool) : CfgO d :=
  ⟨parO d n δ, n, a, r0, R0, (posO d n orc δ r0 R0 a cs).1, (posO d n orc δ r0 R0 a cs).2⟩

/-- P5 MODE: `off` if `ε' > 1/2`; else `run` at the epoch start if the cross check passes, else `guard`. -/
def mode0O (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) : Mode d :=
  if 1 / 2 < c.par.eps then .off else if crossOK orc c then .run (init c.par d) else .guard

/-- The configuration on the world `w`. -/
def cfgW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) : CfgO d := cfgO d n w.orc δ r0 R0 a w.cs

/-- BL-O's run on the world `w`: the mode before round `t` and the points played in the rounds `< t` (`0` from round
`t` on). The reading of round `t` is `clip q ⌊2^p (f_t(x'_t) + noise_t)⌋`, as instruction `obsR` reads it. -/
noncomputable def trajO (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) : ℕ → Mode d × (ℕ → Fin d → ℚ)
  | 0 => (mode0O w.orc (cfgW d n δ r0 R0 a w), fun _ => 0)
  | t + 1 =>
    let c := cfgW d n δ r0 R0 a w
    let prev := trajO d n δ r0 R0 a w t
    let dr := drawO d n δ r0 R0 w.cs t
    let x := playPtO w.orc c prev.1 dr.1
    let o : ℤ := clip c.qO ⌊(2 : ℝ) ^ c.par.p * (w.f t (toE x) + w.noise t)⌋
    (stepO w.orc c n prev.1 dr.1 dr.2 o, Function.update prev.2 t x)

/-- BL-O's mode before round `t`. -/
noncomputable def modeO (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : Mode d :=
  (trajO d n δ r0 R0 a w t).1

/-- BL-O's play of round `t`, a rational point. -/
noncomputable def playO (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : Fin d → ℚ :=
  playPtO w.orc (cfgW d n δ r0 R0 a w) (modeO d n δ r0 R0 a w t) (drawO d n δ r0 R0 w.cs t).1

/-- BL-O's reading of round `t`: `clip q ⌊2^p (f_t(x'_t) + noise_t)⌋`. -/
noncomputable def readO (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : ℤ :=
  clip (cfgW d n δ r0 R0 a w).qO
    ⌊(2 : ℝ) ^ (parO d n δ).p * (w.f t (toE (playO d n δ r0 R0 a w t)) + w.noise t)⌋

/-! ## What the run record on the extension reads -/

section Record

variable {Ω : Type}

/-- The position of the record (`RunW.pos`) on the extension `Ω × (ℕ → ℝ)`: BL-O's position on the environment's
coins. -/
noncomputable def recPos (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (coin : Ω → ℕ → Bool) (δ r0 R0 : ℚ)
    (a : Fin d → ℚ) (p : Ω × (ℕ → ℝ)) : PgSp d :=
  castP (posO d n orc δ r0 R0 a (coin p.1))

/-- The play of the record (`RunW.play`): BL-O's play of round `t` on the environment's world (`envWorld`). -/
noncomputable def recPlay (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
    (noise : ℕ → Ω → ℝ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (t : ℕ) (p : Ω × (ℕ → ℝ)) : E d :=
  toE (playO d n δ r0 R0 a (envWorld orc coin loss noise p.1) t)

end Record

/-! ## The contracts of the program text (UNI-PROG, UNI-MACH) -/

/-- **The machine clauses** of `TheoremUnified` for `P` with the windows of BL-O, on every input and every world:
cost and space within `C' (d log(2dn/δ) S)^k`, and the coin windows `DO`, `DO'`. -/
def BLOMachOK (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → 0 < r0 → r0 ≤ R0 →
    ∀ w : BitRAMO.WorldO d,
      CostOKO P w (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
        SpaceOKO P w (initU d n δ r0 R0 a) n
          (C' * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k) ∧
        CoinWindowsOK P w (initU d n δ r0 R0 a) n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a)

/-! ## The facts the run consumes -/

/-- The frame of a configuration: `K` convex and closed, `0 < r0 ≤ R0`, `B̄(a, r0) ⊆ K ⊆ B̄(a, R0)` and `orc` a
weak membership oracle of `K`. -/
def FrameO (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) : Prop :=
  Convex ℝ K ∧ IsClosed K ∧ 0 < c.r0 ∧ c.r0 ≤ c.R0 ∧ Metric.closedBall (toE c.a) (c.r0 : ℝ) ⊆ K ∧
    K ⊆ Metric.closedBall (toE c.a) (c.R0 : ℝ) ∧ WeakMemOracle K orc

/-- The body in the position of `c`: `S(K) = {y | μ_S + A_S y ∈ K}`. -/
noncomputable def bodyS (K : Set (E d)) (c : CfgO d) : Set (E d) := posBody K (pgMu c.S) (pgOp c.S)

/-- The position of `c` is good for `K` at the radius `Rg`: `B̄(0, 1) ⊆ S(K) ⊆ B̄(0, Rg)`. -/
def GoodPos (K : Set (E d)) (c : CfgO d) (Rg : ℝ) : Prop :=
  Metric.closedBall 0 1 ⊆ bodyS K c ∧ bodyS K c ⊆ Metric.closedBall 0 Rg

/-- The K-part at the scale `s`: `{y | μ_S + A_S (s y) ∈ K}`, in the coordinates of `TestCert`. -/
def QKs (K : Set (E d)) (c : CfgO d) (s : ℚ) : Set (Fin d → ℝ) := {y | WithLp.toLp 2 ((s : ℝ) • y) ∈ bodyS K c}

/-- **UNI-CM, UNI-GAUGE (a): the plays are interior.** For every input, every convex `K` with `B̄(a, r0) ⊆ K` and
every world whose oracle is a weak membership oracle of `K`, every play of BL-O lies in the interior of `K`. -/
def PlayIntO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (w : BitRAMO.WorldO d), 1 ≤ d → 0 < r0 → Convex ℝ K →
    Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → WeakMemOracle K w.orc →
    ∀ t, toE (playO d n δ r0 R0 a w t) ∈ interior K

/-- **The schedule**: BL-O's layout is a schedule of the extension (Unified/WorldGMap.lean). -/
def SchedOKO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ),
    World.SchedOK d (K0O d n δ r0 R0) (parO d n δ).B (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a)

/-- **The prologue reads the coins below `K0`**: the position, hence the configuration and the first mode, depend on
the coins `0, ..., K0O - 1` only, and `m_st L' ≤ K0O`. -/
def PosLocalO : Prop :=
  ∀ (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs cs' : ℕ → Bool),
    0 < δ → (∀ j < K0O d n δ r0 R0, cs j = cs' j) →
      LposO d n δ r0 R0 ≤ K0O d n δ r0 R0 ∧ posO d n orc δ r0 R0 a cs = posO d n orc δ r0 R0 a cs'

/-- **UNI-ORDER: the draws in their windows.** The draw `ξ'_t` reads the coins in `[D t, D' t)`, the dither `ζ'_t`
those in `[D' t, D (t + 1))`. -/
def DrawLocalO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs cs' : ℕ → Bool) (t : ℕ),
    ((∀ j, DO d n δ r0 R0 a t ≤ j → j < DO' d n δ r0 R0 a t → cs j = cs' j) →
      (drawO d n δ r0 R0 cs t).1 = (drawO d n δ r0 R0 cs' t).1) ∧
    ((∀ j, DO' d n δ r0 R0 a t ≤ j → j < DO d n δ r0 R0 a (t + 1) → cs j = cs' j) →
      (drawO d n δ r0 R0 cs t).2 = (drawO d n δ r0 R0 cs' t).2)

/-- **The cross check in the case** (UNI-GAUGE, route Sec. 3.2): in a good position at a radius `Rg ≤ R'`, CM at the
precision `kC` accepts the `2d` points `μ_S ± A_S e_i/2`. -/
def CrossOKO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (Rg : ℝ),
    FrameO K orc c → GoodPos K c Rg → 1 ≤ Rg → Rg ≤ c.par.R → crossOK orc c

/-- **UNI-CM in a position** (route Sec. 3.1): in a good position at a radius `Rg ≥ 1`, the CM test at the precision `k`
and the scale `s > 0` certifies the K-part `QKs s` about `0` with the band `6·2^{-k} Rg R0/r0²`. -/
def TestCertO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (Rg : ℝ) (k : ℕ) (s : ℚ),
    FrameO K orc c → GoodPos K c Rg → 1 ≤ Rg → 0 < s →
    TestCert (c.T orc k s) (QKs K c s) 0 (6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2)

/-- **UNI-GAUGE (b) for the play** (m4's factor included): in a good position at a radius `1 ≤ Rg ≤ R' ≤ R_int`, the
gauge play is within the band `2^{-p-2}` of the gauge of `S(K)`. -/
def GaugeBandO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (Rg : ℝ) (X : Fin d → ℚ),
    1 ≤ d → FrameO K orc c → GoodPos K c Rg → 1 ≤ Rg → Rg ≤ c.par.R → (c.par.R : ℝ) ≤ c.par.Rint →
    gauge (bodyS K c) (toE X) ≤ gaugeP orc c X ∧
      (gaugeP orc c X : ℝ) ≤ (1 + (2 : ℝ)⁻¹ ^ (c.par.p + 2)) * gauge (bodyS K c) (toE X)

/-- The region of a call (rows ignored): `{y | yᵀHy/2 - g·y ≤ ℓ, |y| ≤ R}`. -/
def regionC (D : CallQ d) : Set (Fin d → ℝ) :=
  {y | y ⬝ᵥ (D.H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (D.g j : ℝ)) ⬝ᵥ y ≤ D.ℓ ∧ oNorm y ≤ D.R}

/-- **(O3) for BL-O's calls** (UNI-ELL with the band of UNI-CM): in a good position at a radius `Rg ≤ R'` with
`ε' ≤ 1/2`, a call whose region `QK ∩ regionC` (`QK = QKs (1 - ε')⁻¹`) holds a ball of radius `r > 0`, with `P ≻ 0`,
`H ⪰ 0`, `R ≥ 1`, `e > 0`, returns a point of that region within `e` of the infimum of the objective there. -/
def ApSpecO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (Rg : ℝ) (D : CallQ d) (a0 : Fin d → ℝ),
    1 ≤ d → FrameO K orc c → GoodPos K c Rg → 1 ≤ Rg → Rg ≤ c.par.R → 0 ≤ c.par.eps → c.par.eps ≤ 1 / 2 →
    1 ≤ D.R → 0 < D.r → 0 < D.e → (D.P.map ((↑) : ℚ → ℝ)).PosDef → (D.H.map ((↑) : ℚ → ℝ)).PosSemidef →
    oBall a0 D.r ⊆ QKs K c (1 - c.par.eps)⁻¹ ∩ regionC D →
    ∃ μ, apO orc c D = some μ ∧ (fun j => (μ j : ℝ)) ∈ QKs K c (1 - c.par.eps)⁻¹ ∩ regionC D ∧
      ∀ y ∈ QKs K c (1 - c.par.eps)⁻¹ ∩ regionC D,
        Bit.BLP.CallQ.obj D (fun j => (μ j : ℝ)) ≤ Bit.BLP.CallQ.obj D y + D.e

/-- **UNI-OBS**: a feedback within `4 + 4 (ln(14 n N_e))^{1/2} + (2B)^{1/2}` is read unclipped, within `2^{-p}`. -/
def ObsClipO : Prop :=
  ∀ (d : ℕ) (c : CfgO d) (o : ℝ), 1 ≤ c.n → 1 ≤ c.par.Ne →
    |o| ≤ 4 + 4 * Real.sqrt (Real.log (14 * c.n * c.par.Ne)) + Real.sqrt (2 * c.par.B) →
    clip c.qO ⌊(2 : ℝ) ^ c.par.p * o⌋ = ⌊(2 : ℝ) ^ c.par.p * o⌋ ∧
      |(⌊(2 : ℝ) ^ c.par.p * o⌋ : ℝ) / 2 ^ c.par.p - o| ≤ (2 : ℝ)⁻¹ ^ c.par.p

/-- **UNI-DELTA**: `1/δ < 2^{k_δ} ≤ 4/δ`, so `δ_BL ≤ 2^{-19} δ/(d n)³`, `N_e δ_BL` is BL's, and
`log(2 d n/δ_BL) ≤ 22 log(2 d n/δ)`; the integer form of `k_δ`. -/
def DeltaO : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 →
    1 / (δ : ℝ) < 2 ^ kDel δ ∧ (2 : ℝ) ^ kDel δ ≤ 4 / δ ∧
    deltaO d n (kDel δ) ≤ (2 : ℝ)⁻¹ ^ 19 * δ / ((d : ℝ) * n) ^ 3 ∧
    (NeO d n (kDel δ) : ℝ) * deltaO d n (kDel δ) = 15 * n / 4 ∧
    Real.log (2 * d * n / deltaO d n (kDel δ)) ≤ 22 * Real.log (2 * d * n / δ) ∧
    kDel δ = ((δ.den + δ.num.toNat - 1) / δ.num.toNat).size

/-! ## The position against TRI-OGD-O (Unified/PosMain.lean) -/

open Classical in
/-- The real field of the stages from the rational one: at a rational position and a rational base point the cast of
`stSep`, `0` elsewhere. -/
noncomputable def stSepR (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PgSp d)
    (z : E d) : E d :=
  if h : ∃ q : PosQ d × (Fin d → ℚ), castP q.1 = P ∧ toE q.2 = z then
    toE (stSep orc a r0 R0 j (Classical.choose h).1 (Classical.choose h).2)
  else 0

/-- **TRI-OGD-O in rationals is `triPosT`** (Unified/PosStage.lean) with the real field `stSepR`. -/
def PosCastO : Prop :=
  ∀ (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs : ℕ → Bool), 1 ≤ d → 0 < r0 →
    castP (posO d n orc δ r0 R0 a cs) =
      UniPos.triPosT (stSepR orc a r0 R0) (toE a) r0 R0 (ellPosO d n (kDel δ) r0 R0) cs

/-- **The field of the stages meets `triPosT_bad_sep`'s hypothesis** (Unified/PosMain.lean, `hout`): at every good
rational stage position and rational base point in range, the vector is a SEP output in the form of `SepAcc`'s
conclusion for the gauge of the stage body. -/
def PosSepO : Prop :=
  ∀ (d : ℕ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ), 1 ≤ d → Convex ℝ K →
    IsClosed K → 0 < r0 → Metric.closedBall (toE a) (r0 : ℝ) ⊆ K → K ⊆ Metric.closedBall (toE a) (R0 : ℝ) →
    WeakMemOracle K orc →
    ∀ (j : ℕ) (P : PgSp d), UniPos.IsRatPg P → (pgMat P).det ≠ 0 →
      PgBody (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (Bit.triRa d) →
      ∀ z, UniPos.IsRatE z → ‖z‖ ≤ UniPos.triRz d → ∃ y : Fin d → ℝ,
        oNorm (y - WithLp.ofLp z) ≤ 64 / 63 * (1 / 2 ^ UniPos.triE1 d) ∧
        ∀ v : Fin d → ℝ, gauge (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P))
            (WithLp.toLp 2 y) + WithLp.ofLp (stSepR orc a r0 R0 j P z) ⬝ᵥ (v - y) -
            1 / 2 ^ UniPos.triETau d * ∑ i, |v i - y i| ≤
          gauge (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (WithLp.toLp 2 v)

/-- **The field of the stages is measurable** (`triPosT_bad_sep`'s `hgs`): it vanishes off the countable set of
rational points. -/
def PosFieldMeasO : Prop :=
  ∀ (d : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ),
    Measurable fun q : PgSp d × E d => stSepR orc a r0 R0 j q.1 q.2

end AdversarialBco.Unified.BLO
