/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutM
public import AdversarialBco.Bit.BLLink

@[expose] public section

/-!
# BL's program on the machine, part 0: the invariant `BLInv`

`BLInv L n m K0 E cfg mo t σ` says that the environment `σ` of the extended language holds BL's configuration `cfg`
(Bit/BLPure.lean, `Cfg`: the parameters of PARAM, the position, the frame centre) and BL's mode `mo` before round `t`,
on the input with `n` rounds and `m` rows, `K0` coins of the prologue, every persistent integer at most `2^E` in
absolute value. It is the interface between the prologue of BL's program (piece F1: P0, P1 to P5 with PARAM, which
must end in `BLInv` at `t = 0`) and the round (piece F2: R1 to R15, which keeps it from `t` to `t + 1`).

**Layout.** BL's own area is the registers `0, ..., nN0 - 1`, the slots `0, ..., nS0 - 1` and the arrays
`0, ..., nA0 - 1`; the routines of Interface II (Bit/RoutM.lean) run with their blocks at the bases `o = nS0`,
`rE = nN0`, `aW = nA0`. Of BL's area the persistent cells are the registers `0, ..., 7`, the slots `0, ..., 25` and
the arrays `0, ..., 7`; the rest is scratch, and nothing in `BLInv` reads it.

* Registers: `rD = d`, `rM = m`, `rMk = cfg.m` (the kept rows), `rOne = 1`, `rP = p`, `rPF = pF`,
  `rNb = nBlk d = ⌈d/2⌉ + 1`, `rB = B` (BM-INT, `xbmint` with `on = rB`, uses the registers `8, ..., 18` as scratch).
* Slots: `sZ = 0`; `sMode` (`0` off, `1` guard, `2` run); `sFirst` (`1` at the first round of an epoch, else `0`);
  `sN = n`; `s2p = 2^p`, `s2pF = 2^pF`, `s2g = 2^(2 p_B)` (`p_B = gsm_prec B`, the scale of the draws),
  `s2eh = 1/ê` (a power of two); `sNe = N_e`, `sLam = Λ`, `sRint = R_int`; the numerators at the grid `2^{-pF}` of
  `ε'`, `λ'`, `η'`, `ρ'`, `κ_c'`, `ν'`, `R'`, `s'_b`, `W'` (`qn pF x = ⌊x 2^pF⌋`, which is `x 2^pF` exactly since
  PARAM rounds these fields to `2^{-pF}`) and at the grid `2^{-p}` of `A_0`, `B_0`; `sDS`, the common positive
  denominator of the position; in mode `run`, `sDmu` (the positive denominator of `μ'`), `sK`, `sL` (`k'`, `l'` at
  `2^{-p}`).
* Arrays (`asz d = d² + d` cells each; a vector in the cells `0, ..., d - 1`, a matrix row-major, entry `(i, j)` in the
  cell `d i + j`): `aMuS`, `aAS`, the numerators of `μ_S`, `A_S` over `sDS`; `aC`, the frame centre in the form of the
  play leaf (a positive denominator in cell `0`, the numerators in cells `1, ..., d`); in mode `run`, `aMu` (the
  numerators of `μ'` over `sDmu`) and `aA`, `aB`, `ab`, `aG` (`A'`, `B'`, `b'`, `G'` at `2^{-p}`).

The kept rows `α̃_i`, `β̃_i` of P3 are not stored (no array of size `m` fits the layout): the round recomputes row `i`
from the input cells on demand.

**The state on the grid.** Every field of BL's state but `μ'` lies on `2^{-p} ℤ` on every run (R8, R9 round to it,
the epoch start too); `BLInv` carries it (`OnG`), so the cells hold the exact values.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- The numerator of `x` at the grid `2^{-k}`: `⌊x 2^k⌋`. -/
def qn (k : ℕ) (x : ℚ) : ℤ := ⌊x * 2 ^ k⌋

/-- `x` lies on the grid `2^{-k}`: `qn k x = x 2^k`. -/
def OnG (k : ℕ) (x : ℚ) : Prop := ((qn k x : ℤ) : ℚ) = x * 2 ^ k

/-! ## BL's area -/

/-- The register of `d`. -/
abbrev rD : ℕ := 0
/-- The register of `m`, the number of input rows. -/
abbrev rM : ℕ := 1
/-- The register of `cfg.m`, the number of kept rows. -/
abbrev rMk : ℕ := 2
/-- The register holding `1`. -/
abbrev rOne : ℕ := 3
/-- The register of `p`. -/
abbrev rP : ℕ := 4
/-- The register of `pF`. -/
abbrev rPF : ℕ := 5
/-- The register of `nBlk d`. -/
abbrev rNb : ℕ := 6
/-- The register of `B` (`xbmint` uses the next eleven registers as scratch). -/
abbrev rB : ℕ := 7
/-- The registers of BL's area; the routines' blocks start here. -/
abbrev nN0 : ℕ := 48

/-- The slot holding `0`. -/
abbrev sZ : ℕ := 0
/-- The mode: `0` off, `1` guard, `2` run. -/
abbrev sMode : ℕ := 1
/-- `1` at the first round of an epoch, else `0`. -/
abbrev sFirst : ℕ := 2
/-- `n`. -/
abbrev sN : ℕ := 3
/-- `2^p`. -/
abbrev s2p : ℕ := 4
/-- `2^pF`. -/
abbrev s2pF : ℕ := 5
/-- `2^(2 gsm_prec B)`, the scale of the draws. -/
abbrev s2g : ℕ := 6
/-- `N_e`. -/
abbrev sNe : ℕ := 7
/-- `Λ`. -/
abbrev sLam : ℕ := 8
/-- `R_int`. -/
abbrev sRint : ℕ := 9
/-- `1/ê`. -/
abbrev s2eh : ℕ := 10
/-- `ε' 2^pF`. -/
abbrev sEps : ℕ := 11
/-- `λ' 2^pF`. -/
abbrev sLamb : ℕ := 12
/-- `η' 2^pF`. -/
abbrev sEta : ℕ := 13
/-- `ρ' 2^pF`. -/
abbrev sRho : ℕ := 14
/-- `κ_c' 2^pF`. -/
abbrev sKapc : ℕ := 15
/-- `ν' 2^pF`. -/
abbrev sNu : ℕ := 16
/-- `R' 2^pF`. -/
abbrev sR : ℕ := 17
/-- `s'_b 2^pF`. -/
abbrev sSb : ℕ := 18
/-- `W' 2^pF`. -/
abbrev sW : ℕ := 19
/-- `A_0 2^p`. -/
abbrev sA0 : ℕ := 20
/-- `B_0 2^p`. -/
abbrev sB0 : ℕ := 21
/-- The common denominator of the position. -/
abbrev sDS : ℕ := 22
/-- The denominator of `μ'` (mode `run`). -/
abbrev sDmu : ℕ := 23
/-- `k' 2^p` (mode `run`). -/
abbrev sK : ℕ := 24
/-- `l' 2^p` (mode `run`). -/
abbrev sL : ℕ := 25
/-- The persistent slots are those below `nSP`. -/
abbrev nSP : ℕ := 26
/-- The slots of BL's area; the routines' blocks start here. -/
abbrev nS0 : ℕ := 128

/-- The numerators of `μ_S`. -/
abbrev aMuS : ℕ := 0
/-- The numerators of `A_S`. -/
abbrev aAS : ℕ := 1
/-- The frame centre, in the form of the play leaf. -/
abbrev aC : ℕ := 2
/-- The numerators of `μ'` (mode `run`). -/
abbrev aMu : ℕ := 3
/-- `A' 2^p` (mode `run`). -/
abbrev aA : ℕ := 4
/-- `B' 2^p` (mode `run`). -/
abbrev aB : ℕ := 5
/-- `b' 2^p` (mode `run`). -/
abbrev ab : ℕ := 6
/-- `G' 2^p` (mode `run`). -/
abbrev aG : ℕ := 7
/-- The persistent arrays are those below `nAP`. -/
abbrev nAP : ℕ := 8
/-- The arrays of BL's area; the routines' blocks start here. -/
abbrev nA0 : ℕ := 16

/-! ## The representations -/

/-- The position `(μ_S, A_S)`: a positive common denominator in `sDS`, the numerators in `aMuS` and `aAS`. -/
def PosRep (σ : Env d) (μS : Fin d → ℚ) (AS : Matrix (Fin d) (Fin d) ℚ) : Prop :=
  ∃ DS : ℤ, 0 < DS ∧ σ.sc sDS = DS ∧
    (∀ j : Fin d, ∃ x : ℤ, σ.arr aMuS j = x ∧ (x : ℚ) / DS = μS j) ∧
    ∀ i j : Fin d, ∃ x : ℤ, σ.arr aAS (d * i + j) = x ∧ (x : ℚ) / DS = AS i j

/-- A point in the array `a` in the form of the play leaf: a positive denominator in cell `0`, the numerators in
cells `1, ..., d`. -/
def PtRep (σ : Env d) (a : ℕ) (c : Fin d → ℚ) : Prop :=
  ∃ D : ℤ, 0 < D ∧ σ.arr a 0 = D ∧ ∀ j : Fin d, ∃ x : ℤ, σ.arr a (j + 1) = x ∧ (x : ℚ) / D = c j

/-- BL's state in mode `run`: `first` in `sFirst`; `μ'` over the positive denominator `sDmu`; `A'`, `B'`, `b'`, `k'`,
`G'`, `l'` on the grid `2^{-p}`, their numerators in `aA`, `aB`, `ab`, `sK`, `aG`, `sL`. -/
def StRep (σ : Env d) (p : ℕ) (st : St d) : Prop :=
  σ.sc sFirst = (if st.first then 1 else 0) ∧
  (∃ Dm : ℤ, 0 < Dm ∧ σ.sc sDmu = Dm ∧ ∀ j : Fin d, ∃ x : ℤ, σ.arr aMu j = x ∧ (x : ℚ) / Dm = st.mu j) ∧
  (∀ i j : Fin d, σ.arr aA (d * i + j) = qn p (st.A i j) ∧ OnG p (st.A i j)) ∧
  (∀ i j : Fin d, σ.arr aB (d * i + j) = qn p (st.B i j) ∧ OnG p (st.B i j)) ∧
  (∀ j : Fin d, σ.arr ab j = qn p (st.b j) ∧ OnG p (st.b j)) ∧
  (σ.sc sK = qn p st.k ∧ OnG p st.k) ∧
  (∀ j : Fin d, σ.arr aG j = qn p (st.G j) ∧ OnG p (st.G j)) ∧
  (σ.sc sL = qn p st.l ∧ OnG p st.l)

/-- The mode in `sMode`, with the state in mode `run`. -/
def ModeRep (σ : Env d) (p : ℕ) : Mode d → Prop
  | .off => σ.sc sMode = 0
  | .guard => σ.sc sMode = 1
  | .run st => σ.sc sMode = 2 ∧ StRep σ p st

/-- **BL's invariant** (frozen): the environment `σ` holds the configuration `cfg` and the mode `mo` before round `t`,
on the input with `n` rounds and `m` rows, after the `K0` coins of the prologue and the coins of the rounds `< t`;
every persistent cell is an integer of absolute value at most `2^E`. -/
structure BLInv (L : Layout) (n m K0 E : ℕ) (cfg : Cfg d) (mo : Mode d) (t : ℕ) (σ : Env d) : Prop where
  /-- BL's area fits the layout. -/
  lay : nN0 ≤ L.NN ∧ nS0 ≤ L.NS ∧ nA0 ≤ L.NA
  /-- The registers. -/
  regs : σ.nat rD = d ∧ σ.nat rM = m ∧ σ.nat rMk = cfg.m ∧ σ.nat rOne = 1 ∧ σ.nat rP = cfg.par.p ∧
    σ.nat rPF = cfg.par.pF ∧ σ.nat rNb = Sched.nBlk d ∧ σ.nat rB = cfg.par.B
  /-- The integer constants. -/
  consts : σ.sc sZ = 0 ∧ σ.sc sN = n ∧ σ.sc s2p = 2 ^ cfg.par.p ∧ σ.sc s2pF = 2 ^ cfg.par.pF ∧
    σ.sc s2g = 2 ^ (2 * gsm_prec cfg.par.B) ∧ σ.sc s2eh = ((cfg.par.eHat⁻¹ : ℚ) : ℝ) ∧
    σ.sc sNe = cfg.par.Ne ∧ σ.sc sLam = cfg.par.Lam ∧ σ.sc sRint = cfg.par.Rint
  /-- The rational fields of PARAM, as numerators. -/
  par : σ.sc sEps = qn cfg.par.pF cfg.par.eps ∧ σ.sc sLamb = qn cfg.par.pF cfg.par.lam ∧
    σ.sc sEta = qn cfg.par.pF cfg.par.eta ∧ σ.sc sRho = qn cfg.par.pF cfg.par.rho ∧
    σ.sc sKapc = qn cfg.par.pF cfg.par.kapc ∧ σ.sc sNu = qn cfg.par.pF cfg.par.nu ∧
    σ.sc sR = qn cfg.par.pF cfg.par.R ∧ σ.sc sSb = qn cfg.par.pF cfg.par.sb ∧ σ.sc sW = qn cfg.par.pF cfg.par.W ∧
    σ.sc sA0 = qn cfg.par.p cfg.par.A0 ∧ σ.sc sB0 = qn cfg.par.p cfg.par.B0
  /-- The position. -/
  pos : PosRep σ cfg.μS cfg.AS
  /-- The frame centre. -/
  ctr : PtRep σ aC cfg.c
  /-- The mode and the state. -/
  mode : ModeRep σ cfg.par.p mo
  /-- The rounds played. -/
  rounds : σ.rounds = t
  /-- The coins read: the prologue's and those of the rounds `< t` (Bit/CoinSched.lean). -/
  draws : σ.draws = Sched.blkStart d K0 cfg.par.B t 0
  /-- Every persistent cell is an integer at most `2^E` in absolute value. -/
  bnd : (∀ y < nSP, ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ E) ∧
    ∀ a < nAP, ∀ k < asz d, ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E

end AdversarialBco.Bit.Transfer.BLM
