/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOBL
public import AdversarialBco.Unified.XRunsO
public import AdversarialBco.Unified.BLOParam
public import AdversarialBco.Bit.Transfer.XBLSetupBL

@[expose] public section

/-!
# BL-O's setup on the oracle machine: the sub-block contracts and their assembly

The contract `SetupSpecO xinit C k nS nN nA` of ProgOBL.lean split into named sub-blocks, and
`setupSpecO_of`, which assembles it from them. `xinitO` runs, after the machine's setup (`d` in `rD` and in the slot
`0`):

1. **P0** (`P0SpecO`): reads `n`, `δ` and the frame centre `a` from the input cells: `1` in `rOne`, `n` in `sN`,
   `1, 2, 4` in the slots `26, 27, 28`, `k_δ = kDel δ` in the slot `sKd`, the centre `a` in `aC` in the form of the
   play leaf (`PtIn`); BL's other persistent cells stay at `0`, no row (`rM = rMk = 0`). The oracle data `r0`, `R0`
   stay input cells, read where they are used.
2. **PARAM at `k_δ`** (`ParamSpecO`): Procedure PARAM at `N_e = 15 · 2^{17 + k_δ} d³ n⁴` (`parO d n δ`), its values in
   BL's cells as `BLInv` reads them (`ParO`: the registers `rP, rPF, rNb, rB`, the slots `s2p, ..., sB0`).
3. `sZ := 0` (v2.1's `VL.sconst`, through `base`).
4. **TRI-OGD-O** (`TriSpecO`): the position `posO d n orc δ r0 R0 a` on the coins from `draws`, into `sDS`, `aMuS`,
   `aAS` (`PosIn`), reading exactly `LposO` coins and leaving `LposO` in the slot `sLp`.
5. **The coin count** (`CoinsSpecO`): reads the `K0O - LposO` coins that complete the prologue's whole blocks.
6. **The cross check** (`CrossSpecO`): the flag `sBadS := 0` if `crossOK orc c`, else `1`.
7. The epoch start, v2.1's `xepoch` through `base` (`XV.epoch`).
8. **The mode** (`ModeSpecO`): `sMode := 0` if `2^pF < 2 ε'_num` (`ε' > 1/2`), else `1` if the flag is set, else `2`:
   `mode0O`.

Every block after P0 states the cells it may change (`FrameA`): BL's persistent cells are the registers `0, ..., 7`, the
slots `0, ..., 25` and the arrays `0, ..., 7` (`BLInv`, Bit/Transfer/XBLInv.lean); the blocks keep the registers
`0, ..., 7` but their own outputs, the slots below `30` but their own outputs, and the arrays below `8` but their own
outputs. Units and magnitudes are polynomial in `W = wU d n δ r0 R0 a = d + size n + S + 1`; the cross check's also in
the bound `2^s` of what it reads.

`setupSpecO_of`: the six contracts (with room `172, 48, 16` for v2.1's epoch start) give `SetupSpecO` for `xinitO` at
the constants `csO`, `ksO`; `progSetupO_of`: `ProgSetupO` from the six contracts for some commands.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St Par init up rnd)
open AdversarialBco.Bit.RQ (PosQ)
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The cells of the setup -/

/-- The slot of `k_δ`, written by P0, read by PARAM and TRI-OGD-O (v2.1's `sBadS`, the cross check's flag later). -/
abbrev sKd : ℕ := 29

/-- The slot of `LposO`, the coins of the position, written by TRI-OGD-O and read by the coin count. -/
abbrev sLp : ℕ := 126

/-- The slots `lo, ..., hi - 1` hold integers of absolute value at most `2^s`. -/
def SlotBnd (σ : Env d) (lo hi s : ℕ) : Prop := ∀ y, lo ≤ y → y < hi → ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ s

/-- **PARAM's values in BL's cells** for the parameters `P`: the registers from `rP` on, the integer constants from `s2p`
on and the rational fields of `BLInv` (Bit/Transfer/XBLInv.lean). -/
structure ParO (σ : Env d) (P : Par) : Prop where
  regs : σ.nat rP = P.p ∧ σ.nat rPF = P.pF ∧ σ.nat rNb = Bit.Sched.nBlk d ∧ σ.nat rB = P.B
  consts : σ.sc s2p = 2 ^ P.p ∧ σ.sc s2pF = 2 ^ P.pF ∧ σ.sc s2g = 2 ^ (2 * Bit.gsm_prec P.B) ∧
    σ.sc s2eh = ((P.eHat⁻¹ : ℚ) : ℝ) ∧ σ.sc sNe = P.Ne ∧ σ.sc sLam = P.Lam ∧ σ.sc sRint = P.Rint
  par : σ.sc sEps = qn P.pF P.eps ∧ σ.sc sLamb = qn P.pF P.lam ∧ σ.sc sEta = qn P.pF P.eta ∧
    σ.sc sRho = qn P.pF P.rho ∧ σ.sc sKapc = qn P.pF P.kapc ∧ σ.sc sNu = qn P.pF P.nu ∧
    σ.sc sR = qn P.pF P.R ∧ σ.sc sSb = qn P.pF P.sb ∧ σ.sc sW = qn P.pF P.W ∧
    σ.sc sA0 = qn P.p P.A0 ∧ σ.sc sB0 = qn P.p P.B0

/-- What the blocks after PARAM read: `d` in `rD`, `1` in `rOne`, `0` in `sZ`, `n` in `sN`, `1, 2, 4` in the slots
`26, 27, 28`. -/
def BasO (n : ℕ) (σ : Env d) : Prop :=
  σ.nat rD = d ∧ σ.nat rOne = 1 ∧ σ.sc sZ = 0 ∧ σ.sc sN = n ∧ σ.sc 26 = 1 ∧ σ.sc 27 = 2 ∧ σ.sc 28 = 4

/-- **The state after P0.** `d` in `rD` and in the slot `0` (PARAM reads it there), `1` in `rOne`, no row (`rM`,
`rMk` at `0`); `n` in `sN`, `1, 2, 4` in the slots `26, 27, 28`, `k_δ` in `sKd`; the mode slot and `k'`, `l'` at `0`;
the frame centre `a` in `aC` in the form of the play leaf, integers below `2^s`, the cells of `aC` from `d + 1` on and
BL's other persistent arrays at `0`; no coin read, no round. -/
structure P0PostO (n : ℕ) (δ : ℚ) (a : Fin d → ℚ) (s : ℕ) (σ : Env d) : Prop where
  nat : σ.nat rD = d ∧ σ.nat rM = 0 ∧ σ.nat rMk = 0 ∧ σ.nat rOne = 1
  sc : σ.sc 0 = d ∧ σ.sc sMode = 0 ∧ σ.sc sN = n ∧ σ.sc sK = 0 ∧ σ.sc sL = 0 ∧ σ.sc 26 = 1 ∧ σ.sc 27 = 2 ∧
    σ.sc 28 = 4 ∧ σ.sc sKd = kDel δ
  ctr : PtIn σ aC s a
  arr : (∀ k, d + 1 ≤ k → σ.arr aC k = 0) ∧ ∀ b < nAP, b ≠ aC → ∀ k, σ.arr b k = 0
  draws : σ.draws = 0
  rounds : σ.rounds = 0

/-! ## The sub-block contracts -/

/-- **P0**: from the environment after the machine's setup, `xp0 L` ends in `P0PostO` with the centre's integers below
`2^{C (W + 1)^k}`, within `C (W + 1)^k` units. -/
def P0SpecO (xp0 : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xp0 L) (envSetup rD d) (C * (wU d n δ r0 R0 a + 1) ^ k)
      (P0PostO n δ a (C * (wU d n δ r0 R0 a + 1) ^ k))

/-- The cells PARAM may change: the slots `4, ..., 21` (its values), `30, ..., 123` and from `128` on, the registers
from `rP` on, the arrays from `8` on. -/
def SPar (y : ℕ) : Prop := (4 ≤ y ∧ y < 22) ∨ (29 < y ∧ y < 124) ∨ 128 ≤ y

/-- **PARAM at `k_δ`**: from `d` in `rD` and the slot `0`, `1` in `rOne`, `0` in the mode slot, `n` in `sN`, `1, 2, 4`
in the slots `26, 27, 28` and `k_δ` in `sKd`, `xpar L` writes PARAM's values at `parO d n δ` (`ParO`), integers at most
`2^{C (W + 1)^k}`, within `C (W + 1)^k` units; it reads no coin. -/
def ParamSpecO (xpar : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    σ.nat rD = d → σ.nat rOne = 1 → σ.sc 0 = d → σ.sc sMode = 0 → σ.sc sN = n → σ.sc 26 = 1 → σ.sc 27 = 2 →
    σ.sc 28 = 4 → σ.sc sKd = kDel δ →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpar L) σ (C * (wU d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      ParO σ' (parO d n δ) ∧ SlotBnd σ' 4 22 (C * (wU d n δ r0 R0 a + 1) ^ k) ∧ σ'.draws = σ.draws ∧
      FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ σ')

/-- The cells TRI-OGD-O may change: `sDS` and the slots from `30` on; the registers from `8` on; the numerators of the
position (the cells `0, ..., d - 1` of `aMuS`, `0, ..., d² - 1` of `aAS`) and the arrays from `8` on. -/
def ATri (d : ℕ) (b c : ℕ) : Prop := (b = aMuS ∧ c < d) ∨ (b = aAS ∧ c < d * d) ∨ 8 ≤ b

/-- **TRI-OGD-O**: from `BasO` and `k_δ` in `sKd`, `xtri L` writes the position `posO d n orc δ r0 R0 a` on the coins
from `draws` into `sDS`, `aMuS`, `aAS` (`PosIn`, integers below `2^{C (W + 1)^k}`), leaves `LposO` in the slot `sLp`,
and reads exactly `LposO` coins, within `C (W + 1)^k` units. -/
def TriSpecO (xtri : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → BasO n σ → σ.sc sKd = kDel δ →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xtri L) σ (C * (wU d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      PosIn σ' sDS aMuS (C * (wU d n δ r0 R0 a + 1) ^ k)
        (posO d n w.orc δ r0 R0 a fun j => w.cs (σ.draws + j)) ∧
      σ'.sc sLp = LposO d n δ r0 R0 ∧ σ'.draws = σ.draws + LposO d n δ r0 R0 ∧
      FrameA (fun y => y = sDS ∨ 29 < y) (fun j => 8 ≤ j) (ATri d) σ σ')

/-- **The coin count**: from `BasO`, PARAM's values and `LposO` in `sLp`, `xcoins L` reads the `K0O - LposO` coins
that complete the prologue's `P0O` blocks, within `C (W + 1)^k` units. -/
def CoinsSpecO (xcoins : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → BasO n σ → ParO σ (parO d n δ) →
    σ.sc sLp = LposO d n δ r0 R0 →
    C * (wU d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xcoins L) σ (C * (wU d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      σ'.draws = σ.draws + (K0O d n δ r0 R0 - LposO d n δ r0 R0) ∧
      FrameA (fun y => 29 < y) (fun j => 8 ≤ j) (fun b _ => 8 ≤ b) σ σ')

/-- BL-O's configuration at the input, PARAM at `δ` and the position `S`. -/
def cfgS (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (S : PosQ d) : CfgO d := ⟨parO d n δ, n, a, r0, R0, S.1, S.2⟩

/-- **The cross check**: from `BasO`, PARAM's values (integers at most `2^s`), a position `S` in `sDS`, `aMuS`,
`aAS` and the frame centre `a` in `aC` (integers below `2^s`), `xcross L` sets the flag `sBadS` to `0` if CM at the
precision `kC` accepts the `2d` points `μ_S ± A_S e_i/2` (`crossOK`), to `1` otherwise, within `C (W + s + 1)^k`
units; it reads no coin. -/
def CrossSpecO (xcross : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ s : ℕ) (S : PosQ d)
    (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → BasO n σ → ParO σ (parO d n δ) → SlotBnd σ 4 22 s →
    PosIn σ sDS aMuS s S → PtIn σ aC s a →
    C * (wU d n δ r0 R0 a + s + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + s + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xcross L) σ (C * (wU d n δ r0 R0 a + s + 1) ^ k) (fun σ' =>
      σ'.sc sBadS = ((if crossOK w.orc (cfgS n δ r0 R0 a S) then 0 else 1 : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sBadS ∨ 29 < y) (fun j => 8 ≤ j) (fun b _ => 8 ≤ b) σ σ')

/-- **The mode**: from `0` in `sZ` and in the mode slot, the flag `fl` in `sBadS`, `PF = 2^pF` in `s2pF` and
`ep = ε' 2^pF` in `sEps`, `xmode L` sets the mode slot to `0` if `PF < 2 ep`, else to `1` if `fl > 0`, else to `2`,
within `C` units, changing only the mode slot and the slot `124`. -/
def ModeSpecO (xmode : Layout → XCmdO) (C nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (σ : Env d) (fl PF ep : ℤ), LayOK L d ℓa → RoomO L nS nN nA →
    σ.sc sZ = 0 → σ.sc sBadS = fl → σ.sc s2pF = PF → σ.sc sEps = ep → σ.sc sMode = 0 → |fl| < 2 ^ ℓ →
    |PF| < 2 ^ ℓ → |2 * ep| < 2 ^ ℓ → 2 < ℓ →
    XRunsBO L XO ℓa ℓ (xmode L) σ C (fun σ' =>
      σ'.sc sMode = ((if PF < 2 * ep then 0 else if 0 < fl then 1 else 2 : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sMode ∨ y = 124) (fun _ => False) (fun _ _ => False) σ σ')

/-! ## The program of the setup -/

/-- **BL-O's setup** after the machine's: P0, PARAM at `k_δ`, `sZ := 0`, TRI-OGD-O, the coin count, the cross check,
v2.1's epoch start, the mode. -/
def xinitO (xp0 xpar xtri xcoins xcross xmode : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (xp0 L) (.seq (xpar L) (.seq (.base (toX (VL.sconst L sZ 0))) (.seq (xtri L) (.seq (xcoins L)
    (.seq (xcross L) (.seq (.base (xepoch L)) (xmode L)))))))

/-! ## Facts on the cells -/

/-- `omega` after unfolding the names of BL's cells and of the setup's frames. -/
macro "suomega" : tactic => `(tactic| ((try simp only [SPar, ATri, SE, NE, sKd, sLp, rD, rM, rMk, rOne, rP, rPF,
  rNb, rB, sZ, sMode, sFirst, sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR,
  sSb, sW, sA0, sB0, sDS, sDmu, sK, sL, sBadS, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, ne_eq, not_or, not_and,
  not_lt, not_le]) <;> omega))

theorem ParO.congr {σ σ' : Env d} {P : Par} (h : ParO σ P) (hn : ∀ j, rP ≤ j → j < 8 → σ'.nat j = σ.nat j)
    (hs : ∀ y, 4 ≤ y → y < 22 → σ'.sc y = σ.sc y) : ParO σ' P := by
  obtain ⟨⟨r1, r2, r3, r4⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩⟩ := h
  exact ⟨⟨(hn rP le_rfl (by decide)).trans r1, (hn rPF (by decide) (by decide)).trans r2,
    (hn rNb (by decide) (by decide)).trans r3, (hn rB (by decide) (by decide)).trans r4⟩,
    ⟨(hs s2p le_rfl (by decide)).trans c1, (hs s2pF (by decide) (by decide)).trans c2,
      (hs s2g (by decide) (by decide)).trans c3, (hs s2eh (by decide) (by decide)).trans c4,
      (hs sNe (by decide) (by decide)).trans c5, (hs sLam (by decide) (by decide)).trans c6,
      (hs sRint (by decide) (by decide)).trans c7⟩,
    ⟨(hs sEps (by decide) (by decide)).trans p1, (hs sLamb (by decide) (by decide)).trans p2,
      (hs sEta (by decide) (by decide)).trans p3, (hs sRho (by decide) (by decide)).trans p4,
      (hs sKapc (by decide) (by decide)).trans p5, (hs sNu (by decide) (by decide)).trans p6,
      (hs sR (by decide) (by decide)).trans p7, (hs sSb (by decide) (by decide)).trans p8,
      (hs sW (by decide) (by decide)).trans p9, (hs sA0 (by decide) (by decide)).trans p10,
      (hs sB0 (by decide) (by decide)).trans p11⟩⟩

theorem ParO.frame {σ σ' : Env d} {P : Par} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} (h : ParO σ P)
    (F : FrameA S N Ar σ σ') (hS : ∀ y, 4 ≤ y → y < 22 → ¬ S y) (hN : ∀ j, rP ≤ j → j < 8 → ¬ N j) : ParO σ' P :=
  h.congr (fun j h1 h2 => F.1 j (hN j h1 h2)) fun y h1 h2 => F.2.1 y (hS y h1 h2)

theorem SlotBnd.congr {σ σ' : Env d} {lo hi s : ℕ} (h : SlotBnd σ lo hi s)
    (hs : ∀ y, lo ≤ y → y < hi → σ'.sc y = σ.sc y) : SlotBnd σ' lo hi s := fun y h1 h2 => by
  rw [hs y h1 h2]; exact h y h1 h2

theorem SlotBnd.mono {σ : Env d} {lo hi s s' : ℕ} (h : SlotBnd σ lo hi s) (hs : s ≤ s') : SlotBnd σ lo hi s' :=
  fun y h1 h2 => (h y h1 h2).imp fun _ hz => ⟨hz.1, hz.2.trans (pow_le_pow_right₀ (by norm_num) hs)⟩

theorem BasO.congr {σ σ' : Env d} {n : ℕ} (h : BasO n σ) (hn : ∀ j, j < 4 → σ'.nat j = σ.nat j)
    (hs : ∀ y, (y = 0 ∨ y = 3 ∨ (26 ≤ y ∧ y < 29)) → σ'.sc y = σ.sc y) : BasO n σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hn rD (by decide)).trans h1, (hn rOne (by decide)).trans h2, (hs sZ (by decide)).trans h3,
    (hs sN (by decide)).trans h4, (hs 26 (by decide)).trans h5, (hs 27 (by decide)).trans h6,
    (hs 28 (by decide)).trans h7⟩

theorem posIn_congr {σ σ' : Env d} {o a s : ℕ} {S : PosQ d} (h : PosIn σ o a s S) (ho : σ'.sc o = σ.sc o)
    (h0 : ∀ k, σ'.arr a k = σ.arr a k) (h1 : ∀ k, σ'.arr (a + 1) k = σ.arr (a + 1) k) : PosIn σ' o a s S := by
  obtain ⟨D, hD0, hDs, hDo, hm, hA⟩ := h
  exact ⟨D, hD0, hDs, ho.trans hDo, fun j => (hm j).imp fun x hx => ⟨hx.1, (h0 j).trans hx.2.1, hx.2.2⟩,
    fun i j => (hA i j).imp fun x hx => ⟨hx.1, (h1 _).trans hx.2.1, hx.2.2⟩⟩

theorem posIn_mono {σ : Env d} {o a s s' : ℕ} {S : PosQ d} (h : PosIn σ o a s S) (hs : s ≤ s') :
    PosIn σ o a s' S := by
  have h2 : (2 : ℤ) ^ s ≤ 2 ^ s' := pow_le_pow_right₀ (by norm_num) hs
  obtain ⟨D, hD0, hDs, hDo, hm, hA⟩ := h
  exact ⟨D, hD0, hDs.trans_le h2, hDo, fun j => (hm j).imp fun x hx => ⟨hx.1.trans_le h2, hx.2⟩,
    fun i j => (hA i j).imp fun x hx => ⟨hx.1.trans_le h2, hx.2⟩⟩

theorem ptIn_congr {σ σ' : Env d} {a s : ℕ} {c : Fin d → ℚ} (h : PtIn σ a s c)
    (h0 : ∀ k, σ'.arr a k = σ.arr a k) : PtIn σ' a s c := by
  obtain ⟨D, hD0, hDs, hDa, hx⟩ := h
  exact ⟨D, hD0, hDs, (h0 0).trans hDa, fun j => (hx j).imp fun x hx => ⟨hx.1, (h0 _).trans hx.2.1, hx.2.2⟩⟩

theorem ptIn_mono {σ : Env d} {a s s' : ℕ} {c : Fin d → ℚ} (h : PtIn σ a s c) (hs : s ≤ s') : PtIn σ a s' c := by
  have h2 : (2 : ℤ) ^ s ≤ 2 ^ s' := pow_le_pow_right₀ (by norm_num) hs
  obtain ⟨D, hD0, hDs, hDa, hx⟩ := h
  exact ⟨D, hD0, hDs.trans_le h2, hDa, fun j => (hx j).imp fun x hx => ⟨hx.1.trans_le h2, hx.2⟩⟩

/-- The position that TRI-OGD-O leaves (`PosIn`) is bounded (`PosBnd`). -/
theorem posBnd_of_posInO {σ : Env d} {o a s : ℕ} {c : CfgO d} (h : PosIn σ o a s (c.μS, c.AS)) :
    PosBnd (cfgV c) s := by
  obtain ⟨D, hD0, hDs, -, hmu, hA⟩ := h
  exact ⟨D, hD0, hDs.le, fun j => (hmu j).imp fun x hx => ⟨hx.1.le, hx.2.2⟩,
    fun i j => (hA i j).imp fun x hx => ⟨hx.1.le, hx.2.2⟩⟩

/-- An integer slot read twice. -/
theorem int_of_sc {σ : Env d} {y : ℕ} {z w : ℤ} (h1 : σ.sc y = z) (h2 : σ.sc y = w) : z = w := by
  exact_mod_cast h1.symm.trans h2

/-! ## PARAM's grid facts -/

/-- `1/2 < ε'` on the grid `2^{-pF}`: PARAM rounds `ε'` up. -/
theorem parN_half_iff (ne d n : ℕ) :
    1 / 2 < (parN ne d n).eps ↔ (2 : ℤ) ^ (parN ne d n).pF < 2 * qn (parN ne d n).pF (parN ne d n).eps :=
  half_lt_up_iff _ _

theorem parN_onG_A0 (ne d n : ℕ) : OnG (parN ne d n).p (parN ne d n).A0 := onG_rnd_s _ _

theorem parN_onG_B0 (ne d n : ℕ) : OnG (parN ne d n).p (parN ne d n).B0 := onG_rnd_s _ _

/-! ## The end of the setup is BL-O's invariant -/

set_option maxHeartbeats 2000000 in
/-- **The end of the setup is `BLOInv`** at round `0` with the first mode `mode0O`: from the cells the blocks leave. -/
theorem bloInv_mk {L : Layout} {n E K0 s : ℕ} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {σ : Env d}
    (hlay : nN0 ≤ L.NN ∧ nS0 ≤ L.NS ∧ nA0 ≤ L.NA) (hsE : s ≤ E) (hE1 : 1 ≤ E) (hnE : (n : ℤ) ≤ 2 ^ E)
    (hhalf : 1 / 2 < c.par.eps ↔ (2 : ℤ) ^ c.par.pF < 2 * qn c.par.pF c.par.eps)
    (hOA : OnG c.par.p c.par.A0) (hOB : OnG c.par.p c.par.B0)
    (hrD : σ.nat rD = d) (hrM : σ.nat rM = 0) (hrMk : σ.nat rMk = 0) (hrOne : σ.nat rOne = 1)
    (hP : ParO σ c.par) (hPb : SlotBnd σ 4 22 s)
    (hsZ : σ.sc sZ = 0) (hsN : σ.sc sN = n) (hsF : σ.sc sFirst = 1) (hsDmu : σ.sc sDmu = 1) (hsK : σ.sc sK = 0)
    (hsL : σ.sc sL = 0)
    (hsMode : σ.sc sMode = ((if (2 : ℤ) ^ c.par.pF < 2 * qn c.par.pF c.par.eps then 0
      else if 0 < (if crossOK orc c then 0 else 1 : ℤ) then 1 else 2 : ℤ) : ℝ))
    (hpos : PosIn σ sDS aMuS s (c.μS, c.AS)) (hmu0 : ∀ k, d ≤ k → σ.arr aMuS k = 0)
    (hAS0 : ∀ k, d * d ≤ k → σ.arr aAS k = 0) (hctr : PtIn σ aC s c.a) (hc0 : ∀ k, d + 1 ≤ k → σ.arr aC k = 0)
    (haMu : ∀ k, σ.arr aMu k = 0) (hab : ∀ k, σ.arr ab k = 0) (haG : ∀ k, σ.arr aG k = 0)
    (haA : ∀ k, σ.arr aA k = if ∃ j < d, k = 0 + (d + 1) * j then ((qn c.par.p c.par.A0 : ℤ) : ℝ) else 0)
    (haB : ∀ k, σ.arr aB k = if ∃ j < d, k = 0 + (d + 1) * j then ((qn c.par.p c.par.B0 : ℤ) : ℝ) else 0)
    (hr : σ.rounds = 0) (hdr : σ.draws = K0) :
    BLOInv L n K0 E c (mode0O orc c) 0 σ := by
  have hsE' : (2 : ℤ) ^ s ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hsE
  have hE2 : (2 : ℤ) ≤ 2 ^ E := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
    simpa using this
  obtain ⟨D, xm, xa, hD0, hDs, hsc, hxm, hxa, hS1, hS2⟩ :=
    posIn_fun (σ.sc sDS) (σ.arr aMuS) (σ.arr (aMuS + 1)) s _ hpos
  obtain ⟨xc, hxc, hc0', hc⟩ := ptIn_fun (σ.arr aC) s _ hctr
  obtain ⟨zA, hzA, bA⟩ := hPb sA0 (by decide) (by decide)
  obtain ⟨zB, hzB, bB⟩ := hPb sB0 (by decide) (by decide)
  have eA : zA = qn c.par.p c.par.A0 := int_of_sc hzA hP.par.2.2.2.2.2.2.2.2.2.1
  have eB : zB = qn c.par.p c.par.B0 := int_of_sc hzB hP.par.2.2.2.2.2.2.2.2.2.2
  subst eA eB
  refine ⟨hlay, ⟨hrD, hrM, hrMk, hrOne, hP.regs⟩, ⟨hsZ, hsN, hP.consts⟩, hP.par, ?_, ?_, ?_, hr, ?_, ?_, ?_⟩
  -- the position
  · exact ⟨D, hD0, hsc, fun j => ⟨xm j, (hxm j j.2).1, hS1 j⟩, fun i j => ⟨xa (d * i + j), (hxa _ (by
      have := i.2; have := j.2; nlinarith)).1, hS2 i j⟩⟩
  -- the frame centre
  · exact ⟨xc 0, hc0', (hxc 0 (by omega)).1, fun j => ⟨xc (j + 1), (hxc _ (by omega)).1, hc j⟩⟩
  -- the mode
  · unfold mode0O
    split_ifs with h1 h2
    · show σ.sc sMode = 0
      rw [hsMode, if_pos (hhalf.1 h1)]; simp
    · refine ⟨by rw [hsMode, if_neg (fun h => h1 (hhalf.2 h)), if_pos h2]; simp, ?_⟩
      obtain ⟨z1, z2⟩ := onG_zero c.par.p
      refine ⟨by rw [hsF]; simp [init], ⟨1, one_pos, by rw [hsDmu]; simp, fun j => ⟨0, by rw [haMu]; simp,
        by simp [init]⟩⟩, fun i j => ?_, fun i j => ?_, fun j => ?_, ?_, fun j => ?_, ?_⟩
      · show σ.arr aA (d * i + j) = qn c.par.p ((c.par.A0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
        refine ⟨?_, onG_smul_one _ _ hOA i j⟩
        rw [qn_smul_one, haA]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos ((diag_iff i j).2 hij)]
        · rw [if_neg hij, if_neg (fun h => hij ((diag_iff i j).1 h))]; simp
      · show σ.arr aB (d * i + j) = qn c.par.p ((c.par.B0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
        refine ⟨?_, onG_smul_one _ _ hOB i j⟩
        rw [qn_smul_one, haB]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos ((diag_iff i j).2 hij)]
        · rw [if_neg hij, if_neg (fun h => hij ((diag_iff i j).1 h))]; simp
      · show σ.arr ab j = qn c.par.p ((0 : Fin d → ℚ) j) ∧ OnG c.par.p ((0 : Fin d → ℚ) j)
        rw [Pi.zero_apply, z2, hab]; exact ⟨by simp, z1⟩
      · show σ.sc sK = qn c.par.p 0 ∧ OnG c.par.p 0
        rw [z2, hsK]; exact ⟨by simp, z1⟩
      · show σ.arr aG j = qn c.par.p ((0 : Fin d → ℚ) j) ∧ OnG c.par.p ((0 : Fin d → ℚ) j)
        rw [Pi.zero_apply, z2, haG]; exact ⟨by simp, z1⟩
      · show σ.sc sL = qn c.par.p 0 ∧ OnG c.par.p 0
        rw [z2, hsL]; exact ⟨by simp, z1⟩
    · show σ.sc sMode = 1
      rw [hsMode, if_neg (fun h => h1 (hhalf.2 h)), if_neg h2]; simp
  -- the coins
  · rw [hdr]; simp [Bit.Sched.blkStart]
  -- the slots
  · intro y hy
    simp only [nSP] at hy
    rcases (show y < 4 ∨ (4 ≤ y ∧ y < 22) ∨ 22 ≤ y by omega) with h | h | h
    · interval_cases y
      · exact ⟨0, hsZ.trans (by simp), by simp⟩
      · refine ⟨_, hsMode, ?_⟩
        split_ifs <;> simp [hE2] <;> linarith
      · exact ⟨1, hsF.trans (by simp), by simp; linarith⟩
      · exact ⟨n, hsN.trans (by simp), by rw [abs_of_nonneg (by positivity)]; exact hnE⟩
    · exact (hPb y h.1 h.2).imp fun z hz => ⟨hz.1, hz.2.trans hsE'⟩
    · interval_cases y
      · exact ⟨D, hsc, by rw [abs_of_pos hD0]; exact hDs.le.trans hsE'⟩
      · exact ⟨1, hsDmu.trans (by simp), by simp; linarith⟩
      · exact ⟨0, hsK.trans (by simp), by simp⟩
      · exact ⟨0, hsL.trans (by simp), by simp⟩
  -- the arrays
  · intro a ha k hk
    simp only [nAP] at ha
    interval_cases a
    · by_cases h : k < d
      · exact ⟨xm k, (hxm k h).1, (hxm k h).2.le.trans hsE'⟩
      · exact ⟨0, by rw [hmu0 k (by omega)]; simp, by simp⟩
    · by_cases h : k < d * d
      · exact ⟨xa k, (hxa k h).1, (hxa k h).2.le.trans hsE'⟩
      · exact ⟨0, by rw [hAS0 k (by omega)]; simp, by simp⟩
    · by_cases h : k < d + 1
      · exact ⟨xc k, (hxc k h).1, (hxc k h).2.le.trans hsE'⟩
      · exact ⟨0, by rw [hc0 k (by omega)]; simp, by simp⟩
    · exact ⟨0, (haMu k).trans (by simp), by simp⟩
    · rw [haA]
      split_ifs
      · exact ⟨_, rfl, bA.trans hsE'⟩
      · exact ⟨0, by simp, by simp⟩
    · rw [haB]
      split_ifs
      · exact ⟨_, rfl, bB.trans hsE'⟩
      · exact ⟨0, by simp, by simp⟩
    · exact ⟨0, (hab k).trans (by simp), by simp⟩
    · exact ⟨0, (haG k).trans (by simp), by simp⟩

/-! ## The constants of the setup -/

/-- The constant of the setup from those of the blocks. -/
def csO (C0 Cp Ct Cc Cx kx Cm : ℕ) : ℕ := C0 + Cp + Ct + Cc + Cx * (1 + C0 + Cp + Ct) ^ kx + Cm + 60

/-- The exponent of the setup from those of the blocks. -/
def ksO (k0 kp kt kc kx : ℕ) : ℕ := k0 + kp + kt + kc + (k0 + kp + kt + 1) * kx + 1

/-- Every block's units and magnitudes, and their sum with `e ≤ 25 (W + 1)` units, are at most
`csO (W + 1)^{ksO}` (with room `2`). -/
theorem setupO_bounds (W C0 k0 Cp kp Ct kt Cc kc Cx kx Cm e : ℕ) (he : e ≤ 25 * (W + 1)) :
    C0 * (W + 1) ^ k0 + 2 ≤ csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    Cp * (W + 1) ^ kp + 2 ≤ csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    Ct * (W + 1) ^ kt + 2 ≤ csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    Cc * (W + 1) ^ kc + 2 ≤ csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    Cx * (W + (C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + Ct * (W + 1) ^ kt)) + 1) ^ kx + 2 ≤
      csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + Ct * (W + 1) ^ kt) + 2 ≤
      csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    W + 2 ≤ csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx ∧
    C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + (1 + (Ct * (W + 1) ^ kt + (Cc * (W + 1) ^ kc +
      (Cx * (W + (C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + Ct * (W + 1) ^ kt)) + 1) ^ kx + (e + Cm)))))) ≤
      csO C0 Cp Ct Cc Cx kx Cm * (W + 1) ^ ksO k0 kp kt kc kx := by
  have hX : 1 ≤ W + 1 := by omega
  have pw : ∀ {i j : ℕ}, i ≤ j → (W + 1) ^ i ≤ (W + 1) ^ j := fun h => Nat.pow_le_pow_right hX h
  set Y := (W + 1) ^ ksO k0 kp kt kc kx with hY
  have hY1 : W + 1 ≤ Y := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ Y := pw (by unfold ksO; omega)
  have y0 : C0 * (W + 1) ^ k0 ≤ C0 * Y := Nat.mul_le_mul_left _ (pw (by unfold ksO; omega))
  have yp : Cp * (W + 1) ^ kp ≤ Cp * Y := Nat.mul_le_mul_left _ (pw (by unfold ksO; omega))
  have yt : Ct * (W + 1) ^ kt ≤ Ct * Y := Nat.mul_le_mul_left _ (pw (by unfold ksO; omega))
  have yc : Cc * (W + 1) ^ kc ≤ Cc * Y := Nat.mul_le_mul_left _ (pw (by unfold ksO; omega))
  -- the cross check's work term
  have hm1 : W + (C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + Ct * (W + 1) ^ kt)) + 1 ≤
      (1 + C0 + Cp + Ct) * (W + 1) ^ (k0 + kp + kt + 1) := by
    have a1 : W + 1 ≤ (W + 1) ^ (k0 + kp + kt + 1) :=
      (pow_one (W + 1)).symm.le.trans (pw (by omega))
    have a0 := Nat.mul_le_mul_left C0 (pw (i := k0) (j := k0 + kp + kt + 1) (by omega))
    have a2 := Nat.mul_le_mul_left Cp (pw (i := kp) (j := k0 + kp + kt + 1) (by omega))
    have a3 := Nat.mul_le_mul_left Ct (pw (i := kt) (j := k0 + kp + kt + 1) (by omega))
    have e : (1 + C0 + Cp + Ct) * (W + 1) ^ (k0 + kp + kt + 1) = (W + 1) ^ (k0 + kp + kt + 1) +
        C0 * (W + 1) ^ (k0 + kp + kt + 1) + Cp * (W + 1) ^ (k0 + kp + kt + 1) +
        Ct * (W + 1) ^ (k0 + kp + kt + 1) := by ring
    rw [e]
    omega
  have yx : Cx * (W + (C0 * (W + 1) ^ k0 + (Cp * (W + 1) ^ kp + Ct * (W + 1) ^ kt)) + 1) ^ kx ≤
      Cx * (1 + C0 + Cp + Ct) ^ kx * Y := by
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hm1 kx).trans ?_)
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul_left _ (pw (by unfold ksO; nlinarith))
  have hcs : csO C0 Cp Ct Cc Cx kx Cm * Y =
      C0 * Y + Cp * Y + Ct * Y + Cc * Y + Cx * (1 + C0 + Cp + Ct) ^ kx * Y + Cm * Y + 60 * Y := by
    unfold csO; ring
  have hCm : Cm ≤ Cm * Y := Nat.le_mul_of_pos_right _ (by omega)
  rw [hcs]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The assembly -/

set_option maxHeartbeats 8000000 in
/-- **The setup contract from the sub-block contracts.** With room `172` slots, `48` registers and `16` arrays (v2.1's
epoch start), the contracts of P0, PARAM at `k_δ`, TRI-OGD-O, the coin count, the cross check and the mode give
`SetupSpecO` for `xinitO` at the constants `csO`, `ksO`. -/
theorem setupSpecO_of {xp0 xpar xtri xcoins xcross xmode : Layout → XCmdO}
    {C0 k0 Cp kp Ct kt Cc kc Cx kx Cm nS nN nA : ℕ}
    (h0 : P0SpecO xp0 C0 k0 nS nN nA) (hp : ParamSpecO xpar Cp kp nS nN nA) (ht : TriSpecO xtri Ct kt nS nN nA)
    (hc : CoinsSpecO xcoins Cc kc nS nN nA) (hx : CrossSpecO xcross Cx kx nS nN nA)
    (hm : ModeSpecO xmode Cm nS nN nA) (hNS : 172 ≤ nS) (hNN : 48 ≤ nN) (hNA : 16 ≤ nA) :
    SetupSpecO (xinitO xp0 xpar xtri xcoins xcross xmode) (csO C0 Cp Ct Cc Cx kx Cm) (ksO k0 kp kt kc kx)
      nS nN nA := by
  intro d L w n δ r0 R0 a E ℓa ℓ hI hL hR hE hℓ hℓa
  obtain ⟨hRS, hRN, hRA⟩ := id hR
  have hd := hI.hd
  have hep : epochUnits d ≤ 25 * (wU d n δ r0 R0 a + 1) := by unfold epochUnits wU; omega
  obtain ⟨b0, bp, bt, bc, bx, bs, bW, bK⟩ :=
    setupO_bounds (wU d n δ r0 R0 a) C0 k0 Cp kp Ct kt Cc kc Cx kx Cm (epochUnits d) hep
  have hYE : (wU d n δ r0 R0 a + 1) ^ ksO k0 kp kt kc kx ≤ (wU d n δ r0 R0 a + E + 1) ^ ksO k0 kp kt kc kx :=
    Nat.pow_le_pow_left (by omega) _
  have hYE' := Nat.mul_le_mul_left (csO C0 Cp Ct Cc Cx kx Cm) hYE
  have hns : n.size ≤ wU d n δ r0 R0 a ∧ 1 ≤ wU d n δ r0 R0 a := by unfold wU; omega
  have hnE : (n : ℤ) ≤ 2 ^ E := by
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 2 ^ n.size ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast (h1.trans_le h2).le
  have hℓ2 : 2 < ℓ := by omega
  refine XVO.mono (K := C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp + (1 +
    (Ct * (wU d n δ r0 R0 a + 1) ^ kt + (Cc * (wU d n δ r0 R0 a + 1) ^ kc + (Cx * (wU d n δ r0 R0 a +
      (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp + Ct * (wU d n δ r0 R0 a + 1) ^ kt)) +
        1) ^ kx + (epochUnits d + Cm)))))))
    ?_ (by omega) fun _ h => h
  unfold xinitO
  -- P0
  refine XVO.seq (h0 d L w n δ r0 R0 a ℓa ℓ hI hL hR (by omega) (by omega)) fun σ1 h1 => ?_
  obtain ⟨⟨n1D, n1M, n1Mk, n1One⟩, ⟨c10, c1M, c1N, c1K, c1L, c126, c127, c128, c1Kd⟩, hctr1, ⟨ha1C, ha1⟩, hd1,
    hr1⟩ := h1
  -- PARAM at `k_δ`
  refine XVO.seq (hp d L w n δ r0 R0 a ℓa ℓ σ1 hI hL hR n1D n1One c10 c1M c1N c126 c127 c128 c1Kd (by omega)
    (by omega)) fun σ2 ⟨hP2, hB2, d2, F2⟩ => ?_
  -- `sZ := 0`
  refine XVO.seq (XVO.ofX (XV.sconst hL (x := sZ) (by suomega) 0 rfl (by simp))) fun σ3 e3 => ?_
  subst e3
  have n3 : ∀ j, j < rP → (σ2.setSc sZ ((0 : ℚ) : ℝ)).nat j = σ1.nat j := fun j hj => by
    rw [Env.setSc_nat]; exact F2.1 j (by suomega)
  have s3 : ∀ y, y ≠ sZ → ¬ SPar y → (σ2.setSc sZ ((0 : ℚ) : ℝ)).sc y = σ1.sc y := fun y h h' => by
    rw [Env.setSc_sc, if_neg h]; exact F2.2.1 y h'
  have a3 : ∀ b k, b < 8 → (σ2.setSc sZ ((0 : ℚ) : ℝ)).arr b k = σ1.arr b k := fun b k hb => by
    rw [Env.setSc_arr]; exact F2.2.2.1 b k (by suomega)
  have z3 : (σ2.setSc sZ ((0 : ℚ) : ℝ)).sc sZ = 0 := by simp
  have P3 : ParO (σ2.setSc sZ ((0 : ℚ) : ℝ)) (parO d n δ) :=
    hP2.congr (fun j _ _ => by rw [Env.setSc_nat]) fun y h1 _ => by rw [Env.setSc_sc, if_neg (by suomega)]
  have B3 : SlotBnd (σ2.setSc sZ ((0 : ℚ) : ℝ)) 4 22 (Cp * (wU d n δ r0 R0 a + 1) ^ kp) :=
    hB2.congr fun y h1 _ => by rw [Env.setSc_sc, if_neg (by suomega)]
  have bas3 : BasO n (σ2.setSc sZ ((0 : ℚ) : ℝ)) :=
    ⟨(n3 rD (by decide)).trans n1D, (n3 rOne (by decide)).trans n1One, z3,
      (s3 sN (by decide) (by suomega)).trans c1N, (s3 26 (by decide) (by suomega)).trans c126,
      (s3 27 (by decide) (by suomega)).trans c127, (s3 28 (by decide) (by suomega)).trans c128⟩
  have kd3 : (σ2.setSc sZ ((0 : ℚ) : ℝ)).sc sKd = kDel δ := (s3 sKd (by decide) (by suomega)).trans c1Kd
  have dr3 : (σ2.setSc sZ ((0 : ℚ) : ℝ)).draws = 0 := by rw [Env.setSc_draws, d2, hd1]
  -- TRI-OGD-O
  refine XVO.seq (ht d L w n δ r0 R0 a ℓa ℓ _ hI hL hR bas3 kd3 (by omega) (by omega))
    fun σ4 ⟨hPos4, hLp4, d4, F4⟩ => ?_
  have eS : (posO d n w.orc δ r0 R0 a fun j => w.cs ((σ2.setSc sZ ((0 : ℚ) : ℝ)).draws + j)) =
      ((cfgW d n δ r0 R0 a w).μS, (cfgW d n δ r0 R0 a w).AS) := by
    rw [show (fun j => w.cs ((σ2.setSc sZ ((0 : ℚ) : ℝ)).draws + j)) = w.cs from
      funext fun j => by rw [dr3, zero_add]]
    rfl
  rw [eS] at hPos4
  have bas4 : BasO n σ4 := bas3.congr (fun j hj => F4.1 j (by suomega)) fun y hy => F4.2.1 y (by suomega)
  have P4 : ParO σ4 (parO d n δ) := P3.frame F4 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  -- the coin count
  refine XVO.seq (hc d L w n δ r0 R0 a ℓa ℓ σ4 hI hL hR bas4 P4 hLp4 (by omega) (by omega))
    fun σ5 ⟨d5, F5⟩ => ?_
  have bas5 : BasO n σ5 := bas4.congr (fun j hj => F5.1 j (by suomega)) fun y hy => F5.2.1 y (by suomega)
  have P5 : ParO σ5 (parO d n δ) := P4.frame F5 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  have B5 : SlotBnd σ5 4 22 (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) :=
    (B3.congr fun y h1 h2 => (F5.2.1 y (by suomega)).trans (F4.2.1 y (by suomega))).mono (by omega)
  have Pos5 : PosIn σ5 sDS aMuS (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) ((cfgW d n δ r0 R0 a w).μS, (cfgW d n δ r0 R0 a w).AS) :=
    (posIn_congr hPos4 (F5.2.1 _ (by suomega)) (fun k => F5.2.2.1 _ k (by suomega))
      fun k => F5.2.2.1 _ k (by suomega)) |> (posIn_mono · (by omega))
  have Ctr5 : PtIn σ5 aC (C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) a :=
    ptIn_mono (ptIn_congr hctr1 fun k => by
      rw [F5.2.2.1 aC k (by suomega), F4.2.2.1 aC k (by suomega), a3 aC k (by decide)]) (by omega)
  -- the cross check
  refine XVO.seq (hx d L w n δ r0 R0 a ℓa ℓ _ _ σ5 hI hL hR bas5 P5 B5 Pos5 Ctr5 (by omega) (by omega))
    fun σ6 ⟨hfl6, d6, F6⟩ => ?_
  have bas6 : BasO n σ6 := bas5.congr (fun j hj => F6.1 j (by suomega)) fun y hy => F6.2.1 y (by suomega)
  have P6 : ParO σ6 (parO d n δ) := P5.frame F6 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  have B6 : SlotBnd σ6 4 22 (Cp * (wU d n δ r0 R0 a + 1) ^ kp) :=
    B3.congr fun y h1 h2 => ((F6.2.1 y (by suomega)).trans (F5.2.1 y (by suomega))).trans (F4.2.1 y (by suomega))
  obtain ⟨zA, hzA, bA⟩ := B6 sA0 (by decide) (by decide)
  obtain ⟨zB, hzB, bB⟩ := B6 sB0 (by decide) (by decide)
  have eA : zA = qn (parO d n δ).p (parO d n δ).A0 := int_of_sc hzA P6.par.2.2.2.2.2.2.2.2.2.1
  have eB : zB = qn (parO d n δ).p (parO d n δ).B0 := int_of_sc hzB P6.par.2.2.2.2.2.2.2.2.2.2
  subst eA eB
  -- the epoch start
  refine XVO.seq (XVO.ofX (XV.epoch (E := Cp * (wU d n δ r0 R0 a + 1) ^ kp) hL (by omega) (by omega) (by omega)
    bas6.1 bas6.2.1 bas6.2.2.1 hzA hzB bA bB (by omega))) fun σ7 ⟨hF7, hDm7, hA7, hB7, d7, F7⟩ => ?_
  have P7 : ParO σ7 (parO d n δ) := P6.frame F7 (fun y h1 h2 => by suomega) fun j h1 h2 => by suomega
  have B7 : SlotBnd σ7 4 22 (Cp * (wU d n δ r0 R0 a + 1) ^ kp) := B6.congr fun y h1 h2 => F7.2.1 y (by suomega)
  -- the mode
  obtain ⟨zP, hzP, bP⟩ := B7 s2pF (by decide) (by decide)
  obtain ⟨zE, hzE, bE⟩ := B7 sEps (by decide) (by decide)
  have ePF : zP = 2 ^ (parO d n δ).pF := int_of_sc hzP (by rw [P7.consts.2.1]; push_cast; rfl)
  have eEp : zE = qn (parO d n δ).pF (parO d n δ).eps := int_of_sc hzE P7.par.1
  subst ePF eEp
  have hz7 : σ7.sc sZ = 0 := (F7.2.1 sZ (by suomega)).trans bas6.2.2.1
  have hfl7 : σ7.sc sBadS = ((if crossOK w.orc (cfgS n δ r0 R0 a
      ((cfgW d n δ r0 R0 a w).μS, (cfgW d n δ r0 R0 a w).AS)) then 0 else 1 : ℤ) : ℝ) :=
    (F7.2.1 sBadS (by suomega)).trans hfl6
  have hm7 : σ7.sc sMode = 0 := by
    rw [F7.2.1 sMode (by suomega), F6.2.1 sMode (by suomega), F5.2.1 sMode (by suomega), F4.2.1 sMode (by suomega),
      s3 sMode (by decide) (by suomega)]
    exact c1M
  have b2 : (2 : ℤ) ^ (Cp * (wU d n δ r0 R0 a + 1) ^ kp + 2) ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) (by omega)
  have b1 : (1 : ℤ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  have bsp : (0 : ℤ) < 2 ^ (Cp * (wU d n δ r0 R0 a + 1) ^ kp) := by positivity
  have e4 : (2 : ℤ) ^ (Cp * (wU d n δ r0 R0 a + 1) ^ kp + 2) = 4 * 2 ^ (Cp * (wU d n δ r0 R0 a + 1) ^ kp) := by
    ring
  refine XVO.mono (hm d L _ ℓa ℓ σ7 _ _ _ hL hR hz7 hfl7 hzP hzE hm7
    (by split_ifs <;> (simp only [abs_zero, abs_one]; linarith))
    (by linarith) (by rw [abs_mul, abs_two]; linarith) hℓ2) le_rfl fun σ8 ⟨hm8, d8, F8⟩ => ?_
  -- the cells at the end
  have nat8 : ∀ j, j < 8 → σ8.nat j = σ6.nat j := fun j hj => by
    rw [F8.1 j id, F7.1 j (by suomega)]
  have nat8' : ∀ j, j < 4 → σ8.nat j = σ1.nat j := fun j hj => by
    rw [nat8 j (by suomega), F6.1 j (by suomega), F5.1 j (by suomega), F4.1 j (by suomega), n3 j hj]
  have sc84 : ∀ y, y < 30 → y ≠ 29 → y ≠ 2 → y ≠ 23 → y ≠ 1 → σ8.sc y = σ4.sc y :=
    fun y h1 h2 h3 h4 h5 => by
      rw [F8.2.1 y (by suomega), F7.2.1 y (by suomega), F6.2.1 y (by suomega), F5.2.1 y (by suomega)]
  have sc81 : ∀ y, y < 30 → y ≠ 29 → y ≠ 2 → y ≠ 23 → y ≠ 1 → y ≠ 22 → y ≠ 0 → ¬ SPar y →
      σ8.sc y = σ1.sc y := fun y h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [sc84 y h1 h2 h3 h4 h5, F4.2.1 y (by suomega), s3 y h7 h8]
  have arr84 : ∀ b k, b < 8 → b ≠ aA → b ≠ aB → σ8.arr b k = σ4.arr b k := fun b k h1 h2 h3 => by
    rw [F8.2.2.1 b k id, F7.2.2.1 b k (fun h => h.1.elim h2 h3), F6.2.2.1 b k (by suomega),
      F5.2.2.1 b k (by suomega)]
  have arr71 : ∀ b k, b < 8 → ¬ ATri d b k → σ6.arr b k = σ1.arr b k := fun b k h1 h2 => by
    rw [F6.2.2.1 b k (by suomega), F5.2.2.1 b k (by suomega), F4.2.2.1 b k h2, a3 b k h1]
  have arr81 : ∀ b k, b < 8 → b ≠ aA → b ≠ aB → ¬ ATri d b k → σ8.arr b k = σ1.arr b k :=
    fun b k h1 h2 h3 h4 => by rw [arr84 b k h1 h2 h3, F4.2.2.1 b k h4, a3 b k h1]
  have hA8 : ∀ b, (b = aA ∨ b = aB) → ∀ k, σ8.arr b k = if ∃ j < d, k = 0 + (d + 1) * j then σ7.arr b k else 0 :=
    fun b hb k => by
      rw [F8.2.2.1 b k id]
      split_ifs with h
      · rfl
      · rw [F7.2.2.1 b k (fun h' => h h'.2), arr71 b k (by rcases hb with rfl | rfl <;> decide)
          (by rcases hb with rfl | rfl <;> suomega)]
        exact ha1 b (by rcases hb with rfl | rfl <;> decide) (by rcases hb with rfl | rfl <;> decide) k
  have dr8 : σ8.draws = K0O d n δ r0 R0 := by
    have := LposO_le_K0O d n δ r0 R0
    rw [d8, d7, d6, d5, d4, dr3]
    omega
  have rd8 : σ8.rounds = 0 := by
    rw [F8.2.2.2.1, F7.2.2.2.1, F6.2.2.2.1, F5.2.2.2.1, F4.2.2.2.1, Env.setSc_rounds, F2.2.2.2.1]
    exact hr1
  refine ⟨bloInv_mk (s := C0 * (wU d n δ r0 R0 a + 1) ^ k0 + (Cp * (wU d n δ r0 R0 a + 1) ^ kp +
      Ct * (wU d n δ r0 R0 a + 1) ^ kt)) (orc := w.orc) (c := cfgW d n δ r0 R0 a w)
    ⟨by simp only [nN0]; omega, by simp only [nS0]; omega, by simp only [nA0]; omega⟩ (by omega) (by omega) hnE
    (parN_half_iff _ _ _) (parN_onG_A0 _ _ _) (parN_onG_B0 _ _ _)
    ((nat8' rD (by decide)).trans n1D) ((nat8' rM (by decide)).trans n1M) ((nat8' rMk (by decide)).trans n1Mk)
    ((nat8' rOne (by decide)).trans n1One) (P7.frame F8 (fun y _ _ => by suomega) fun j _ _ => id)
    ((B7.congr fun y _ _ => F8.2.1 y (by suomega)).mono (by omega))
    ((F8.2.1 sZ (by suomega)).trans hz7) ((sc81 sN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by suomega)).trans c1N) ((F8.2.1 sFirst (by suomega)).trans hF7)
    ((F8.2.1 sDmu (by suomega)).trans hDm7)
    ((sc81 sK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by suomega)).trans c1K)
    ((sc81 sL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by suomega)).trans c1L)
    hm8
    (posIn_mono (posIn_congr hPos4 (sc84 sDS (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun k => arr84 _ k (by decide) (by decide) (by decide)) fun k => arr84 _ k (by decide) (by decide)
        (by decide)) (by omega))
    (fun k hk => (arr81 aMuS k (by decide) (by decide) (by decide) (by suomega)).trans
      (ha1 aMuS (by decide) (by decide) k))
    (fun k hk => (arr81 aAS k (by decide) (by decide) (by decide) (by suomega)).trans
      (ha1 aAS (by decide) (by decide) k))
    (ptIn_mono (ptIn_congr hctr1 fun k => arr81 aC k (by decide) (by decide) (by decide) (by suomega))
      (by omega))
    (fun k hk => (arr81 aC k (by decide) (by decide) (by decide) (by suomega)).trans (ha1C k hk))
    (fun k => (arr81 aMu k (by decide) (by decide) (by decide) (by suomega)).trans (ha1 aMu (by decide) (by decide) k))
    (fun k => (arr81 ab k (by decide) (by decide) (by decide) (by suomega)).trans (ha1 ab (by decide) (by decide) k))
    (fun k => (arr81 aG k (by decide) (by decide) (by decide) (by suomega)).trans (ha1 aG (by decide) (by decide) k))
    (fun k => by
      rw [hA8 aA (Or.inl rfl) k]
      split_ifs with h
      · obtain ⟨j, hj, rfl⟩ := h; exact hA7 j hj
      · rfl)
    (fun k => by
      rw [hA8 aB (Or.inr rfl) k]
      split_ifs with h
      · obtain ⟨j, hj, rfl⟩ := h; exact hB7 j hj
      · rfl)
    rd8 dr8, posBnd_of_posInO (posIn_mono hPos4 (by omega))⟩

/-! ## `ProgSetupO` from the sub-block contracts -/

theorem RoomO.mono {L : Layout} {nS nN nA nS' nN' nA' : ℕ} (h : RoomO L nS' nN' nA') (hS : nS ≤ nS')
    (hN : nN ≤ nN') (hA : nA ≤ nA') : RoomO L nS nN nA :=
  ⟨hS.trans h.1, hN.trans h.2.1, hA.trans h.2.2⟩

section Room

variable {x : Layout → XCmdO} {C k nS nN nA nS' nN' nA' : ℕ}

theorem P0SpecO.room (h : P0SpecO x C k nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    P0SpecO x C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ hI hL (hR.mono hS hN hA)

theorem ParamSpecO.room (h : ParamSpecO x C k nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    ParamSpecO x C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ σ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ σ hI hL (hR.mono hS hN hA)

theorem TriSpecO.room (h : TriSpecO x C k nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    TriSpecO x C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ σ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ σ hI hL (hR.mono hS hN hA)

theorem CoinsSpecO.room (h : CoinsSpecO x C k nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    CoinsSpecO x C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ σ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ σ hI hL (hR.mono hS hN hA)

theorem CrossSpecO.room (h : CrossSpecO x C k nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    CrossSpecO x C k nS' nN' nA' := fun d L w n δ r0 R0 a ℓa ℓ s S σ hI hL hR =>
  h d L w n δ r0 R0 a ℓa ℓ s S σ hI hL (hR.mono hS hN hA)

theorem ModeSpecO.room (h : ModeSpecO x C nS nN nA) (hS : nS ≤ nS') (hN : nN ≤ nN') (hA : nA ≤ nA') :
    ModeSpecO x C nS' nN' nA' := fun d L XO ℓa ℓ σ fl PF ep hL hR =>
  h d L XO ℓa ℓ σ fl PF ep hL (hR.mono hS hN hA)

end Room

/-- **`ProgSetupO` from the six sub-block contracts**, each for some command, constants and room. -/
theorem progSetupO_of (h0 : ∃ (xp0 : Layout → XCmdO) (C k nS nN nA : ℕ), P0SpecO xp0 C k nS nN nA)
    (hp : ∃ (xpar : Layout → XCmdO) (C k nS nN nA : ℕ), ParamSpecO xpar C k nS nN nA)
    (ht : ∃ (xtri : Layout → XCmdO) (C k nS nN nA : ℕ), TriSpecO xtri C k nS nN nA)
    (hc : ∃ (xcoins : Layout → XCmdO) (C k nS nN nA : ℕ), CoinsSpecO xcoins C k nS nN nA)
    (hx : ∃ (xcross : Layout → XCmdO) (C k nS nN nA : ℕ), CrossSpecO xcross C k nS nN nA)
    (hm : ∃ (xmode : Layout → XCmdO) (C nS nN nA : ℕ), ModeSpecO xmode C nS nN nA) : ProgSetupO := by
  obtain ⟨x0, C0, k0, s0, n0, a0, h0⟩ := h0
  obtain ⟨xp, Cp, kp, sp, np, ap, hp⟩ := hp
  obtain ⟨xt, Ct, kt, st, nt, at', ht⟩ := ht
  obtain ⟨xc, Cc, kc, sc, nc, ac, hc⟩ := hc
  obtain ⟨xx, Cx, kx, sx, nx, ax, hx⟩ := hx
  obtain ⟨xm, Cm, sm, nm, am, hm⟩ := hm
  refine ⟨_, _, _, s0 + sp + st + sc + sx + sm + 172, n0 + np + nt + nc + nx + nm + 48,
    a0 + ap + at' + ac + ax + am + 16, setupSpecO_of (xp0 := x0) (xpar := xp) (xtri := xt) (xcoins := xc)
      (xcross := xx) (xmode := xm) (h0.room (by omega) (by omega) (by omega)) (hp.room (by omega) (by omega)
      (by omega)) (ht.room (by omega) (by omega) (by omega)) (hc.room (by omega) (by omega) (by omega))
      (hx.room (by omega) (by omega) (by omega)) (hm.room (by omega) (by omega) (by omega)) (by omega) (by omega)
      (by omega)⟩

end AdversarialBco.Unified.ProgO
