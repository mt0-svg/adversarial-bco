/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgODrv
public import AdversarialBco.Unified.BLOSpec
public import AdversarialBco.Bit.Transfer.XDrvPoly

@[expose] public section

/-!
# BL-O's program on the oracle machine: the invariant, the setup contract and the driver

The skeleton of UNI-PROG: BL-O's program is `progBLO xinit xA xM xB L`, the driver `progO` of
ProgODrv.lean with the machine's setup `xsetup L rD` (Bit/Transfer/XSetup.lean) followed by `xinit L` (P0, PARAM at
`k_δ`, TRI-OGD-O, the cross check, the mode), and the round in three segments `xA L` (R1a, the draw blocks), `xM L`
(R2, the gauge play and the play leaf) and `xB L` (R3 the clipped reading, R1b the dither block, R5 to R15).

* `BLOInv`: BL's invariant `BLInv` (Bit/Transfer/XBLInv.lean) on the rowless configuration `cfgV c` of BL-O's
  configuration `c` (no input row, no kept row, the frame centre `a`): the parameters of PARAM, the position, the
  centre in the form of the play leaf, the mode and the state, the round count and the coins on BL's schedule with the
  prologue `K0O`. So every v2.1 piece stated on `BLInv` applies to BL-O's cells. The oracle data `r0`, `R0`, `a` are
  the input cells (read by `rdIn` at any time); the constants `kC`, `jG`, `qO`, `kK` of BLOSpec.lean are computed
  from them and from the parameters where they are used.
* `SetupSpecO xinit C k nS nN nA`: from the environment after the machine's setup, `xinit L` ends in `BLOInv` at round
  `0` with the mode `modeO .. 0`, the position bounded by `2^{C (W + 1)^k}`, within `C (W + E + 1)^k` units.

Here `W = wU = d + size n + S + 1`, `S` the input size.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The invariant and the inputs -/

/-- The rowless configuration of BL that BL-O's cells hold: BL-O's parameters, position and frame centre, no row. -/
def cfgV (c : CfgO d) : Cfg d := ⟨c.par, 0, fun i => i.elim0, fun i => i.elim0, c.μS, c.AS, c.a⟩

/-- **BL-O's invariant** before round `t`: BL's invariant on the rowless configuration, with no input row. -/
def BLOInv (L : Layout) (n K0 E : ℕ) (c : CfgO d) (mo : Mode d) (t : ℕ) (σ : Env d) : Prop :=
  BLInv L n 0 K0 E (cfgV c) mo t σ

/-- The inputs of `TheoremUnified`. -/
structure InU (d n : ℕ) (δ r0 R0 : ℚ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hr0 : 0 < r0
  hR0 : r0 ≤ R0

/-- The work term of an input: `d + size n + S + 1`, `S` the input size. -/
def wU (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℕ := d + n.size + sizeN δ r0 R0 a + 1

/-- Room for a block's cells in the layout. -/
def RoomO (L : Layout) (nS nN nA : ℕ) : Prop := nS ≤ L.NS ∧ nN ≤ L.NN ∧ nA ≤ L.NA

/-! ## The contracts -/

/-- **The setup contract.** From the environment after the machine's setup (`envSetup rD d`), `xinit L` ends in BL-O's
invariant at round `0` with the first mode, the position bounded by `2^{C (W + 1)^k}`, within `C (W + E + 1)^k`
units, on every input and world, for every exponent `E ≥ C (W + 1)^k`, with room `nS, nN, nA` in the layout. -/
def SetupSpecO (xinit : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (E ℓa ℓ : ℕ),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → C * (wU d n δ r0 R0 a + 1) ^ k ≤ E →
    C * (wU d n δ r0 R0 a + E + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + E + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xinit L) (envSetup rD d) (C * (wU d n δ r0 R0 a + E + 1) ^ k)
      (fun σ => BLOInv L n (K0O d n δ r0 R0) E (cfgW d n δ r0 R0 a w) (modeO d n δ r0 R0 a w 0) 0 σ ∧
        PosBnd (cfgV (cfgW d n δ r0 R0 a w)) (C * (wU d n δ r0 R0 a + 1) ^ k))

/-- **BL-O's program** on the layout `L`. -/
def progBLO (xinit xA xM xB : Layout → XCmdO) (L : Layout) : List InstrO :=
  progO (.seq (.base (xsetup L rD)) (xinit L)) (xA L) (xM L) (xB L)

/-! ## The constants of the driver -/

/-- The constants of the setup and of the round. -/
structure DrvKO where
  Cs : ℕ
  ks : ℕ
  nSs : ℕ
  nNs : ℕ
  nAs : ℕ
  C : ℕ
  k : ℕ
  Cn : ℕ
  kn : ℕ
  nS : ℕ
  nN : ℕ
  nA : ℕ

namespace DrvKO

variable (K : DrvKO) (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ)

/-- The layout: room for the setup's cells and the round's, and for the machine's setup. -/
def L : Layout := { NN := K.nNs + K.nN + 1, NS := K.nSs + K.nS + 1, NA := K.nAs + K.nA + 1 }

/-- The bound of the position. -/
def E0 : ℕ := K.Cs * (wU d n δ r0 R0 a + 1) ^ K.ks

/-- The exponent of the invariant. -/
def E : ℕ := K.E0 d n δ r0 R0 a + K.Cn * (wU d n δ r0 R0 a + K.E0 d n δ r0 R0 a + 1) ^ K.kn

/-- The units of the setup after the machine's. -/
def Ki : ℕ := K.Cs * (wU d n δ r0 R0 a + K.E d n δ r0 R0 a + 1) ^ K.ks

/-- The units of one segment of a round. -/
def Kr : ℕ := K.C * (wU d n δ r0 R0 a + K.E d n δ r0 R0 a + 1) ^ K.k

/-- The bits of the magnitudes. -/
def ell : ℕ := K.Ki d n δ r0 R0 a + K.Kr d n δ r0 R0 a + d + 1

/-- Every count that a register must hold. -/
def Q : ℕ := K.Ki d n δ r0 R0 a + K.Kr d n δ r0 R0 a + (K.L.NN + K.L.NS + K.L.NA + 8) + K.L.base d K.L.NA +
  offU d + 4

/-- The bits of the registers. -/
def ella : ℕ := (K.Q d n δ r0 R0 a).size

/-- The units of the setup, the machine's included. -/
def Ks : ℕ := K.L.NS + 2 * K.L.NA + 7 + K.Ki d n δ r0 R0 a

/-- The cost bound of `progO_ok`. -/
def cost : ℕ :=
  costP (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) (K.Ks d n δ r0 R0 a) +
    2 * costR (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a)
      (K.Kr d n δ r0 R0 a + K.Kr d n δ r0 R0 a + K.Kr d n δ r0 R0 a)

/-- The space bound of `progO_ok`, in `ℕ`. -/
def space : ℕ :=
  max (inSpaceU d n δ r0 R0 a) (ckSpaceU d n δ r0 R0 a (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a)) +
    (costP (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a) (K.Ks d n δ r0 R0 a) +
      costR (K.ella d n δ r0 R0 a) (K.ell d n δ r0 R0 a)
        (K.Kr d n δ r0 R0 a + K.Kr d n δ r0 R0 a + K.Kr d n δ r0 R0 a))

theorem Q_lt : K.Q d n δ r0 R0 a < 2 ^ K.ella d n δ r0 R0 a := Nat.lt_size_self _

theorem layOK : LayOK K.L d (K.ella d n δ r0 R0 a) := by
  have := K.Q_lt d n δ r0 R0 a
  unfold Q at this
  exact ⟨by omega, by omega⟩

end DrvKO

/-! ## The polynomial bounds -/

/-- An input of `TheoremUnified`. -/
structure UInp where
  d : ℕ
  n : ℕ
  δ : ℚ
  r0 : ℚ
  R0 : ℚ
  a : Fin d → ℚ

/-- The inputs of `TheoremUnified`. -/
def UInp.OK (i : UInp) : Prop := InU i.d i.n i.δ i.r0 i.R0

/-- The work term of an input. -/
def UInp.X (i : UInp) : ℕ := wU i.d i.n i.δ i.r0 i.R0 i.a

theorem UInp.X_ge (i : UInp) : i.d ≤ i.X ∧ i.n.size ≤ i.X ∧ sizeN i.δ i.r0 i.R0 i.a ≤ i.X ∧ 1 ≤ i.X := by
  unfold UInp.X wU
  omega

/-- **The totals of the driver are polynomial** in the work term `W = d + size n + S + 1`. -/
theorem drvO_poly (K : DrvKO) : ∃ c k : ℕ, ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 →
    K.cost d n δ r0 R0 a ≤ c * wU d n δ r0 R0 a ^ k ∧ K.space d n δ r0 R0 a ≤ c * wU d n δ r0 R0 a ^ k := by
  have hX : ∀ i : UInp, i.OK → 1 ≤ i.X := fun i _ => i.X_ge.2.2.2
  have pX : PolyB UInp.OK UInp.X (fun i => i.X) := PolyB.self
  have pd : PolyB UInp.OK UInp.X (fun i => i.d) := PolyB.le_X fun i _ => i.X_ge.1
  have pns : PolyB UInp.OK UInp.X (fun i => i.n.size) := PolyB.le_X fun i _ => i.X_ge.2.1
  have pS : PolyB UInp.OK UInp.X (fun i => sizeN i.δ i.r0 i.R0 i.a) := PolyB.le_X fun i _ => i.X_ge.2.2.1
  have pc : ∀ c : ℕ, PolyB UInp.OK UInp.X (fun _ => c) := PolyB.const
  have pE0 : PolyB UInp.OK UInp.X (fun i => K.E0 i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pc K.Cs).mul ((pX.add hX (pc 1)).pow K.ks)).mono fun i _ => le_rfl
  have pE : PolyB UInp.OK UInp.X (fun i => K.E i.d i.n i.δ i.r0 i.R0 i.a) :=
    (pE0.add hX ((pc K.Cn).mul (((pX.add hX pE0).add hX (pc 1)).pow K.kn))).mono fun i _ => le_rfl
  have pKi : PolyB UInp.OK UInp.X (fun i => K.Ki i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pc K.Cs).mul (((pX.add hX pE).add hX (pc 1)).pow K.ks)).mono fun i _ => le_rfl
  have pKr : PolyB UInp.OK UInp.X (fun i => K.Kr i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pc K.C).mul (((pX.add hX pE).add hX (pc 1)).pow K.k)).mono fun i _ => le_rfl
  have pell : PolyB UInp.OK UInp.X (fun i => K.ell i.d i.n i.δ i.r0 i.R0 i.a) :=
    (((pKi.add hX pKr).add hX pd).add hX (pc 1)).mono fun i _ => le_rfl
  have poff : PolyB UInp.OK UInp.X (fun i => offU i.d) :=
    ((pc 8).add hX ((pc 2).mul pd)).mono fun i _ => le_rfl
  have pQ : PolyB UInp.OK UInp.X (fun i => K.Q i.d i.n i.δ i.r0 i.R0 i.a) := by
    have p1 := (((((pKi.add hX pKr).add hX (pc (K.L.NN + K.L.NS + K.L.NA + 8))).add hX
      ((pc (K.L.NS + 1)).add hX ((pc K.L.NA).mul ((pd.mul pd).add hX pd)))).add hX poff).add hX (pc 4))
    refine p1.mono fun i _ => le_of_eq ?_
    simp only [DrvKO.Q, Layout.base, asz]
  have pella : PolyB UInp.OK UInp.X (fun i => K.ella i.d i.n i.δ i.r0 i.R0 i.a) := pQ.size
  have p2a : PolyB UInp.OK UInp.X (fun i => 2 ^ K.ella i.d i.n i.δ i.r0 i.R0 i.a) := PolyB.two_pow_size hX pQ
  have pKs : PolyB UInp.OK UInp.X (fun i => K.Ks i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pc (K.L.NS + 2 * K.L.NA + 7)).add hX pKi).mono fun i _ => le_rfl
  have pxs : PolyB UInp.OK UInp.X
      (fun i => xstepCost (K.ella i.d i.n i.δ i.r0 i.R0 i.a) (K.ell i.d i.n i.δ i.r0 i.R0 i.a)) :=
    ((((pc 40).add hX ((pc 12).mul pella)).add hX ((pc 4).mul pell)).add hX
      (((pella.add hX pell).add hX (pc 1)).pow 2)).mono fun i _ => le_rfl
  have pcP : PolyB UInp.OK UInp.X (fun i => costP (K.ella i.d i.n i.δ i.r0 i.R0 i.a) (K.ell i.d i.n i.δ i.r0 i.R0 i.a)
      (K.Ks i.d i.n i.δ i.r0 i.R0 i.a)) :=
    ((pxs.add hX (pKs.mul pxs)).add hX (pc 5)).mono fun i _ => le_rfl
  have pcR : PolyB UInp.OK UInp.X (fun i => costR (K.ella i.d i.n i.δ i.r0 i.R0 i.a) (K.ell i.d i.n i.δ i.r0 i.R0 i.a)
      (K.Kr i.d i.n i.δ i.r0 i.R0 i.a + K.Kr i.d i.n i.δ i.r0 i.R0 i.a + K.Kr i.d i.n i.δ i.r0 i.R0 i.a)) :=
    ((((pKr.add hX pKr).add hX pKr).mul pxs).add hX (pc 6)).mono fun i _ => le_rfl
  have pcost : PolyB UInp.OK UInp.X (fun i => K.cost i.d i.n i.δ i.r0 i.R0 i.a) :=
    (pcP.add hX ((pc 2).mul pcR)).mono fun i _ => le_rfl
  have plen : PolyB UInp.OK UInp.X (fun i => lenIn i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pd.add hX pns).add hX pS).mono fun i _ => by
      unfold lenIn
      have h1 := Conj1BitSanity.len_le_self i.d
      have h2 : len (i.n : ℤ) = i.n.size := by unfold len; rw [Int.natAbs_natCast]
      omega
  have pin : PolyB UInp.OK UInp.X (fun i => inSpaceU i.d i.n i.δ i.r0 i.R0 i.a) :=
    (poff.mul (poff.add hX plen)).mono fun i _ => by
      unfold inSpaceU
      have := Conj1BitSanity.len_le_self (offU i.d)
      gcongr
  have pck : PolyB UInp.OK UInp.X (fun i => ckSpaceU i.d i.n i.δ i.r0 i.R0 i.a (K.ella i.d i.n i.δ i.r0 i.R0 i.a)
      (K.ell i.d i.n i.δ i.r0 i.R0 i.a)) :=
    ((poff.add hX ((pc 2).mul p2a)).mul (((((pc 2).mul pella).add hX pell).add hX plen).add hX (pc 3))).mono
      fun i _ => le_rfl
  have pspace : PolyB UInp.OK UInp.X (fun i => K.space i.d i.n i.δ i.r0 i.R0 i.a) :=
    ((pin.add hX pck).add hX (pcP.add hX pcR)).mono fun i _ => by
      unfold DrvKO.space
      have := max_le_add_of_nonneg (Nat.zero_le (inSpaceU i.d i.n i.δ i.r0 i.R0 i.a))
        (Nat.zero_le (ckSpaceU i.d i.n i.δ i.r0 i.R0 i.a (K.ella i.d i.n i.δ i.r0 i.R0 i.a)
          (K.ell i.d i.n i.δ i.r0 i.R0 i.a)))
      omega
  obtain ⟨c, k, h⟩ := pcost.add hX pspace
  refine ⟨c, k, fun d n δ r0 R0 a hI => ?_⟩
  have := h ⟨d, n, δ, r0, R0, a⟩ hI
  simp only [UInp.X] at this
  constructor <;> omega

/-! ## The frozen form -/

/-- The input size is at least `1`: the denominator of `δ` is. -/
theorem sizeN_pos (δ r0 R0 : ℚ) (a : Fin d → ℚ) : 1 ≤ sizeN δ r0 R0 a := by
  have h : 1 ≤ len (δ.den : ℤ) := by
    unfold len
    rw [Int.natAbs_natCast]
    exact Nat.size_pos.2 δ.pos
  unfold sizeN
  omega

/-- The work term against the frozen form: `W ≤ (4 / log 2) d log(2 d n/δ) S`. -/
theorem wU_le_log {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    (wU d n δ r0 R0 a : ℝ) ≤ 4 / Real.log 2 * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hI.hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hI.hn
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hI.hδ0
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hI.hδ1
  have hS : (1 : ℝ) ≤ sizeU δ r0 R0 a := by rw [sizeU_eq]; exact_mod_cast sizeN_pos δ r0 R0 a
  -- `log (2 n) ≤ log (2 d n / δ)`
  have h2n : (2 : ℝ) * n ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hL2n : Real.log (2 * n) ≤ Real.log (2 * d * n / δ) := Real.log_le_log (by positivity) h2n
  have hL2 : Real.log 2 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
  set Lg := Real.log (2 * d * n / (δ : ℝ))
  have hLg : Real.log 2 ≤ Lg := hL2.trans hL2n
  have hns : (n.size : ℝ) * Real.log 2 ≤ Lg := by
    have := Conj1BitSanity.len_mul_log_le n hI.hn
    have e : len (n : ℤ) = n.size := by unfold len; rw [Int.natAbs_natCast]
    rw [e] at this
    exact this.trans hL2n
  set Y := (d : ℝ) * Lg * sizeU δ r0 R0 a / Real.log 2
  have hY1 : (d : ℝ) * sizeU δ r0 R0 a ≤ Y := by
    rw [le_div_iff₀ hl2]
    have : (d : ℝ) * sizeU δ r0 R0 a * Real.log 2 ≤ (d : ℝ) * sizeU δ r0 R0 a * Lg :=
      mul_le_mul_of_nonneg_left hLg (by positivity)
    linarith
  have hdS : (1 : ℝ) ≤ (d : ℝ) * sizeU δ r0 R0 a := by nlinarith
  have hdY : (d : ℝ) ≤ Y := (le_mul_of_one_le_right (by positivity) hS).trans hY1
  have hSY : sizeU δ r0 R0 a ≤ Y := (le_mul_of_one_le_left (by positivity) hdR).trans hY1
  have hnY : (n.size : ℝ) ≤ Y := by
    have h1 : (n.size : ℝ) ≤ Lg / Real.log 2 := by rw [le_div_iff₀ hl2]; exact hns
    have h2 : Lg / Real.log 2 ≤ Y := by
      simp only [Y]
      rw [div_le_div_iff_of_pos_right hl2]
      have hL0 : 0 ≤ Lg := hl2.le.trans hLg
      nlinarith
    exact h1.trans h2
  have e : (wU d n δ r0 R0 a : ℝ) = d + n.size + sizeU δ r0 R0 a + 1 := by
    unfold wU; rw [sizeU_eq]; push_cast; ring
  rw [e]
  have : 4 / Real.log 2 * ((d : ℝ) * Lg * sizeU δ r0 R0 a) = 4 * Y := by
    simp only [Y]; field_simp
  rw [this]
  linarith

/-- `c W^k ≤ c (4 / log 2)^k (d log(2 d n/δ) S)^k`. -/
theorem frozenO_form {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) (c k : ℕ) :
    (c : ℝ) * (wU d n δ r0 R0 a : ℝ) ^ k ≤
      c * (4 / Real.log 2) ^ k * ((d : ℝ) * Real.log (2 * d * n / (δ : ℝ)) * sizeU δ r0 R0 a) ^ k := by
  rw [mul_assoc, ← mul_pow]
  gcongr
  exact wU_le_log a hI

theorem costOKO_mono {P : List InstrO} {w : WorldO d} {s0 : State d} {n : ℕ} {B B' : ℝ}
    (h : CostOKO P w s0 n B) (hB : B ≤ B') : CostOKO P w s0 n B' := fun k hk => by
  obtain ⟨j, h1, h2⟩ := h k hk
  exact ⟨j, h1, h2.trans (by linarith)⟩

theorem spaceOKO_mono {P : List InstrO} {w : WorldO d} {s0 : State d} {n : ℕ} {B B' : ℝ}
    (h : SpaceOKO P w s0 n B) (hB : B ≤ B') : SpaceOKO P w s0 n B' := fun k hk =>
  spaceLE_mono (h k hk) hB

/-! ## The contracts of BLOSpec.lean -/

/-- The setup contract for some command and constants. -/
def ProgSetupO : Prop := ∃ (xinit : Layout → XCmdO) (C k nS nN nA : ℕ), SetupSpecO xinit C k nS nN nA

end AdversarialBco.Unified.ProgO
