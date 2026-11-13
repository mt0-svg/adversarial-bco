/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Bit
public import AdversarialBco.Bit.ShadowWEv
public import AdversarialBco.Bit.ShadowCoup
public import AdversarialBco.Bit.TriStage
public import AdversarialBco.Bit.CoinSchedLaw
public import AdversarialBco.Bit.RegMeas
public import AdversarialBco.Conj1Bit.Sanity
public import AdversarialBco.Conj1Poly.Geom
public import AdversarialBco.Conj1PolyExp.Majorant
public import AdversarialBco.Conj1Exp.Bound
public import AdversarialBco.Poly.Df2CompProof
public import AdversarialBco.Poly.Df2DetProof

@[expose] public section

/-!
# The assembly of `TheoremConj1UpperBit`

`theoremConj1UpperBit_of : AsmHyp D C' k → TheoremConj1UpperBit` for a bit learner `D` (`BLInst`: its program, its
prologue length `K0` and block length `B`, its run record on the coupled world; its digit map is `Sched.beta` of
Bit/CoinSched.lean, `BLInst.β`). `AsmHyp` is the conjunction of the bricks, one named `Prop` each; Conj1Bit/Main.lean
proves each of them:

* `MachOK` (the machine clauses, `CostOKBit`, `SpaceOKBit` and the plays in `K`, for every admissible deterministic
  strategy and every coin sequence): the proposition of the bounds of BL with the compiler of the compilation
  proposition
  (`prog_ok_frozenR` of Bit/Transfer/XDrvReach.lean turns the program texts into the two
  clauses).
* `RunOK` (BL's run record: the coupling `coupMax`, `BLMeas`, `BitsHyp` with `bits = E_bits ∩ Z_n` at the noise law
  `dirac 0`, `EngineHyp`, and the record's losses and plays equal to BL's on the coins `β gs`): the proposition of the
  run of BL (with (O3), (O6), (W0) and (P1) to (P5) inside its proof), cut into pieces A to D in
  Bit/BLRun.lean.
* `PosInst` (BL's position is the output `triPos` of TRI-OGD staged on a frame `B̄(c, 1/2) ⊆ K`, its `m_st L` coins
  within the `K0` coins of the prologue): the position theorem and the frame theorem; `PosTri` of Bit/BLRun.lean.
  `PosHyp` at BL's record follows by `triPos_posHyp` (Bit/TriStage.lean): `posOK_of_inst`.

Proved here: `W0Law (D.β d n)` (`w0Law_blInst`, from `Sched.w0Law_beta` of Bit/CoinSchedLaw.lean, the digit-map lemma),
and the prologue coins read odd terms of the stream only
(`Sched.grp_odd`); `RegMeasOK P` for every program `P` (`regMeasOK`, from `RegMeas.measurable_regret` of
Bit/RegMeas.lean: the regret is measurable in the seed and the coins under `RandAdv` when `P` plays in `K`).

The glue: BL runs at `δ = deltaBL d n = 2^{-19}/(d n)^3` (Algorithm BL). If
`ε > 1/4` at `df2oPar d n δ`, the regret is at most `n` on every run and `n ≤ thrBL d n` (`n_le_thr`, from
`Df2Trivial`). If `ε ≤ 1/4` (`RunCase`), at each seed `θ` the proposition of the coupling of a run (`shadowProp_holds`)
bounds the
probability of `{B_n + 1 < Reg}` on the coupled world at `ν = dirac 0` by `δpos + δ_ref + δbits + n (κ0 + κ1) ≤ 1/n`,
and the digit map moves it to the coins (`coins_eq`); `B_n + 1 ≤ thrBL d n` (`comp_thresh`). So every section of the
bad event `{thrBL d n < Reg}` of `ρ ⊗ coinStream` has measure at most `1/n`, the bad event too
(`prod_le_of_sections`), and `exists_majorant_of_bad` gives the majorant with mean at most `thrBL d n + 1`, which is at
most `10^29 d^{3/2} n^{1/2} log^5 (2 d n)` (`thr_add_one_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace AdversarialBco.Bit.Asm

open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd regretPts polytope HeightLE gaussStream)
open AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Bit.Cpl

variable {d : ℕ}

/-! ## BL's confidence and the threshold -/

/-- BL's confidence `δ = 2^{-19}/(d n)^3` (Algorithm BL): BL runs D0's parameters `df2oPar d n δ` at this
`δ`, and the bricks are asked at it. -/
noncomputable def deltaBL (d n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ 19 / ((d : ℝ) * n) ^ 3

/-- The threshold of the bad event: the bound of `comp_thresh` at `δ = deltaBL d n`. -/
noncomputable def thrBL (d n : ℕ) : ℝ :=
  10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / deltaBL d n) ^ 5

/-! ## The input, the strategies, the regret -/

/-- The hypotheses of `TheoremConj1UpperBit` on the input `d, n, m, M, A, b`. -/
structure InputOK (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  height : HeightLE A b M
  ball : ∃ c : E d, Metric.closedBall c 1 ⊆ polytope A b
  diam : ∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n

/-- An admissible deterministic strategy on `K` for `n` rounds: on every rational history the loss of each round
`t < n` is admissible (the first clause of `RandAdv` at a fixed seed). -/
def AdmStrat (K : Set (E d)) (n : ℕ) (σ : Strategy d) : Prop :=
  ∀ t < n, ∀ q : ℕ → Fin d → ℚ, AdmLoss K (lossAd σ 0 (fun i => toE (q i)) t)

/-- The regret of the run of `P` on the input `d, n, m, A, b` against the strategy `σ` with the coins `cs`, as in
`TheoremConj1UpperBit`. -/
noncomputable def regBit (P : List Instr) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : Strategy d) (cs : ℕ → Bool) : ℝ :=
  regretPts (polytope A b) (lossAd σ 0 (playedBit P ⟨σ, cs⟩ (initBit d n m A b)))
    (playedBit P ⟨σ, cs⟩ (initBit d n m A b)) n

/-- The case in which the assembly uses SHADOW: `ε ≤ 1/4` at `df2oPar d n (deltaBL d n)`. BL is then in its mode `run`
(it needs `ε' ≤ 1/2`, and `ε' ≤ ε + 2^{-p-4} ρ`); off this case the regret is at most
`n ≤ thrBL d n`, in every mode. -/
def RunCase (d n : ℕ) : Prop := (df2oPar d n (deltaBL d n)).eps ≤ 1 / 4

/-! ## BL and the bricks -/

/-- The bit learner BL as the assembly reads it. -/
structure BLInst where
  /-- The program. -/
  P : List Instr
  /-- The number of coins of the prologue at `(d, n)` (TRI-OGD staged reads the first `m_st L` of them). -/
  K0 : ℕ → ℕ → ℕ
  /-- BL's block length at `(d, n)`: each uniform of `BM-INT` reads `B d n` coins. -/
  B : ℕ → ℕ → ℕ
  /-- The block length is positive. -/
  B_pos : ∀ d n, 0 < B d n
  /-- BL's run record on the coupled world (`Run` of Bit/ShadowIface.lean), on the input `d, n, m, A, b` against the
  strategy `σ`. -/
  run : (d n m : ℕ) → (A : Matrix (Fin m) (Fin d) ℚ) → (b : Fin m → ℚ) → Strategy d → Run d n (polytope A b)

/-- BL's digit map at `(d, n)`: the map `Sched.beta` of Bit/CoinSched.lean with BL's prologue length and block length
(the digit-map lemma). BL's program reads its coins on the schedule of Bit/CoinSched.lean. -/
noncomputable def BLInst.β (D : BLInst) (d n : ℕ) : (ℕ → ℝ) → ℕ → Bool := Sched.beta d (D.K0 d n) (D.B d n)

/-- Brick (MACH), the machine clauses of `TheoremConj1UpperBit` for every admissible deterministic strategy and every
coin sequence: the cost clause, the space clause with `C' (d m log (2 d n) log (2 M))^k`, and the plays of the rounds
`t < n` in `K` (the proposition of the bounds of BL), through `prog_ok_frozenR` (Bit/Transfer/XDrvReach.lean). -/
def MachOK (P : List Instr) (C' : ℝ) (k : ℕ) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b →
    ∀ σ : Strategy d, AdmStrat (polytope A b) n σ → ∀ cs : ℕ → Bool,
      CostOKBit P ⟨σ, cs⟩ (initBit d n m A b) n
          (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
        SpaceOKBit P ⟨σ, cs⟩ (initBit d n m A b) n
          (C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
        ∀ t < n, playedBit P ⟨σ, cs⟩ (initBit d n m A b) t ∈ polytope A b

/-- (REG-MEAS): under `RandAdv`, if `P` plays its rounds `t < n` in `K` on every run, its regret is a measurable
function of the seed and the coins. Its proof is the argument of StatementConj1Bit.lean ("The regret and the
expectation": the points played take countably many values, each on an event measurable in the seed and the coins,
since every reading of `obs` before the play of round `n - 1` is the loss of a round `t < n` at a point of `K`; the
infimum of a convex function over `K` is its infimum over a countable dense subset of the interior). A statement on
the machine, about any program; proved for every program by `regMeasOK` below. -/
def RegMeasOK (P : List Instr) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b →
    ∀ (Θ : Type) [MeasurableSpace Θ] (σ : Θ → Strategy d), RandAdv (polytope A b) n σ →
      (∀ θ cs, ∀ t < n, playedBit P ⟨σ θ, cs⟩ (initBit d n m A b) t ∈ polytope A b) →
      Measurable fun ω : Θ × (ℕ → Bool) => regBit P d n m A b (σ ω.1) ω.2

/-- What BL's run record `B` on the input `d, n, m, A, b` against the strategy `σ` must satisfy
(the proposition of the run of BL): the coupling is `coupMax` (the coupling lemma, Bit/ShadowCoup.lean); `BLMeas`;
`BitsHyp` at
`dirac 0` with `bits = E_bits ∩ Z_n` (the lemma of the draws) and `EngineHyp` at `deltaBL d n` (the precision theorem;
`κ1 = 0` for
BL), with `n (δbits + n (κ0 + κ1)) ≤ 1/4`; and the record's losses and plays of the rounds `t < n` are those of BL's
run on the coins `β gs` of the world (the hypotheses `hlo`, `hpl` of `coins_eq`). -/
structure RunSpec (P : List Instr) (β : (ℕ → ℝ) → ℕ → Bool) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (σ : Strategy d) (B : Run d n (polytope A b)) : Prop where
  /-- The coupling is the maximal coupling of the coupling lemma. -/
  coup : B.Coup = coupMax
  /-- The measurability of BL's draws. -/
  meas : BLMeas B
  /-- The bit clause and Step 1 of SHADOW, with their budget. -/
  engine : ∃ δbits κ0 κ1 : ℝ, 0 ≤ δbits ∧ 0 ≤ κ0 ∧ 0 ≤ κ1 ∧ (n : ℝ) * (δbits + n * (κ0 + κ1)) ≤ 1 / 4 ∧
    BitsHyp (Measure.dirac 0) B δbits ∧ EngineHyp B (deltaBL d n) κ0 κ1
  /-- The losses of the record are those of BL's run on the coins `β gs`. -/
  loss : ∀ (ω : WΩ) (t : ℕ), t < n → B.loss ω t = lossAd σ 0 (playedBit P ⟨σ, β ω.1⟩ (initBit d n m A b)) t
  /-- The plays of the record are those of BL's run on the coins `β gs`. -/
  play : ∀ (ω : WΩ) (t : ℕ), t < n → B.play t ω = playedBit P ⟨σ, β ω.1⟩ (initBit d n m A b) t

/-- Brick (RUN): BL's run record meets `RunSpec` for every input of the frozen statement in the case `RunCase` and
every admissible deterministic strategy (the proposition of the run of BL); its proof uses (O3), (O6), (W0)
and
(P1) to (P5) (the tracking lemma, the selection lemma, the lemma of validity of the mean, the horizon lemma and the
guard). Cut into pieces A to D in
Bit/BLRun.lean. -/
def RunOK (D : BLInst) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b → RunCase d n →
    ∀ σ : Strategy d, AdmStrat (polytope A b) n σ → RunSpec D.P (D.β d n) d n m A b σ (D.run d n m A b σ)

/-- (POS) at BL's record, what SHADOW reads: BL's position is known before round 0 and good off an event of
probability `δpos` with `n δpos ≤ 1/4` (`PosHyp` at `dirac 0` and `deltaBL d n`). Proved from `PosInst` and
`triPos_posHyp` (`posOK_of_inst`). -/
def PosOK (D : BLInst) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b → RunCase d n →
    ∀ σ : Strategy d, AdmStrat (polytope A b) n σ →
      ∃ δpos : ℝ, 0 ≤ δpos ∧ (n : ℝ) * δpos ≤ 1 / 4 ∧
        PosHyp (Measure.dirac 0) (D.run d n m A b σ) (deltaBL d n) δpos

/-- Brick (POS-INST): BL's record has as position the output `triPos` of TRI-OGD staged (Bit/TriStage.lean), on rows
of `K`, at a frame centre `c` with `B̄(c, 1/2) ⊆ K` (the frame theorem (i)), with an integer
`ℓ ≥ log (m_st/δpos)` for some `δpos` with `n δpos ≤ 1/4` (BL's `δpos = δ1 ≤ δ/3`), its `m_st L` coins within the
`K0 d n` coins of the prologue, which read odd terms of the Gaussian stream only (`Sched.grp_odd`, the digit-map lemma);
`PosTri` of Bit/BLRun.lean. -/
def PosInst (D : BLInst) : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b → RunCase d n →
    ∀ σ : Strategy d, AdmStrat (polytope A b) n σ →
      ∃ (m' : ℕ) (α : Fin m' → E d) (β' : Fin m' → ℝ) (c : E d) (ℓ : ℕ) (δpos : ℝ),
        polytope A b = {y | ∀ k, inner ℝ (α k) y ≤ β' k} ∧ Metric.closedBall c (1 / 2) ⊆ polytope A b ∧
        0 < δpos ∧ (n : ℝ) * δpos ≤ 1 / 4 ∧ Real.log (triMst (1 / 2) n / δpos) ≤ ℓ ∧
        triMst (1 / 2) n * triL d ℓ ≤ D.K0 d n ∧
        ∀ ω : WΩ, (D.run d n m A b σ).pos ω = triPos α β' c (1 / 2) n ℓ (D.β d n ω.1)

/-- The bricks of the assembly. (W0-LEAN) and (REG-MEAS) are proved: `Sched.w0Law_beta` (Bit/CoinSchedLaw.lean) and
`regMeasOK` (from `RegMeas.measurable_regret`, Bit/RegMeas.lean). -/
structure AsmHyp (D : BLInst) (C' : ℝ) (k : ℕ) : Prop where
  mach : MachOK D.P C' k
  run : RunOK D
  posInst : PosInst D

/-- (REG-MEAS) for every program: `RegMeas.measurable_regret` on the polytope, whose interior contains the centre of
the unit ball of `InputOK`, from the initial state, at which no round is played. -/
theorem regMeasOK (P : List Instr) : RegMeasOK P := by
  intro d n m M A b hI Θ _ σ hσ hplay
  obtain ⟨c, hc⟩ := hI.ball
  have hint : (interior (polytope A b)).Nonempty :=
    ⟨c, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds c one_pos)
      (Metric.ball_subset_closedBall.trans hc))⟩
  exact RegMeas.measurable_regret P (polytope A b) hint σ hσ (initBit d n m A b) rfl hplay

/-- (W0) for BL's digit map: `Sched.w0Law_beta` with BL's block length, which is positive. -/
theorem w0Law_blInst (D : BLInst) (d n : ℕ) : W0Law (D.β d n) :=
  Sched.w0Law_beta d (D.K0 d n) (D.B d n) (D.B_pos d n)

/-- (POS) at BL's record from the instance of TRI-OGD staged: `triPos_posHyp` on the frame `B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)`,
the outer ball from the diameter bound. -/
theorem posOK_of_inst {D : BLInst} (h : PosInst D) : PosOK D := by
  intro d n m M A b hI hc σ hσ
  obtain ⟨m', α, β', c, ℓ, δpos, hK, hin, hδ0, hnδ, hℓ, hK0, hpos⟩ := h d n m M A b hI hc σ hσ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hI.hn
  have hδ1 : δpos < 1 := by nlinarith
  have hcK : c ∈ polytope A b := hin (Metric.mem_closedBall_self (by norm_num))
  have hout : polytope A b ⊆ Metric.closedBall c n := fun y hy => by
    rw [Metric.mem_closedBall]
    exact hI.diam y hy c hcK
  exact ⟨δpos, hδ0.le, hnδ, triPos_posHyp hI.hd α β' (polytope A b) hK c hin hout (deltaBL d n) δpos hδ0 hδ1 ℓ hℓ
    (Measure.dirac 0) (D.run d n m A b σ) (D.β d n) (w0Law_blInst D d n) (Sched.grp d (D.K0 d n) (D.B d n))
    (Sched.beta_local d (D.K0 d n) (D.B d n)) (fun j hj => Sched.grp_odd (lt_of_lt_of_le hj hK0)) hpos⟩

/-! ## Arithmetic -/

theorem deltaBL_pos {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < deltaBL d n := by
  unfold deltaBL
  have hpos_d_nat : 0 < d := Nat.lt_of_lt_of_le (by decide : 0 < 1) hd
  have hpos_n_nat : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 1) hn
  have hpos_d : (0 : ℝ) < (d : ℝ) := by exact mod_cast hpos_d_nat
  have hpos_n : (0 : ℝ) < (n : ℝ) := by exact mod_cast hpos_n_nat
  have hpos_dn : (0 : ℝ) < (d : ℝ) * (n : ℝ) := mul_pos hpos_d hpos_n
  positivity

theorem deltaBL_lt_one {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : deltaBL d n < 1 := by
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : 1 ≤ (d : ℝ) * (n : ℝ) :=
    one_le_mul_of_one_le_of_one_le hd' hn'
  have h_nonneg_prod : 0 ≤ (d : ℝ) * (n : ℝ) := by linarith
  have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
  have hcube : 1 ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
    have hsq : 1 ≤ ((d : ℝ) * (n : ℝ)) ^ 2 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ ((d : ℝ) * (n : ℝ)) * ((d : ℝ) * (n : ℝ)) :=
          mul_le_mul hprod hprod h_one_nonneg h_nonneg_prod
        _ = ((d : ℝ) * (n : ℝ)) ^ 2 := by ring
    have ha_sq_nonneg : 0 ≤ ((d : ℝ) * (n : ℝ)) ^ 2 := by nlinarith
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((d : ℝ) * (n : ℝ)) ^ 2 * ((d : ℝ) * (n : ℝ)) :=
        mul_le_mul hsq hprod h_one_nonneg ha_sq_nonneg
      _ = ((d : ℝ) * (n : ℝ)) ^ 3 := by ring
  have hpos : 0 ≤ (2 : ℝ)⁻¹ ^ 19 := by positivity
  have hhalf_lt_one : (2 : ℝ)⁻¹ < 1 := by norm_num
  have hhalf_nonneg : 0 ≤ (2 : ℝ)⁻¹ := by norm_num
  have hlt : (2 : ℝ)⁻¹ ^ 19 < 1 :=
    ((pow_lt_one_iff_of_nonneg hhalf_nonneg (by norm_num : 19 ≠ 0)).mpr hhalf_lt_one)
  calc
    deltaBL d n = (2 : ℝ)⁻¹ ^ 19 / ((d : ℝ) * (n : ℝ)) ^ 3 := rfl
    _ ≤ (2 : ℝ)⁻¹ ^ 19 := div_le_self hpos hcube
    _ < 1 := hlt

theorem n_mul_deltaBL_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : (n : ℝ) * deltaBL d n ≤ (2 : ℝ)⁻¹ ^ 19 := by
  dsimp [deltaBL]
  have hpos : 0 < (2 : ℝ)⁻¹ ^ 19 := by positivity
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hineq : (n : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
    have hdn : (n : ℝ) ≤ (d : ℝ) * (n : ℝ) := by
      nlinarith
    have hpos_dn : 1 ≤ (d : ℝ) * (n : ℝ) := by nlinarith
    have hcube : (d : ℝ) * (n : ℝ) ≤ ((d : ℝ) * (n : ℝ)) ^ 3 := by
      have hsq : 1 ≤ ((d : ℝ) * (n : ℝ)) ^ 2 := by
        nlinarith
      calc
        (d : ℝ) * (n : ℝ) = ((d : ℝ) * (n : ℝ)) * 1 := by ring
        _ ≤ ((d : ℝ) * (n : ℝ)) * ((d : ℝ) * (n : ℝ)) ^ 2 := by
          gcongr
        _ = ((d : ℝ) * (n : ℝ)) ^ 3 := by ring
    nlinarith
  have hpos_sq : 0 < ((d : ℝ) * (n : ℝ)) ^ 3 := by positivity
  calc
    (n : ℝ) * ((2 : ℝ)⁻¹ ^ 19 / ((d : ℝ) * (n : ℝ)) ^ 3)
        = ((2 : ℝ)⁻¹ ^ 19) * ((n : ℝ) / ((d : ℝ) * (n : ℝ)) ^ 3) := by ring
    _ ≤ ((2 : ℝ)⁻¹ ^ 19) * 1 := by
      gcongr
      exact (div_le_one hpos_sq).mpr hineq
    _ = (2 : ℝ)⁻¹ ^ 19 := by ring

theorem log_ratio_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    0 ≤ Real.log (2 * d * n / deltaBL d n) ∧ Real.log (2 * d * n / deltaBL d n) ≤ 20 * Real.log (2 * d * n) := by
  have hx : 1 ≤ (d : ℝ) * (n : ℝ) := by
    have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hpos : 0 < (d : ℝ) * (n : ℝ) := by linarith
  have h_eq : 2 * (d : ℝ) * (n : ℝ) / deltaBL d n = (2 : ℝ) ^ 20 * ((d : ℝ) * (n : ℝ)) ^ 4 := by
    unfold deltaBL
    field_simp
  have h_left : 0 ≤ Real.log (2 * (d : ℝ) * (n : ℝ) / deltaBL d n) := by
    rw [h_eq]
    have h_base : 1 ≤ (2 : ℝ) ^ 20 * ((d : ℝ) * (n : ℝ)) ^ 4 := by
      have h2 : 1 ≤ (2 : ℝ) ^ 20 := by norm_num
      have hx4 : 1 ≤ ((d : ℝ) * (n : ℝ)) ^ 4 :=
        one_le_pow₀ hx (n := 4)
      nlinarith
    exact Real.log_nonneg h_base
  have h_right : Real.log (2 * (d : ℝ) * (n : ℝ) / deltaBL d n) ≤ 20 * Real.log (2 * (d : ℝ) * (n : ℝ)) := by
    rw [h_eq]
    have h_pow : (2 : ℝ) ^ 20 * ((d : ℝ) * (n : ℝ)) ^ 4 ≤ ((2 : ℝ) * ((d : ℝ) * (n : ℝ))) ^ 20 := by
      calc
        (2 : ℝ) ^ 20 * ((d : ℝ) * (n : ℝ)) ^ 4 ≤ (2 : ℝ) ^ 20 * ((d : ℝ) * (n : ℝ)) ^ 20 := by
          have hx4x20 : ((d : ℝ) * (n : ℝ)) ^ 4 ≤ ((d : ℝ) * (n : ℝ)) ^ 20 := by
            refine pow_le_pow_right₀ hx ?_
            omega
          nlinarith
        _ = ((2 : ℝ) * ((d : ℝ) * (n : ℝ))) ^ 20 := by ring
    have hpos' : 0 < (2 : ℝ) * ((d : ℝ) * (n : ℝ)) := by nlinarith
    have h_log := Real.log_le_log (by positivity) h_pow
    rw [Real.log_pow, Nat.cast_ofNat] at h_log
    have h_ring : (2 : ℝ) * ((d : ℝ) * (n : ℝ)) = 2 * (d : ℝ) * (n : ℝ) := by ring
    rw [h_ring] at h_log
    exact h_log
  exact And.intro h_left h_right

theorem one_le_seven_X {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 ≤ 7 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos_d : 0 ≤ (d : ℝ) := by linarith
  have hpos_n : 0 ≤ (n : ℝ) := by linarith
  -- d^(3/2) ≥ 1
  have hA : 1 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := by
    apply Real.one_le_rpow hd'
    norm_num
  have hA_nonneg : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hpos_d _
  -- √n ≥ 1
  have hB : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact hn'
  have hB_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  -- log(2dn) ≥ log 2 > 0
  have h_log_lower : Real.log 2 ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) := by
    apply Real.log_le_log (by norm_num : 0 < (2 : ℝ))
    nlinarith
  have h_log_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have h_log_pos' : 0 ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) := le_trans (le_of_lt h_log_pos) h_log_lower
  -- log(2dn)^5 ≥ (log 2)^5
  have hC : (Real.log 2) ^ 5 ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) ^ 5 := by
    apply pow_le_pow_left₀ (le_of_lt h_log_pos) h_log_lower 5
  have hC_nonneg : 0 ≤ (Real.log 2) ^ 5 := pow_nonneg (le_of_lt h_log_pos) 5
  -- 7*(log 2)^5 ≥ 1 using Real.log_two_gt_d9
  have h_final : (1 : ℝ) ≤ 7 * (Real.log 2) ^ 5 := by
    have h_approx : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h_approx_pow : (0.6931471803 : ℝ) ^ 5 < (Real.log 2) ^ 5 := by
      apply pow_lt_pow_left₀ h_approx (by norm_num : 0 ≤ (0.6931471803 : ℝ)) (n := 5) (by norm_num : 5 ≠ 0)
    have h_norm : (1 : ℝ) ≤ 7 * (0.6931471803 : ℝ) ^ 5 := by norm_num
    linarith
  -- assemble: 1 ≤ 7*(log 2)^5 ≤ 7*(A*B*C)
  have h_prod : (1 : ℝ) * (1 : ℝ) * (Real.log 2) ^ 5 ≤
      (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (n : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) ^ 5 := by
    have h_AB : (1 : ℝ) * (1 : ℝ) ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
      exact mul_le_mul hA hB (by norm_num) hA_nonneg
    have h_nonneg_AB : 0 ≤ (1 : ℝ) * (1 : ℝ) := by norm_num
    exact mul_le_mul h_AB hC hC_nonneg (mul_nonneg hA_nonneg hB_nonneg)
  have h_nonneg_prod : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (n : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) ^ 5 := by
    apply mul_nonneg (mul_nonneg hA_nonneg hB_nonneg)
    exact pow_nonneg h_log_pos' 5
  calc
    (1 : ℝ) ≤ 7 * (Real.log 2) ^ 5 := h_final
    _ ≤ 7 * ((d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (n : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) ^ 5) := by
      nlinarith

theorem thr_add_one_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    thrBL d n + 1 ≤ 10 ^ 29 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 := by
  set X := (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 with hX
  set Λ := Real.log (2 * d * n / deltaBL d n) with hΛ
  rcases log_ratio_le hd hn with ⟨hΛ_nonneg, hΛ_le⟩
  have h_log_nonneg : 0 ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact mod_cast hd
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact mod_cast hn
    have hpos : (1 : ℝ) ≤ 2 * (d : ℝ) * (n : ℝ) := by nlinarith
    exact Real.log_nonneg hpos
  have hX_nonneg : 0 ≤ X := by
    rw [hX]
    have hd_nonneg : 0 ≤ (d : ℝ) := by exact mod_cast (Nat.zero_le d)
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact mod_cast (Nat.zero_le n)
    positivity
  have h_pow : Λ ^ 5 ≤ (20 * Real.log (2 * (d : ℝ) * (n : ℝ))) ^ 5 :=
    pow_le_pow_left₀ hΛ_nonneg hΛ_le 5
  have h_thrBL_le : thrBL d n ≤ ((10 : ℝ) ^ 22 * (20 : ℝ) ^ 5) * X := by
    dsimp [thrBL]
    calc
      10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Λ ^ 5
          ≤ 10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * ((20 * Real.log (2 * d * n)) ^ 5) := by
        gcongr
      _ = ((10 : ℝ) ^ 22 * (20 : ℝ) ^ 5) * X := by
        dsimp [X]
        ring
  have h_sum : thrBL d n + 1 ≤ (((10 : ℝ) ^ 22 * (20 : ℝ) ^ 5) + 7) * X := by
    have h_one : (1 : ℝ) ≤ 7 * X := one_le_seven_X hd hn
    nlinarith
  have h_final : (((10 : ℝ) ^ 22 * (20 : ℝ) ^ 5) + 7) * X ≤ 10 ^ 29 * X := by
    have h_coeff : ((10 : ℝ) ^ 22 * (20 : ℝ) ^ 5) + 7 ≤ (10 : ℝ) ^ 29 := by
      norm_num
    nlinarith
  nlinarith

/-- The arithmetic of the trivial bound at `ε > 1/4`. -/
theorem quarter_bound (TR : Df2Trivial) (d n L Λ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hL0 : 0 < L)
    (hLΛ : L ≤ 900 * Λ) (h : 1 / 4 < 20 * 725 * (d * Real.sqrt d) * L ^ 5 / Real.sqrt n) :
    n ≤ 10 ^ 22 * d ^ (3 / 2 : ℝ) * Real.sqrt n * Λ ^ 5 := by
  have hd_nonneg : 0 ≤ d := by linarith
  have hn_nonneg : 0 ≤ n := by linarith
  have hs_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hL_nonneg : 0 ≤ L := by linarith
  have hΛ_nonneg : 0 ≤ Λ := by
    have hΛ_pos : 0 < Λ := by
      have : 0 < 900 * Λ := by linarith
      exact pos_of_mul_pos_right this (by norm_num : 0 ≤ (900 : ℝ))
    exact le_of_lt hΛ_pos
  -- from h: 1/4 < 20*725 * d * √d * L^5 / √n = 14500 * d * √d * L^5 / √n
  -- multiply by √n > 0
  have h_simp : (20 : ℝ) * 725 = (14500 : ℝ) := by norm_num
  have h1' : (1 / 4 : ℝ) * Real.sqrt n < 14500 * d * Real.sqrt d * L ^ 5 := by
    -- rewrite h using the simplification
    have h' := h
    simpa [h_simp, mul_assoc] using (lt_div_iff₀ hs_pos).mp h
  -- multiply by 4: √n < 58000 * d * √d * L^5
  have h1 : Real.sqrt n < 58000 * d * Real.sqrt d * L ^ 5 := by
    linarith
  -- square both sides (all quantities nonnegative)
  have h_rhs_nonneg : 0 ≤ 58000 * d * Real.sqrt d * L ^ 5 := by
    positivity
  have h_sqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h2 : n < (58000 * d * Real.sqrt d * L ^ 5) ^ 2 := by
    have hsq : (Real.sqrt n) ^ 2 < (58000 * d * Real.sqrt d * L ^ 5) ^ 2 := by
      exact ((sq_lt_sq₀ h_sqrt_nonneg h_rhs_nonneg).mpr h1)
    calc
      n = (Real.sqrt n) ^ 2 := by rw [Real.sq_sqrt hn_nonneg]
      _ < (58000 * d * Real.sqrt d * L ^ 5) ^ 2 := hsq
  -- rewrite RHS: (58000 * d * √d * L^5)^2 = 4 * 29000^2 * d^3 * L^10
  have hbound : n < 4 * ((29000 : ℝ) ^ 2) * d ^ 3 * L ^ 10 := by
    calc
      n < (58000 * d * Real.sqrt d * L ^ 5) ^ 2 := h2
      _ = (58000 : ℝ) ^ 2 * d ^ 2 * (Real.sqrt d) ^ 2 * (L ^ 5) ^ 2 := by ring
      _ = (58000 : ℝ) ^ 2 * d ^ 2 * d * (L ^ 5) ^ 2 := by rw [Real.sq_sqrt hd_nonneg]
      _ = (58000 : ℝ) ^ 2 * d ^ 3 * L ^ 10 := by ring
      _ = 4 * ((29000 : ℝ) ^ 2) * d ^ 3 * L ^ 10 := by norm_num
  -- apply Df2Trivial with Ceps = 29000
  have hTR := TR d n (29000 : ℝ) L hd hn (by norm_num : 0 < (29000 : ℝ)) hL0 hbound
  -- hTR: n ≤ 2 * 29000 * d ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n
  have h3 : n ≤ 58000 * d ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n := by
    simpa [show (2 : ℝ) * (29000 : ℝ) = (58000 : ℝ) by norm_num] using hTR
  -- L^5 ≤ (900 * Λ)^5
  have hL_pow : L ^ 5 ≤ (900 * Λ) ^ 5 := by
    gcongr
  have h_sqrt_nonneg' : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_coeff_nonneg : 0 ≤ 58000 * d ^ ((3 : ℝ) / 2) := by
    positivity
  calc
    n ≤ 58000 * d ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n := h3
    _ ≤ 58000 * d ^ ((3 : ℝ) / 2) * (900 * Λ) ^ 5 * Real.sqrt n := by
      -- (A * L^5) * √n ≤ (A * (900*Λ)^5) * √n
      -- where A = 58000 * d^(3/2) ≥ 0
      -- First: A * L^5 ≤ A * (900*Λ)^5
      have h_mul : 58000 * d ^ ((3 : ℝ) / 2) * L ^ 5 ≤ 58000 * d ^ ((3 : ℝ) / 2) * (900 * Λ) ^ 5 := by
        exact mul_le_mul_of_nonneg_left hL_pow h_coeff_nonneg
      -- Then multiply both sides by √n ≥ 0
      exact mul_le_mul_of_nonneg_right h_mul h_sqrt_nonneg'
    _ = 58000 * (900 : ℝ) ^ 5 * (d ^ ((3 : ℝ) / 2) * Real.sqrt n * Λ ^ 5) := by ring
    _ ≤ (10 : ℝ) ^ 22 * (d ^ ((3 : ℝ) / 2) * Real.sqrt n * Λ ^ 5) := by
      gcongr
      norm_num
    _ = (10 : ℝ) ^ 22 * d ^ (3 / 2 : ℝ) * Real.sqrt n * Λ ^ 5 := by ring

/-- The arithmetic of `n δ_ref ≤ 1/2`. -/
theorem deltaRef_arith (n δ δ1 : ℝ) (hn : 1 ≤ n) (hδ1 : 0 < δ1) (hle : δ1 ≤ δ / 3) (hnδ : n * δ ≤ 2⁻¹ ^ 19) :
    n * (n * (149 / 168 * (4 * δ1 / (5 * n))) + 4 * δ1 / (5 * n) / 7) ≤ 1 / 2 := by
  have hnpos : 0 < n := by linarith
  have hδ1_nonneg : 0 ≤ δ1 := by linarith
  have h_simplify : n * (n * (149 / 168 * (4 * δ1 / (5 * n))) + 4 * δ1 / (5 * n) / 7) = (596/840) * n * δ1 + (4/35) * δ1 := by
    field_simp [hnpos.ne.symm]
    ring
  rw [h_simplify]
  have htemp : n * δ1 ≤ (2⁻¹ ^ 19) / 3 := by
    have h1 : n * δ1 ≤ n * (δ / 3) := by
      nlinarith
    have h2 : n * (δ / 3) ≤ (2⁻¹ ^ 19) / 3 := by
      nlinarith
    nlinarith
  nlinarith

/-- The budget of one seed: `δpos + δ_ref + δbits + n (κ0 + κ1) ≤ 1/n`. -/
theorem budget_le (n a r b c : ℝ) (hn : 1 ≤ n) (ha : n * a ≤ 1 / 4) (hr : n * r ≤ 1 / 2)
    (hb : n * (b + n * c) ≤ 1 / 4) : a + r + b + n * c ≤ 1 / n := by
  have hnpos : 0 < n := by linarith
  apply (le_div_iff₀ hnpos).mpr
  calc
    (a + r + b + n * c) * n = n * a + n * r + n * (b + n * c) := by ring
    _ ≤ 1/4 + 1/2 + 1/4 := by nlinarith
    _ = 1 := by norm_num

/-- A set of a product with every section of measure at most `ε` has measure at most `ε`. -/
theorem prod_le_of_sections {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω] (ρ : Measure Θ)
    [IsProbabilityMeasure ρ] (μ : Measure Ω) [SFinite μ] {S : Set (Θ × Ω)} (hS : MeasurableSet S) {ε : ℝ≥0∞}
    (h : ∀ θ, μ (Prod.mk θ ⁻¹' S) ≤ ε) : (ρ.prod μ) S ≤ ε := by
  calc
    (ρ.prod μ) S = ∫⁻ θ, μ (Prod.mk θ ⁻¹' S) ∂ρ := by
      rw [Measure.prod_apply hS]
    _ ≤ ∫⁻ θ, ε ∂ρ := lintegral_mono h
    _ = ε * ρ Set.univ := by rw [lintegral_const]
    _ = ε * 1 := by rw [measure_univ]
    _ = ε := by simp

/-- The regret reads the losses and the points of the rounds `t < n` only. -/
theorem regretPts_congr {K : Set (E d)} {n : ℕ} {f f' : ℕ → E d → ℝ} {x x' : ℕ → E d}
    (hf : ∀ t < n, f t = f' t) (hx : ∀ t < n, x t = x' t) : regretPts K f x n = regretPts K f' x' n := by
  unfold regretPts
  have hsum : (∑ t ∈ Finset.range n, f t (x t)) = (∑ t ∈ Finset.range n, f' t (x' t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [hf t ht, hx t ht]
  have hfun : (fun y => ∑ t ∈ Finset.range n, f t y) = (fun y => ∑ t ∈ Finset.range n, f' t y) := by
    funext y
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    rw [hf t ht]
  rw [hsum, hfun]

/-! ## The constants of D0 at BL's confidence -/

theorem n_le_thr {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h : 1 / 4 < (df2oPar d n (deltaBL d n)).eps) :
    (n : ℝ) ≤ thrBL d n := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ0 := deltaBL_pos hd hn
  have hδ1 := deltaBL_lt_one hd hn
  obtain ⟨-, hle⟩ := log_inv_de_le d n (deltaBL d n) hd1 hn1 hδ0 hδ1
  set L := (df2oPar d n (deltaBL d n)).Le with hL
  have hLdef : L = 36 * Real.log (1 / (4 * min (deltaBL d n / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) /
      (5 * n))) := by
    rw [hL]; simp only [df2oPar, df2C0]
  have hpos := (log_inv_de_le d n (deltaBL d n) hd1 hn1 hδ0 hδ1).1
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hLΛ : L ≤ 900 * Real.log (2 * d * n / deltaBL d n) := by rw [hLdef]; linarith
  have heps : (df2oPar d n (deltaBL d n)).eps = 20 * 725 * (d * Real.sqrt d) * L ^ 5 / Real.sqrt n := by
    rw [hL]; simp only [df2oPar, df2oClam]
  rw [heps] at h
  exact quarter_bound df2Trivial_holds d n L _ hd1 hn1 hL0 hLΛ h

theorem bReg_le_thr {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n) :
    bReg d n (deltaBL d n) + 1 ≤ thrBL d n :=
  comp_thresh (df2oPar d n (deltaBL d n)) d n (deltaBL d n)
    (rowHyp_of d n (deltaBL d n) hd hn (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) (hc.trans (by norm_num)))
    (deltaBL_pos hd hn) (deltaBL_lt_one hd hn) rfl rfl

theorem n_deltaRef_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : (n : ℝ) * deltaRef d n (deltaBL d n) ≤ 1 / 2 :=
  deltaRef_arith n (deltaBL d n) (df2oPar d n (deltaBL d n)).δ1 (by exact_mod_cast hn)
    (par_δ1_pos d n _ hd hn (deltaBL_pos hd hn)) (par_δ1_le d n _) (n_mul_deltaBL_le hd hn)

/-! ## The runs -/

open Classical in
/-- The rational point played in round `t` (`0` if that round never comes). -/
noncomputable def ptsBit (P : List Instr) (g : GameBit d) (s0 : State d) (t : ℕ) : Fin d → ℚ :=
  if h : ∃ k, t < (runBit P g s0 k).rounds then (runBit P g s0 (Nat.find h)).pts t else 0

/-- The points played are rational points. -/
theorem playedBit_eq (P : List Instr) (g : GameBit d) (s0 : State d) :
    playedBit P g s0 = fun t => toE (ptsBit P g s0 t) := by
  funext t
  unfold playedBit ptsBit
  split_ifs with h
  · rfl
  · ext i; simp [toE]

/-- Against an admissible strategy the losses of the rounds `t < n` of every run are admissible. -/
theorem adm_played {K : Set (E d)} {n : ℕ} {σ : Strategy d} (hσ : AdmStrat K n σ) (P : List Instr)
    (cs : ℕ → Bool) (s0 : State d) {t : ℕ} (ht : t < n) : AdmLoss K (lossAd σ 0 (playedBit P ⟨σ, cs⟩ s0) t) := by
  rw [playedBit_eq]
  exact hσ t ht _

/-- The regret of a run that plays in `K` against an admissible strategy is at most `n`. -/
theorem regBit_le {P : List Instr} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {σ : Strategy d}
    (hσ : AdmStrat (polytope A b) n σ) (cs : ℕ → Bool)
    (hK : ∀ t < n, playedBit P ⟨σ, cs⟩ (initBit d n m A b) t ∈ polytope A b) : regBit P d n m A b σ cs ≤ n :=
  RealRAM.regretPts_le_of_mem (fun _ ht => adm_played hσ P cs _ ht) hK

/-! ## The transfer to the coins -/

/-- The transfer to the coins under (W0), with the losses and the plays of the rounds `t < n` only. -/
theorem coins_eq {n : ℕ} {K : Set (E d)} (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν] (B : Run d n K)
    (β : (ℕ → ℝ) → ℕ → Bool) (hβ : W0Law β) (lo : (ℕ → Bool) → ℕ → E d → ℝ) (pl : (ℕ → Bool) → ℕ → E d)
    (hlo : ∀ (ω : WΩ) (t : ℕ), t < n → B.loss ω t = lo (β ω.1) t)
    (hpl : ∀ (ω : WΩ) (t : ℕ), t < n → B.play t ω = pl (β ω.1) t) (c : ℝ)
    (hS : MeasurableSet {cs | c < regretPts K (lo cs) (pl cs) n}) :
    coinStream {cs | c < regretPts K (lo cs) (pl cs) n} =
      μs ν {ω | c < regretPts K (B.loss ω) (fun t => B.play t ω) n} := by
  have hset : {ω : WΩ | c < regretPts K (B.loss ω) (fun t => B.play t ω) n} =
      (β ⁻¹' {cs | c < regretPts K (lo cs) (pl cs) n}) ×ˢ Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_preimage, Set.mem_univ, and_true]
    rw [regretPts_congr (hlo ω) (hpl ω)]
  rw [hset, Measure.prod_prod, measure_univ, mul_one, ← hβ.2, Measure.map_apply hβ.1 hS]

/-! ## One seed -/

section Seed

variable {D : BLInst} {C' : ℝ} {k : ℕ} {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}

/-- In the case `RunCase`, at one seed: the bad event of the coins has probability at most `1/n` (SHADOW at
`dirac 0`, moved to the coins). -/
theorem section_run (h : AsmHyp D C' k) (hI : InputOK d n m M A b) (hc : RunCase d n) (σ : Strategy d)
    (hσ : AdmStrat (polytope A b) n σ) (hmeas : Measurable fun cs => regBit D.P d n m A b σ cs) :
    coinStream {cs | thrBL d n < regBit D.P d n m A b σ cs} ≤ ENNReal.ofReal (1 / n) := by
  have hR := h.run d n m M A b hI hc σ hσ
  obtain ⟨δpos, hδpos, hnpos, hpos⟩ := posOK_of_inst h.posInst d n m M A b hI hc σ hσ
  obtain ⟨δbits, κ0, κ1, hδb, hκ0, hκ1, hnb, hbits, heng⟩ := hR.engine
  have hreg : Regime d n (deltaBL d n) :=
    ⟨hI.hd, hI.hn, deltaBL_pos hI.hd hI.hn, deltaBL_lt_one hI.hd hI.hn, hc.trans (by norm_num)⟩
  have hlaw : CoupLaw (D.run d n m A b σ).Coup := hR.coup ▸ coupLaw_coupMax
  have htv : CoupTV (D.run d n m A b σ).Coup := hR.coup ▸ coupTV_coupMax
  have hS := shadowProp_holds d n (deltaBL d n) (polytope A b) (Measure.dirac 0) (D.run d n m A b σ) δpos δbits κ0
    κ1 hreg (Conj1Poly.isClosed_polytope A b) (Conj1Poly.convex_polytope A b)
    RealRAM.Conj1PolySanity.noiseOK_dirac hpos hlaw htv hR.meas hbits heng hδpos hδb hκ0 hκ1
  have heq := coins_eq (Measure.dirac 0) (D.run d n m A b σ) (D.β d n) (w0Law_blInst D d n)
    (fun cs => lossAd σ 0 (playedBit D.P ⟨σ, cs⟩ (initBit d n m A b)))
    (fun cs => playedBit D.P ⟨σ, cs⟩ (initBit d n m A b)) hR.loss hR.play (bReg d n (deltaBL d n) + 1)
    (measurableSet_lt measurable_const hmeas)
  have hsub : {cs | thrBL d n < regBit D.P d n m A b σ cs} ⊆
      {cs | bReg d n (deltaBL d n) + 1 < regBit D.P d n m A b σ cs} := fun cs hcs =>
    lt_of_le_of_lt (bReg_le_thr hI.hd hI.hn hc) hcs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hI.hn
  calc coinStream {cs | thrBL d n < regBit D.P d n m A b σ cs}
      ≤ coinStream {cs | bReg d n (deltaBL d n) + 1 < regBit D.P d n m A b σ cs} := measure_mono hsub
    _ = μs (Measure.dirac 0) {ω | bReg d n (deltaBL d n) + 1 < regretPts (polytope A b)
          ((D.run d n m A b σ).loss ω) (fun t => (D.run d n m A b σ).play t ω) n} := heq
    _ ≤ ENNReal.ofReal (δpos + deltaRef d n (deltaBL d n) + δbits + n * (κ0 + κ1)) := hS
    _ ≤ ENNReal.ofReal (1 / n) :=
      ENNReal.ofReal_le_ofReal (budget_le n δpos _ δbits _ hn1 hnpos (n_deltaRef_le hI.hd hI.hn) hnb)

/-- Off the case `RunCase`, at one seed: the bad event is empty. -/
theorem section_off (h : AsmHyp D C' k) (hI : InputOK d n m M A b) (hc : ¬ RunCase d n) (σ : Strategy d)
    (hσ : AdmStrat (polytope A b) n σ) :
    coinStream {cs | thrBL d n < regBit D.P d n m A b σ cs} ≤ ENNReal.ofReal (1 / n) := by
  have hn_le : (n : ℝ) ≤ thrBL d n := n_le_thr hI.hd hI.hn (not_le.1 hc)
  have he : {cs | thrBL d n < regBit D.P d n m A b σ cs} = ∅ := by
    ext cs
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (regBit_le hσ cs (h.mach d n m M A b hI σ hσ cs).2.2).trans hn_le
  rw [he, measure_empty]
  exact zero_le

theorem section_le (h : AsmHyp D C' k) (hI : InputOK d n m M A b) (σ : Strategy d)
    (hσ : AdmStrat (polytope A b) n σ) (hmeas : Measurable fun cs => regBit D.P d n m A b σ cs) :
    coinStream {cs | thrBL d n < regBit D.P d n m A b σ cs} ≤ ENNReal.ofReal (1 / n) := by
  by_cases hc : RunCase d n
  · exact section_run h hI hc σ hσ hmeas
  · exact section_off h hI hc σ hσ

end Seed

/-! ## The assembly -/

/-- `TheoremConj1UpperBit` from the bricks, with `C = 10^29` and the program, `C'` and `k` of the bricks. -/
theorem theoremConj1UpperBit_of (D : BLInst) (C' : ℝ) (k : ℕ) (h : AsmHyp D C' k) : TheoremConj1UpperBit := by
  refine ⟨D.P, 10 ^ 29, C', k, ?_⟩
  intro d hd n hn m M A b hH hball hdiam Θ _ ρ hρ σ hσ
  have hI : InputOK d n m M A b := ⟨hd, hn, hH, hball, hdiam⟩
  have hadm : ∀ θ, AdmStrat (polytope A b) n (σ θ) := fun θ t ht q => (hσ t ht q).1 θ
  refine ⟨fun θ cs => h.mach d n m M A b hI (σ θ) (hadm θ) cs, ?_⟩
  have hmeas := regMeasOK D.P d n m M A b hI Θ σ hσ fun θ cs => (h.mach d n m M A b hI (σ θ) (hadm θ) cs).2.2
  have hbad : (ρ.prod coinStream) {ω | thrBL d n < regBit D.P d n m A b (σ ω.1) ω.2} ≤ ENNReal.ofReal (1 / n) :=
    prod_le_of_sections ρ coinStream (measurableSet_lt measurable_const hmeas) fun θ =>
      section_le h hI (σ θ) (hadm θ) (hmeas.comp measurable_prodMk_left)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hthr : 0 ≤ thrBL d n := by
    unfold thrBL
    have := (log_ratio_le hd hn).1
    positivity
  obtain ⟨R, hRm, hRle, hRint⟩ := RealRAM.exists_majorant_of_bad (ρ.prod coinStream)
    (fun ω => regBit D.P d n m A b (σ ω.1) ω.2) hthr le_rfl (δ := 1 / n) (n := n)
    (by rw [mul_one_div_cancel (by positivity)]) (fun ω => regBit_le (hadm ω.1) ω.2
      (h.mach d n m M A b hI (σ ω.1) (hadm ω.1) ω.2).2.2) hbad
  exact ⟨R, hRm, hRle, hRint.trans (ENNReal.ofReal_le_ofReal (thr_add_one_le hd hn))⟩

end AdversarialBco.Bit.Asm
