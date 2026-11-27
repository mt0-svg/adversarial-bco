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
public import AdversarialBco.Conj1Exp.Bound
public import AdversarialBco.Poly.Df2CompProof
public import AdversarialBco.Poly.Df2DetProof

@[expose] public section

/-!
# The assembly of the bit-model upper bound: the bricks and the bad event

`AsmHyp D C' k`, for a bit learner `D` (`BLInst`: its program, its prologue length `K0` and block length `B`, its run
record on the coupled world; its digit map is `Sched.beta` of Bit/CoinSched.lean, `BLInst.β`), is the conjunction of
the bricks, one named `Prop` each; `theoremConj1UpperBitHP_of_roundBL` (Conj1BitHP/Assembly.lean) gives them for BL:

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
bad event `{thrBL d n < Reg}` of `ρ ⊗ coinStream` has measure at most `1/n` (`section_le`), and the bad event too
(`prod_le_of_sections`, in `bad_le` of Conj1BitHP/Assembly.lean); there `exists_majorant_of_bad` gives a majorant
of `max (Reg, 0)` with mean at most `thrBL d n + 1`, which is at most `10^29 d^{3/2} n^{1/2} log^5 (2 d n)`
(`thr_add_one_le`).
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

/-- (W0) for BL's digit map: `Sched.w0Law_beta` with BL's block length, which is positive. -/
theorem w0Law_blInst (D : BLInst) (d n : ℕ) : W0Law (D.β d n) :=
  Sched.w0Law_beta d (D.K0 d n) (D.B d n) (D.B_pos d n)

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

end AdversarialBco.Bit.Asm
