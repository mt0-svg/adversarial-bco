/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRows
public import AdversarialBco.Bit.BLBasic
public import AdversarialBco.Bit.CoinSchedLaw
public import AdversarialBco.Conj1.RunAd
public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Bit.BLRecMeas

@[expose] public section

/-!
# Piece D: `RunOK` for the record `blRun`

`runOK_of`: `RunOK (blInst P R)` from the program link `BLLink P R`, (O3) on BL's calls `O3SpecQ R.ap`, the coin
locality `PosLocal R`, and pieces A (`BudA`), B (`BitsB`, `MeasDrawB`) and C (`PlayC`, `RoundC`) of Bit/BLRun.lean.

The fields of `RunSpec`: the coupling is `coupMax` by definition; the plays and losses of the record are those of the
program on the coins `β gs` (`BLLink`, with the history of the run read before round `t` known at `cσ d t`,
`lamR_eq` of Bit/BLEngine.lean); the bit clause from `BitsB` (`Z_n` is a null set's complement under `dirac 0`); the engine with
`δbits = 2^{-p-2}`, `κ0 = Bud.kap0`, `κ1 = 0` (`engine_of`, Bit/BLEngine.lean); (O4-M) (`blMeas_of`, Bit/BLRecMeas.lean).
-/

namespace AdversarialBco.Bit.BLP

open MeasureTheory
open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## The plays and the losses of the record -/

theorem blRun_play {P : List Instr} {R : Routines} (hL : BLLink P R) {d n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} (hI : InputOK d n m M A b) (hc : RunCase d n) {σ : Strategy d}
    (hσ : AdmStrat (polytope A b) n σ) (ω : WΩ) (t : ℕ) (ht : t < n) :
    (blRun R d n m A b σ).play t ω = playedBit P ⟨σ, betaR R d n ω.1⟩ (initBit d n m A b) t :=
  (hL d n m M A b hI hc σ hσ (betaR R d n ω.1) t ht).symm

theorem blRun_loss {P : List Instr} {R : Routines} (hL : BLLink P R) (hR : PosLocal R) {d n m M : ℕ}
    {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) (hc : RunCase d n) {σ : Strategy d}
    (hσ : AdmStrat (polytope A b) n σ) (ω : WΩ) (t : ℕ) (ht : t < n) :
    (blRun R d n m A b σ).loss ω t = lossAd σ 0 (playedBit P ⟨σ, betaR R d n ω.1⟩ (initBit d n m A b)) t := by
  show lossL (polytope A b) n σ t (lamR R d n m A b σ t ω) = _
  rw [lamR_eq R hR, lossL, ite_eq_left hσ]
  apply Conj1.lossAd_congr
  intro i hi
  rw [hL d n m M A b hI hc σ hσ (betaR R d n ω.1) i (hi.trans ht)]
  show toE ((traj R d n m A b σ (betaR R d n ω.1) t).2 i) = _
  rw [traj_hist R d n m A b σ _ t i hi]

/-! ## The bit clause -/

/-- The noisy worlds are null under `dirac 0`. -/
theorem zn_compl_null (n : ℕ) : μs (Measure.dirac 0) (Zn n)ᶜ = 0 := by
  have hS : MeasurableSet {e : ℕ → ℝ | ∃ t < n, e t ≠ 0} := by
    have : {e : ℕ → ℝ | ∃ t < n, e t ≠ 0} = ⋃ t ∈ Finset.range n, {e | e t ≠ 0} := by
      ext e; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun t _ => (measurableSet_eq_fun (measurable_pi_apply t)
      measurable_const).compl
  have hZ : (Zn n)ᶜ = Set.univ ×ˢ {e : ℕ → ℝ | ∃ t < n, e t ≠ 0} := by
    ext ω; simp [Zn]
  rw [hZ, Measure.prod_prod, Measure.dirac_apply' _ hS]
  simp

theorem blRun_bits {R : Routines} (hB : BitsB) {d n m : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n)
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d) :
    BitsHyp (Measure.dirac 0) (blRun R d n m A b σ) (Bud.dbits d n) := by
  show μs (Measure.dirac 0) (Ebits R d n ∩ Zn n)ᶜ ≤ _
  rw [Set.compl_inter]
  calc μs (Measure.dirac 0) ((Ebits R d n)ᶜ ∪ (Zn n)ᶜ)
      ≤ μs (Measure.dirac 0) (Ebits R d n)ᶜ + μs (Measure.dirac 0) (Zn n)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Bud.dbits d n) := by rw [zn_compl_null, add_zero]; exact hB R d n hd hn hc

/-! ## `RunOK` -/

/-- Piece D: `RunOK` for the instance `blInst P R`. -/
theorem runOK_of {P : List Instr} {R : Routines} (hL : BLLink P R) (hO3 : O3SpecQ R.ap) (hR : PosLocal R)
    (hA : BudA) (hB : BitsB) (hD : MeasDrawB) (hP : PlayC) (hC : RoundC) : RunOK (blInst P R) := by
  intro d n m M A b hI hc σ hσ
  have hbud := hA d n hI.hd hI.hn hc
  refine ⟨rfl, blMeas_of hR hD hI.hd hI.hn hc, ⟨Bud.dbits d n, Bud.kap0 d n, 0, ?_, hbud.kap0_nonneg, le_rfl, ?_,
    blRun_bits hB hI.hd hI.hn hc A b σ, engine_of hO3 hR hA hP hC hI hc hσ⟩,
    fun ω t ht => blRun_loss hL hR hI hc hσ ω t ht, fun ω t ht => blRun_play hL hI hc hσ ω t ht⟩
  · unfold Bud.dbits Bud.tp; positivity
  · simpa using hbud.budget

end AdversarialBco.Bit.BLP
