/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSplit
public import AdversarialBco.Bit.Transfer.XBLSetupInv
public import AdversarialBco.Bit.Transfer.XTrans
public import AdversarialBco.Bit.ApQ.Ell
public import AdversarialBco.Bit.Transfer.XBLMagLem

@[expose] public section

/-!
# The magnitudes of BL's state, part B: the draws

The draws of BM-INT are at most `B` (`draw_abs`, from `gOut_abs` and `blkUW_lt2`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ AdversarialBco.Bit.Asm Matrix
open AdversarialBco.BitRAM (toE)

variable {d : ℕ}

/-! ## The draws -/

theorem gOut_abs (B U W : ℕ) (hB : 8 ≤ B) (hU : U < 2 ^ B) (hW : W < 2 ^ B) :
    |(gOut B (U, W)).1| ≤ B ∧ |(gOut B (U, W)).2| ≤ B := by
  obtain ⟨-, -, h1, h2⟩ := gsSpec_err B U W hB hU hW
  have hs := sqrt_two_mul_le B (by omega)
  have e : gOut B (U, W) = (((gsSpec B U W).1 : ℚ) / 2 ^ (2 * gsm_prec B),
      ((gsSpec B U W).2 : ℚ) / 2 ^ (2 * gsm_prec B)) := rfl
  rw [e]
  generalize gsSpec B U W = g at h1 h2
  generalize 2 * gsm_prec B = q at h1 h2
  have key : ∀ z : ℤ, |(z : ℝ) / 2 ^ q| ≤ Real.sqrt (2 * B) → |(z : ℚ) / 2 ^ q| ≤ B := fun z hz => by
    have h : ((|(z : ℚ) / 2 ^ q| : ℚ) : ℝ) ≤ ((B : ℚ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h
  exact ⟨key _ h1, key _ h2⟩

theorem blkUW_lt2 (cs : ℕ → Bool) (K0 B d t j : ℕ) :
    (blkUW cs K0 B d t j).1 < 2 ^ B ∧ (blkUW cs K0 B d t j).2 < 2 ^ B := by
  unfold blkUW
  obtain ⟨a0, a1⟩ := readCoins_bounds cs (Sched.blkStart d K0 B t j) B
  obtain ⟨b0, b1⟩ := readCoins_bounds cs (Sched.blkStart d K0 B t j + B) B
  have e1 := Int.toNat_of_nonneg a0
  have e2 := Int.toNat_of_nonneg b0
  constructor
  · have : (((BitRAM.readCoins cs (Sched.blkStart d K0 B t j) B).toNat : ℕ) : ℤ) < 2 ^ B := by rw [e1]; exact a1
    exact_mod_cast this
  · have : (((BitRAM.readCoins cs (Sched.blkStart d K0 B t j + B) B).toNat : ℕ) : ℤ) < 2 ^ B := by rw [e2]; exact b1
    exact_mod_cast this

/-- **The draws are at most `B`.** -/
theorem draw_abs (cs : ℕ → Bool) (K0 B t : ℕ) (hB : 8 ≤ B) :
    (∀ i, |(draw cs K0 B d t).1 i| ≤ B) ∧ |(draw cs K0 B d t).2| ≤ B := by
  have hg : ∀ j, |(gOut B (blkUW cs K0 B d t j)).1| ≤ B ∧ |(gOut B (blkUW cs K0 B d t j)).2| ≤ B := fun j => by
    obtain ⟨h1, h2⟩ := blkUW_lt2 cs K0 B d t j
    exact gOut_abs B _ _ hB h1 h2
  refine ⟨fun i => ?_, ?_⟩
  · unfold draw
    dsimp only
    split_ifs
    · exact (hg _).1
    · exact (hg _).2
  · unfold draw
    dsimp only
    rw [abs_div, abs_two]
    have := (hg ((d + 1) / 2)).1
    have hB0 : (0 : ℚ) ≤ B := by positivity
    linarith

end AdversarialBco.Bit.Transfer.BLM
