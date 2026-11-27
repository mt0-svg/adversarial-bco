/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadM
public import AdversarialBco.Bit.Transfer.XBLHeadB
public import AdversarialBco.Bit.Transfer.XBLMag

@[expose] public section

/-!
# BL's round in mode `run` after R5: the bounds of the cells

`BLInv.sc_abs`, `BLInv.arr_abs`: a persistent slot or array cell holding an integer `z` has `|z| ≤ 2^E`; the index
bounds `idx_lt`, `idx1_lt` and `pow_two_le`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Facts -/

/-- A persistent slot holding the integer `z`: `|z| ≤ 2^E`. -/
theorem BLInv.sc_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {y : ℕ} (hy : y < nSP) {z : ℤ} (hz : σ.sc y = z) : |z| ≤ 2 ^ E := by
  obtain ⟨z', e', b'⟩ := h.bnd.1 y hy
  have : z = z' := by exact_mod_cast hz.symm.trans e'
  rw [this]; exact b'

/-- A persistent array cell holding the integer `z`: `|z| ≤ 2^E`. -/
theorem BLInv.arr_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {a k : ℕ} (ha : a < nAP) (hk : k < asz d) {z : ℤ} (hz : σ.arr a k = z) :
    |z| ≤ 2 ^ E := by
  obtain ⟨z', e', b'⟩ := h.bnd.2 a ha k hk
  have : z = z' := by exact_mod_cast hz.symm.trans e'
  rw [this]; exact b'

theorem idx_lt (i j : Fin d) : d * i + j < asz d := by
  unfold asz; have := i.2; have := j.2; nlinarith

theorem idx1_lt (j : Fin d) : (j : ℕ) < asz d := by
  unfold asz; have := j.2; nlinarith

theorem pow_two_le {p E : ℕ} (h : |((2 : ℤ) ^ p)| ≤ 2 ^ E) : p ≤ E := by
  rw [abs_of_pos (by positivity)] at h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 h

end AdversarialBco.Bit.Transfer.BLM
