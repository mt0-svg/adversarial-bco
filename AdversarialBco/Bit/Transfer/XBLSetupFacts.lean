/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-!
# BL's setup on the machine: facts of P5 and the epoch start

The test `1/2 < ε'` on the grid (`half_lt_up_iff`); the epoch start on the grid `2^{-p}` (`qn_smul_one`,
`onG_smul_one`, `onG_rnd_s`, `onG_zero`) and the diagonal cells of a matrix (`diag_iff`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP Matrix

theorem half_lt_up_iff (k : ℕ) (x : ℚ) :
    1 / 2 < up k x ↔ (2 : ℤ) ^ k < 2 * qn k (up k x) := by
  have h2pos : (0 : ℚ) < (2 : ℚ) ^ k := pow_pos (by norm_num) k
  have hqn_eq : qn k (up k x) = ⌈x * 2 ^ k⌉ := by
    dsimp [qn, up]
    have h : ((⌈x * 2 ^ k⌉ : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ k = (⌈x * 2 ^ k⌉ : ℚ) := by
      field_simp [pow_ne_zero k (by norm_num : (2 : ℚ) ≠ 0)]
    rw [h]
    exact Int.floor_intCast _
  have hup_eq : up k x = (qn k (up k x) : ℚ) / (2 : ℚ) ^ k := by
    calc
      up k x = (⌈x * 2 ^ k⌉ : ℚ) / (2 : ℚ) ^ k := rfl
      _ = (qn k (up k x) : ℚ) / (2 : ℚ) ^ k := by rw [hqn_eq]
  have h_equiv : (1 : ℚ) / 2 < (qn k (up k x) : ℚ) / ((2 : ℚ) ^ k) ↔ (2 : ℚ) ^ k < 2 * (qn k (up k x) : ℚ) := by
    field_simp [h2pos.ne.symm, show (2 : ℚ) ≠ 0 from by norm_num]
  have hleft : 1 / 2 < up k x ↔ 1 / 2 < (qn k (up k x) : ℚ) / ((2 : ℚ) ^ k) := by
    conv =>
      lhs
      rw [hup_eq]
  have hright : ((2 : ℚ) ^ k < 2 * (qn k (up k x) : ℚ)) ↔ ((2 : ℤ) ^ k < 2 * qn k (up k x)) := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  calc
    1 / 2 < up k x ↔ 1 / 2 < (qn k (up k x) : ℚ) / ((2 : ℚ) ^ k) := hleft
    _ ↔ (2 : ℚ) ^ k < 2 * (qn k (up k x) : ℚ) := h_equiv
    _ ↔ (2 : ℤ) ^ k < 2 * qn k (up k x) := hright

theorem qn_smul_one {d : ℕ} (k : ℕ) (a : ℚ) (i j : Fin d) :
    qn k ((a • (1 : Matrix (Fin d) (Fin d) ℚ)) i j) = if i = j then qn k a else 0 := by
  simp [Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp [qn]

theorem onG_smul_one {d : ℕ} (k : ℕ) (a : ℚ) (h : OnG k a) (i j : Fin d) :
    OnG k ((a • (1 : Matrix (Fin d) (Fin d) ℚ)) i j) := by
  simp [Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h_eq
  · exact h
  · unfold OnG qn
    simp

theorem onG_rnd_s (k : ℕ) (x : ℚ) : OnG k (rnd k x) := by
  unfold OnG qn rnd
  simp [Int.floor_intCast]

theorem onG_zero (k : ℕ) : OnG k 0 ∧ qn k 0 = 0 := by
  unfold OnG qn
  simp

theorem diag_iff {d : ℕ} (i j : Fin d) :
    (∃ k < d, d * (i : ℕ) + j = 0 + (d + 1) * k) ↔ i = j := by
  constructor
  · intro h
    rcases h with ⟨k, hk, h⟩
    have hmod := congrArg (fun x => x % d) h
    have hleft : (d * (i : ℕ) + (j : ℕ)) % d = (j : ℕ) := by
      calc
        (d * (i : ℕ) + (j : ℕ)) % d = (j : ℕ) % d := by simpa using Nat.mul_add_mod d (i : ℕ) (j : ℕ)
        _ = (j : ℕ) := Nat.mod_eq_of_lt j.2
    have hright : ((d + 1) * k) % d = (k : ℕ) := by
      calc
        ((d + 1) * k) % d = (d * k + k) % d := by ring
        _ = k % d := by simpa using Nat.mul_add_mod d k k
        _ = k := Nat.mod_eq_of_lt hk
    have hmod_simp : (j : ℕ) = (k : ℕ) := by
      simpa [hleft, hright] using hmod
    -- From h: d * i + j = 0 + (d+1)*k = d*k + k
    -- Using j = k, we get d*i + k = d*k + k, so d*i = d*k
    have h_eq_mul : d * (i : ℕ) = d * (k : ℕ) := by
      have htemp := h
      -- rewrite j as k in h
      simpa [hmod_simp, add_comm, add_left_comm, add_assoc, mul_add, add_mul] using htemp
    by_cases hd : d = 0
    · subst hd
      exact Fin.elim0 i
    · have hi_eq_k : (i : ℕ) = (k : ℕ) :=
        Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) h_eq_mul
      -- Now we have i = k (as ℕ) and j = k (as ℕ), so i = j
      have hi_eq_j : (i : ℕ) = (j : ℕ) := by
        calc
          (i : ℕ) = (k : ℕ) := hi_eq_k
          _ = (j : ℕ) := by symm; exact hmod_simp
      exact Fin.ext hi_eq_j
  · intro h
    subst h
    refine ⟨i, i.2, ?_⟩
    ring

theorem frMhat_le_M {d m M : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (hH : RealRAM.HeightLE A b M) (hM : 1 ≤ M) : RQ.frMhat A b ≤ M := by
  unfold RQ.frMhat
  apply max_le hM
  apply Finset.sup_le
  intro i hi
  have hiA := hH.1 i
  have hib := hH.2 i
  apply max_le
  · apply Finset.sup_le
    intro j hj
    have hijA := hiA j
    apply max_le
    · exact hijA.1
    · exact hijA.2
  · apply max_le
    · exact hib.1
    · exact hib.2

end AdversarialBco.Bit.Transfer.BLM
