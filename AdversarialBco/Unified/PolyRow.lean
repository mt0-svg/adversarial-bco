/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyMap

@[expose] public section

/-!
# UNI-POLY: the arithmetic of the membership test `ROWMEM`

* `rowSQ nm dn Y j`: the pair `(S, Q)` after `j` columns of a row: `S / Q = Σ_{k<j} (nm k / dn k) Y (1 + k)`,
  `Q = Π_{k<j} dn k`.
* `rowOK_iff`: the test `S dn_d ≤ nm_d Q Y_0` of the machine is the inequality of the row at the point
  `Y (1 + k) / Y 0`.
* `rowSQ_bound`: `|S| ≤ j M^j B`, `|Q| ≤ M^j`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM

/-- The pair `(S, Q)` after `j` columns. -/
def rowSQ (nm dn Y : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | j + 1 => ((rowSQ nm dn Y j).1 * dn j + nm j * Y (1 + j) * (rowSQ nm dn Y j).2, (rowSQ nm dn Y j).2 * dn j)

variable {nm dn Y : ℕ → ℤ}

theorem rowSQ_pos {j : ℕ} (hdn : ∀ k < j, 0 < dn k) : 0 < (rowSQ nm dn Y j).2 := by
  induction j with
  | zero => simp [rowSQ]
  | succ j ih => simp only [rowSQ]; exact mul_pos (ih fun k hk => hdn k (by omega)) (hdn j (by omega))

theorem rowSQ_eq {j : ℕ} (hdn : ∀ k < j, 0 < dn k) :
    ((rowSQ nm dn Y j).1 : ℚ) =
      (rowSQ nm dn Y j).2 * ∑ k ∈ Finset.range j, ((nm k : ℚ) / dn k) * (Y (1 + k) : ℚ) := by
  induction j with
  | zero => simp [rowSQ]
  | succ j ih =>
    have hj : (dn j : ℚ) ≠ 0 := by exact_mod_cast (hdn j (by omega)).ne'
    simp only [rowSQ, Finset.sum_range_succ]
    push_cast
    rw [ih fun k hk => hdn k (by omega)]
    field_simp
    try ring

/-- The machine's test of a row is the row's inequality at the point `Y (1 + k) / Y 0`. -/
theorem rowOK_iff {d : ℕ} (hY0 : 0 < Y 0) (hdn : ∀ k ≤ d, 0 < dn k) :
    (rowSQ nm dn Y d).1 * dn d ≤ nm d * (rowSQ nm dn Y d).2 * Y 0 ↔
      ∑ k ∈ Finset.range d, ((nm k : ℚ) / dn k) * ((Y (1 + k) : ℚ) / Y 0) ≤ (nm d : ℚ) / dn d := by
  have hQ := rowSQ_pos (nm := nm) (Y := Y) (j := d) fun k hk => hdn k (by omega)
  have hS := rowSQ_eq (nm := nm) (Y := Y) (j := d) fun k hk => hdn k (by omega)
  have hd : (0 : ℚ) < dn d := by exact_mod_cast hdn d le_rfl
  have hY : (0 : ℚ) < Y 0 := by exact_mod_cast hY0
  have hQ' : (0 : ℚ) < (rowSQ nm dn Y d).2 := by exact_mod_cast hQ
  have e : ∑ k ∈ Finset.range d, ((nm k : ℚ) / dn k) * ((Y (1 + k) : ℚ) / Y 0) =
      (∑ k ∈ Finset.range d, ((nm k : ℚ) / dn k) * (Y (1 + k) : ℚ)) / Y 0 := by
    rw [Finset.sum_div]; congr 1; ext k; ring
  rw [e, div_le_div_iff₀ hY hd, ← @Int.cast_le ℚ]
  push_cast
  rw [hS, show ((rowSQ nm dn Y d).2 : ℚ) * (∑ k ∈ Finset.range d, (nm k : ℚ) / dn k * (Y (1 + k) : ℚ)) * dn d =
    ((rowSQ nm dn Y d).2 : ℚ) * ((∑ k ∈ Finset.range d, (nm k : ℚ) / dn k * (Y (1 + k) : ℚ)) * dn d) by ring,
    show (nm d : ℚ) * ((rowSQ nm dn Y d).2 : ℚ) * (Y 0 : ℚ) = ((rowSQ nm dn Y d).2 : ℚ) * ((nm d : ℚ) * Y 0) by ring,
    mul_le_mul_iff_of_pos_left hQ']

/-- The sizes along a row. -/
theorem rowSQ_bound {M B : ℤ} (hM1 : 1 ≤ M) (hB : 0 ≤ B) {j : ℕ}
    (hM : ∀ k < j, |nm k| ≤ M ∧ 0 < dn k ∧ dn k ≤ M) (hY : ∀ k < j, |Y (1 + k)| ≤ B) :
    |(rowSQ nm dn Y j).1| ≤ j * M ^ j * B ∧ 0 < (rowSQ nm dn Y j).2 ∧ (rowSQ nm dn Y j).2 ≤ M ^ j := by
  induction j with
  | zero => simp [rowSQ]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k hk => hM k (by omega)) (fun k hk => hY k (by omega))
    obtain ⟨n1, d1, d2⟩ := hM j (by omega)
    have y1 := hY j (by omega)
    have hMj : (0 : ℤ) ≤ M ^ j := by positivity
    simp only [rowSQ]
    refine ⟨?_, mul_pos h2 d1, ?_⟩
    · calc |(rowSQ nm dn Y j).1 * dn j + nm j * Y (1 + j) * (rowSQ nm dn Y j).2|
          ≤ |(rowSQ nm dn Y j).1| * |dn j| + |nm j| * |Y (1 + j)| * |(rowSQ nm dn Y j).2| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul, abs_mul]
        _ ≤ (j * M ^ j * B) * M + M * B * M ^ j := by
            rw [abs_of_pos d1, abs_of_pos h2]
            gcongr
        _ = ((j + 1 : ℕ) : ℤ) * M ^ (j + 1) * B := by push_cast; ring
    · calc (rowSQ nm dn Y j).2 * dn j ≤ M ^ j * M := by gcongr
        _ = M ^ (j + 1) := by ring

end AdversarialBco.UniPoly
