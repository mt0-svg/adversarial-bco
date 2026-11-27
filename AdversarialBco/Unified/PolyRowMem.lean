/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyRow
public import AdversarialBco.Unified.PolyBlk
public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# UNI-POLY, part 8a: the answer of `ROWMEM` and the polytope

* `rowT`, `rowR`: the test of a row on the buffer, the answer after the rows `i < k`.
* `rowR_nrm`: on the normalised buffer, the answer is the membership of the point of `P` in the polytope.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM


variable {d : ℕ}

/-- The test of a row: `S dn_d ≤ nm_d Q Y_0`. -/
abbrev rowT (d : ℕ) (nm dn Y : ℕ → ℤ) : Prop := (rowSQ nm dn Y d).1 * dn d ≤ nm d * (rowSQ nm dn Y d).2 * Y 0

/-- The answer of `ROWMEM` after the rows `i < k`. -/
def rowR (d k : ℕ) (nm dn : ℕ → ℕ → ℤ) (Y : ℕ → ℤ) : ℤ :=
  if ∀ i < k, rowT d (nm i) (dn i) Y then 1 else 0

theorem rowR_succ {k : ℕ} {nm dn : ℕ → ℕ → ℤ} {Y : ℕ → ℤ} :
    rowR d (k + 1) nm dn Y = if rowT d (nm k) (dn k) Y then rowR d k nm dn Y else 0 := by
  unfold rowR
  by_cases hk : rowT d (nm k) (dn k) Y
  · rw [ite_eq_left hk]
    have : (∀ i < k + 1, rowT d (nm i) (dn i) Y) ↔ ∀ i < k, rowT d (nm i) (dn i) Y :=
      ⟨fun h i hi => h i (by omega), fun h i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h i hi
        · exact hk⟩
    by_cases h : ∀ i < k, rowT d (nm i) (dn i) Y
    · rw [ite_eq_left h, ite_eq_left (this.2 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.1 h'))]
  · rw [ite_eq_right hk, ite_eq_right]; intro h; exact hk (h k (by omega))

theorem rowR_zero {nm dn : ℕ → ℕ → ℤ} {Y : ℕ → ℤ} : rowR d 0 nm dn Y = 1 := by
  unfold rowR; rw [ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i))]

theorem rowR_cases {k : ℕ} {nm dn : ℕ → ℕ → ℤ} {Y : ℕ → ℤ} : rowR d k nm dn Y = 0 ∨ rowR d k nm dn Y = 1 := by
  unfold rowR; split_ifs <;> simp

/-- The buffer `nrm` has a positive entry `0`. -/
theorem nrm_zero_pos (y0 : ℤ) : 0 < nrm y0 y0 0 := by
  unfold nrm; split_ifs <;> omega

/-- The buffer `nrm` holds the same ratios as the point. -/
theorem nrm_ratio (y0 yj : ℤ) {j : ℤ} (hj : j ≠ 0) :
    (nrm y0 yj j : ℚ) / (nrm y0 y0 0 : ℚ) = (yj : ℚ) / y0 := by
  unfold nrm
  by_cases h0 : y0 = 0
  · simp [h0, hj]
  · by_cases hn : y0 < 0
    · simp only [h0, hn, ↓reduceIte, Int.cast_neg]; rw [neg_div_neg_eq]
    · simp only [h0, hn, ↓reduceIte]

open Classical in
/-- On the normalised buffer, the answer of `ROWMEM` is the membership of the point of `P` in the polytope. -/
theorem rowR_nrm {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {nm dn : ℕ → ℕ → ℤ} (Pm : ℤ → ℤ) (a : ℤ)
    (hent : ∀ i (hi : i < m), ∀ j ≤ d, (nm i j : ℚ) / dn i j = entry A b ⟨i, hi⟩ j)
    (hdn : ∀ i < m, ∀ j ≤ d, 0 < dn i j) :
    rowR d m nm dn (fun j => nrm (Pm a) (Pm (a + j)) j) =
      if toE (ptAt d Pm a) ∈ RealRAM.polytope A b then 1 else 0 := by
  set Y : ℕ → ℤ := fun j => nrm (Pm a) (Pm (a + j)) j with hY
  have hY0 : 0 < Y 0 := by
    simp only [hY, Nat.cast_zero, add_zero]; exact nrm_zero_pos _
  have hrat : ∀ k : ℕ, ((Y (1 + k) : ℤ) : ℚ) / (Y 0 : ℚ) = (Pm (a + 1 + k) : ℚ) / Pm a := fun k => by
    simp only [hY, Nat.cast_zero, add_zero]
    rw [nrm_ratio _ _ (by omega)]
    rw [show a + ((1 + k : ℕ) : ℤ) = a + 1 + k by push_cast; ring]
  have key : (∀ i < m, rowT d (nm i) (dn i) Y) ↔ toE (ptAt d Pm a) ∈ RealRAM.polytope A b := by
    simp only [RealRAM.polytope, Set.mem_ofPred_eq]
    constructor
    · intro h i
      have hi := (rowOK_iff (d := d) (Y := Y) hY0 (fun k hk => hdn i i.2 k hk)).1 (h i i.2)
      have e : ∑ j : Fin d, (A i j : ℝ) * (toE (ptAt d Pm a)) j =
          ((∑ k ∈ Finset.range d, ((nm i k : ℚ) / dn i k) * ((Y (1 + k) : ℚ) / Y 0) : ℚ) : ℝ) := by
        rw [Rat.cast_sum, Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hent i i.2 j (by omega), hrat]
        simp only [entry, j.2, ↓reduceDIte, Fin.eta, Rat.cast_mul]
        rfl
      rw [e]
      have eb : (b i : ℝ) = (((nm i d : ℚ) / dn i d : ℚ) : ℝ) := by
        rw [hent i i.2 d le_rfl]; simp [entry]
      rw [eb]; exact_mod_cast hi
    · intro h i hi
      refine (rowOK_iff (d := d) (Y := Y) hY0 (fun k hk => hdn i hi k hk)).2 ?_
      have h' := h ⟨i, hi⟩
      have e : ∑ j : Fin d, (A ⟨i, hi⟩ j : ℝ) * (toE (ptAt d Pm a)) j =
          ((∑ k ∈ Finset.range d, ((nm i k : ℚ) / dn i k) * ((Y (1 + k) : ℚ) / Y 0) : ℚ) : ℝ) := by
        rw [Rat.cast_sum, Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hent i hi j (by omega), hrat]
        simp only [entry, j.2, ↓reduceDIte, Fin.eta, Rat.cast_mul]
        rfl
      have eb : (b ⟨i, hi⟩ : ℝ) = (((nm i d : ℚ) / dn i d : ℚ) : ℝ) := by
        rw [hent i hi d le_rfl]; simp [entry]
      rw [e, eb] at h'
      exact_mod_cast h'
  unfold rowR
  by_cases hK : toE (ptAt d Pm a) ∈ RealRAM.polytope A b
  · rw [ite_eq_left (key.2 hK), ite_eq_left hK]
  · rw [ite_eq_right (fun h => hK (key.1 h)), ite_eq_right hK]

end AdversarialBco.UniPoly
