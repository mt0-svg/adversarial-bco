/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupRows
public import AdversarialBco.Bit.Transfer.XBLR2q

@[expose] public section

/-!
# BL's setup on the machine: P3's loop is P3

On the input cells (`NmI`, `DnI`), the loop `xS3` counts the kept rows (`s3cnt_eq`: `keptCnt`, which is
`(keptIdx A).length` at `m`), and its flag is P5's test on the kept rows (`s3bad_iff`). `inp_bnd`: the input cells are
at most `M` under `HeightLE A b M`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP Matrix

variable {d n m : ℕ}

/-- `keptCnt` as the length of a filtered range. -/
theorem keptCnt_range (A : Matrix (Fin m) (Fin d) ℚ) (k : ℕ) :
    keptCnt A k = ((List.range k).filter fun j => if h : j < m then decide (A ⟨j, h⟩ ≠ 0) else false).length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [keptCnt, ih, List.range_succ, List.filter_append, List.length_append]
    congr 1
    by_cases h : k < m
    · by_cases hA : A ⟨k, h⟩ ≠ 0
      · simp [h, hA]
      · simp [h, hA]
    · simp [h]

/-- P3's count over all rows is the number of kept rows. -/
theorem keptCnt_eq (A : Matrix (Fin m) (Fin d) ℚ) : keptCnt A m = (keptIdx A).length := by
  rw [keptCnt_range, keptIdx, ← List.map_coe_finRange_eq_range, List.filter_map, List.length_map]
  congr 2
  funext i
  simp [i.2]

variable (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

/-- Row `r < m` is kept iff its cleared row is nonzero. -/
theorem s3S_pos_iff (i : Fin m) : 0 < s3S (NmI d n m A b) (DnI d n m A b) d i ↔ A i ≠ 0 :=
  (kept_row_abs (A i) (fun j => rowA (NmI d n m A b) (DnI d n m A b) d i j) (PiI d n m A b i) (PiI_pos A b i)
    (rowA_A A b i)).symm

/-- P3's count on the input cells. -/
theorem s3cnt_eq : ∀ r, r ≤ m → s3cnt (NmI d n m A b) (DnI d n m A b) d r = keptCnt A r
  | 0, _ => rfl
  | r + 1, hr => by
    have hrm : r < m := by omega
    rw [s3cnt, keptCnt, s3cnt_eq r (by omega), dif_pos hrm]
    congr 1
    have := s3S_pos_iff (n := n) A b ⟨r, hrm⟩
    by_cases hA : A ⟨r, hrm⟩ ≠ 0
    · rw [if_pos (this.2 hA), if_pos hA]
    · rw [if_neg (fun h => hA (this.1 h)), if_neg hA]

/-- P5's test on row `i` from the cells of the position. -/
theorem s3U_iff (i : Fin m) (xm : Fin d → ℤ) (D : ℤ) (hD : 0 < D) :
    s3U (NmI d n m A b) (DnI d n m A b) xm D i ≤ 0 ↔ b i - A i ⬝ᵥ (fun j => (xm j : ℚ) / D) ≤ 0 :=
  (beta_row_abs (A i) (b i) (fun j => rowA (NmI d n m A b) (DnI d n m A b) d i j)
    (rowA (NmI d n m A b) (DnI d n m A b) d i d) (PiI d n m A b i) D xm (PiI_pos A b i) hD (rowA_A A b i)
    (rowA_b A b i)).symm

/-- The flag of P3's loop is P5's test on the kept rows. -/
theorem s3bad_iff (xm : Fin d → ℤ) (D : ℤ) (hD : 0 < D) :
    s3bad (NmI d n m A b) (DnI d n m A b) xm D m ↔
      ∃ i : Fin (keptIdx A).length, b ((keptIdx A).get i) - A ((keptIdx A).get i) ⬝ᵥ (fun j => (xm j : ℚ) / D) ≤ 0 := by
  rw [bad_iff]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    exact ⟨⟨k, hk⟩, (s3S_pos_iff A b ⟨k, hk⟩).1 h1, (s3U_iff A b ⟨k, hk⟩ xm D hD).1 h2⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, i.2, (s3S_pos_iff A b i).2 h1, (s3U_iff A b i xm D hD).2 h2⟩

/-- The input cells under `HeightLE A b M`. -/
theorem inp_bnd {M : ℕ} (hH : RealRAM.HeightLE A b M) :
    (∀ r < m, ∀ j ≤ d, |NmI d n m A b r j| ≤ M) ∧ ∀ r < m, ∀ j ≤ d, 1 ≤ DnI d n m A b r j ∧ DnI d n m A b r j ≤ M := by
  have he : ∀ (i : Fin m) (j : ℕ), (BitRAM.entry A b i j).num.natAbs ≤ M ∧ (BitRAM.entry A b i j).den ≤ M :=
    fun i j => by
      unfold BitRAM.entry
      split_ifs with hj
      · exact hH.1 i ⟨j, hj⟩
      · exact hH.2 i
  refine ⟨fun r hr j hj => ?_, fun r hr j hj => ?_⟩
  · rw [NmI_eq A b ⟨r, hr⟩ hj, Int.abs_eq_natAbs]
    exact_mod_cast (he ⟨r, hr⟩ j).1
  · rw [DnI_eq A b ⟨r, hr⟩ hj]
    exact ⟨by exact_mod_cast (BitRAM.entry A b ⟨r, hr⟩ j).den_pos, by exact_mod_cast (he ⟨r, hr⟩ j).2⟩

end AdversarialBco.Bit.Transfer.BLM
