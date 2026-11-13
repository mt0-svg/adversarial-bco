/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowP

@[expose] public section

/-!
# The kept-row scan finds the `i`-th kept row

`scanK_spec` is proved on a recursion of the same shape and restated on `RowP.scanK`; `scanK_get` transfers it to a
row test given on the naturals.
-/

namespace AdversarialBco.Bit.Transfer.RowP

/-- The scan reads `keep` below `k` only. -/
theorem scanK_congr (keep keep' : ℕ → Bool) (i : ℕ) :
    ∀ k, (∀ r < k, keep r = keep' r) → scanK keep i k = scanK keep' i k
  | 0, _ => rfl
  | k + 1, h => by
    rw [scanK_succ, scanK_succ, h k (by omega), scanK_congr keep keep' i k fun r hr => h r (by omega)]

end AdversarialBco.Bit.Transfer.RowP

open AdversarialBco.Bit.Transfer.RowP

/-- The scan finds the `i`-th element of the list of the rows with the property `z` (in increasing order). -/
theorem AdversarialBco.Bit.Transfer.RowP.scanK_spec {m : ℕ} (z : Fin m → Bool)
    (i : Fin ((List.finRange m).filter fun r => z r).length) :
    (scanK (fun r => if h : r < m then z ⟨r, h⟩ else false) i m).2 =
      (((List.finRange m).filter fun r => z r).get i : ℕ) := by
  let z' : ℕ → Bool := fun r => if h : r < m then z ⟨r, h⟩ else false
  let L : ℕ → List ℕ := fun r => (List.range r).filter z'
  have hz'_val (x : Fin m) : z' x.val = z x := by
    dsimp [z']
    have hx : x.val < m := x.isLt
    simp [hx]
  have hL_eq : L m = ((List.finRange m).filter (z' ∘ Fin.val)).map Fin.val := by
    calc
      L m = (List.range m).filter z' := rfl
      _ = (List.map Fin.val (List.finRange m)).filter z' := by rw [List.map_coe_finRange_eq_range]
      _ = ((List.finRange m).filter (z' ∘ Fin.val)).map Fin.val := by rw [List.filter_map]
  have h_filter_eq : ((List.finRange m).filter (z' ∘ Fin.val)) = ((List.finRange m).filter fun r => z r) := by
    apply List.filter_congr
    intro x hx
    simp [hz'_val x]
  have h_main : ∀ (r : ℕ) (j : ℕ), (scanK z' j r).1 = (L r).length ∧ (∀ (hj : j < (L r).length), (scanK z' j r).2 = (L r).get ⟨j, hj⟩) := by
    intro r
    induction' r with r ih
    · intro j
      refine ⟨rfl, ?_⟩
      intro h; exfalso; exact Nat.not_lt_zero _ h
    · intro j
      have hL_succ : L (r + 1) = L r ++ (if z' r then [r] else []) := by
        dsimp [L]
        rw [List.range_succ, List.filter_append]
        by_cases hz' : z' r
        · simp [hz']
        · simp [hz']
      have h_len_succ : (L (r + 1)).length = (L r).length + (if z' r then 1 else 0) := by
        rw [hL_succ, List.length_append]
        by_cases hz' : z' r
        · simp [hz']
        · simp [hz']
      have h_count_eq : (scanK z' j r).1 = (L r).length := (ih j).1
      constructor
      · -- (scanK z' j (r+1)).1 = (L (r+1)).length
        by_cases hz' : z' r
        · rw [scanK]
          simp [hz']
          have h_simp : (if (scanK z' j r).1 = j then ((scanK z' j r).1 + 1, r) else ((scanK z' j r).1 + 1, (scanK z' j r).2)).1 = (scanK z' j r).1 + 1 := by
            split_ifs <;> simp
          rw [h_simp, h_count_eq, hL_succ]
          simp [hz']
        · rw [scanK]
          simp [hz']
          rw [h_count_eq, hL_succ]
          simp [hz']
      · -- j < (L (r+1)).length → (scanK z' j (r+1)).2 = (L (r+1)).get ⟨j, hj⟩
        intro hj
        -- hj : j < (L (r+1)).length
        by_cases hz' : z' r
        · rw [scanK]
          simp [hz']
          rw [h_count_eq]
          by_cases h_eq : (L r).length = j
          · subst h_eq
            simp
            -- Goal: r = (L (r + 1)).get ⟨(L r).length, hj⟩
            have hL_succ' : L (r + 1) = L r ++ [r] := by
              rw [hL_succ]; simp [hz']
            have hj_trans : (L r).length < (L r ++ [r]).length := by
              simpa [hL_succ'] using hj
            have h_rhs : (L (r + 1))[(L r).length]'hj = r := by
              calc
                (L (r + 1))[(L r).length]'hj = (L r ++ [r])[(L r).length]'hj_trans := by
                  simpa [hL_succ'] using rfl
                _ = r := by
                  simp [List.getElem_append_right (le_refl _) (h₂ := hj_trans)]
            exact h_rhs.symm
          · have h_lt : j < (L r).length := by
              have : j < (L r).length + 1 := by simpa [hL_succ, hz'] using hj
              omega
            have h_get_eq : (scanK z' j r).2 = (L r).get ⟨j, h_lt⟩ := (ih j).2 h_lt
            rw [h_get_eq]
            -- Goal: (if (L r).length = j then ((L r).length + 1, r) else ((L r).length + 1, (L r).get ⟨j, h_lt⟩)).2 = (L (r + 1)).get ⟨j, hj⟩
            simp [h_eq]
            -- Goal: (L r).get ⟨j, h_lt⟩ = (L (r + 1)).get ⟨j, hj⟩
            -- But displayed as (L r)[j] = (L (r+1))[j]
            have hL_succ' : L (r + 1) = L r ++ [r] := by
              rw [hL_succ]; simp [hz']
            have hj_trans : j < (L r ++ [r]).length := by
              simpa [hL_succ', hz'] using hj
            have h_calc : (L r)[j]'h_lt = (L (r + 1))[j]'hj := by
              calc
                (L r)[j]'h_lt = (L r ++ [r])[j]'hj_trans := by
                  simp [List.getElem_append_left h_lt]
                _ = (L (r + 1))[j]'hj := by
                  simpa [hL_succ'] using rfl
            simpa using h_calc
        · rw [scanK]
          simp [hz']
          -- Goal: (scanK z' j r).2 = (L (r + 1)).get ⟨j, hj⟩
          have hL_succ' : L (r + 1) = L r := by
            rw [hL_succ]; simp [hz']
          have h_lt : j < (L r).length := by
            simpa [hL_succ'] using hj
          have h_get_eq : (scanK z' j r).2 = (L r).get ⟨j, h_lt⟩ := (ih j).2 h_lt
          rw [h_get_eq]
          -- Goal: (L r).get ⟨j, h_lt⟩ = (L (r + 1)).get ⟨j, hj⟩
          -- hj : j < (L (r+1)).length, and hL_succ' : L (r+1) = L r
          -- So hj can be transported to j < (L r).length
          have hj' : j < (L r).length := by
            simpa [hL_succ'] using hj
          -- Now the goal is (L r).get ⟨j, h_lt⟩ = (L r).get ⟨j, hj'⟩
          -- These are equal by proof irrelevance
          simpa [hL_succ'] using rfl
  have h_len_eq : (L m).length = ((List.finRange m).filter fun r => z r).length := by
    rw [hL_eq, List.length_map, h_filter_eq]
  have h_i_lt : (i : ℕ) < (L m).length := by
    rw [h_len_eq]
    exact i.isLt
  have h_scanK_eq : (scanK z' (i : ℕ) m).2 = (L m).get ⟨(i : ℕ), h_i_lt⟩ := by
    have := (h_main m (i : ℕ)).2
    exact this h_i_lt
  have h_L_get : (L m).get ⟨(i : ℕ), h_i_lt⟩ = (((List.finRange m).filter fun r => z r).get i : ℕ) := by
    have h_map_eq : L m = (((List.finRange m).filter fun r => z r).map Fin.val) := by
      rw [hL_eq, h_filter_eq]
    have h_lt_A : (i : ℕ) < ((List.finRange m).filter fun r => z r).length := i.isLt
    have h_lt_map : (i : ℕ) < ((((List.finRange m).filter fun r => z r).map Fin.val)).length := by
      rw [List.length_map]
      exact h_lt_A
    calc
      (L m).get ⟨(i : ℕ), h_i_lt⟩ = ((((List.finRange m).filter fun r => z r).map Fin.val).get ⟨(i : ℕ), h_lt_map⟩) := by
        simpa [h_map_eq] using rfl
      _ = ((((List.finRange m).filter fun r => z r).map Fin.val)[(i : ℕ)]'h_lt_map) := by rw [List.get_eq_getElem]
      _ = Fin.val ((((List.finRange m).filter fun r => z r)[(i : ℕ)]'h_lt_A)) := by rw [List.getElem_map]
      _ = Fin.val ((((List.finRange m).filter fun r => z r).get ⟨(i : ℕ), h_lt_A⟩)) := by rw [List.get_eq_getElem]
      _ = Fin.val ((((List.finRange m).filter fun r => z r).get i)) := by
        congr
      _ = (((List.finRange m).filter fun r => z r).get i : ℕ) := rfl
  calc
    (scanK (fun r => if h : r < m then z ⟨r, h⟩ else false) i m).2 = (scanK z' (i : ℕ) m).2 := rfl
    _ = (L m).get ⟨(i : ℕ), h_i_lt⟩ := h_scanK_eq
    _ = (((List.finRange m).filter fun r => z r).get i : ℕ) := h_L_get

/-- The scan finds the kept row number `i`: the `i`-th element of the filtered list of `Fin m`. -/
theorem AdversarialBco.Bit.Transfer.RowP.scanK_get {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
    (keep : ℕ → Bool) (hk : ∀ k : Fin m, keep k = decide (P k)) (i : ℕ)
    (h : i < ((List.finRange m).filter fun k => decide (P k)).length) :
    (AdversarialBco.Bit.Transfer.RowP.scanK keep i m).2 =
      (((List.finRange m).filter fun k => decide (P k)).get ⟨i, h⟩ : ℕ) := by
  rw [scanK_congr keep (fun r => if h : r < m then decide (P ⟨r, h⟩) else false) i m
    fun r hr => by simp only [hr, ↓reduceDIte]; exact hk ⟨r, hr⟩]
  exact scanK_spec (fun k => decide (P k)) ⟨i, h⟩
