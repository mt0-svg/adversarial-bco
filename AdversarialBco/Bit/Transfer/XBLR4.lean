/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR3

@[expose] public section

/-!
# BL's round on the machine, R2 to R4 in mode `run`

The gauge of the machine is BL's gauge (`gauge_mach`, from `bestG_gauge`), and `XV.r24` runs R2 to
R4 in mode `run`: the point `X̂`, the gauge, the scale, the play buffer, the play of `playPt cfg (.run st) ξ`, and the
reading `⌊2^p f_t(x_t)⌋` into the slot `sObs`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.BitRAM (toE inputMem entry)

variable {d : ℕ}

/-! ## The gauge from the machine's integers -/

private lemma foldl_max_ge_self (l : List ℚ) (a : ℚ) : a ≤ l.foldl max a := by
  induction' l with b l ih generalizing a
  · rfl
  · simp [List.foldl]
    have h : a ≤ max a b := by simp
    have h' : max a b ≤ List.foldl max (max a b) l := ih (max a b)
    exact le_trans h h'

private lemma foldl_max_mono (l : List ℚ) (a b : ℚ) (h : a ≤ b) : l.foldl max a ≤ l.foldl max b := by
  induction' l with c l ih generalizing a b
  · simp [h]
  · simp [List.foldl]
    have hmax : max a c ≤ max b c := max_le_max h (le_refl c)
    exact ih _ _ hmax

private lemma foldl_max_zero_nonneg (l : List ℚ) : 0 ≤ l.foldl max 0 :=
  foldl_max_ge_self l 0

private lemma foldl_max_zero_ge_all (l : List ℚ) : ∀ x ∈ l, x ≤ l.foldl max 0 := by
  induction' l with a l ih
  · intro x hx; cases hx
  · intro x hx
    simp [List.foldl]
    cases hx with
    | head _ =>
      have h := foldl_max_ge_self l (max 0 a)
      have ha_max : a ≤ max 0 a := by simp
      exact le_trans ha_max h
    | tail _ hx =>
      have h := ih x hx
      have hmono := foldl_max_mono l 0 (max 0 a) (by simp)
      linarith

private lemma foldl_max_zero_eq_zero_or_mem (l : List ℚ) : l.foldl max 0 = 0 ∨ l.foldl max 0 ∈ l := by
  rw [List.foldl_max]
  by_cases hle : l.max?.getD 0 ≤ (0 : ℚ)
  · left; simp [hle]
  · right
    have hpos : 0 ≤ l.max?.getD 0 := by linarith
    simp [hpos]
    cases h : l.max? with
    | none => simp [h] at hle
    | some x =>
      have hx_mem : x ∈ l := List.max?_mem h
      simp [h, hx_mem]

private lemma foldl_max_zero_eq_of_char (l : List ℚ) (v : ℚ) (h0 : 0 ≤ v) (hle : ∀ x ∈ l, x ≤ v)
    (hmem : v = 0 ∨ v ∈ l) : v = l.foldl max 0 := by
  have hle' : ∀ x ∈ l, x ≤ l.foldl max 0 := foldl_max_zero_ge_all l
  have hmem' : l.foldl max 0 = 0 ∨ l.foldl max 0 ∈ l := foldl_max_zero_eq_zero_or_mem l
  have h1 : v ≤ l.foldl max 0 := by
    rcases hmem with (hv | hv)
    · rcases hmem' with (hfl | hfl)
      · rw [hv, hfl]
      · rw [hv]
        exact foldl_max_zero_nonneg l
    · exact hle' _ hv
  have h2 : l.foldl max 0 ≤ v := by
    rcases hmem' with (hfl | hfl)
    · rw [hfl]; exact h0
    · exact hle _ hfl
  exact (le_antisymm h2 h1).symm

private lemma bestG_inv (num den : ℕ → ℤ) (k : ℕ) :
    (0 < (bestG num den k).2) ∧
    (0 ≤ ((bestG num den k).1 : ℚ) / (bestG num den k).2) ∧
    (∀ r : ℕ, r < k → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((bestG num den k).1 : ℚ) / (bestG num den k).2) ∧
    (bestG num den k = (0, 1) ∨ ∃ r : ℕ, r < k ∧ 0 < den r ∧ bestG num den k = (num r, den r)) := by
  induction' k with k ih
  · have h0 : bestG num den 0 = (0, 1) := by simp [bestG]
    refine ⟨?_, ?_, ?_, Or.inl h0⟩
    · simp [h0]
    · simp [h0]
    · intro r hr; exfalso; exact Nat.not_lt_zero _ hr
  · rcases ih with ⟨hDpos, hVnonneg, hVle, hGcases⟩
    by_cases hcond : 0 < den k ∧ ((bestG num den k).1 * den k < num k * (bestG num den k).2)
    · rcases hcond with ⟨hDkpos, hlt⟩
      have hG'_val : bestG num den (k + 1) = (num k, den k) := by
        rw [bestG]
        simp [hDkpos, hlt]
      have hDpos_q : (0 : ℚ) < (den k : ℚ) := by exact_mod_cast hDkpos
      have hlt' : ((bestG num den k).1 : ℚ) * (den k : ℚ) < (num k : ℚ) * ((bestG num den k).2 : ℚ) := by
        exact_mod_cast hlt
      have hV'nonneg : 0 ≤ ((num k : ℚ) / (den k : ℚ)) := by
        have hpos : 0 ≤ ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ) := hVnonneg
        have hlt_div : ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ) < (num k : ℚ) / (den k : ℚ) :=
          (div_lt_div_iff₀ (by exact_mod_cast hDpos) hDpos_q).mpr hlt'
        linarith
      have hV'le : ∀ r : ℕ, r < k + 1 → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((num k : ℚ) / (den k : ℚ)) := by
        intro r hr hDrpos
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with (hrk | hr_eq)
        · have hle_r := hVle r hrk hDrpos
          have hlt_div : ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ) < (num k : ℚ) / (den k : ℚ) :=
            (div_lt_div_iff₀ (by exact_mod_cast hDpos) hDpos_q).mpr hlt'
          have hle' : ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ) ≤ (num k : ℚ) / (den k : ℚ) := by linarith
          linarith
        · rw [hr_eq]
      have hG'cases : bestG num den (k + 1) = (0, 1) ∨ ∃ r : ℕ, r < k + 1 ∧ 0 < den r ∧ bestG num den (k + 1) = (num r, den r) := by
        right; refine ⟨k, Nat.lt_succ_self k, hDkpos, ?_⟩; simp [hG'_val]
      have hG2pos : 0 < (bestG num den (k + 1)).2 := by
        simp [hG'_val, hDkpos]
      have hV'nonneg' : 0 ≤ ((bestG num den (k + 1)).1 : ℚ) / (bestG num den (k + 1)).2 := by
        simp [hG'_val, hV'nonneg]
      have hV'le' : ∀ r : ℕ, r < k + 1 → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((bestG num den (k + 1)).1 : ℚ) / (bestG num den (k + 1)).2 := by
        intro r hr hDrpos
        have h := hV'le r hr hDrpos
        simp [hG'_val] at h ⊢
        exact h
      exact ⟨hG2pos, hV'nonneg', hV'le', hG'cases⟩
    · have hG'_val : bestG num den (k + 1) = bestG num den k := by
        rw [bestG]
        simp [hcond]
      have hV'le_full : ∀ r : ℕ, r < k + 1 → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ) := by
        intro r hr hDrpos
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with (hrk | hr_eq)
        · exact hVle r hrk hDrpos
        · rw [hr_eq] at hDrpos ⊢
          by_cases hDkpos' : 0 < den k
          · have hge : (bestG num den k).1 * den k ≥ num k * (bestG num den k).2 := by
              have h_not_and : ¬ (0 < den k ∧ ((bestG num den k).1 * den k < num k * (bestG num den k).2)) := hcond
              have h_not_lt : ¬ ((bestG num den k).1 * den k < num k * (bestG num den k).2) := by
                intro hlt'; apply h_not_and; exact ⟨hDkpos', hlt'⟩
              omega
            have hge' : ((bestG num den k).1 : ℚ) * (den k : ℚ) ≥ (num k : ℚ) * ((bestG num den k).2 : ℚ) := by
              exact_mod_cast hge
            have hDpos_q : (0 : ℚ) < (den k : ℚ) := by exact_mod_cast hDkpos'
            have hDpos_q' : (0 : ℚ) < ((bestG num den k).2 : ℚ) := by exact_mod_cast hDpos
            exact (div_le_div_iff₀ hDpos_q hDpos_q').mpr hge'
          · exfalso; exact hDkpos' hDrpos
      have hG'cases : bestG num den k = (0, 1) ∨ ∃ r : ℕ, r < k + 1 ∧ 0 < den r ∧ bestG num den k = (num r, den r) := by
        rcases hGcases with (hGzero | ⟨r, hr_lt_k, hDrpos_r, hGval_r⟩)
        · left; exact hGzero
        · right; refine ⟨r, Nat.lt_of_lt_of_le hr_lt_k (Nat.le_succ k), hDrpos_r, hGval_r⟩
      have hgoal : (0 < (bestG num den k).2) ∧
        (0 ≤ ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ)) ∧
        (∀ r : ℕ, r < k + 1 → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((bestG num den k).1 : ℚ) / ((bestG num den k).2 : ℚ)) ∧
        (bestG num den k = (0, 1) ∨ ∃ r : ℕ, r < k + 1 ∧ 0 < den r ∧ bestG num den k = (num r, den r)) :=
        ⟨hDpos, hVnonneg, hV'le_full, hG'cases⟩
      simpa [hG'_val] using hgoal

/-- The guarded running maximum over all rows is the maximum of `0` and the values `q r` of the selected rows (`z r`),
when every selected row has `den r > 0` and `num r / den r = q r` and every other row has `num r = 0`; it is `(0, 1)`
or one of the pairs with a positive denominator. -/
theorem bestG_gauge {m : ℕ} (z : Fin m → Bool) (q : Fin m → ℚ) (num den : ℕ → ℤ)
    (hk : ∀ r : Fin m, z r = true → 0 < den r ∧ (num r : ℚ) / den r = q r)
    (hz : ∀ r : Fin m, z r = false → num r = 0) :
    0 < (bestG num den m).2 ∧
      ((bestG num den m).1 : ℚ) / (bestG num den m).2 =
        (List.ofFn fun j : Fin ((List.finRange m).filter z).length =>
          q (((List.finRange m).filter z).get j)).foldl max 0 ∧
      (bestG num den m = (0, 1) ∨ ∃ r < m, 0 < den r ∧ bestG num den m = (num r, den r)) := by
  set l := List.ofFn fun j : Fin ((List.finRange m).filter z).length =>
    q (((List.finRange m).filter z).get j) with hl
  have hinv := bestG_inv num den m
  rcases hinv with ⟨hDpos, hVnonneg, hVle, hGcases⟩
  have hVle' : ∀ r : ℕ, r < m → 0 < den r → ((num r : ℚ) / (den r : ℚ)) ≤ ((bestG num den m).1 : ℚ) / (bestG num den m).2 := hVle
  have hmem_list : ∀ x ∈ l, x ≤ ((bestG num den m).1 : ℚ) / (bestG num den m).2 := by
    intro x hx
    rw [hl] at hx
    rcases List.mem_ofFn.mp hx with ⟨j, rfl⟩
    set r := ((List.finRange m).filter z).get j with hr_def
    have hmem_filter : r ∈ (List.finRange m).filter z := by
      have := List.get_mem ((List.finRange m).filter z) j
      simpa [hr_def] using this
    rcases List.mem_filter.mp hmem_filter with ⟨hmem_range, hz_true⟩
    have hr_lt_m : (r : ℕ) < m := r.is_lt
    have hden_pos : 0 < den (r : ℕ) := (hk r hz_true).1
    have hq_eq : (num (r : ℕ) : ℚ) / (den (r : ℕ) : ℚ) = q r := (hk r hz_true).2
    have hle := hVle' (r : ℕ) hr_lt_m hden_pos
    rw [← hq_eq]
    exact hle
  have hmem_zero_or : (((bestG num den m).1 : ℚ) / (bestG num den m).2 = 0) ∨
    (((bestG num den m).1 : ℚ) / (bestG num den m).2 ∈ l) := by
    rcases hGcases with (hGzero | ⟨r, hr_lt_m, hDrpos, hGval⟩)
    · left
      simp [hGzero]
    · by_cases hz_true : z ⟨r, hr_lt_m⟩ = true
      · right
        have hq_eq := (hk ⟨r, hr_lt_m⟩ hz_true).2
        have hV_eq : ((bestG num den m).1 : ℚ) / (bestG num den m).2 = q ⟨r, hr_lt_m⟩ := by
          simp [hGval, hq_eq]
        rw [hV_eq]
        rw [hl]
        have hmem : (⟨r, hr_lt_m⟩ : Fin m) ∈ (List.finRange m).filter z := by
          apply List.mem_filter.mpr
          exact ⟨List.mem_finRange _, hz_true⟩
        rcases List.mem_iff_get.mp hmem with ⟨j, hj⟩
        apply List.mem_ofFn.mpr
        refine ⟨j, ?_⟩
        rw [hj]
      · have hz_false : z ⟨r, hr_lt_m⟩ = false := by
          cases hz_cases : z ⟨r, hr_lt_m⟩
          · rfl
          · exfalso; exact hz_true hz_cases
        have hnum_zero := hz ⟨r, hr_lt_m⟩ hz_false
        left
        simp [hGval, hnum_zero]
  have heq : ((bestG num den m).1 : ℚ) / (bestG num den m).2 = l.foldl max 0 :=
    foldl_max_zero_eq_of_char l (((bestG num den m).1 : ℚ) / (bestG num den m).2)
      hVnonneg hmem_list hmem_zero_or
  exact ⟨hDpos, heq, hGcases⟩

section Gauge

variable {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

theorem gNI_cast (aS : Matrix (Fin d) (Fin d) ℤ) (xh : Fin d → ℤ) (DS DX : ℤ) (AS : Matrix (Fin d) (Fin d) ℚ)
    (hA : ∀ i j, (aS i j : ℚ) / DS = AS i j) (hDS : 0 < DS) (hDX : 0 < DX) (r : Fin m) :
    (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh) r : ℚ) =
      (ASᵀ *ᵥ A r) ⬝ᵥ (fun j => (xh j : ℚ) / DX) * (PiI d n m A b r * DS * DX) := by
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have hDX' : (DX : ℚ) ≠ 0 := by exact_mod_cast hDX.ne'
  have hr : ∀ j : Fin d, (rowA (NmI d n m A b) (DnI d n m A b) d r j : ℚ) = A r j * PiI d n m A b r := fun j => by
    rw [rowA_cast A b r j.2.le]; simp [entry]
  have hAS : ∀ i j, (aS i j : ℚ) = AS i j * DS := fun i j => by rw [← hA i j]; field_simp
  unfold gNI
  simp only [dotProduct, mulVec, transpose_apply]
  push_cast
  simp only [hr, hAS, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

theorem gDI_cast (muS : Fin d → ℤ) (DS DX : ℤ) (μS : Fin d → ℚ) (hmu : ∀ j, (muS j : ℚ) / DS = μS j)
    (hDS : 0 < DS) (r : Fin m) :
    (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX r : ℚ) =
      (b r - A r ⬝ᵥ μS) * (PiI d n m A b r * DS * DX) := by
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have hr : ∀ j : Fin d, (rowA (NmI d n m A b) (DnI d n m A b) d r j : ℚ) = A r j * PiI d n m A b r := fun j => by
    rw [rowA_cast A b r j.2.le]; simp [entry]
  have hb : (rowA (NmI d n m A b) (DnI d n m A b) d r d : ℚ) = b r * PiI d n m A b r := by
    rw [rowA_cast A b r le_rfl]; simp [entry]
  have hm : ∀ j, (muS j : ℚ) = μS j * DS := fun j => by rw [← hmu j]; field_simp
  unfold gDI
  simp only [dotProduct]
  push_cast
  simp only [hr, hb, hm]
  rw [show ∑ i, A r i * (PiI d n m A b r : ℚ) * (μS i * DS) = (PiI d n m A b r * DS) * ∑ i, A r i * μS i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  ring

/-- **The gauge from the machine's integers**: the guarded running maximum over all input rows of the cross-multiplied
ratios is BL's gauge at `X = X̂/D_X`, with a positive denominator, when every kept row has `β̃ > 0`. -/
theorem gauge_mach (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (DS DX : ℤ) (muS : Fin d → ℤ)
    (aS : Matrix (Fin d) (Fin d) ℤ) (xh : Fin d → ℤ) (hDS : 0 < DS) (hDX : 0 < DX)
    (hmu : ∀ j, (muS j : ℚ) / DS = S.1 j) (hA : ∀ i j, (aS i j : ℚ) / DS = S.2 i j)
    (hβ : ∀ i, 0 < (mkCfg d n m A b c S).β i) :
    0 < (bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh)) (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX) m).2 ∧
      ((bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh))
          (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX) m).1 : ℚ) /
        (bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh))
          (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX) m).2 =
      gaugeQ (mkCfg d n m A b c S) (fun j => (xh j : ℚ) / DX) := by
  set X : Fin d → ℚ := fun j => (xh j : ℚ) / DX with hX
  have hP : ∀ r : Fin m, (0 : ℚ) < PiI d n m A b r * DS * DX := fun r => by
    have := PiI_pos (n := n) A b r
    have : (0 : ℚ) < DS := by exact_mod_cast hDS
    have : (0 : ℚ) < DX := by exact_mod_cast hDX
    positivity
  have hk : ∀ r : Fin m, decide (A r ≠ 0) = true →
      0 < gDI (NmI d n m A b) (DnI d n m A b) muS DS DX r ∧
        (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh) r : ℚ) / gDI (NmI d n m A b) (DnI d n m A b) muS DS DX r =
          (S.2ᵀ *ᵥ A r) ⬝ᵥ X / (b r - A r ⬝ᵥ S.1) := by
    intro r hr
    have hAr : A r ≠ 0 := by simpa using hr
    have hmem : r ∈ keptIdx A := by simp [keptIdx, hAr]
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    have hb : 0 < b r - A r ⬝ᵥ S.1 := by
      have := hβ i; simp only [mkCfg] at this; rw [hi] at this; exact this
    have hD := gDI_cast (n := n) A b muS DS DX S.1 hmu hDS r
    have hN := gNI_cast (n := n) A b aS xh DS DX S.2 hA hDS hDX r
    refine ⟨?_, ?_⟩
    · have : (0 : ℚ) < gDI (NmI d n m A b) (DnI d n m A b) muS DS DX r := by rw [hD]; exact mul_pos hb (hP r)
      exact_mod_cast this
    · rw [hD, hN, mul_div_mul_right _ _ (hP r).ne']
  have hz : ∀ r : Fin m, decide (A r ≠ 0) = false → gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh) r = 0 := by
    intro r hr
    have hAr : A r = 0 := by simpa using hr
    unfold gNI
    simp only [dotProduct]
    exact Finset.sum_eq_zero fun j _ => by rw [rowA_zero A b r hAr j, zero_mul]
  obtain ⟨h1, h2, -⟩ := bestG_gauge (fun r => decide (A r ≠ 0))
    (fun r => (S.2ᵀ *ᵥ A r) ⬝ᵥ X / (b r - A r ⬝ᵥ S.1)) _ _ hk hz
  exact ⟨h1, h2⟩

/-- The input cells are bounded by the height of the input. -/
theorem height_inp {M : ℕ} (hH : RealRAM.HeightLE A b M) {r : ℕ} (hr : r < m) {j : ℕ} (hj : j ≤ d) :
    |NmI d n m A b r j| ≤ M ∧ 1 ≤ DnI d n m A b r j ∧ DnI d n m A b r j ≤ M := by
  have e1 := NmI_eq (n := n) A b ⟨r, hr⟩ hj
  have e2 := DnI_eq (n := n) A b ⟨r, hr⟩ hj
  simp only at e1 e2
  rw [e1, e2]
  have hb : (entry A b ⟨r, hr⟩ j).num.natAbs ≤ M ∧ (entry A b ⟨r, hr⟩ j).den ≤ M := by
    unfold entry
    split_ifs with h
    · exact hH.1 _ _
    · exact hH.2 _
  refine ⟨?_, by exact_mod_cast (entry A b ⟨r, hr⟩ j).den_pos, by exact_mod_cast hb.2⟩
  rw [Int.abs_eq_natAbs]; exact_mod_cast hb.1

end Gauge

/-! ## Bounds -/

theorem bnd_sc {σ : Env d} {E y : ℕ} {v : ℤ} (hb : ∀ y < nSP, ∃ z : ℤ, σ.sc y = z ∧ |z| ≤ 2 ^ E) (hy : y < nSP)
    (h : σ.sc y = v) : |v| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb y hy
  rw [h] at hz
  rw [show v = z by exact_mod_cast hz]; exact bz

theorem bnd_arr {σ : Env d} {E a k : ℕ} {v : ℤ}
    (hb : ∀ a < nAP, ∀ k < asz d, ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E) (ha : a < nAP) (hk : k < asz d)
    (h : σ.arr a k = v) : |v| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := hb a ha k hk
  rw [h] at hz
  rw [show v = z by exact_mod_cast hz]; exact bz

theorem abs_mul_pow {x y : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ b) : |x * y| ≤ 2 ^ (a + b) := by
  rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

theorem abs_add_pow {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x + y| ≤ 2 ^ (a + 1) := by
  rw [pow_succ]; exact (abs_add_le _ _).trans (by linarith)

/-! ## The play of mode `run` from the machine's integers -/

/-- The scale from the gauge pair. -/
theorem ptQ_mach (cfg : Cfg d) (X : Fin d → ℚ) (bN bD : ℤ) (hbD : 0 < bD) (hg : (bN : ℚ) / bD = gaugeQ cfg X)
    (heps : OnG cfg.par.pF cfg.par.eps) (he1 : cfg.par.eps < 1) :
    ptQ cfg X = ((ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).1 : ℚ) /
      (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).2 := by
  set F : ℤ := 2 ^ cfg.par.pF with hF
  set eh := qn cfg.par.pF cfg.par.eps with heh
  have hF0 : (0 : ℤ) < F := by rw [hF]; positivity
  have hF0' : (0 : ℚ) < (F : ℚ) := by exact_mod_cast hF0
  have heF : (eh : ℚ) = cfg.par.eps * F := by rw [heh, heps, hF]; push_cast; ring
  have he : eh < F := by
    have : (eh : ℚ) < F := by rw [heF]; nlinarith
    exact_mod_cast this
  have hε : cfg.par.eps = (eh : ℚ) / F := by rw [heF]; field_simp
  unfold ptQ
  rw [← hg, hε, ptQ_int bN bD eh F hbD hF0 he]
  unfold ptPair
  split_ifs <;> simp

/-- BL's point `X'` from the machine's integers. -/
theorem XQ_mach (cfg : Cfg d) (st : St d) (Dm : ℤ) (mh Γ : Fin d → ℤ) (g : ℕ) (hDm : 0 < Dm)
    (hmh : ∀ j, (mh j : ℚ) / Dm = st.mu j) (hA : ∀ i k, OnG cfg.par.p (st.A i k))
    (hlam : OnG cfg.par.pF cfg.par.lam) (j : Fin d) :
    XQ cfg st (fun i => (Γ i : ℚ) / 2 ^ g) j =
      (xhI mh (fun i k => qn cfg.par.p (st.A i k)) Γ Dm (2 ^ cfg.par.pF) (2 ^ cfg.par.p) (2 ^ g)
        (qn cfg.par.pF cfg.par.lam) j : ℚ) / ((Dm * 2 ^ cfg.par.pF * 2 ^ cfg.par.p * 2 ^ g : ℤ) : ℚ) := by
  have hmuq : st.mu = fun j => (mh j : ℚ) / Dm := funext fun j => (hmh j).symm
  have hAq : st.A = Matrix.of fun i k => ((qn cfg.par.p (st.A i k) : ℤ) : ℚ) / ((2 ^ cfg.par.p : ℤ) : ℚ) := by
    ext i k; rw [Matrix.of_apply]; push_cast; exact eq_qn_div _ (hA i k)
  have hlq : cfg.par.lam = ((qn cfg.par.pF cfg.par.lam : ℤ) : ℚ) / ((2 ^ cfg.par.pF : ℤ) : ℚ) := by
    push_cast; exact eq_qn_div _ hlam
  have hg : (2 : ℚ) ^ g = ((2 ^ g : ℤ) : ℚ) := by push_cast; rfl
  unfold XQ
  rw [hg]
  conv_lhs => rw [hmuq, hAq, hlq]
  rw [XQ_int Dm (2 ^ cfg.par.pF) (2 ^ cfg.par.p) (2 ^ g) (qn cfg.par.pF cfg.par.lam) mh
    (fun i k => qn cfg.par.p (st.A i k)) Γ hDm (by positivity) (by positivity) (by positivity) j]
  rfl

/-- **The play of mode `run` from the machine's integers**, all at once: the gauge pair, the scale and the play
buffer of R2 are BL's `gaugeQ`, `ptQ` and `playPt`. -/
theorem run_play_pure {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d) (Dm DS : ℤ) (mh muS Γ : Fin d → ℤ)
    (aS : Matrix (Fin d) (Fin d) ℤ) (g : ℕ) (hDm : 0 < Dm) (hDS : 0 < DS) (hmh : ∀ j, (mh j : ℚ) / Dm = st.mu j)
    (hmuS : ∀ j, (muS j : ℚ) / DS = S.1 j) (haS : ∀ i j, (aS i j : ℚ) / DS = S.2 i j)
    (hA : ∀ i k, OnG (par d n).p (st.A i k)) (hlam : OnG (par d n).pF (par d n).lam)
    (heps : OnG (par d n).pF (par d n).eps) (he1 : (par d n).eps < 1)
    (hβ : ∀ i, 0 < (mkCfg d n m A b c S).β i) (bN bD pN pD : ℤ)
    (hb : (bN, bD) = bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xhI mh (fun i k => qn (par d n).p (st.A i k)) Γ
        Dm (2 ^ (par d n).pF) (2 ^ (par d n).p) (2 ^ g) (qn (par d n).pF (par d n).lam)))
      (gDI (NmI d n m A b) (DnI d n m A b) muS DS (Dm * 2 ^ (par d n).pF * 2 ^ (par d n).p * 2 ^ g)) m)
    (hp : (pN, pD) = ptPair bN bD (2 ^ (par d n).pF) (qn (par d n).pF (par d n).eps)) :
    0 < pN ∧ 0 < pD ∧
      ptQ (mkCfg d n m A b c S) (XQ (mkCfg d n m A b c S) st (fun i => (Γ i : ℚ) / 2 ^ g)) = (pN : ℚ) / pD ∧
      ∀ j, playPt (mkCfg d n m A b c S) (.run st) (fun i => (Γ i : ℚ) / 2 ^ g) j =
        ((muS j * (Dm * 2 ^ (par d n).pF * 2 ^ (par d n).p * 2 ^ g) * pN +
            (aS *ᵥ xhI mh (fun i k => qn (par d n).p (st.A i k)) Γ Dm (2 ^ (par d n).pF) (2 ^ (par d n).p) (2 ^ g)
              (qn (par d n).pF (par d n).lam)) j * pD : ℤ) : ℚ) /
          ((DS * (Dm * 2 ^ (par d n).pF * 2 ^ (par d n).p * 2 ^ g) * pN : ℤ) : ℚ) := by
  have hDX : 0 < Dm * 2 ^ (par d n).pF * 2 ^ (par d n).p * 2 ^ g := by positivity
  have hX := XQ_mach (mkCfg d n m A b c S) st Dm mh Γ g hDm hmh hA hlam
  have hXf : XQ (mkCfg d n m A b c S) st (fun i => (Γ i : ℚ) / 2 ^ g) = fun j =>
      (xhI mh (fun i k => qn (par d n).p (st.A i k)) Γ Dm (2 ^ (par d n).pF) (2 ^ (par d n).p) (2 ^ g)
        (qn (par d n).pF (par d n).lam) j : ℚ) / ((Dm * 2 ^ (par d n).pF * 2 ^ (par d n).p * 2 ^ g : ℤ) : ℚ) :=
    funext hX
  obtain ⟨hbD0, hg⟩ := gauge_mach (n := n) A b c S DS _ muS aS _ hDS hDX hmuS haS hβ
  rw [← hb] at hbD0 hg
  rw [← hXf] at hg
  obtain ⟨hN, hD, hpl⟩ := playPt_mach (mkCfg d n m A b c S) st _ DS _ bN bD muS _ aS hDS hDX hbD0 hmuS haS hX hg
    heps he1
  have hpt := ptQ_mach (mkCfg d n m A b c S) _ bN bD hbD0 hg heps he1
  simp only [show (mkCfg d n m A b c S).par = par d n from rfl] at hN hD hpl hpt
  rw [← hp] at hN hD hpl hpt
  exact ⟨hN, hD, hpt, fun j => by rw [hpl j]; rfl⟩

/-! ## R2 to R4 in mode `run` -/

/-- The slot of the reading `obs`. -/
abbrev sObs : ℕ := 44

/-- `romega` with the slot of the reading unfolded. -/
macro "r24omega" : tactic => `(tactic| ((try simp only [sObs] at *) <;> romega))

/-- R2 to R4 in mode `run`: the point, the gauge, the scale and the play buffer, the play, the reading. -/
def xR24 (L : Layout) : XCmd :=
  .seq (xR2x L) (.seq (xR2g L) (.seq (xR2p L) (.seq (xplay L aPl) (xobs L sObs rP))))

/-- The units of `xR24`. -/
def r24Units (d m : ℕ) : ℕ := r2xUnits d + (r2gUnits d m + (r2pUnits d + ((d + 2) + 1)))

/-- The scratch of R2 to R4. -/
def S24 (y : ℕ) : Prop := (sZeta < y ∧ y < 64) ∨ tR ≤ y
def N24 (j : ℕ) : Prop := rD2 < j ∧ j < 32
def A24 (a _k : ℕ) : Prop := aGam < a ∧ a < 32

/-- `σ'` agrees with `σ` outside the cells `S`, `N`, `Ar` (rounds and points free). -/
def FrameC (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) (σ σ' : Env d) : Prop :=
  (∀ j, ¬ N j → σ'.nat j = σ.nat j) ∧ (∀ y, ¬ S y → σ'.sc y = σ.sc y) ∧ (∀ b k, ¬ Ar b k → σ'.arr b k = σ.arr b k)

set_option maxHeartbeats 4000000 in
/-- **R2 to R4 in mode `run`.** From BL's invariant at the start of the round (`σ0`) and R1's draw in `aGam`, BL
plays `playPt cfg (.run st) ξ` and reads `⌊2^p f_t(x_t)⌋`; the scale `pt' = pt_N/pt_D` stays in its slots, `Â Γ` in
`aWv`. -/
theorem XV.r24 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {n m K0 E Mh t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ}
    {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d} {cs : ℕ → Bool} {σ0 σ : Env d}
    (hI : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ0) (hP : SamePers σ0 σ) (hr : σ.rounds = t)
    (hGam : ∀ i : Fin d, σ.arr aGam i = gamI cs K0 (par d n).B d t i)
    (hX : X.inp = fun j : ℕ => inputMem d n m A b (j : ℤ)) (hoff : 3 + 2 * ((d + 1) * m) ≤ X.off)
    (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa) (hH : RealRAM.HeightLE A b Mh) (hM1 : 1 ≤ Mh) (hME : Mh ≤ 2 ^ E)
    (hβ : ∀ i, 0 < (mkCfg d n m A b c S).β i) (heps : OnG (par d n).pF (par d n).eps) (he1 : (par d n).eps < 1)
    (hlam : OnG (par d n).pF (par d n).lam) (hEB : 4 * gsm_prec (par d n).B ≤ E) (hdE : d ≤ 2 ^ E)
    (hd1 : 1 ≤ d) (hℓ : 3 * (E * d) + 33 * E + 11 ≤ ℓ) (hpℓ : (par d n).p ≤ ℓ) (hpa : (par d n).p < 2 ^ ℓa)
    (hobs : |((⌊(2 : ℝ) ^ (par d n).p * X.wb.f t
      (toE (playPt (mkCfg d n m A b c S) (.run st) (draw cs K0 (par d n).B d t).1))⌋ : ℤ) : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xR24 L) σ (r24Units d m) (fun σ' =>
      σ'.rounds = t + 1 ∧
      σ'.pts = Function.update σ.pts t (toE (playPt (mkCfg d n m A b c S) (.run st) (draw cs K0 (par d n).B d t).1)) ∧
      σ'.sc sObs = ((⌊(2 : ℝ) ^ (par d n).p * X.wb.f t
        (toE (playPt (mkCfg d n m A b c S) (.run st) (draw cs K0 (par d n).B d t).1))⌋ : ℤ) : ℝ) ∧
      (∃ pN pD : ℤ, 0 < pN ∧ 0 < pD ∧ σ'.sc sPtN = pN ∧ σ'.sc sPtD = pD ∧
        ptQ (mkCfg d n m A b c S) (XQ (mkCfg d n m A b c S) st (draw cs K0 (par d n).B d t).1) = (pN : ℚ) / pD ∧
        |pN| ≤ 2 ^ (tG d E + E + 1) ∧ |pD| ≤ 2 ^ (tG d E + E + 1)) ∧
      (∀ i : Fin d, σ'.arr aWv i =
        ((fun i k => qn (par d n).p (st.A i k) : Matrix (Fin d) (Fin d) ℤ) *ᵥ
          fun k => gamI cs K0 (par d n).B d t k) i) ∧
      σ'.draws = σ.draws ∧ FrameC S24 N24 A24 σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by omega)
  have hdl : ∀ i k : Fin d, d * i + k < asz d := fun i k => by
    unfold asz; have := i.2; have := k.2; nlinarith
  have hdl1 : ∀ k : Fin d, (k : ℕ) < asz d := fun k => by unfold asz; have := k.2; nlinarith
  set cfg := mkCfg d n m A b c S with hcfg
  have hpar : cfg.par = par d n := rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hI.regs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := hI.consts
  obtain ⟨p0, p1, -⟩ := hI.par
  obtain ⟨DS, hDS0, hDS, hmuS, hAS⟩ := hI.pos
  choose muS hmuS1 hmuS2 using hmuS
  choose aS haS1 haS2 using hAS
  obtain ⟨-, -, ⟨Dm, hDm0, hDm, hmu⟩, hA, -⟩ := hI.mode
  choose mh hmh1 hmh2 using hmu
  obtain ⟨bS, bA⟩ := hI.bnd
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hP.1
  have eS : ∀ y < nSP, σ.sc y = σ0.sc y := hP.2.1
  have eA : ∀ a < nAP, ∀ k, σ.arr a k = σ0.arr a k := hP.2.2
  -- the integers
  set B := (par d n).B with hB
  set Ah : Matrix (Fin d) (Fin d) ℤ := fun i k => qn (par d n).p (st.A i k) with hAh
  set Γ : Fin d → ℤ := fun k => gamI cs K0 B d t k with hΓ
  set PF : ℤ := 2 ^ (par d n).pF with hPF
  set Pq : ℤ := 2 ^ (par d n).p with hPq
  set G : ℤ := 2 ^ (2 * gsm_prec B) with hG
  set lh := qn (par d n).pF (par d n).lam with hlh
  set eh := qn (par d n).pF (par d n).eps with heh
  have vA : ∀ i k : Fin d, σ.arr aA (d * i + k) = Ah i k := fun i k => by
    rw [eA _ (by decide)]; exact (hA i k).1
  have vAS : ∀ i k : Fin d, σ.arr aAS (d * i + k) = aS i k := fun i k => by rw [eA _ (by decide)]; exact haS1 i k
  have vmu : ∀ k : Fin d, σ.arr aMu k = mh k := fun k => by rw [eA _ (by decide)]; exact hmh1 k
  have vmuS : ∀ k : Fin d, σ.arr aMuS k = muS k := fun k => by rw [eA _ (by decide)]; exact hmuS1 k
  have vDm : σ.sc sDmu = Dm := by rw [eS _ (by decide), hDm]
  have vDS : σ.sc sDS = DS := by rw [eS _ (by decide), hDS]
  have vPF : σ.sc s2pF = PF := by rw [eS _ (by decide), c3, hPF]; push_cast; rfl
  have vPq : σ.sc s2p = Pq := by rw [eS _ (by decide), c2, hPq]; push_cast; rfl
  have vG : σ.sc s2g = G := by rw [eS _ (by decide), c4, hG]; push_cast; rfl
  have vlh : σ.sc sLamb = lh := by rw [eS _ (by decide)]; exact p1
  have veh : σ.sc sEps = eh := by rw [eS _ (by decide)]; exact p0
  have vD : σ.nat rD = d := by rw [eN _ (by decide), r0]
  have vM : σ.nat rM = m := by rw [eN _ (by decide), r1]
  have v1 : σ.nat rOne = 1 := by rw [eN _ (by decide), r3]
  have vP : σ.nat rP = (par d n).p := by rw [eN _ (by decide), r4]; rfl
  have vz : σ.sc sZ = 0 := by rw [eS _ (by decide), c0]
  -- the bounds
  have bAh : ∀ i k, |Ah i k| ≤ 2 ^ E := fun i k => bnd_arr bA (by decide) (hdl i k) (hA i k).1
  have bAS : ∀ i k, |aS i k| ≤ 2 ^ E := fun i k => bnd_arr bA (by decide) (hdl i k) (haS1 i k)
  have bmh : ∀ k, |mh k| ≤ 2 ^ E := fun k => bnd_arr bA (by decide) (hdl1 k) (hmh1 k)
  have bmuS : ∀ k, |muS k| ≤ 2 ^ E := fun k => bnd_arr bA (by decide) (hdl1 k) (hmuS1 k)
  have bDm : |Dm| ≤ 2 ^ E := bnd_sc (y := sDmu) bS (by decide) hDm
  have bDS : |DS| ≤ 2 ^ E := bnd_sc (y := sDS) bS (by decide) hDS
  have bPF : |PF| ≤ 2 ^ E := bnd_sc (y := s2pF) bS (by decide) (by rw [c3, hPF]; push_cast; rfl)
  have bPq : |Pq| ≤ 2 ^ E := bnd_sc (y := s2p) bS (by decide) (by rw [c2, hPq]; push_cast; rfl)
  have bG : |G| ≤ 2 ^ E := bnd_sc (y := s2g) bS (by decide) (by rw [c4, hG]; push_cast; rfl)
  have blh : |lh| ≤ 2 ^ E := bnd_sc (y := sLamb) bS (by decide) p1
  have beh : |eh| ≤ 2 ^ E := bnd_sc (y := sEps) bS (by decide) p0
  have bΓ : ∀ k, |Γ k| ≤ 2 ^ E := fun k => (gamI_abs_le cs K0 B d t k).trans (pow_mono_z hEB)
  -- R2, the point
  refine XV.seq (XV.r2x hL hlay (σ := σ) (E := E) (Ah := Ah) (ASh := aS) (Γ := Γ) (mh := mh) (Dm := Dm) (PF := PF)
    (P := Pq) (G := G) (lh := lh) vD v1 vz vA vAS hGam vmu vDm vPF vPq vG vlh bAh bAS bΓ bmh bDm bPF bPq bG blh hdE
    (by omega)) fun σ1 ⟨w1, x1, xh1, y1, d1, F1⟩ => ?_
  set xh := xhI mh Ah Γ Dm PF Pq G lh with hxh
  set DX := Dm * PF * Pq * G with hDX
  have n1 : ∀ j, ¬ NR2 j → σ1.nat j = σ.nat j := F1.1
  have s1 : ∀ y, ¬ SR2 y → σ1.sc y = σ.sc y := F1.2.1
  have a1 : ∀ b k, ¬ AR2 b k → σ1.arr b k = σ.arr b k := F1.2.2.1
  have bDX : |DX| ≤ 2 ^ (4 * E) := by
    rw [hDX, show 4 * E = E + E + E + E by ring]
    exact abs_mul_pow (abs_mul_pow (abs_mul_pow bDm bPF) bPq) bG
  have bxh : ∀ k, |xh k| ≤ 2 ^ (5 * E + 2) := fun k => xhI_abs bAh bΓ bmh bDm bPF bPq bG blh hdE k
  have byv : ∀ k, |(aS *ᵥ xh) k| ≤ 2 ^ (7 * E + 2) := fun k =>
    (mulVec_abs_le bAS bxh hdE k).trans (pow_mono_z (by omega))
  -- R2, the gauge
  have hNm := fun r (hr : r < m) j (hj : j ≤ d) => (height_inp (n := n) A b hH hr hj)
  refine XV.seq (XV.r2g hL hlay (σ := σ1) (E := E) (m := m) (Nm := NmI d n m A b) (Dn := DnI d n m A b)
    (Mh := Mh) (DS := DS) (DX := DX) (yv := aS *ᵥ xh) (muS := muS)
    (by rw [n1 _ (by romega), vD]) (by rw [n1 _ (by romega), vM]) (by rw [n1 _ (by romega), v1])
    (by rw [s1 _ (by romega), vz]) (by rw [s1 _ (by romega), vDS]) x1 y1
    (fun k => by rw [a1 _ _ (by romega), vmuS]) hoff hma (fun r _ j _ => by rw [hX]; rfl)
    (fun r _ j _ => by rw [hX]; rfl) (by exact_mod_cast hM1) (fun r hr j hj => (hNm r hr j hj).1)
    (fun r hr j hj => ⟨(hNm r hr j hj).2.1, (hNm r hr j hj).2.2⟩) (by exact_mod_cast hME)
    (by omega) (le_of_abs_le bDS) bDX byv bmuS hdE (by omega)) fun σ2 ⟨g1, g2, d2, F2, bbN, bbD⟩ => ?_
  set bN := (bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh))
    (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX) m).1 with hbN
  set bD := (bestG (gNI (NmI d n m A b) (DnI d n m A b) (aS *ᵥ xh))
    (gDI (NmI d n m A b) (DnI d n m A b) muS DS DX) m).2 with hbD
  have n2 : ∀ j, ¬ NG j → σ2.nat j = σ1.nat j := F2.1
  have s2 : ∀ y, ¬ SG y → σ2.sc y = σ1.sc y := F2.2.1
  have a2 : ∀ b k, ¬ AG b k → σ2.arr b k = σ1.arr b k := F2.2.2.1
  -- R2, the scale and the play buffer
  refine XV.seq (XV.r2p hL hlay (σ := σ2) (E := E) (bN := bN) (bD := bD) (F := PF) (eh := eh) (DS := DS) (DX := DX)
    (yv := aS *ᵥ xh) (muS := muS)
    (by rw [n2 _ (by qomega), n1 _ (by romega), vD]) (by rw [n2 _ (by qomega), n1 _ (by romega), v1])
    (by rw [s2 _ (by qomega), s1 _ (by romega), vz]) g1 g2
    (by rw [s2 _ (by qomega), s1 _ (by romega), vPF]) (by rw [s2 _ (by qomega), s1 _ (by romega), veh])
    (by rw [s2 _ (by qomega), s1 _ (by romega), vDS]) (by rw [s2 _ (by qomega), x1])
    (fun k => by rw [a2 _ _ (by qomega), y1]) (fun k => by rw [a2 _ _ (by qomega), a1 _ _ (by romega), vmuS])
    bbN bbD bPF beh bDS bDX byv bmuS hd1 hℓ) fun σ3 ⟨q1, q2, q3, q4, d3, F3⟩ => ?_
  set pN := (ptPair bN bD PF eh).1 with hpN
  set pD := (ptPair bN bD PF eh).2 with hpD
  -- the pure side: the play
  have hξe : (draw cs K0 B d t).1 = fun i => (Γ i : ℚ) / 2 ^ (2 * gsm_prec B) := by
    rw [draw_eq]
  obtain ⟨hpN0, hpD0, hpt, hpl⟩ := run_play_pure (n := n) A b c S st Dm DS mh muS Γ aS (2 * gsm_prec B) hDm0 hDS0
    hmh2 hmuS2 haS2 (fun i k => (hA i k).2) hlam heps he1 hβ bN bD pN pD rfl rfl
  have hptE : ptE σ3 aPl = toE (playPt cfg (.run st) (draw cs K0 B d t).1) := by
    rw [hξe]
    exact ptE_eq q3 q4 fun j => (hpl j).symm
  obtain ⟨bpN, bpD⟩ := ptPair_abs (T := tG d E) bbN bbD bPF beh
  -- the play
  have n3 : ∀ j, ¬ NP j → σ3.nat j = σ2.nat j := F3.1
  have s3 : ∀ y, ¬ SP y → σ3.sc y = σ2.sc y := F3.2.1
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  have bpl : ∀ j ≤ d, |σ3.arr aPl j| < 2 ^ ℓ := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [q3]
      refine XV.abs_int_lt (lt_of_le_of_lt (abs_mul_pow (abs_mul_pow bDS bDX) bpN) (hℓ2 ?_))
      unfold tG; omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = 1 + k := ⟨j - 1, by omega⟩
      rw [q4 ⟨k, by omega⟩]
      have h1 := abs_mul_pow (abs_mul_pow (bmuS ⟨k, by omega⟩) bDX) bpN
      have h2 := abs_mul_pow (byv ⟨k, by omega⟩) bpD
      have := abs_add_pow (h1.trans (pow_mono_z (show E + 4 * E + (tG d E + E + 1) ≤ 7 * E + 2 + (tG d E + E + 1)
        by omega))) h2
      refine XV.abs_int_lt (lt_of_le_of_lt this (hℓ2 ?_))
      unfold tG; omega
  have hr3 : σ3.rounds = t := by rw [F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1, hr]
  have hp3 : σ3.pts = σ.pts := by rw [F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]
  refine XV.seq (XV.play hL hd1 (σ := σ3) (v := aPl) (by romega) bpl) fun σ4 e4 => ?_
  subst e4
  -- the reading
  have hfb : fbE X { σ3 with rounds := σ3.rounds + 1, pts := Function.update σ3.pts σ3.rounds (ptE σ3 aPl) } =
      X.wb.f t (toE (playPt cfg (.run st) (draw cs K0 B d t).1)) := by
    unfold fbE
    simp only [hr3, Nat.add_sub_cancel, Nat.add_one_ne_zero, ↓reduceIte, Function.update_self, hptE]
  have vP3 : σ3.nat rP = (par d n).p := by
    rw [n3 _ (by pomega), n2 _ (by qomega), n1 _ (by romega), vP]
  refine XV.mono (XV.obs hL (x := sObs) (i := rP) (by r24omega) (by r24omega) (by simp only; rw [vP3]; exact hpℓ)
    (by simp only; rw [vP3]; exact hpa) (by simp only; rw [vP3, hfb]; exact hobs)) le_rfl fun σ5 e5 => ?_
  subst e5
  refine ⟨by simp [hr3], by simp [hr3, hp3, hptE], ?_, ⟨pN, pD, hpN0, hpD0, ?_, ?_, by rw [hξe]; exact hpt, bpN, bpD⟩, ?_,
    by simp [d3, d2, d1], ?_⟩
  · simp only [Env.setSc_sc, ↓reduceIte, vP3, hfb]
  · rw [scO _ (by r24omega)]; exact q1
  · rw [scO _ (by r24omega)]; exact q2
  · intro i
    simp only [Env.setSc_arr]
    rw [F3.2.2.1 _ _ (by pomega), a2 _ _ (by qomega), w1 i]
  · refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_⟩
    · simp only [Env.setSc_nat]
      rw [n3 j (by simp only [N24, NP] at hj ⊢; r24omega), n2 j (by simp only [N24, NG] at hj ⊢; r24omega),
        n1 j (by simp only [N24, NR2] at hj ⊢; r24omega)]
    · simp only [Env.setSc_sc]
      rw [ite_eq_right (by simp only [S24] at hy; r24omega), s3 y (by simp only [S24, SP] at hy ⊢; r24omega),
        s2 y (by simp only [S24, SG] at hy ⊢; r24omega), s1 y (by simp only [S24, SR2] at hy ⊢; r24omega)]
    · simp only [Env.setSc_arr]
      rw [F3.2.2.1 b k (by simp only [A24, AP] at hb ⊢; r24omega), a2 b k (by simp only [A24, AG] at hb ⊢; r24omega),
        a1 b k (by simp only [A24, AR2] at hb ⊢; r24omega)]

end AdversarialBco.Bit.Transfer.BLM
