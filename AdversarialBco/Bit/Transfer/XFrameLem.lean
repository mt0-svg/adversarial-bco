/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# Lemmas of Procedure FRAME

The arithmetic of steps F1 to F3 of `frameQ` (`Bit/RoutQ.lean`): the cleared rows, their bounds by `M̂`, the
comparison of fractions by cross multiplication, and the scan that computes the read-off F2 (`d = 1`) in one pass.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco.Bit.RQ Matrix

/-- One row of the scan of the read-off F2: the index of the largest `β_i/α_i` over `α_i < 0` so far, the index of the
least over `α_i > 0` so far (fractions compared by cross multiplication), and whether a zero row with `β_i < 0` was
seen. -/
def f1step (al be : ℕ → ℤ) (st : Option ℕ × Option ℕ × Bool) (i : ℕ) : Option ℕ × Option ℕ × Bool :=
  (if al i < 0 then
      (match st.1 with
        | none => some i
        | some k => if be k * al i < be i * al k then some i else some k)
    else st.1,
    if 0 < al i then
      (match st.2.1 with
        | none => some i
        | some k => if be i * al k < be k * al i then some i else some k)
    else st.2.1,
    st.2.2 || decide (al i = 0 ∧ be i < 0))

/-- The scan of the first `t` rows. -/
def f1scan (al be : ℕ → ℤ) : ℕ → Option ℕ × Option ℕ × Bool
  | 0 => (none, none, false)
  | t + 1 => f1step al be (f1scan al be t) t

/-- The read-off from the scan. -/
def f1out (al be : ℕ → ℤ) (st : Option ℕ × Option ℕ × Bool) : Option ℚ :=
  match st with
  | (some i, some k, false) =>
    if (be k : ℚ) / al k - be i / al i < 1 then none else some (((be i : ℚ) / al i + be k / al k) / 2)
  | _ => none

theorem frac_lt_iff (a b x y : ℤ) (h : 0 < x * y) :
    ((a : ℚ) / x < b / y ↔ a * y < b * x) := by
  have hpos : (0 : ℚ) < (x : ℚ) * (y : ℚ) := by exact_mod_cast h
  have hx : (x : ℚ) ≠ 0 := by
    intro hx0
    have hx0' : (x : ℤ) = 0 := by exact_mod_cast hx0
    have : x * y = 0 := by simp [hx0']
    linarith
  have hy : (y : ℚ) ≠ 0 := by
    intro hy0
    have hy0' : (y : ℤ) = 0 := by exact_mod_cast hy0
    have : x * y = 0 := by simp [hy0']
    linarith
  constructor
  · intro hlt
    have hlt' : (a : ℚ) * (y : ℚ) < (b : ℚ) * (x : ℚ) := by
      -- multiply hlt by x*y > 0
      have := mul_lt_mul_of_pos_right hlt hpos
      -- this : ((a : ℚ) / x) * (x * y) < (b / y) * (x * y)
      -- simplify both sides
      calc
        (a : ℚ) * (y : ℚ) = ((a : ℚ) / (x : ℚ)) * ((x : ℚ) * (y : ℚ)) := by field_simp [hx]
        _ < ((b : ℚ) / (y : ℚ)) * ((x : ℚ) * (y : ℚ)) := this
        _ = (b : ℚ) * (x : ℚ) := by field_simp [hy]
    exact_mod_cast hlt'
  · intro hlt
    have hlt' : (a : ℚ) * (y : ℚ) < (b : ℚ) * (x : ℚ) := by exact_mod_cast hlt
    calc
      (a : ℚ) / (x : ℚ) = ((a : ℚ) * (y : ℚ)) / ((x : ℚ) * (y : ℚ)) := by field_simp [hx, hy]
      _ < ((b : ℚ) * (x : ℚ)) / ((x : ℚ) * (y : ℚ)) :=
        (div_lt_div_iff_of_pos_right hpos).mpr hlt'
      _ = (b : ℚ) / (y : ℚ) := by field_simp [hx, hy]

theorem mid_eq (bi bk ai ak : ℤ) (hi : ai < 0) (hk : 0 < ak) :
    0 < -2 * ai * ak ∧
      ((bi : ℚ) / ai + bk / ak) / 2 = ((-(bi * ak + bk * ai) : ℤ) : ℚ) / ((-2 * ai * ak : ℤ) : ℚ) := by
  have hpos : 0 < -2 * ai * ak := by
    nlinarith
  have heq : ((bi : ℚ) / ai + bk / ak) / 2 = ((-(bi * ak + bk * ai) : ℤ) : ℚ) / ((-2 * ai * ak : ℤ) : ℚ) := by
    have hai : ai ≠ 0 := by linarith
    have hak : ak ≠ 0 := by linarith
    push_cast
    field_simp [hai, hak]
  exact And.intro hpos heq

theorem frMhat_le {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    1 ≤ frMhat A b ∧ (∀ i j, (A i j).num.natAbs ≤ frMhat A b ∧ (A i j).den ≤ frMhat A b) ∧
      ∀ i, (b i).num.natAbs ≤ frMhat A b ∧ (b i).den ≤ frMhat A b := by
  unfold frMhat
  have h1 : 1 ≤ max 1 (Finset.univ.sup fun (i : Fin m) =>
    max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den)) :=
    Nat.le_max_left _ _
  have h_outer_le_max1 (i : Fin m) : max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den)
      (max (b i).num.natAbs (b i).den) ≤
      max 1 (Finset.univ.sup fun (i : Fin m) =>
        max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den)) :=
    Nat.le_trans (Finset.le_sup (f := fun (i : Fin m) =>
      max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den))
      (Finset.mem_univ i)) (Nat.le_max_right _ _)
  have h_entry_max1 (i : Fin m) (j : Fin d) : max (A i j).num.natAbs (A i j).den ≤
      max 1 (Finset.univ.sup fun (i : Fin m) =>
        max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den)) :=
    Nat.le_trans (Finset.le_sup (f := fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (Finset.mem_univ j))
      (Nat.le_trans (Nat.le_max_left _ _) (h_outer_le_max1 i))
  have h_b_max1 (i : Fin m) : max (b i).num.natAbs (b i).den ≤
      max 1 (Finset.univ.sup fun (i : Fin m) =>
        max (Finset.univ.sup fun (j : Fin d) => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den)) :=
    Nat.le_trans (Nat.le_max_right _ _) (h_outer_le_max1 i)
  refine ⟨h1, ?_, ?_⟩
  · intro i j
    have h := h_entry_max1 i j
    exact ⟨Nat.le_trans (Nat.le_max_left _ _) h, Nat.le_trans (Nat.le_max_right _ _) h⟩
  · intro i
    have h := h_b_max1 i
    exact ⟨Nat.le_trans (Nat.le_max_left _ _) h, Nat.le_trans (Nat.le_max_right _ _) h⟩

theorem frDen_dvd {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (i : Fin m) : 0 < frDen A b i ∧ (∀ j, (A i j).den ∣ frDen A b i) ∧ (b i).den ∣ frDen A b i := by
  have hpos_den : ∀ (x : ℚ), 0 < x.den := Rat.den_pos
  have hpos_prod : 0 < ∏ j : Fin d, (A i j).den :=
    Finset.prod_pos fun j _ => hpos_den _
  have hpos_frDen : 0 < frDen A b i := by
    dsimp [frDen]
    exact mul_pos hpos_prod (hpos_den _)
  have h_dvd_entry (j : Fin d) : (A i j).den ∣ frDen A b i := by
    dsimp [frDen]
    refine dvd_mul_of_dvd_left ?_ (b i).den
    exact Finset.dvd_prod_of_mem (fun x => (A i x).den) (Finset.mem_univ j)
  have h_dvd_b : (b i).den ∣ frDen A b i := by
    dsimp [frDen]
    exact dvd_mul_of_dvd_right (dvd_refl (b i).den) (∏ j : Fin d, (A i j).den)
  exact ⟨hpos_frDen, h_dvd_entry, h_dvd_b⟩

theorem frAl_le {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (i : Fin m) : frDen A b i ≤ frMhat A b ^ (d + 1) ∧ (∀ j, |frAl A b i j| ≤ (frMhat A b : ℤ) ^ (d + 1)) ∧
      |frBe A b i| ≤ (frMhat A b : ℤ) ^ (d + 1) := by
  set M := frMhat A b with hM
  have hM_one : 1 ≤ M := (frMhat_le A b).1
  have hM_pos : 0 < M := by omega
  have hA_num : ∀ i j, (A i j).num.natAbs ≤ M := fun i j => (frMhat_le A b).2.1 i j |>.1
  have hA_den : ∀ i j, (A i j).den ≤ M := fun i j => (frMhat_le A b).2.1 i j |>.2
  have hb_num : ∀ i, (b i).num.natAbs ≤ M := fun i => (frMhat_le A b).2.2 i |>.1
  have hb_den : ∀ i, (b i).den ≤ M := fun i => (frMhat_le A b).2.2 i |>.2
  have hDen_pos : 0 < frDen A b i := (frDen_dvd A b i).1
  have hA_den_dvd : ∀ j, (A i j).den ∣ frDen A b i := (frDen_dvd A b i).2.1
  have hb_den_dvd : (b i).den ∣ frDen A b i := (frDen_dvd A b i).2.2
  have hcard_univ : (Finset.univ : Finset (Fin d)).card = d := Finset.card_fin d
  -- Part 1: frDen A b i ≤ M ^ (d + 1)
  have hDen_le : frDen A b i ≤ M ^ (d + 1) := by
    dsimp [frDen]
    have hprod : (∏ j : Fin d, (A i j).den) ≤ M ^ d := by
      calc
        (∏ j : Fin d, (A i j).den) = ∏ j ∈ (Finset.univ : Finset (Fin d)), (A i j).den := by simp
        _ ≤ M ^ ((Finset.univ : Finset (Fin d)).card) :=
          Finset.prod_le_pow_card (Finset.univ : Finset (Fin d)) (fun j => (A i j).den) M
            (fun j hj => hA_den i j)
        _ = M ^ d := by simp [Finset.card_fin d]
    have hb_den_le : (b i).den ≤ M := hb_den i
    calc
      (∏ j : Fin d, (A i j).den) * (b i).den ≤ M ^ d * M := Nat.mul_le_mul hprod hb_den_le
      _ = M ^ (d + 1) := by ring
  -- Part 2: ∀ j, |frAl A b i j| ≤ (M : ℤ) ^ (d + 1)
  have hAl : ∀ j, |frAl A b i j| ≤ (M : ℤ) ^ (d + 1) := by
    intro j
    have hd_pos : 1 ≤ d := by
      have : Nonempty (Fin d) := ⟨j⟩
      have hcard_pos : 0 < Fintype.card (Fin d) := Fintype.card_pos
      have hcard_eq : Fintype.card (Fin d) = d := Fintype.card_fin d
      omega
    dsimp [frAl, clr]
    -- frAl A b i j = (A i j).num * ((frDen A b i / (A i j).den : ℕ) : ℤ)
    have h_div_le : frDen A b i / (A i j).den ≤ M ^ d := by
      apply Nat.div_le_of_le_mul
      dsimp [frDen]
      have hprod_erase : (∏ j' : Fin d, (A i j').den) =
          (A i j).den * (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) := by
        calc
          (∏ j' : Fin d, (A i j').den) = ∏ j' ∈ (Finset.univ : Finset (Fin d)), (A i j').den := by simp
          _ = (A i j).den * (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) := by
            rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin d)) (fun j' => (A i j').den) (Finset.mem_univ j)]
      rw [hprod_erase]
      have hprod_erase_le : (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) ≤ M ^ (d - 1) := by
        calc
          (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) ≤
              M ^ (((Finset.univ : Finset (Fin d)).erase j).card) :=
            Finset.prod_le_pow_card ((Finset.univ : Finset (Fin d)).erase j) (fun j' => (A i j').den) M
              (fun j' hj => hA_den i j')
          _ = M ^ (d - 1) := by
            have hcard_erase : ((Finset.univ : Finset (Fin d)).erase j).card = d - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ j), hcard_univ]
            rw [hcard_erase]
      have hb_den_le : (b i).den ≤ M := hb_den i
      have hprod_mul_le : (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) * (b i).den ≤ M ^ (d - 1) * M :=
        Nat.mul_le_mul hprod_erase_le hb_den_le
      have h_pow_eq : M ^ (d - 1) * M = M ^ d := by
        calc
          M ^ (d - 1) * M = M ^ ((d - 1) + 1) := by rw [Nat.pow_succ]
          _ = M ^ d := by rw [Nat.sub_add_cancel hd_pos]
      calc
        ((A i j).den * (∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den)) * (b i).den =
            (A i j).den * ((∏ j' ∈ (Finset.univ : Finset (Fin d)).erase j, (A i j').den) * (b i).den) := by ring
        _ ≤ (A i j).den * (M ^ (d - 1) * M) := Nat.mul_le_mul_left _ hprod_mul_le
        _ = (A i j).den * (M ^ d) := by rw [h_pow_eq]
    have h_num_natAbs_le : ((A i j).num.natAbs : ℤ) ≤ (M : ℤ) := by
      exact mod_cast hA_num i j
    have h_div_nat_le : ((frDen A b i / (A i j).den : ℕ) : ℤ) ≤ (M ^ d : ℤ) := by
      exact mod_cast h_div_le
    calc
      |(A i j).num * ((frDen A b i / (A i j).den : ℕ) : ℤ)| =
          |(A i j).num| * |((frDen A b i / (A i j).den : ℕ) : ℤ)| := by rw [abs_mul]
      _ = ((A i j).num.natAbs : ℤ) * |((frDen A b i / (A i j).den : ℕ) : ℤ)| := by
        rw [Int.abs_eq_natAbs]
      _ = ((A i j).num.natAbs : ℤ) * ((frDen A b i / (A i j).den : ℕ) : ℤ) := by
        rw [abs_of_nonneg (by exact mod_cast Nat.zero_le _)]
      _ ≤ (M : ℤ) * ((frDen A b i / (A i j).den : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_right h_num_natAbs_le (by exact mod_cast Nat.zero_le _)
      _ ≤ (M : ℤ) * (M ^ d : ℤ) :=
        mul_le_mul_of_nonneg_left h_div_nat_le (by exact mod_cast Nat.zero_le M)
      _ = (M : ℤ) ^ (d + 1) := by
        rw [← pow_succ']
  -- Part 3: |frBe A b i| ≤ (M : ℤ) ^ (d + 1)
  have hBe : |frBe A b i| ≤ (M : ℤ) ^ (d + 1) := by
    dsimp [frBe, clr]
    -- frBe A b i = (b i).num * ((frDen A b i / (b i).den : ℕ) : ℤ)
    have h_div_le : frDen A b i / (b i).den ≤ M ^ d := by
      apply Nat.div_le_of_le_mul
      dsimp [frDen]
      have hprod_le : (∏ j : Fin d, (A i j).den) ≤ M ^ d := by
        calc
          (∏ j : Fin d, (A i j).den) = ∏ j ∈ (Finset.univ : Finset (Fin d)), (A i j).den := by simp
          _ ≤ M ^ ((Finset.univ : Finset (Fin d)).card) :=
            Finset.prod_le_pow_card (Finset.univ : Finset (Fin d)) (fun j => (A i j).den) M
              (fun j hj => hA_den i j)
          _ = M ^ d := by simp [Finset.card_fin d]
      have hb_den_le : (b i).den ≤ M := hb_den i
      -- frDen = (∏ j, (A i j).den) * (b i).den ≤ M ^ d * M
      -- But we need frDen ≤ (b i).den * M ^ d
      -- Since (b i).den divides frDen, we have frDen = (b i).den * (frDen / (b i).den)
      -- And frDen / (b i).den = ∏ j, (A i j).den
      -- So frDen = (b i).den * (∏ j, (A i j).den) ≤ (b i).den * M ^ d
      -- Let's use this approach:
      -- target: (∏ j, (A i j).den) * (b i).den ≤ (b i).den * M ^ d
      -- rewrite LHS as (b i).den * (∏ j, (A i j).den) by commutativity
      rw [mul_comm]
      exact Nat.mul_le_mul_left (b i).den hprod_le
    have h_num_natAbs_le : ((b i).num.natAbs : ℤ) ≤ (M : ℤ) := by
      exact mod_cast hb_num i
    have h_div_nat_le : ((frDen A b i / (b i).den : ℕ) : ℤ) ≤ (M ^ d : ℤ) := by
      exact mod_cast h_div_le
    calc
      |(b i).num * ((frDen A b i / (b i).den : ℕ) : ℤ)| =
          |(b i).num| * |((frDen A b i / (b i).den : ℕ) : ℤ)| := by rw [abs_mul]
      _ = ((b i).num.natAbs : ℤ) * |((frDen A b i / (b i).den : ℕ) : ℤ)| := by
        rw [Int.abs_eq_natAbs]
      _ = ((b i).num.natAbs : ℤ) * ((frDen A b i / (b i).den : ℕ) : ℤ) := by
        rw [abs_of_nonneg (by exact mod_cast Nat.zero_le _)]
      _ ≤ (M : ℤ) * ((frDen A b i / (b i).den : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_right h_num_natAbs_le (by exact mod_cast Nat.zero_le _)
      _ ≤ (M : ℤ) * (M ^ d : ℤ) :=
        mul_le_mul_of_nonneg_left h_div_nat_le (by exact mod_cast Nat.zero_le M)
      _ = (M : ℤ) ^ (d + 1) := by
        rw [← pow_succ']
  exact ⟨hDen_le, hAl, hBe⟩

theorem gap_lt_iff (bi bk ai ak : ℤ) (hi : ai < 0) (hk : 0 < ak) :
    ((bk : ℚ) / ak - bi / ai < 1 ↔ ai * ak < bk * ai - bi * ak) := by
  have ha_ne_zero : (ai : ℚ) ≠ 0 := by exact mod_cast (ne_of_lt hi)
  have hk_ne_zero : (ak : ℚ) ≠ 0 := by exact mod_cast ((ne_of_lt hk).symm)
  have ha_neg : (ai : ℚ) < 0 := by exact mod_cast hi
  have hk_pos : (0 : ℚ) < ak := by exact mod_cast hk
  have h_denom_neg : (ak : ℚ) * (ai : ℚ) < 0 := mul_neg_of_pos_of_neg hk_pos ha_neg
  constructor
  · intro h
    field_simp [ha_ne_zero, hk_ne_zero] at h
    -- h : (↑bk * ↑ai - ↑ak * ↑bi) / ↑ai < ↑ak
    have h_div := (div_lt_iff_of_neg ha_neg).mp h
    -- h_div : ↑ak * ↑ai < ↑bk * ↑ai - ↑ak * ↑bi
    have h_goal_ℚ : (ai : ℚ) * (ak : ℚ) < (bk : ℚ) * (ai : ℚ) - (bi : ℚ) * (ak : ℚ) := by linarith
    exact_mod_cast h_goal_ℚ
  · intro h
    -- h : ai * ak < bk * ai - bi * ak
    have h_ℚ : (ai : ℚ) * (ak : ℚ) < (bk : ℚ) * (ai : ℚ) - (bi : ℚ) * (ak : ℚ) := by exact mod_cast h
    have h_div : (ak : ℚ) * (ai : ℚ) < (bk : ℚ) * (ai : ℚ) - (bi : ℚ) * (ak : ℚ) := by linarith
    field_simp [ha_ne_zero, hk_ne_zero]
    -- Goal: (↑bk * ↑ai - ↑ak * ↑bi) / ↑ai < ↑ak
    rw [div_lt_iff_of_neg ha_neg]
    -- Goal: ↑ak * ↑ai < ↑bk * ↑ai - ↑ak * ↑bi
    simpa [mul_comm] using h_div

theorem frMhat_flat {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    frMhat A b = max 1 ((Finset.range (m * (d + 1))).sup fun e =>
      if h : e / (d + 1) < m then
        max (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
          (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den
      else 0) := by
  have hpos : 0 < d + 1 := by omega
  apply le_antisymm
  · -- frMhat A b ≤ RHS
    unfold frMhat
    apply max_le_max
    · exact le_rfl
    · refine Finset.sup_le fun i hi => ?_
      apply max_le
      · refine Finset.sup_le fun j hj => ?_
        have hi_val : (i : ℕ) < m := i.2
        have hj_val : (j : ℕ) < d := j.2
        set e := (d + 1) * (i : ℕ) + (j : ℕ) with he_def
        have he_lt : e < m * (d + 1) := by
          rw [he_def]
          nlinarith
        have he_div_eq : e / (d + 1) = (i : ℕ) := by
          rw [he_def]
          rw [add_comm, Nat.add_mul_div_left (j : ℕ) (i : ℕ) hpos]
          have hj_lt_d1 : (j : ℕ) < d + 1 := by omega
          rw [Nat.div_eq_of_lt hj_lt_d1]
          simp
        have he_mod_eq : e % (d + 1) = (j : ℕ) := by
          rw [he_def]
          rw [add_comm, Nat.add_mul_mod_self_left]
          have hj_lt_d1 : (j : ℕ) < d + 1 := by omega
          rw [Nat.mod_eq_of_lt hj_lt_d1]
        have h_fin_eq : ⟨e / (d + 1), by rw [he_div_eq]; exact hi_val⟩ = i := by
          ext; exact he_div_eq
        have h_entry : AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), by rw [he_div_eq]; exact hi_val⟩ (e % (d + 1)) = A i j := by
          rw [h_fin_eq, he_mod_eq]
          dsimp [AdversarialBco.BitRAM.entry]
          simp [hj_val]
        have hmem : e ∈ Finset.range (m * (d + 1)) := by
          rw [Finset.mem_range]; exact he_lt
        have hcond : e / (d + 1) < m := by rw [he_div_eq]; exact hi_val
        have h_sup := Finset.le_sup (f := fun e => if h : e / (d + 1) < m then max (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
          (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den else 0) hmem
        simpa [hcond, h_entry] using h_sup
      · have hi_val : (i : ℕ) < m := i.2
        set e := (d + 1) * (i : ℕ) + d with he_def
        have he_lt : e < m * (d + 1) := by
          rw [he_def]
          nlinarith
        have he_div_eq : e / (d + 1) = (i : ℕ) := by
          rw [he_def]
          rw [add_comm, Nat.add_mul_div_left d (i : ℕ) hpos]
          have hd_lt_d1 : d < d + 1 := by omega
          rw [Nat.div_eq_of_lt hd_lt_d1]
          simp
        have he_mod_eq : e % (d + 1) = d := by
          rw [he_def]
          rw [add_comm, Nat.add_mul_mod_self_left]
          have hd_lt_d1 : d < d + 1 := by omega
          rw [Nat.mod_eq_of_lt hd_lt_d1]
        have h_fin_eq : ⟨e / (d + 1), by rw [he_div_eq]; exact hi_val⟩ = i := by
          ext; exact he_div_eq
        have h_entry : AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), by rw [he_div_eq]; exact hi_val⟩ (e % (d + 1)) = b i := by
          rw [h_fin_eq, he_mod_eq]
          dsimp [AdversarialBco.BitRAM.entry]
          simp
        have hmem : e ∈ Finset.range (m * (d + 1)) := by
          rw [Finset.mem_range]; exact he_lt
        have hcond : e / (d + 1) < m := by rw [he_div_eq]; exact hi_val
        have h_sup := Finset.le_sup (f := fun e => if h : e / (d + 1) < m then max (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
          (AdversarialBco.BitRAM.entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den else 0) hmem
        simpa [hcond, h_entry] using h_sup
  · -- RHS ≤ frMhat A b
    unfold frMhat
    apply max_le_max
    · exact le_rfl
    · refine Finset.sup_le fun e he => ?_
      rw [Finset.mem_range] at he
      split_ifs with hdiv
      · let i : Fin m := ⟨e / (d + 1), hdiv⟩
        let j : ℕ := e % (d + 1)
        have hj_lt : j < d + 1 := Nat.mod_lt e hpos
        by_cases hj_lt_d : j < d
        · have h_entry : AdversarialBco.BitRAM.entry A b i j = A i ⟨j, hj_lt_d⟩ := by
            dsimp [AdversarialBco.BitRAM.entry]
            simp [hj_lt_d]
          rw [h_entry]
          have hmem_j : (⟨j, hj_lt_d⟩ : Fin d) ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
          have hle_j := Finset.le_sup (f := fun (k : Fin d) => max (A i k).num.natAbs (A i k).den) hmem_j
          have hle_i : Finset.univ.sup (fun (k : Fin d) => max (A i k).num.natAbs (A i k).den) ≤
            Finset.univ.sup (fun (i' : Fin m) => max (Finset.univ.sup (fun (j' : Fin d) => max (A i' j').num.natAbs (A i' j').den))
              (max (b i').num.natAbs (b i').den)) := by
            refine Finset.sup_le fun k hk => ?_
            have hk_sup : max (A i k).num.natAbs (A i k).den ≤
              Finset.univ.sup (fun (j' : Fin d) => max (A i j').num.natAbs (A i j').den) :=
              Finset.le_sup (f := fun (j' : Fin d) => max (A i j').num.natAbs (A i j').den) hk
            have hk_max : Finset.univ.sup (fun (j' : Fin d) => max (A i j').num.natAbs (A i j').den) ≤
              max (Finset.univ.sup (fun (j' : Fin d) => max (A i j').num.natAbs (A i j').den))
                (max (b i).num.natAbs (b i).den) := le_max_left _ _
            have hi_sup : max (Finset.univ.sup (fun (j' : Fin d) => max (A i j').num.natAbs (A i j').den))
                (max (b i).num.natAbs (b i).den) ≤
              Finset.univ.sup (fun (i' : Fin m) => max (Finset.univ.sup (fun (j' : Fin d) => max (A i' j').num.natAbs (A i' j').den))
                (max (b i').num.natAbs (b i').den)) :=
              Finset.le_sup (f := fun (i' : Fin m) => max (Finset.univ.sup (fun (j' : Fin d) => max (A i' j').num.natAbs (A i' j').den))
                (max (b i').num.natAbs (b i').den)) (Finset.mem_univ i)
            exact le_trans hk_sup (le_trans hk_max hi_sup)
          exact le_trans hle_j hle_i
        · have h_entry : AdversarialBco.BitRAM.entry A b i j = b i := by
            dsimp [AdversarialBco.BitRAM.entry]
            simp [hj_lt_d]
          rw [h_entry]
          have hle_i := Finset.le_sup (f := fun (i' : Fin m) => max (Finset.univ.sup (fun (j' : Fin d) => max (A i' j').num.natAbs (A i' j').den))
            (max (b i').num.natAbs (b i').den)) (Finset.mem_univ i)
          exact le_trans (le_max_right _ _) hle_i
      · exact Nat.zero_le _

end AdversarialBco.Bit.Transfer
