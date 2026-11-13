/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrame1

@[expose] public section

/-!
# Procedure FRAME on the machine for `d ≥ 2`: `M̂` and `e_R`

`xmhScan` computes `M̂ = frMhat A b` from the input cells of `ctxOf`, as the largest `|cell|` over the cells of the
rows, at least `1` (`frMhat_cells`). `xpowS` is the power `x^k` by `k` products. `xfrE0` then computes
`e_R = frER d m M̂` in a register, with `j = 1` and `λ = e_R + 1`, the registers that `xellSetR` reads.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## `M̂` over the input cells -/

/-- The largest `|cell|` over the first `t` cells of the rows. -/
def mhV (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (t : ℕ) : ℕ :=
  (Finset.range t).sup fun c => (BitRAM.inputMem d n m A b ((3 + c : ℕ) : ℤ)).natAbs

open BitRAM BitRAM.Conj1BitSanity in
theorem frMhat_cells {d n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    frMhat A b = max 1 ((Finset.range (2 * ((d + 1) * m))).sup fun c =>
      (BitRAM.inputMem d n m A b ((3 + c : ℕ) : ℤ)).natAbs) := by
  rw [frMhat_flat]
  congr 1
  apply le_antisymm
  · -- sup over range (m*(d+1)) ≤ sup over range (2*((d+1)*m))
    apply Finset.sup_le
    intro e he
    rw [Finset.mem_range] at he
    have he_bound : e < m * (d + 1) := he
    have h_entry_row : e / (d + 1) < m := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      exact he_bound
    have h_entry_col : e % (d + 1) ≤ d := by
      have h := Nat.mod_lt e (by omega : 0 < d + 1)
      omega
    have h_eq_num : (3 + 2 * e : ℕ) = (3 + 2 * ((d + 1) * (e / (d + 1)) + e % (d + 1)) : ℕ) := by
      rw [Nat.div_add_mod e (d + 1)]
    have h_eq_den : (4 + 2 * e : ℕ) = (4 + 2 * ((d + 1) * (e / (d + 1)) + e % (d + 1)) : ℕ) := by
      rw [Nat.div_add_mod e (d + 1)]
    have hc1_lt : 2 * e < 2 * ((d + 1) * m) := by
      have : e < (d + 1) * m := by
        rw [mul_comm]; exact he_bound
      omega
    have hc2_lt : 2 * e + 1 < 2 * ((d + 1) * m) := by
      have : e < (d + 1) * m := by
        rw [mul_comm]; exact he_bound
      omega
    have h_term_eq : (if h : e / (d + 1) < m then
      max (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
        (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den
      else 0) = max ((inputMem d n m A b ((3 + (2 * e) : ℕ) : ℤ)).natAbs)
        ((inputMem d n m A b ((3 + (2 * e + 1) : ℕ) : ℤ)).natAbs) := by
      have hpos : (e / (d + 1)) < m := h_entry_row
      rw [dite_eq_left hpos]
      have hnum := inputMem_num (n := n) A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1)) h_entry_col
      have hden := inputMem_den (n := n) A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1)) h_entry_col
      -- hnum: inputMem ... (3 + 2*((d+1)*i + j) : ℕ) = (entry ...).num
      -- hden: inputMem ... (4 + 2*((d+1)*i + j) : ℕ) = (entry ...).den
      -- We need to rewrite the inputMem calls to use the same form
      have h1 : (inputMem d n m A b ((3 + (2 * e) : ℕ) : ℤ)) = (entry A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1))).num := by
        rw [h_eq_num]; exact hnum
      have h2 : (inputMem d n m A b ((3 + (2 * e + 1) : ℕ) : ℤ)) = ((entry A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1))).den : ℤ) := by
        have : (3 + (2 * e + 1) : ℕ) = (4 + 2 * e : ℕ) := by omega
        rw [this, h_eq_den]; exact hden
      rw [h1, h2]
      simp
    rw [h_term_eq]
    apply max_le
    · apply Finset.le_sup (f := fun c => (inputMem d n m A b ((3 + c : ℕ) : ℤ)).natAbs)
      rw [Finset.mem_range]
      exact hc1_lt
    · apply Finset.le_sup (f := fun c => (inputMem d n m A b ((3 + c : ℕ) : ℤ)).natAbs)
      rw [Finset.mem_range]
      exact hc2_lt
  · -- sup over range (2*((d+1)*m)) ≤ sup over range (m*(d+1))
    apply Finset.sup_le
    intro c hc
    rw [Finset.mem_range] at hc
    have hc_bound : c < 2 * ((d + 1) * m) := hc
    set e := c / 2 with he_def
    set r := c % 2 with hr_def
    have hc_eq : c = 2 * e + r := by
      rw [he_def, hr_def]
      exact (Nat.div_add_mod c 2).symm
    have hr_lt_2 : r < 2 := Nat.mod_lt c (by omega)
    have hr_le_1 : r ≤ 1 := by omega
    have he_lt : e < m * (d + 1) := by
      rw [he_def]
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      calc
        c < 2 * ((d + 1) * m) := hc_bound
        _ = (m * (d + 1)) * 2 := by ring
    have h_entry_row : e / (d + 1) < m := by
      apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
      exact he_lt
    have h_entry_col : e % (d + 1) ≤ d := by
      have h := Nat.mod_lt e (by omega : 0 < d + 1)
      omega
    -- We need to relate the cell at c to the flat entry at e
    -- c = 2*e + r where r ∈ {0,1}
    -- The cell value at c is either |num| or den of the entry at e
    -- Both are ≤ max |num| den of the entry at e
    -- And the flat entry at e is max |num| den
    -- So the cell value ≤ flat value
    -- But we need to show it's ≤ sup of flat values
    -- Since e is in range (m*(d+1)), the flat value at e ≤ sup
    -- So cell value ≤ flat value at e ≤ sup
    have h_flat_term_le_sup : (if h : e / (d + 1) < m then
      max (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
        (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den
      else 0) ≤
      (Finset.range (m * (d + 1))).sup fun e' =>
        (if h : e' / (d + 1) < m then
          max (entry A b ⟨e' / (d + 1), h⟩ (e' % (d + 1))).num.natAbs
            (entry A b ⟨e' / (d + 1), h⟩ (e' % (d + 1))).den
          else 0) := by
      apply Finset.le_sup (f := fun e' =>
        (if h : e' / (d + 1) < m then
          max (entry A b ⟨e' / (d + 1), h⟩ (e' % (d + 1))).num.natAbs
            (entry A b ⟨e' / (d + 1), h⟩ (e' % (d + 1))).den
          else 0))
      rw [Finset.mem_range]
      exact he_lt
    -- Now relate the cell value to the flat value at e
    -- We need to show: (inputMem ... ((3 + c : ℕ) : ℤ)).natAbs ≤ flat_term_at_e
    -- And then combine with h_flat_term_le_sup
    have h_cell_le_flat : (inputMem d n m A b ((3 + c : ℕ) : ℤ)).natAbs ≤
      (if h : e / (d + 1) < m then
        max (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).num.natAbs
          (entry A b ⟨e / (d + 1), h⟩ (e % (d + 1))).den
        else 0) := by
      rw [hc_eq]
      -- c = 2*e + r, so we need to consider r = 0 or r = 1
      -- Since r < 2, r is 0 or 1
      have hr_cases : r = 0 ∨ r = 1 := by omega
      rcases hr_cases with (hr | hr)
      · -- r = 0: cell is 3 + 2*e
        rw [hr, add_zero]
        -- Need: (inputMem ... ((3 + 2*e : ℕ) : ℤ)).natAbs ≤ flat_term
        have h_eq_num : (3 + 2 * e : ℕ) = (3 + 2 * ((d + 1) * (e / (d + 1)) + e % (d + 1)) : ℕ) := by
          rw [Nat.div_add_mod e (d + 1)]
        rw [h_eq_num]
        have hpos : (e / (d + 1)) < m := h_entry_row
        rw [dite_eq_left hpos]
        have hnum := inputMem_num (n := n) A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1)) h_entry_col
        rw [hnum]
        -- Now: (entry ...).num.natAbs ≤ max (entry ...).num.natAbs (entry ...).den
        apply le_max_left
      · -- r = 1: cell is 4 + 2*e
        rw [hr]
        -- c = 2*e + 1, so 3 + c = 3 + (2*e + 1) = 4 + 2*e
        -- Need: (inputMem ... ((3 + (2*e + 1) : ℕ) : ℤ)).natAbs ≤ flat_term
        have h_eq_den : (4 + 2 * e : ℕ) = (4 + 2 * ((d + 1) * (e / (d + 1)) + e % (d + 1)) : ℕ) := by
          rw [Nat.div_add_mod e (d + 1)]
        have : (3 + (2 * e + 1) : ℕ) = (4 + 2 * e : ℕ) := by omega
        rw [this, h_eq_den]
        have hpos : (e / (d + 1)) < m := h_entry_row
        rw [dite_eq_left hpos]
        have hden := inputMem_den (n := n) A b ⟨e / (d + 1), h_entry_row⟩ (e % (d + 1)) h_entry_col
        rw [hden]
        -- Now: ((entry ...).den : ℤ).natAbs ≤ max (entry ...).num.natAbs (entry ...).den
        -- The denominator is nonnegative, so natAbs of the cast is the denominator itself
        simp
    -- Now combine: cell ≤ flat ≤ sup
    exact le_trans h_cell_le_flat h_flat_term_le_sup

theorem mhV_zero {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : mhV d n m A b 0 = 0 := by
  simp [mhV]

theorem mhV_succ {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (t : ℕ) :
    mhV d n m A b (t + 1) = max (mhV d n m A b t) (BitRAM.inputMem d n m A b ((3 + t : ℕ) : ℤ)).natAbs := by
  unfold mhV
  rw [Finset.range_add_one, Finset.sup_insert, max_comm]

theorem mhV_le {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {t : ℕ} (ht : t ≤ 2 * ((d + 1) * m)) :
    mhV d n m A b t ≤ frMhat A b := by
  rw [frMhat_cells (n := n)]
  exact le_max_of_le_right (Finset.sup_mono (Finset.range_mono ht))

theorem cell_le {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {t : ℕ} (ht : t < 2 * ((d + 1) * m)) :
    (BitRAM.inputMem d n m A b ((3 + t : ℕ) : ℤ)).natAbs ≤ frMhat A b := by
  have h := mhV_le (n := n) A b (Nat.succ_le_of_lt ht)
  rw [mhV_succ] at h
  exact (le_max_right _ _).trans h

theorem natAbs_cast_abs (x : ℤ) : |(x : ℝ)| = ((x.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]; rfl

/-! ## The scan on the machine -/

/-- One cell: `sT := inp(nat nA)`, `sT := |sT|`, `sM := max sM sT`, `nA := nA + 1` (`u` holds `0`). -/
def xmhCell (L : Layout) (u sM sT nA one : ℕ) : XCmd :=
  .seq (xrdIn L sT nA) (.seq (xifS L sT u (toX (VL.sop2 L .sub sT u sT)) .skip)
    (.seq (xifS L sM sT (xset L sM sT u) .skip) (.prim (.frag (.nadd nA nA one)))))

/-- The scan: `nK := 2 (d + 1) m`, `sM := 1`, `nA := 3`, one turn per cell of the rows. -/
def xmhScan (L : Layout) (rd rm u sM sT nA nK nk one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nadd nK rd one))) (.seq (xnmul nK nK rm) (.seq (.prim (.frag (.nadd nK nK nK)))
  (.seq (toX (VL.sconst L sM 1)) (.seq (.prim (.frag (.nconst nA 3)))
    (xforN nk nK one (xmhCell L u sM sT nA one))))))

set_option maxHeartbeats 2000000 in
/-- The rule of `xmhCell`: the cell `3 + t` joins the maximum. -/
theorem XV.mhCell {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u sM sT nA one t : ℕ}
    (hu : u < L.NS) (hsM : sM < L.NS) (hsT : sT < L.NS) (huT : u ≠ sT) (hMT : sM ≠ sT)
    (hnA : nA < L.NN) (hone : one < L.NN)
    (hz : σ.sc u = 0) (h1 : σ.nat one = 1) (hA : σ.nat nA = 3 + t) (ht : t < 2 * ((d + 1) * m))
    (hM : σ.sc sM = ((max 1 (mhV d n m A b t) : ℕ) : ℝ)) (hta : 3 + t + 1 < 2 ^ ℓa)
    (hb : (frMhat A b : ℝ) < 2 ^ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xmhCell L u sM sT nA one) σ 6 (fun σ' =>
      σ'.sc sM = ((max 1 (mhV d n m A b (t + 1)) : ℕ) : ℝ) ∧ σ'.nat nA = 3 + (t + 1) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sM ∨ y = sT) (fun j => j = nA) (fun _ _ => False) σ σ') := by
  set x : ℤ := BitRAM.inputMem d n m A b ((3 + t : ℕ) : ℤ) with hx
  have hxM : x.natAbs ≤ frMhat A b := cell_le A b ht
  have hMt : max 1 (mhV d n m A b t) ≤ frMhat A b := max_le (frMhat_le A b).1 (mhV_le A b ht.le)
  have bx : |(x : ℝ)| < 2 ^ ℓ := by
    rw [natAbs_cast_abs]; exact lt_of_le_of_lt (by exact_mod_cast hxM) hb
  have bxa : |((x.natAbs : ℕ) : ℝ)| < 2 ^ ℓ := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact lt_of_le_of_lt (by exact_mod_cast hxM) hb
  have bM : |((max 1 (mhV d n m A b t) : ℕ) : ℝ)| < 2 ^ ℓ := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact lt_of_le_of_lt (by exact_mod_cast hMt) hb
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have hoff : σ.nat nA < (ctxOf w n m A b).off := by
    show σ.nat nA < offOf d m
    unfold offOf; rw [hA, show 2 * (d + 1) * m = 2 * ((d + 1) * m) by ring]; omega
  refine XV.seq (K₂ := 5) (XV.rdIn hL (x := sT) (i := nA) hsT hnA hoff (by omega) (by rw [hA]; exact bx))
    fun σ1 e1 => ?_
  subst e1
  have s1 : (σ.setSc sT ((ctxOf w n m A b).inp (σ.nat nA) : ℝ)).sc sT = (x : ℝ) := by
    simp only [Env.setSc_sc, ite_true]; rw [hA]; rfl
  set σ1 := σ.setSc sT ((ctxOf w n m A b).inp (σ.nat nA) : ℝ) with hσ1
  have z1 : σ1.sc u = 0 := by rw [hσ1, sc_setSc_ne _ huT, hz]
  have F1 : FrameA (fun y => y = sT) (fun _ => False) (fun _ _ => False) σ σ1 :=
    (FrameA.refl (fun y => y = sT) (fun _ => False) (fun _ _ => False) σ).setSc rfl _
  -- `sT := |x|`
  refine XV.seq (K₁ := 2) (K₂ := 3) (Q₁ := fun σ2 => σ2.sc sT = ((x.natAbs : ℕ) : ℝ) ∧ σ2.draws = σ.draws ∧
    FrameA (fun y => y = sT) (fun _ => False) (fun _ _ => False) σ σ2) ?_ fun σ2 ⟨s2, d2, F2⟩ => ?_
  · by_cases hx0 : x < 0
    · refine XV.ifS_t hL hsT hu (by rw [s1]; exact bx) (by rw [z1]; exact h0)
        (by rw [s1, z1]; exact_mod_cast hx0) (XV.mono (XV.subI hL (u := 0) (v := x) hsT hu hsT
          (by rw [z1]; simp) s1 (by simp) (by exact_mod_cast bx)
          (by rw [zero_sub, abs_neg]; exact_mod_cast bx)) le_rfl fun σ' e => ?_)
      subst e
      refine ⟨?_, by simp [hσ1], F1.setSc rfl _⟩
      simp only [Env.setSc_sc, ite_true]
      have : ((x.natAbs : ℕ) : ℤ) = 0 - x := by rw [Int.natCast_natAbs, abs_of_neg hx0]; ring
      rw [← this, Int.cast_natCast]
    · refine XV.ifS_f hL hsT hu (by rw [s1]; exact bx) (by rw [z1]; exact h0)
        (by rw [s1, z1]; exact_mod_cast hx0) (XV.mono (XV.skip _) le_rfl fun σ' e => ?_)
      subst e
      refine ⟨?_, by simp [hσ1], F1⟩
      rw [s1]
      have : ((x.natAbs : ℕ) : ℤ) = x := Int.natAbs_of_nonneg (not_lt.1 hx0)
      rw [← Int.cast_natCast, this]
  -- `sM := max sM sT`
  have M2 : σ2.sc sM = ((max 1 (mhV d n m A b t) : ℕ) : ℝ) := by rw [F2.2.1 _ hMT, hM]
  have z2 : σ2.sc u = 0 := by rw [F2.2.1 _ huT, hz]
  have eV : max 1 (mhV d n m A b (t + 1)) = max (max 1 (mhV d n m A b t)) x.natAbs := by
    rw [mhV_succ, max_assoc]
  have hA2 : σ2.nat nA = 3 + t := by rw [F2.1 _ not_false, hA]
  refine XV.seq (K₁ := 2) (K₂ := 1) (Q₁ := fun σ3 => σ3.sc sM = ((max 1 (mhV d n m A b (t + 1)) : ℕ) : ℝ) ∧
    σ3.draws = σ.draws ∧ FrameA (fun y => y = sM ∨ y = sT) (fun _ => False) (fun _ _ => False) σ σ3 ∧
    σ3.nat nA = 3 + t) ?_ fun σ3 ⟨s3, d3, F3, n3⟩ => ?_
  · have G2 : FrameA (fun y => y = sM ∨ y = sT) (fun _ => False) (fun _ _ => False) σ σ2 :=
      F2.mono (fun y h => Or.inr h) (fun _ h => h) (fun _ _ h => h)
    by_cases hlt : max 1 (mhV d n m A b t) < x.natAbs
    · refine XV.ifS_t hL hsM hsT (by rw [M2]; exact bM) (by rw [s2]; exact bxa)
        (by rw [M2, s2]; exact_mod_cast hlt) (XV.mono (XV.cpy hL hsM hsT hu z2 (by rw [s2]; exact bxa)) le_rfl
          fun σ' e => ?_)
      subst e
      refine ⟨?_, by simp [d2], G2.setSc (Or.inl rfl) _, by simp [hA2]⟩
      simp only [Env.setSc_sc, ite_true, s2, eV, max_eq_right hlt.le]
    · refine XV.ifS_f hL hsM hsT (by rw [M2]; exact bM) (by rw [s2]; exact bxa)
        (by rw [M2, s2]; exact_mod_cast hlt) (XV.mono (XV.skip _) le_rfl fun σ' e => ?_)
      subst e
      exact ⟨by rw [M2, eV, max_eq_left (not_lt.1 hlt)], d2, G2, hA2⟩
  -- `nA := nA + 1`
  have o3 : σ3.nat one = 1 := by rw [F3.1 _ not_false, h1]
  refine XV.mono (XV.nadd hL (i := nA) (a := nA) (b := one) hnA hnA hone (by rw [n3]; omega)
    (by rw [o3]; omega)) le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by simp [s3], by simp [n3, o3]; omega, by simp [d3], ?_⟩
  exact (F3.mono (N' := fun j => j = nA) (fun _ h => h) (fun _ h => h.elim) (fun _ _ h => h)).setNat rfl _

set_option maxHeartbeats 2000000 in
/-- **The scan of `M̂` on the machine**: `frMhat A b` into the slot `s`, from the cells of the rows of `ctxOf`
(registers `r, r + 1, r + 2` and the slot `s + 1` scratch). -/
theorem XV.mhScan {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {rd rm u s r one : ℕ}
    (hus : u < s) (hS : s + 2 ≤ L.NS) (hdr : rd < r) (hmr : rm < r) (hor : one < r) (hN : r + 3 ≤ L.NN)
    (hz : σ.sc u = 0) (h1 : σ.nat one = 1) (e_d : σ.nat rd = d) (e_m : σ.nat rm = m)
    (hKa : 3 + 2 * ((d + 1) * m) + 1 < 2 ^ ℓa) (hda : d + 1 < 2 ^ ℓa) (hb : (frMhat A b : ℝ) < 2 ^ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xmhScan L rd rm u s (s + 1) r (r + 1) (r + 2) one) σ
      (5 + (2 * ((d + 1) * m) * (6 + 3) + 3)) (fun σ' =>
      σ'.sc s = ((frMhat A b : ℕ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = s ∨ y = s + 1) (fun j => r ≤ j ∧ j ≤ r + 2) (fun _ _ => False) σ σ') := by
  have hℓ : 1 ≤ ℓ := by
    by_contra h
    have : (frMhat A b : ℝ) < 1 := by simpa [show ℓ = 0 by omega] using hb
    have := (frMhat_le A b).1
    have : (1 : ℝ) ≤ frMhat A b := by exact_mod_cast this
    linarith
  have hdm : (d + 1) * m < 2 ^ ℓa := by omega
  have hma : m < 2 ^ ℓa := by have := Nat.le_mul_of_pos_left m (show 0 < d + 1 by omega); omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (2 * ((d + 1) * m) * (6 + 3) + 3)))))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.nadd hL (i := r + 1) (a := rd) (b := one)
    (by omega) (by omega) (by omega) (by rw [e_d]; omega) (by rw [h1]; omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nmul hL (i := r + 1) (a := r + 1) (b := rm) (by omega) (by omega) (by omega)
    (by simp [e_d, h1]; omega) (by simp [show rm ≠ r + 1 by omega, e_m]; exact hma)
    (by simp [show rm ≠ r + 1 by omega, e_m, e_d, h1]; exact hdm)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := r + 1) (a := r + 1) (b := r + 1) (by omega) (by omega) (by omega)
    (by simp [show rm ≠ r + 1 by omega, e_m, e_d, h1]; exact hdm)
    (by simp [show rm ≠ r + 1 by omega, e_m, e_d, h1]; exact hdm)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.sconst hL (x := s) (by omega) 1 rfl (by
    rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nconst hL (i := r) (by omega) 3 (by omega)) fun σ5 e5 => ?_
  subst e5
  set σ5 := ((((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).setNat (r + 1)
    ((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat (r + 1) * (σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat rm)).setNat
    (r + 1) (((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).setNat (r + 1)
    ((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat (r + 1) * (σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat rm)).nat
    (r + 1) + ((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).setNat (r + 1)
    ((σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat (r + 1) * (σ.setNat (r + 1) (σ.nat rd + σ.nat one)).nat rm)).nat
    (r + 1))).setSc s ((1 : ℚ) : ℝ)).setNat r 3 with hσ5
  have K5 : σ5.nat (r + 1) = 2 * ((d + 1) * m) := by
    simp [hσ5, show rm ≠ r + 1 by omega, e_m, e_d, h1]; ring
  have o5 : σ5.nat one = 1 := by simp [hσ5, show one ≠ r by omega, show one ≠ r + 1 by omega, h1]
  have F5 : FrameA (fun y => y = s ∨ y = s + 1) (fun j => r ≤ j ∧ j ≤ r + 2) (fun _ _ => False) σ σ5 :=
    ((((FrameA.refl _ _ _ σ).setNat ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _).setNat
      ⟨by omega, by omega⟩ _ |>.setSc (Or.inl rfl) _).setNat ⟨le_rfl, by omega⟩ _
  -- the loop
  let J : ℕ → Env d → Prop := fun t σ' => σ'.sc s = ((max 1 (mhV d n m A b t) : ℕ) : ℝ) ∧ σ'.nat r = 3 + t ∧
    σ'.draws = σ.draws ∧ FrameA (fun y => y = s ∨ y = s + 1) (fun j => r ≤ j ∧ j ≤ r + 2) (fun _ _ => False) σ σ'
  refine XV.mono (XV.forN hL (i := r + 2) (n := r + 1) (one := one) (by omega) (by omega) (by omega) (by omega)
    (by omega) (2 * ((d + 1) * m)) 6 (by omega) J σ5 K5 o5 ⟨?_, ?_, ?_, F5.setNat ⟨by omega, le_rfl⟩ _⟩ ?_) le_rfl ?_
  · simp [hσ5, mhV_zero]
  · simp [hσ5]
  · simp [hσ5]
  · intro t ht σ' ⟨hs, hr, hd, hF⟩ hi hn ho
    have z' : σ'.sc u = 0 := by rw [hF.2.1 _ (by omega), hz]
    refine XV.mono (XV.mhCell hL (u := u) (sM := s) (sT := s + 1) (nA := r) (one := one) (t := t) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z' ho hr ht hs
      (by omega) hb) le_rfl fun σ'' ⟨s'', r'', d'', F''⟩ => ?_
    refine ⟨by rw [F''.1 _ (by omega), hi], by rw [F''.1 _ (by omega), hn], by rw [F''.1 _ (by omega), ho], ?_,
      by simpa using r'', by simp [d'', hd], ?_⟩
    · simpa using s''
    · exact (hF.trans (F''.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))).setNat ⟨by omega, le_rfl⟩ _
  · rintro σ' ⟨⟨hs, -, hd, hF⟩, -⟩
    refine ⟨by rw [hs, frMhat_cells (n := n)]; rfl, hd, hF⟩

/-! ## The power -/

/-- `r := 1`; `nat n` times `r := r x`. -/
def xpowS (L : Layout) (r x i n one : ℕ) : XCmd :=
  .seq (toX (VL.sconst L r 1)) (xforN i n one (toX (VL.sop2 L .mul r r x)))

theorem pow_le_two_pow {v : ℤ} {E j : ℕ} (h0 : 0 ≤ v) (h : v ≤ 2 ^ E) : v ^ j ≤ 2 ^ (j * E) := by
  rw [mul_comm, pow_mul]; exact pow_le_pow_left₀ h0 h j

set_option maxHeartbeats 1000000 in
/-- The rule of `xpowS`: `v^k` into the slot `r`, for `0 ≤ v ≤ 2^E` in the slot `x` and `k E < ℓ`. -/
theorem XV.powS {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {r x i n one E k : ℕ} {v : ℤ}
    (hr : r < L.NS) (hx : x < L.NS) (hrx : r ≠ x) (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN)
    (hin : i ≠ n) (hio : i ≠ one) (hv : σ.sc x = v) (hv0 : 0 ≤ v) (hvE : v ≤ 2 ^ E) (hk : σ.nat n = k)
    (h1 : σ.nat one = 1) (hka : k < 2 ^ ℓa) (hkE : k * E < ℓ) :
    XRunsB L X ℓa ℓ (xpowS L r x i n one) σ (1 + (k * (1 + 3) + 3)) (fun σ' =>
      σ'.sc r = ((v ^ k : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r) (fun j => j = i) (fun _ _ => False) σ σ') := by
  have bp : ∀ j ≤ k, |v ^ j| < 2 ^ ℓ := fun j hj => by
    have h2 : (2 : ℤ) ^ (j * E) < 2 ^ ℓ :=
      pow_lt_pow_right₀ (by norm_num) (lt_of_le_of_lt (Nat.mul_le_mul_right E hj) hkE)
    rw [abs_of_nonneg (pow_nonneg hv0 j)]; exact (pow_le_two_pow hv0 hvE).trans_lt h2
  refine XV.seq (XV.sconst hL (x := r) hr 1 rfl (by simpa using XV.abs_int_lt (bp 0 (Nat.zero_le _))))
    fun σ1 e1 => ?_
  subst e1
  let J : ℕ → Env d → Prop := fun t σ' => σ'.sc r = ((v ^ t : ℤ) : ℝ) ∧ σ'.sc x = v ∧ σ'.draws = σ.draws ∧
    FrameA (fun y => y = r) (fun j => j = i) (fun _ _ => False) σ σ'
  refine XV.mono (XV.forN hL hi hn ho hin hio k 1 hka J _ (by simp [hk])
    (by simp [h1]) ⟨by simp, by simp [Ne.symm hrx, hv], by simp,
      ((FrameA.refl (fun y => y = r) (fun j => j = i) (fun _ _ => False) σ).setSc rfl _).setNat rfl _⟩ ?_) le_rfl
    fun σ' h => ⟨h.1.1, h.1.2.2.1, h.1.2.2.2⟩
  intro t ht σ' ⟨s1, s2, hd, hF⟩ hit hnk ho1
  have bv : |v| < 2 ^ ℓ := by simpa using bp 1 (by omega)
  refine XV.mono (XV.mulI hL (u := v ^ t) (v := v) hr hr hx s1 s2 (bp t ht.le) bv
    (by rw [← pow_succ]; exact bp (t + 1) ht)) le_rfl fun σ'' e => ?_
  subst e
  refine ⟨by simp [hit], by simp [hnk], by simp [ho1], by simp [pow_succ], by simp [Ne.symm hrx, s2], by simp [hd],
    (hF.setSc rfl _).setNat rfl _⟩

/-! ## `e_R` -/

/-- The bits of the argument of `e_R`: `G = (d + 1) (size d + size m + 2 (d + 1) size M̂)`. -/
def frG (d m Mh : ℕ) : ℕ := (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size Mh)

theorem frY_lt (d m M : ℕ) :
    d * m * M ^ (2 * (d + 1)) < 2 ^ (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) := by
  have hM : M ^ (2 * (d + 1)) < 2 ^ (2 * (d + 1) * Nat.size M) := by
    rw [show 2 * (d + 1) * Nat.size M = Nat.size M * (2 * (d + 1)) by ring, pow_mul 2]
    exact Nat.pow_lt_pow_left (Nat.lt_size_self M) (by omega)
  rw [pow_add, pow_add]
  exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.lt_size_self d) (Nat.lt_size_self m)) hM

theorem frArg_le (d m M : ℕ) : (d * m * M ^ (2 * (d + 1))) ^ (d + 1) + 1 ≤ 2 ^ frG d m M := by
  have h := Nat.pow_lt_pow_left (frY_lt d m M) (show d + 1 ≠ 0 by omega)
  rw [← pow_mul] at h
  unfold frG
  rw [show (d + 1) * (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) =
    (Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M) * (d + 1) by ring]
  omega

theorem frER_leG (d m M : ℕ) : frER d m M ≤ frG d m M :=
  Nat.clog_le_of_le_pow (frArg_le d m M)

theorem frG_ge (d m M : ℕ) : Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M ≤ frG d m M :=
  Nat.le_mul_of_pos_left _ (by omega)

theorem XV.mulIA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS)
    (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ} (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ)
    (bv : |v| < 2 ^ ℓ) (br : |u * v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L .mul x a b)) σ 1 (fun σ' => σ'.sc x = ((u * v : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x) (fun _ => False) (fun _ _ => False) σ σ') :=
  XV.mono (XV.mulI hL hx ha hb hu hv bu bv br) le_rfl fun _ e => by
    subst e; exact ⟨by simp, rfl, (FrameA.refl (fun y => y = x) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩

theorem XV.addIA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS)
    (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ} (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ)
    (bv : |v| < 2 ^ ℓ) (br : |u + v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L .add x a b)) σ 1 (fun σ' => σ'.sc x = ((u + v : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x) (fun _ => False) (fun _ _ => False) σ σ') :=
  XV.mono (XV.addI hL hx ha hb hu hv bu bv br) le_rfl fun _ e => by
    subst e; exact ⟨by simp, rfl, (FrameA.refl (fun y => y = x) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩

/-- `M̂` into the slot `c + 30` (scratch `c + 31` and the registers `n0 + 19, n0 + 20, n0 + 21`), then `e_R` into the
register `n0 + 9` through the slots `c + 32, ..., c + 38`, `j = 1` into `n0 + 8` and `λ = e_R + 1` into `n0 + 10`. -/
def xfrE0 (L : Layout) (B : PrBlk) (u c n0 : ℕ) : XCmd :=
  .seq (xmhScan L B.rd B.rm u (c + 30) (c + 31) (n0 + 19) (n0 + 20) (n0 + 21) (n0 + 4))
  (.seq (.prim (.frag (.nadd (n0 + 20) B.rd (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 20) (n0 + 20) (n0 + 20))))
  (.seq (xpowS L (c + 32) (c + 30) (n0 + 21) (n0 + 20) (n0 + 4))
  (.seq (toX (VL.ncast L (c + 33) B.rd))
  (.seq (toX (VL.ncast L (c + 34) B.rm))
  (.seq (toX (VL.sop2 L .mul (c + 35) (c + 33) (c + 34)))
  (.seq (toX (VL.sop2 L .mul (c + 35) (c + 35) (c + 32)))
  (.seq (.prim (.frag (.nadd (n0 + 20) B.rd (n0 + 4))))
  (.seq (xpowS L (c + 36) (c + 35) (n0 + 21) (n0 + 20) (n0 + 4))
  (.seq (toX (VL.sop2 L .add (c + 37) (c + 36) (u + 1)))
  (.seq (xclogS L (c + 38) (c + 37) (n0 + 9) (n0 + 4))
  (.seq (.prim (.frag (.nconst (n0 + 8) 1)))
    (.prim (.frag (.nadd (n0 + 10) (n0 + 9) (n0 + 8))))))))))))))))

/-- The units of `xfrE0`. -/
def frE0U (d m Mh : ℕ) : ℕ :=
  (5 + (2 * ((d + 1) * m) * (6 + 3) + 3)) + (1 + (1 + ((1 + (2 * (d + 1) * (1 + 3) + 3)) + (1 + (1 + (1 + (1 +
    (1 + ((1 + ((d + 1) * (1 + 3) + 3)) + (1 + ((4 * frG d m Mh + 4) + (1 + 1))))))))))))

/-- The cells `xfrE0` changes. -/
abbrev fr0S (c y : ℕ) : Prop := c + 30 ≤ y

/-- The registers `xfrE0` changes. -/
abbrev fr0N (n0 j : ℕ) : Prop := (n0 + 8 ≤ j ∧ j ≤ n0 + 10) ∨ (n0 + 19 ≤ j ∧ j ≤ n0 + 21)

set_option maxHeartbeats 8000000 in
/-- **`M̂` and `e_R` on the machine**: `e_R = frER d m M̂` in the register `n0 + 9`, `1` in `n0 + 8`, `e_R + 1` in
`n0 + 10`, from the input cells of `ctxOf`. -/
theorem XV.frE0 {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} {u c n0 : ℕ}
    (hc : u + 2 ≤ c) (hS : c + 39 ≤ L.NS) (hrd : B.rd < n0) (hrm : B.rm < n0) (hN : n0 + 22 ≤ L.NN)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hone : σ.nat (n0 + 4) = 1) (e_d : σ.nat B.rd = d)
    (e_m : σ.nat B.rm = m) (hKa : 3 + 2 * ((d + 1) * m) + 1 < 2 ^ ℓa)
    (hGa : 2 * (d + 1) + frG d m (frMhat A b) + 1 < 2 ^ ℓa) (hG : frG d m (frMhat A b) + 1 < ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xfrE0 L B u c n0) σ (frE0U d m (frMhat A b)) (fun σ' =>
      σ'.nat (n0 + 8) = 1 ∧ σ'.nat (n0 + 9) = frER d m (frMhat A b) ∧
      σ'.nat (n0 + 10) = frER d m (frMhat A b) + 1 ∧ σ'.draws = σ.draws ∧
      FrameA (fr0S c) (fr0N n0) (fun _ _ => False) σ σ') := by
  set M := frMhat A b with hMdef
  set G := frG d m M with hGdef
  set G0 := Nat.size d + Nat.size m + 2 * (d + 1) * Nat.size M with hG0
  have hG0G : G0 ≤ G := frG_ge d m M
  have hsM : Nat.size M ≤ 2 * (d + 1) * Nat.size M := Nat.le_mul_of_pos_left _ (by omega)
  have pG : ∀ a, a ≤ G → (2 : ℤ) ^ a < 2 ^ ℓ := fun a ha => pow_lt_pow_right₀ (by norm_num) (by omega)
  have bM : (M : ℤ) ≤ 2 ^ Nat.size M := by exact_mod_cast (Nat.lt_size_self M).le
  have bd : (d : ℤ) < 2 ^ Nat.size d := by exact_mod_cast Nat.lt_size_self d
  have bm : (m : ℤ) < 2 ^ Nat.size m := by exact_mod_cast Nat.lt_size_self m
  have bMl : (M : ℝ) < 2 ^ ℓ := by
    have := bM.trans_lt (pG _ (by omega)); exact_mod_cast this
  have h2l : 2 ≤ ℓ := by omega
  have b1 : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have keep : ∀ σ' : Env d, FrameA (fr0S c) (fr0N n0) (fun _ _ => False) σ σ' →
      σ'.sc u = 0 ∧ σ'.sc (u + 1) = 1 ∧ σ'.nat (n0 + 4) = 1 ∧ σ'.nat B.rd = d ∧ σ'.nat B.rm = m :=
    fun σ' F => ⟨by rw [F.2.1 _ (by simp only [fr0S]; omega), hz], by rw [F.2.1 _ (by simp only [fr0S]; omega), h1],
      by rw [F.1 _ (by simp only [fr0N]; omega), hone], by rw [F.1 _ (by simp only [fr0N]; omega), e_d],
      by rw [F.1 _ (by simp only [fr0N]; omega), e_m]⟩
  have F0 := FrameA.refl (fr0S c) (fr0N n0) (fun _ _ => False) σ
  unfold frE0U
  -- `M̂`
  refine XV.seq (XV.mhScan hL (rd := B.rd) (rm := B.rm) (u := u) (s := c + 30) (r := n0 + 19) (one := n0 + 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hz hone e_d e_m hKa (by omega) bMl)
    fun σ1 ⟨s1, d1, F1⟩ => ?_
  have G1 := F0.trans (F1.mono (fun y h => by simp only [fr0S]; omega) (fun j h => by simp only [fr0N]; omega)
    (fun _ _ h => h))
  obtain ⟨-, -, o1, rd1, rm1⟩ := keep σ1 G1
  -- `2 (d + 1)`
  refine XV.seq (XV.naddA hL (i := n0 + 20) (a := B.rd) (b := n0 + 4) (by omega) (by omega) (by omega) rd1 o1
    (by omega)) fun σ2 ⟨n2, d2, F2⟩ => ?_
  have G2 := G1.trans (F2.mono (fun _ h => h.elim) (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h))
  obtain ⟨-, -, o2, rd2, rm2⟩ := keep σ2 G2
  refine XV.seq (XV.naddA hL (i := n0 + 20) (a := n0 + 20) (b := n0 + 20) (by omega) (by omega) (by omega) n2 n2
    (by omega)) fun σ3 ⟨n3, d3, F3⟩ => ?_
  have G3 := G2.trans (F3.mono (fun _ h => h.elim) (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h))
  obtain ⟨-, -, o3, rd3, rm3⟩ := keep σ3 G3
  have s3 : σ3.sc (c + 30) = ((M : ℤ) : ℝ) := by
    rw [F3.2.1 _ id, F2.2.1 _ id, s1, Int.cast_natCast]
  -- `M̂^{2(d+1)}`
  refine XV.seq (XV.powS hL (r := c + 32) (x := c + 30) (i := n0 + 21) (n := n0 + 20) (one := n0 + 4)
    (E := Nat.size M) (k := 2 * (d + 1)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) s3 (by positivity) bM (by rw [n3]; ring) o3 (by omega) (by omega))
    fun σ4 ⟨s4, d4, F4⟩ => ?_
  have G4 := G3.trans (F4.mono (fun y h => by simp only [fr0S]; omega) (fun j h => by simp only [fr0N]; omega)
    (fun _ _ h => h))
  obtain ⟨-, -, o4, rd4, rm4⟩ := keep σ4 G4
  -- `d m M̂^{2(d+1)}`
  refine XV.seq (XV.ncastA hL (x := c + 33) (i := B.rd) (by omega) (by omega) rd4 (by omega))
    fun σ5 ⟨s5, d5, F5⟩ => ?_
  have G5 := G4.trans (F5.mono (fun y h => by simp only [fr0S]; omega) (fun _ h => h.elim) (fun _ _ h => h))
  obtain ⟨-, -, o5, rd5, rm5⟩ := keep σ5 G5
  refine XV.seq (XV.ncastA hL (x := c + 34) (i := B.rm) (by omega) (by omega) rm5
    (by have := Nat.le_mul_of_pos_left m (show 0 < d + 1 by omega); omega)) fun σ6 ⟨s6, d6, F6⟩ => ?_
  have G6 := G5.trans (F6.mono (fun y h => by simp only [fr0S]; omega) (fun _ h => h.elim) (fun _ _ h => h))
  have bdm : (d : ℤ) * m < 2 ^ (Nat.size d + Nat.size m) := by
    have := Nat.mul_lt_mul'' (Nat.lt_size_self d) (Nat.lt_size_self m)
    rw [← pow_add] at this; exact_mod_cast this
  refine XV.seq (XV.mulIA hL (x := c + 35) (a := c + 33) (b := c + 34) (u := d) (v := m) (by omega) (by omega)
    (by omega) (by rw [F6.2.1 _ (by omega), s5]) s6
    (by rw [abs_of_nonneg (by positivity)]; exact bd.trans (pG _ (by omega)))
    (by rw [abs_of_nonneg (by positivity)]; exact bm.trans (pG _ (by omega)))
    (by rw [abs_of_nonneg (by positivity)]; exact bdm.trans (pG _ (by omega)))) fun σ7 ⟨s7, d7, F7⟩ => ?_
  have G7 := G6.trans (F7.mono (fun y h => by simp only [fr0S]; omega) (fun _ h => h.elim) (fun _ _ h => h))
  have bY : (d : ℤ) * m * M ^ (2 * (d + 1)) < 2 ^ G0 := by exact_mod_cast frY_lt d m M
  have bP : (M : ℤ) ^ (2 * (d + 1)) ≤ 2 ^ G0 := by
    have : (M : ℤ) ^ (2 * (d + 1)) < 2 ^ (2 * (d + 1) * Nat.size M) := by
      rw [show 2 * (d + 1) * Nat.size M = Nat.size M * (2 * (d + 1)) by ring, pow_mul (2 : ℤ)]
      exact_mod_cast Nat.pow_lt_pow_left (Nat.lt_size_self M) (by omega)
    exact this.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine XV.seq (XV.mulIA hL (x := c + 35) (a := c + 35) (b := c + 32) (u := d * m) (v := M ^ (2 * (d + 1)))
    (by omega) (by omega) (by omega) s7
    (by rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), F5.2.1 _ (by omega), s4])
    (by rw [abs_of_nonneg (by positivity)]; exact bdm.trans (pG _ (by omega)))
    (by rw [abs_of_nonneg (by positivity)]; exact bP.trans_lt (pG _ hG0G))
    (by rw [abs_of_nonneg (by positivity)]; exact bY.trans (pG _ hG0G))) fun σ8 ⟨s8, d8, F8⟩ => ?_
  have G8 := G7.trans (F8.mono (fun y h => by simp only [fr0S]; omega) (fun _ h => h.elim) (fun _ _ h => h))
  obtain ⟨-, h18, o8, rd8, rm8⟩ := keep σ8 G8
  -- `(d m M̂^{2(d+1)})^{d+1} + 1`
  refine XV.seq (XV.naddA hL (i := n0 + 20) (a := B.rd) (b := n0 + 4) (by omega) (by omega) (by omega) rd8 o8
    (by omega)) fun σ9 ⟨n9, d9, F9⟩ => ?_
  have G9 := G8.trans (F9.mono (fun _ h => h.elim) (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h))
  obtain ⟨-, -, o9, -, -⟩ := keep σ9 G9
  refine XV.seq (XV.powS hL (r := c + 36) (x := c + 35) (i := n0 + 21) (n := n0 + 20) (one := n0 + 4)
    (E := G0) (k := d + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [F9.2.1 _ not_false, s8]) (by positivity) bY.le n9 o9 (by omega) (by rw [show (d + 1) * G0 = G from rfl]; omega))
    fun σ10 ⟨s10, d10, F10⟩ => ?_
  have G10 := G9.trans (F10.mono (fun y h => by simp only [fr0S]; omega) (fun j h => by simp only [fr0N]; omega)
    (fun _ _ h => h))
  obtain ⟨-, h110, o10, -, -⟩ := keep σ10 G10
  have bA : ((d : ℤ) * m * M ^ (2 * (d + 1))) ^ (d + 1) + 1 ≤ 2 ^ G := by exact_mod_cast frArg_le d m M
  have bA0 : (0 : ℤ) ≤ ((d : ℤ) * m * M ^ (2 * (d + 1))) ^ (d + 1) := by positivity
  refine XV.seq (XV.addIA hL (x := c + 37) (a := c + 36) (b := u + 1) (u := ((d : ℤ) * m * M ^ (2 * (d + 1))) ^ (d + 1))
    (v := 1) (by omega) (by omega) (by omega) s10 (by rw [h110, Int.cast_one])
    (by rw [abs_of_nonneg bA0]; exact (by omega : _ ≤ (2 : ℤ) ^ G).trans_lt (pG _ le_rfl)) b1
    (by rw [abs_of_nonneg (by positivity)]; exact bA.trans_lt (pG _ le_rfl))) fun σ11 ⟨s11, d11, F11⟩ => ?_
  have G11 := G10.trans (F11.mono (fun y h => by simp only [fr0S]; omega) (fun _ h => h.elim) (fun _ _ h => h))
  obtain ⟨-, -, o11, -, -⟩ := keep σ11 G11
  -- `e_R`
  refine XV.seq (XV.clogS hL (G := G) (w := c + 38) (x := c + 37) (c := n0 + 9) (one := n0 + 4) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) s11 (by positivity) bA o11 (by omega) (by omega))
    fun σ12 ⟨n12, d12, F12⟩ => ?_
  have G12 := G11.trans ((FrameA.ofP (Ar := fun _ _ => False) F12).mono (fun y h => by simp only [fr0S]; omega)
    (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h.elim))
  have eR : σ12.nat (n0 + 9) = frER d m M := by
    rw [n12]; unfold frER; congr 1
  have heR := frER_leG d m M
  refine XV.seq (XV.nconstA hL (i := n0 + 8) (by omega) 1 (by omega)) fun σ13 ⟨n13, d13, F13⟩ => ?_
  have G13 := G12.trans (F13.mono (fun _ h => h.elim) (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h))
  have eR13 : σ13.nat (n0 + 9) = frER d m M := by rw [F13.1 _ (by omega), eR]
  refine XV.mono (XV.naddA hL (i := n0 + 10) (a := n0 + 9) (b := n0 + 8) (by omega) (by omega) (by omega) eR13 n13
    (by omega)) le_rfl fun σ14 ⟨n14, d14, F14⟩ => ?_
  refine ⟨by rw [F14.1 _ (by omega), n13], by rw [F14.1 _ (by omega), eR13], n14, ?_,
    G13.trans (F14.mono (fun _ h => h.elim) (fun j h => by simp only [fr0N]; omega) (fun _ _ h => h))⟩
  rw [d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]

end AdversarialBco.Bit.Transfer
