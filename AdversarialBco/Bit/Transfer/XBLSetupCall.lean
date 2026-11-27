/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupPrm
public import AdversarialBco.Bit.Transfer.XBLSetupFacts

@[expose] public section

/-!
# BL's setup on the machine: the block of FRAME and TRI

`FrameSpec`: the body of the machine rule of FRAME for a given command and constants. `blkS`: the block of the
setup's calls of FRAME and TRI, and `SC`, `NC`, `AC` the cells they change. `ptIn_fun`, `posIn_fun`: `PtIn` and
`PosIn` as functions of the cells.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## The rules as hypotheses -/

/-- The body of `FrameRule` for the command `xframe` and the constants `C, k, nS, nN, nA`. -/
def FrameSpec (xframe : Layout → PrBlk → XCmd) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (ℓa ℓ : ℕ) (B : PrBlk) (σ : Env d),
    1 ≤ d → LayOK L d ℓa → B.OK L nS nN nA → σ.nat B.rd = d → σ.nat B.rm = m →
    C * (d + m + (frMhat A b).size + 1) ^ k ≤ ℓ → C * (d + m + (frMhat A b).size + 1) ^ k < 2 ^ ℓa →
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xframe L B) σ (C * (d + m + (frMhat A b).size + 1) ^ k) (fun σ' =>
      PtIn σ' B.aW (C * (d + m + (frMhat A b).size + 1) ^ k) (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ')

/-! ## The calls -/

/-- The block of the setup's calls: `d`, `m` in `rD`, `rM`, `n` in `sN`, the centre in `aC`; the routines' own cells
from the slot `128`, the register `48`, the array `16`. -/
def blkS : PrBlk := ⟨rD, rM, sN, aC, 128, 48, 16⟩

/-- The cells that the setup's calls of FRAME and TRI change. -/
def SC (y : ℕ) : Prop := y = sDS ∨ 124 ≤ y
def NC (j : ℕ) : Prop := j = 8 ∨ j = 9 ∨ j = 10 ∨ 48 ≤ j
def AC (a c : ℕ) : Prop := (a = aC ∧ c < d + 1) ∨ (a = aMuS ∧ c < d) ∨ (a = aAS ∧ c < d * d) ∨ 16 ≤ a

/-- `PtIn` as a function of the cells. -/
theorem ptIn_fun {d : ℕ} (arr : ℕ → ℝ) (s : ℕ) (c : Fin d → ℚ)
    (h : ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ arr 0 = D ∧
      ∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr (j + 1) = x ∧ (x : ℚ) / D = c j) :
    ∃ x : ℕ → ℤ, (∀ k < d + 1, arr k = x k ∧ |x k| < 2 ^ s) ∧ 0 < x 0 ∧
      ∀ j : Fin d, (x (j + 1) : ℚ) / x 0 = c j := by
  rcases h with ⟨D, hDpos, hDlt, harr0, hx⟩
  choose xf hx_bound hx_arr hx_eq using hx
  let x : ℕ → ℤ := λ k =>
    if hk0 : k = 0 then D
    else if hk : k - 1 < d then xf ⟨k - 1, hk⟩
    else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have hx0 : x 0 = D := by simp [x]
      refine ⟨?_, ?_⟩
      · simpa [x] using harr0
      · rw [hx0]
        have habs : |D| = D := abs_of_pos hDpos
        rw [habs]
        exact hDlt
    · have hk_sub_lt : k - 1 < d := by
        have hk_le_d : k ≤ d := by omega
        omega
      have hx_val : x k = xf ⟨k - 1, hk_sub_lt⟩ := by
        simp [x, hk0, hk_sub_lt]
      refine ⟨?_, ?_⟩
      · -- arr k = x k
        rw [hx_val]
        have := hx_arr ⟨k - 1, hk_sub_lt⟩
        have hpos : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk0)
        -- this : arr (↑⟨k-1, hk_sub_lt⟩ + 1) = ↑(xf ⟨k-1, hk_sub_lt⟩)
        -- ↑⟨k-1, hk_sub_lt⟩ = k-1, so this : arr ((k-1) + 1) = ↑(xf ⟨k-1, hk_sub_lt⟩)
        -- And (k-1) + 1 = k
        simpa [Nat.sub_add_cancel hpos] using this
      · -- |x k| < 2 ^ s
        rw [hx_val]
        exact hx_bound ⟨k - 1, hk_sub_lt⟩
  · -- 0 < x 0
    have hx0 : x 0 = D := by simp [x]
    rw [hx0]
    exact hDpos
  · -- ∀ j : Fin d, (x (j + 1) : ℚ) / x 0 = c j
    intro j
    have hx0 : x 0 = D := by simp [x]
    rw [hx0]
    have hx_j1 : x (j.val + 1) = xf j := by
      dsimp [x]
      simp [j.is_lt]
    -- Now (x (j.val + 1) : ℚ) / D = c j
    -- hx_eq j : (xf j : ℚ) / D = c j
    -- And x (j.val + 1) = xf j
    rw [hx_j1]
    exact hx_eq j

/-- `PosIn` as functions of the cells. -/
theorem posIn_fun {d : ℕ} (sc : ℝ) (arr0 arr1 : ℕ → ℝ) (s : ℕ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (h : ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ sc = D ∧
      (∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr0 j = x ∧ (x : ℚ) / D = S.1 j) ∧
      ∀ i j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr1 (d * i + j) = x ∧ (x : ℚ) / D = S.2 i j) :
    ∃ (D : ℤ) (xm xa : ℕ → ℤ), 0 < D ∧ D < 2 ^ s ∧ sc = D ∧
      (∀ k < d, arr0 k = xm k ∧ |xm k| < 2 ^ s) ∧ (∀ k < d * d, arr1 k = xa k ∧ |xa k| < 2 ^ s) ∧
      (∀ j : Fin d, (xm j : ℚ) / D = S.1 j) ∧ ∀ i j : Fin d, (xa (d * i + j) : ℚ) / D = S.2 i j := by
  obtain ⟨D, hD0, hDs, hsc, hm, ha⟩ := h
  choose xmf hxm1 hxm2 hxm3 using hm
  choose xaf hxa1 hxa2 hxa3 using ha
  have hd0 : ∀ k, k < d * d → 0 < d := fun k hk => by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hk
    · exact h
  refine ⟨D, fun k => if hk : k < d then xmf ⟨k, hk⟩ else 0,
    fun k => if hk : k < d * d then xaf ⟨k / d, Nat.div_lt_of_lt_mul hk⟩ ⟨k % d, Nat.mod_lt _ (hd0 k hk)⟩ else 0,
    hD0, hDs, hsc, fun k hk => ?_, fun k hk => ?_, fun j => ?_, fun i j => ?_⟩
  · simp only [dif_pos hk]; exact ⟨hxm2 ⟨k, hk⟩, hxm1 ⟨k, hk⟩⟩
  · simp only [dif_pos hk]
    have e : d * (k / d) + k % d = k := Nat.div_add_mod k d
    have := hxa2 ⟨k / d, Nat.div_lt_of_lt_mul hk⟩ ⟨k % d, Nat.mod_lt _ (hd0 k hk)⟩
    simp only at this
    rw [e] at this
    exact ⟨this, hxa1 _ _⟩
  · simp only [dif_pos j.2]; exact hxm3 j
  · have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i.2
    have hlt : d * (i : ℕ) + j < d * d := by
      have := i.2; have := j.2; nlinarith
    simp only [dif_pos hlt]
    have h1 : (d * (i : ℕ) + j) / d = i := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt j.2, add_zero]
    have h2 : (d * (i : ℕ) + j) % d = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
    have e : xaf ⟨(d * (i : ℕ) + j) / d, Nat.div_lt_of_lt_mul hlt⟩ ⟨(d * (i : ℕ) + j) % d, Nat.mod_lt _ hd⟩ =
        xaf i j := by
      congr 1 <;> exact Fin.ext (by simp only [h1, h2])
    rw [e]; exact hxa3 i j

end AdversarialBco.Bit.Transfer.BLM
