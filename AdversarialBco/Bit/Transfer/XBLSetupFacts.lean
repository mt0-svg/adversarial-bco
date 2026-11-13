/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-!
# BL's setup on the machine: facts of P3, P5 and the epoch start

The kept count `keptCnt` of the row loop, read on the integers of the rows (`kept_row_abs`, `beta_row_abs`); the test
`1/2 < ε'` on the grid (`half_lt_up_iff`); the epoch start on the grid `2^{-p}` (`qn_smul_one`, `onG_smul_one`,
`onG_rnd_s`, `onG_zero`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP Matrix

/-- The kept rows among the first `k`: the count of P3's loop. -/
def keptCnt {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => keptCnt A k + if h : k < m then (if A ⟨k, h⟩ ≠ 0 then 1 else 0) else 0

theorem bad_iff {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (μ : Fin d → ℚ) :
    (∃ i : Fin (keptIdx A).length, b ((keptIdx A).get i) - A ((keptIdx A).get i) ⬝ᵥ μ ≤ 0) ↔
      ∃ i : Fin m, A i ≠ 0 ∧ b i - A i ⬝ᵥ μ ≤ 0 := by
  constructor
  · rintro ⟨i, hi⟩
    have mem : (keptIdx A).get i ∈ keptIdx A := List.get_mem (keptIdx A) i
    rcases (List.mem_filter.mp mem) with ⟨_mem_range, hA⟩
    have hA' : A ((keptIdx A).get i) ≠ 0 := by simpa using hA
    refine ⟨(keptIdx A).get i, hA', ?_⟩
    exact hi
  · rintro ⟨i, hA, hi⟩
    have mem_kept : i ∈ keptIdx A := by
      apply List.mem_filter.mpr
      exact ⟨List.mem_finRange i, by simpa using hA⟩
    rcases (List.mem_iff_get.mp mem_kept) with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    rw [hj]
    exact hi

theorem beta_row_abs {d : ℕ} (a : Fin d → ℚ) (β : ℚ) (ra : Fin d → ℤ) (rb P DS : ℤ)
    (x : Fin d → ℤ) (hP : 0 < P) (hDS : 0 < DS) (hA : ∀ k, (ra k : ℚ) / P = a k) (hb : (rb : ℚ) / P = β) :
    β - a ⬝ᵥ (fun j => (x j : ℚ) / DS) ≤ 0 ↔ rb * DS - ra ⬝ᵥ x ≤ 0 := by
  have ha : a = fun k => (ra k : ℚ) / P := by
    ext k; exact (hA k).symm
  have hβ : β = (rb : ℚ) / P := hb.symm
  rw [ha, hβ]
  have hdot : ((fun k : Fin d => (ra k : ℚ) / P) ⬝ᵥ (fun j : Fin d => (x j : ℚ) / DS)) =
      ((ra ⬝ᵥ x : ℤ) : ℚ) / ((P : ℚ) * (DS : ℚ)) := by
    calc
      ((fun k : Fin d => (ra k : ℚ) / P) ⬝ᵥ (fun j : Fin d => (x j : ℚ) / DS))
          = ∑ k : Fin d, ((ra k : ℚ) / P) * ((x k : ℚ) / DS) := rfl
      _ = ∑ k : Fin d, ((ra k : ℚ) * (x k : ℚ)) / ((P : ℚ) * (DS : ℚ)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
      _ = (∑ k : Fin d, (ra k : ℚ) * (x k : ℚ)) / ((P : ℚ) * (DS : ℚ)) := by
        rw [Finset.sum_div]
      _ = ((ra ⬝ᵥ x : ℤ) : ℚ) / ((P : ℚ) * (DS : ℚ)) := by
        simp [dotProduct]
  rw [hdot]
  have hP' : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne.symm
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne.symm
  field_simp [hP', hDS']
  simp
  exact_mod_cast Iff.rfl

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

theorem kept_row_abs {d : ℕ} (a : Fin d → ℚ) (ra : Fin d → ℤ) (P : ℤ) (hP : 0 < P)
    (h : ∀ k, (ra k : ℚ) / P = a k) : a ≠ 0 ↔ 0 < ra ⬝ᵥ ra := by
  have hP_ne_zero : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne'
  have h_zero_iff : ∀ k, a k = 0 ↔ ra k = 0 := by
    intro k
    have hk := h k
    have hdiv : (ra k : ℚ) / (P : ℚ) = a k := hk
    constructor
    · intro hak
      have hzero : (ra k : ℚ) / (P : ℚ) = 0 := by rw [hdiv, hak]
      rw [div_eq_zero_iff] at hzero
      rcases hzero with (h' | h')
      · exact_mod_cast h'
      · exact (hP_ne_zero h').elim
    · intro hrak
      have hrak' : (ra k : ℚ) = 0 := by exact_mod_cast hrak
      rw [← hdiv, hrak', zero_div]
  have h_dot_eq_sum : ra ⬝ᵥ ra = ∑ i : Fin d, ra i * ra i := rfl
  have h_nonneg : ∀ i, 0 ≤ ra i * ra i := fun i => mul_self_nonneg (ra i)
  constructor
  · intro ha
    have ha' : ¬∀ k, a k = 0 := by
      intro h_all
      apply ha
      ext k
      exact h_all k
    push Not at ha'
    rcases ha' with ⟨k, hk⟩
    have hrak : ra k ≠ 0 := by
      contrapose! hk
      exact (h_zero_iff k).mpr hk
    have hsq_pos : 0 < ra k * ra k := by
      have hsq := sq_pos_iff.mpr hrak
      simpa [sq] using hsq
    have hsum_pos : 0 < ∑ i : Fin d, ra i * ra i :=
      Finset.sum_pos' (fun i _ => h_nonneg i) ⟨k, Finset.mem_univ k, hsq_pos⟩
    rw [h_dot_eq_sum]
    exact hsum_pos
  · intro hpos
    rw [h_dot_eq_sum] at hpos
    by_contra! hzero
    have hra_zero : ra = 0 := by
      ext k
      have hak : a k = 0 := by simpa [hzero] using rfl
      exact (h_zero_iff k).mp hak
    have hsum_zero : ∑ i : Fin d, ra i * ra i = 0 := by
      simp [hra_zero]
    rw [hsum_zero] at hpos
    exact lt_irrefl 0 hpos

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
