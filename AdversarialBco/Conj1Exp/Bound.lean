/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1

@[expose] public section

/-!
# The regret of points of `K` against losses of the class is in `[-n, n]`

Each loss of a round `t < n` has values in `[0, 1]` on `K`, so the sum of the losses at the points played is in
`[0, n]` when those points are in `K`, and so is the sum at every point of `K`, hence its infimum over `K` (`0` for an
empty `K`, by `Real.sInf_empty`): `regretPts_le_of_mem`, `neg_le_regretPts_of_mem`.
-/

namespace AdversarialBco

namespace RealRAM

variable {d : ℕ} {K : Set (E d)} {f : ℕ → E d → ℝ} {x : ℕ → E d} {n : ℕ}

/-- The regret of points of `K` against `n` losses of the class is at most `n`. -/
theorem regretPts_le_of_mem (hf : ∀ t < n, AdmLoss K (f t)) (hx : ∀ t < n, x t ∈ K) : regretPts K f x n ≤ n := by
  unfold regretPts
  have h1 : ∑ t ∈ Finset.range n, f t (x t) ≤ n := by
    calc ∑ t ∈ Finset.range n, f t (x t) ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun t ht => ((hf t (Finset.mem_range.1 ht)).2 _ (hx t (Finset.mem_range.1 ht))).2
      _ = n := by simp
  have h2 : 0 ≤ sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) := by
    apply Real.sInf_nonneg
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun t ht => ((hf t (Finset.mem_range.1 ht)).2 y hy).1
  linarith

/-- The regret of points of `K` against `n` losses of the class is at least `-n`. -/
theorem neg_le_regretPts_of_mem (hf : ∀ t < n, AdmLoss K (f t)) (hx : ∀ t < n, x t ∈ K) :
    -(n : ℝ) ≤ regretPts K f x n := by
  unfold regretPts
  have h1 : 0 ≤ ∑ t ∈ Finset.range n, f t (x t) :=
    Finset.sum_nonneg fun t ht => ((hf t (Finset.mem_range.1 ht)).2 _ (hx t (Finset.mem_range.1 ht))).1
  have h2 : sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) ≤ n := by
    rcases K.eq_empty_or_nonempty with hK | ⟨y, hy⟩
    · simp [hK]
    · have hbdd : BddBelow ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        exact Finset.sum_nonneg fun t ht => ((hf t (Finset.mem_range.1 ht)).2 z hz).1
      calc sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) ≤ ∑ t ∈ Finset.range n, f t y :=
            csInf_le hbdd ⟨y, hy, rfl⟩
        _ ≤ ∑ _t ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun t ht => ((hf t (Finset.mem_range.1 ht)).2 y hy).2
        _ = n := by simp
  linarith

end RealRAM

end AdversarialBco
