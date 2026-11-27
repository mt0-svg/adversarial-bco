/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR3
public import AdversarialBco.Bit.Transfer.XBLR2g

@[expose] public section

/-!
# The arithmetic glue of BL's round

The units of R1 and of the round in the modes `off` and `guard` as quadratic terms, the bound `U` of the head and the
tail's work term as quadratic in the round's, the width facts (`130 U + 120 < ℓ`, the input area), `M ≤ 2^E` from
`size M ≤ E`, an entry of a matrix from its squared Frobenius norm.
-/

open AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM Matrix

/-- An entry of a matrix is at most its squared Frobenius norm when that is at most `c ≥ 1`. -/
theorem AdversarialBco.Bit.Transfer.BLM.gl_frob {d : ℕ} (M : Matrix (Fin d) (Fin d) ℚ) (c : ℚ) (h : frob2 M ≤ c)
    (hc : 1 ≤ c) (i j : Fin d) : |M i j| ≤ c := by
  have hsq : M i j ^ 2 ≤ c := by
    calc
      M i j ^ 2 ≤ ∑ j : Fin d, M i j ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, M i j ^ 2 :=
        Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
      _ = frob2 M := rfl
      _ ≤ c := h
  have habssq : |M i j| ^ 2 ≤ c := by
    calc
      |M i j| ^ 2 = M i j ^ 2 := sq_abs _
      _ ≤ c := hsq
  by_cases hle : |M i j| ≤ 1
  · linarith
  · have hone : 1 ≤ |M i j| := by linarith
    have hpow : |M i j| ≤ |M i j| ^ 2 := by
      nlinarith
    linarith

