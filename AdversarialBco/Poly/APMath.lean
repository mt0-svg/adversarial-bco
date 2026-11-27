/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# The subroutine AP: the procedures of `Df2Oracle.lean` in the shape the machine computes them

`lineSt` is one pass of the loop of LINE on the machine state (a running window, a result or a failure) and
`lineEnd` the last check; `line_eq_lineEnd` writes LINE through them. `ccUpdate_eq` rewrites the update of CC into the
order of operations of the code of `MachAPCode.lean`, and `update_add_eq_oUnit` writes the coordinate step as a vector
sum.
-/

open Matrix

namespace AdversarialBco.Poly.AP

variable {d : ℕ}

/-- One pass of the loop of LINE on its state: a running window `inl W` stops at `(p₀ + 2λ, λ)` when its measured
second difference is at most `τ λ/2`, else it is halved; a result `inr` and a failure `none` stay. -/
noncomputable def lineSt (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) :
    Option (LineWin ⊕ (ℝ × ℝ)) → Option (LineWin ⊕ (ℝ × ℝ))
  | some (.inl W) =>
    if W.sd ≤ τ * W.lam / 2 then some (.inr (W.p0 + 2 * W.lam, W.lam)) else (lineHalve ev1 τ W).map .inl
  | o => o

/-- The last check of LINE: a running window stops or fails. -/
noncomputable def lineEnd (τ : ℝ) : Option (LineWin ⊕ (ℝ × ℝ)) → Option (ℝ × ℝ)
  | some (.inl W) => if W.sd ≤ τ * W.lam / 2 then some (W.p0 + 2 * W.lam, W.lam) else none
  | some (.inr r) => some r
  | none => none

theorem lineSt_iterate_none (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (j : ℕ) : (lineSt ev1 τ)^[j] none = none := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem lineSt_iterate_inr (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (r : ℝ × ℝ) (j : ℕ) :
    (lineSt ev1 τ)^[j] (some (.inr r)) = some (.inr r) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem lineLoop_eq_lineEnd (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (j : ℕ) (W : LineWin) :
    lineLoop ev1 τ j W = lineEnd τ ((lineSt ev1 τ)^[j] (some (.inl W))) := by
  induction j generalizing W with
  | zero => rw [lineLoop]; rfl
  | succ j ih =>
    rw [lineLoop, Function.iterate_succ_apply]
    by_cases h : W.sd ≤ τ * W.lam / 2
    · simp only [lineSt, h, ite_true, lineSt_iterate_inr, lineEnd]
    · cases hH : lineHalve ev1 τ W with
      | none => simp [lineSt, h, hH, lineSt_iterate_none, lineEnd]
      | some W' => simp [lineSt, h, hH, ih]

theorem line_eq_lineEnd (ev1 : ℝ → ℝ → Option ℝ) (ℓ τ : ℝ) (J : ℕ) :
    line ev1 ℓ τ J = lineEnd τ ((lineSt ev1 τ)^[J] ((lineFirst ev1 ℓ τ).map .inl)) := by
  unfold line
  cases hF : lineFirst ev1 ℓ τ with
  | none => simp [lineSt_iterate_none, lineEnd]
  | some W => simp [lineLoop_eq_lineEnd]

theorem update_add_eq_oUnit (y : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    Function.update y i (y i + s) = y + s • oUnit i := by
  ext j
  simp [oUnit, Function.update_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem ccUpdate_eq (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) :
    ccUpdate A a c =
      (((d : ℝ) * d / ((d : ℝ) * d - 1)) • A +
          (0 - (d : ℝ) * d / ((d : ℝ) * d - 1) * (2 / ((d : ℝ) + 1))) •
            vecMulVec ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)),
        a + (0 - 1 / ((d : ℝ) + 1)) • ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c))) := by
  dsimp [ccUpdate]
  simp only [← one_div]
  apply Prod.ext
  · -- first component
    set α := ((d : ℝ) ^ 2) / ((d : ℝ) ^ 2 - 1) with hα
    set k := 2 / ((d : ℝ) + 1) with hk
    set M := vecMulVec ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) with hM
    calc
      α • (A - k • M) = α • A - α • (k • M) := by rw [smul_sub]
      _ = α • A - (α * k) • M := by rw [smul_smul]
      _ = α • A + (-(α * k)) • M := by rw [sub_eq_add_neg, neg_smul]
      _ = α • A + (0 - α * k) • M := by rw [zero_sub]
      _ = ((d : ℝ) * d / ((d : ℝ) * d - 1)) • A + (0 - (d : ℝ) * d / ((d : ℝ) * d - 1) * (2 / ((d : ℝ) + 1))) • M := by
        simp [hα, hk, hM, sq]
  · -- second component
    set b' := (1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c) with hb'
    calc
      a - (1 / ((d : ℝ) + 1)) • b' = a + (-((1 / ((d : ℝ) + 1)) • b')) := by rw [sub_eq_add_neg]
      _ = a + ((-(1 / ((d : ℝ) + 1))) • b') := by rw [neg_smul]
      _ = a + ((0 - 1 / ((d : ℝ) + 1)) • b') := by rw [zero_sub]

end AdversarialBco.Poly.AP
