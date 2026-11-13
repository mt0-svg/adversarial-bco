/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSplit
public import AdversarialBco.Bit.Transfer.XBLSetupInv
public import AdversarialBco.Bit.Transfer.XTrans
public import AdversarialBco.Bit.ApQ.Ell

@[expose] public section

/-!
# The magnitudes of BL's state, part A: the sure facts of a run

The point that ELL-R or BIS-R returns passed the norm test of its step 1, so every coordinate of the output of `apQ`
is at most the call's radius (`apQ_abs`); the draws are at most `B` (`draw_abs`); a run in mode `run` started in mode
`run` (`modeAt_run`), so `ε' ≤ 1/2` and every kept `β̃_i` is positive.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The output of the projection routine -/

/-- The norm test of step 1 of ELL-R at the scale `2^s`: `|a|² ≤ 2^{2s} R²`. -/
def NormOK (I : EllI d) (s : ℕ) (a : Fin d → ℤ) : Prop :=
  (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2 ≤ 2 ^ (2 * s) * I.R.num ^ 2

/-- The kept point passed the norm test. -/
def KeptN (I : EllI d) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → NormOK I s b

/-- What a test leaves: a returned point, or a kept point, that passed the norm test. -/
def CutN (I : EllI d) (s : ℕ) : Cut d → Prop
  | .ret x => NormOK I s x
  | .cut _ kept => KeptN I s kept

theorem keptN_none (I : EllI d) (s : ℕ) : KeptN I s none := fun _ _ h => by cases h

theorem keptN_upd (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (V : ℤ) (kept : Option ((Fin d → ℤ) × ℤ))
    (ha : NormOK I s a) (hk : KeptN I s kept) : KeptN I s (ApQ.updK a V kept) := by
  intro b W h
  rcases kept with _ | ⟨b0, W0⟩
  · simp only [ApQ.updK, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ha
  · simp only [ApQ.updK] at h
    split_ifs at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ha
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hk b0 W0 rfl

theorem ellTest_norm (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ))
    (hk : KeptN I s kept) : CutN I s (ellTest I s a kept) := by
  unfold ellTest
  by_cases h1 : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2
  · simp only [h1, ↓reduceIte]
    exact hk
  have ha : NormOK I s a := not_lt.1 h1
  simp only [h1, ↓reduceIte]
  cases hfn : (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) with
  | some i => exact hk
  | none =>
    by_cases h3 : 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)
    · simp only [h3, ↓reduceIte]
      exact hk
    simp only [h3, ↓reduceIte]
    show CutN I s (if ApQ.ghI I s a = 0 then .ret a else .cut (ApQ.ghI I s a) (ApQ.updK a (ApQ.VI I s a) kept))
    split_ifs
    · exact ha
    · exact keptN_upd I s a _ kept ha hk

theorem map_fst_norm (I : EllI d) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) (hk : KeptN I s kept)
    (x : Fin d → ℤ) (h : kept.map Prod.fst = some x) : NormOK I s x := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨b, W⟩, hb, rfl⟩ := h
  exact hk b W hb

theorem ellLoop_norm (I : EllI d) : ∀ (k : ℕ) (st : ESt d) (x : Fin d → ℤ), KeptN I I.p st.kept →
    ellLoop I k st = some x → NormOK I I.p x
  | 0, st, x, hk, h => by
    simp only [ellLoop] at h
    exact map_fst_norm I _ _ hk x h
  | k + 1, st, x, hk, h => by
    have hc := ellTest_norm I I.p st.a st.kept hk
    simp only [ellLoop] at h
    generalize ellTest I I.p st.a st.kept = T at hc h
    cases T with
    | ret y =>
      simp only [Option.some.injEq] at h
      subst h; exact hc
    | cut c kept =>
      simp only at h hc
      split_ifs at h
      · exact map_fst_norm I _ _ hc x h
      · revert h
        split
        · exact map_fst_norm I _ _ hc x
        · exact ellLoop_norm I k _ x hc

theorem bisLoop_norm (I : EllI d) : ∀ (k : ℕ) (lo hi : ℤ) (kept : Option ((Fin d → ℤ) × ℤ)) (x : Fin d → ℤ),
    KeptN I (I.lam + 1) kept → bisLoop I k lo hi kept = some x → NormOK I (I.lam + 1) x
  | 0, lo, hi, kept, x, hk, h => by
    simp only [bisLoop] at h
    exact map_fst_norm I _ _ hk x h
  | k + 1, lo, hi, kept, x, hk, h => by
    have hc := ellTest_norm I (I.lam + 1) (fun _ => (lo + hi) / 2) kept hk
    simp only [bisLoop] at h
    generalize ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept = T at hc h
    cases T with
    | ret y =>
      simp only [Option.some.injEq] at h
      subst h; exact hc
    | cut c kept' =>
      simp only at h hc
      split_ifs at h
      · exact map_fst_norm I _ _ hc x h
      · exact bisLoop_norm I k _ _ kept' x hc h
      · exact bisLoop_norm I k _ _ kept' x hc h

/-- A point returned by the routine on the integer problem passed the norm test at its exponent, with `R ≥ 1`. -/
theorem ellRI_norm (I : EllI d) (x : Fin d → ℤ) (h : ellRI I = some x) : 1 ≤ I.R ∧ NormOK I (ellExp I) x := by
  unfold ellRI at h
  split_ifs at h with h0 hd0 hd1
  · cases h
    refine ⟨by push_neg at h0; exact h0.1, ?_⟩
    unfold NormOK
    simp only [dotProduct_zero, zero_mul]
    positivity
  · refine ⟨by push_neg at h0; exact h0.1, ?_⟩
    rw [show ellExp I = I.lam + 1 by simp [ellExp, hd1]]
    exact bisLoop_norm I _ _ _ none x (keptN_none I _) h
  · refine ⟨by push_neg at h0; exact h0.1, ?_⟩
    rw [show ellExp I = I.p by simp [ellExp, hd1]]
    exact ellLoop_norm I _ _ x (keptN_none I _) h

/-- **Every coordinate of the point of `apQ` is at most the call's radius.** -/
theorem apQ_abs (D : CallQ d) (y : Fin d → ℚ) (h : apQ D = some y) (j : Fin d) : |y j| ≤ D.R := by
  unfold apQ at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hR, hn⟩ := ellRI_norm _ x hx
  set s := ellExp (clearQ D)
  have hRc : (clearQ D).R = D.R := rfl
  rw [hRc] at hR
  unfold NormOK at hn
  rw [hRc] at hn
  have hR0 : (0 : ℚ) < D.R := by linarith
  have hden : (0 : ℚ) < D.R.den := by exact_mod_cast D.R.den_pos
  have hnum : (D.R.num : ℚ) = D.R * D.R.den := by
    exact_mod_cast (Rat.mul_den_eq_num D.R).symm
  -- `x_j² ≤ x·x ≤ 2^{2s} R²`
  have hsq : ((x j : ℚ)) ^ 2 ≤ (2 ^ s) ^ 2 * D.R ^ 2 := by
    have h1 : ((x j : ℤ) : ℚ) ^ 2 ≤ ((x ⬝ᵥ x : ℤ) : ℚ) := by
      have : (x j) ^ 2 ≤ x ⬝ᵥ x := by
        unfold dotProduct
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), sq]
        have : 0 ≤ ∑ i ∈ Finset.univ.erase j, x i * x i :=
          Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
        linarith
      exact_mod_cast this
    have h2 : ((x ⬝ᵥ x : ℤ) : ℚ) * (D.R.den : ℚ) ^ 2 ≤ 2 ^ (2 * s) * (D.R.num : ℚ) ^ 2 := by exact_mod_cast hn
    rw [hnum, mul_pow, pow_mul] at h2
    have h3 : ((x ⬝ᵥ x : ℤ) : ℚ) ≤ (2 ^ 2) ^ s * D.R ^ 2 := by
      have hd2 : (0 : ℚ) < (D.R.den : ℚ) ^ 2 := by positivity
      have h2' : ((x ⬝ᵥ x : ℤ) : ℚ) * (D.R.den : ℚ) ^ 2 ≤ ((2 ^ 2) ^ s * D.R ^ 2) * (D.R.den : ℚ) ^ 2 := by
        linarith
      exact le_of_mul_le_mul_right h2' hd2
    calc ((x j : ℤ) : ℚ) ^ 2 ≤ ((x ⬝ᵥ x : ℤ) : ℚ) := h1
      _ ≤ (2 ^ 2) ^ s * D.R ^ 2 := h3
      _ = (2 ^ s) ^ 2 * D.R ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm s 2]
  have hs : (0 : ℚ) < 2 ^ s := by positivity
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h4 : ((x j : ℤ) : ℚ) ^ 2 ≤ (2 ^ s * D.R) ^ 2 := by rw [mul_pow]; exact hsq
  have := sq_le_sq.1 h4
  rw [abs_of_pos (mul_pos hs hR0)] at this
  linarith

end AdversarialBco.Bit.Transfer.BLM
