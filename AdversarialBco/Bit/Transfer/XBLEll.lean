/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ

@[expose] public section

/-! # The box bound on the points of the projection routine

Every point that `ellRI` returns passed step 1 of `ellTest` (the box test) at the scale of its denominator: `ellRI_box`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open Matrix AdversarialBco.Bit.RQ

variable {d : ℕ}

/-- `a / 2^s` lies in the ball of radius `R`. -/
def Boxed (I : EllI d) (s : ℕ) (a : Fin d → ℤ) : Prop :=
  (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2 ≤ 2 ^ (2 * s) * I.R.num ^ 2

/-- The kept point, if any, is boxed. -/
def KBoxed (I : EllI d) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → Boxed I s b

theorem kboxed_none (I : EllI d) (s : ℕ) : KBoxed I s none := by
  intro b W h; cases h

theorem kboxed_map (I : EllI d) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) (h : KBoxed I s kept)
    (x : Fin d → ℤ) (hx : kept.map Prod.fst = some x) : Boxed I s x := by
  rcases kept with _ | ⟨b, W⟩
  · cases hx
  · simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    exact h b W rfl

/-- The outcome of `ellTest` keeps the invariant: a returned point is boxed, a cut carries a boxed kept point. -/
def CutOK (I : EllI d) (s : ℕ) : Cut d → Prop
  | .ret x => Boxed I s x
  | .cut _ k => KBoxed I s k

/-- Steps 1 to 4 keep the invariant. -/
theorem ellTest_box (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ))
    (hk : KBoxed I s kept) : CutOK I s (ellTest I s a kept) := by
  unfold ellTest
  by_cases h1 : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2
  · simp only [h1, ↓reduceIte]
    exact hk
  · simp only [h1, ↓reduceIte]
    have ha : Boxed I s a := not_lt.mp h1
    split
    · exact hk
    · split_ifs
      · exact hk
      · exact ha
      · intro b W hb
        rcases kept with _ | ⟨b0, W0⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at hb
          rw [← hb.1]; exact ha
        · dsimp only at hb
          split_ifs at hb
          · simp only [Option.some.injEq, Prod.mk.injEq] at hb
            rw [← hb.1]; exact ha
          · simp only [Option.some.injEq, Prod.mk.injEq] at hb
            rw [← hb.1]; exact hk b0 W0 rfl

theorem ellLoop_box (I : EllI d) (k : ℕ) (st : ESt d) (hk : KBoxed I I.p st.kept) (x : Fin d → ℤ)
    (hx : ellLoop I k st = some x) : Boxed I I.p x := by
  induction k generalizing st with
  | zero => exact kboxed_map I _ _ hk x hx
  | succ k ih =>
    have ht := ellTest_box I I.p st.a st.kept hk
    simp only [ellLoop] at hx
    cases hc : ellTest I I.p st.a st.kept with
    | ret x0 =>
      simp only [hc, Option.some.injEq] at hx
      rw [hc] at ht
      subst hx; exact ht
    | cut c kept' =>
      simp only [hc] at hx
      rw [hc] at ht
      split_ifs at hx
      · exact kboxed_map I _ _ ht x hx
      · split at hx
        · exact kboxed_map I _ _ ht x hx
        · exact ih ⟨_, _, kept'⟩ ht hx

theorem bisLoop_box (I : EllI d) (k : ℕ) (lo hi : ℤ) (kept : Option ((Fin d → ℤ) × ℤ))
    (hk : KBoxed I (I.lam + 1) kept) (x : Fin d → ℤ) (hx : bisLoop I k lo hi kept = some x) :
    Boxed I (I.lam + 1) x := by
  induction k generalizing lo hi kept with
  | zero => exact kboxed_map I _ _ hk x hx
  | succ k ih =>
    have ht := ellTest_box I (I.lam + 1) (fun _ => (lo + hi) / 2) kept hk
    simp only [bisLoop] at hx
    cases hc : ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept with
    | ret x0 =>
      simp only [hc, Option.some.injEq] at hx
      rw [hc] at ht
      subst hx; exact ht
    | cut c kept' =>
      simp only [hc] at hx
      rw [hc] at ht
      split_ifs at hx
      · exact kboxed_map I _ _ ht x hx
      · exact ih _ _ kept' ht hx
      · exact ih _ _ kept' ht hx

/-- The box bound: the point `x / 2^(ellExp I)` returned by `ellRI` lies in the ball of radius `R`. -/
theorem ellRI_box (I : EllI d) (x : Fin d → ℤ) (h : ellRI I = some x) :
    (x ⬝ᵥ x) * (I.R.den : ℤ) ^ 2 ≤ 2 ^ (2 * ellExp I) * I.R.num ^ 2 := by
  unfold ellRI at h
  split_ifs at h with h0 hd0 hd1
  · subst hd0
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, zero_mul]
    positivity
  · have hE : ellExp I = I.lam + 1 := by simp [ellExp, hd1]
    rw [hE]
    exact bisLoop_box I _ _ _ none (kboxed_none I _) x h
  · have hE : ellExp I = I.p := by simp [ellExp, hd1]
    rw [hE]
    exact ellLoop_box I _ _ (kboxed_none I _) x h

end AdversarialBco.Bit.Transfer.BLM
