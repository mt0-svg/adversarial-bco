/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetW

@[expose] public section

/-!
# The horizon lemma of SHADOW: the case split of DET, named, and its companions

On (O7). For an epoch context `c` (any routine per round), a path `π`:

* `tau_or_fire`: under `DetHyp` at `m`, the epoch fires at `τ(m)`, or every condition holds below `m` and
  `τ(m) = m - 1` (HOR (a); the case split inside `DetHyp.epoch_ok`);
* `tau_mono`: `τ` is nondecreasing in the horizon (HOR (b));
* `evG_mono`, `evY_mono`, `evLQ_mono`, `evSDF_mono`, `evDQ_mono`: the five events pass to a horizon with a smaller
  stopping time (HOR (b));
* `detBase_mono`: the hypotheses of DET without the events pass to a smaller horizon;
* `fire_not_cont`: a round does not both fire and continue;
* `hor_step`: under `DetHyp` at `m`, if the epoch continues at every round `u < s` and `s + 1 ≤ m`, then `DetHyp` holds
  at `s + 1` and `τ(s + 1) = s` (HOR (c)).
-/

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.Poly

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m m' : ℕ}

/-- HOR (a): the epoch fires at `τ(m)`, or every condition holds below `m` and `τ(m) = m - 1`. -/
theorem tau_or_fire (H : DetHyp c δ π m) :
    c.fire π (c.tau π m) ∨ ((∀ s < m, c.Cond π s) ∧ c.tau π m = m - 1) := by
  by_cases hf : c.fire π (c.tau π m)
  · exact Or.inl hf
  · obtain ⟨hc1, -⟩ := H.w_main.2 hf
    obtain ⟨ha, hq⟩ := H.aq (le_refl (c.tau π m))
    have hcond : c.Cond π (c.tau π m) :=
      ⟨hc1, ⟨by linarith, by linarith⟩, H.c3_tau, H.cont_tau hf⟩
    rcases H.tau_cases with h | hn
    · exact Or.inr h
    · exact absurd hcond hn

open Classical in
/-- HOR (b): the stopping time is nondecreasing in the horizon. -/
theorem tau_mono (c : Df2Ctx d) (π : Df2Path d) (h : m' ≤ m) : c.tau π m' ≤ c.tau π m := by
  by_cases h' : ∃ s, s < m' ∧ ¬ c.Cond π s
  · have hm : ∃ s, s < m ∧ ¬ c.Cond π s :=
      ⟨Nat.find h', (Nat.find_spec h').1.trans_le h, (Nat.find_spec h').2⟩
    simp only [Df2Ctx.tau, h', hm, ↓reduceDIte]
    have h1 : Nat.find hm ≤ Nat.find h' := Nat.find_mono fun s hs => ⟨hs.1.trans_le h, hs.2⟩
    exact Nat.find_min' h' ⟨h1.trans_lt (Nat.find_spec h').1, (Nat.find_spec hm).2⟩
  · simp only [Df2Ctx.tau, h', ↓reduceDIte]
    split_ifs with hm
    · by_contra hlt
      exact h' ⟨Nat.find hm, by omega, (Nat.find_spec hm).2⟩
    · omega

theorem evG_mono (hτ : c.tau π m' ≤ c.tau π m) (h : c.EvG π m) : c.EvG π m' :=
  fun s hs => h s (hs.trans hτ)

theorem evY_mono (hτ : c.tau π m' ≤ c.tau π m) (h : c.EvY π m) : c.EvY π m' :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    fun _ _ _ => sq_nonneg _).trans h

theorem evLQ_mono (hτ : c.tau π m' ≤ c.tau π m) (h : c.EvLQ π m) : c.EvLQ π m' :=
  fun s hs => h s (hs.trans hτ)

theorem evSDF_mono (hτ : c.tau π m' ≤ c.tau π m) (h : c.EvSDF π m) : c.EvSDF π m' :=
  fun s hs => h s (hs.trans hτ)

theorem evDQ_mono (hτ : c.tau π m' ≤ c.tau π m) (h : c.EvDQ π m) : c.EvDQ π m' :=
  fun s hs => h s (hs.trans hτ)

/-- The hypotheses of DET without the events pass to a smaller horizon. -/
theorem detBase_mono (H : DetBase c δ π m) (h1 : 1 ≤ m') (h : m' ≤ m) : DetBase c δ π m' :=
  { H with hm1 := h1, hmn := h.trans H.hmn, adm := fun s hs => H.adm s (hs.trans_le h) }

/-- A round does not both fire and continue: the fresh state has `first = true`. -/
theorem fire_not_cont {u : ℕ} (hf : c.fire π u) : ¬ c.cont π u := by
  rintro ⟨st, hst, hfirst⟩
  rw [Df2Ctx.fire] at hf
  rw [hf] at hst
  cases hst
  simp [df2Init] at hfirst

/-- HOR (c): if the epoch continues at every round before `s` and `s + 1 ≤ m`, DET holds at the horizon `s + 1` and
its stopping time is `s`. -/
theorem hor_step (H : DetHyp c δ π m) {s : ℕ} (hs : s + 1 ≤ m) (hc : ∀ u < s, c.cont π u) :
    DetHyp c δ π (s + 1) ∧ c.tau π (s + 1) = s := by
  have hτ : c.tau π (s + 1) ≤ c.tau π m := tau_mono c π hs
  have H' : DetHyp c δ π (s + 1) :=
    { detBase_mono H.toDetBase (Nat.le_add_left 1 s) hs with
      evG := evG_mono hτ H.evG, evY := evY_mono hτ H.evY, evLQ := evLQ_mono hτ H.evLQ,
      evSDF := evSDF_mono hτ H.evSDF, evDQ := evDQ_mono hτ H.evDQ }
  refine ⟨H', ?_⟩
  have hlt := H'.tau_lt
  rcases tau_or_fire H' with hf | ⟨-, heq⟩
  · by_contra hne
    exact fire_not_cont hf (hc _ (by omega))
  · simpa using heq

end AdversarialBco.Bit.Cpl
