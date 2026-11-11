/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1

@[expose] public section

/-!
# `TheoremConj1Upper` implies `TheoremPoly32O`

A fixed sequence `f` is the constant strategy `fun t _ _ => f t`: its world at every step is `⟨K, f, ε, gs⟩`, so the run
against it is the run of `TheoremPoly32O` step by step (`stepAd_const`, by `rfl`), and its realised losses are `f`.
The constant strategy is in `Strats K n` for `f ∈ Advs K n`. The cost bounds of `TheoremConj1Upper` are at most those
of `TheoremPoly32O` with `C'` replaced by `max C' 0`, since `n ≥ 1`, and `CostOK` is monotone in its two bounds
because the number of rounds played never decreases along a run.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

namespace RealRAM

/-- The constant strategy of a sequence. -/
def constStrat {d : ℕ} (f : ℕ → E d → ℝ) : Strategy d := fun t _ _ => f t

theorem constStrat_mem {d : ℕ} {K : Set (E d)} {n : ℕ} {f : ℕ → E d → ℝ} (hf : f ∈ Advs K n) :
    constStrat f ∈ Strats K n :=
  fun t ht => ⟨fun _ _ => hf t ht, fun _ _ => measurable_const⟩

theorem lossAd_const {d : ℕ} (f : ℕ → E d → ℝ) (ε : ℕ → ℝ) (x : ℕ → E d) : lossAd (constStrat f) ε x = f := rfl

theorem stepAd_const {d : ℕ} (P : List Instr) (K : Set (E d)) (f : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) :
    stepAd P ⟨K, constStrat f, ε, gs⟩ = step P ⟨K, f, ε, gs⟩ := rfl

theorem runAd_const {d : ℕ} (P : List Instr) (K : Set (E d)) (f : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) :
    runAd P ⟨K, constStrat f, ε, gs⟩ = run P ⟨K, f, ε, gs⟩ := rfl

theorem playedAd_const {d : ℕ} (P : List Instr) (K : Set (E d)) (f : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) :
    playedAd P ⟨K, constStrat f, ε, gs⟩ = played P ⟨K, f, ε, gs⟩ := rfl

theorem costOKAd_const {d : ℕ} (P : List Instr) (K : Set (E d)) (f : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) :
    CostOKAd P ⟨K, constStrat f, ε, gs⟩ = CostOK P ⟨K, f, ε, gs⟩ := rfl

/-- A step plays at most one round and never removes one. -/
theorem step_rounds_le {d : ℕ} (P : List Instr) (w : World d) (s : State d) : s.rounds ≤ (step P w s).rounds := by
  unfold step
  rcases P[s.pc]? with _ | ins
  · simp
  · cases ins <;> simp <;> split_ifs <;> simp

theorem run_rounds_mono {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) {k k' : ℕ} (h : k ≤ k') :
    (run P w s0 k).rounds ≤ (run P w s0 k').rounds := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [run, Function.iterate_succ_apply']
    exact step_rounds_le P w _

/-- `CostOK` is monotone in its two bounds. -/
theorem costOK_mono {d : ℕ} (P : List Instr) (w : World d) (s0 : State d) (n : ℕ) {B0 B B0' B' : ℝ}
    (h0 : B0 ≤ B0') (h1 : B ≤ B') (h : CostOK P w s0 n B0 B) : CostOK P w s0 n B0' B' :=
  ⟨h.1.trans (run_rounds_mono P w s0 (Nat.ceil_mono h0)), fun k t ht1 htn hk =>
    (h.2 k t ht1 htn hk).trans (run_rounds_mono P w s0 (Nat.add_le_add_left (Nat.ceil_mono h1) k))⟩

end RealRAM

open RealRAM

/-- `C' a^k ≤ max C' 0 (n a)^k` for `a ≥ 0` and `n ≥ 1`. -/
theorem conj1_bound_le (C' a n : ℝ) (k : ℕ) (ha : 0 ≤ a) (hn : 1 ≤ n) :
    C' * a ^ k ≤ max C' 0 * (n * a) ^ k := by
  have hak : 0 ≤ a ^ k := pow_nonneg ha k
  calc C' * a ^ k ≤ max C' 0 * a ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hak
    _ ≤ max C' 0 * (n * a) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha (le_mul_of_one_le_left ha hn) k) (le_max_right _ _)

/-- `TheoremConj1Upper` implies the frozen `TheoremPoly32O`, with the same program, the same `C` and `k`, and
`max C' 0` in place of `C'`. -/
theorem theoremPoly32O_of_conj1 : TheoremConj1Upper → TheoremPoly32O := by
  rintro ⟨P, C, C', k, h⟩
  refine ⟨P, C, max C' 0, k, ?_⟩
  intro d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKcv hball hK f hf ν hν
  obtain ⟨hrun, hreg⟩ := h d hd n hn r0 R0 δ hr0 hrR hδ hδ1 K hKc hKcv hball hK (constStrat f) (constStrat_mem hf)
    ν hν
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log (2 * d * n / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hR : 0 ≤ 2 + Real.log (R0 / r0) := by
    have : 0 ≤ Real.log (R0 / r0) := Real.log_nonneg ((one_le_div hr0).2 hrR)
    linarith
  have hdL : 0 ≤ (d : ℝ) * Real.log (2 * d * n / δ) := mul_nonneg (by positivity) hL
  refine ⟨fun gs noise => ?_, ?_⟩
  · obtain ⟨hc, hin⟩ := hrun gs noise
    refine ⟨?_, hin⟩
    refine costOK_mono P _ _ n ?_ ?_ hc
    · have := conj1_bound_le C' ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) n k
        (mul_nonneg hdL hR) hn'
      calc C' * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k
          ≤ max C' 0 * (n * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0)))) ^ k := this
        _ = max C' 0 * ((d : ℝ) * n * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k := by ring
    · have := conj1_bound_le C' ((d : ℝ) * Real.log (2 * d * n / δ)) n k hdL hn'
      calc C' * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k
          ≤ max C' 0 * (n * ((d : ℝ) * Real.log (2 * d * n / δ))) ^ k := this
        _ = max C' 0 * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k := by ring
  · exact hreg

end AdversarialBco
