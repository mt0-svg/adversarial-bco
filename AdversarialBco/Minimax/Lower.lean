/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Minimax.Upper
public import AdversarialBco.LowerDelta.Arith

@[expose] public section

/-!
# The lower half of the minimax theorem from `TheoremLowerUProg` and `TheoremLowerUDProg`

`minimax_lower_of_env`: from an environment of every learner with `P(Reg_n ≥ c) ≥ 1/2`, `c ≥ 0`, the bounds
`V⁺(G) ≥ c / 2` (the expectation form, read through the tail) and `V_δ(G) ≥ c` for `δ < 1/2`. The environments come
from clause (a) of `TheoremLowerUDProg` at the failure `1/2`, with `c = 1.12·10^-8 (1/2)^2 Λ = 2.8·10^-9 Λ`; the
arithmetic facts `ofReal_half` and `min_half_fail` serve the failure `1/2` and the failure `(1 - δ) / 2`.
-/

open MeasureTheory Set

namespace AdversarialBco.Minimax

open BitRAM BitRAMO Unified UnifiedLower

/-- `ENNReal.ofReal (1/2) = 1/2`. -/
theorem ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 := by
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-- `min ((1 - δ) / 2) (1 / 2) = (1 - δ) / 2` for `δ ≥ 0`. -/
theorem min_half_fail {δ : ℝ} (hδ : 0 ≤ δ) : min ((1 - δ) / 2) (1 / 2) = (1 - δ) / 2 :=
  min_eq_left (by linarith)

/-! ## From `TheoremLowerUDProg` alone -/

/-- The two bounds from an environment of every learner with `P(Reg_n ≥ c) ≥ 1/2`, `c ≥ 0`: `c / 2 ≤ V⁺(G)` (the
expectation form, read through the tail) and `c ≤ V_δ(G)` when `δ < 1/2`. -/
theorem minimax_lower_of_env {d n : ℕ} {δ r0 R0 : ℚ} (hr0 : 0 < r0) {a : Fin d → ℚ} {K : Set (E d)}
    (hb1 : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K) {orc : (Fin d → ℚ) → ℕ → Bool}
    (hLne : (Learners K orc (initU d n δ r0 R0 a) n).Nonempty) {c : ℝ} (hc0 : 0 ≤ c)
    (henv : ∀ ℓ ∈ Learners K orc (initU d n δ r0 R0 a) n,
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
        (noise : ℕ → Ω → ℝ), NoisyAdv K n ℓ.D ℓ.D' μ coin loss noise ∧
          (1 / 2 : ENNReal) ≤ μ {ω | c ≤ regretU ℓ.prog K n (initU d n δ r0 R0 a) (envWorld orc coin loss noise ω)}) :
    1 / 2 * c ≤ valMean d n δ r0 R0 a K orc ∧ ((δ : ℝ) < 1 / 2 → c ≤ valQuant d n δ r0 R0 a K orc δ) := by
  have hne : K.Nonempty := body_nonempty hr0 hb1
  refine ⟨le_valMean_of hLne hne hc0 (by norm_num) fun ℓ hℓ => ?_, fun hδ => le_valQuant_of hLne hne
    (by linarith) fun ℓ hℓ => ?_⟩
  · obtain ⟨Ω, _, μ, coin, loss, noise, hA, hp⟩ := henv ℓ hℓ
    exact ⟨Ω, inferInstance, μ, coin, loss, noise, hA, ofReal_half ▸ hp⟩
  · obtain ⟨Ω, _, μ, coin, loss, noise, hA, hp⟩ := henv ℓ hℓ
    refine ⟨Ω, inferInstance, μ, coin, loss, noise, hA, lt_of_lt_of_le ?_ hp⟩
    rw [← ofReal_half]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hδ

end AdversarialBco.Minimax
