/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosStage

@[expose] public section

/-!
# UNI-POS: Theorem TRI-OGD-O against SEP outputs (the interface of the machine part)

`triPosT_bad_sep`: Theorem TRI-OGD-O (`triPosT_bad`, Unified/PosStage.lean) at the SEP parameters of
Unified/PosRow.lean (`τ = 2^{-e_τ}`, `ℓ_1 = 2^{-e_1}`, `L = 1`), with `PosSepHyp` read off SEP outputs through
`SepZero` (`posSepHyp_of_sepOut`, Unified/PosSep.lean) and the row closed by `tri_par_tau`. What the machine part
supplies: a program field `gs`, measurable in `(P, z)`, and at every good rational position and rational base point
in range a SEP output in the form of `SepAcc`'s conclusion (a point `y` within `(64/63) ℓ_1` of the base point at
which `gs j P z` is a `τ`-subgradient of the gauge of the stage body in the `ℓ_1` form).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

variable {d : ℕ}

/-- **Theorem TRI-OGD-O against SEP outputs**: on the frame `B̄(c, r0) ⊆ K ⊆ B̄(c, R0)` (`K` convex and closed, `c` and
`r0` rational), for a program field `gs` measurable in `(P, z)` whose vectors are SEP outputs at the parameters
`τ = 2^{-e_τ}`, `ℓ_1 = 2^{-e_1}` at every good rational position (`hout`), and an integer `ℓ ≥ log(m_st/δ)`, the
position `triPosT` on the coin stream is good for `K` at the radius `36.4 d λ(ρ_h)` outside an event of
probability `δ`. -/
theorem triPosT_bad_sep (hZ : AdversarialBco.Uni.SepZero) (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (c : EuclideanSpace ℝ (Fin d)) (hcq : IsRatE c) (r0 R0 : ℝ)
    (hr0q : IsQ r0) (hr0 : 0 < r0) (hK0 : Metric.closedBall c r0 ⊆ K) (hKR : K ⊆ Metric.closedBall c R0)
    (gs : ℕ → PgSp d → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgs : ∀ j, Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) => gs j q.1 q.2)
    (hout : ∀ (j : ℕ) (P : PgSp d), IsRatPg P → (pgMat P).det ≠ 0 →
      PgBody (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (triRa d) →
      ∀ z, IsRatE z → ‖z‖ ≤ triRz d → ∃ y : Fin d → ℝ, oNorm (y - WithLp.ofLp z) ≤ 64 / 63 * (1 / 2 ^ triE1 d) ∧
        ∀ w : Fin d → ℝ, gauge (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (WithLp.toLp 2 y) +
          WithLp.ofLp (gs j P z) ⬝ᵥ (w - y) - 1 / 2 ^ triETau d * ∑ i, |w i - y i| ≤
            gauge (posBody (K ∩ triCube c (2 ^ (j + 1) * r0)) (pgMu P) (pgOp P)) (WithLp.toLp 2 w))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ℓ : ℕ) (hℓ : Real.log (triMst r0 R0 / δ) ≤ ℓ) :
    AdversarialBco.BitRAM.coinStream {cs' | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
      (some (triPosT gs c r0 R0 ℓ cs'))} ≤ ENNReal.ofReal δ := by
  have hsep := posSepHyp_of_sepOut hZ K c r0 gs (1 / 2 ^ triETau d) (64 / 63 * (1 / 2 ^ triE1 d))
    (by positivity) hout
  have has : 1 / 2 ^ triETau d * Real.sqrt d = triAs d := rfl
  have hcs : (2 * 1 + 2 * (1 / 2 ^ triETau d) * Real.sqrt d) * (64 / 63 * (1 / 2 ^ triE1 d)) = triCs d := by
    unfold triCs triAs; ring
  rw [has, hcs] at hsep
  obtain ⟨has0, has1, hcs0, -, hτ⟩ := tri_par_tau d hd
  exact triPosT_bad hd K hKc hKcl c hcq r0 R0 hr0q hr0 hK0 hKR gs hgs (triAs d) (triCs d) has0 hcs0 has1 hτ hsep
    δ hδ0 hδ1 ℓ hℓ

end AdversarialBco.UniPos
