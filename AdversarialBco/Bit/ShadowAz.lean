/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowSetE
public import AdversarialBco.Poly.Df2AzumaProof
public import AdversarialBco.Poly.Df2PropGProof

@[expose] public section

/-!
# Proposition W-AZ: the Azuma event of P°

* `roundGa_fst_ap`: the play of a round reads neither the routine, nor (`roundGa_fst`) the loss, the noise or the
  dither;
* `Run.mode_ne_off`, `Run.refPlay_interior`: on `Case`, P° is never switched off and every play of P° lies in the
  interior of `K`;
* `Run.waz` (Proposition W-AZ): on the coupled world, `Case` without the Azuma event has probability at most
  `δe/7`. The loss of round `t` at P°'s play, `fL` at the play of the round with a fixed routine, the draw `ξ_t` and
  the parameter `((S', λ_t), mode_t)` known before round `t`, is in `[0, 1]` and adapted to `cσ`; Lemma FR gives its
  conditional mean, which is P°'s mean loss on `Case`; `df2AzumaEvent` concludes.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Poly.Conj1 (fL lamAt measurable_fL)

variable {d : ℕ}

/-- The play of a round does not read the routine. -/
theorem roundGa_fst_ap (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap ap' : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap' ft nt ξ ζ m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundGa]
    split_ifs <;> rfl

/-- The loss `fL` of a round `t < n` takes its values in `[0, 1]`. -/
theorem fL_mem {K : Set (E d)} {Λ : Type} {L : ℕ → Λ → E d → ℝ} {t : ℕ} {l : Λ} (hf : AdmLoss K (L t l))
    (y : E d) : fL K L t l y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hi : y ∈ interior K
  · simp only [fL, Set.piecewise_eq_of_mem _ _ _ hi]
    exact hf.2 y (interior_subset hi)
  · simp [fL, Set.piecewise_eq_of_notMem _ _ _ hi]

theorem fL_interior {K : Set (E d)} {Λ : Type} {L : ℕ → Λ → E d → ℝ} {t : ℕ} {l : Λ} {y : E d}
    (hy : y ∈ interior K) : fL K L t l y = L t l y := by
  classical
  simp only [fL, Set.piecewise_eq_of_mem _ _ _ hy]

end AdversarialBco.Bit.Cpl
