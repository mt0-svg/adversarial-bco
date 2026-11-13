/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldVE

@[expose] public section

/-!
# The round of D0: measurability tools and the loss read at the play

* Functions of a mode: the code of a mode is measurable (`measurable_modeCode`), and a function of a mode is
  measurable when its three branches are (`measurable_mode_split`).
* The point a round plays does not depend on the loss, the noise or the dither of that round (`roundGa_fst`); the
  round depends on the loss through its values on the interior of `K` only (`roundGa_loss_congr`).
* The point played from a state, for the gauge of the body `kTh` of `Df2WorldVE.lean`: `cX`, `cPt` and `cPoint`,
  `S⁻¹(X/pip(X))` with `X = μ + (1 - λ) A ξ`.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Functions of a mode -/

theorem measurable_modeCode : Measurable (Df2Mode.code (d := d)) := Measurable.of_comap_le le_rfl

/-- A function of a mode is measurable when its three branches are. -/
theorem measurable_mode_split {Θ Z β : Type*} [MeasurableSpace Θ] [MeasurableSpace Z] [MeasurableSpace β]
    (F : Θ × Df2Mode d × Z → β) (h0 : Measurable fun x : Θ × Z => F (x.1, .off, x.2))
    (h1 : Measurable fun x : Θ × Z => F (x.1, .guard, x.2))
    (h2 : Measurable fun x : Θ × Df2St d × Z => F (x.1, .run x.2.1, x.2.2)) : Measurable F := by
  classical
  let G : Θ × (Fin 3 × Df2St d) × Z → β := fun x =>
    if x.2.1.1 = 0 then F (x.1, .off, x.2.2) else if x.2.1.1 = 1 then F (x.1, .guard, x.2.2)
    else F (x.1, .run x.2.1.2, x.2.2)
  have hG : Measurable G := by
    refine Measurable.ite ?_ (h0.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (Measurable.ite ?_ (h1.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
        (h2.comp (measurable_fst.prodMk ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))))
    · exact measurable_fst.comp (measurable_fst.comp measurable_snd) (measurableSet_singleton 0)
    · exact measurable_fst.comp (measurable_fst.comp measurable_snd) (measurableSet_singleton 1)
  have hF : F = G ∘ fun x => (x.1, x.2.1.code, x.2.2) := by
    funext x
    obtain ⟨θ, m, z⟩ := x
    cases m <;> simp [G, Df2Mode.code]
  rw [hF]
  exact hG.comp (measurable_fst.prodMk ((measurable_modeCode.comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd)))

/-! ## The round of D0 reads the loss at its play only -/

theorem roundGa_fst (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (nt nt' : ℝ) (ξ : Fin d → ℝ) (ζ ζ' : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap ft' nt' ξ ζ' m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundGa]
    split_ifs <;> rfl

/-- The round of D0 depends on the loss through its values on the interior of `K` only. -/
theorem roundGa_loss_congr {K : Set (E d)} (hKconv : Convex ℝ K) {p : Df2OPar} {q : PgSp d}
    (hq : PgGood d K p.R (some q)) (heps0 : 0 < p.eps) (heps1 : p.eps < 1) (n : ℕ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (h : ∀ y ∈ interior K, ft y = ft' y) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K q (gauge (df2Kp K q p.R)) ap ft nt ξ ζ m =
      df2RoundGa p n K q (gauge (df2Kp K q p.R)) ap ft' nt ξ ζ m := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    have hin := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ ξ)))
    simp only [df2Pip, ← WithLp.toLp_smul] at hin
    simp only [df2RoundGa, h _ hin]

/-! ## The point played from a state -/

/-- `X = μ + (1 - λ) A ξ`. -/
noncomputable def cX (n : ℕ) (δ : ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ :=
  st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ ξ)

/-- `pip(X)` for the gauge of `kTh q`. -/
noncomputable def cPt (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (gauge (kTh n δ K q) (WithLp.toLp 2 (cX n δ st ξ)) / (1 - (df2oPar d n δ).eps))

/-- The point played from the state `st`, `S⁻¹(X/pip(X))`. -/
noncomputable def cPoint (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu q + pgOp q (WithLp.toLp 2 ((cPt n δ K q st ξ)⁻¹ • cX n δ st ξ))

end Layer2

end AdversarialBco.Poly
