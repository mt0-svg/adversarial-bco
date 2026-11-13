/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2ApMeasProof
public import AdversarialBco.Poly.Df2EvProc

@[expose] public section

/-!
# The round of an epoch as a function of the parameter, the mode, the draw and the noise

With the body and the losses functions of a parameter `θ` and the round maps measurable as `Df2EpochMeas` asks: the
round map is read through `roundOf`, which takes the parameter, the mode, the draw and the noise; `roundOf_eq`
factors it through the code of the mode (the tag, then the state on the tag `2`), and `measurable_ite_code` makes such
a factorisation measurable. The point `X = μ + (1 - λ) A ξ` (`xOf`) is measurable, and so is the value observed in a
round, `e_s(X) + pip(X) ε` (`yOf`), from the extension and the gauge.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open ApMeas

namespace EvGY

variable {d : ℕ} (n : ℕ) (δ : ℝ) {m : ℕ} {Θ : Type} [MeasurableSpace Θ] (Kθ : Θ → Set (E d))
  (gθ : ℕ → Θ → E d → ℝ) (ap : ApFun d)

/-- The point `X = μ + (1 - λ) A ξ` of a state. -/
noncomputable def xOf (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ :=
  st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ ξ)

/-- The value observed in round `s` from the state `st`: `e_s(X) + pip(X) ε`. -/
noncomputable def yOf (s : ℕ) (q : Θ) (st : Df2St d) (ξ : Fin d → ℝ) (e : ℝ) : ℝ :=
  df2Ext (df2oPar d n δ) (Kθ q) (gθ s q) (WithLp.toLp 2 (xOf n δ st ξ)) +
    df2Pip (df2oPar d n δ) (Kθ q) (WithLp.toLp 2 (xOf n δ st ξ)) * e

/-- The round map of round `s` at the parameter. -/
noncomputable def roundOf (s : ℕ) (x : Θ × Df2Mode d × (Fin d → ℝ) × ℝ) : Df2Mode d :=
  (df2RoundE (df2CtxAt d n δ (Kθ x.1) ap) ap (gθ s x.1) x.2.2.2 x.2.2.1 x.2.1).2

omit [MeasurableSpace Θ] in
theorem roundOf_eq (s : ℕ) (x : Θ × Df2Mode d × (Fin d → ℝ) × ℝ) :
    roundOf n δ Kθ gθ ap s x =
      if x.2.1.code.1 = 0 then .off else if x.2.1.code.1 = 1 then .guard else
        df2NextAP ap (df2oPar d n δ) n (df2KepsOf (Kθ x.1) (df2oPar d n δ).eps) x.2.1.code.2 x.2.2.1
          (x.2.1.code.2.A *ᵥ x.2.2.1) (yOf n δ Kθ gθ s x.1 x.2.1.code.2 x.2.2.1 x.2.2.2) := by
  obtain ⟨q, M, ξ, e⟩ := x
  cases M with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [Df2Mode.code, show ((2 : Fin 3) = 0) ↔ False by decide, show ((2 : Fin 3) = 1) ↔ False by decide,
      ite_false]
    show df2NextAP ap (df2oPar d n δ) n _ st ξ _ _ = df2NextAP ap (df2oPar d n δ) n _ st ξ _ _
    congr 1
    simp only [yOf, xOf, df2Ext, df2CtxAt, WithLp.toLp_smul]
    ring

theorem measurable_xOf : Measurable fun x : Df2St d × (Fin d → ℝ) => xOf n δ x.1 x.2 := by
  unfold xOf
  have hA : Measurable fun x : Df2St d × (Fin d → ℝ) => (x.1.A, x.2) :=
    (measurable_st_A.comp measurable_fst).prodMk measurable_snd
  have hmv : Measurable fun y : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => y.1 *ᵥ y.2 :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable
  have h2 : Measurable fun x : Df2St d × (Fin d → ℝ) => x.1.A *ᵥ x.2 := hmv.comp hA
  have h3 : Measurable fun x : Df2St d × (Fin d → ℝ) => (1 - (df2oPar d n δ).lam) • (x.1.A *ᵥ x.2) :=
    h2.const_smul (1 - (df2oPar d n δ).lam)
  exact (measurable_st_mu.comp measurable_fst).add h3

theorem measurable_yOf (hmeas : Df2EpochMeas (df2oPar d n δ) n m Kθ gθ ap) {s : ℕ} (hs : s < m) :
    Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ => yOf n δ Kθ gθ s x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hX : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
      (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2.1) : E d) :=
    (WithLp.measurable_toLp 2 _).comp ((measurable_xOf n δ).comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))))
  have hext := (hmeas.2.1 s hs).comp (measurable_fst.prodMk hX)
  have hg := hmeas.1.comp (measurable_fst.prodMk hX)
  have hpip : Measurable fun x : Θ × Df2St d × (Fin d → ℝ) × ℝ =>
      df2Pip (df2oPar d n δ) (Kθ x.1) (WithLp.toLp 2 (xOf n δ x.2.1 x.2.2.1)) := by
    unfold df2Pip
    exact measurable_const.max (hg.div_const _)
  exact hext.add (hpip.mul (measurable_snd.comp (measurable_snd.comp measurable_snd)))

theorem measurable_ite_code {α : Type*} [MeasurableSpace α] {tag : α → Fin 3} (htag : Measurable tag)
    {f : α → Df2Mode d} (hf : Measurable f) :
    Measurable fun x => if tag x = 0 then Df2Mode.off else if tag x = 1 then Df2Mode.guard else f x :=
  Measurable.ite (htag (measurableSet_singleton 0)) measurable_const
    (Measurable.ite (htag (measurableSet_singleton 1)) measurable_const hf)

variable {Ω : Type} {m0 : MeasurableSpace Ω}

end EvGY

end AdversarialBco.Poly
