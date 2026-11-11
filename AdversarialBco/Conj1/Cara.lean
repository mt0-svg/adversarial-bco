/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

/-!
# The Carathéodory lemma on the interior of a convex set

A family `F l` of functions on `E d`, continuous on an open set `U` and measurable in the parameter `l` at each point
of `U`, is jointly measurable on `Λ × U` (`measurable_subtype_of_continuousOn`, from Mathlib's
`measurable_uncurry_of_continuous_of_measurable` on the subtype `U`, which is metrizable and second countable), hence
on `Λ × E d` once extended by `0` off `U` (`measurable_piecewise_of_continuousOn`, `measurable_indicator_of_continuousOn`).
No hypothesis on the measurable space `Λ`. A convex function on `K` is continuous on `interior K`
(`ConvexOn.continuousOn_interior`), which gives the form on the interior of a convex set
(`measurable_piecewise_interior`, `measurable_indicator_interior`), its use at a measurable random point of the
interior (`measurable_at_interior_point`) and the joint measurability of the losses of a strategy of the class
(`strats_measurable_interior`).
-/

open MeasureTheory

namespace AdversarialBco.Poly.Conj1

open AdversarialBco.RealRAM

theorem measurable_subtype_of_continuousOn {Λ : Type*} [MeasurableSpace Λ] {d : ℕ} (U : Set (E d))
    (F : Λ → E d → ℝ) (hc : ∀ l, ContinuousOn (F l) U) (hm : ∀ y ∈ U, Measurable fun l => F l y) :
    Measurable fun p : Λ × U => F p.1 p.2 := by
  have h_cont : ∀ (l : Λ), Continuous fun (y : U) => F l y := by
    intro l
    exact (continuousOn_iff_continuous_domRestrict (s := U) (f := F l)).mp (hc l)
  have h_meas : ∀ (y : U), Measurable fun (l : Λ) => F l y := by
    intro y
    exact hm y y.2
  have h_uncurry : Measurable (Function.uncurry fun (y : U) (l : Λ) => F l y) :=
    MeasureTheory.measurable_uncurry_of_continuous_of_measurable h_cont h_meas
  have : (Function.uncurry fun (y : U) (l : Λ) => F l y) ∘ Prod.swap = fun p : Λ × U => F p.1 p.2 := by
    ext ⟨l, y⟩; rfl
  simpa [this] using h_uncurry.comp measurable_swap

open Classical in
theorem measurable_piecewise_of_continuousOn {Λ : Type*} [MeasurableSpace Λ] {d : ℕ} (U : Set (E d)) (hU : IsOpen U)
    (F : Λ → E d → ℝ) (hc : ∀ l, ContinuousOn (F l) U) (hm : ∀ y ∈ U, Measurable fun l => F l y) :
    Measurable fun p : Λ × E d => U.piecewise (F p.1) 0 p.2 := by
  have hT : MeasurableSet {p : Λ × E d | p.2 ∈ U} := measurable_snd hU.measurableSet
  refine measurable_of_restrict_of_restrict_compl hT ?_ ?_
  · have h := (measurable_subtype_of_continuousOn U F hc hm).comp
      (f := fun p : {p : Λ × E d | p.2 ∈ U} => (p.1.1, (⟨p.1.2, p.2⟩ : U)))
      ((measurable_fst.comp measurable_subtype_coe).prodMk
        ((measurable_snd.comp measurable_subtype_coe).subtype_mk))
    convert h using 1
    funext p
    simp only [Function.comp_apply, Set.domRestrict_apply]
    exact Set.piecewise_eq_of_mem _ _ _ p.2
  · convert (measurable_const : Measurable fun _ : ({p : Λ × E d | p.2 ∈ U}ᶜ : Set _) => (0 : ℝ)) using 1
    funext p
    simp only [Set.domRestrict_apply]
    exact Set.piecewise_eq_of_notMem _ _ _ p.2

theorem measurable_indicator_of_continuousOn {Λ : Type*} [MeasurableSpace Λ] {d : ℕ} (U : Set (E d)) (hU : IsOpen U)
    (F : Λ → E d → ℝ) (hc : ∀ l, ContinuousOn (F l) U) (hm : ∀ y ∈ U, Measurable fun l => F l y) :
    Measurable fun p : Λ × E d => U.indicator (F p.1) p.2 := by
  classical
  convert measurable_piecewise_of_continuousOn U hU F hc hm using 2 with p
  rw [Set.piecewise_eq_indicator]

open Classical in
theorem measurable_piecewise_interior {Λ : Type*} [MeasurableSpace Λ] {d : ℕ} (K : Set (E d))
    (F : Λ → E d → ℝ) (hconv : ∀ l, ConvexOn ℝ K (F l)) (hm : ∀ y ∈ interior K, Measurable fun l => F l y) :
    Measurable fun p : Λ × E d => (interior K).piecewise (F p.1) 0 p.2 :=
  measurable_piecewise_of_continuousOn (interior K) isOpen_interior F (fun l => (hconv l).continuousOn_interior) hm

theorem measurable_indicator_interior {Λ : Type*} [MeasurableSpace Λ] {d : ℕ} (K : Set (E d))
    (F : Λ → E d → ℝ) (hconv : ∀ l, ConvexOn ℝ K (F l)) (hm : ∀ y ∈ interior K, Measurable fun l => F l y) :
    Measurable fun p : Λ × E d => (interior K).indicator (F p.1) p.2 :=
  measurable_indicator_of_continuousOn (interior K) isOpen_interior F (fun l => (hconv l).continuousOn_interior) hm

theorem measurable_at_interior_point {Λ Ω : Type*} [MeasurableSpace Λ] {m : MeasurableSpace Ω} {d : ℕ}
    (K : Set (E d)) (F : Λ → E d → ℝ) (hconv : ∀ l, ConvexOn ℝ K (F l))
    (hm : ∀ y ∈ interior K, Measurable fun l => F l y) (lam : Ω → Λ) (Y : Ω → E d) (hlam : Measurable[m] lam)
    (hY : Measurable[m] Y) (hYK : ∀ ω, Y ω ∈ interior K) : Measurable[m] fun ω => F (lam ω) (Y ω) := by
  classical
    have h_eq : (fun ω => F (lam ω) (Y ω)) = (fun ω => (interior K).piecewise (F (lam ω)) 0 (Y ω)) := by
      ext ω
      exact (Set.piecewise_eq_of_mem _ _ _ (hYK ω)).symm
    rw [h_eq]
    have h_pair : Measurable[m] fun ω => (lam ω, Y ω) := hlam.prodMk hY
    have h_meas : Measurable fun p : Λ × E d => (interior K).piecewise (F p.1) 0 p.2 :=
      measurable_piecewise_interior K F hconv hm
    exact h_meas.comp h_pair

open Classical in
theorem strats_measurable_interior {d : ℕ} {K : Set (E d)} {n : ℕ} {σ : Strategy d} (hσ : σ ∈ Strats K n)
    (t : ℕ) (ht : t < n) :
    Measurable fun p : ((Fin t → E d) × (Fin t → ℝ)) × E d => (interior K).piecewise (σ t p.1.1 p.1.2) 0 p.2 :=
  measurable_piecewise_interior K (fun h : (Fin t → E d) × (Fin t → ℝ) => σ t h.1 h.2)
    (fun h => ((hσ t ht).1 h.1 h.2).1)
    fun y hy => (hσ t ht).2 y (interior_subset hy)

end AdversarialBco.Poly.Conj1
