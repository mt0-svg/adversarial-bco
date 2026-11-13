/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# An i.i.d. product under an injective reindexing

`infinitePi_comp_inj`: the image of the product `μ^ℕ` under an injective reindexing `σ : J → ℕ` is the product
`μ^J`.
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

/-! ## Product measures -/

theorem infinitePi_comp_inj {X J : Type*} [MeasurableSpace X] [Countable J]
    (μ : Measure X) [IsProbabilityMeasure μ] (σ : J → ℕ) (hσ : Function.Injective σ) :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun x : ℕ → X => fun j => x (σ j)) =
      Measure.infinitePi fun _ : J => μ := by
  classical
    apply MeasureTheory.Measure.eq_infinitePi
    intro s t ht
    have hmeas : Measurable (fun (x : ℕ → X) (j : J) => x (σ j)) := by
      refine Measurable.of_eval (fun j => ?_)
      exact measurable_pi_apply (σ j)
    have hmeasSet : MeasurableSet ((s : Set J).pi t) := by
      refine (measurableSet_pi (Finset.countable_toSet s)).mpr ?_
      left
      intro i hi
      exact ht i
    rw [Measure.map_apply hmeas hmeasSet]
    -- define t' : ℕ → Set X
    let t' : ℕ → Set X := fun i =>
      if h : i ∈ Finset.image σ s then
        t (Classical.choose (Finset.mem_image.1 h))
      else Set.univ
    have h_t'_eq : ∀ j ∈ s, t' (σ j) = t j := by
      intro j hj
      dsimp [t']
      have h_mem : σ j ∈ Finset.image σ s :=
        Finset.mem_image.mpr ⟨j, hj, rfl⟩
      simp [h_mem]
      have h_spec := Classical.choose_spec (Finset.mem_image.1 h_mem)
      -- h_spec : Classical.choose (Finset.mem_image.1 h_mem) ∈ s ∧ σ (Classical.choose (Finset.mem_image.1 h_mem)) = σ j
      have h_choose_eq : Classical.choose (Finset.mem_image.1 h_mem) = j := hσ h_spec.2
      rw [h_choose_eq]
    have h_preimage : (fun (x : ℕ → X) (j : J) => x (σ j)) ⁻¹' ((s : Set J).pi t) =
        ((Finset.image σ s : Set ℕ).pi t') := by
      ext x
      constructor
      · intro hx
        have hx' : ∀ j ∈ s, x (σ j) ∈ t j := by
          intro j hj
          have := hx j hj
          simpa using this
        intro i hi
        rw [Finset.mem_coe, Finset.mem_image] at hi
        rcases hi with ⟨j, hj, rfl⟩
        -- Need: x (σ j) ∈ t' (σ j)
        -- We know: x (σ j) ∈ t j, and t' (σ j) = t j
        rw [h_t'_eq j hj]
        exact hx' j hj
      · intro hx j hj
        have hi : σ j ∈ (Finset.image σ s : Set ℕ) := by
          apply Finset.mem_coe.mpr
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
        have hx' := hx (σ j) hi
        -- hx' : x (σ j) ∈ t' (σ j)
        -- We need: x (σ j) ∈ t j
        -- Since t' (σ j) = t j, we're done
        rw [h_t'_eq j hj] at hx'
        exact hx'
    rw [h_preimage]
    have hmeas_t' : ∀ i ∈ Finset.image σ s, MeasurableSet (t' i) := by
      intro i hi
      rw [Finset.mem_image] at hi
      rcases hi with ⟨j, hj, rfl⟩
      dsimp [t']
      have h_mem : σ j ∈ Finset.image σ s :=
        Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have h_spec := Classical.choose_spec (Finset.mem_image.1 h_mem)
      -- h_spec : Classical.choose (Finset.mem_image.1 h_mem) ∈ s ∧ σ (Classical.choose (Finset.mem_image.1 h_mem)) = σ j
      have h_eq : Classical.choose (Finset.mem_image.1 h_mem) = j := hσ h_spec.2
      simp [h_mem]
      rw [h_eq]
      exact ht j
    rw [MeasureTheory.Measure.infinitePi_pi (fun _ => μ) hmeas_t']
    -- Now: ∏ i ∈ Finset.image σ s, μ (t' i) = ∏ j ∈ s, μ (t j)
    calc
      ∏ i ∈ Finset.image σ s, μ (t' i) = ∏ j ∈ s, μ (t' (σ j)) := by
        refine Finset.prod_image ?_
        intro x hx y hy h_eq
        exact hσ h_eq
      _ = ∏ j ∈ s, μ (t j) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [h_t'_eq j hj]

variable (d : ℕ)

end Layer2

end AdversarialBco.Poly
