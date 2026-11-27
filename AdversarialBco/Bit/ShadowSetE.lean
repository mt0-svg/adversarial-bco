/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowMeas
public import AdversarialBco.Poly.Df2Layer2Proof
public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# Proposition W-SETE: the lemmas on the coupled layout

The indices of the coupling coordinates of round `t` (`zIdx`, `zc_eq`, `zIdx_inj`, `xiIdx_inj`), the law of a map of
a product whose fibres all carry the second factor to the same law (`map_prod_fiber`), and the dither of the coupling
under (O2-L), with the law of `Z/2` (`integral_coup`). The proposition on an abstract coupled world
(`RunW.setE_ref`, with Lemma W-LAW: `zs_law`, `condExp_zs_F`, `condExp_zs_H`) is in Unified/WorldShadow.lean.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-! ## The coordinates of round `t` -/

/-- The indices of the coupling coordinates of round `t`. -/
def zIdx (d t : ℕ) : Fin 3 → ℕ := ![cIdx d t (d + 1), cIdx d t (d + 3), cIdx d t (d + 4)]

theorem zc_eq (t : ℕ) : zc d t = fun ω : WΩ => fun k => ω.1 (zIdx d t k) := by
  funext ω k
  fin_cases k <;> rfl

theorem zIdx_inj (t : ℕ) : Function.Injective (zIdx d t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [zIdx, cIdx]

theorem xiIdx_inj (t : ℕ) : Function.Injective fun c : Fin d => cIdx d t c := by
  intro a b h
  simp only [cIdx] at h
  exact Fin.ext (by omega)

/-! ## The law of the dither (Lemma W-LAW) -/

/-- A map of a product whose fibres all carry the second factor to the same law has that law. -/
theorem map_prod_fiber {X Z Y : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y] (ρ : Measure X)
    [IsProbabilityMeasure ρ] (κ : Measure Z) [SFinite κ] (Φ : X × Z → Y) (hΦ : Measurable Φ) (lam : Measure Y)
    (h : ∀ x, κ.map (fun z => Φ (x, z)) = lam) : (ρ.prod κ).map Φ = lam := by
  ext A hA
  rw [Measure.map_apply hΦ hA, Measure.prod_apply (hΦ hA)]
  have hx : ∀ x, κ (Prod.mk x ⁻¹' (Φ ⁻¹' A)) = lam A := fun x => by
    have hm : Measurable fun z => Φ (x, z) := hΦ.comp (measurable_const.prodMk measurable_id)
    rw [← h x, Measure.map_apply hm hA]
    rfl
  simp_rw [hx]
  simp

theorem integral_coup {Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ} (hC : CoupLaw Coup) {G : ℝ → ℝ} (hG : Measurable G)
    (m r : ℝ) : ∫ z, G (Coup m r z) ∂gaussK 3 = ∫ y, G (y / 2) ∂(gaussianReal 0 1) := by
  have hc : Measurable (Coup m r) :=
    hC.meas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [← integral_map hc.aemeasurable hG.aestronglyMeasurable, hC.law m r,
    integral_map (by fun_prop) hG.aestronglyMeasurable]

end AdversarialBco.Bit.Cpl
