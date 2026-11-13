/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowSetE
public import AdversarialBco.Bit.ShadowFarm
public import AdversarialBco.Poly.Df2PropGTools

@[expose] public section

/-!
# Step 2 of SHADOW: a decoupled round with a small shift is rare

`coupStepProp_holds : CoupStepProp`: round `t` decouples with a shift whose bound of the coupling lemma is at most
`κ0 + κ1 |ε_t|` with probability at most `κ0 + κ1`. The pair (shift, `ε_t`) is `F_t`-measurable, the coupling
coordinates are three standard Gaussians independent of `F_t` (`zc_law`, `zc_indep`), (O2-C) bounds the section of
the decoupling set, and `E |ε_t| ≤ 1`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

theorem tvB_measurable : Measurable fun x : ℝ × ℝ => tvB x.1 x.2 := by
  unfold tvB; fun_prop

/-- Step 2 of SHADOW. -/
theorem coupStepProp_holds : CoupStepProp := by
  intro d n δ K ν B κ0 κ1 hreg hKc hKconv hν hpos hC hTV hB hκ0 hκ1 t
  have := hν.1
  have hmode := mode_meas B δ hreg hKc hKconv hpos hB hC t
  have hX : Measurable[Fσ d t] fun ω : WΩ => (B.shR δ t ω, ω.2 t) :=
    (shR_meas B δ hB hmode).prodMk ((Measurable.of_comap_le le_sup_right : Measurable[Fσ d t] fun ω : WΩ => ω.2 t))
  have hFle := Fσ_le_m0 (d := d) t
  have hZ : Measurable (zc d t) := (meas_zc t).mono ((cσ d).le (t + 1)) le_rfl
  set D : Set (((ℝ × ℝ) × ℝ) × (Fin 3 → ℝ)) := {p | B.Coup p.1.1.1 p.1.1.2 p.2 ≠ p.1.1.1 + p.1.1.2 * p.2 0 / 2}
  set Bs : Set ((ℝ × ℝ) × ℝ) := {x | 0 < x.1.2 ∧ tvB x.1.1 x.1.2 ≤ κ0 + κ1 * |x.2|}
  have hD : MeasurableSet D := by
    have hc := hC.meas.comp (show Measurable fun p : ((ℝ × ℝ) × ℝ) × (Fin 3 → ℝ) => (p.1.1.1, p.1.1.2, p.2) by
      fun_prop)
    exact (measurableSet_eq_fun hc (by fun_prop)).compl
  have hBs : MeasurableSet Bs := by
    have h1 : Measurable fun x : (ℝ × ℝ) × ℝ => tvB x.1.1 x.1.2 := tvB_measurable.comp measurable_fst
    have h2 : Measurable fun x : (ℝ × ℝ) × ℝ => κ0 + κ1 * |x.2| := by fun_prop
    exact (measurableSet_lt (f := fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) (g := fun x => x.1.2) measurable_const
      (by fun_prop)).inter (measurableSet_le h1 h2)
  have hcore := step2_core (Fσ d t) (μs ν) hFle (fun ω : WΩ => (B.shR δ t ω, ω.2 t)) hX (zc d t) hZ
    (zc_indep ν t) D hD Bs hBs (fun x => κ0 + κ1 * |x.2|) (by fun_prop) (by
      rintro ⟨⟨m, r⟩, e⟩ ⟨hr, hb⟩
      rw [zc_law ν t]
      exact (hTV m r hr).trans (ENNReal.ofReal_le_ofReal hb))
  have hnoise : ∫⁻ ω, ENNReal.ofReal |(fun ω : WΩ => ω.2 t) ω| ∂(μs ν) ≤ 1 := by
    have h1 := PropG.noise_abs_lintegral ν hν t
    rw [← map_snd_world ν, lintegral_map (by fun_prop) measurable_snd] at h1
    exact h1
  have hint := lintegral_affine_abs (μs ν) (fun ω : WΩ => ω.2 t) (by fun_prop) hnoise κ0 κ1 hκ0 hκ1
  refine le_trans (le_of_eq ?_) (hcore.trans hint)
  rfl

end AdversarialBco.Bit.Cpl
