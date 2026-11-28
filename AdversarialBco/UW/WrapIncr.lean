/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# The wrapper of Lemma U for the weighted increments

One round of setting (E) as in Poly/Df2EvSICond.lean: a parameter `σ` measurable in `𝒢`, a draw `ξ` of law `gam d`
independent of `𝒢`, a noise `e` centred with `E[exp(e²)] ≤ 2` given `𝒢 ⊔ σ(ξ)`. The observation is
`Y = E(σ, ξ) + P(σ, ξ) e`, the weighted observation `W(ξ, Y)` with `|W(x, y)| ≤ |y|`, and the increment
`X = W(ξ, Y) D(σ, ξ)` for a direction `D`.

* `cond_sq_le`: `E[(A + B e)² | 𝒢] ≤ ∫ (A² + B²)(σ, z) dγ(z)`, the uncentred second moment (the computation of
  `cond_incr` without the mean);
* `cond_incr_w`, `condIncrW : CondIncrW` (W1): `X` is square integrable, `X - E[X | 𝒢]` is centred given `𝒢`, and its
  conditional variance is at most `∫ (E² + P²) D² dγ`, since `X² ≤ (Y D)²` and the variance is below the second
  moment (`condVar_ae_le_condExp_sq`);
* `lemmaU_setW`, `lemmaUSetW : LemmaUSetW` (W3): Lemma U (`lemmaU`) for the family `X c s - E[X c s | 𝒢 s]`, the
  proof of `lemmaU_setE` with `cond_incr` replaced by (W1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-! ## The uncentred second moment -/

/-- `E[(A + B e)² | 𝒢] ≤ ∫ (A² + B²)(σ, z) dγ(z)` for `A`, `B` of polynomial growth in the draw. -/
theorem cond_sq_le {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (hσ : Measurable[𝒢] σ) (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (A B : S × (Fin d → ℝ) → ℝ) (hA : Measurable A) (hB : Measurable B) (K : ℝ) (k : ℕ)
    (hAK : ∀ x, |A x| ≤ K * (1 + ‖x.2‖) ^ k) (hBK : ∀ x, |B x| ≤ K * (1 + ‖x.2‖) ^ k) :
    Integrable (fun ω => (A (σ ω, ξ ω) + B (σ ω, ξ ω) * e ω) ^ 2) μ ∧
      μ[fun ω => (A (σ ω, ξ ω) + B (σ ω, ξ ω) * e ω) ^ 2 | 𝒢] ≤ᵐ[μ]
        fun ω => ∫ z, (A (σ ω, z) ^ 2 + B (σ ω, z) ^ 2) ∂(gam d) := by
  classical
  have hξle : MeasurableSpace.comap ξ inferInstance ≤ m0 := hξ.comap_le
  have h𝒢G : (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) ≤ m0 := sup_le h𝒢 hξle
  have hσ' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] σ := hσ.mono le_sup_left le_rfl
  have hξ' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ξ :=
    (comap_measurable ξ).mono le_sup_right le_rfl
  set a : Ω → ℝ := fun ω => A (σ ω, ξ ω) with ha_def
  set b : Ω → ℝ := fun ω => B (σ ω, ξ ω) with hb_def
  have ha' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] a := hA.comp (hσ'.prodMk hξ')
  have hb' : Measurable[(𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] b := hB.comp (hσ'.prodMk hξ')
  have ha : Measurable a := ha'.mono h𝒢G le_rfl
  have hb : Measurable b := hb'.mono h𝒢G le_rfl
  have hdom := fun {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (C : ℝ) (i j : ℕ) (hi : i ≤ 2)
      (hfb : ∀ ω, |f ω| ≤ C * ((1 + ‖ξ ω‖) ^ j * (1 + |e ω|) ^ i)) =>
    integrable_of_dom hξ he hlaw hei hf C i j hi hfb
  have hab : ∀ ω, |a ω| ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => hAK (σ ω, ξ ω)
  have hbb : ∀ ω, |b ω| ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => hBK (σ ω, ξ ω)
  have heb : ∀ ω, |e ω| ≤ 1 + |e ω| := fun ω => by linarith
  have hP : ∀ ω, 0 ≤ (1 + ‖ξ ω‖) ^ k := fun ω => pow_nonneg (by positivity) k
  have hKp : ∀ ω, 0 ≤ K * (1 + ‖ξ ω‖) ^ k := fun ω => (abs_nonneg _).trans (hab ω)
  have i_e : Integrable e μ := hdom he.aestronglyMeasurable 1 1 0 (by norm_num) fun ω => by simp
  have i_e2 : Integrable (fun ω => e ω ^ 2) μ :=
    hdom (he.pow_const 2).aestronglyMeasurable 1 2 0 le_rfl fun ω => by
      rw [abs_pow]; simpa using pow_le_pow_left₀ (abs_nonneg _) (heb ω) 2
  have i_w1 : Integrable (fun ω => a ω ^ 2) μ := by
    refine hdom (ha.pow_const 2).aestronglyMeasurable (K ^ 2) 0 (2 * k) (by norm_num) fun ω => ?_
    rw [abs_pow, pow_mul']
    simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hab ω) 2
  have i_w2 : Integrable (fun ω => (2 * a ω * b ω) * e ω) μ := by
    refine hdom (((ha.const_mul 2).mul hb).mul he).aestronglyMeasurable (2 * K * K) 1 (2 * k)
      (by norm_num) fun ω => ?_
    rw [abs_mul, abs_mul, abs_mul, abs_two, pow_one, pow_mul']
    have h1 := hab ω; have h2 := hbb ω; have h3 := heb ω
    have hk := hKp ω
    calc 2 * |a ω| * |b ω| * |e ω|
        ≤ 2 * (K * (1 + ‖ξ ω‖) ^ k) * (K * (1 + ‖ξ ω‖) ^ k) * (1 + |e ω|) := by
          refine mul_le_mul ?_ h3 (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hk) hk)
          refine mul_le_mul ?_ h2 (abs_nonneg _) (mul_nonneg (by norm_num) hk)
          linarith
      _ = _ := by ring
  have i_w3 : Integrable (fun ω => b ω ^ 2 * e ω ^ 2) μ := by
    refine hdom ((hb.pow_const 2).mul (he.pow_const 2)).aestronglyMeasurable (K ^ 2) 2 (2 * k) le_rfl fun ω => ?_
    rw [abs_mul, abs_pow, abs_pow, pow_mul']
    have h2 := hbb ω; have h3 := heb ω
    calc |b ω| ^ 2 * |e ω| ^ 2 ≤ (K * (1 + ‖ξ ω‖) ^ k) ^ 2 * (1 + |e ω|) ^ 2 := by gcongr
      _ = _ := by ring
  have i_b2 : Integrable (fun ω => b ω ^ 2) μ := by
    refine hdom (hb.pow_const 2).aestronglyMeasurable (K ^ 2) 0 (2 * k) (by norm_num) fun ω => ?_
    rw [abs_pow, pow_mul']
    simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hbb ω) 2
  have hZ2 : (fun ω => (a ω + b ω * e ω) ^ 2) =
      fun ω => (a ω ^ 2 + (2 * a ω * b ω) * e ω) + b ω ^ 2 * e ω ^ 2 := by
    funext ω; ring
  have i_Z2 : Integrable (fun ω => (a ω + b ω * e ω) ^ 2) μ := by rw [hZ2]; exact (i_w1.add i_w2).add i_w3
  refine ⟨i_Z2, ?_⟩
  have hle' : μ[fun ω => (a ω + b ω * e ω) ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ≤ᵐ[μ]
      fun ω => a ω ^ 2 + b ω ^ 2 := by
    rw [hZ2]
    have h1 := condExp_add (i_w1.add i_w2) i_w3 (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
    have h1' := condExp_add i_w1 i_w2 (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)
    have h2 : μ[fun ω => a ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] = fun ω => a ω ^ 2 :=
      condExp_of_stronglyMeasurable h𝒢G (ha'.pow_const 2).stronglyMeasurable i_w1
    have h3 := condExp_mul_of_stronglyMeasurable_left (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance))
      ((ha'.const_mul 2).mul hb').stronglyMeasurable i_w2 i_e
    have h4 := condExp_mul_of_stronglyMeasurable_left (m := (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance))
      (hb'.pow_const 2).stronglyMeasurable i_w3 i_e2
    have h5 := condExp_sq_le_one (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance) h𝒢G he hei hee
    filter_upwards [h1, h1', h3, h4, h5, hem] with ω h1 h1' h3 h4 h5 h6
    have h3' : μ[fun ω => (2 * a ω * b ω) * e ω | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω =
        (2 * a ω * b ω) * μ[e | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω := h3
    have h4' : μ[fun ω => b ω ^ 2 * e ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω =
        b ω ^ 2 * μ[fun ω => e ω ^ 2 | (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)] ω := h4
    refine le_of_eq_of_le h1 ?_
    rw [Pi.add_apply]
    refine le_of_eq_of_le (congrArg (· + _) h1') ?_
    rw [Pi.add_apply, h2, h3', h4', h6]
    simp only [Pi.zero_apply, mul_zero, add_zero]
    have hb2 : 0 ≤ b ω ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h5 hb2]
  have hT := (condExp_condExp_of_le (f := fun ω => (a ω + b ω * e ω) ^ 2) (μ := μ)
    (le_sup_left : 𝒢 ≤ (𝒢 ⊔ MeasurableSpace.comap ξ inferInstance)) h𝒢G).symm
  have hMono := condExp_mono (m := 𝒢) integrable_condExp (i_w1.add i_b2) hle'
  have hF : Measurable fun x : S × (Fin d → ℝ) => A x ^ 2 + B x ^ 2 := (hA.pow_const 2).add (hB.pow_const 2)
  have hFR := lemmaFR Ω S (Fin d → ℝ) 𝒢 μ σ ξ (fun x => A x ^ 2 + B x ^ 2) h𝒢 hσ hξ hind hF (i_w1.add i_b2)
  rw [hlaw] at hFR
  filter_upwards [hT, hMono, hFR] with ω hT hMono hFR
  rw [hT]
  exact hMono.trans (le_of_eq hFR)

/-! ## (W1) -/

/-- **(W1) `cond_incr_w`**: the weighted increment `X = W(ξ, E + P e) D`, centred at its conditional mean, is a
martingale difference with the variance proxy `∫ (E² + P²) D² dγ`. -/
theorem cond_incr_w {Ω S : Type} (𝒢 : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ m0) (σ : Ω → S) (ξ : Ω → Fin d → ℝ) (e : Ω → ℝ)
    (hσ : Measurable[𝒢] σ) (hξ : Measurable ξ) (he : Measurable e) (hlaw : μ.map ξ = gam d)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) 𝒢 μ)
    (hei : Integrable (fun ω => Real.exp (e ω ^ 2)) μ)
    (hem : μ[e | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] =ᵐ[μ] 0)
    (hee : μ[fun ω => Real.exp (e ω ^ 2) | 𝒢 ⊔ MeasurableSpace.comap ξ inferInstance] ≤ᵐ[μ] fun _ => 2)
    (E P D : S × (Fin d → ℝ) → ℝ) (hE : Measurable E) (hP : Measurable P) (hD : Measurable D)
    (K : ℝ) (k : ℕ) (hK : 0 ≤ K) (hEK : ∀ x, |E x| ≤ K * (1 + ‖x.2‖) ^ k)
    (hPK : ∀ x, |P x| ≤ K * (1 + ‖x.2‖) ^ k) (hDK : ∀ x, |D x| ≤ K * (1 + ‖x.2‖) ^ k)
    (Wf : (Fin d → ℝ) → ℝ → ℝ) (hW : Measurable (Function.uncurry Wf)) (hWle : ∀ x y, |Wf x y| ≤ |y|) :
    Integrable (fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω)) μ ∧
      Integrable (fun ω => (Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω)) ^ 2) μ ∧
      μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) -
          μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω | 𝒢] =ᵐ[μ] 0 ∧
      μ[fun ω => (Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) -
          μ[fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) | 𝒢] ω) ^ 2 | 𝒢] ≤ᵐ[μ]
        fun ω => ∫ z, (E (σ ω, z) ^ 2 + P (σ ω, z) ^ 2) * D (σ ω, z) ^ 2 ∂(gam d) := by
  set A : S × (Fin d → ℝ) → ℝ := fun x => E x * D x with hAdef
  set B : S × (Fin d → ℝ) → ℝ := fun x => P x * D x with hBdef
  set X : Ω → ℝ := fun ω => Wf (ξ ω) (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) with hXdef
  have hσ0 : Measurable σ := hσ.mono h𝒢 le_rfl
  have hp : Measurable fun ω => (σ ω, ξ ω) := hσ0.prodMk hξ
  have hYm : Measurable fun ω => E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω := (hE.comp hp).add ((hP.comp hp).mul he)
  have hXm : Measurable X := (hW.comp (hξ.prodMk hYm)).mul (hD.comp hp)
  have hAK : ∀ x, |A x| ≤ K ^ 2 * (1 + ‖x.2‖) ^ (2 * k) := by
    intro x
    rw [hAdef, abs_mul, pow_mul', sq, sq, mul_mul_mul_comm]
    exact mul_le_mul (hEK x) (hDK x) (abs_nonneg _) (mul_nonneg hK (pow_nonneg (by positivity) _))
  have hBK : ∀ x, |B x| ≤ K ^ 2 * (1 + ‖x.2‖) ^ (2 * k) := by
    intro x
    rw [hBdef, abs_mul, pow_mul', sq, sq, mul_mul_mul_comm]
    exact mul_le_mul (hPK x) (hDK x) (abs_nonneg _) (mul_nonneg hK (pow_nonneg (by positivity) _))
  obtain ⟨i_Z2, hsq⟩ := cond_sq_le 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee A B (hE.mul hD) (hP.mul hD)
    (K ^ 2) (2 * k) hAK hBK
  have hYD : ∀ ω, A (σ ω, ξ ω) + B (σ ω, ξ ω) * e ω = (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω) * D (σ ω, ξ ω) := by
    intro ω; simp only [hAdef, hBdef]; ring
  have hXle : ∀ ω, X ω ^ 2 ≤ (A (σ ω, ξ ω) + B (σ ω, ξ ω) * e ω) ^ 2 := by
    intro ω
    rw [hYD, hXdef, mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs, ← sq_abs (E (σ ω, ξ ω) + P (σ ω, ξ ω) * e ω)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hWle _ _) 2
  have i_X2 : Integrable (fun ω => X ω ^ 2) μ :=
    i_Z2.mono' (hXm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hXle ω)
  have hX2 : MemLp X 2 μ := (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 i_X2
  have i_X : Integrable X μ := hX2.integrable one_le_two
  refine ⟨i_X, i_X2, ?_, ?_⟩
  · have h1 := condExp_sub (m := 𝒢) i_X (integrable_condExp (m := 𝒢) (μ := μ) (f := X))
    have h2 : μ[μ[X | 𝒢] | 𝒢] = μ[X | 𝒢] :=
      condExp_of_stronglyMeasurable h𝒢 stronglyMeasurable_condExp integrable_condExp
    filter_upwards [h1] with ω h1
    have e1 : (fun ω => X ω - μ[X | 𝒢] ω) = X - μ[X | 𝒢] := rfl
    rw [e1, h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
  · have hV := condVar_ae_le_condExp_sq h𝒢 hX2
    have hM := condExp_mono (m := 𝒢) i_X2 i_Z2 (Filter.Eventually.of_forall hXle)
    filter_upwards [hV, hM, hsq] with ω hV hM hsq
    have e2 : ∫ z, (A (σ ω, z) ^ 2 + B (σ ω, z) ^ 2) ∂(gam d) =
        ∫ z, (E (σ ω, z) ^ 2 + P (σ ω, z) ^ 2) * D (σ ω, z) ^ 2 ∂(gam d) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [hAdef, hBdef]; ring)
    rw [← e2]
    exact hV.trans (hM.trans hsq)

/-- **(W1)** as the interface states it. -/
theorem condIncrW : CondIncrW := by
  intro d Ω S 𝒢 m0 _ μ _ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee E P D hE hP hD K k hK hEK hPK hDK Wf hW hWle
  exact cond_incr_w 𝒢 μ h𝒢 σ ξ e hσ hξ he hlaw hind hei hem hee E P D hE hP hD K k hK hEK hPK hDK Wf hW hWle


/-! ## (W3) -/

/-- **(W3) `lemmaU_setW`**: Lemma U for the increments `X c s - E[X c s | 𝒢 s]`, `X c s = W(ξ_s, E_s + P_s e_s) D_{c,s}`
for `s < m` and `0` from the horizon `m` on; the levels `V`, `R` are any functions of the path. -/
theorem lemmaU_setW {Ω S ι : Type} [m0 : MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (C : Finset ι) (m n : ℕ) (hmn : m ≤ n)
    (σ : ℕ → Ω → S) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hσ : ∀ s < m, Measurable[𝒢 s] (σ s)) (hξm : ∀ s, Measurable[𝒢 (s + 1)] (ξ s))
    (hlaw : ∀ s, μ.map (ξ s) = gam d) (hind : ∀ s, Indep (MeasurableSpace.comap (ξ s) inferInstance) (𝒢 s) μ)
    (hem : ∀ s, Measurable[𝒢 (s + 1)] (e s)) (hei : ∀ s, Integrable (fun ω => Real.exp (e s ω ^ 2)) μ)
    (hmean : ∀ s, μ[e s | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] =ᵐ[μ] 0)
    (hexp : ∀ s, μ[fun ω => Real.exp (e s ω ^ 2) | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] ≤ᵐ[μ]
      fun _ => 2)
    (E P : ℕ → S × (Fin d → ℝ) → ℝ) (D : ι → ℕ → S × (Fin d → ℝ) → ℝ)
    (hE : ∀ s < m, Measurable (E s)) (hP : ∀ s < m, Measurable (P s)) (hD : ∀ c s, s < m → Measurable (D c s))
    (Kc : ι → ℝ) (k : ℕ) (hK : ∀ c, 0 ≤ Kc c)
    (hEK : ∀ c s, s < m → ∀ x, |E s x| ≤ Kc c * (1 + ‖x.2‖) ^ k)
    (hPK : ∀ c s, s < m → ∀ x, |P s x| ≤ Kc c * (1 + ‖x.2‖) ^ k)
    (hDK : ∀ c s, s < m → ∀ x, |D c s x| ≤ Kc c * (1 + ‖x.2‖) ^ k)
    (Wf : (Fin d → ℝ) → ℝ → ℝ) (hW : Measurable (Function.uncurry Wf)) (hWle : ∀ x y, |Wf x y| ≤ |y|)
    (κ δ' : ℝ) (hκ : 0 < κ) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1) (V R : ι → ℕ → Ω → ℝ) (X : ι → ℕ → Ω → ℝ)
    (hX : ∀ c s, X c s = fun ω => if s < m then
      Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) else 0) :
    μ {ω | ∃ c ∈ C, ∃ t < m, 0 ≤ V c t ω ∧ 1 ≤ κ * R c t ω ∧
        ∑ s ∈ Finset.range (t + 1),
          ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d) ≤ V c t ω ∧
        (∀ s ≤ t, |X c s ω - μ[X c s | 𝒢 s] ω| ≤ R c t ω) ∧
        3 * Real.sqrt (V c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ')) +
          2 * R c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ') <
          |∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω)|} ≤ ENNReal.ofReal δ' := by
  classical
  set Z : ι → ℕ → Ω → ℝ := fun c s ω => X c s ω - μ[X c s | 𝒢 s] ω with hZdef
  have hci : ∀ c s, s < m → _ := fun c s hs =>
    cond_incr_w (𝒢 s) μ (𝒢.le s) (σ s) (ξ s) (e s) (hσ s hs) ((hξm s).mono (𝒢.le _) le_rfl)
      ((hem s).mono (𝒢.le _) le_rfl) (hlaw s) (hind s) (hei s) (hmean s) (hexp s) (E s) (P s) (D c s)
      (hE s hs) (hP s hs) (hD c s hs) (Kc c) k (hK c) (hEK c s hs) (hPK c s hs) (hDK c s hs) Wf hW hWle
  have hXlt : ∀ c s, s < m → X c s = fun ω =>
      Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) := by
    intro c s hs; rw [hX]; funext ω; simp [hs]
  have hXge : ∀ c s, m ≤ s → X c s = 0 := by
    intro c s hs; rw [hX]; funext ω; simp [not_lt.2 hs]
  have hXm : ∀ c s, Measurable[𝒢 (s + 1)] (X c s) := by
    intro c s
    by_cases hs : s < m
    · rw [hXlt c s hs]
      have hσ' : Measurable[𝒢 (s + 1)] (σ s) := (hσ s hs).mono (𝒢.mono (Nat.le_succ s)) le_rfl
      have hp : Measurable[𝒢 (s + 1)] fun ω => (σ s ω, ξ s ω) := hσ'.prodMk (hξm s)
      have hY : Measurable[𝒢 (s + 1)] fun ω => E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω :=
        ((hE s hs).comp hp).add (((hP s hs).comp hp).mul (hem s))
      exact (hW.comp ((hξm s).prodMk hY)).mul ((hD c s hs).comp hp)
    · rw [hXge c s (not_lt.1 hs)]; exact measurable_const
  have hX2 : ∀ c t, MemLp (X c t) 2 μ := by
    intro c t
    refine (memLp_two_iff_integrable_sq ((hXm c t).mono (𝒢.le (t + 1)) le_rfl).aestronglyMeasurable).2 ?_
    by_cases ht : t < m
    · rw [hXlt c t ht]; exact (hci c t ht).2.1
    · rw [hXge c t (not_lt.1 ht)]; simp
  have hZ2m : ∀ c t, MemLp (Z c t) 2 μ := fun c t => (hX2 c t).sub ((hX2 c t).condExp one_le_two)
  -- the hypotheses of Lemma U
  have hZm : ∀ c ∈ C, ∀ t, StronglyMeasurable[𝒢 (t + 1)] (Z c t) := fun c _ t =>
    (hXm c t).stronglyMeasurable.sub (stronglyMeasurable_condExp.mono (𝒢.mono (Nat.le_succ t)))
  have hZi : ∀ c ∈ C, ∀ t, Integrable (Z c t) μ := fun c _ t => (hZ2m c t).integrable one_le_two
  have hZ2 : ∀ c ∈ C, ∀ t, Integrable (fun ω => Z c t ω ^ 2) μ := fun c _ t => (hZ2m c t).integrable_sq
  have hZ0 : ∀ c ∈ C, ∀ t, μ[Z c t | 𝒢 t] =ᵐ[μ] 0 := by
    intro c _ t
    by_cases ht : t < m
    · have h := (hci c t ht).2.2.1
      have e1 : Z c t = fun ω => Wf (ξ t ω) (E t (σ t ω, ξ t ω) + P t (σ t ω, ξ t ω) * e t ω) * D c t (σ t ω, ξ t ω) -
          μ[fun ω => Wf (ξ t ω) (E t (σ t ω, ξ t ω) + P t (σ t ω, ξ t ω) * e t ω) * D c t (σ t ω, ξ t ω) | 𝒢 t] ω := by
        simp only [hZdef, hXlt c t ht]
      rw [e1]; exact h
    · have e1 : Z c t = 0 := by
        funext ω; simp only [hZdef, hXge c t (not_lt.1 ht), condExp_zero, Pi.zero_apply, sub_zero]
      rw [e1, condExp_zero]
  have hU := lemmaU μ 𝒢 C Z hZm hZi hZ2 hZ0 n κ δ' hκ hδ0 hδ1
  -- the variance bounds, outside a null set
  have hae : ∀ᵐ ω ∂μ, ∀ c ∈ C, ∀ s ∈ Finset.range m,
      μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤
        ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d) := by
    refine (Filter.eventually_all_finset C).2 fun c _ => (Filter.eventually_all_finset _).2 fun s hs => ?_
    have hs' : s < m := Finset.mem_range.1 hs
    have h := (hci c s hs').2.2.2
    have e1 : (fun ω => Z c s ω ^ 2) = fun ω =>
        (Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) -
          μ[fun ω => Wf (ξ s ω) (E s (σ s ω, ξ s ω) + P s (σ s ω, ξ s ω) * e s ω) * D c s (σ s ω, ξ s ω) |
            𝒢 s] ω) ^ 2 := by
      simp only [hZdef, hXlt c s hs']
    rw [e1]
    exact h
  set G := {ω | ∃ c ∈ C, ∃ t < m, 0 ≤ V c t ω ∧ 1 ≤ κ * R c t ω ∧
        ∑ s ∈ Finset.range (t + 1),
          ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d) ≤ V c t ω ∧
        (∀ s ≤ t, |X c s ω - μ[X c s | 𝒢 s] ω| ≤ R c t ω) ∧
        3 * Real.sqrt (V c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ')) +
          2 * R c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ') <
          |∑ s ∈ Finset.range (t + 1), (X c s ω - μ[X c s | 𝒢 s] ω)|} with hG
  set Nset := {ω | ¬ ∀ c ∈ C, ∀ s ∈ Finset.range m, μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤
      ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d)} with hN
  have hN0 : μ Nset = 0 := ae_iff.1 hae
  have hsub : G ⊆ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
      fkBound μ 𝒢 (Z c) κ (n * C.card) δ' t ω < |∑ s ∈ Finset.range t, Z c s ω|} ∪ Nset := by
    intro ω hω
    by_cases hgood : ω ∈ Nset
    · exact Or.inr hgood
    · left
      have hgood' : ∀ c ∈ C, ∀ s ∈ Finset.range m, μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤
          ∫ z, (E s (σ s ω, z) ^ 2 + P s (σ s ω, z) ^ 2) * D c s (σ s ω, z) ^ 2 ∂(gam d) := by
        simpa [hN] using hgood
      obtain ⟨c, hc, t, ht, hV0, hR1, hVt, hRt, hlt⟩ := hω
      refine ⟨c, hc, t + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, lt_of_le_of_lt ?_ hlt⟩
      have hNc : (1 : ℝ) ≤ n * C.card := by
        have h1 : 1 ≤ n := by omega
        have h2 : 1 ≤ C.card := Finset.card_pos.2 ⟨c, hc⟩
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have : (1 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast h2
        nlinarith
      refine fkBound_mono μ 𝒢 (Z c) κ (n * C.card) δ' (V c t ω) (R c t ω) (t + 1) ω hκ hNc hδ0 hδ1 hV0 hR1 ?_ ?_
      · unfold predVar
        refine le_trans (Finset.sum_le_sum fun s hs => hgood' c hc s ?_) hVt
        exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hs) (by omega))
      · intro s hs
        exact hRt s (by omega)
  calc μ G ≤ μ ({ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
        fkBound μ 𝒢 (Z c) κ (n * C.card) δ' t ω < |∑ s ∈ Finset.range t, Z c s ω|} ∪ Nset) := measure_mono hsub
    _ ≤ μ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
        fkBound μ 𝒢 (Z c) κ (n * C.card) δ' t ω < |∑ s ∈ Finset.range t, Z c s ω|} + μ Nset :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal δ' := by rw [hN0, add_zero]; exact hU

/-- **(W3)** as the interface states it. -/
theorem lemmaUSetW : LemmaUSetW := by
  intro d Ω S ι m0 _ μ _ 𝒢 C m n hmn σ ξ e hσ hξm hlaw hind hem hei hmean hexp E P D hE hP hD Kc k hK hEK hPK hDK
    Wf hW hWle κ δ' hκ hδ0 hδ1 V R
  exact lemmaU_setW μ 𝒢 C m n hmn σ ξ e hσ hξm hlaw hind hem hei hmean hexp E P D hE hP hD Kc k hK hEK hPK hDK
    Wf hW hWle κ δ' hκ hδ0 hδ1 V R _ fun _ _ => rfl

end AdversarialBco.UW
