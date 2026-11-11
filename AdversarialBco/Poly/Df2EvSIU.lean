/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvSICond
public import AdversarialBco.Poly.SrcToolsProof

@[expose] public section

/-!
# Lemma U on setting (E), in the pathwise form the three events read

A finite family `C` of increments `zSeq c s = A_{c,s}(σ_s, ξ_s) + B_{c,s}(σ_s, ξ_s) e_s - mean A_{c,s}(σ_s)` for
`s < m`, and `0` from the horizon `m` on, with `σ_s` measurable in `𝒢 s` and the draws and the noise of setting
(E). `lemmaU_setE`: with probability at least `1 - δ'`, for every `c ∈ C` and `t < m`, if the Gaussian integrals
`∑_{s ≤ t} ∫ (A_{c,s}² + B_{c,s}²)(σ_s, z) dγ(z)` are at most `V` and the increments up to `t` are at most `R` in
absolute value, then `|∑_{s ≤ t} zSeq c s| ≤ 3 (V l)^{1/2} + 2 R l` with
`l = log (4 n |C| max(κ R, κ V^{1/2})/δ')`. `V` and `R` are any functions of the path, of `c` and of `t`.

Proof: `cond_incr` gives the hypotheses of Lemma U (`lemmaU`) and bounds `E[zSeq c s² | 𝒢 s]` by the Gaussian
integral outside a null set; outside it the predictable variance is at most `V`, and `fkBound_mono` bounds Freedman's
level by `3 (V l)^{1/2} + 2 R l`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AdversarialBco.Poly.EvSI

variable {d : ℕ}

/-- Freedman's level is monotone in the predictable variance and in the range. -/
theorem fkBound_mono {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (X : ℕ → Ω → ℝ) (κ N δ V R : ℝ) (t : ℕ) (ω : Ω) (hκ : 0 < κ) (hN : 1 ≤ N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hV0 : 0 ≤ V) (hR : 1 ≤ κ * R) (hV : predVar μ ℱ X t ω ≤ V) (hX : ∀ s < t, |X s ω| ≤ R) :
    fkBound μ ℱ X κ N δ t ω ≤
      3 * Real.sqrt (V * Real.log (4 * N * max (κ * R) (κ * Real.sqrt V) / δ)) +
        2 * R * Real.log (4 * N * max (κ * R) (κ * Real.sqrt V) / δ) := by
  -- Unfold the definition of fkBound
  unfold fkBound
  -- Introduce abbreviations for readability
  set V0 := predVar μ ℱ X t ω with hV0_def
  set A := absMax (fun s ω => κ * X s ω) t ω with hA_def
  set l := Real.log (4 * N * max A (κ * Real.sqrt V0) / δ) with hl_def
  set l' := Real.log (4 * N * max (κ * R) (κ * Real.sqrt V) / δ) with hl'_def
  -- Goal: 3 * sqrt(V0 * l) + 2 * (A / κ) * l ≤ 3 * sqrt(V * l') + 2 * R * l'
  have hA_one : 1 ≤ A := by
    rw [hA_def, absMax]
    rw [Finset.le_fold_max]
    left
    exact le_refl 1
  have hA_le : A ≤ κ * R := by
    rw [hA_def, absMax]
    rw [Finset.fold_max_le]
    constructor
    · -- 1 ≤ κ * R
      exact hR
    · -- ∀ x ∈ Finset.range t, |κ * X x ω| ≤ κ * R
      intro s hs
      have hs_lt_t : s < t := Finset.mem_range.1 hs
      have hXs : |X s ω| ≤ R := hX s hs_lt_t
      calc
        |κ * X s ω| = |κ| * |X s ω| := abs_mul κ (X s ω)
        _ = κ * |X s ω| := by rw [abs_of_pos hκ]
        _ ≤ κ * R := mul_le_mul_of_nonneg_left hXs hκ.le
  have h_sqrt_V0_le_sqrt_V : Real.sqrt V0 ≤ Real.sqrt V :=
    Real.sqrt_le_sqrt hV
  have h_max_le : max A (κ * Real.sqrt V0) ≤ max (κ * R) (κ * Real.sqrt V) := by
    have h_sqrt_mul : κ * Real.sqrt V0 ≤ κ * Real.sqrt V :=
      mul_le_mul_of_nonneg_left h_sqrt_V0_le_sqrt_V hκ.le
    exact max_le_max hA_le h_sqrt_mul
  have hl_nonneg : 0 ≤ l := by
    rw [hl_def]
    have h_arg : 1 ≤ 4 * N * max A (κ * Real.sqrt V0) / δ := by
      refine (one_le_div hδ0).mpr ?_
      have h_max : 1 ≤ max A (κ * Real.sqrt V0) :=
        le_trans hA_one (le_max_left _ _)
      nlinarith
    exact Real.log_nonneg h_arg
  have hl'_nonneg : 0 ≤ l' := by
    rw [hl'_def]
    have h_arg : 1 ≤ 4 * N * max (κ * R) (κ * Real.sqrt V) / δ := by
      refine (one_le_div hδ0).mpr ?_
      have h_max : 1 ≤ max (κ * R) (κ * Real.sqrt V) := le_max_of_le_left hR
      nlinarith
    exact Real.log_nonneg h_arg
  have hl_le_l' : l ≤ l' := by
    rw [hl_def, hl'_def]
    refine Real.log_le_log ?_ ?_
    · -- 0 < 4*N*max A (κ*√V0)/δ
      have hA_pos : 0 < A := by linarith
      have h_max : 0 < max A (κ * Real.sqrt V0) :=
        lt_of_lt_of_le hA_pos (le_max_left _ _)
      have h_num : 0 < 4 * N * max A (κ * Real.sqrt V0) := by nlinarith
      exact div_pos h_num hδ0
    · -- 4*N*max A (κ*√V0)/δ ≤ 4*N*max (κ*R) (κ*√V)/δ
      have h_mul : 4 * N * max A (κ * Real.sqrt V0) ≤ 4 * N * max (κ * R) (κ * Real.sqrt V) := by
        nlinarith
      exact div_le_div_of_nonneg_right h_mul hδ0.le
  have hA_div_nonneg : 0 ≤ A / κ := div_nonneg (by linarith) hκ.le
  have hA_div_κ_le_R : A / κ ≤ R := by
    -- From hA_le: A ≤ κ * R and hκ > 0
    -- div_le_iff₀ hκ : A / κ ≤ R ↔ A ≤ R * κ
    -- But we have A ≤ κ * R, so use mul_comm
    refine (div_le_iff₀ hκ).mpr ?_
    simpa [mul_comm] using hA_le
  have h_mul1 : V0 * l ≤ V * l' := by
    by_cases hV0_nonneg : 0 ≤ V0
    · -- V0 ≥ 0: use mul_le_mul
      -- mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a*c ≤ b*d
      exact mul_le_mul hV hl_le_l' hl_nonneg hV0
    · -- V0 < 0: then V0 * l ≤ 0 ≤ V * l'
      have h_nonpos : V0 * l ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hl_nonneg
      have h_nonneg' : 0 ≤ V * l' := mul_nonneg hV0 hl'_nonneg
      linarith
  have h_mul2 : (A / κ) * l ≤ R * l' := by
    have h_nonneg_prod : 0 ≤ (A / κ) * l := mul_nonneg hA_div_nonneg hl_nonneg
    have h_nonneg_prod' : 0 ≤ R * l' := mul_nonneg (by linarith) hl'_nonneg
    nlinarith
  -- Now combine: 3*sqrt(V0*l) ≤ 3*sqrt(V*l') and 2*(A/κ)*l ≤ 2*R*l'
  have h_sqrt : Real.sqrt (V0 * l) ≤ Real.sqrt (V * l') :=
    Real.sqrt_le_sqrt h_mul1
  have h_main : 3 * Real.sqrt (V0 * l) + 2 * ((A / κ) * l) ≤
      3 * Real.sqrt (V * l') + 2 * (R * l') := by
    nlinarith
  simpa [mul_assoc] using h_main

/-- The increments of a family, `0` from the horizon `m` on. -/
noncomputable def zSeq {Ω S ι : Type*} (m : ℕ) (A B : ι → ℕ → S × (Fin d → ℝ) → ℝ) (σ : ℕ → Ω → S)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (c : ι) (s : ℕ) (ω : Ω) : ℝ :=
  if s < m then incr (A c s) (B c s) (σ s) (ξ s) (e s) ω else 0

theorem zSeq_of_lt {Ω S ι : Type*} {m : ℕ} (A B : ι → ℕ → S × (Fin d → ℝ) → ℝ) (σ : ℕ → Ω → S)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (c : ι) {s : ℕ} (hs : s < m) :
    zSeq m A B σ ξ e c s = incr (A c s) (B c s) (σ s) (ξ s) (e s) := by
  funext ω; simp [zSeq, hs]

theorem zSeq_of_ge {Ω S ι : Type*} {m : ℕ} (A B : ι → ℕ → S × (Fin d → ℝ) → ℝ) (σ : ℕ → Ω → S)
    (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ) (c : ι) {s : ℕ} (hs : m ≤ s) :
    zSeq m A B σ ξ e c s = 0 := by
  funext ω; simp [zSeq, not_lt.2 hs]

/-- The increment is measurable in `𝒢 (s + 1)`. -/
theorem measurable_incr {Ω S : Type*} [MeasurableSpace S] (𝒢 𝒢' : MeasurableSpace Ω) (h : 𝒢 ≤ 𝒢')
    (A B : S × (Fin d → ℝ) → ℝ) (hA : Measurable A) (hB : Measurable B) (σ : Ω → S) (ξ : Ω → Fin d → ℝ)
    (e : Ω → ℝ) (hσ : Measurable[𝒢] σ) (hξ : Measurable[𝒢'] ξ) (he : Measurable[𝒢'] e) :
    Measurable[𝒢'] (incr A B σ ξ e) := by
  have hσ' : Measurable[𝒢'] σ := hσ.mono h le_rfl
  have hp : Measurable[𝒢'] fun ω => (σ ω, ξ ω) := hσ'.prodMk hξ
  have hm : Measurable[𝒢'] fun ω => mean A (σ ω) := (measurable_mean hA).comp hσ'
  exact ((hA.comp hp).add ((hB.comp hp).mul he)).sub hm

theorem lemmaU_setE {Ω S ι : Type} [m0 : MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (C : Finset ι) (m n : ℕ) (hmn : m ≤ n)
    (σ : ℕ → Ω → S) (ξ : ℕ → Ω → Fin d → ℝ) (e : ℕ → Ω → ℝ)
    (hσ : ∀ s < m, Measurable[𝒢 s] (σ s)) (hξm : ∀ s, Measurable[𝒢 (s + 1)] (ξ s))
    (hlaw : ∀ s, μ.map (ξ s) = gam d) (hind : ∀ s, Indep (MeasurableSpace.comap (ξ s) inferInstance) (𝒢 s) μ)
    (hem : ∀ s, Measurable[𝒢 (s + 1)] (e s)) (hei : ∀ s, Integrable (fun ω => Real.exp (e s ω ^ 2)) μ)
    (hmean : ∀ s, μ[e s | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] =ᵐ[μ] 0)
    (hexp : ∀ s, μ[fun ω => Real.exp (e s ω ^ 2) | 𝒢 s ⊔ MeasurableSpace.comap (ξ s) inferInstance] ≤ᵐ[μ]
      fun _ => 2)
    (A B : ι → ℕ → S × (Fin d → ℝ) → ℝ) (hA : ∀ c s, s < m → Measurable (A c s))
    (hB : ∀ c s, s < m → Measurable (B c s)) (K : ι → ℝ) (k : ℕ) (hK : ∀ c, 0 ≤ K c)
    (hAK : ∀ c s, s < m → ∀ x, |A c s x| ≤ K c * (1 + ‖x.2‖) ^ k)
    (hBK : ∀ c s, s < m → ∀ x, |B c s x| ≤ K c * (1 + ‖x.2‖) ^ k)
    (κ δ' : ℝ) (hκ : 0 < κ) (hδ0 : 0 < δ') (hδ1 : δ' ≤ 1) (V R : ι → ℕ → Ω → ℝ) :
    μ {ω | ∃ c ∈ C, ∃ t < m, 0 ≤ V c t ω ∧ 1 ≤ κ * R c t ω ∧
        ∑ s ∈ Finset.range (t + 1), ∫ z, (A c s (σ s ω, z) ^ 2 + B c s (σ s ω, z) ^ 2) ∂(gam d) ≤ V c t ω ∧
        (∀ s ≤ t, |zSeq m A B σ ξ e c s ω| ≤ R c t ω) ∧
        3 * Real.sqrt (V c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ')) +
          2 * R c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ') <
          |∑ s ∈ Finset.range (t + 1), zSeq m A B σ ξ e c s ω|} ≤ ENNReal.ofReal δ' := by
  classical
  set Z := zSeq m A B σ ξ e with hZdef
  -- the conditional moments of each increment
  have hci : ∀ c s, s < m → _ := fun c s hs =>
    cond_incr (𝒢 s) μ (𝒢.le s) (σ s) (ξ s) (e s) (hσ s hs) ((hξm s).mono (𝒢.le _) le_rfl)
      ((hem s).mono (𝒢.le _) le_rfl) (hlaw s) (hind s) (hei s) (hmean s) (hexp s) (A c s) (B c s) (hA c s hs)
      (hB c s hs) (K c) k (hK c) (hAK c s hs) (hBK c s hs)
  -- the hypotheses of Lemma U
  have hZm : ∀ c ∈ C, ∀ t, StronglyMeasurable[𝒢 (t + 1)] (Z c t) := by
    intro c _ t
    by_cases ht : t < m
    · rw [hZdef, zSeq_of_lt A B σ ξ e c ht]
      exact (measurable_incr (𝒢 t) (𝒢 (t + 1)) (𝒢.mono (Nat.le_succ t)) (A c t) (B c t) (hA c t ht) (hB c t ht)
        (σ t) (ξ t) (e t) (hσ t ht) (hξm t) (hem t)).stronglyMeasurable
    · rw [hZdef, zSeq_of_ge A B σ ξ e c (not_lt.1 ht)]
      exact stronglyMeasurable_const
  have hZi : ∀ c ∈ C, ∀ t, Integrable (Z c t) μ := by
    intro c _ t
    by_cases ht : t < m
    · rw [hZdef, zSeq_of_lt A B σ ξ e c ht]; exact (hci c t ht).1
    · rw [hZdef, zSeq_of_ge A B σ ξ e c (not_lt.1 ht)]; exact integrable_zero _ _ _
  have hZ2 : ∀ c ∈ C, ∀ t, Integrable (fun ω => Z c t ω ^ 2) μ := by
    intro c _ t
    by_cases ht : t < m
    · rw [hZdef, zSeq_of_lt A B σ ξ e c ht]; exact (hci c t ht).2.1
    · rw [hZdef, zSeq_of_ge A B σ ξ e c (not_lt.1 ht)]
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact integrable_zero _ _ _
  have hZ0 : ∀ c ∈ C, ∀ t, μ[Z c t | 𝒢 t] =ᵐ[μ] 0 := by
    intro c _ t
    by_cases ht : t < m
    · rw [hZdef, zSeq_of_lt A B σ ξ e c ht]; exact (hci c t ht).2.2.1
    · rw [hZdef, zSeq_of_ge A B σ ξ e c (not_lt.1 ht), condExp_zero]
  have hU := lemmaU μ 𝒢 C Z hZm hZi hZ2 hZ0 n κ δ' hκ hδ0 hδ1
  -- the variance bounds, outside a null set
  have hae : ∀ᵐ ω ∂μ, ∀ c ∈ C, ∀ s ∈ Finset.range m,
      μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤ ∫ z, (A c s (σ s ω, z) ^ 2 + B c s (σ s ω, z) ^ 2) ∂(gam d) := by
    refine (Filter.eventually_all_finset C).2 fun c _ => (Filter.eventually_all_finset _).2 fun s hs => ?_
    have hs' : s < m := Finset.mem_range.1 hs
    have h := (hci c s hs').2.2.2
    have e1 : (fun ω => Z c s ω ^ 2) = fun ω => incr (A c s) (B c s) (σ s) (ξ s) (e s) ω ^ 2 := by
      rw [hZdef, zSeq_of_lt A B σ ξ e c hs']
    rw [e1]
    exact h
  set G := {ω | ∃ c ∈ C, ∃ t < m, 0 ≤ V c t ω ∧ 1 ≤ κ * R c t ω ∧
        ∑ s ∈ Finset.range (t + 1), ∫ z, (A c s (σ s ω, z) ^ 2 + B c s (σ s ω, z) ^ 2) ∂(gam d) ≤ V c t ω ∧
        (∀ s ≤ t, |zSeq m A B σ ξ e c s ω| ≤ R c t ω) ∧
        3 * Real.sqrt (V c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ')) +
          2 * R c t ω * Real.log (4 * (n * C.card) * max (κ * R c t ω) (κ * Real.sqrt (V c t ω)) / δ') <
          |∑ s ∈ Finset.range (t + 1), zSeq m A B σ ξ e c s ω|} with hG
  set Nset := {ω | ¬ ∀ c ∈ C, ∀ s ∈ Finset.range m,
      μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤ ∫ z, (A c s (σ s ω, z) ^ 2 + B c s (σ s ω, z) ^ 2) ∂(gam d)} with hN
  have hN0 : μ Nset = 0 := ae_iff.1 hae
  have hsub : G ⊆ {ω | ∃ c ∈ C, ∃ t ∈ Finset.Icc 1 n,
      fkBound μ 𝒢 (Z c) κ (n * C.card) δ' t ω < |∑ s ∈ Finset.range t, Z c s ω|} ∪ Nset := by
    intro ω hω
    by_cases hgood : ω ∈ Nset
    · exact Or.inr hgood
    · left
      have hgood' : ∀ c ∈ C, ∀ s ∈ Finset.range m,
          μ[fun ω => Z c s ω ^ 2 | 𝒢 s] ω ≤ ∫ z, (A c s (σ s ω, z) ^ 2 + B c s (σ s ω, z) ^ 2) ∂(gam d) := by
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

end AdversarialBco.Poly.EvSI
