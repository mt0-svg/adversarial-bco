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

namespace Run

variable {n : ℕ} {K : Set (E d)} {B : Run d n K} {δ : ℝ}

theorem goodPos_of_case {ω : WΩ} (hq : B.Case δ ω) : PropG.GoodPos K (df2oPar d n δ).R (B.pos ω) := by
  obtain ⟨h1, h2, h3, -⟩ := good_unpack hq
  exact ⟨h1, h2, h3⟩

section Case

variable (hKconv : Convex ℝ K) (hKc : IsClosed K) {ω : WΩ} (hq : B.Case δ ω) (heps0 : 0 < (df2oPar d n δ).eps)
  (heps1 : (df2oPar d n δ).eps < 1)
include hKconv hKc hq heps0 heps1

/-- On `Case`, a round of P° from a mode other than `off` plays in the interior of `K` and does not switch off. -/
theorem cRoundA_good (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) {m : Df2Mode d}
    (hm : m ≠ .off) :
    (cRoundA n δ K (B.pos ω) ap ft nt ξ ζ m).1 ∈ interior K ∧ (cRoundA n δ K (B.pos ω) ap ft nt ξ ζ m).2 ≠ .off := by
  unfold cRoundA
  rw [kTh_good hq]
  exact PropG.round_good _ n hKconv hKc (goodPos_of_case hq) heps0 heps1 _ (fun _ => le_rfl) ap ft nt ξ ζ hm

theorem mode_ne_off : ∀ t, B.mode δ t ω ≠ .off
  | 0 => nofun
  | t + 1 => (cRoundA_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (mode_ne_off t)).2

theorem refPlay_interior (t : ℕ) : B.refPlay δ t ω ∈ interior K :=
  (cRoundA_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (mode_ne_off hKconv hKc hq heps0 heps1 t)).1

end Case

/-- The play of P° in round `t` is the play of the round with the routine `apAdv (0, 0)`, the loss `fL`, no noise
and no dither. -/
theorem refPlay_eq (t : ℕ) (ω : WΩ) : B.refPlay δ t ω =
    (cRoundA n δ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (ξc d t ω) 0 (B.mode δ t ω)).1 := by
  unfold refPlay cRoundA
  rw [roundGa_fst_ap _ _ _ _ _ _ (apAdv (0, 0)),
    roundGa_fst _ _ _ _ _ _ _ (fL K B.F.L t (B.F.lam t ω)) _ 0 _ _ 0]

/-- Proposition W-AZ: on the coupled world, `Case` without the Azuma event has probability at most `δe/7`. -/
theorem waz {ν : Measure (ℕ → ℝ)} (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hν : NoiseOK ν)
    (hpos : Measurable[cσ d 0] B.pos) (hB : BLMeas B) (hC : CoupLaw B.Coup) :
    μs ν {ω | B.Case δ ω ∧ ¬ B.Az δ ω} ≤ ENNReal.ofReal ((df2oPar d n δ).δe / 7) := by
  classical
  have hmode := mode_meas B δ hreg hKc hKconv hpos hB hC
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have := hν.1
  set μ := μs ν with hμ
  set ℱ := cσ d with hℱ
  set Z : ℕ → WΩ → ℝ := fun t ω => B.lossR t ω (B.refPlay δ t ω) with hZ
  set x : ℕ → WΩ → (PgSp d × B.F.Λ) × Df2Mode d := fun t ω => ((B.pos ω, B.F.lam t ω), B.mode δ t ω) with hxdef
  set F : ℕ → ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) → ℝ :=
    fun t p => fL K B.F.L t p.1.1.2
      (cRoundA n δ K p.1.1.1 (apAdv (0, 0)) (fL K B.F.L t p.1.1.2) 0 p.2 0 p.1.2).1 with hFdef
  have hFm : ∀ t < n, Measurable (F t) := by
    intro t ht
    have hfL := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
    have hR' := cRoundA_measL (n := n) (δ := δ) hKc hKconv hR hmw hfL
    have harg : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) =>
        (((p.1.1.1, p.1.1.2, ((0, 0) : Adv d)), p.1.2, p.2, (0 : ℝ), (0 : ℝ)) :
          (PgSp d × B.F.Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ) := by
      fun_prop
    have hpt := measurable_fst.comp (hR'.comp harg)
    have hl : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) => p.1.1.2 := by fun_prop
    have h := hfL.comp (hl.prodMk hpt)
    exact h
  have hZF : ∀ t < n, Z t = fun ω => F t (x t ω, ξc d t ω) := by
    intro t ht
    funext ω
    simp only [hZ, hFdef, hxdef, lossR, ht, ↓reduceIte]
    rw [refPlay_eq]
  have hZpast : ∀ t, ¬ t < n → Z t = fun _ => 0 := by
    intro t ht
    funext ω
    simp [hZ, lossR, ht]
  have hx : ∀ t < n, Measurable[ℱ t] (x t) := fun t ht =>
    ((hpos.mono (ℱ.mono (Nat.zero_le t)) le_rfl).prodMk (B.F.lam_meas t ht)).prodMk (hmode t)
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := by
    intro t
    by_cases ht : t < n
    · have hm : Measurable[ℱ (t + 1)] (Z t) := by
        rw [hZF t ht]
        exact (hFm t ht).comp (((hx t ht).mono (ℱ.mono (Nat.le_succ t)) le_rfl).prodMk (meas_ξc t))
      exact hm.stronglyMeasurable
    · rw [hZpast t ht]
      exact stronglyMeasurable_const
  have hZ01 : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (0 : ℝ) 1 := fun t => Filter.Eventually.of_forall fun ω => by
    by_cases ht : t < n
    · simp only [hZ, lossR, ht, ↓reduceIte]
      exact fL_mem (B.F.adm t ht _) _
    · rw [hZpast t ht]
      exact ⟨le_rfl, zero_le_one⟩
  have hAz := df2AzumaEvent μ ℱ Z hZm hZ01 n (df2oPar d n δ).δe H.de_pos
  have hFR : ∀ t < n, μ[Z t | ℱ t] =ᵐ[μ] fun ω => ∫ z, F t (x t ω, z) ∂gaussK d := by
    intro t ht
    have hξ : Measurable (ξc d t) := (meas_ξc t).mono (ℱ.le _) le_rfl
    have hint : Integrable (fun ω => F t (x t ω, ξc d t ω)) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hFm t ht).comp (((hx t ht).mono (ℱ.le t) le_rfl).prodMk hξ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h01 := fL_mem (B.F.adm t ht (B.F.lam t ω))
        (cRoundA n δ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (ξc d t ω) 0 (B.mode δ t ω)).1
      rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
      exact h01.2
    have h := lemmaFR WΩ ((PgSp d × B.F.Λ) × Df2Mode d) (Fin d → ℝ) (ℱ t) μ (x t) (ξc d t) (F t) (ℱ.le t)
      (hx t ht) hξ (ξc_indep ν t) (hFm t ht) hint
    rw [ξc_law ν t] at h
    rw [hZF t ht]
    exact h
  have hmean : ∀ ω, B.Case δ ω → ∀ t < n, ∫ z, F t (x t ω, z) ∂gaussK d = B.mean δ t ω := by
    intro ω hcase t ht
    unfold mean
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hm := mode_ne_off hKconv hKc hcase heps0 heps1 t
    have hin := (cRoundA_good hKconv hKc hcase heps0 heps1 (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 z 0
      hm).1
    simp only [hFdef, hxdef]
    rw [fL_interior hin]
    unfold cRoundA
    rw [roundGa_fst_ap _ _ _ _ _ _ apCall, roundGa_fst _ _ _ _ _ _ _ (B.lossR t ω) _ 0 _ _ 0]
    rfl
  have hZcase : ∀ ω, B.Case δ ω → ∀ t < n, Z t ω = B.loss ω t (B.refPlay δ t ω) := by
    intro ω hcase t ht
    simp only [hZ, lossR, ht, ↓reduceIte]
    exact fL_interior (refPlay_interior hKconv hKc hcase heps0 heps1 t)
  have hall : ∀ᵐ ω ∂μ, ∀ t, t < n → μ[Z t | ℱ t] ω = ∫ z, F t (x t ω, z) ∂gaussK d := by
    refine ae_all_iff.mpr fun t => ?_
    by_cases ht : t < n
    · exact (hFR t ht).mono fun ω h _ => h
    · exact Filter.Eventually.of_forall fun ω h => absurd h ht
  refine (measure_mono_ae ?_).trans hAz
  filter_upwards [hall] with ω hω hmem
  obtain ⟨hcase, hnot⟩ := hmem
  show ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe)) <
    ∑ t ∈ Finset.range n, Z t ω
  rw [Finset.sum_congr rfl fun t ht => (hω t (Finset.mem_range.mp ht)).trans
      (hmean ω hcase t (Finset.mem_range.mp ht)),
    Finset.sum_congr rfl fun t ht => hZcase ω hcase t (Finset.mem_range.mp ht)]
  unfold Az at hnot
  exact lt_of_not_ge hnot

end Run

end AdversarialBco.Bit.Cpl
