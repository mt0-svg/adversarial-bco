/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvSetE

@[expose] public section

/-!
# W-AZ for P° of Theorem UW at the level `δc`

The port of Proposition W-AZ (`RunW.waz`, Unified/WorldShadow.lean) to the weighted round: on `Case`, P°'s plays and
their means given the past satisfy the Azuma event `AzU` at the level `δc` outside a set of probability at most
`δc/7` (`wazU`).

The weight and the clip change only the observation, never the point played (`roundGaW_fst_ga`), so P°'s plays are those
of the unweighted round from the same mode, and they lie in the interior of `K` on `Case` (`roundGaW_good`, from
`PropG.round_good` and `PropG.df2NextAP_ne_off`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.UW

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

variable {d : ℕ}

/-! ## The weighted round plays as the unweighted one -/

/-- The point of the weighted round is the point of the unweighted round. -/
theorem roundGaW_fst_ga (p : Df2OPar) (b0 y0 : ℝ) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ)
    (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    (df2RoundGaW p b0 y0 n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 := by
  classical
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundGaW, df2RoundGa]
    split_ifs <;> rfl

/-- On a good position, a weighted round from a mode other than `off` plays in the interior of `K` and does not
switch off. -/
theorem roundGaW_good (p : Df2OPar) (b0 y0 : ℝ) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K)
    {Ps : PgSp d} (hP : PropG.GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    {m : Df2Mode d} (hm : m ≠ .off) :
    (df2RoundGaW p b0 y0 n K Ps ga ap ft nt ξ ζ m).1 ∈ interior K ∧
      (df2RoundGaW p b0 y0 n K Ps ga ap ft nt ξ ζ m).2 ≠ .off := by
  classical
  have hg := PropG.round_good p n hK hKc hP hε hε1 ga hga ap ft nt ξ ζ hm
  cases m with
  | off => exact absurd rfl hm
  | guard => exact hg
  | run st =>
    simp only [df2RoundGa, df2RoundGaW] at hg ⊢
    split_ifs at hg ⊢ with hx
    · exact ⟨hg.1, PropG.df2NextAP_ne_off _ _ _ _ _ _ _ _⟩
    · exact absurd rfl hg.2

namespace RunU

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} {B : RunW d n K W}
  {ρ : RefW}

section Case

variable (hKconv : Convex ℝ K) (hKc : IsClosed K) {ω : Ω} (hq : B.Case ρ.δc ω) (heps0 : 0 < (parW d n ρ.u).eps)
  (heps1 : (parW d n ρ.u).eps < 1)
include hKconv hKc hq heps0 heps1

/-- On `Case`, a weighted round of P° from a mode other than `off` plays in the interior of `K` and does not switch
off. -/
theorem cRoundW_good (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) {m : Df2Mode d}
    (hm : m ≠ .off) :
    (cRoundW n ρ K (B.pos ω) ap ft nt ξ ζ m).1 ∈ interior K ∧ (cRoundW n ρ K (B.pos ω) ap ft nt ξ ζ m).2 ≠ .off := by
  unfold cRoundW
  rw [kTh_good hq]
  exact roundGaW_good (parW d n ρ.u) _ _ n hKconv hKc (Unified.World.RunW.goodPos_of_case hq) heps0 heps1 _
    (fun _ => le_rfl) ap ft nt ξ ζ hm

theorem modeU_ne_off : ∀ t, modeU B ρ t ω ≠ .off
  | 0 => nofun
  | t + 1 => (cRoundW_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (modeU_ne_off t)).2

theorem refPlayU_interior (t : ℕ) : refPlayU B ρ t ω ∈ interior K :=
  (cRoundW_good hKconv hKc hq heps0 heps1 _ _ _ _ _ (modeU_ne_off hKconv hKc hq heps0 heps1 t)).1

end Case

/-- The play of P° in round `t` is the play of the weighted round with the routine `apAdv (0, 0)`, the loss `fL`, no
noise and no dither. -/
theorem refPlayU_eq (t : ℕ) (ω : Ω) : refPlayU B ρ t ω =
    (cRoundW n ρ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (W.xi t ω) 0 (modeU B ρ t ω)).1 := by
  unfold refPlayU cRoundW
  rw [roundGaW_fst_ga, roundGaW_fst_ga, roundGa_fst_ap _ _ _ _ _ _ (apAdv (0, 0)),
    roundGa_fst _ _ _ _ _ _ _ (fL K B.F.L t (B.F.lam t ω)) _ 0 _ _ 0]

/-- **W-AZ** for P° of Theorem UW: `Case` without the Azuma event at the level `δc` has probability at most
`δc/7`. -/
theorem wazU (hW : WorldLawOK W) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hB : BLMeasW B) (hC : CoupLaw B.Coup) :
    W.μ {ω | B.Case ρ.δc ω ∧ ¬ AzU B ρ ω} ≤ ENNReal.ofReal (ρ.δc / 7) := by
  classical
  have hmode := modeU_meas B ρ hW hreg.hd hKc hKconv hpos hB hC
  have hR := one_le_R_of n ρ.δc hreg.hd
  have hmw := inv_R_le_of n ρ.δc hreg.hd
  have heps0 := EvP.eps_pos hreg
  have heps1 := EvP.eps_lt_one hreg
  have := hW.prob
  set μ := W.μ with hμ
  set ℱ := W.𝓕 with hℱ
  set Z : ℕ → Ω → ℝ := fun t ω => B.lossR t ω (refPlayU B ρ t ω) with hZ
  set x : ℕ → Ω → (PgSp d × B.F.Λ) × Df2Mode d := fun t ω => ((B.pos ω, B.F.lam t ω), modeU B ρ t ω) with hxdef
  set F : ℕ → ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) → ℝ :=
    fun t p => fL K B.F.L t p.1.1.2
      (cRoundW n ρ K p.1.1.1 (apAdv (0, 0)) (fL K B.F.L t p.1.1.2) 0 p.2 0 p.1.2).1 with hFdef
  have hFm : ∀ t < n, Measurable (F t) := by
    intro t ht
    have hfL := measurable_fL (K := K) (L := B.F.L) (t := t) (fun l => (B.F.adm t ht l).1) (B.F.meas t ht)
    have hR' := cRoundW_measL (n := n) (ρ := ρ) hKc hKconv hR hmw hfL
    have harg : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) =>
        (((p.1.1.1, p.1.1.2, ((0, 0) : Adv d)), p.1.2, p.2, (0 : ℝ), (0 : ℝ)) :
          (PgSp d × B.F.Λ × Adv d) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ) := by
      fun_prop
    have hpt := measurable_fst.comp (hR'.comp harg)
    have hl : Measurable fun p : ((PgSp d × B.F.Λ) × Df2Mode d) × (Fin d → ℝ) => p.1.1.2 := by fun_prop
    have h := hfL.comp (hl.prodMk hpt)
    exact h
  have hZF : ∀ t < n, Z t = fun ω => F t (x t ω, W.xi t ω) := by
    intro t ht
    funext ω
    simp only [hZ, hFdef, hxdef, RunW.lossR, ht, ↓reduceIte]
    rw [refPlayU_eq]
  have hZpast : ∀ t, ¬ t < n → Z t = fun _ => 0 := by
    intro t ht
    funext ω
    simp [hZ, RunW.lossR, ht]
  have hx : ∀ t < n, Measurable[ℱ t] (x t) := fun t ht =>
    ((hpos.mono (ℱ.mono (Nat.zero_le t)) le_rfl).prodMk (B.F.lam_meas t ht)).prodMk (hmode t)
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := by
    intro t
    by_cases ht : t < n
    · have hm : Measurable[ℱ (t + 1)] (Z t) := by
        rw [hZF t ht]
        exact (hFm t ht).comp (((hx t ht).mono (ℱ.mono (Nat.le_succ t)) le_rfl).prodMk (hW.meas_xi t))
      exact hm.stronglyMeasurable
    · rw [hZpast t ht]
      exact stronglyMeasurable_const
  have hZ01 : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (0 : ℝ) 1 := fun t => Filter.Eventually.of_forall fun ω => by
    by_cases ht : t < n
    · simp only [hZ, RunW.lossR, ht, ↓reduceIte]
      exact fL_mem (B.F.adm t ht _) _
    · rw [hZpast t ht]
      exact ⟨le_rfl, zero_le_one⟩
  have hAz := df2AzumaEvent μ ℱ Z hZm hZ01 n ρ.δc hreg.dc_pos
  have hFR : ∀ t < n, μ[Z t | ℱ t] =ᵐ[μ] fun ω => ∫ z, F t (x t ω, z) ∂gaussK d := by
    intro t ht
    have hξ : Measurable (W.xi t) := (hW.meas_xi t).mono (ℱ.le _) le_rfl
    have hint : Integrable (fun ω => F t (x t ω, W.xi t ω)) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hFm t ht).comp (((hx t ht).mono (ℱ.le t) le_rfl).prodMk hξ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h01 := fL_mem (B.F.adm t ht (B.F.lam t ω))
        (cRoundW n ρ K (B.pos ω) (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 (W.xi t ω) 0 (modeU B ρ t ω)).1
      rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
      exact h01.2
    have h := lemmaFR Ω ((PgSp d × B.F.Λ) × Df2Mode d) (Fin d → ℝ) (ℱ t) μ (x t) (W.xi t) (F t) (ℱ.le t)
      (hx t ht) hξ (hW.xi_indep t) (hFm t ht) hint
    rw [hW.xi_law t] at h
    rw [hZF t ht]
    exact h
  have hmean : ∀ ω, B.Case ρ.δc ω → ∀ t < n, ∫ z, F t (x t ω, z) ∂gaussK d = meanU B ρ t ω := by
    intro ω hcase t ht
    unfold meanU
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hm := modeU_ne_off hKconv hKc hcase heps0 heps1 t
    have hin := (cRoundW_good hKconv hKc hcase heps0 heps1 (apAdv (0, 0)) (fL K B.F.L t (B.F.lam t ω)) 0 z 0
      hm).1
    simp only [hFdef, hxdef]
    rw [fL_interior hin]
    unfold cRoundW
    rw [roundGaW_fst_ga, roundGaW_fst_ga, roundGa_fst_ap _ _ _ _ _ _ apCall,
      roundGa_fst _ _ _ _ _ _ _ (B.lossR t ω) _ 0 _ _ 0]
    rfl
  have hZcase : ∀ ω, B.Case ρ.δc ω → ∀ t < n, Z t ω = B.loss ω t (refPlayU B ρ t ω) := by
    intro ω hcase t ht
    simp only [hZ, RunW.lossR, ht, ↓reduceIte]
    exact fL_interior (refPlayU_interior hKconv hKc hcase heps0 heps1 t)
  have hall : ∀ᵐ ω ∂μ, ∀ t, t < n → μ[Z t | ℱ t] ω = ∫ z, F t (x t ω, z) ∂gaussK d := by
    refine ae_all_iff.mpr fun t => ?_
    by_cases ht : t < n
    · exact (hFR t ht).mono fun ω h _ => h
    · exact Filter.Eventually.of_forall fun ω h => absurd h ht
  refine (measure_mono_ae ?_).trans hAz
  filter_upwards [hall] with ω hω hmem
  obtain ⟨hcase, hnot⟩ := hmem
  show ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * n * Real.log (7 / ρ.δc)) <
    ∑ t ∈ Finset.range n, Z t ω
  rw [Finset.sum_congr rfl fun t ht => (hω t (Finset.mem_range.mp ht)).trans
      (hmean ω hcase t (Finset.mem_range.mp ht)),
    Finset.sum_congr rfl fun t ht => hZcase ω hcase t (Finset.mem_range.mp ht)]
  unfold AzU at hnot
  exact lt_of_not_ge hnot

end RunU

end AdversarialBco.UW
