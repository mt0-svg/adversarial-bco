/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.WorldVEAd
public import AdversarialBco.Poly.Df2WorldAz

@[expose] public section

/-!
# The Azuma event on the world of a loss process

`df2AzWorldAdOf_holds : Df2AzWorldAdOf`. As `df2AzWorldOf_holds` (Df2WorldAz.lean), on the clean run `cMode` of the
losses `F.loss ω`. The clean loss of round `t` is `fL t (lam t ω)`, `fL t l` the loss `L t l` on the interior of `K`
and `0` elsewhere, so the round reads the parameter `((q, lam t ω), mode)` measurable before round `t`
(`prefixσ_le_𝒢w`), and Lemma FR gives the conditional mean of the loss of round `t` at that parameter. The clean round
is jointly measurable in `(q, l, mode, ξ, noise, ζ)` by the Carathéodory lemma (`cRound_measL`).

`df2AzWorld_of_ad`: the constant process gives back `Df2AzWorld`.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly.Conj1

open Layer2

variable {d : ℕ}

/-! ## The clean round with a loss parameter -/

attribute [local fun_prop] measurable_st_A measurable_st_mu

open Classical in
/-- The clean loss of round `t` at the parameter `l`: `L t l` on the interior of `K`, `0` elsewhere. -/
noncomputable def fL (K : Set (E d)) {Λ : Type} (L : ℕ → Λ → E d → ℝ) (t : ℕ) (l : Λ) : E d → ℝ :=
  (interior K).piecewise (L t l) 0

theorem measurable_fL {K : Set (E d)} {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ} {t : ℕ}
    (hconv : ∀ l, ConvexOn ℝ K (L t l)) (hm : ∀ y ∈ interior K, Measurable fun l => L t l y) :
    Measurable fun p : Λ × E d => fL K L t p.1 p.2 :=
  Conj1.measurable_piecewise_interior K (L t) hconv hm

theorem cRound_measL {n : ℕ} {δ : ℝ} {K : Set (E d)} (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hAp : Df2ApCallMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    {Λ : Type} [MeasurableSpace Λ] {ft : Λ → E d → ℝ} (hft : Measurable fun p : Λ × E d => ft p.1 p.2) :
    Measurable fun x : (PgSp d × Λ) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
      cRound n δ K x.1.1 (ft x.1.2) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1 := by
  classical
  refine measurable_mode_split (fun x : (PgSp d × Λ) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
    cRound n δ K x.1.1 (ft x.1.2) x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1) ?_ ?_ ?_
  · simp only [cRound, df2RoundGa]
    exact measurable_const
  · simp only [cRound, df2RoundGa]
    have hc : Measurable fun x : (PgSp d × Λ) × (Fin d → ℝ) × ℝ × ℝ => pgMu x.1.1 + pgOp x.1.1 0 := by
      have h := (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_const : Measurable fun _ : (PgSp d × Λ) × (Fin d → ℝ) × ℝ × ℝ => (0 : E d)))
      rw [Function.comp_def] at h
      exact h
    exact Measurable.ite (hc hKc.measurableSet) (hc.prodMk measurable_const) measurable_const
  · simp only [cRound_run]
    have hX : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cX n δ x.2.1 x.2.2.1 := by
      unfold cX; fun_prop
    have hgauge := gauge_kTh_meas (n := n) (δ := δ) hKc hKconv hG hR hmw
    have hq : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => x.1.1 :=
      measurable_fst.comp measurable_fst
    have hpt : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cPt n δ K x.1.1 x.2.1 x.2.2.1 :=
      measurable_const.max ((hgauge.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp hX))).div_const _)
    have hx : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPoint n δ K x.1.1 x.2.1 x.2.2.1 :=
      (pg_continuous d).2.2.measurable.comp (hq.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp (hpt.inv.smul hX)))
    have hfx : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        ft x.1.2 (cPoint n δ K x.1.1 x.2.1 x.2.2.1) := by
      have h := hft.comp ((measurable_snd.comp measurable_fst).prodMk hx)
      rw [Function.comp_def] at h
      exact h
    have hY : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPt n δ K x.1.1 x.2.1 x.2.2.1 * (ft x.1.2 (cPoint n δ K x.1.1 x.2.1 x.2.2.1) + x.2.2.2.1 + x.2.2.2.2) / 2 +
          2 * (cPt n δ K x.1.1 x.2.1 x.2.2.1 - 1) / (df2oPar d n δ).eps := by
      fun_prop
    have hnext := (hAp d n δ K hd hKc hKconv).comp (hq.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hY)))
    rw [Function.comp_def] at hnext
    exact Measurable.ite (hx hKc.measurableSet) (hx.prodMk hnext) measurable_const

/-! ## The clean run of a loss process is adapted to the filtration of the world -/

section Adapted

variable {n : ℕ} {r0 R0 δ : ℝ} {K : Set (E d)}

/-- The parameter of round `t < n` is measurable for the sigma-field of the world before round `t`. -/
theorem lam_meas_𝒢w (F : Df2LossProcOf d n r0 R0 δ K) {t : ℕ} (ht : t < n) :
    Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t]
      (F.lam t) := by
  have h := prefixσ_le_𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t
    le_rfl
  rw [zero_add] at h
  exact (F.lam_meas t ht).mono h le_rfl

theorem fT_loss (F : Df2LossProcOf d n r0 R0 δ K) (ω : WΩ) (t : ℕ) :
    fT K (F.loss ω) t = fL K F.L t (F.lam t ω) := rfl

theorem cMode_measAd (PGM : PgMeas) (PGG : PgGoodMeas) (APM : Df2ApCallMeas) (hd : 1 ≤ d) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    (F : Df2LossProcOf d n r0 R0 δ K) : ∀ t ≤ n,
      Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t]
        fun ω => cMode n r0 R0 δ K (F.loss ω) ω t := by
  intro t
  induction t with
  | zero =>
    intro _
    classical
    simp only [cMode]
    simp_rw [mode0_eq]
    refine measurable_ite_of ?_ measurable_const measurable_const
    refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    exact omega_meas_𝒢w n r0 R0 (df2oPar d n δ).δ1 0 (PGM d K r0 R0 (df2oPar d n δ).δ1 hKc).1
  | succ t ih =>
    intro ht
    set ℱ := 𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0
    have htn : t < n := by omega
    have hθ : Measurable[ℱ (t + 1)] fun ω => df2oPs d n r0 R0 δ (df2World K (F.loss ω) ω) :=
      (ps_world_meas PGM hKc F.loss 0).mono (ℱ.mono (Nat.zero_le _)) le_rfl
    have hl : Measurable[ℱ (t + 1)] (F.lam t) := (lam_meas_𝒢w F htn).mono (ℱ.mono (Nat.le_succ t)) le_rfl
    have hm : Measurable[ℱ (t + 1)] fun ω => cMode n r0 R0 δ K (F.loss ω) ω t :=
      (ih (by omega)).mono (ℱ.mono (Nat.le_succ t)) le_rfl
    have hξ : Measurable[ℱ (t + 1)] fun ω : WΩ => df2oXi (d := d) (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t := by
      have := xiL_meas (d := d) (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n 0
        le_rfl t
      convert this using 1
      funext ω
      exact xi_eq_xiL htn ω
    have hnt : Measurable[ℱ (t + 1)] fun ω : WΩ => ω.2 t :=
      (meas_noise (0 + (t + 1)) t (by omega)).mono le_sup_right le_rfl
    have hζ : Measurable[ℱ (t + 1)] fun ω : WΩ => df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t := by
      have h := meas_coord (𝒢 := ℱ (t + 1)) _ (gσ_le_𝒢w (d := d) _ _ n 0 (t + 1) _
        (lay_not_fut (d := d) (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n 0
          le_rfl t (Fin.last d)))
      have heq : (fun ω : WΩ => df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t) = fun ω : WΩ =>
          ω.1 (lay (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t
            (Fin.last d)) / 2 := by
        funext ω
        simp [df2oZeta, lay, htn]
      rw [heq]
      exact h.div_const 2
    have hR' := cRound_measL (n := n) (δ := δ) hd hKc hKconv PGG APM hR hmw
      (measurable_fL (fun l => (F.adm t htn l).1) (F.meas t htn))
    have h := measurable_snd.comp (hR'.comp ((hθ.prodMk hl).prodMk (hm.prodMk (hξ.prodMk (hnt.prodMk hζ)))))
    rw [Function.comp_def, Function.comp_def] at h
    exact h

end Adapted

/-! ## The Azuma event on the world of a loss process -/

/-- `Df2AzWorldAdOf`: the Azuma event of the run of D0 on the world of a loss process, from `Df2AzumaEvent` on the
clean run. -/
theorem df2AzWorldAdOf_holds : Df2AzWorldAdOf := by
  intro AZ PGM PGG APM d n r0 R0 δ K hB Fp ν hν
  obtain ⟨hd, hn, hr0, _, hδ0, hδ1, hKcpt, hKconv, hball0, _⟩ := hB
  have hKc := hKcpt.isClosed
  have := hν.1
  by_cases heps : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · exact (measure_mono (show _ ⊆ (∅ : Set WΩ) from fun ω hω => heps hω.1.2)).trans (by simp)
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have h0K : (0 : E d) ∈ K := hball0 (Metric.mem_closedBall_self hr0.le)
  set N0 := df2oN0 d r0 R0 (df2oPar d n δ).δ1 with hN0
  set S := df2oSpare d n r0 R0 (df2oPar d n δ).δ1 with hS
  set ℱ := 𝒢w N0 S n d 0 with hℱ
  set μ := gaussStream.prod ν with hμ
  set θ : WΩ → PgSp d := fun ω => df2oPs d n r0 R0 δ (df2World K (Fp.loss ω) ω) with hθdef
  set Z : ℕ → WΩ → ℝ := fun t ω => if t < n then fT K (Fp.loss ω) t (cPlay n r0 R0 δ K (Fp.loss ω) ω t) else 0
    with hZ
  set F : ℕ → ((PgSp d × Fp.Λ) × Df2Mode d) × (Fin d → ℝ) → ℝ :=
    fun t p => fL K Fp.L t p.1.1.2 (cRound n δ K p.1.1.1 (fL K Fp.L t p.1.1.2) 0 p.2 0 p.1.2).1 with hFdef
  have hFm : ∀ t < n, Measurable (F t) := by
    intro t ht
    have hfL := measurable_fL (fun l => (Fp.adm t ht l).1) (Fp.meas t ht)
    have hR' := cRound_measL (n := n) (δ := δ) hd hKc hKconv PGG APM hR hmw hfL
    have harg : Measurable fun p : ((PgSp d × Fp.Λ) × Df2Mode d) × (Fin d → ℝ) =>
        ((p.1.1, p.1.2, p.2, (0 : ℝ), (0 : ℝ)) : (PgSp d × Fp.Λ) × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_const.prodMk measurable_const)))
    have hpt : Measurable fun p : ((PgSp d × Fp.Λ) × Df2Mode d) × (Fin d → ℝ) =>
        (cRound n δ K p.1.1.1 (fL K Fp.L t p.1.1.2) 0 p.2 0 p.1.2).1 := by
      have h := measurable_fst.comp (hR'.comp harg)
      rw [Function.comp_def, Function.comp_def] at h
      exact h
    have hl : Measurable fun p : ((PgSp d × Fp.Λ) × Df2Mode d) × (Fin d → ℝ) => p.1.1.2 :=
      (measurable_snd.comp measurable_fst).comp measurable_fst
    have h := hfL.comp (hl.prodMk hpt)
    rw [Function.comp_def] at h
    exact h
  have hF01 : ∀ t < n, ∀ p, F t p ∈ Set.Icc (0 : ℝ) 1 := fun t ht p =>
    fT_mem (f := fun t => Fp.L t p.1.1.2) (Fp.adm t ht p.1.1.2) (roundGa_play_mem h0K _ _ _ _ _ _ _ _)
  have hZF : ∀ t < n, Z t = fun ω => F t (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t),
      xiL N0 S n d 0 t ω) := by
    intro t ht
    funext ω
    simp only [hZ, ht, ↓reduceIte, hFdef, cPlay, hθdef, fT_loss]
    rw [← xi_eq_xiL ht ω]
    unfold cRound
    rw [roundGa_fst (nt' := 0) (ζ' := 0) (ft' := fL K Fp.L t (Fp.lam t ω))]
  have hθm : ∀ t, Measurable[ℱ t] θ := fun t =>
    (ps_world_meas PGM hKc Fp.loss 0).mono (ℱ.mono (Nat.zero_le t)) le_rfl
  have hx : ∀ t < n, Measurable[ℱ t] fun ω => ((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t) :=
    fun t ht => ((hθm t).prodMk (lam_meas_𝒢w Fp ht)).prodMk
      (cMode_measAd PGM PGG APM hd hKc hKconv hR hmw Fp t ht.le)
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := by
    intro t
    by_cases ht : t < n
    · have hm : Measurable[ℱ (t + 1)] (Z t) := by
        rw [hZF t ht]
        exact (hFm t ht).comp (((hx t ht).mono (ℱ.mono (Nat.le_succ t)) le_rfl).prodMk
          (xiL_meas N0 S n 0 le_rfl t))
      exact hm.stronglyMeasurable
    · have : Z t = fun _ => 0 := by funext ω; simp [hZ, ht]
      rw [this]
      exact stronglyMeasurable_const
  have hZ01 : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (0 : ℝ) 1 := fun t => Filter.Eventually.of_forall fun ω => by
    by_cases ht : t < n
    · rw [hZF t ht]; exact hF01 t ht _
    · simp [hZ, ht]
  have hAz := AZ μ ℱ Z hZm hZ01 n (df2oPar d n δ).δe H.de_pos
  have hFR : ∀ t < n, μ[Z t | ℱ t] =ᵐ[μ] fun ω => ∫ z, F t (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t), z)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    intro t ht
    have hζ : Measurable (xiL N0 S n d 0 t) := (xiL_meas N0 S n 0 le_rfl t).mono (ℱ.le _) le_rfl
    have hint : Integrable (fun ω => F t (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t),
        xiL N0 S n d 0 t ω)) μ := by
      refine (integrable_const (1 : ℝ)).mono'
        ((hFm t ht).comp (((hx t ht).mono (ℱ.le t) le_rfl).prodMk hζ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h01 := hF01 t ht (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t), xiL N0 S n d 0 t ω)
      rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
      exact h01.2
    have h := lemmaFR WΩ ((PgSp d × Fp.Λ) × Df2Mode d) (Fin d → ℝ) (ℱ t) μ
      (fun ω => ((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t))
      (xiL N0 S n d 0 t) (F t) (ℱ.le t) (hx t ht) hζ (xiL_indep N0 S n 0 ν t) (hFm t ht) hint
    rw [xiL_law N0 S n 0 le_rfl ν t] at h
    rw [hZF t ht]
    exact h
  have hmean : ∀ ω, Df2Case d n r0 R0 δ (df2World K (Fp.loss ω) ω) → ∀ t,
      ∫ z, F t (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t), z)
        ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = df2zMean d n r0 R0 δ (df2World K (Fp.loss ω) ω) t := by
    intro ω hcase t
    have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K (Fp.loss ω) ω))) :=
      case_good hcase
    unfold df2zMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFdef, hθdef]
    rw [cMode_eq hKconv heps0 heps1 ω hgood t]
    unfold cRound
    rw [kTh_good hgood, roundGa_fst (ft' := (df2World K (Fp.loss ω) ω).f t), ← fT_loss]
    exact fT_interior (roundGa_play_interior hKconv hr0 hball0 hgood heps0 heps1 n apCall _ _ _ _ _)
  have hZcase : ∀ ω, Df2Case d n r0 R0 δ (df2World K (Fp.loss ω) ω) → ∀ t < n,
      Z t ω = Fp.loss ω t (df2zPlay d n r0 R0 δ (df2World K (Fp.loss ω) ω) t) := by
    intro ω hcase t ht
    have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K (Fp.loss ω) ω))) :=
      case_good hcase
    simp only [hZ, ht, ↓reduceIte]
    rw [cPlay_eq hKconv heps0 heps1 ω hgood t]
    exact fT_interior (roundGa_play_interior hKconv hr0 hball0 hgood heps0 heps1 n apCall _ _ _ _ _)
  have hall : ∀ᵐ ω ∂μ, ∀ t, t < n → μ[Z t | ℱ t] ω =
      ∫ z, F t (((θ ω, Fp.lam t ω), cMode n r0 R0 δ K (Fp.loss ω) ω t), z)
        ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    refine ae_all_iff.mpr fun t => ?_
    by_cases ht : t < n
    · exact (hFR t ht).mono fun ω h _ => h
    · exact Filter.Eventually.of_forall fun ω h => absurd h ht
  refine (measure_mono_ae ?_).trans hAz
  filter_upwards [hall] with ω hω hmem
  obtain ⟨hcase, hnot⟩ := hmem
  show ∑ t ∈ Finset.range n, μ[Z t | ℱ t] ω + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe)) <
    ∑ t ∈ Finset.range n, Z t ω
  rw [Finset.sum_congr rfl fun t ht => (hω t (Finset.mem_range.mp ht)).trans (hmean ω hcase t),
    Finset.sum_congr rfl fun t ht => hZcase ω hcase t (Finset.mem_range.mp ht)]
  unfold Df2AzPath at hnot
  exact lt_of_not_ge hnot

/-! ## The constant process -/

/-- The constant process gives back `Df2AzWorld`: the adapted statement is no weaker. -/
theorem df2AzWorld_of_ad (h : Df2AzWorldAd) : Df2AzWorld := by
  intro d n r0 R0 δ K f hW ν hν
  obtain ⟨hd, hn, hr0, hr, hδ0, hδ1, hKc, hKconv, hball, hsub, hf⟩ := hW
  exact h d n r0 R0 δ K ⟨hd, hn, hr0, hr, hδ0, hδ1, hKc, hKconv, hball, hsub⟩ (constProc hf) ν hν

end AdversarialBco.Poly.Conj1
