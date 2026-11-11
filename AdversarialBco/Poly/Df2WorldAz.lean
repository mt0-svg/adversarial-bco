/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldVE

@[expose] public section

/-!
# The Azuma event on the world

`df2AzWorldOf_holds : Df2AzWorldOf`. The run of D0 reads the losses at its plays only, and on the case of the
analysis every play lies in the interior of `K` (`roundGa_play_interior`), where a convex loss agrees with the
measurable `fT K f t = (interior K).piecewise (f t) 0`. The clean run (`cMode`, `cPlay`) is D0 with the losses `fT`
and the gauge of the body `kTh` of Df2WorldVE.lean; it is measurable for the filtration `𝒢w … 0` of the world
(`cMode_meas`), and on the case of the analysis it is the run of D0 (`cMode_eq`, `cPlay_eq`). `df2zRun_piecewise`
states the same for D0 itself on the world with the losses `fT`: same modes, same plays, same Azuma event. The
regret is never built from `fT`.

The process `Z t = fT K f t (cPlay t)` has values in `[0, 1]` and is measurable before round `t + 1`; by Lemma FR
its conditional mean given the past is the integral over the draw of round `t`, which on the case of the analysis is
`df2zMean`. `Df2AzumaEvent` then bounds the event.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Functions of a mode -/

theorem measurable_stCode : Measurable (Df2St.code (d := d)) := Measurable.of_comap_le le_rfl

theorem measurable_modeCode : Measurable (Df2Mode.code (d := d)) := Measurable.of_comap_le le_rfl

theorem measurable_st_A : Measurable fun st : Df2St d => st.A :=
  (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_stCode)))))

theorem measurable_st_mu : Measurable fun st : Df2St d => st.mu :=
  measurable_fst.comp (measurable_snd.comp measurable_stCode)

/-- A function of a mode is measurable when its three branches are. -/
theorem measurable_mode_split {Θ Z β : Type*} [MeasurableSpace Θ] [MeasurableSpace Z] [MeasurableSpace β]
    (F : Θ × Df2Mode d × Z → β) (h0 : Measurable fun x : Θ × Z => F (x.1, .off, x.2))
    (h1 : Measurable fun x : Θ × Z => F (x.1, .guard, x.2))
    (h2 : Measurable fun x : Θ × Df2St d × Z => F (x.1, .run x.2.1, x.2.2)) : Measurable F := by
  classical
  let G : Θ × (Fin 3 × Df2St d) × Z → β := fun x =>
    if x.2.1.1 = 0 then F (x.1, .off, x.2.2) else if x.2.1.1 = 1 then F (x.1, .guard, x.2.2)
    else F (x.1, .run x.2.1.2, x.2.2)
  have hG : Measurable G := by
    refine Measurable.ite ?_ (h0.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (Measurable.ite ?_ (h1.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
        (h2.comp (measurable_fst.prodMk ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)))))
    · exact measurable_fst.comp (measurable_fst.comp measurable_snd) (measurableSet_singleton 0)
    · exact measurable_fst.comp (measurable_fst.comp measurable_snd) (measurableSet_singleton 1)
  have hF : F = G ∘ fun x => (x.1, x.2.1.code, x.2.2) := by
    funext x
    obtain ⟨θ, m, z⟩ := x
    cases m <;> simp [G, Df2Mode.code]
  rw [hF]
  exact hG.comp (measurable_fst.prodMk ((measurable_modeCode.comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd)))

/-! ## The round of D0 reads the loss at its play only -/

theorem roundGa_fst (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (nt nt' : ℝ) (ξ : Fin d → ℝ) (ζ ζ' : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap ft' nt' ξ ζ' m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    simp only [df2RoundGa]
    split_ifs <;> rfl

theorem zero_mem_interior {K : Set (E d)} {r0 : ℝ} (hr0 : 0 < r0) (hball : Metric.closedBall 0 r0 ⊆ K) :
    (0 : E d) ∈ interior K :=
  interior_mono hball (by rw [interior_closedBall _ hr0.ne']; exact Metric.mem_ball_self hr0)

theorem guard_interior {K : Set (E d)} {R : ℝ} {q : PgSp d} (hq : PgGood d K R (some q)) :
    pgMu q + pgOp q 0 ∈ interior K := by
  obtain ⟨hdet, hb1, _, _⟩ := good_unpack hq
  refine affine_interior_mem K _ (pgMu q) (pgOp q) (pgOp_surjective hdet) (fun y hy => hy) 0 ?_
  exact interior_mono hb1 (by rw [interior_closedBall _ one_ne_zero]; exact Metric.mem_ball_self one_pos)

/-- On a position of `PgGood`, every play of a round of D0 lies in the interior of `K`. -/
theorem roundGa_play_interior {K : Set (E d)} (hKconv : Convex ℝ K) {r0 : ℝ} (hr0 : 0 < r0)
    (hball : Metric.closedBall 0 r0 ⊆ K) {p : Df2OPar} {q : PgSp d} (hq : PgGood d K p.R (some q))
    (heps0 : 0 < p.eps) (heps1 : p.eps < 1) (n : ℕ) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K q (gauge (df2Kp K q p.R)) ap ft nt ξ ζ m).1 ∈ interior K := by
  have h0 := zero_mem_interior hr0 hball
  cases m with
  | off => exact h0
  | guard =>
    simp only [df2RoundGa]
    split_ifs
    · exact guard_interior hq
    · exact h0
  | run st =>
    simp only [df2RoundGa]
    split_ifs
    · have := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ ξ)))
      simpa only [df2Pip, WithLp.toLp_smul] using this
    · exact h0

/-- The round of D0 depends on the loss through its values on the interior of `K` only. -/
theorem roundGa_loss_congr {K : Set (E d)} (hKconv : Convex ℝ K) {p : Df2OPar} {q : PgSp d}
    (hq : PgGood d K p.R (some q)) (heps0 : 0 < p.eps) (heps1 : p.eps < 1) (n : ℕ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (h : ∀ y ∈ interior K, ft y = ft' y) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K q (gauge (df2Kp K q p.R)) ap ft nt ξ ζ m =
      df2RoundGa p n K q (gauge (df2Kp K q p.R)) ap ft' nt ξ ζ m := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    have hin := play_interior hKconv hq heps0 heps1 (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ ξ)))
    simp only [df2Pip, ← WithLp.toLp_smul] at hin
    simp only [df2RoundGa, h _ hin]

/-! ## The clean losses and the clean run -/

open Classical in
/-- The clean loss of round `t`: `f_t` on the interior of `K`, `0` elsewhere. -/
noncomputable def fT (K : Set (E d)) (f : ℕ → E d → ℝ) (t : ℕ) : E d → ℝ := (interior K).piecewise (f t) 0

theorem fT_interior {K : Set (E d)} {f : ℕ → E d → ℝ} {t : ℕ} {y : E d} (hy : y ∈ interior K) :
    fT K f t y = f t y := by
  classical
  simp [fT, Set.piecewise_eq_of_mem _ _ _ hy]

theorem measurable_fT {K : Set (E d)} {f : ℕ → E d → ℝ} {t : ℕ} (hf : ConvexOn ℝ K (f t)) :
    Measurable (fT K f t) :=
  measurable_piecewise_interior hf

theorem fT_mem {K : Set (E d)} {f : ℕ → E d → ℝ} {t : ℕ} (hf : AdmLoss K (f t)) {y : E d} (hy : y ∈ K) :
    fT K f t y ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hi : y ∈ interior K
  · rw [fT_interior hi]; exact hf.2 y hy
  · simp [fT, Set.piecewise_eq_of_notMem _ _ _ hi]

/-- The clean round: the round of D0 with the gauge of the body `kTh` of the instance. -/
noncomputable def cRound (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa (df2oPar d n δ) n K q (gauge (kTh n δ K q)) apCall ft nt ξ ζ m

/-- The mode of the clean run before round `t`. -/
noncomputable def cMode (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ) (ω : WΩ) : ℕ → Df2Mode d
  | 0 => df2oMode0 d n r0 R0 δ (df2World K f ω)
  | t + 1 => (cRound n δ K (df2oPs d n r0 R0 δ (df2World K f ω)) (fT K f t) (ω.2 t)
      (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t)
      (cMode n r0 R0 δ K f ω t)).2

/-- The play of the clean run in round `t`. -/
noncomputable def cPlay (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ) (ω : WΩ) (t : ℕ) : E d :=
  (cRound n δ K (df2oPs d n r0 R0 δ (df2World K f ω)) (fT K f t) (ω.2 t)
    (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t)
    (cMode n r0 R0 δ K f ω t)).1

/-! ## Measurability of the clean round -/

attribute [local fun_prop] measurable_st_A measurable_st_mu

/-- `X = μ + (1 - λ) A ξ`. -/
noncomputable def cX (n : ℕ) (δ : ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ :=
  st.mu + (1 - (df2oPar d n δ).lam) • (st.A *ᵥ ξ)

/-- `pip(X)` for the gauge of `kTh q`. -/
noncomputable def cPt (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (gauge (kTh n δ K q) (WithLp.toLp 2 (cX n δ st ξ)) / (1 - (df2oPar d n δ).eps))

/-- The point played from the state `st`, `S⁻¹(X/pip(X))`. -/
noncomputable def cPoint (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu q + pgOp q (WithLp.toLp 2 ((cPt n δ K q st ξ)⁻¹ • cX n δ st ξ))

open Classical in
theorem cRound_run (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    (st : Df2St d) : cRound n δ K q ft nt ξ ζ (.run st) =
      if cPoint n δ K q st ξ ∈ K then (cPoint n δ K q st ξ, df2NextAP apCall (df2oPar d n δ) n
        (df2KepsOf (df2Kp K q (df2oPar d n δ).R) (df2oPar d n δ).eps) st ξ (st.A *ᵥ ξ)
        (cPt n δ K q st ξ * (ft (cPoint n δ K q st ξ) + nt + ζ) / 2 + 2 * (cPt n δ K q st ξ - 1) / (df2oPar d n δ).eps))
      else (0, .off) := rfl

theorem cRound_meas {n : ℕ} {δ : ℝ} {K : Set (E d)} (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hAp : Df2ApCallMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    {ft : E d → ℝ} (hft : Measurable ft) :
    Measurable fun x : PgSp d × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
      cRound n δ K x.1 ft x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1 := by
  classical
  refine measurable_mode_split (fun x : PgSp d × Df2Mode d × (Fin d → ℝ) × ℝ × ℝ =>
    cRound n δ K x.1 ft x.2.2.2.1 x.2.2.1 x.2.2.2.2 x.2.1) ?_ ?_ ?_
  · simp only [cRound, df2RoundGa]
    exact measurable_const
  · simp only [cRound, df2RoundGa]
    have hc : Continuous fun x : PgSp d × (Fin d → ℝ) × ℝ × ℝ => pgMu x.1 + pgOp x.1 0 :=
      (pg_continuous d).2.2.comp (continuous_fst.prodMk continuous_const)
    exact Measurable.ite (hc.measurable hKc.measurableSet) (hc.measurable.prodMk measurable_const) measurable_const
  · simp only [cRound_run]
    have hX : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cX n δ x.2.1 x.2.2.1 := by
      unfold cX; fun_prop
    have hgauge := gauge_kTh_meas (n := n) (δ := δ) hKc hKconv hG hR hmw
    have hpt : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cPt n δ K x.1 x.2.1 x.2.2.1 :=
      measurable_const.max ((hgauge.comp (measurable_fst.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp hX))).div_const _)
    have hx : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ × ℝ => cPoint n δ K x.1 x.2.1 x.2.2.1 :=
      (pg_continuous d).2.2.measurable.comp (measurable_fst.prodMk
        ((PiLp.continuous_toLp 2 _).measurable.comp (hpt.inv.smul hX)))
    have hfx : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ × ℝ => ft (cPoint n δ K x.1 x.2.1 x.2.2.1) :=
      hft.comp hx
    have hY : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ × ℝ =>
        cPt n δ K x.1 x.2.1 x.2.2.1 * (ft (cPoint n δ K x.1 x.2.1 x.2.2.1) + x.2.2.2.1 + x.2.2.2.2) / 2 +
          2 * (cPt n δ K x.1 x.2.1 x.2.2.1 - 1) / (df2oPar d n δ).eps := by
      fun_prop
    have hnext := (hAp d n δ K hd hKc hKconv).comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk hY)))
    exact Measurable.ite (hx hKc.measurableSet) (hx.prodMk hnext) measurable_const

theorem roundGa_play_mem {p : Df2OPar} {n : ℕ} {K : Set (E d)} (h0 : (0 : E d) ∈ K) (q : PgSp d) (ga : E d → ℝ)
    (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K q ga ap ft nt ξ ζ m).1 ∈ K := by
  cases m with
  | off => exact h0
  | guard =>
    simp only [df2RoundGa]
    split_ifs with h
    · exact h
    · exact h0
  | run st =>
    simp only [df2RoundGa]
    split_ifs with h
    · exact h
    · exact h0

/-! ## The clean run is the run of D0 on the case of the analysis -/

section Case

variable {n : ℕ} {r0 R0 δ : ℝ} {K : Set (E d)} {f : ℕ → E d → ℝ}

theorem cRound_eq_zRound (hKconv : Convex ℝ K) (heps0 : 0 < (df2oPar d n δ).eps)
    (heps1 : (df2oPar d n δ).eps < 1) (ω : WΩ)
    (hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω)))) (t : ℕ) (m : Df2Mode d) :
    cRound n δ K (df2oPs d n r0 R0 δ (df2World K f ω)) (fT K f t) (ω.2 t)
        (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t) m =
      df2zRoundAt d n r0 R0 δ (df2World K f ω) t m := by
  unfold cRound df2zRoundAt
  rw [kTh_good hgood]
  exact roundGa_loss_congr hKconv hgood heps0 heps1 n apCall _ _ (fun y hy => fT_interior hy) _ _ _ m

theorem cMode_eq (hKconv : Convex ℝ K) (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1)
    (ω : WΩ) (hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω)))) :
    ∀ t, cMode n r0 R0 δ K f ω t = df2zMode d n r0 R0 δ (df2World K f ω) t
  | 0 => rfl
  | t + 1 => by
    have ih := cMode_eq hKconv heps0 heps1 ω hgood t
    show _ = (df2zRoundAt d n r0 R0 δ (df2World K f ω) (0 + t) (df2zMode d n r0 R0 δ (df2World K f ω) t)).2
    rw [cMode, ih, zero_add, cRound_eq_zRound hKconv heps0 heps1 ω hgood]

theorem cPlay_eq (hKconv : Convex ℝ K) (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1)
    (ω : WΩ) (hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω)))) (t : ℕ) :
    cPlay n r0 R0 δ K f ω t = df2zPlay d n r0 R0 δ (df2World K f ω) t := by
  unfold cPlay df2zPlay
  rw [cMode_eq hKconv heps0 heps1 ω hgood, cRound_eq_zRound hKconv heps0 heps1 ω hgood]

/-- On the case of the analysis, D0 on the world with the losses `fT K f` runs as on the world with `f`: same modes,
same plays, same Azuma event. -/
theorem df2zRun_piecewise (hKconv : Convex ℝ K) (hr0 : 0 < r0) (hball : Metric.closedBall 0 r0 ⊆ K)
    (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1) (ω : WΩ)
    (hcase : Df2Case d n r0 R0 δ (df2World K f ω)) :
    (∀ t, df2zMode d n r0 R0 δ (df2World K (fT K f) ω) t = df2zMode d n r0 R0 δ (df2World K f ω) t) ∧
      (∀ t, df2zPlay d n r0 R0 δ (df2World K (fT K f) ω) t = df2zPlay d n r0 R0 δ (df2World K f ω) t) ∧
      (Df2AzPath d n r0 R0 δ (df2World K (fT K f) ω) ↔ Df2AzPath d n r0 R0 δ (df2World K f ω)) := by
  have hgood := case_good hcase
  have hround : ∀ t m, df2zRoundAt d n r0 R0 δ (df2World K (fT K f) ω) t m =
      df2zRoundAt d n r0 R0 δ (df2World K f ω) t m := fun t m =>
    roundGa_loss_congr hKconv hgood heps0 heps1 n apCall _ _ (fun y hy => fT_interior hy) _ _ _ m
  have hmode : ∀ t, df2zMode d n r0 R0 δ (df2World K (fT K f) ω) t = df2zMode d n r0 R0 δ (df2World K f ω) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      show (df2zRoundAt d n r0 R0 δ _ (0 + t) (df2zMode d n r0 R0 δ _ t)).2 =
        (df2zRoundAt d n r0 R0 δ _ (0 + t) (df2zMode d n r0 R0 δ _ t)).2
      rw [ih, hround]
  have hplay : ∀ t, df2zPlay d n r0 R0 δ (df2World K (fT K f) ω) t = df2zPlay d n r0 R0 δ (df2World K f ω) t := by
    intro t
    unfold df2zPlay
    rw [hmode, hround]
  have hin : ∀ t, df2zPlay d n r0 R0 δ (df2World K f ω) t ∈ interior K := fun t =>
    roundGa_play_interior hKconv hr0 hball hgood heps0 heps1 n apCall _ _ _ _ _
  have hmean : ∀ t, df2zMean d n r0 R0 δ (df2World K (fT K f) ω) t = df2zMean d n r0 R0 δ (df2World K f ω) t := by
    intro t
    unfold df2zMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hmode t, roundGa_fst (ft' := (df2World K f ω).f t)]
    exact fT_interior (roundGa_play_interior hKconv hr0 hball hgood heps0 heps1 n apCall _ _ _ _ _)
  refine ⟨hmode, hplay, ?_⟩
  unfold Df2AzPath
  have h1 : ∑ t ∈ Finset.range n, (df2World K (fT K f) ω).f t (df2zPlay d n r0 R0 δ (df2World K (fT K f) ω) t) =
      ∑ t ∈ Finset.range n, (df2World K f ω).f t (df2zPlay d n r0 R0 δ (df2World K f ω) t) :=
    Finset.sum_congr rfl fun t _ => by rw [hplay]; exact fT_interior (hin t)
  rw [h1, Finset.sum_congr rfl fun t _ => hmean t]

end Case

/-! ## The clean run is adapted to the filtration of the world -/

theorem measurable_ite_of {Ω β : Type*} [MeasurableSpace β] {m : MeasurableSpace Ω} {p : Ω → Prop}
    [DecidablePred p] (hp : MeasurableSet[m] {a | p a}) {f g : Ω → β} (hf : Measurable[m] f) (hg : Measurable[m] g) :
    Measurable[m] fun x => if p x then f x else g x :=
  Measurable.ite hp hf hg

section Adapted

variable {n : ℕ} {r0 R0 δ : ℝ} {K : Set (E d)} {f : ℕ → E d → ℝ}

theorem mode0_eq (w : World d) : df2oMode0 d n r0 R0 δ w =
    if (df2oPos d n r0 R0 δ w).isSome = true ∧ (df2oPar d n δ).eps ≤ 1 / 2 then .run (df2Init (df2oPar d n δ) d)
    else .off := by
  classical
  unfold df2oMode0
  cases df2oPos d n r0 R0 δ w with
  | none => simp
  | some _ =>
    simp only [Option.isSome_some, true_and]
    split_ifs <;> first | rfl | (exfalso; linarith)

theorem xi_eq_xiL {t : ℕ} (ht : t < n) (ω : WΩ) :
    df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) ω.1 t =
      xiL (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t ω := by
  funext c
  simp [xiL, lay, ht, df2oXi]

theorem cMode_meas (PGM : PgMeas) (PGG : PgGoodMeas) (APM : Df2ApCallMeas) (hd : 1 ≤ d) (hKc : IsClosed K)
    (hKconv : Convex ℝ K) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    (hf : f ∈ Advs K n) : ∀ t ≤ n,
      Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d 0 t]
        fun ω => cMode n r0 R0 δ K f ω t := by
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
    have hθ : Measurable[ℱ (t + 1)] fun ω => df2oPs d n r0 R0 δ (df2World K f ω) :=
      (theta_meas PGM hKc f 0).mono (ℱ.mono (Nat.zero_le _)) le_rfl
    have hm : Measurable[ℱ (t + 1)] fun ω => cMode n r0 R0 δ K f ω t :=
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
    have hR' := cRound_meas (n := n) (δ := δ) hd hKc hKconv PGG APM hR hmw (measurable_fT (hf t htn).1)
    exact measurable_snd.comp (hR'.comp (hθ.prodMk (hm.prodMk (hξ.prodMk (hnt.prodMk hζ)))))

end Adapted

/-! ## The Azuma event on the world -/

/-- `Df2AzWorldOf`: the Azuma event of the run of D0 on the world, from `Df2AzumaEvent` on the clean run. -/
theorem df2AzWorldOf_holds : Df2AzWorldOf := by
  intro AZ PGM PGG APM d n r0 R0 δ K f hW ν hν
  obtain ⟨hd, hn, hr0, _, hδ0, hδ1, hKcpt, hKconv, hball0, _, hf⟩ := hW
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
  set θ : WΩ → PgSp d := fun ω => df2oPs d n r0 R0 δ (df2World K f ω) with hθdef
  set Z : ℕ → WΩ → ℝ := fun t ω => if t < n then fT K f t (cPlay n r0 R0 δ K f ω t) else 0 with hZ
  set F : ℕ → (PgSp d × Df2Mode d) × (Fin d → ℝ) → ℝ :=
    fun t p => fT K f t (cRound n δ K p.1.1 (fT K f t) 0 p.2 0 p.1.2).1 with hFdef
  have hFm : ∀ t < n, Measurable (F t) := fun t ht =>
    (measurable_fT (hf t ht).1).comp (measurable_fst.comp
      ((cRound_meas hd hKc hKconv PGG APM hR hmw (measurable_fT (hf t ht).1)).comp
        ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk
          (measurable_snd.prodMk (measurable_const.prodMk measurable_const))))))
  have hF01 : ∀ t < n, ∀ p, F t p ∈ Set.Icc (0 : ℝ) 1 := fun t ht p =>
    fT_mem (hf t ht) (roundGa_play_mem h0K _ _ _ _ _ _ _ _)
  have hZF : ∀ t < n, Z t = fun ω => F t ((θ ω, cMode n r0 R0 δ K f ω t), xiL N0 S n d 0 t ω) := by
    intro t ht
    funext ω
    simp only [hZ, ht, ↓reduceIte, hFdef, cPlay, hθdef]
    rw [← xi_eq_xiL ht ω]
    unfold cRound
    rw [roundGa_fst (nt' := 0) (ζ' := 0) (ft' := fT K f t)]
  have hθm : ∀ t, Measurable[ℱ t] θ := fun t => (theta_meas PGM hKc f 0).mono (ℱ.mono (Nat.zero_le t)) le_rfl
  have hZm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (Z t) := by
    intro t
    by_cases ht : t < n
    · have hm : Measurable[ℱ (t + 1)] (Z t) := by
        rw [hZF t ht]
        exact (hFm t ht).comp (((hθm (t + 1)).prodMk ((cMode_meas PGM PGG APM hd hKc hKconv hR hmw hf t ht.le).mono
          (ℱ.mono (Nat.le_succ t)) le_rfl)).prodMk (xiL_meas N0 S n 0 le_rfl t))
      exact hm.stronglyMeasurable
    · have : Z t = fun _ => 0 := by funext ω; simp [hZ, ht]
      rw [this]
      exact stronglyMeasurable_const
  have hZ01 : ∀ t, ∀ᵐ ω ∂μ, Z t ω ∈ Set.Icc (0 : ℝ) 1 := fun t => Filter.Eventually.of_forall fun ω => by
    by_cases ht : t < n
    · rw [hZF t ht]; exact hF01 t ht _
    · simp [hZ, ht]
  have hAz := AZ μ ℱ Z hZm hZ01 n (df2oPar d n δ).δe H.de_pos
  have hFR : ∀ t < n, μ[Z t | ℱ t] =ᵐ[μ] fun ω => ∫ z, F t ((θ ω, cMode n r0 R0 δ K f ω t), z)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    intro t ht
    have hx : Measurable[ℱ t] fun ω => (θ ω, cMode n r0 R0 δ K f ω t) :=
      (hθm t).prodMk (cMode_meas PGM PGG APM hd hKc hKconv hR hmw hf t ht.le)
    have hζ : Measurable (xiL N0 S n d 0 t) := (xiL_meas N0 S n 0 le_rfl t).mono (ℱ.le _) le_rfl
    have hint : Integrable (fun ω => F t ((θ ω, cMode n r0 R0 δ K f ω t), xiL N0 S n d 0 t ω)) μ := by
      refine (integrable_const (1 : ℝ)).mono' ((hFm t ht).comp ((hx.mono (ℱ.le t) le_rfl).prodMk hζ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h01 := hF01 t ht ((θ ω, cMode n r0 R0 δ K f ω t), xiL N0 S n d 0 t ω)
      rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
      exact h01.2
    have h := lemmaFR WΩ (PgSp d × Df2Mode d) (Fin d → ℝ) (ℱ t) μ (fun ω => (θ ω, cMode n r0 R0 δ K f ω t))
      (xiL N0 S n d 0 t) (F t) (ℱ.le t) hx hζ (xiL_indep N0 S n 0 ν t) (hFm t ht) hint
    rw [xiL_law N0 S n 0 le_rfl ν t] at h
    rw [hZF t ht]
    exact h
  have hmean : ∀ ω, Df2Case d n r0 R0 δ (df2World K f ω) → ∀ t, ∫ z, F t ((θ ω, cMode n r0 R0 δ K f ω t), z)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = df2zMean d n r0 R0 δ (df2World K f ω) t := by
    intro ω hcase t
    have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω))) := case_good hcase
    unfold df2zMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hFdef, hθdef]
    rw [cMode_eq hKconv heps0 heps1 ω hgood t]
    unfold cRound
    rw [kTh_good hgood, roundGa_fst (ft' := (df2World K f ω).f t)]
    exact fT_interior (roundGa_play_interior hKconv hr0 hball0 hgood heps0 heps1 n apCall _ _ _ _ _)
  have hZcase : ∀ ω, Df2Case d n r0 R0 δ (df2World K f ω) → ∀ t < n,
      Z t ω = f t (df2zPlay d n r0 R0 δ (df2World K f ω) t) := by
    intro ω hcase t ht
    have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω))) := case_good hcase
    simp only [hZ, ht, ↓reduceIte]
    rw [cPlay_eq hKconv heps0 heps1 ω hgood t]
    exact fT_interior (roundGa_play_interior hKconv hr0 hball0 hgood heps0 heps1 n apCall _ _ _ _ _)
  have hall : ∀ᵐ ω ∂μ, ∀ t, t < n → μ[Z t | ℱ t] ω = ∫ z, F t ((θ ω, cMode n r0 R0 δ K f ω t), z)
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

end Layer2

end AdversarialBco.Poly
