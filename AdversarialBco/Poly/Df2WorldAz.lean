/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldVE

@[expose] public section

/-!
# The round of D0: measurability tools and the loss read at the play

* Functions of a mode: the code of a mode is measurable (`measurable_modeCode`), and a function of a mode is
  measurable when its three branches are (`measurable_mode_split`).
* The point a round plays does not depend on the loss, the noise or the dither of that round (`roundGa_fst`); the
  round depends on the loss through its values on the interior of `K` only (`roundGa_loss_congr`).
* The point played from a state, for the gauge of the body `kTh` of `Df2WorldVE.lean`: `cX`, `cPt` and `cPoint`,
  `S⁻¹(X/pip(X))` with `X = μ + (1 - λ) A ξ`.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM
open AdversarialBco.Conj1Arith (PgMeasN clampNSRoutine)

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

end Adapted

end Layer2

end AdversarialBco.Poly
