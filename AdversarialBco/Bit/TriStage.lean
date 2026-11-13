/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.TriSamp2
public import AdversarialBco.Bit.ShadowIface

@[expose] public section

/-!
# The position theorem, the stages and (POS) for its position

* The core on rows: `triCoreOut` (the average of `N' = 2^n` steps of rounded projected subgradient descent on the box
  from `(0, I)`), `triCoreRows` (the core theorem, for a polytope given by rows with `PgBody K ρ_a`, the
  parameters of dimension `d` and draws of the sampler at `B_g = 4 k_g` bits: a good position at the radius
  `36.4 d λ(ρ_h)` outside probability `δ`), from `triCore` (Bit/TriCore.lean), the subgradient selection `triU_spec`,
  the coupling `gs_cpl` and the row (R) `tri_par_row`.
* The stages, on the frame `B̄(c, r0) ⊆ K ⊆ B̄(c, R0)`: stage `j` runs the core on the polytope
  `K ∩ triCube c (2^{j+1} r0)` (rows `triRowsA`, `triRowsB`) read in the position of stage `j - 1`, on its own block
  of `L` coins (`triStep`, `triStageN`, `triPos`); `triStages` (every stage good outside probability `δ`, by
  `slice_resample`), `triPos_meas`, `triPos_local` (the position reads the first `m_st L` coins only), `triPos_bad`.
* `triPos_posHyp`: (POS) of the proposition of the coupling of a run (`PosHyp`, Bit/ShadowIface.lean) for the position
  `triPos` on the frame
  `B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)` of Procedure FRAME, its coins read off the odd terms of the Gaussian stream by the
  digit map of (W0).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

open AdversarialBco.Poly

/-- The core on the polytope `{y | ⟪α_k, y⟫ ≤ β_k}` with the parameters of dimension `d` and the integer majorant `ℓ`
of `log(1/δ')`, on the draws `y`: the average of `N' = 2^n` steps of rounded projected subgradient descent on the
box, from `(0, I)`. -/
noncomputable def triCoreOut (d : ℕ) {m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ) (ℓ : ℕ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) : PgSp d :=
  triAvg (triR d) (triA d) (triB d) (1 / 2 ^ triJs d ℓ) (fun x w => triRound (triBv d) (triV (triU α β) x w)) y
    (2 ^ triNe d ℓ)

/-- **The core theorem, on rows**: for a polytope `K = {y | ⟪α_k, y⟫ ≤ β_k}` with
`PgBody K ρ_a`, an integer `ℓ ≥ log(1/δ)`, and draws independent with the law of the sampler at `B_g = 4 k_g` bits,
the core returns a good position for `K` at the radius `36.4 d λ(ρ_h)` outside an event of probability `δ`. -/
theorem triCoreRows (d : ℕ) (hd : 1 ≤ d) {m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hK : PgBody {y | ∀ k, inner ℝ (α k) y ≤ β k} (triRa d)) (ℓ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hℓ : Real.log (1 / δ) ≤ ℓ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = gsLaw d (4 * triKg d))
    (hyM : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (2 * d * (4 * triKg d : ℕ))) :
    P {ω | ¬ PgGood d {y | ∀ k, inner ℝ (α k) y ≤ β k} (36.4 * d * pgLam (triRh d))
      (some (triCoreOut d α β ℓ fun t => y t ω))} ≤ ENNReal.ofReal δ := by
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (α k) y ≤ β k} with hKdef
  obtain ⟨hρa, hρρ, hr, ha0, ha, ha1, hb1, hb⟩ := tri_par_box d hd
  obtain ⟨hGu0, hGu⟩ := tri_par_Gu d hd
  obtain ⟨hD0, hrow⟩ := tri_par_row d ℓ hd δ hδ0 hδ1 hℓ
  have hαβ : ∀ k, ‖α k‖ ≤ β k := rows_norm_le α β hK.2.2.1
  have hkg : 2 ≤ triKg d := le_max_left _ _
  have hB8 : 8 ≤ 4 * triKg d := by omega
  obtain ⟨hlip, hgn⟩ := tri_gauge K hK.1 hK.2.2.1
  have hb0 : 0 ≤ triB d := by linarith
  -- the coupling of the objective on the box
  have hcpl : ∀ x ∈ triBox d (triR d) (triA d) (triB d),
      |∫ w, gauge K (pgMu x + pgOp x w) ∂(gsLaw d (4 * triKg d)) - posK K (pgMu x) (pgOp x)| ≤ triEpsG d := by
    intro x hx
    have h1 := gs_cpl d (4 * triKg d) hB8 (gauge K) hlip (fun z => by rw [abs_of_nonneg (hgn z).1]; exact (hgn z).2)
      (pgMu x) (pgOp x)
    have h2 := tri_opNorm (triR d) (triA d) (triB d) ha0.le x hx
    have h3 := tri_epsG_le d (triKg d) hd hkg (triB d) hb0
    have hε : 0 ≤ gsEps (4 * triKg d) := by unfold gsEps; positivity
    unfold posK posF
    refine h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans ?_)
    unfold triEpsG
    convert h3 using 2
  have hVt : Measurable (Function.uncurry fun x w => triRound (triBv d) (triV (triU α β) x w)) :=
    (tri_round_meas (triBv d)).comp (tri_V_meas (triU α β) (triU_meas α β))
  have hβ : ∀ x ∈ triBox d (triR d) (triA d) (triB d), ∀ w, ‖w‖ ≤ Real.sqrt (8 * d * triKg d) →
      ‖triRound (triBv d) (triV (triU α β) x w) - triV (triU α β) x w‖ ≤ triBu d :=
    fun x _ w _ => tri_round_err (triBv d) _
  have hΔ0 : 0 < Real.sqrt (triD2 d) := Real.sqrt_pos.2 hD0
  have hΔ : 4 * d * triR d ^ 2 + d * (triB d - triA d) ^ 2 + 2 * d * (d - 1) * triB d ^ 2 ≤
      Real.sqrt (triD2 d) ^ 2 := by rw [Real.sq_sqrt hD0.le]; rfl
  have hyM' : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (8 * d * triKg d) := by
    intro t ω
    refine (hyM t ω).trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have := triCore d hd (triRa d) (triRh d) hρa hρρ K hK (triU α β) (fun z => (triU_spec α β hαβ z).1)
    (fun z => (triU_spec α β hαβ z).2.1) (fun z => (triU_spec α β hαβ z).2.2) (triR d) (triA d) (triB d) hr ha0
    ha ha1 hb1 hb (gsLaw d (4 * triKg d)) (triEpsG d) hcpl
    (fun x w => triRound (triBv d) (triV (triU α β) x w)) hVt (Real.sqrt (8 * d * triKg d)) (triBu d)
    (by unfold triBu; positivity) hβ (triGu d) (Real.sqrt (triD2 d)) (1 / 2 ^ triJs d ℓ) hGu0 hGu hΔ0 hΔ
    (by positivity) (2 ^ triNe d ℓ) (by positivity) δ hδ0 hδ1 hrow P y hy hind hlaw hyM'
  exact this

open AdversarialBco.Poly

variable {d : ℕ}

/-! ## The stages -/

/-- `B_g = 4 k_g`, the coins of one block of the sampler. -/
noncomputable def triBg (d : ℕ) : ℕ := 4 * triKg d

/-- The coins of one stage: `N' = 2^n` draws of `2 d B_g` coins. -/
noncomputable def triL (d ℓ : ℕ) : ℕ := 2 ^ triNe d ℓ * (2 * d * triBg d)

/-- The rows of the body of a stage read in the position `P`: `Tᵀ a_k`. -/
noncomputable def triStA {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (P : PgSp d) :
    Fin (m + (d + d)) → EuclideanSpace ℝ (Fin d) :=
  fun k => ContinuousLinearMap.adjoint (pgOp P) (triRowsA A k)

/-- The right-hand sides of the body of a stage read in the position `P`: `b_k - ⟪a_k, μ⟫`. -/
noncomputable def triStB {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) (P : PgSp d) : Fin (m + (d + d)) → ℝ :=
  fun k => triRowsB b c s k - inner ℝ (triRowsA A k) (pgMu P)

/-- Stage `j` from the position `P` on the coins `x` of the stage: the core on the body
`K ∩ triCube c (2^{j+1} r0)` read in `P`, composed with `P`. -/
noncomputable def triStep {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ j : ℕ) (P : PgSp d) (x : ℕ → Bool) : PgSp d :=
  pgComp P (triCoreOut d (triStA A P) (triStB A b c (2 ^ (j + 1) * r0) P) ℓ fun t => triDraw d (triBg d) x t)

/-- The position after the stages `0, ..., j - 1`, from `P_0 = (c, r0 I)`, stage `i` on the coins `ω i`. -/
noncomputable def triStageN {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ : ℕ) (ω : ℕ → ℕ → Bool) : ℕ → PgSp d
  | 0 => pgPack c (r0 • 1)
  | j + 1 => triStep A b c r0 ℓ j (triStageN A b c r0 ℓ ω j) (ω j)

/-- The position returned on the coin stream `cs`: stage `j` reads the coins `j L, ..., j L + L - 1`. -/
noncomputable def triPos {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (ℓ : ℕ) (cs : ℕ → Bool) : PgSp d :=
  triStageN A b c r0 ℓ (fun j k => cs (triLay (triMst r0 R0) (triL d ℓ) (j, k))) (triMst r0 R0)

/-- What holds after the first `i` stages: nothing after none; after stage `i`, a good position for
`K ∩ triCube c (2^{i+1} r0)` at the radius `36.4 d λ(ρ_h)`. -/
def TriStageGood (K : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) :
    ℕ → PgSp d → Prop
  | 0, _ => True
  | i + 1, P => PgGood d (K ∩ triCube c (2 ^ (i + 1) * r0)) (36.4 * d * pgLam (triRh d)) (some P)

theorem triBg_ge (d : ℕ) : 8 ≤ triBg d := by
  have := le_max_left 2 (Nat.clog 2 ⌈16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d⌉₊)
  unfold triBg triKg; omega

/-- The body of a stage, read in `P`, is the polytope of the rows `triStA`, `triStB`. -/
theorem triStage_rows {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) (P : PgSp d) :
    posBody ({y | ∀ k, inner ℝ (A k) y ≤ b k} ∩ triCube c s) (pgMu P) (pgOp P) =
      {z | ∀ k, inner ℝ (triStA A P k) z ≤ triStB A b c s P k} := by
  rw [← tri_cube_rows, tri_rows_pull]
  rfl

theorem triStageN_dep {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ : ℕ) (ω ω' : ℕ → ℕ → Bool) (j : ℕ) (h : ∀ i < j, ω i = ω' i) :
    triStageN A b c r0 ℓ ω j = triStageN A b c r0 ℓ ω' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [triStageN, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)]

theorem tri_pgOp_continuous : Continuous fun P : PgSp d => pgOp P := by
  refine continuous_clm_apply.2 fun v => ?_
  have h := (pg_continuous d).2.2.comp (continuous_id.prodMk continuous_const :
    Continuous fun P : PgSp d => (P, v))
  have e : (fun P : PgSp d => pgOp P v) = fun P => (pgMu P + pgOp P v) - pgMu P := by
    funext P; abel
  rw [e]
  exact h.sub (pg_continuous d).1

theorem triStA_continuous {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) :
    Continuous fun P : PgSp d => triStA A P :=
  continuous_pi fun k =>
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp tri_pgOp_continuous).clm_apply continuous_const

theorem triStB_continuous {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Continuous fun P : PgSp d => triStB A b c s P :=
  continuous_pi fun k => continuous_const.sub (continuous_const.inner (pg_continuous d).1)

theorem triStep_meas {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ j : ℕ) :
    Measurable fun p : PgSp d × (ℕ → Bool) => triStep A b c r0 ℓ j p.1 p.2 := by
  have hf : Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) =>
      (triStA A q.1, triStB A b c (2 ^ (j + 1) * r0) q.1, q.2) :=
    ((triStA_continuous A).measurable.comp measurable_fst).prodMk
      (((triStB_continuous A b c _).measurable.comp measurable_fst).prodMk measurable_snd)
  have hU : Measurable fun q : PgSp d × EuclideanSpace ℝ (Fin d) =>
      triU (triStA A q.1) (triStB A b c (2 ^ (j + 1) * r0) q.1) q.2 := by
    simpa only [Function.comp_def] using (triU_meas2 d (m + (d + d))).comp hf
  have hV := tri_V_meas2 (fun θ z => triU (triStA A θ) (triStB A b c (2 ^ (j + 1) * r0) θ) z) hU
  have hVt : Measurable fun q : PgSp d × PgSp d × EuclideanSpace ℝ (Fin d) =>
      triRound (triBv d) (triV (triU (triStA A q.1) (triStB A b c (2 ^ (j + 1) * r0) q.1)) q.2.1 q.2.2) := by
    simpa only [Function.comp_def] using (tri_round_meas (d := d) (triBv d)).comp hV
  have hA := (triIter_meas2 (triR d) (triA d) (triB d) (1 / 2 ^ triJs d ℓ)
    (fun θ x w => triRound (triBv d) (triV (triU (triStA A θ) (triStB A b c (2 ^ (j + 1) * r0) θ)) x w))
    hVt).2 (2 ^ triNe d ℓ)
  have hY : Measurable fun x : ℕ → Bool => fun t => triDraw d (triBg d) x t :=
    (tri_draw_facts d (triBg d) (triBg_ge d)).2.1
  have hg : Measurable fun p : PgSp d × (ℕ → Bool) => (p.1, fun t => triDraw d (triBg d) p.2 t) :=
    measurable_fst.prodMk (hY.comp measurable_snd)
  have hout : Measurable fun p : PgSp d × (ℕ → Bool) =>
      triAvg (triR d) (triA d) (triB d) (1 / 2 ^ triJs d ℓ)
        (fun x w => triRound (triBv d) (triV (triU (triStA A p.1) (triStB A b c (2 ^ (j + 1) * r0) p.1)) x w))
        (fun t => triDraw d (triBg d) p.2 t) (2 ^ triNe d ℓ) := by
    simpa only [Function.comp_def] using hA.comp hg
  have hfin := (PgMeas.pgComp_continuous d).measurable.comp (measurable_fst.prodMk hout)
  simpa only [Function.comp_def, triStep, triCoreOut] using hfin

theorem triStageN_meas {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ j : ℕ) :
    Measurable fun ω : ℕ → ℕ → Bool => triStageN A b c r0 ℓ ω j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact (triStep_meas A b c r0 ℓ j).comp (ih.prodMk (measurable_pi_apply j))

theorem triStageGood_meas {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (j : ℕ) :
    MeasurableSet {P : PgSp d | TriStageGood {y | ∀ k, inner ℝ (A k) y ≤ b k} c r0 j P} := by
  cases j with
  | zero => simp [TriStageGood]
  | succ i =>
    obtain ⟨h1, h2, h3, h4⟩ := tri_poly_cc A b c (2 ^ (i + 1) * r0)
    exact PgMeas.pgGoodMeas d _ _ (h1.inter h3) (h2.inter h4)

/-- The input of stage `j`: an invertible position and a body between the unit ball and `B(0, ρ_a)`. -/
theorem triStage_input (hd : 1 ≤ d) {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall c r0 ⊆ {y | ∀ k, inner ℝ (A k) y ≤ b k}) (j : ℕ) (P : PgSp d)
    (hP : j = 0 → P = pgPack c (r0 • 1)) (hg : TriStageGood {y | ∀ k, inner ℝ (A k) y ≤ b k} c r0 j P) :
    (pgMat P).det ≠ 0 ∧ PgBody (posBody ({y | ∀ k, inner ℝ (A k) y ≤ b k} ∩ triCube c (2 ^ (j + 1) * r0))
      (pgMu P) (pgOp P)) (triRa d) := by
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (A k) y ≤ b k} with hKdef
  obtain ⟨hKc, hKcl, -, -⟩ := tri_poly_cc A b c 0
  obtain ⟨hpar1, hpar2, -⟩ := tri_par_stage d hd
  have hcK : c ∈ K := hK0 (Metric.mem_closedBall_self hr0.le)
  cases j with
  | zero =>
    rw [hP rfl]
    obtain ⟨hdet, hbody⟩ := tri_stage0_body K hKc hKcl c r0 hr0 hK0
    refine ⟨hdet, ?_⟩
    have e : (2 : ℝ) ^ (0 + 1) * r0 = 2 * r0 := by ring
    rw [e]
    exact pgBody_mono _ _ _ hpar2 hbody
  | succ i =>
    obtain ⟨P', hP', hdet, h1, hR, -⟩ := hg
    obtain rfl := Option.some.inj hP'
    set s := (2 : ℝ) ^ (i + 1) * r0 with hs
    have hs0 : 0 ≤ s := by positivity
    obtain ⟨hcs, hsub, hmid⟩ := tri_cube_mid K hKc c hcK s hs0
    obtain ⟨-, -, hc2, hcl2⟩ := tri_poly_cc A b c (2 * s)
    have e : (2 : ℝ) ^ (i + 1 + 1) * r0 = 2 * s := by rw [hs]; ring
    rw [e]
    refine ⟨hdet, pgBody_mono _ _ _ hpar1 ?_⟩
    exact tri_stage_body (K ∩ triCube c s) (K ∩ triCube c (2 * s)) (hKc.inter hc2) (hKcl.inter hcl2) hsub c hcs
      hmid P hdet _ h1 hR

/-- **The position theorem, the stages**: on independent coin streams, one per stage, the position after the last
stage is good for `K` at the radius `36.4 d λ(ρ_h)` outside an event of probability `δ`. -/
theorem triStages (hd : 1 ≤ d) {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall c r0 ⊆ {y | ∀ k, inner ℝ (A k) y ≤ b k})
    (hKR : {y | ∀ k, inner ℝ (A k) y ≤ b k} ⊆ Metric.closedBall c R0) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ℓ : ℕ) (hℓ : Real.log (triMst r0 R0 / δ) ≤ ℓ) :
    (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
      {ω | ¬ PgGood d {y | ∀ k, inner ℝ (A k) y ≤ b k} (36.4 * d * pgLam (triRh d))
        (some (triStageN A b c r0 ℓ ω (triMst r0 R0)))} ≤ ENNReal.ofReal δ := by
  classical
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (A k) y ≤ b k} with hKdef
  set M := triMst r0 R0 with hM
  obtain ⟨hm1, hmR⟩ := tri_mst r0 R0 hr0
  have hm0 : (0 : ℝ) < M := by exact_mod_cast hm1
  set δ' := δ / M with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ0 hm0
  have hδ'1 : δ' < 1 := (div_le_self hδ0.le (by exact_mod_cast hm1)).trans_lt hδ1
  have hℓ' : Real.log (1 / δ') ≤ ℓ := by rw [hδ', one_div_div]; exact hℓ
  -- the draws of a stage
  set B := triBg d with hB
  obtain ⟨hyM, hYm, -⟩ := tri_draw_facts d B (triBg_ge d)
  have hy : ∀ t, Measurable fun x : ℕ → Bool => triDraw d B x t := fun t => (measurable_pi_apply t).comp hYm
  have hlawJ := tri_draws_law d B
  have hlaw : ∀ t, AdversarialBco.BitRAM.coinStream.map (fun x => triDraw d B x t) = gsLaw d B := by
    intro t
    have e : (fun x => triDraw d B x t) = (fun f : ℕ → EuclideanSpace ℝ (Fin d) => f t) ∘
        (fun x t => triDraw d B x t) := rfl
    rw [e, ← Measure.map_map (measurable_pi_apply t) hYm, hlawJ, Measure.infinitePi_map_eval]
  have hind : iIndepFun (fun t x => triDraw d B x t) AdversarialBco.BitRAM.coinStream := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hy, hlawJ]
    congr 1
    funext t
    rw [hlaw t]
  -- the event of stage `j`: good after `j` stages, not good after `j + 1`
  let C : ℕ → Set ((ℕ → ℕ → Bool) × (ℕ → Bool)) := fun j =>
    {q | TriStageGood K c r0 j (triStageN A b c r0 ℓ q.1 j) ∧
      ¬ TriStageGood K c r0 (j + 1) (triStageN A b c r0 ℓ (Function.update q.1 j q.2) (j + 1))}
  have hCm : ∀ j, MeasurableSet (C j) := fun j =>
    ((triStageGood_meas A b c r0 j).preimage ((triStageN_meas A b c r0 ℓ j).comp measurable_fst)).inter
      ((triStageGood_meas A b c r0 (j + 1)).preimage
        ((triStageN_meas A b c r0 ℓ (j + 1)).comp measurable_update')).compl
  have hE : ∀ j, (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream) {ω | (ω, ω j) ∈ C j} ≤
      ENNReal.ofReal δ' := by
    intro j
    refine slice_resample AdversarialBco.BitRAM.coinStream j (C j) (hCm j) ?_ _ ?_
    · intro ω x x'
      have hdep : triStageN A b c r0 ℓ (Function.update ω j x') j = triStageN A b c r0 ℓ ω j :=
        triStageN_dep A b c r0 ℓ _ _ j fun i hi => Function.update_of_ne (ne_of_lt hi) _ _
      simp only [C, Set.mem_ofPred_eq, Function.update_idem, hdep]
    · intro ω
      set P := triStageN A b c r0 ℓ ω j with hPdef
      by_cases hg : TriStageGood K c r0 j P
      · have hP0 : j = 0 → P = pgPack c (r0 • 1) := by rintro rfl; rfl
        obtain ⟨hdet, hbody⟩ := triStage_input hd A b c r0 hr0 hK0 j P hP0 hg
        rw [triStage_rows] at hbody
        refine le_trans (measure_mono ?_) (triCoreRows d hd (triStA A P) (triStB A b c (2 ^ (j + 1) * r0) P)
          hbody ℓ δ' hδ'0 hδ'1 hℓ' AdversarialBco.BitRAM.coinStream (fun t x => triDraw d B x t) hy hind hlaw
          fun t x => hyM x t)
        intro x hx hgood
        apply hx.2
        have hsj : triStageN A b c r0 ℓ (Function.update ω j x) j = P :=
          triStageN_dep A b c r0 ℓ _ _ j fun i hi => Function.update_of_ne (ne_of_lt hi) _ _
        show PgGood d (K ∩ triCube c (2 ^ (j + 1) * r0)) (36.4 * d * pgLam (triRh d))
          (some (triStageN A b c r0 ℓ (Function.update ω j x) (j + 1)))
        simp only [triStageN, hsj, Function.update_self]
        refine pgGood_comp d _ _ P _ hdet ?_
        rw [triStage_rows]
        exact hgood
      · have hempty : {x | (ω, x) ∈ C j} = ∅ := by
          ext x
          simp only [C, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [hempty, measure_empty]
        exact bot_le
  have hKm : K ∩ triCube c (2 ^ M * r0) = K := by
    refine Set.inter_eq_left.2 fun y hy i => ?_
    have h1 : dist y c ≤ R0 := hKR hy
    have h2 : |y i - c i| ≤ dist y c := by
      rw [dist_eq_norm, ← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (y - c) i
    linarith
  have hfinal : ∀ ω, TriStageGood K c r0 M (triStageN A b c r0 ℓ ω M) →
      PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageN A b c r0 ℓ ω M)) := by
    intro ω hω
    obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [hk] at hω ⊢
    rw [hk] at hKm
    simpa only [TriStageGood, hKm] using hω
  have hcover : {ω | ¬ PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageN A b c r0 ℓ ω M))} ⊆
      ⋃ j ∈ Finset.range M, {ω | (ω, ω j) ∈ C j} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Finset.mem_range, not_exists] at hnot
    have hall : ∀ i ≤ M, TriStageGood K c r0 i (triStageN A b c r0 ℓ ω i) := by
      intro i hi
      induction i with
      | zero => trivial
      | succ i ih =>
        by_contra hb
        refine hnot i (by omega) ?_
        refine ⟨ih (by omega), ?_⟩
        simpa only [Function.update_eq_self] using hb
    exact hω (hfinal ω (hall _ le_rfl))
  calc (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
        {ω | ¬ PgGood d K (36.4 * d * pgLam (triRh d)) (some (triStageN A b c r0 ℓ ω M))}
      ≤ (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
          (⋃ j ∈ Finset.range M, {ω | (ω, ω j) ∈ C j}) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range M, (Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream)
          {ω | (ω, ω j) ∈ C j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range M, ENNReal.ofReal δ' := Finset.sum_le_sum fun j _ => hE j
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hδ']
        field_simp

/-! ## The coins of the procedure and (POS) -/

/-- Stage `j` reads the first `L` coins of its stream only. -/
theorem triStep_local {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ j : ℕ) (P : PgSp d) (x x' : ℕ → Bool)
    (h : ∀ i < triL d ℓ, x i = x' i) : triStep A b c r0 ℓ j P x = triStep A b c r0 ℓ j P x' := by
  have hy : ∀ t < 2 ^ triNe d ℓ, triDraw d (triBg d) x t = triDraw d (triBg d) x' t := by
    intro t ht
    refine (tri_draw_facts d (triBg d) (triBg_ge d)).2.2 x x' t fun i hi => h i ?_
    have ht' : t + 1 ≤ 2 ^ triNe d ℓ := ht
    have hle : 2 * (t + 1) * d * triBg d ≤ triL d ℓ := by
      unfold triL
      calc 2 * (t + 1) * d * triBg d = (t + 1) * (2 * d * triBg d) := by ring
        _ ≤ 2 ^ triNe d ℓ * (2 * d * triBg d) := Nat.mul_le_mul_right _ ht'
    omega
  simp only [triStep, triCoreOut]
  rw [triAvg_congr_y _ _ _ _ _ (fun t => triDraw d (triBg d) x t) (fun t => triDraw d (triBg d) x' t) _ hy]

theorem triStageN_local {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) (ℓ : ℕ) (ω ω' : ℕ → ℕ → Bool) (J : ℕ)
    (h : ∀ j < J, ∀ k < triL d ℓ, ω j k = ω' j k) :
    triStageN A b c r0 ℓ ω J = triStageN A b c r0 ℓ ω' J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [triStageN]
    rw [ih fun j hj k hk => h j (Nat.lt_succ_of_lt hj) k hk]
    exact triStep_local A b c r0 ℓ J _ _ _ fun i hi => h J (Nat.lt_succ_self J) i hi

/-- The position depends on the first `m_st L` coins only. -/
theorem triPos_local {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (ℓ : ℕ) (cs cs' : ℕ → Bool)
    (h : ∀ i < triMst r0 R0 * triL d ℓ, cs i = cs' i) :
    triPos A b c r0 R0 ℓ cs = triPos A b c r0 R0 ℓ cs' := by
  unfold triPos
  refine triStageN_local A b c r0 ℓ _ _ _ fun j hj k hk => h _ ?_
  rw [triLay, if_pos (show j < triMst r0 R0 ∧ k < triL d ℓ from ⟨hj, hk⟩)]
  calc j * triL d ℓ + k < j * triL d ℓ + triL d ℓ := by omega
    _ = (j + 1) * triL d ℓ := by ring
    _ ≤ triMst r0 R0 * triL d ℓ := Nat.mul_le_mul_right _ hj

theorem triPos_meas {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (ℓ : ℕ) : Measurable (triPos A b c r0 R0 ℓ) := by
  have hΦ : Measurable fun cs : ℕ → Bool => fun j k => cs (triLay (triMst r0 R0) (triL d ℓ) (j, k)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_pi_apply _
  exact (triStageN_meas A b c r0 ℓ _).comp hΦ

/-- **The position theorem** on the coin stream: the position returned is good for `K` at the radius `36.4 d λ(ρ_h)`
outside an event of probability `δ`. -/
theorem triPos_bad (hd : 1 ≤ d) {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (r0 R0 : ℝ) (hr0 : 0 < r0)
    (hK0 : Metric.closedBall c r0 ⊆ {y | ∀ k, inner ℝ (A k) y ≤ b k})
    (hKR : {y | ∀ k, inner ℝ (A k) y ≤ b k} ⊆ Metric.closedBall c R0) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ℓ : ℕ) (hℓ : Real.log (triMst r0 R0 / δ) ≤ ℓ) :
    AdversarialBco.BitRAM.coinStream {cs | ¬ PgGood d {y | ∀ k, inner ℝ (A k) y ≤ b k} (36.4 * d * pgLam (triRh d))
      (some (triPos A b c r0 R0 ℓ cs))} ≤ ENNReal.ofReal δ := by
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (A k) y ≤ b k} with hKdef
  obtain ⟨hKc, hKcl, -, -⟩ := tri_poly_cc A b c 0
  set Φ : (ℕ → Bool) → ℕ → ℕ → Bool := fun cs j k => cs (triLay (triMst r0 R0) (triL d ℓ) (j, k)) with hΦdef
  have hΦ : Measurable Φ :=
    Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_pi_apply _
  have hlaw : AdversarialBco.BitRAM.coinStream.map Φ =
      Measure.infinitePi fun _ : ℕ => AdversarialBco.BitRAM.coinStream :=
    coin_curry_inj AdversarialBco.BitRAM.coinLaw _ (tri_lay_inj (triMst r0 R0) (triL d ℓ))
  set S := {ω : ℕ → ℕ → Bool | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
    (some (triStageN A b c r0 ℓ ω (triMst r0 R0)))} with hSdef
  have hS : MeasurableSet S :=
    (PgMeas.pgGoodMeas d K _ hKc hKcl).compl.preimage (triStageN_meas A b c r0 ℓ _)
  calc AdversarialBco.BitRAM.coinStream {cs | ¬ PgGood d K (36.4 * d * pgLam (triRh d))
        (some (triPos A b c r0 R0 ℓ cs))} = AdversarialBco.BitRAM.coinStream (Φ ⁻¹' S) := rfl
    _ = (AdversarialBco.BitRAM.coinStream.map Φ) S := (Measure.map_apply hΦ hS).symm
    _ ≤ ENNReal.ofReal δ := by
      rw [hlaw]
      exact triStages hd A b c r0 R0 hr0 hK0 hKR δ hδ0 hδ1 ℓ hℓ

open AdversarialBco.Bit.Cpl AdversarialBco.Poly.Layer2 in
/-- **(POS) for the position of the position theorem**: on the frame
`B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)` of Procedure FRAME, with an integer `ℓ ≥ log(m_st/δpos)`, if BL's position is the
position `triPos` returned on the coins `β ω.1` read off the Gaussian stream by the digit map `β` of (W0), and the
coins it reads (the first `m_st L`) come from odd terms of the stream, then `PosHyp` holds. -/
theorem triPos_posHyp (hd : 1 ≤ d) {n m : ℕ} (A : Fin m → E d) (b : Fin m → ℝ) (K : Set (E d))
    (hK : K = {y | ∀ k, inner ℝ (A k) y ≤ b k}) (c : E d) (hin : Metric.closedBall c (1 / 2) ⊆ K)
    (hout : K ⊆ Metric.closedBall c n) (δ δpos : ℝ) (hδ0 : 0 < δpos) (hδ1 : δpos < 1) (ℓ : ℕ)
    (hℓ : Real.log (triMst (1 / 2) n / δpos) ≤ ℓ) (ν : Measure (ℕ → ℝ)) [IsProbabilityMeasure ν]
    (B : Run d n K) (β : (ℕ → ℝ) → ℕ → Bool) (hβ : W0Law β) (grp : ℕ → Set ℕ)
    (hloc : ∀ j (x y : ℕ → ℝ), (∀ i ∈ grp j, x i = y i) → β x j = β y j)
    (hodd : ∀ j < triMst (1 / 2) n * triL d ℓ, grp j ⊆ {i | i % 2 = 1})
    (hpos : ∀ ω, B.pos ω = triPos A b c (1 / 2) n ℓ (β ω.1)) : PosHyp ν B δ δpos := by
  subst hK
  set N := triMst (1 / 2) n * triL d ℓ with hN
  let oddPart : (ℕ → ℝ) → ℕ → ℝ := fun x i => if i % 2 = 1 then x i else 0
  have hβodd : ∀ x, ∀ j < N, β (oddPart x) j = β x j := fun x j hj =>
    hloc j _ _ fun i hi => by
      have h1 : i % 2 = 1 := hodd j hj hi
      simp only [oddPart, h1, if_true]
  have hB : B.pos = (fun x => triPos A b c (1 / 2) n ℓ (β x)) ∘ (fun ω : WΩ => oddPart ω.1) := by
    funext ω
    simp only [Function.comp]
    rw [hpos]
    exact triPos_local A b c _ _ ℓ _ _ fun i hi => (hβodd ω.1 i hi).symm
  have hodd_meas : Measurable[cσ d 0] fun ω : WΩ => oddPart ω.1 := by
    refine @Measurable.of_eval WΩ ℕ (fun _ => ℝ) (cσ d 0) _ _ fun i => ?_
    by_cases hi : i % 2 = 1
    · simp only [oddPart, hi, if_true]
      refine Measurable.of_comap_le ?_
      have hle : gσ i ≤ cSeq d 0 :=
        (le_iSup₂ (f := fun i (_ : i ∈ idxC d 0) => gσ i) i (Or.inl hi)).trans le_sup_left
      refine le_trans ?_ hle
      rw [gσ, MeasurableSpace.comap_comp]
      rfl
    · simp only [oddPart, hi, if_false]
      exact measurable_const
  refine ⟨?_, ?_⟩
  · rw [hB]
    exact ((triPos_meas A b c _ _ ℓ).comp hβ.1).comp hodd_meas
  · obtain ⟨-, -, hR⟩ := tri_par_stage d hd
    have hRdf : (df2oPar d n δ).R = 134 * d * Real.sqrt (Real.log (2 * d + 2)) := rfl
    set S := {cs : ℕ → Bool | ¬ PgGood d {y | ∀ k, inner ℝ (A k) y ≤ b k} (36.4 * d * pgLam (triRh d))
      (some (triPos A b c (1 / 2) n ℓ cs))} with hSdef
    obtain ⟨hKc, hKcl, -, -⟩ := tri_poly_cc A b c 0
    have hSm : MeasurableSet S :=
      (PgMeas.pgGoodMeas d _ _ hKc hKcl).compl.preimage (triPos_meas A b c _ _ ℓ)
    have hsub : {ω | ¬ B.Case δ ω} ⊆ (β ⁻¹' S) ×ˢ Set.univ := by
      intro ω hω
      refine ⟨fun hg => hω ?_, Set.mem_univ _⟩
      show PgGood d _ (df2oPar d n δ).R (some (B.pos ω))
      rw [hpos, hRdf]
      exact pgGood_mono d _ _ _ hR _ hg
    calc μs ν {ω | ¬ B.Case δ ω} ≤ μs ν ((β ⁻¹' S) ×ˢ Set.univ) := measure_mono hsub
      _ = AdversarialBco.RealRAM.gaussStream (β ⁻¹' S) := by rw [Measure.prod_prod, measure_univ, mul_one]
      _ = AdversarialBco.BitRAM.coinStream S := by rw [← hβ.2, Measure.map_apply hβ.1 hSm]
      _ ≤ ENNReal.ofReal δpos :=
        triPos_bad hd A b c (1 / 2) n (by norm_num) hin hout δpos hδ0 hδ1 ℓ hℓ

end AdversarialBco.Bit
