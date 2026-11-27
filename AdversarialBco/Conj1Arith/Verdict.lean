/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLin
public import AdversarialBco.Conj1Arith.GjMeas

@[expose] public section

/-!
# The verdict without the step function (leaves D1 and D2)

The third clause of the basic verdict becomes strict, `Q^ - (5/8)(κ/d) I` positive definite (`pgVerdictS`), and the
machine decides it by the signs of the pivots of the Gauss-Jordan elimination it already runs: Lemma P
(`posDef_iff_pivots`, D1, the converse of `gj_pivot_pos`). The accuracy event of Lemma T takes a strict third clause
(`PgAccurateS`) at no cost in probability (D2: in the bound of Lemma T on `Q^`, the event `(κ/(8d))² < ∑` becomes `≤`,
`pgLemmaT_Qle`, and the accuracy bound `pgNotAccurateS_le` follows the decomposition of Lemma T with `pgLemmaT_k` and
`pgLemmaT_b`).

Everything here is proved (`measurableSet_posDef` through the pivots, GjMeas.lean). Junk values: `κ/d` and `κ/(8d)` at
`d ≥ 1`; `gjRun` divides by its pivots, read as a test only.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AdversarialBco.Conj1Arith

open AdversarialBco.Poly AdversarialBco.Poly.PG

variable {d : ℕ}

/-- The invariant `GjInv` along the run when every pivot met is nonzero (the induction of `gjRun_inv`,
MachPGLin.lean, with that hypothesis in place of positive definiteness). -/
theorem gjInv_run (N : Matrix (Fin d) (Fin d) ℝ)
    (hp : ∀ k : Fin d, GjInv N k (gjRun N k) → (gjRun N k).1 k k ≠ 0) : ∀ k, GjInv N k (gjRun N k) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [gjRun]
    · intro i j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro i j _; simp [gjRun, Matrix.one_apply]
  | succ k ih =>
    by_cases hk : k < d
    · have hstep : gjRun N (k + 1) = gjStep (⟨k, hk⟩ : Fin d) (gjRun N k) := by simp [gjRun, hk]
      rw [hstep]
      exact gjStep_inv N (⟨k, hk⟩ : Fin d) (gjRun N k) ih (hp ⟨k, hk⟩ ih)
    · have hrun : gjRun N (k + 1) = gjRun N k := by simp [gjRun, hk]
      rw [hrun]
      rcases ih with ⟨h_eq, h_left, h_right⟩
      refine ⟨h_eq, fun i j hj => h_left i j (by have := j.2; omega), fun i j hj => by have := j.2; omega⟩

/-- D1, direct half: the pivots of a positive definite matrix are positive (`gj_pivot_pos` along the run). -/
theorem pivots_pos_of_posDef (N : Matrix (Fin d) (Fin d) ℝ) (hN : N.PosDef) (k : Fin d) :
    0 < (gjRun N k).1 k k :=
  gj_pivot_pos N hN k _ (gjInv_run N (fun k h => (gj_pivot_pos N hN k _ h).ne') k)

/-- D1, converse half: a symmetric `N` with a lower unitriangular `V` such that `V N` is upper triangular with a
positive diagonal is positive definite, since `V N Vᵀ` is then that diagonal. -/
theorem posDef_of_unitri (N V : Matrix (Fin d) (Fin d) ℝ) (hN : N.IsHermitian)
    (hV : ∀ k m : Fin d, k < m → V k m = 0) (hV1 : ∀ k, V k k = 1)
    (hL : ∀ k j : Fin d, j < k → (V * N) k j = 0) (hD : ∀ k, 0 < (V * N) k k) : N.PosDef := by
  have hdet : V.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular V (fun i j h => hV i j h)]
    simp [hV1]
  have hU : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr (by rw [hdet]; exact isUnit_one)
  rw [← Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
  have hlow : ∀ k l : Fin d, l < k → (V * N * star V) k l = 0 := by
    intro k l hlk
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j k with hjk | hkj
    · rw [hL k j hjk, zero_mul]
    · simp [hV l j (lt_of_lt_of_le hlk hkj)]
  have hsymm : (V * N * star V).IsHermitian := by
    rw [Matrix.star_eq_conjTranspose]; exact Matrix.isHermitian_mul_mul_conjTranspose V hN
  have hW : V * N * star V = Matrix.diagonal fun k => (V * N) k k := by
    ext k l
    rcases lt_trichotomy k l with hkl | rfl | hkl
    · rw [← hsymm.apply k l, hlow l k hkl, Matrix.diagonal_apply_ne _ hkl.ne]; simp
    · rw [Matrix.diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single k]
      · simp [hV1]
      · intro j _ hjk
        rcases lt_or_gt_of_ne hjk with h | h
        · rw [hL k j h, zero_mul]
        · simp [hV k j h]
      · simp
    · rw [hlow k l hkl, Matrix.diagonal_apply_ne _ hkl.ne']
  rw [hW, Matrix.posDef_diagonal_iff]
  exact hD

/-- D1, Lemma P: a symmetric matrix is positive definite if and only if every pivot of Gauss-Jordan elimination
without pivoting is positive. -/
theorem posDef_iff_pivots (N : Matrix (Fin d) (Fin d) ℝ) (hN : N.IsHermitian) :
    N.PosDef ↔ ∀ k : Fin d, 0 < (gjRun N k).1 k k := by
  refine ⟨fun h k => pivots_pos_of_posDef N h k, fun hpiv => ?_⟩
  have hI := gjInv_run N (fun k _ => (hpiv k).ne')
  have hrow : ∀ k j : Fin d, ((Matrix.of fun (k m : Fin d) => (gjRun N k).2 k m) * N) k j = (gjRun N k).1 k j := by
    intro k j
    rw [(hI k).1]
    simp [Matrix.mul_apply]
  refine posDef_of_unitri N (Matrix.of fun (k m : Fin d) => (gjRun N k).2 k m) hN ?_ ?_ ?_ ?_
  · intro k m hkm
    simp only [Matrix.of_apply]
    rw [(hI k).2.2 k m hkm.le]
    simp [hkm.ne]
  · intro k
    simp only [Matrix.of_apply]
    rw [(hI k).2.2 k k le_rfl]
    simp
  · intro k j hjk
    rw [hrow, (hI k).2.1 k j hjk]
    simp [hjk.ne']
  · intro k
    rw [hrow]
    exact hpiv k

/-- The basic verdict with a strict third clause. -/
def pgVerdictS (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  pgKh K ρ x w ≤ 1.075 * pgKappa ∧ ‖pgBh K ρ x w‖ ≤ 3 / 4 * pgTaub d ρ ∧
    (pgQh K ρ x w - (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef

/-- The accuracy event of Lemma T with a strict third clause. -/
def PgAccurateS (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d) (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40 ∧ ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4 ∧
    ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 < (pgKappa / (8 * d)) ^ 2

/-- D2d: the positive definite matrices form a measurable set. -/
theorem measurableSet_posDef (d : ℕ) : MeasurableSet {M : Matrix (Fin d) (Fin d) ℝ | M.PosDef} := by
  have hset : {M : Matrix (Fin d) (Fin d) ℝ | M.PosDef} =
      (⋂ i : Fin d, ⋂ j : Fin d, {M : Matrix (Fin d) (Fin d) ℝ | M j i = M i j}) ∩
        ⋂ k : Fin d, {M : Matrix (Fin d) (Fin d) ℝ | 0 < (gjRun M k).1 k k} := by
    have hH : ∀ M : Matrix (Fin d) (Fin d) ℝ, M.IsHermitian ↔ ∀ i j : Fin d, M j i = M i j := fun M =>
      ⟨fun h i j => by simpa using h.apply i j, fun h => Matrix.IsHermitian.ext fun i j => by simpa using h i j⟩
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨(hH M).mp h.isHermitian, (posDef_iff_pivots M h.isHermitian).mp h⟩,
      fun h => (posDef_iff_pivots M ((hH M).mpr h.1)).mpr h.2⟩
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun k => ?_)
  · exact measurableSet_eq_fun (matrix_entry_measurable measurable_id j i) (matrix_entry_measurable measurable_id i j)
  · exact measurableSet_lt measurable_const (matrix_entry_measurable (measurable_fst.comp (gjRun_measurable k)) k k)

/-- D2e: the matrix of the third clause is symmetric. -/
theorem ggSum_isHermitian (n : ℕ) (F : ℕ → ℝ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i • pgGG (w i) - c • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    pgGG, Matrix.vecMulVec_apply, Matrix.one_apply, mul_comm, eq_comm]

/-- The acceptance set of a strict basic verdict is measurable, for measurable gauge values `F i` and samples
`w i`. -/
theorem verdictS_generic_measurableSet {α : Type*} [MeasurableSpace α] (F : ℕ → α → ℝ)
    (hF : ∀ i, Measurable (F i)) (w : ℕ → α → EuclideanSpace ℝ (Fin d)) (hw : ∀ i, Measurable (w i)) (n : ℕ)
    (c1 c2 c3 : ℝ) :
    MeasurableSet {a | (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F i a ≤ c1 ∧
      ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • w i a‖ ≤ c2 ∧
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • pgGG (w i a) - c3 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef} := by
  have hk : Measurable (fun a => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F i a) :=
    (Finset.measurable_sum _ fun i _ => hF i).const_mul ((n : ℝ)⁻¹)
  have hb : Measurable (fun a => ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • w i a‖) :=
    ((Finset.measurable_sum _ fun i _ => (hF i).smul (hw i)).const_smul ((n : ℝ)⁻¹)).norm
  have hQ : Measurable (fun a =>
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • pgGG (w i a) - c3 • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    refine Measurable.of_eval_matrix _ fun j k => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    refine ((Finset.measurable_sum _ fun i _ => (hF i).mul ?_).const_mul ((n : ℝ)⁻¹)).sub measurable_const
    have hc : Continuous (fun g : EuclideanSpace ℝ (Fin d) => pgGG g j k) := by
      unfold pgGG
      exact ((((PiLp.continuous_ofLp 2 _).matrix_vecMulVec (PiLp.continuous_ofLp 2 _)).sub
        continuous_const).matrix_elem j k)
    exact hc.measurable.comp (hw i)
  exact (measurableSet_le hk measurable_const).inter ((measurableSet_le hb measurable_const).inter
    (hQ (measurableSet_posDef d)))

/-- D2a: the strict verdict implies the old one, so soundness (`pgVerdict_sound`) holds as it is. -/
theorem pgVerdict_of_pgVerdictS (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (h : pgVerdictS K ρ x w) : pgVerdict K ρ x w := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hp := h3.dotProduct_mulVec_pos hv
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at hp
    show 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (pgQh K ρ x w *ᵥ v)
    linarith

/-- D2a': the strict accuracy event implies the old one. -/
theorem pgAccurate_of_pgAccurateS (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (h : PgAccurateS K ρ x w) : PgAccurate K ρ x w := by
  exact ⟨h.1, h.2.1, h.2.2.le⟩

/-- D2b: completeness with the strict clauses (as `pgVerdict_complete`, PgProcProof.lean). -/
theorem pgVerdictS_complete (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) (x : PgSp d)
    (hQ : ∀ v, posQ K (pgMu x) (pgOp x) v v = ∑ i, ∑ j, v i * v j * pgQs K x i j)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hacc : PgAccurateS K ρ x w) (hc : PgComplete K ρ x) :
    pgVerdictS K ρ x w := by
  have hold := pgVerdict_complete d ρ hd K x hQ w (pgAccurate_of_pgAccurateS K ρ x w hacc) hc
  refine ⟨hold.1, hold.2.1, ?_⟩
  have hH : (pgQh K ρ x w - (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian :=
    ggSum_isHermitian (pgNT d ρ) (fun i => pgFt K ρ x (w i)) w (5 / 8 * (pgKappa / d))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv => ?_
  have hkappa : 0 < pgKappa := by unfold pgKappa; norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set v' : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v with hv'
  have hv_norm_sq : ‖v'‖ ^ 2 = v ⬝ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, v', sq]
  have hvv : 0 < v ⬝ᵥ v := by
    rw [← hv_norm_sq]
    have : v' ≠ 0 := fun h => hv (by simpa [v'] using congrArg WithLp.ofLp h)
    positivity
  have hQs_ineq : 3 / 4 * (pgKappa / d) * (v ⬝ᵥ v) ≤ ∑ i, ∑ j, v i * v j * pgQs K x i j := by
    calc 3 / 4 * (pgKappa / d) * (v ⬝ᵥ v) = 3 / 4 * (pgKappa / d) * ‖v'‖ ^ 2 := by rw [hv_norm_sq]
      _ ≤ posQ K (pgMu x) (pgOp x) v' v' := hc.2.2 v'
      _ = ∑ i, ∑ j, v' i * v' j * pgQs K x i j := hQ v'
      _ = ∑ i, ∑ j, v i * v j * pgQs K x i j := by simp [v']
  set M := pgQh K ρ x w - pgQs K x with hM
  set ε := Real.sqrt (∑ i, ∑ j, M i j ^ 2) with hε
  have hε_lt : ε < pgKappa / (8 * d) := by
    rw [hε, Real.sqrt_lt' (by positivity)]
    simpa [hM] using hacc.2.2
  have hquad := quad_le_frob M ε (Real.sqrt_nonneg _) (by rw [hε, Real.sq_sqrt (by positivity)]) v'
  rw [hv_norm_sq] at hquad
  have hquad' : |∑ i, ∑ j, v i * v j * M i j| < pgKappa / (8 * d) * (v ⬝ᵥ v) := by
    have : |∑ i, ∑ j, v i * v j * M i j| ≤ ε * (v ⬝ᵥ v) := by simpa [v'] using hquad
    exact this.trans_lt (mul_lt_mul_of_pos_right hε_lt hvv)
  have h_diff_eq : ∑ i, ∑ j, v i * v j * M i j =
      (∑ i, ∑ j, v i * v j * pgQh K ρ x w i j) - (∑ i, ∑ j, v i * v j * pgQs K x i j) := by
    simp [hM, Finset.sum_sub_distrib, mul_sub]
  have h_lhs : star v ⬝ᵥ ((pgQh K ρ x w - (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) =
      (∑ i, ∑ j, v i * v j * pgQh K ρ x w i j) - 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) := by
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h_lhs]
  have habs := (abs_lt.mp hquad').1
  have h8 : pgKappa / (8 * d) = 1 / 8 * (pgKappa / d) := by field_simp
  rw [h8] at habs
  nlinarith

/-- The bound of Lemma T on `Q^` with the event at `≤`, for the strict clause of `PgAccurateS`: the event
`(κ/(8d))² ≤ ∑ (Q^ - Q)²` has probability at most `1/12`. The proof of the bound at `<`, with `2 t ≤ |Q^ - Q|` in
place of `2 t < |Q^ - Q|`. -/
theorem pgLemmaT_Qle (hCheb : ChebAvg) (hBT : PgBiasTest) (hCnt : PgCounts)
    (hPT : PiTildeMeasurable) (hLB : LemmaB) (hD4 : D4Bounds) (hEta : PgEtaSq)
    (hVec : VecCS) (hMat : MatCS) (hFrob : FrobStat) (hMom : MomentsE) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {w | (pgKappa / (8 * d)) ^ 2 ≤ ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2} ≤ ENNReal.ofReal (1 / 12) := by
  -- Convenient abbreviations
  let n := pgNT d ρ
  let t := pgKappa / (16 * (d : ℝ))
  have hd_pos_nat : 0 < d := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hd
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have ht_pos : 0 < t := by
    dsimp [t]
    refine div_pos (by norm_num [pgKappa]) ?_
    nlinarith
  have hn_pos : 1 ≤ n := by
    rcases hCnt (d : ℝ) ρ (by exact_mod_cast hd) hρ with ⟨_, _, hthird⟩
    have hpos : 0 < pgNTreal d ρ := by
      have h_pgLD_pos : 0 < pgLD ρ := by
        dsimp [pgLD, pgKappa, pgPB]
        positivity
      have hpos_num : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) := by
        positivity
      have hpos_den : 0 < (pgKappa / (16 * (d : ℝ))) ^ 2 := by
        have hpos_div : 0 < pgKappa / (16 * (d : ℝ)) :=
          div_pos (by norm_num [pgKappa]) (by nlinarith)
        positivity
      have hpos' : 0 < 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) /
          (pgKappa / (16 * (d : ℝ))) ^ 2 :=
        div_pos hpos_num hpos_den
      linarith
    have hceil : 0 < ⌈pgNTreal d ρ⌉₊ := Nat.ceil_pos.mpr hpos
    have h_one_le : (1 : ℕ) ≤ ⌈pgNTreal d ρ⌉₊ := Nat.one_le_of_lt hceil
    simpa [n, pgNT] using h_one_le
  -- Measurability of pgFt K ρ x
  have h_pgFt_meas : Measurable (pgFt K ρ x) := by
    have h := pgFt_measurable hPT d K ρ hK.2.1
    exact h.comp (Measurable.prodMk measurable_const measurable_id)
  -- Measurability of each entry of gstat
  have h_gstat_entry_meas : ∀ (i j : Fin d),
      Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => gstat g i j) := by
    intro i j
    have h_gi : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
      have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
        have h_equiv_cont : Continuous (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous
        have h_proj_cont : Continuous (fun (f : Fin d → ℝ) => f i) := continuous_apply i
        have h_eq : (fun (g : EuclideanSpace ℝ (Fin d)) => g i) =
            (fun (f : Fin d → ℝ) => f i) ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) := by
          ext g
          simp [PiLp.continuousLinearEquiv_apply]
        rw [h_eq]
        exact h_proj_cont.comp h_equiv_cont
      exact h_cont.measurable
    have h_gj : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g j) := by
      have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g j) := by
        have h_equiv_cont : Continuous (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) :=
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous
        have h_proj_cont : Continuous (fun (f : Fin d → ℝ) => f j) := continuous_apply j
        have h_eq : (fun (g : EuclideanSpace ℝ (Fin d)) => g j) =
            (fun (f : Fin d → ℝ) => f j) ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) := by
          ext g
          simp [PiLp.continuousLinearEquiv_apply]
        rw [h_eq]
        exact h_proj_cont.comp h_equiv_cont
      exact h_cont.measurable
    have h_prod : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i * g j) :=
      Measurable.mul h_gi h_gj
    have h_const : Measurable (fun (_ : EuclideanSpace ℝ (Fin d)) => (if i = j then (1 : ℝ) else 0)) :=
      measurable_const
    have h_diff : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
      g i * g j - (if i = j then (1 : ℝ) else 0)) :=
      Measurable.sub h_prod h_const
    simpa [gstat] using h_diff
  -- Define Φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d × Fin d)
  let Φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d × Fin d) :=
    fun g => WithLp.toLp 2 (fun p : Fin d × Fin d => pgFt K ρ x g * gstat g p.1 p.2)
  -- Φ is measurable
  have hΦ_meas : Measurable Φ := by
    have h_toLp_meas : Measurable (WithLp.toLp 2 :
      ((Fin d × Fin d) → ℝ) → EuclideanSpace ℝ (Fin d × Fin d)) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d × Fin d => ℝ)).symm.continuous.measurable
    have h_inner_meas : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
      (fun (p : Fin d × Fin d) => pgFt K ρ x g * gstat g p.1 p.2)) := by
      rw [measurable_pi_iff]
      intro p
      rcases p with ⟨i, j⟩
      exact Measurable.mul h_pgFt_meas (h_gstat_entry_meas i j)
    exact h_toLp_meas.comp h_inner_meas
  -- Φ is in L²
  have hΦ_memLp : MemLp Φ 2 (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have h_moments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
    simpa [Φ] using h_moments.2.2.2.2.1
  -- Second moment bound from pgFt_moments
  have h_int_bound : ∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5)) := by
    have h_moments := pgFt_moments hPT hLB hD4 hEta hFrob hMom d ρ hd hρ K hK x hx
    simpa [Φ] using h_moments.2.2.2.2.2
  -- Integrability of Φ
  have hΦ_int : Integrable Φ (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hΦ_memLp.integrable (by norm_num : 1 ≤ (2 : ENNReal))
  -- Apply Chebyshev's inequality
  have h_cheb := hCheb (EuclideanSpace ℝ (Fin d × Fin d)) (EuclideanSpace ℝ (Fin d))
    (stdGaussian (EuclideanSpace ℝ (Fin d))) Φ hΦ_meas hΦ_memLp n t hn_pos ht_pos
  -- h_cheb : P(‖avg - EΦ‖ ≥ t) ≤ ENNReal.ofReal ((∫ ‖Φ‖²) / (n * t²))
  -- Bound the RHS using PgCounts
  have h_bound : ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2)) ≤
      ENNReal.ofReal (1 / 12) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rcases hCnt (d : ℝ) ρ (by exact_mod_cast hd) hρ with ⟨_, _, hthird⟩
    have hpos_t_sq : 0 < t ^ 2 := by positivity
    have hn_pos_nat : 0 < n := by omega
    have hn_pos' : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    -- From hthird: 12 * num / (pgKappa/(16*d))² ≤ pgNTreal ≤ n
    -- So 12 * num / t² ≤ n, i.e., num / (n * t²) ≤ 1/12
    have hthird' : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / (pgKappa / (16 * (d : ℝ))) ^ 2 ≤
        pgNTreal d ρ := hthird
    have hNTreal_le_n : pgNTreal d ρ ≤ (n : ℝ) := by
      have hceil : (pgNTreal d ρ : ℝ) ≤ (⌈pgNTreal d ρ⌉₊ : ℝ) :=
        Nat.ceil_le.mp (le_refl (⌈pgNTreal d ρ⌉₊))
      simpa [n, pgNT] using hceil
    have h_ineq : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / (pgKappa / (16 * (d : ℝ))) ^ 2 ≤ (n : ℝ) := by
      linarith
    -- From h_ineq: 12*num/t² ≤ n, multiply by t²: 12*num ≤ n*t²
    -- Then divide by 12*n*t²: num/(n*t²) ≤ 1/12
    have h_ineq' : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) ≤ (n : ℝ) * t ^ 2 := by
      have hpos_sq : (pgKappa / (16 * (d : ℝ))) ^ 2 ≠ 0 := by positivity
      have h_eq : 12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) =
          (12 * (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((pgKappa / (16 * (d : ℝ))) ^ 2)) *
          ((pgKappa / (16 * (d : ℝ))) ^ 2) := by
        exact (div_mul_cancel₀ _ hpos_sq).symm
      rw [h_eq]
      -- Goal: (A / B) * B ≤ (n : ℝ) * t ^ 2
      -- Using h_ineq: A / B ≤ n (where A = 12*..., B = (pgKappa/(16*d))^2)
      -- And t = pgKappa/(16*d), so B = t^2
      -- So (A / B) * B ≤ n * t^2
      have hB_nonneg : 0 ≤ ((pgKappa / (16 * (d : ℝ))) ^ 2) := by positivity
      have hB_eq_t_sq : ((pgKappa / (16 * (d : ℝ))) ^ 2) = t ^ 2 := by
        dsimp [t]
      rw [hB_eq_t_sq]
      exact mul_le_mul_of_nonneg_right h_ineq hB_nonneg
    -- Now combine h_int_bound and h_ineq'
    have h_div_le : (∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2) ≤
        (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((n : ℝ) * t ^ 2) :=
      div_le_div_of_nonneg_right h_int_bound (by positivity)
    have h_goal : (5 / 4 * pgLD ρ ^ 2 * (2 * (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 5))) / ((n : ℝ) * t ^ 2) ≤ 1 / 12 := by
      field_simp [hn_pos'.ne.symm, hpos_t_sq.ne.symm]
      nlinarith
    exact le_trans h_div_le h_goal
  -- Now the main inclusion: the event in the theorem is contained in the Chebyshev tail event
  have h_inclusion : {ω | (pgKappa / (8 * d)) ^ 2 ≤ ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2} ⊆
      {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) -
        ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖} := by
    intro ω hω
    -- hω : (pgKappa / (8 * d)) ^ 2 ≤ ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2
    -- We need to show: t ≤ ‖avg - EΦ‖
    -- First, relate the coordinates of avg_val to pgQh
    have h_avg_coord : ∀ (i j : Fin d), ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)) (i, j) = pgQh K ρ x ω i j := by
      intro i j
      calc
        ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)) (i, j)
            = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, (Φ (ω k)) (i, j)) := by
          simp [smul_eq_mul, Finset.sum_apply]
        _ = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, pgFt K ρ x (ω k) * gstat (ω k) i j) := by
          simp [Φ]
        _ = ((pgNT d ρ : ℝ)⁻¹ • ∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (ω k) • pgGG (ω k)) i j := by
          rw [Matrix.smul_apply, Matrix.sum_apply]
          simp [pgGG, gstat, Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
          rfl
        _ = pgQh K ρ x ω i j := rfl
    -- From pgFt_bias, we have the bias bound
    have h_bias := pgFt_bias hPT hLB hD4 hEta hVec hMat d ρ hd hρ K hK x hx
    rcases h_bias with ⟨_, _, h_bias_sq⟩
    -- From PgBiasTest, we have: sqrt(2)*pgU ≤ τ_b/8 ≤ κ/(16*d) = t
    have h_bias_test := hBT (d : ℝ) ρ (by exact_mod_cast hd) hρ
    rcases h_bias_test with ⟨h_sqrt2_U_le_taub, _, h_taub_le_t⟩
    have h_sqrt2_U_le_t : Real.sqrt 2 * pgU d ρ ≤ t := by
      dsimp [pgU, t]
      linarith
    -- Convert Matrix to EuclideanSpace
    let matToEuclidean (A : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (Fin d × Fin d) :=
      WithLp.toLp 2 (fun (p : Fin d × Fin d) => A p.1 p.2)
    -- The Frobenius norm squared equals the Euclidean norm squared
    have h_norm_sq_eq (A : Matrix (Fin d) (Fin d) ℝ) : ‖matToEuclidean A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [matToEuclidean, Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
    -- Note that (pgKappa / (8 * d)) = 2 * t
    have h_kappa_over_8d_eq_2t : pgKappa / (8 * (d : ℝ)) = 2 * t := by
      dsimp [t]
      field_simp [show (d : ℝ) ≠ 0 from by linarith]
      ring
    -- The squared Frobenius norm of (pgQh - pgQs) equals the squared Euclidean norm
    have h_frob_sq_eq : ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2 =
        ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ^ 2 := by
      rw [h_norm_sq_eq]
      simp [Matrix.sub_apply]
    -- From hω: 4 t² ≤ |Q^ - Q|², so 2 t ≤ |Q^ - Q|
    have h_norm_avgQ_gt_2t : 2 * t ≤ ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ := by
      have h_sq : (2 * t) ^ 2 ≤ ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ^ 2 := by
        rw [← h_kappa_over_8d_eq_2t, ← h_frob_sq_eq]
        simpa using hω
      have h_nonneg : 0 ≤ ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ := norm_nonneg _
      have h_2t_nonneg : 0 ≤ 2 * t := by nlinarith
      exact (pow_le_pow_iff_left₀ h_2t_nonneg h_nonneg two_ne_zero).mp h_sq
    -- Now we need to bound ‖matToEuclidean (EΦ - Q)‖ ≤ t
    let EΦ_val := ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
    -- The key identity: EΦ_val (i, j) = ∫ pgFt * gstat i j
    have h_EΦ_coord : ∀ (i j : Fin d), EΦ_val (i, j) = ∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
      intro i j
      calc
        EΦ_val (i, j) = (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (i, j) := rfl
        _ = ∫ g, (Φ g) (i, j) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
          -- Use ContinuousLinearMap.integral_comp_comm with the projection
          let L : EuclideanSpace ℝ (Fin d × Fin d) →L[ℝ] ℝ := EuclideanSpace.proj (i, j)
          have h_int_eq : ∫ g, L (Φ g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = L (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
            ContinuousLinearMap.integral_comp_comm L hΦ_int
          calc
            (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) (i, j) = L (∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
              simp [L, EuclideanSpace.proj]
            _ = ∫ g, L (Φ g) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by rw [h_int_eq]
            _ = ∫ g, (Φ g) (i, j) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by simp [L, EuclideanSpace.proj]
        _ = ∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by simp [Φ]
    -- Using h_EΦ_coord, we can bound the norm
    have h_norm_EΦQ_le_t : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ≤ t := by
      have h_sq_sum : ∑ i, ∑ j, (EΦ_val (i, j) - (matToEuclidean (pgQs K x)) (i, j)) ^ 2 ≤ t ^ 2 := by
        calc
          ∑ i, ∑ j, (EΦ_val (i, j) - (matToEuclidean (pgQs K x)) (i, j)) ^ 2
              = ∑ i, ∑ j, (EΦ_val (i, j) - pgQs K x i j) ^ 2 := by
            simp [matToEuclidean]
          _ = ∑ i, ∑ j, (∫ g, pgFt K ρ x g * gstat g i j ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) - pgQs K x i j) ^ 2 := by
            simp_rw [h_EΦ_coord]
          _ ≤ 2 * pgU d ρ ^ 2 := h_bias_sq
          _ ≤ t ^ 2 := by
            have h_sq : (Real.sqrt 2 * pgU d ρ) ^ 2 ≤ t ^ 2 := by
              have h_nonneg_sqrt : 0 ≤ Real.sqrt 2 * pgU d ρ := by
                have h_sqrt2 : 0 ≤ Real.sqrt 2 := by positivity
                have h_pgU : 0 ≤ pgU d ρ := by
                  have e1 := (hEta d ρ (by exact_mod_cast hd) hρ).1
                  have e2 : 0 ≤ pgLD ρ := by
                    unfold pgLD pgKappa pgPB; have : (0 : ℝ) ≤ ρ := by linarith
                    positivity
                  unfold pgU; positivity
                nlinarith
              nlinarith
            have h_sqrt_sq : (Real.sqrt 2 * pgU d ρ) ^ 2 = 2 * pgU d ρ ^ 2 := by
              calc
                (Real.sqrt 2 * pgU d ρ) ^ 2 = (Real.sqrt 2) ^ 2 * pgU d ρ ^ 2 := by ring
                _ = 2 * pgU d ρ ^ 2 := by rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
            nlinarith
      -- Now relate the sum of squares to the Euclidean norm squared
      have h_norm_sq_eq' : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ^ 2 = ∑ i, ∑ j, ((EΦ_val - matToEuclidean (pgQs K x)) (i, j)) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        -- Goal: ∑ i, ‖x.ofLp i‖ ^ 2 = ∑ i, ∑ j, x.ofLp (i, j) ^ 2
        -- where x = EΦ_val - matToEuclidean (pgQs K x)
        -- Simplify the left side: ‖x.ofLp i‖ ^ 2 = (x i) ^ 2
        -- and the right side using Fintype.sum_prod_type
        have h_simp (p : Fin d × Fin d) : ‖((EΦ_val - matToEuclidean (pgQs K x))).ofLp p‖ ^ 2 = ((EΦ_val - matToEuclidean (pgQs K x)) p) ^ 2 := by
          simp [Real.norm_eq_abs, sq_abs]
        calc
          ∑ i : Fin d × Fin d, ‖((EΦ_val - matToEuclidean (pgQs K x))).ofLp i‖ ^ 2
              = ∑ i : Fin d × Fin d, ((EΦ_val - matToEuclidean (pgQs K x)) i) ^ 2 := by
            simp_rw [h_simp]
          _ = ∑ i : Fin d, ∑ j : Fin d, ((EΦ_val - matToEuclidean (pgQs K x)) (i, j)) ^ 2 := by
            rw [Fintype.sum_prod_type]
      have h_sub_coord : ∀ (i j : Fin d), (EΦ_val - matToEuclidean (pgQs K x)) (i, j) = EΦ_val (i, j) - pgQs K x i j := by
        intro i j; simp [matToEuclidean]
      have h_norm_sq_le : ‖EΦ_val - matToEuclidean (pgQs K x)‖ ^ 2 ≤ t ^ 2 := by
        rw [h_norm_sq_eq']
        simp_rw [h_sub_coord]
        simpa [matToEuclidean] using h_sq_sum
      nlinarith
    -- Now we can use the triangle inequality
    have h_triangle : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
        ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
      let avg_val := (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k)
      have h_avg_sub : matToEuclidean (pgQh K ρ x ω - pgQs K x) = avg_val - matToEuclidean (pgQs K x) := by
        refine PiLp.ext fun p => ?_
        rcases p with ⟨i, j⟩
        unfold matToEuclidean
        rw [PiLp.toLp_apply, PiLp.toLp_apply]
        simp [Matrix.sub_apply]
        rw [← h_avg_coord i j]
      have h_tri := norm_sub_le (avg_val - EΦ_val) (matToEuclidean (pgQs K x) - EΦ_val)
      have h_goal : ‖avg_val - matToEuclidean (pgQs K x)‖ ≤ ‖avg_val - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
        have h_left : (avg_val - EΦ_val) - (matToEuclidean (pgQs K x) - EΦ_val) = avg_val - matToEuclidean (pgQs K x) := by
          calc
            (avg_val - EΦ_val) - (matToEuclidean (pgQs K x) - EΦ_val)
                = avg_val - EΦ_val - matToEuclidean (pgQs K x) + EΦ_val := by abel
            _ = avg_val - matToEuclidean (pgQs K x) := by abel
        have h_right : ‖matToEuclidean (pgQs K x) - EΦ_val‖ = ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by rw [norm_sub_rev]
        rw [h_left, h_right] at h_tri
        exact h_tri
      -- Now combine with h_avg_sub
      have h_target : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
          ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
        -- Using h_avg_sub and h_goal
        have h_target' : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ ≤
            ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ + ‖EΦ_val - matToEuclidean (pgQs K x)‖ := by
          have h_norm_eq : ‖matToEuclidean (pgQh K ρ x ω - pgQs K x)‖ = ‖avg_val - matToEuclidean (pgQs K x)‖ :=
            congrArg norm h_avg_sub
          rw [h_norm_eq]
          rw [show ‖avg_val - EΦ_val‖ = ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ by dsimp [avg_val]]
          exact h_goal
        exact h_target'
      exact h_target
    -- Combine the bounds
    have h_result : t ≤ ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Φ (ω k) - EΦ_val‖ := by
      nlinarith
    -- Return the result
    exact h_result
  -- Combine everything
  calc
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {ω | (pgKappa / (8 * d)) ^ 2 ≤ ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2}
    ≤ (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d)))
      {ω | t ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Φ (ω i) -
        ∫ g, Φ g ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))‖} :=
      measure_mono h_inclusion
    _ ≤ ENNReal.ofReal ((∫ g, ‖Φ g‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) / ((n : ℝ) * t ^ 2)) := h_cheb
    _ ≤ ENNReal.ofReal (1 / 12) := h_bound

/-- D2c: the accuracy bound with the strict clause, through `pgLemmaT_k`, `pgLemmaT_b` and `pgLemmaT_Qle`. -/
theorem pgNotAccurateS_le (H : PgCoreHyps) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : PgBody K ρ) (x : PgSp d) (hx : x ∈ pgDom d ρ) :
    (Measure.infinitePi fun _ : ℕ => stdGaussian (EuclideanSpace ℝ (Fin d))) {w | ¬ PgAccurateS K ρ x w} ≤
      ENNReal.ofReal (1 / 4) := by
  have hsub : {w | ¬ PgAccurateS K ρ x w} ⊆
      {w | pgKappa / 40 < |pgKh K ρ x w - pgKs K x|} ∪ {w | pgTaub d ρ / 4 < ‖pgBh K ρ x w - pgBs K x‖} ∪
        {w | (pgKappa / (8 * d)) ^ 2 ≤ ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2} := by
    intro w hw
    simp only [PgAccurateS, Set.mem_ofPred_eq, Set.mem_union] at hw ⊢
    by_contra h
    push Not at h
    exact hw ⟨h.1.1, h.1.2, h.2⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add
    (pgLemmaT_k H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x hx)
    (pgLemmaT_b H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x hx)))
    (pgLemmaT_Qle H.hCheb H.hBT H.hCnt H.hPT H.hLB H.hD4 H.hEta H.hVec H.hMat H.hFrob H.hMom d ρ hd hρ K hK x
      hx)).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- D2d: the strict accuracy event is measurable. -/
theorem pgAccurateS_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) (x : PgSp d) : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | PgAccurateS K ρ x w} := by
  have hFt_meas (i : ℕ) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgFt K ρ x (w i)) := by
    have h_pair : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (x, w i)) :=
      Measurable.prodMk measurable_const (measurable_pi_apply i)
    have hFt : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgFt K ρ p.1 p.2) :=
      pgFt_measurable hPT d K ρ hK
    exact hFt.comp h_pair
  have h_sumFt : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i)) :=
    Finset.measurable_sum _ (fun i hi => hFt_meas i)
  have h_pgKh : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgKh K ρ x w) := by
    unfold pgKh
    have : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ *
        (∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i))) =
        (fun s : ℝ => (pgNT d ρ : ℝ)⁻¹ * s) ∘
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i)) := rfl
    rw [this]
    exact (measurable_const_mul _).comp h_sumFt
  have h1 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => |pgKh K ρ x w - pgKs K x|) :=
      (h_pgKh.sub measurable_const).abs
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => pgKappa / 40) := measurable_const
    exact measurableSet_le h_meas h_rhs
  have h_pgBh : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgBh K ρ x w) := by
    unfold pgBh
    have h_sum : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i) :=
      Finset.measurable_sum _ (fun i hi => (hFt_meas i).smul (measurable_pi_apply i))
    have : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ •
        (∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i)) =
        (fun s : EuclideanSpace ℝ (Fin d) => (pgNT d ρ : ℝ)⁻¹ • s) ∘
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w i) • w i) := rfl
    rw [this]
    exact (measurable_const_smul _).comp h_sum
  have h2 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) | ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => ‖pgBh K ρ x w - pgBs K x‖) :=
      (h_pgBh.sub measurable_const).norm
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => pgTaub d ρ / 4) := measurable_const
    exact measurableSet_le h_meas h_rhs
  have h_apply (i : Fin d) : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
    have h_cont : Continuous (fun (g : EuclideanSpace ℝ (Fin d)) => g i) := by
      simpa using PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
    exact h_cont.measurable
  have h_meas_pgGG (i j : Fin d) : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => pgGG g i j) := by
    unfold pgGG
    have h_mul : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) => g i * g j) :=
      (h_apply i).mul (h_apply j)
    have h_sub : Measurable (fun (g : EuclideanSpace ℝ (Fin d)) =>
        g i * g j - (1 : Matrix (Fin d) (Fin d) ℝ) i j) :=
      h_mul.sub measurable_const
    simpa [Matrix.vecMulVec_apply, Matrix.one_apply] using h_sub
  have h_pgQh (i j : Fin d) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgQh K ρ x w i j) := by
    unfold pgQh
    have h_meas_entry (k : ℕ) : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgFt K ρ x (w k) * pgGG (w k) i j) :=
      (hFt_meas k).mul ((h_meas_pgGG i j).comp (measurable_pi_apply k))
    have h_sum : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) * pgGG (w k) i j) :=
      Finset.measurable_sum _ (fun k hk => h_meas_entry k)
    have h_eq : (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => ((pgNT d ρ : ℝ)⁻¹ •
        (∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) • pgGG (w k))) i j) =
        (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => (pgNT d ρ : ℝ)⁻¹ *
        (∑ k ∈ Finset.range (pgNT d ρ), pgFt K ρ x (w k) * pgGG (w k) i j)) := by
      ext w
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
    rw [h_eq]
    exact (measurable_const_mul _).comp h_sum
  have h3 : MeasurableSet {w : ℕ → EuclideanSpace ℝ (Fin d) |
      ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2 < (pgKappa / (8 * d)) ^ 2} := by
    have h_meas : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) =>
        ∑ i, ∑ j, (pgQh K ρ x w i j - pgQs K x i j) ^ 2) := by
      refine Finset.measurable_sum Finset.univ (fun i hi => ?_)
      refine Finset.measurable_sum Finset.univ (fun j hj => ?_)
      have h_sub : Measurable (fun (w : ℕ → EuclideanSpace ℝ (Fin d)) => pgQh K ρ x w i j - pgQs K x i j) :=
        (h_pgQh i j).sub (measurable_const (a := pgQs K x i j))
      have h_mul := h_sub.mul h_sub
      convert h_mul using 1
      ext w
      simp [sq]
    have h_rhs : Measurable (fun _ : ℕ → EuclideanSpace ℝ (Fin d) => (pgKappa / (8 * d)) ^ 2) := measurable_const
    exact measurableSet_lt h_meas h_rhs
  have h_acc : {w : ℕ → EuclideanSpace ℝ (Fin d) | PgAccurateS K ρ x w} =
      ({w | |pgKh K ρ x w - pgKs K x| ≤ pgKappa / 40} ∩
      {w | ‖pgBh K ρ x w - pgBs K x‖ ≤ pgTaub d ρ / 4}) ∩
      {ω | ∑ i, ∑ j, (pgQh K ρ x ω i j - pgQs K x i j) ^ 2 < (pgKappa / (8 * d)) ^ 2} := by
    ext w; simp [PgAccurateS, and_assoc]
  rw [h_acc]
  exact (h1.inter h2).inter h3

/-- D2d: the strict verdict is measurable jointly in the point and the samples. -/
theorem pgVerdictS_measurableSet (hPT : PiTildeMeasurable) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdictS K ρ p.1 p.2} := by
  have h := verdictS_generic_measurableSet
    (fun i (p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d))) => pgFt K ρ p.1 (p.2 i))
    (fun i => (pgFt_measurable hPT d K ρ hK).comp
      (f := fun p : PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) => (p.1, p.2 i)) (by fun_prop))
    (fun i p => p.2 i) (fun i => by fun_prop) (pgNT d ρ) (1.075 * pgKappa) (3 / 4 * pgTaub d ρ)
    (5 / 8 * (pgKappa / d))
  convert h using 2 with p
  rfl

/-- D2e: the matrix of the third clause is symmetric, so Lemma P decides the clause by the pivots. -/
theorem pgVerdictS_iff_pivots (K : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (x : PgSp d)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) :
    pgVerdictS K ρ x w ↔ pgKh K ρ x w ≤ 1.075 * pgKappa ∧ ‖pgBh K ρ x w‖ ≤ 3 / 4 * pgTaub d ρ ∧
      ∀ k : Fin d, 0 < (gjRun (pgQh K ρ x w - (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)) k).1 k k := by
  have hH : (pgQh K ρ x w - (5 / 8 * (pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian :=
    ggSum_isHermitian (pgNT d ρ) (fun i => pgFt K ρ x (w i)) w (5 / 8 * (pgKappa / d))
  unfold pgVerdictS
  rw [posDef_iff_pivots _ hH]

end AdversarialBco.Conj1Arith
