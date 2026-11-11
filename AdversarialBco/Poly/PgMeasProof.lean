/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.PgProcBase

@[expose] public section

/-!
# Procedures PG-core and PG: measurability of the outputs

Proofs of the named hypotheses `PgCoreMeas`, `PgMeas` and `PgGoodMeas` of `AdversarialBco/Poly/PgProc.lean`
(theorems `pgCoreMeas`, `pgMeas`, `pgGoodMeas`).

Every step of `pgCore` is proved measurable for a body that depends on a parameter: `K : X → Set E` whose graph
`{(x, y) | y ∈ K x}` is measurable in `X × E`. The gauge by bisection asks `s⁻¹ • y ∈ K x` at a measurable `s`
(`piTilde_family_measurable`); the estimate `pgV` is a continuous function of the gauge value, the inverse matrix and
the sample, and the inverse `M⁻¹ = (det M)⁻¹ • adj M` is measurable (`pgV_family_measurable`); the verdict is a closed
condition on measurable averages and the amplified test counts measurable verdicts (`verdict_generic_measurableSet`,
`count_generic_measurableSet`); the descent iterates a continuous projection (`pgProj_continuous`: the metric
projection onto the closed convex domain, or the identity when the domain is empty). The first accepted repeat goes
through `Measurable.find` (`measurable_dite_find`). For `PgCoreMeas` the parameter is the position `P` and the body
`posBody K' (pgMu P) (pgOp P)`, whose graph is closed when `K'` is (`posBody_family_measurableSet`); `PgMeas` follows
stage by stage (`pgStage_meas`). For `PgGoodMeas`, the gauge of a convex body containing `B̄(0, 1)` is an infimum over
rational scales (`gauge_eq_iInf_rat`), jointly measurable in the position and the point, so the mean width is
measurable in the position; the outer radius condition is a countable intersection over a dense subset of the body
(`posBody_subset_ball_measurableSet`).

Elaboration note: matching a measurability statement against the concrete `pgVerdict`, `pgTest` or `pgDescent` by
unification unfolds them and times out; the statements are proved for abstract functions and transported with
`convert` and `simp only`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AdversarialBco.Poly

namespace PgMeas

/-! ## Continuity of the coordinates and of the composition -/

theorem pgPack_continuous (d : ℕ) :
    Continuous (fun p : EuclideanSpace ℝ (Fin d) × Matrix (Fin d) (Fin d) ℝ => pgPack p.1 p.2) := by
  unfold pgPack
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
  rintro (i | ⟨i, j⟩)
  · exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
  · exact (continuous_snd.matrix_elem i j)

theorem pgComp_continuous (d : ℕ) : Continuous (fun p : PgSp d × PgSp d => pgComp p.1 p.2) := by
  unfold pgComp
  refine (pgPack_continuous d).comp (Continuous.prodMk ?_ ?_)
  · exact (pg_continuous d).2.2.comp (continuous_fst.prodMk ((pg_continuous d).1.comp continuous_snd))
  · exact ((pg_continuous d).2.1.comp continuous_fst).matrix_mul ((pg_continuous d).2.1.comp continuous_snd)

theorem pgOut_continuous (d : ℕ) : Continuous (fun x : PgSp d => pgOut x) :=
  (pgPack_continuous d).comp ((pg_continuous d).1.prodMk ((pg_continuous d).2.1.const_smul pgA))

/-! ## The projection -/

theorem pgProj_continuous (d : ℕ) (ρ : ℝ) : Continuous (pgProj d ρ) := by
  by_cases hne : (pgDom d ρ).Nonempty
  · exact (pgProj_spec d ρ hne (pgDom_isCompact d ρ).isClosed (pgDom_convex d ρ)).2.2.continuous
  · have h : pgProj d ρ = id := by
      funext y
      unfold pgProj
      split_ifs with h
      · obtain ⟨z, hz, -⟩ := h
        exact absurd ⟨z, hz⟩ hne
      · rfl
    rw [h]
    exact continuous_id

/-! ## Bodies depending measurably on a parameter -/

theorem piTilde_family_measurable {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (hK : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ K p.1}) (ρ : ℝ) (j : ℕ) :
    Measurable (fun p : X × EuclideanSpace ℝ (Fin d) => piTilde (K p.1) ρ j p.2) := by
  classical
  have hI : ∀ j, Measurable (fun p : X × EuclideanSpace ℝ (Fin d) =>
      bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j) := by
    intro j
    induction j with
    | zero =>
      simp only [bisect]
      exact ((measurable_norm.comp measurable_snd).div_const ρ).prodMk (measurable_norm.comp measurable_snd)
    | succ j ih =>
      simp only [bisect]
      have hm : Measurable (fun p : X × EuclideanSpace ℝ (Fin d) =>
          ((bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).1 +
            (bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).2) / 2) :=
        (ih.fst.add ih.snd).div_const 2
      have hS : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) |
          0 < ((bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).1 +
            (bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).2) / 2 ∧
          (((bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).1 +
            (bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).2) / 2)⁻¹ • p.2 ∈ K p.1} := by
        refine (measurableSet_lt measurable_const hm).inter ?_
        exact hK.preimage (f := fun p : X × EuclideanSpace ℝ (Fin d) => (p.1,
          (((bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).1 +
            (bisect (fun s => 0 < s ∧ s⁻¹ • p.2 ∈ K p.1) (‖p.2‖ / ρ) ‖p.2‖ j).2) / 2)⁻¹ • p.2))
          (measurable_fst.prodMk (hm.inv.smul measurable_snd))
      exact Measurable.ite hS (ih.fst.prodMk hm) (hm.prodMk ih.snd)
  unfold piTilde
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const (hI j).snd

theorem posBody_family_measurableSet {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    MeasurableSet {p : PgSp d × EuclideanSpace ℝ (Fin d) | p.2 ∈ posBody K (pgMu p.1) (pgOp p.1)} :=
  (hK.preimage (pg_continuous d).2.2).measurableSet

theorem pgFt_family_measurable {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (hK : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ K p.1}) (ρ : ℝ) :
    Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgFt (K q.1) ρ q.2.1 q.2.2) :=
  (piTilde_family_measurable K hK ρ (pgJb d ρ)).comp
    (measurable_fst.prodMk ((pg_continuous d).2.2.measurable.comp measurable_snd))

/-- `M ↦ M⁻¹ = (det M)⁻¹ • adj M` is measurable. -/
theorem matrix_inv_measurable (d : ℕ) : Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) := by
  have h : (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul ((continuous_id.matrix_adjugate.matrix_elem i j).measurable)

/-- `pgV` is a continuous function of the gauge value `f`, the inverse matrix `Mi` and the sample `g`. -/
theorem pgVOf_continuous (d : ℕ) :
    Continuous (fun p : ℝ × Matrix (Fin d) (Fin d) ℝ × EuclideanSpace ℝ (Fin d) =>
      pgPack (WithLp.toLp 2 (p.1 • (p.2.1 *ᵥ fun i => p.2.2 i)))
        ((p.1 / 2) • (p.2.1 * pgGG p.2.2 + (p.2.1 * pgGG p.2.2)ᵀ) - (pgKappa / d) • p.2.1)) := by
  have hg : Continuous (fun p : ℝ × Matrix (Fin d) (Fin d) ℝ × EuclideanSpace ℝ (Fin d) => fun i => p.2.2 i) :=
    (PiLp.continuous_ofLp 2 _).comp (continuous_snd.comp continuous_snd)
  have hM : Continuous (fun p : ℝ × Matrix (Fin d) (Fin d) ℝ × EuclideanSpace ℝ (Fin d) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hG : Continuous (fun p : ℝ × Matrix (Fin d) (Fin d) ℝ × EuclideanSpace ℝ (Fin d) => pgGG p.2.2) := by
    unfold pgGG
    exact (hg.matrix_vecMulVec hg).sub continuous_const
  have hMG := hM.matrix_mul hG
  refine (pgPack_continuous d).comp (Continuous.prodMk ?_ ?_)
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_fst.smul (hM.matrix_mulVec hg))
  · exact ((continuous_fst.div_const 2).smul (hMG.add hMG.matrix_transpose)).sub
      (hM.const_smul (pgKappa / (d : ℝ)))

theorem pgV_family_measurable {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hFt : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgFt (K q.1) ρ q.2.1 q.2.2)) :
    Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgV (K q.1) ρ q.2.1 q.2.2) := by
  have hMi : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => (pgMat q.2.1)⁻¹) :=
    (matrix_inv_measurable d).comp ((pg_continuous d).2.1.measurable.comp (measurable_fst.comp measurable_snd))
  exact (pgVOf_continuous d).measurable.comp (hFt.prodMk (hMi.prodMk (measurable_snd.comp measurable_snd)))

theorem quadForm_isClosed (d : ℕ) (c : ℝ) :
    IsClosed {Q : Matrix (Fin d) (Fin d) ℝ | ∀ v : Fin d → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Q *ᵥ v)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

/-- The acceptance set of a basic verdict, for measurable gauge values `F i` and samples `w i`. -/
theorem verdict_generic_measurableSet {α : Type*} [MeasurableSpace α] {d : ℕ} (F : ℕ → α → ℝ)
    (hF : ∀ i, Measurable (F i)) (w : ℕ → α → EuclideanSpace ℝ (Fin d)) (hw : ∀ i, Measurable (w i)) (n : ℕ)
    (c1 c2 c3 : ℝ) :
    MeasurableSet {a | (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F i a ≤ c1 ∧
      ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • w i a‖ ≤ c2 ∧
      ∀ v : Fin d → ℝ, c3 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • pgGG (w i a)) *ᵥ v)} := by
  have hk : Measurable (fun a => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F i a) :=
    (Finset.measurable_sum _ fun i _ => hF i).const_mul ((n : ℝ)⁻¹)
  have h1 : ∀ i, Measurable (fun a => F i a • w i a) := fun i => (hF i).smul (hw i)
  have h2 : Measurable (fun a => ∑ i ∈ Finset.range n, F i a • w i a) := Finset.measurable_sum _ fun i _ => h1 i
  have hb : Measurable (fun a => ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • w i a‖) :=
    (h2.const_smul ((n : ℝ)⁻¹)).norm
  have hQ : Measurable (fun a => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, F i a • pgGG (w i a)) := by
    refine Measurable.of_eval_matrix _ fun j k => ?_
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    refine (Finset.measurable_sum _ fun i _ => (hF i).mul ?_).const_mul ((n : ℝ)⁻¹)
    have hc : Continuous (fun g : EuclideanSpace ℝ (Fin d) => pgGG g j k) := by
      unfold pgGG
      exact ((((PiLp.continuous_ofLp 2 _).matrix_vecMulVec (PiLp.continuous_ofLp 2 _)).sub
        continuous_const).matrix_elem j k)
    exact hc.measurable.comp (hw i)
  exact (measurableSet_le hk measurable_const).inter ((measurableSet_le hb measurable_const).inter
    (hQ ((quadForm_isClosed d c3).measurableSet)))

theorem pgVerdict_family_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hFt : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgFt (K q.1) ρ q.2.1 q.2.2)) :
    MeasurableSet {q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict (K q.1) ρ q.2.1 q.2.2} := by
  have h := verdict_generic_measurableSet (fun i (q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d))) =>
      pgFt (K q.1) ρ q.2.1 (q.2.2 i))
    (fun i => hFt.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))))
    (fun i q => q.2.2 i) (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
    (pgNT d ρ) (1.075 * pgKappa) (3 / 4 * pgTaub d ρ) (5 / 8 * (pgKappa / d))
  convert h using 2 with q
  simp only [pgVerdict]

/-- More than `c` of the predicates `V 0, ..., V (m - 1)` hold at the point. -/
theorem count_generic_measurableSet {α : Type*} [MeasurableSpace α] (V : ℕ → α → Prop)
    (hV : ∀ i, MeasurableSet {a | V i a}) {inst : ∀ i a, Decidable (V i a)} (m : ℕ) (c : ℝ) :
    MeasurableSet {a | c < (((Finset.range m).filter fun i => V i a).card : ℝ)} := by
  have hs : Measurable (fun a => ∑ i ∈ Finset.range m, if V i a then (1 : ℝ) else 0) :=
    Finset.measurable_sum _ fun i _ => Measurable.ite (hV i) measurable_const measurable_const
  have heq : {a | c < (((Finset.range m).filter fun i => V i a).card : ℝ)} =
      {a | c < ∑ i ∈ Finset.range m, if V i a then (1 : ℝ) else 0} := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [heq]
  exact measurableSet_lt measurable_const hs

open Classical in
theorem pgTest_family_measurableSet {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ)
    (hVer : MeasurableSet {q : X × PgSp d × (ℕ → EuclideanSpace ℝ (Fin d)) | pgVerdict (K q.1) ρ q.2.1 q.2.2}) :
    MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTest (K q.1) ρ δ q.2.1 q.2.2} := by
  have hV : ∀ i, MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) |
      pgVerdict (K q.1) ρ q.2.1 (q.2.2 i)} := fun i => by
    have h' := hVer.preimage (f := fun q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) => (q.1, q.2.1, q.2.2 i))
      (by fun_prop)
    simpa only [Set.preimage_ofPred_eq] using h'
  have h := count_generic_measurableSet
    (fun i (q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d))) => pgVerdict (K q.1) ρ q.2.1 (q.2.2 i)) hV
    (inst := fun i q => Classical.dec _)
    (pgMT δ) ((pgMT δ : ℝ) / 2)
  convert h using 2 with q
  simp only [pgTest]

theorem sgdAvg_family_measurable {X E G : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace G] (proj : E → E)
    (hproj : Measurable proj) (V : X → E → G → E) (hV : Measurable (fun q : X × E × G => V q.1 q.2.1 q.2.2))
    (s : ℝ) (x1 : E) (N : ℕ) :
    Measurable (fun q : X × (ℕ → G) => sgdAvg proj (V q.1) s x1 N q.2) := by
  have hit : ∀ t, Measurable (fun q : X × (ℕ → G) => sgdIter proj (V q.1) s x1 q.2 t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have hV' : Measurable (fun q : X × (ℕ → G) => V q.1 (sgdIter proj (V q.1) s x1 q.2 t) (q.2 t)) :=
        hV.comp (measurable_fst.prodMk (ih.prodMk ((measurable_pi_apply t).comp measurable_snd)))
      exact hproj.comp (ih.sub (hV'.const_smul s))
  exact (Finset.measurable_sum _ fun t _ => hit t).const_smul ((N : ℝ)⁻¹)

theorem pgDescent_family_measurable {X : Type*} [MeasurableSpace X] {d : ℕ}
    (K : X → Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (hV : Measurable (fun q : X × PgSp d × EuclideanSpace ℝ (Fin d) => pgV (K q.1) ρ q.2.1 q.2.2)) :
    Measurable (fun q : X × (ℕ → EuclideanSpace ℝ (Fin d)) => pgDescent (K q.1) ρ q.2) :=
  sgdAvg_family_measurable (pgProj d ρ) (pgProj_continuous d ρ).measurable (fun x => pgV (K x) ρ) hV _ _ _

/-! ## Procedure PG-core -/

theorem measurable_comp_lam {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {g : β → γ} (hg : Measurable g) (f : α → β) (hf : Measurable f) : Measurable (fun x => g (f x)) :=
  hg.comp hf

/-- The first index `r < J` at which `P r x` holds, read through a measurable family `f`, is measurable; for any
decidability instances. -/
theorem measurable_dite_find {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (J : ℕ) (P : ℕ → α → Prop)
    (hP : ∀ r, MeasurableSet {x | P r x}) {i1 : ∀ x, DecidablePred fun r => r < J ∧ P r x}
    {i2 : ∀ x, Decidable (∃ r < J, P r x)} (f : ℕ → α → β) (hf : ∀ r, Measurable (f r)) (b : β) :
    Measurable (fun x => @dite β (∃ r < J, P r x) (i2 x) (fun h => f (@Nat.find _ (i1 x) h) x) (fun _ => b)) := by
  classical
  let p : ℕ → α → Prop := fun n x => n = J ∨ (n < J ∧ P n x)
  have hp : ∀ x, ∃ n, p n x := fun x => ⟨J, Or.inl rfl⟩
  let g : ℕ → α → β := fun n x => if n < J then f n x else b
  have hg : ∀ n, Measurable (g n) := by
    intro n
    by_cases hn : n < J
    · simp only [g, hn, ite_true]
      exact hf n
    · simp only [g, hn, ite_false]
      exact measurable_const
  have hpm : ∀ n, MeasurableSet {x | p n x} := fun n =>
    (MeasurableSet.const (n = J)).union ((MeasurableSet.const (n < J)).inter (hP n))
  have key := Measurable.find hg hpm hp
  convert key using 1
  funext x
  split_ifs with h
  · have hJ : Nat.find h < J := (Nat.find_spec h).1
    have h1 : Nat.find (hp x) = Nat.find h := by
      apply le_antisymm
      · exact Nat.find_min' (hp x) (Or.inr (Nat.find_spec h))
      · apply Nat.find_min' h
        have hle : Nat.find (hp x) ≤ Nat.find h := Nat.find_min' (hp x) (Or.inr (Nat.find_spec h))
        rcases Nat.find_spec (hp x) with heq | ⟨hlt, hmem⟩
        · omega
        · exact ⟨hlt, hmem⟩
    simp only [g, h1, hJ, ite_true]
  · have h1 : Nat.find (hp x) = J := by
      apply le_antisymm
      · exact Nat.find_min' (hp x) (Or.inl rfl)
      · by_contra hc
        rw [not_le] at hc
        rcases Nat.find_spec (hp x) with heq | ⟨hlt, hmem⟩
        · omega
        · exact h ⟨_, hlt, hmem⟩
    simp only [g, h1, lt_irrefl, ite_false]

theorem pgCore_family_meas {X : Type*} [MeasurableSpace X] {d : ℕ} (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (ρ δ : ℝ)
    (hTest : MeasurableSet {q : X × PgSp d × (ℕ → ℕ → EuclideanSpace ℝ (Fin d)) | pgTest (K q.1) ρ δ q.2.1 q.2.2})
    (hDesc : Measurable (fun q : X × (ℕ → EuclideanSpace ℝ (Fin d)) => pgDescent (K q.1) ρ q.2)) :
    MeasurableSet {q : X × (ℕ → PgRound d) | (pgCore d (K q.1) ρ δ q.2).isSome} ∧
      Measurable (fun q : X × (ℕ → PgRound d) => (pgCore d (K q.1) ρ δ q.2).getD 0) := by
  have hD : ∀ r, Measurable (fun q : X × (ℕ → PgRound d) => pgDescent (K q.1) ρ (q.2 r).1) := fun r =>
    measurable_comp_lam hDesc (fun q : X × (ℕ → PgRound d) => (q.1, (q.2 r).1)) (by fun_prop)
  have hA : ∀ r, MeasurableSet {q : X × (ℕ → PgRound d) |
      pgTest (K q.1) ρ δ (pgDescent (K q.1) ρ (q.2 r).1) (q.2 r).2} := fun r => by
    have h' := hTest.preimage (f := fun q : X × (ℕ → PgRound d) => (q.1, pgDescent (K q.1) ρ (q.2 r).1, (q.2 r).2))
      (measurable_fst.prodMk ((hD r).prodMk (by fun_prop)))
    simpa only [Set.preimage_ofPred_eq] using h'
  constructor
  · have hset : {q : X × (ℕ → PgRound d) | (pgCore d (K q.1) ρ δ q.2).isSome} =
        ⋃ r ∈ Finset.range (pgJr δ),
          {q : X × (ℕ → PgRound d) | pgTest (K q.1) ρ δ (pgDescent (K q.1) ρ (q.2 r).1) (q.2 r).2} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
      unfold pgCore
      split_ifs with h
      · simpa using h
      · simpa using h
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun r _ => hA r
  · simp only [pgCore, apply_dite (fun o : Option (PgSp d) => o.getD 0), Option.getD_some, Option.getD_none]
    exact measurable_dite_find (pgJr δ)
      (fun r (q : X × (ℕ → PgRound d)) => pgTest (K q.1) ρ δ (pgDescent (K q.1) ρ (q.2 r).1) (q.2 r).2) hA
      (fun r q => pgOut (pgDescent (K q.1) ρ (q.2 r).1)) (fun r => (pgOut_continuous d).measurable.comp (hD r)) 0

theorem pgCore_family {X : Type*} [MeasurableSpace X] {d : ℕ} (K : X → Set (EuclideanSpace ℝ (Fin d)))
    (hK : MeasurableSet {p : X × EuclideanSpace ℝ (Fin d) | p.2 ∈ K p.1}) (ρ δ : ℝ) :
    MeasurableSet {q : X × (ℕ → PgRound d) | (pgCore d (K q.1) ρ δ q.2).isSome} ∧
      Measurable (fun q : X × (ℕ → PgRound d) => (pgCore d (K q.1) ρ δ q.2).getD 0) := by
  have hFt := pgFt_family_measurable K hK ρ
  exact pgCore_family_meas K ρ δ
    (pgTest_family_measurableSet K ρ δ (pgVerdict_family_measurableSet K ρ hFt))
    (pgDescent_family_measurable K ρ (pgV_family_measurable K ρ hFt))

theorem pgCoreMeas : PgCoreMeas := fun d K' ρ δ hK' =>
  pgCore_family (fun P : PgSp d => posBody K' (pgMu P) (pgOp P)) (posBody_family_measurableSet K' hK') ρ δ

/-! ## Procedure PG -/

theorem option_bind_map_isSome {α : Type*} [Zero α] (o : Option α) (c : α → Option α) (g : α → α → α) :
    (o.bind fun P => (c P).map (g P)).isSome = (o.isSome && (c (o.getD 0)).isSome) := by
  cases o <;> simp

theorem option_bind_map_getD {α : Type*} [Zero α] (o : Option α) (c : α → Option α) (g : α → α → α) :
    (o.bind fun P => (c P).map (g P)).getD 0 =
      if (o.bind fun P => (c P).map (g P)).isSome then g (o.getD 0) ((c (o.getD 0)).getD 0) else 0 := by
  cases o with
  | none => simp
  | some P => cases h : c P <;> simp [h]

theorem pgStage_meas (hC : PgCoreMeas) (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K)
    (r0 δ' : ℝ) (i : ℕ) :
    MeasurableSet {ω : ℕ → ℕ → PgRound d | (pgStage d K r0 δ' ω i).isSome} ∧
      Measurable fun ω : ℕ → ℕ → PgRound d => (pgStage d K r0 δ' ω i).getD 0 := by
  induction i with
  | zero =>
    simp only [pgStage, Option.isSome_some]
    exact ⟨MeasurableSet.univ, measurable_const⟩
  | succ i ih =>
    obtain ⟨hS, hP⟩ := ih
    have hKi : IsClosed (K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 ^ (i + 1) * r0)) :=
      hK.inter Metric.isClosed_closedBall
    obtain ⟨hC1, hC2⟩ := hC d _ (pgRhoStage d i) δ' hKi
    have hφ : Measurable (fun ω : ℕ → ℕ → PgRound d => ((pgStage d K r0 δ' ω i).getD 0, ω i)) :=
      hP.prodMk (measurable_pi_apply i)
    have hstep : ∀ ω : ℕ → ℕ → PgRound d, pgStage d K r0 δ' ω (i + 1) = (pgStage d K r0 δ' ω i).bind fun P =>
        (pgCore d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0)) (pgMu P) (pgOp P)) (pgRhoStage d i) δ'
          (ω i)).map (pgComp P) := fun ω => rfl
    have hset : {ω : ℕ → ℕ → PgRound d | (pgStage d K r0 δ' ω (i + 1)).isSome} =
        {ω | (pgStage d K r0 δ' ω i).isSome} ∩
          (fun ω : ℕ → ℕ → PgRound d => ((pgStage d K r0 δ' ω i).getD 0, ω i)) ⁻¹'
            {p : PgSp d × (ℕ → PgRound d) | (pgCore d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0))
              (pgMu p.1) (pgOp p.1)) (pgRhoStage d i) δ' p.2).isSome} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hstep, option_bind_map_isSome,
        Bool.and_eq_true]
    have hmeas : MeasurableSet {ω : ℕ → ℕ → PgRound d | (pgStage d K r0 δ' ω (i + 1)).isSome} :=
      hset ▸ hS.inter (hC1.preimage hφ)
    refine ⟨hmeas, ?_⟩
    have hfun : (fun ω : ℕ → ℕ → PgRound d => (pgStage d K r0 δ' ω (i + 1)).getD 0) =
        fun ω => if (pgStage d K r0 δ' ω (i + 1)).isSome then
          pgComp ((pgStage d K r0 δ' ω i).getD 0)
            ((pgCore d (posBody (K ∩ Metric.closedBall 0 (2 ^ (i + 1) * r0))
              (pgMu ((pgStage d K r0 δ' ω i).getD 0)) (pgOp ((pgStage d K r0 δ' ω i).getD 0)))
              (pgRhoStage d i) δ' (ω i)).getD 0) else 0 := by
      funext ω
      rw [hstep]
      exact option_bind_map_getD _ _ _
    rw [hfun]
    exact Measurable.ite hmeas ((pgComp_continuous d).measurable.comp (hP.prodMk (hC2.comp hφ))) measurable_const

theorem pgMeas : PgMeas := fun d K r0 R0 δ hK =>
  pgStage_meas pgCoreMeas d K hK r0 (δ / pgStages r0 R0) (pgStages r0 R0)

/-! ## The event `PgGood` -/

open Classical in
theorem gauge_eq_iInf_rat {d : ℕ} (s : Set (EuclideanSpace ℝ (Fin d))) (hs : Convex ℝ s)
    (h1 : Metric.closedBall 0 1 ⊆ s) (x : EuclideanSpace ℝ (Fin d)) :
    gauge s x = ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖ := by
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ s := h1 (Metric.mem_closedBall_self zero_le_one)
  have habsB : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (absorbent_ball_zero zero_lt_one).mono Metric.ball_subset_closedBall
  have habs : Absorbent ℝ s := habsB.mono h1
  have hgx : gauge s x ≤ ‖x‖ := by
    calc gauge s x ≤ gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x := gauge_mono habsB h1 x
      _ = ‖x‖ := by rw [gauge_closedBall zero_le_one, div_one]
  have hfge : ∀ q : ℚ, gauge s x ≤ if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖ := by
    intro q
    split_ifs with h
    · have hq : (0 : ℝ) < q := by exact_mod_cast h.1
      apply gauge_le_of_mem hq.le
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hq.ne' s x]
      exact h.2
    · exact hgx
  have hbdd : BddBelow (Set.range fun q : ℚ => if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact (gauge_nonneg x).trans (hfge q)⟩
  apply le_antisymm (le_ciInf hfge)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (gauge s x) hε)
  have hqpos : (0 : ℝ) < q := (gauge_nonneg x).trans_lt hq1
  have hmem : (q : ℝ)⁻¹ • x ∈ s := by
    apply setOfPred_gauge_lt_one_subset_self hs h0 habs
    show gauge s ((q : ℝ)⁻¹ • x) < 1
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hqpos.le), smul_eq_mul, inv_mul_lt_iff₀ hqpos, mul_one]
    exact hq1
  calc (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖)
      ≤ (if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ s then (q : ℝ) else ‖x‖) := ciInf_le hbdd q
    _ = q := by
      split_ifs with h
      · rfl
      · exact absurd ⟨by exact_mod_cast hqpos, hmem⟩ h
    _ < gauge s x + ε := hq2

open Classical in
theorem gaugeRat_family_measurable {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    Measurable (fun p : PgSp d × EuclideanSpace ℝ (Fin d) =>
      ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • p.2 ∈ posBody K (pgMu p.1) (pgOp p.1) then (q : ℝ) else ‖p.2‖) := by
  refine Measurable.iInf fun q => ?_
  have hS : MeasurableSet {p : PgSp d × EuclideanSpace ℝ (Fin d) |
      0 < q ∧ (q : ℝ)⁻¹ • p.2 ∈ posBody K (pgMu p.1) (pgOp p.1)} :=
    (MeasurableSet.const (0 < q)).inter ((posBody_family_measurableSet K hK).preimage
      (f := fun p : PgSp d × EuclideanSpace ℝ (Fin d) => (p.1, (q : ℝ)⁻¹ • p.2))
      (measurable_fst.prodMk (measurable_snd.const_smul ((q : ℝ)⁻¹))))
  exact Measurable.ite hS measurable_const (measurable_norm.comp measurable_snd)

theorem posBody_subset_ball_measurableSet {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) :
    MeasurableSet {Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} := by
  obtain ⟨D, hDK, hDc, hKD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hT : ∀ k : EuclideanSpace ℝ (Fin d), Measurable (fun Q : PgSp d =>
      ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖) := by
    intro k
    have h1 : Measurable (fun Q : PgSp d => (pgMat Q)⁻¹) :=
      (matrix_inv_measurable d).comp (pg_continuous d).2.1.measurable
    have h2 : Measurable (fun Q : PgSp d => WithLp.ofLp (k - pgMu Q)) :=
      ((PiLp.continuous_ofLp 2 _).comp (continuous_const.sub (pg_continuous d).1)).measurable
    have hc : Continuous (fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => ‖WithLp.toLp 2 (p.1 *ᵥ p.2)‖) :=
      ((PiLp.continuous_toLp 2 _).comp (continuous_fst.matrix_mulVec continuous_snd)).norm
    exact measurable_comp_lam hc.measurable (fun Q : PgSp d => ((pgMat Q)⁻¹, WithLp.ofLp (k - pgMu Q))) (h1.prodMk h2)
  have hop : ∀ (Q : PgSp d) (v : EuclideanSpace ℝ (Fin d)),
      pgOp Q v = WithLp.toLp 2 (pgMat Q *ᵥ WithLp.ofLp v) := fun Q v => by
    rw [pgOp, ← Matrix.toEuclideanCLM_toLp]
  have heq : {Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} =
      {Q : PgSp d | (pgMat Q).det ≠ 0} ∩
        ⋂ k ∈ D, {Q | ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖ ≤ R} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hdet, hsub⟩
      refine ⟨hdet, fun k hk => ?_⟩
      have hmem : WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q)) ∈ posBody K (pgMu Q) (pgOp Q) := by
        show pgMu Q + pgOp Q _ ∈ K
        rw [hop, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.one_mulVec, WithLp.toLp_ofLp, add_sub_cancel]
        exact hDK hk
      simpa using hsub hmem
    · rintro ⟨hdet, hD⟩
      refine ⟨hdet, fun y hy => ?_⟩
      have hk0 : pgMu Q + pgOp Q y ∈ closure D := hKD hy
      have hclosed : IsClosed {k : EuclideanSpace ℝ (Fin d) |
          ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp (k - pgMu Q))‖ ≤ R} :=
        isClosed_le (((PiLp.continuous_toLp 2 _).comp (continuous_const.matrix_mulVec
          ((PiLp.continuous_ofLp 2 _).comp (continuous_id.sub continuous_const)))).norm) continuous_const
      have h3 : ‖WithLp.toLp 2 ((pgMat Q)⁻¹ *ᵥ WithLp.ofLp ((pgMu Q + pgOp Q y) - pgMu Q))‖ ≤ R :=
        closure_minimal (fun k hk => hD k hk) hclosed hk0
      rw [add_sub_cancel_left, hop, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec, WithLp.toLp_ofLp] at h3
      rw [mem_closedBall_zero_iff]
      exact h3
  rw [heq]
  exact (isOpen_ne_fun (pg_continuous d).2.1.matrix_det continuous_const).measurableSet.inter
    (MeasurableSet.biInter hDc fun k _ => measurableSet_le (hT k) measurable_const)

theorem ball_subset_posBody_isClosed {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K) :
    IsClosed {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} := by
  have h_cont : Continuous (fun (x : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMu x.1 + pgOp x.1 x.2) :=
    (pg_continuous d).2.2
  have h_cont_fixed (y : EuclideanSpace ℝ (Fin d)) : Continuous (fun (Q : PgSp d) => pgMu Q + pgOp Q y) := by
    refine h_cont.comp (Continuous.prodMk ?_ continuous_const)
    exact continuous_id
  have h_eq : {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} =
      ⋂ y ∈ Metric.closedBall 0 1, {Q : PgSp d | pgMu Q + pgOp Q y ∈ K} := by
    ext Q; simp [Set.subset_def, posBody]
  rw [h_eq]
  refine isClosed_biInter (fun y hy => ?_)
  rw [← Set.preimage_ofPred_eq]
  exact hK.preimage (h_cont_fixed y)

theorem posBody_convex {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K) (μ : EuclideanSpace ℝ (Fin d))
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Convex ℝ (posBody K μ A) := by
  intro x hx y hy a b ha hb hab
  show μ + A (a • x + b • y) ∈ K
  have h : μ + A (a • x + b • y) = a • (μ + A x) + b • (μ + A y) := by
    rw [map_add, map_smul, map_smul, smul_add, smul_add]
    have hμ : μ = a • μ + b • μ := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hμ]
    abel
  rw [h]
  exact hK hx hy ha hb hab

theorem pgGood_measurableSet (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (hcv : Convex ℝ K)
    (hK : IsClosed K) : MeasurableSet {Q : PgSp d | PgGood d K R (some Q)} := by
  classical
  have hGm := gaugeRat_family_measurable K hK
  have hI : Measurable (fun Q : PgSp d => ∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
      then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
    (hGm.stronglyMeasurable.integral_prod_right').measurable
  have hA : MeasurableSet {Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} :=
    (ball_subset_posBody_isClosed K hK).measurableSet
  have hdet : MeasurableSet {Q : PgSp d | (pgMat Q).det ≠ 0} :=
    (isOpen_ne_fun ((pg_continuous d).2.1.matrix_det) continuous_const).measurableSet
  have hB := posBody_subset_ball_measurableSet K R
  have hW : MeasurableSet {Q : PgSp d | (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
      then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
        (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ 1.27 * Real.sqrt (d + 1) / d} :=
    measurableSet_le (hI.div_const _) measurable_const
  have hmw : ∀ Q : PgSp d, Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q) →
      pgMw (posBody K (pgMu Q) (pgOp Q)) = (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
        then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
          (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    intro Q hQ
    unfold pgMw
    congr 2
    funext g
    exact gauge_eq_iInf_rat _ (posBody_convex K hcv _ _) hQ g
  have heq : {Q : PgSp d | PgGood d K R (some Q)} =
      {Q : PgSp d | (pgMat Q).det ≠ 0} ∩ ({Q : PgSp d | Metric.closedBall 0 1 ⊆ posBody K (pgMu Q) (pgOp Q)} ∩
        ({Q : PgSp d | (pgMat Q).det ≠ 0 ∧ posBody K (pgMu Q) (pgOp Q) ⊆ Metric.closedBall 0 R} ∩
          {Q : PgSp d | (∫ g, (⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • g ∈ posBody K (pgMu Q) (pgOp Q)
            then (q : ℝ) else ‖g‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) /
              (∫ g, ‖g‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) ≤ 1.27 * Real.sqrt (d + 1) / d})) := by
    ext Q
    simp only [PgGood, Option.some.injEq, exists_eq_left', Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, ⟨h1, h3⟩, hmw Q h2 ▸ h4⟩
    · rintro ⟨h1, h2, ⟨-, h3⟩, h4⟩
      exact ⟨h1, h2, h3, (hmw Q h2).symm ▸ h4⟩
  rw [heq]
  exact hdet.inter (hA.inter (hB.inter hW))

theorem pgGoodMeas : PgGoodMeas := fun d K R hcv hK => pgGood_measurableSet d K R hcv hK

end PgMeas

end AdversarialBco.Poly
