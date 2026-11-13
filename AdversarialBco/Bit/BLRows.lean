/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# The rows lemma of BL for BL's rational rows

The rows lemma of BL in the rational form of Bit/BLPure.lean: the kept rows `α̃_i = A_Sᵀ a_i`,
`β̃_i = b_i - a_i·μ_S` (`a_i ≠ 0`) describe the positioned body `K~ = {y | μ_S + A_S y ∈ K}` once `μ_S ∈ K`
(`rows_iff`); on a good position every `β̃_i` is positive (`beta_pos_of_good`); and then BL's gauge `gaugeQ` is the
gauge of P°'s body `kTh` (`gaugeQ_eq_of_good`). These are the three hypotheses of `RoundC` that read the rows.
-/

namespace AdversarialBco.Bit.BLP

open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Bit.Asm
open Matrix
open scoped Pointwise

variable {d : ℕ}

/-! ## The gauge of a finite system of rows -/

/-- The fold of `gaugeQ`: `0 ≤ G`, every term is at most `G`, and `G` is `0` or a term. -/
theorem foldl_max_spec {m : ℕ} (f : Fin m → ℚ) :
    let G := (List.ofFn f).foldl max 0
    0 ≤ G ∧ (∀ i, f i ≤ G) ∧ (G = 0 ∨ ∃ i, G = f i) := by
  intro G
  have key : ∀ (l : List ℚ) (a : ℚ), 0 ≤ a →
      0 ≤ l.foldl max a ∧ a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧
        (l.foldl max a = a ∨ l.foldl max a ∈ l) := by
    intro l
    induction l with
    | nil => intro a ha; simp [ha]
    | cons x l ih =>
      intro a ha
      obtain ⟨h0, h1, h2, h3⟩ := ih (max a x) (le_trans ha (le_max_left _ _))
      refine ⟨h0, le_trans (le_max_left _ _) h1, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_trans (le_max_right _ _) h1
        · exact h2 y hy
      · simp only [List.foldl_cons]
        rcases h3 with h3 | h3
        · rw [h3]
          rcases max_choice a x with h | h
          · left; exact h
          · right; rw [h]; exact List.mem_cons_self
        · right; exact List.mem_cons_of_mem _ h3
  obtain ⟨h0, -, h2, h3⟩ := key (List.ofFn f) 0 le_rfl
  refine ⟨h0, fun i => h2 _ ((List.mem_ofFn' f (f i)).mpr ⟨i, rfl⟩), ?_⟩
  rcases h3 with h3 | h3
  · left; exact h3
  · right
    obtain ⟨i, hi⟩ := (List.mem_ofFn' f _).mp h3
    exact ⟨i, hi.symm⟩

/-- The gauge of `{y | α_i·y ≤ β_i for every i}` with every `β_i > 0`, at `x`: the least `G ≥ 0` with
`α_i·x ≤ G β_i` for every `i`, given here through any `G` that is `0` or a ratio `α_i·x/β_i` and bounds them all. -/
theorem gauge_rows {m : ℕ} (α : Fin m → Fin d → ℝ) (β : Fin m → ℝ) (hβ : ∀ i, 0 < β i) (x : Fin d → ℝ) (G : ℝ)
    (hG0 : 0 ≤ G) (hGi : ∀ i, α i ⬝ᵥ x / β i ≤ G) (hGe : G = 0 ∨ ∃ i, G = α i ⬝ᵥ x / β i) :
    gauge {y : E d | ∀ i, α i ⬝ᵥ (WithLp.ofLp y) ≤ β i} (WithLp.toLp 2 x) = G := by
  set s : Set (E d) := {y : E d | ∀ i, α i ⬝ᵥ (WithLp.ofLp y) ≤ β i}
  have hmem : ∀ r : ℝ, 0 < r → (WithLp.toLp 2 x ∈ r • s ↔ ∀ i, α i ⬝ᵥ x / β i ≤ r) := by
    intro r hr
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    simp only [s, Set.mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    rw [div_le_iff₀ (hβ i)]
    have : WithLp.ofLp (r⁻¹ • WithLp.toLp 2 x) = r⁻¹ • x := rfl
    rw [this, dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hr, mul_comm]
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun e he => ?_
    have hr0 : 0 < G + e := by linarith
    exact gauge_le_of_mem hr0.le ((hmem _ hr0).mpr fun i => by linarith [hGi i])
  · rcases hGe with h | ⟨i, h⟩
    · rw [h]; exact gauge_nonneg _
    · rw [gauge_def]
      have hG1 : (0 : ℝ) < G + 1 := by linarith
      refine le_csInf ⟨G + 1, hG1, (hmem _ hG1).mpr fun j => (hGi j).trans (by linarith)⟩ ?_
      rintro r ⟨hr, hrx⟩
      rw [h]
      exact (hmem r hr).mp hrx i

/-! ## The kept rows describe the positioned body -/

/-- Row `i` of `K` at the positioned point `μ_S + A_S y`: `a_i·μ_S + (A_Sᵀ a_i)·y`. -/
theorem row_pos {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (y : Fin d → ℝ) (i : Fin m) :
    ∑ j, (A i j : ℝ) * (pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) (WithLp.toLp 2 y)) j =
      ((A i ⬝ᵥ S.1 : ℚ) : ℝ) + cV (S.2ᵀ *ᵥ A i) ⬝ᵥ y := by
  rw [pgOp_apply, pgMu_pgPack, pgMat_pgPack]
  simp only [PiLp.add_apply, toE, cV, cM, dotProduct, mulVec, transpose_apply, Matrix.map_apply, Rat.cast_sum,
    Rat.cast_mul]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The rows lemma of BL (a): once `μ_S ∈ K`, the kept rows `α̃_i·y ≤ β̃_i` describe `{y | μ_S + A_S y ∈ K}`. -/
theorem rows_iff (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (hS : toE S.1 ∈ polytope A b) (y : Fin d → ℝ) :
    (∀ i, cV ((mkCfg d n m A b c S).α i) ⬝ᵥ y ≤ (mkCfg d n m A b c S).β i) ↔
      pgMu (pgPack (toE S.1) (cM S.2)) + pgOp (pgPack (toE S.1) (cM S.2)) (WithLp.toLp 2 y) ∈ polytope A b := by
  have h0 : ∀ i, ((A i ⬝ᵥ S.1 : ℚ) : ℝ) ≤ b i := by
    intro i
    have := hS i
    simpa [toE, dotProduct] using this
  simp only [polytope, Set.mem_ofPred_eq, row_pos]
  constructor
  · intro h i
    by_cases hi : A i = 0
    · have : S.2ᵀ *ᵥ A i = 0 := by rw [hi, mulVec_zero]
      have hz : cV (0 : Fin d → ℚ) ⬝ᵥ y = 0 := by unfold cV; simp [dotProduct]
      rw [this, hz, add_zero]
      exact h0 i
    · have hmem : i ∈ keptIdx A := List.mem_filter.mpr ⟨List.mem_finRange i, by simpa using hi⟩
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
      have := h k
      simp only [mkCfg, hk, Rat.cast_sub] at this
      linarith
  · intro h k
    have := h ((keptIdx A).get k)
    simp only [mkCfg, Rat.cast_sub]
    linarith

/-- On a good position the centre `μ_S` lies in `K`. -/
theorem mu_mem_of_good {m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {Rr : ℝ}
    (hg : PgGood d (polytope A b) Rr (some (pgPack (toE S.1) (cM S.2)))) : toE S.1 ∈ polytope A b := by
  obtain ⟨P, hP, -, hball, -, -⟩ := hg
  cases Option.some_inj.mp hP
  have := hball (Metric.mem_closedBall_self zero_le_one)
  simpa [posBody, pgMu_pgPack] using this

/-- The rows lemma of BL (b): on a good position every kept `β̃_i` is positive (`B̄(0, 1) ⊆ K~` and `A_S`
invertible). -/
theorem beta_pos_of_good (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) {Rr : ℝ}
    (hg : PgGood d (polytope A b) Rr (some (pgPack (toE S.1) (cM S.2)))) (k : Fin (mkCfg d n m A b c S).m) :
    0 < (mkCfg d n m A b c S).β k := by
  have hS := mu_mem_of_good hg
  obtain ⟨P, hP, hdet, hball, -, -⟩ := hg
  cases Option.some_inj.mp hP
  set v : Fin d → ℝ := cV ((mkCfg d n m A b c S).α k)
  have hv : v ≠ 0 := by
    intro hv0
    have hq : S.2ᵀ *ᵥ A ((keptIdx A).get k) = 0 := by
      funext j
      have := congrFun hv0 j
      simp only [v, cV, mkCfg, Pi.zero_apply, Rat.cast_eq_zero] at this
      exact this
    have hdetq : S.2ᵀ.det ≠ 0 := by
      rw [det_transpose]
      intro h0
      apply hdet
      rw [pgMat_pgPack, cM, show (S.2.map ((↑) : ℚ → ℝ)) = (Rat.castHom ℝ).mapMatrix S.2 from rfl, ← RingHom.map_det,
        h0, map_zero]
    have hA := Matrix.eq_zero_of_mulVec_eq_zero hdetq hq
    have hkept := (List.mem_filter.mp (List.get_mem (keptIdx A) k)).2
    simp only [decide_eq_true_eq] at hkept
    exact hkept hA
  set w : E d := WithLp.toLp 2 v
  have hw : 0 < ‖w‖ := norm_pos_iff.mpr (by simpa [w] using hv)
  have hdot : v ⬝ᵥ v = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [w, dotProduct, sq]
  set y : Fin d → ℝ := ‖w‖⁻¹ • v
  have hy : WithLp.toLp 2 y ∈ Metric.closedBall (0 : E d) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have : WithLp.toLp 2 y = ‖w‖⁻¹ • w := rfl
    rw [this, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw.ne']
  have hin := hball hy
  simp only [posBody, Set.mem_ofPred_eq] at hin
  have hrow := ((rows_iff n m A b c S hS y).mpr hin) k
  have hval : v ⬝ᵥ y = ‖w‖ := by
    rw [dotProduct_smul, hdot, smul_eq_mul]
    field_simp
  rw [hval] at hrow
  exact_mod_cast hw.trans_le hrow

/-- The cast of a rational dot product. -/
theorem cast_dot (v w : Fin d → ℚ) : ((v ⬝ᵥ w : ℚ) : ℝ) = cV v ⬝ᵥ cV w := by
  simp [dotProduct, cV]

/-- The rows lemma of BL (c): on a good position BL's gauge `gaugeQ` is the gauge of P°'s body `kTh` at BL's
position. -/
theorem gaugeQ_eq_of_good (n m : ℕ) (δ : ℝ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (hg : PgGood d (polytope A b) (df2oPar d n δ).R (some (pgPack (toE S.1) (cM S.2)))) (X : Fin d → ℚ) :
    (gaugeQ (mkCfg d n m A b c S) X : ℝ) =
      gauge (kTh n δ (polytope A b) (pgPack (toE S.1) (cM S.2))) (WithLp.toLp 2 (cV X)) := by
  have hS := mu_mem_of_good hg
  have hβ := beta_pos_of_good n m A b c S hg
  set cfg := mkCfg d n m A b c S
  have hK : kTh n δ (polytope A b) (pgPack (toE S.1) (cM S.2)) =
      {y : E d | ∀ i, cV (cfg.α i) ⬝ᵥ (WithLp.ofLp y) ≤ (cfg.β i : ℝ)} := by
    rw [kTh_good hg]
    obtain ⟨P, hP, -, -, hsub, -⟩ := hg
    cases Option.some_inj.mp hP
    ext y
    simp only [df2Kp, Set.mem_ofPred_eq]
    rw [rows_iff n m A b c S hS]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      have := hsub (show y ∈ posBody (polytope A b) _ _ from h)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
  rw [hK]
  obtain ⟨h0, hi, he⟩ := foldl_max_spec fun i => cfg.α i ⬝ᵥ X / cfg.β i
  refine (gauge_rows (fun i => cV (cfg.α i)) (fun i => (cfg.β i : ℝ)) (fun i => by exact_mod_cast hβ i) (cV X)
    _ (by exact_mod_cast h0) (fun i => ?_) ?_).symm
  · have := hi i
    rw [← cast_dot, ← Rat.cast_div]
    exact_mod_cast this
  · rcases he with h | ⟨i, h⟩
    · left; simp only [gaugeQ]; exact_mod_cast h
    · right
      refine ⟨i, ?_⟩
      rw [← cast_dot, ← Rat.cast_div]
      simp only [gaugeQ]
      exact_mod_cast h

/-! ## The three hypotheses of `RoundC` on BL's own configuration -/

/-- The three hypotheses of `RoundC` that read the rows, at BL's configuration `cfgOf` and position `posR`, from
`PgGood` at P°'s outer radius. -/
theorem rowsC (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (hg : PgGood d (polytope A b) (po d n).R (some (posR R d n m A b cs))) :
    (∀ y : Fin d → ℝ, (∀ i, cV ((cfgOf R d n m A b cs).α i) ⬝ᵥ y ≤ (cfgOf R d n m A b cs).β i) ↔
      pgMu (posR R d n m A b cs) + pgOp (posR R d n m A b cs) (WithLp.toLp 2 y) ∈ polytope A b) ∧
    (∀ i, 0 < (cfgOf R d n m A b cs).β i) ∧
    (∀ X : Fin d → ℚ, (gaugeQ (cfgOf R d n m A b cs) X : ℝ) =
      gauge (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) (WithLp.toLp 2 (cV X))) :=
  ⟨rows_iff n m A b _ _ (mu_mem_of_good hg), beta_pos_of_good n m A b _ _ hg,
    gaugeQ_eq_of_good n m (deltaBL d n) A b _ _ hg⟩

end AdversarialBco.Bit.BLP
