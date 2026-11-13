/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Poly
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Data.Int.NatAbs

@[expose] public section

/-!
# The real-RAM upper bound on a polytope, geometry of a rational polytope

The localisation lemma in the form the proof uses: a compact polytope whose data has height at most `M` lies in the
closed ball of
radius `Rloc d m M = (d m M^{2(d+1)})^{d+1}` about `0`. The route avoids the basic-solution argument of Lemma BASIC:

* `extreme_ker` (G1): at an extreme point `x` of the polytope, the rows active at `x` have no common nonzero null
  vector (else `x ± ε v` stay in the polytope);
* `clear_den` (G3): a family of `k` rationals of height at most `M` becomes a family of integers of absolute value at
  most `M^k` on multiplying by the product of the denominators;
* `gram_det_ne_zero` (G4): the integer Gram matrix `Σ_{i ∈ S} α_i α_iᵀ` of rows with no common nonzero null vector is
  invertible;
* `cramer_int_bound` (G2): a solution of an invertible integer system with entries at most `X` has coordinates at most
  `d! X^d` (Cramer's rule and `Matrix.det_le`);
* `extreme_norm_le` (G5): an extreme point has norm at most `Rloc d m M` (G1 to G4 on the active rows, cleared row by
  row: `G x = h` with `G` the Gram matrix of the cleared active rows and `h = Σ β_i α_i`);
* `polytope_sub_ball` (G6): Krein and Milman (`closure_convexHull_extremePoints`) carries the bound to the polytope.

G1 to G6 are proved here, with the elementary facts on polytopes they use.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM

variable {d m : ℕ}

/-- The radius of the localisation lemma used in Lean: `(d m M^{2(d+1)})^{d+1}`. -/
noncomputable def Rloc (d m M : ℕ) : ℝ := ((d : ℝ) * m * (M : ℝ) ^ (2 * (d + 1))) ^ (d + 1)

theorem isClosed_polytope (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) : IsClosed (polytope Am bv) := by
  have : polytope Am bv = ⋂ i, {x : E d | ∑ j, (Am i j : ℝ) * x j ≤ (bv i : ℝ)} := by
    ext x; simp [polytope]
  rw [this]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((PiLp.continuous_apply 2 _ j))

theorem convex_polytope (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) : Convex ℝ (polytope Am bv) := by
  intro x hx y hy a c ha hc hac i
  have hx' := hx i
  have hy' := hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc ∑ j, (Am i j : ℝ) * (a * x j + c * y j)
        = a * ∑ j, (Am i j : ℝ) * x j + c * ∑ j, (Am i j : ℝ) * y j := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring
    _ ≤ a * (bv i : ℝ) + c * (bv i : ℝ) := by gcongr
    _ = (bv i : ℝ) := by rw [← add_mul, hac, one_mul]

/-- BEL's diameter normalisation makes the polytope compact. -/
theorem isCompact_polytope (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (n : ℕ)
    (hdiam : ∀ x ∈ polytope Am bv, ∀ y ∈ polytope Am bv, dist x y ≤ n) : IsCompact (polytope Am bv) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_polytope Am bv) (Metric.isBounded_iff.2 ⟨n, hdiam⟩)

/-- G1: the rows active at an extreme point have no common nonzero null vector. -/
theorem extreme_ker (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {x : E d}
    (hx : x ∈ Set.extremePoints ℝ (polytope Am bv)) (v : E d)
    (hv : ∀ i, ∑ j, (Am i j : ℝ) * x j = (bv i : ℝ) → ∑ j, (Am i j : ℝ) * v j = 0) : v = 0 := by
  rw [mem_extremePoints] at hx
  obtain ⟨hxP, hext⟩ := hx
  have hlin : ∀ (i : Fin m) (t : ℝ),
      ∑ j, (Am i j : ℝ) * (x + t • v) j = ∑ j, (Am i j : ℝ) * x j + t * ∑ j, (Am i j : ℝ) * v j := by
    intro i t
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ polytope Am bv := by
    simp only [polytope, Set.mem_ofPred_eq]
    rw [Filter.eventually_all]
    intro i
    by_cases hact : ∑ j, (Am i j : ℝ) * x j = (bv i : ℝ)
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [hlin, hv i hact, hact, mul_zero, add_zero]
    · have hlt : ∑ j, (Am i j : ℝ) * x j < (bv i : ℝ) := lt_of_le_of_ne (hxP i) hact
      have hcont : Continuous fun t : ℝ => ∑ j, (Am i j : ℝ) * x j + t * ∑ j, (Am i j : ℝ) * v j := by
        fun_prop
      have ht := (hcont.tendsto 0).eventually (eventually_lt_nhds (by simpa using hlt))
      filter_upwards [ht] with t ht
      rw [hlin]
      exact ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have h1 := @hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have h2 := @hball (-(ε / 2)) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  have hseg : x ∈ openSegment ℝ (x + (ε / 2) • v) (x + (-(ε / 2)) • v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, ← add_smul]
    norm_num
  have := (hext _ h1 _ h2 hseg).1
  rw [add_eq_left, smul_eq_zero] at this
  rcases this with h | h
  · linarith
  · exact h

/-- G3: clearing the denominators of a family of `k` rationals of height at most `M`. -/
theorem clear_den {k M : ℕ} (q : Fin k → ℚ) (hq : ∀ j, (q j).num.natAbs ≤ M ∧ (q j).den ≤ M) :
    ∃ D : ℕ, 0 < D ∧ ∀ j, ∃ z : ℤ, (D : ℚ) * q j = z ∧ z.natAbs ≤ M ^ k := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨1, by decide, ?_⟩
    intro j
    exact Fin.elim0 j
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  set D := ∏ j : Fin k, (q j).den with hD
  have hD_pos : 0 < D := by
    rw [hD]
    refine Finset.prod_pos ?_
    intro j hj
    exact Rat.den_pos (q j)
  refine ⟨D, hD_pos, ?_⟩
  intro j
  set z := (q j).num * ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ) with hz
  refine ⟨z, ?_, ?_⟩
  · -- (D : ℚ) * q j = (z : ℚ)
    rw [hz]
    -- Goal: (D : ℚ) * q j = ((q j).num * ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ) : ℚ)
    rw [hD, Nat.cast_prod]
    -- Goal: (∏ i : Fin k, ((q i).den : ℚ)) * q j = ((q j).num * ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ) : ℚ)
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin k)) (fun i => ((q i).den : ℚ)) (Finset.mem_univ j)]
    -- Goal: (∏ i ∈ univ.erase j, ((q i).den : ℚ)) * ↑(q j).den * q j = ↑((q j).num * ∏ i ∈ univ.erase j, ((q i).den : ℤ))
    rw [mul_assoc, mul_comm ((q j).den : ℚ) (q j), Rat.mul_den_eq_num (q j)]
    -- Goal: (∏ i ∈ univ.erase j, ((q i).den : ℚ)) * ↑(q j).num = ↑((q j).num * ∏ i ∈ univ.erase j, ((q i).den : ℤ))
    have hprod_eq : (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℚ)) =
        ↑(∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)) := by
      simpa using (map_prod (Int.castRingHom ℚ) (fun i => ((q i).den : ℤ)) (Finset.univ.erase j)).symm
    rw [hprod_eq, mul_comm, Int.cast_mul]
  · -- z.natAbs ≤ M ^ k
    rw [hz]
    have hnum : (q j).num.natAbs ≤ M := (hq j).1
    have hden : ∀ i, (q i).den ≤ M := fun i => (hq i).2
    have hprod : (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (q i).den) ≤ M ^ ((Finset.univ : Finset (Fin k)).erase j).card := by
      refine Finset.prod_le_pow_card _ _ M ?_
      intro i hi
      exact hden i
    have hcard : ((Finset.univ : Finset (Fin k)).erase j).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    have h_pow_eq : M * M ^ (k - 1) = M ^ k := by
      have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      calc
        M * M ^ (k - 1) = M ^ (k - 1) * M := Nat.mul_comm _ _
        _ = M ^ ((k - 1) + 1) := by rw [Nat.pow_succ]
        _ = M ^ k := by rw [hk_sub]
    have h_natAbs_prod : (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)).natAbs =
        ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (q i).den := by
      calc
        (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)).natAbs =
            Int.natAbsHom (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)) := rfl
        _ = ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, Int.natAbsHom (((q i).den : ℤ)) := by
          rw [map_prod Int.natAbsHom]
        _ = ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (q i).den := by
          simp [Int.natAbs_natCast]
    calc
      ((q j).num * ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)).natAbs =
          ((q j).num).natAbs * (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, ((q i).den : ℤ)).natAbs := by
        rw [Int.natAbs_mul]
      _ = ((q j).num).natAbs * (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (q i).den) := by
        rw [h_natAbs_prod]
      _ ≤ M * (∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, (q i).den) :=
        Nat.mul_le_mul hnum (le_refl _)
      _ ≤ M * (M ^ ((Finset.univ : Finset (Fin k)).erase j).card) :=
        Nat.mul_le_mul_left M hprod
      _ = M * M ^ (k - 1) := by rw [hcard]
      _ = M ^ k := by rw [h_pow_eq]

/-- G4: the Gram matrix of integer rows with no common nonzero null vector is invertible. -/
theorem gram_det_ne_zero (S : Finset (Fin m)) (α : Fin m → Fin d → ℤ)
    (hker : ∀ v : Fin d → ℝ, (∀ i ∈ S, ∑ j, (α i j : ℝ) * v j = 0) → v = 0) :
    (∑ i ∈ S, Matrix.vecMulVec (α i) (α i)).det ≠ 0 := by
  by_contra! hdet
  let G := ∑ i ∈ S, Matrix.vecMulVec (α i) (α i)
  have hGdet : G.det = 0 := hdet
  have h_exists := ((Matrix.exists_mulVec_eq_zero_iff (M := G)).mpr hGdet)
  rcases h_exists with ⟨v, hv_ne, hv_mul⟩
  have h_dot_zero : v ⬝ᵥ (G *ᵥ v) = 0 := by
    rw [hv_mul, dotProduct_zero]
  have h_dot_sum : v ⬝ᵥ (G *ᵥ v) = ∑ i ∈ S, (v ⬝ᵥ (α i)) * (v ⬝ᵥ (α i)) := by
    calc
      v ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ ((∑ i ∈ S, Matrix.vecMulVec (α i) (α i)) *ᵥ v) := rfl
      _ = v ⬝ᵥ (∑ i ∈ S, Matrix.vecMulVec (α i) (α i) *ᵥ v) := by rw [sum_mulVec]
      _ = ∑ i ∈ S, v ⬝ᵥ (Matrix.vecMulVec (α i) (α i) *ᵥ v) := by rw [dotProduct_sum]
      _ = ∑ i ∈ S, (v ⬝ᵥ (α i)) * (v ⬝ᵥ (α i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [vecMulVec_mulVec]
        have htemp : MulOpposite.op ((α i) ⬝ᵥ v) • (α i) = ((α i) ⬝ᵥ v) • (α i) := by
          ext j
          simp [Pi.smul_apply, mul_comm]
        rw [htemp]
        rw [dotProduct_smul, smul_eq_mul]
        rw [dotProduct_comm]
  rw [h_dot_sum] at h_dot_zero
  have h_nonneg : ∀ i ∈ S, 0 ≤ (v ⬝ᵥ (α i)) * (v ⬝ᵥ (α i)) := by
    intro i hi
    have : (v ⬝ᵥ (α i)) * (v ⬝ᵥ (α i)) = (v ⬝ᵥ (α i)) ^ 2 := by ring
    rw [this]
    exact Int.sq_nonneg _
  have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_dot_zero
  have h_vi_zero : ∀ i ∈ S, v ⬝ᵥ (α i) = 0 := by
    intro i hi
    have h_sq_zero := h_all_zero i hi
    exact (eq_zero_or_eq_zero_of_mul_eq_zero h_sq_zero).elim id id
  have h_ker_input : ∀ i ∈ S, ∑ j : Fin d, (α i j : ℝ) * (v j : ℝ) = 0 := by
    intro i hi
    have hz := h_vi_zero i hi
    have hz' : ((v ⬝ᵥ (α i) : ℤ) : ℝ) = (0 : ℝ) := by
      -- cast the dot product equality from ℤ to ℝ
      simpa using congrArg (fun x : ℤ => (x : ℝ)) hz
    simpa [dotProduct, mul_comm] using hz'
  have hv_zero : (fun j => (v j : ℝ)) = 0 := hker (fun j => (v j : ℝ)) h_ker_input
  have hv_all_zero : ∀ j, v j = 0 := by
    intro j
    have h := congr_fun hv_zero j
    -- h : (v j : ℝ) = 0
    exact_mod_cast (show (v j : ℝ) = (0 : ℝ) from h)
  apply hv_ne
  ext j
  exact hv_all_zero j

/-- G2: Cramer's rule with Hadamard's bound replaced by `Matrix.det_le`. -/
theorem cramer_int_bound (G : Matrix (Fin d) (Fin d) ℤ) (h : Fin d → ℤ) (X : ℕ) (hG : ∀ i j, |G i j| ≤ X)
    (hh : ∀ i, |h i| ≤ X) (hdet : G.det ≠ 0) (x : Fin d → ℝ)
    (hx : (G.map (Int.cast : ℤ → ℝ)) *ᵥ x = fun i => (h i : ℝ)) (l : Fin d) :
    |x l| ≤ (d.factorial : ℝ) * (X : ℝ) ^ d := by
  set Gℝ := G.map (Int.cast : ℤ → ℝ) with hGℝ
  have hdet' : Gℝ.det ≠ 0 := by
    intro hzero
    apply hdet
    have hcast := Int.cast_det (R := ℝ) G
    have hzero' : (G.det : ℝ) = 0 := by
      calc
        (G.det : ℝ) = (G.map (fun (x : ℤ) => (x : ℝ))).det := hcast
        _ = (G.map (Int.cast : ℤ → ℝ)).det := by simp
        _ = 0 := hzero
    exact_mod_cast hzero'
  set b := fun i => (h i : ℝ) with hb
  -- Express x in terms of cramer
  have h_mulVec_cramer := Matrix.mulVec_cramer Gℝ b
  have hx' : Gℝ *ᵥ x = b := hx
  have h_eq : Gℝ *ᵥ cramer Gℝ b = Gℝ *ᵥ (Gℝ.det • x) := by
    calc
      Gℝ *ᵥ cramer Gℝ b = Gℝ.det • b := h_mulVec_cramer
      _ = Gℝ.det • (Gℝ *ᵥ x) := by rw [hx']
      _ = Gℝ *ᵥ (Gℝ.det • x) := by simp [mulVec_smul]
  have h_zero : Gℝ *ᵥ (cramer Gℝ b - Gℝ.det • x) = 0 := by
    rw [mulVec_sub, h_eq, sub_self]
  have h_inv_det : IsUnit Gℝ.det := isUnit_iff_ne_zero.mpr hdet'
  haveI : Invertible Gℝ.det := h_inv_det.invertible
  haveI : Invertible Gℝ := Matrix.invertibleOfDetInvertible Gℝ
  have h_solve : cramer Gℝ b - Gℝ.det • x = 0 := by
    calc
      cramer Gℝ b - Gℝ.det • x = 1 *ᵥ (cramer Gℝ b - Gℝ.det • x) := by simp
      _ = (Gℝ⁻¹ * Gℝ) *ᵥ (cramer Gℝ b - Gℝ.det • x) := by simp
      _ = Gℝ⁻¹ *ᵥ (Gℝ *ᵥ (cramer Gℝ b - Gℝ.det • x)) := by simp [mulVec_mulVec]
      _ = Gℝ⁻¹ *ᵥ 0 := by rw [h_zero]
      _ = 0 := by simp
  have h_cramer_eq : cramer Gℝ b = Gℝ.det • x := sub_eq_zero.mp h_solve
  -- Express x and take absolute value
  have hx_eq : x = (Gℝ.det)⁻¹ • cramer Gℝ b := by
    calc
      x = 1 • x := by simp
      _ = ((Gℝ.det)⁻¹ * Gℝ.det) • x := by simp [hdet']
      _ = (Gℝ.det)⁻¹ • (Gℝ.det • x) := by simp [smul_smul]
      _ = (Gℝ.det)⁻¹ • cramer Gℝ b := by rw [h_cramer_eq]
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, abs_mul, abs_inv]
  -- Goal: |Gℝ.det|⁻¹ * |det (Gℝ.updateCol l b)| ≤ (d.factorial : ℝ) * (X : ℝ) ^ d
  -- Bound |det (Gℝ.updateCol l b)| ≤ d! * X^d
  have h_bound_det : |(Gℝ.updateCol l b).det| ≤ (d.factorial : ℝ) * (X : ℝ) ^ d := by
    have h_entries : ∀ i j, |(Gℝ.updateCol l b) i j| ≤ (X : ℝ) := by
      intro i j
      rw [Matrix.updateCol_apply]
      split
      · rw [hb]; simp; exact_mod_cast hh i
      · rw [hGℝ]
        have hG' : |(G i j : ℝ)| ≤ (X : ℝ) := by exact_mod_cast hG i j
        simpa [Matrix.map_apply] using hG'
    have h := Matrix.det_le (abv := AbsoluteValue.abs) h_entries
    simpa [Fintype.card_fin] using h
  -- Bound |Gℝ.det| ≥ 1
  have h_det_ge_one : 1 ≤ |Gℝ.det| := by
    have h_cast : Gℝ.det = (G.det : ℝ) := by
      rw [hGℝ]
      simpa using (Int.cast_det (R := ℝ) G).symm
    rw [h_cast]
    have h_abs_int : 1 ≤ |G.det| := Int.one_le_abs hdet
    have h_cast_abs : |(G.det : ℝ)| = (|G.det| : ℝ) := by
      simpa using (Int.cast_abs (a := G.det) (R := ℝ)).symm
    rw [h_cast_abs]
    exact_mod_cast h_abs_int
  -- Combine bounds
  have h_pos : 0 < |Gℝ.det| := by linarith
  have h_inv_le_one : |Gℝ.det|⁻¹ ≤ 1 := by
    have h_nonneg_inv : 0 ≤ |Gℝ.det|⁻¹ := by positivity
    have h := mul_le_mul_of_nonneg_right h_det_ge_one h_nonneg_inv
    simpa [mul_inv_cancel₀ h_pos.ne'] using h
  have h_nonneg_fact : 0 ≤ (d.factorial : ℝ) * (X : ℝ) ^ d := by positivity
  have h_nonneg_det_abs : 0 ≤ |(Gℝ.updateCol l b).det| := abs_nonneg _
  calc
    |Gℝ.det|⁻¹ * |(Gℝ.updateCol l b).det| ≤ 1 * |(Gℝ.updateCol l b).det| := by
      gcongr
    _ ≤ 1 * ((d.factorial : ℝ) * (X : ℝ) ^ d) := by gcongr
    _ = (d.factorial : ℝ) * (X : ℝ) ^ d := by simp

/-- G5: an extreme point of a polytope of height at most `M` has norm at most `Rloc d m M`. -/
theorem extreme_norm_le (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {M : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hM : 1 ≤ M) (hH : HeightLE Am bv M) {x : E d} (hx : x ∈ Set.extremePoints ℝ (polytope Am bv)) :
    ‖x‖ ≤ Rloc d m M := by
  -- define the set S of active rows (where equality holds)
  let S : Finset (Fin m) := Finset.filter (λ i => ∑ j, (Am i j : ℝ) * x j = (bv i : ℝ)) Finset.univ
  have hS_active : ∀ i ∈ S, ∑ j, (Am i j : ℝ) * x j = (bv i : ℝ) := by
    intro i hi
    simpa [S] using hi
  -- clear denominators for each row i to get integer representatives
  -- define the function q_i : Fin (d+1) → ℚ for clearing denominators
  let q (i : Fin m) : Fin (d+1) → ℚ := λ j =>
    if h : (j : ℕ) < d then Am i ⟨j, h⟩ else bv i
  have hq_bound : ∀ i j, ((q i) j).num.natAbs ≤ M ∧ ((q i) j).den ≤ M := by
    intro i j
    dsimp [q]
    by_cases hj : (j : ℕ) < d
    · simp [hj]
      rcases hH.1 i ⟨j, hj⟩ with ⟨hnum, hden⟩
      exact ⟨hnum, hden⟩
    · simp [hj]
      rcases hH.2 i with ⟨hnum, hden⟩
      exact ⟨hnum, hden⟩
  have hclear : ∀ i, ∃ D : ℕ, 0 < D ∧ ∀ j : Fin (d+1), ∃ z : ℤ, (D : ℚ) * (q i j) = z ∧ z.natAbs ≤ M ^ (d+1) := by
    intro i
    apply clear_den (q i)
    exact hq_bound i
  choose D hDpos hrest using hclear
  have hα : ∀ i j, ∃ z : ℤ, (D i : ℚ) * (q i j) = z ∧ z.natAbs ≤ M ^ (d+1) := hrest
  choose α hα_eq hα_bound using hα
  -- extract αi (Fin d → ℤ) and βi (ℤ) for each row i
  let αi (i : Fin m) (j : Fin d) : ℤ := α i (Fin.castSucc j)
  let βi (i : Fin m) : ℤ := α i (Fin.last d)
  have hq_castSucc : ∀ i j, q i (Fin.castSucc j) = Am i j := by
    intro i j
    dsimp [q]
    simp
  have hq_last : ∀ i, q i (Fin.last d) = bv i := by
    intro i
    dsimp [q]
    simp
  have hαi_eq : ∀ i j, (D i : ℚ) * (Am i j : ℚ) = (αi i j : ℚ) := by
    intro i j
    rw [← hq_castSucc i j]
    simpa [αi] using hα_eq i (Fin.castSucc j)
  have hβi_eq : ∀ i, (D i : ℚ) * (bv i : ℚ) = (βi i : ℚ) := by
    intro i
    rw [← hq_last i]
    simpa [βi] using hα_eq i (Fin.last d)
  have hαi_bound : ∀ i j, (αi i j).natAbs ≤ M ^ (d+1) := by
    intro i j; simpa [αi] using hα_bound i (Fin.castSucc j)
  have hβi_bound : ∀ i, (βi i).natAbs ≤ M ^ (d+1) := by
    intro i; simpa [βi] using hα_bound i (Fin.last d)
  -- define the Gram matrix G = Σ_{i∈S} α_i α_i^T and vector h = Σ_{i∈S} β_i α_i
  let G : Matrix (Fin d) (Fin d) ℤ := ∑ i ∈ S, Matrix.vecMulVec (αi i) (αi i)
  let h : Fin d → ℤ := λ j => ∑ i ∈ S, (βi i) * (αi i j)
  -- key identity: for i ∈ S, Σ_k α_i(k) * x_k = β_i
  have h_active_eq : ∀ i ∈ S, (∑ k, (αi i k : ℝ) * x.ofLp k) = (βi i : ℝ) := by
    intro i hi
    have hactive := hS_active i hi
    -- hactive: ∑ j, (Am i j : ℝ) * x.ofLp j = (bv i : ℝ)
    have hαi_eq_real : ∀ k, (D i : ℝ) * (Am i k : ℝ) = (αi i k : ℝ) := by
      intro k
      have h := hαi_eq i k
      exact_mod_cast h
    have h_right : (D i : ℝ) * (bv i : ℝ) = (βi i : ℝ) := by
      have h := hβi_eq i
      exact_mod_cast h
    calc
      (∑ k, (αi i k : ℝ) * x.ofLp k) = (∑ k, ((D i : ℝ) * (Am i k : ℝ)) * x.ofLp k) := by
        apply Finset.sum_congr rfl; intro k _
        rw [hαi_eq_real k]
      _ = (D i : ℝ) * (∑ k, (Am i k : ℝ) * x.ofLp k) := by
        simp [Finset.mul_sum, mul_assoc]
      _ = (D i : ℝ) * (bv i : ℝ) := by rw [hactive]
      _ = (βi i : ℝ) := by rw [h_right]
  -- lemma: G x = h (as real vectors)
  have hGx_eq_h : (G.map (Int.cast : ℤ → ℝ)) *ᵥ (x : Fin d → ℝ) = (λ j => (h j : ℝ)) := by
    ext j
    rw [Matrix.mulVec_apply, dotProduct]
    -- Goal: ((G.map Int.cast).row j) ⬝ᵥ x.ofLp = (h j : ℝ)
    simp only [G, h, Matrix.row_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Int.cast_sum, Int.cast_mul]
    -- Goal: (∑ k, (∑ i ∈ S, (αi i j : ℝ) * (αi i k : ℝ)) * x.ofLp k) = (∑ i ∈ S, (βi i : ℝ) * (αi i j : ℝ))
    simp only [Finset.sum_mul]
    -- Goal: (∑ k, ∑ i ∈ S, (αi i j : ℝ) * (αi i k : ℝ) * x.ofLp k) = (∑ i ∈ S, (βi i : ℝ) * (αi i j : ℝ))
    -- Swap sums on LHS
    rw [Finset.sum_comm]
    -- Goal: (∑ i ∈ S, ∑ k, (αi i j : ℝ) * (αi i k : ℝ) * x.ofLp k) = (∑ i ∈ S, (βi i : ℝ) * (αi i j : ℝ))
    calc
      (∑ i ∈ S, ∑ k, (αi i j : ℝ) * (αi i k : ℝ) * x.ofLp k) =
          (∑ i ∈ S, (αi i j : ℝ) * (∑ k, (αi i k : ℝ) * x.ofLp k)) := by
        apply Finset.sum_congr rfl; intro i hi
        simp [Finset.mul_sum, mul_assoc]
      _ = (∑ i ∈ S, (αi i j : ℝ) * (βi i : ℝ)) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [h_active_eq i hi]
      _ = ∑ i ∈ S, (βi i : ℝ) * (αi i j : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi; ring
  -- lemma: the kernel condition for gram_det_ne_zero
  have hker : ∀ v : Fin d → ℝ, (∀ i ∈ S, ∑ j, (αi i j : ℝ) * v j = 0) → v = 0 := by
    intro v hv
    let v' : E d := WithLp.toLp 2 v
    have hv' : ∀ i, ∑ j, (Am i j : ℝ) * x j = (bv i : ℝ) → ∑ j, (Am i j : ℝ) * v' j = 0 := by
      intro i heq
      -- heq means i ∈ S
      have hiS : i ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ i, heq⟩
      have hsum : ∑ j, (αi i j : ℝ) * v j = 0 := hv i hiS
      have hsum' : ∑ j, (αi i j : ℝ) * v' j = 0 := by simpa [v'] using hsum
      have hDpos' : (0 : ℝ) < (D i : ℝ) := by exact_mod_cast hDpos i
      have hD_ne_zero : (D i : ℝ) ≠ 0 := by linarith
      have h_eq_real : ∀ j, (D i : ℝ) * (Am i j : ℝ) = (αi i j : ℝ) := by
        intro j
        have h := hαi_eq i j
        exact_mod_cast h
      calc
        ∑ j, (Am i j : ℝ) * v' j = ((D i : ℝ)⁻¹) * ((D i : ℝ) * (∑ j, (Am i j : ℝ) * v' j)) := by
          field_simp [hD_ne_zero]
        _ = ((D i : ℝ)⁻¹) * (∑ j, (D i : ℝ) * ((Am i j : ℝ) * v' j)) := by
          simp [Finset.mul_sum, mul_assoc]
        _ = ((D i : ℝ)⁻¹) * (∑ j, ((D i : ℝ) * (Am i j : ℝ)) * v' j) := by
          simp [mul_assoc]
        _ = ((D i : ℝ)⁻¹) * (∑ j, (αi i j : ℝ) * v' j) := by
          simp [h_eq_real]
        _ = ((D i : ℝ)⁻¹) * (0 : ℝ) := by rw [hsum']
        _ = 0 := by ring
    have hzero : v' = 0 := extreme_ker Am bv hx v' hv'
    ext i; simpa [v'] using congrArg (λ f : E d => f i) hzero
  -- apply gram_det_ne_zero to get det G ≠ 0
  have hdet : G.det ≠ 0 := by
    apply gram_det_ne_zero S αi hker
  -- bound on entries of G and h
  let X : ℕ := m * M ^ (2 * (d + 1))
  have hXpos_nat : 0 < X := by
    apply Nat.mul_pos; exact Nat.one_pos.trans_le hm; apply pow_pos; exact Nat.one_pos.trans_le hM
  have hXpos : 0 ≤ (X : ℝ) := by exact Nat.cast_nonneg _
  have hG_bound : ∀ i j, |G i j| ≤ X := by
    intro i j
    have hG_entry : G i j = ∑ k ∈ S, (αi k i) * (αi k j) := by
      simp [G, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [hG_entry]
    calc
      |∑ k ∈ S, (αi k i) * (αi k j)| ≤ ∑ k ∈ S, |(αi k i) * (αi k j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ S, |αi k i| * |αi k j| := by
        refine Finset.sum_congr rfl (λ k hk => ?_)
        simp [abs_mul]
      _ ≤ ∑ k ∈ S, ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        refine Finset.sum_le_sum (λ k hk => ?_)
        have hi := hαi_bound k i
        have hj := hαi_bound k j
        have hi_abs : |αi k i| ≤ (M ^ (d+1) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hi
        have hj_abs : |αi k j| ≤ (M ^ (d+1) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hj
        have h_mul : |αi k i| * |αi k j| ≤ (M ^ (d+1) : ℤ) * (M ^ (d+1) : ℤ) :=
          mul_le_mul hi_abs hj_abs (abs_nonneg _) (by positivity)
        simpa [abs_mul] using h_mul
      _ = (S.card : ℤ) • ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        simp [Finset.sum_const]
      _ = (S.card : ℤ) * ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by simp
      _ ≤ (m : ℤ) * ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h_card : S.card ≤ Fintype.card (Fin m) := Finset.card_le_univ S
        have h_card' : (S.card : ℤ) ≤ (m : ℤ) := by
          simpa using h_card
        exact h_card'
      _ = (X : ℤ) := by
        dsimp [X]
        push_cast
        ring
      _ = X := by simp
  -- bound on entries of h
  have hh_bound : ∀ i, |h i| ≤ X := by
    intro i
    have hh_entry : h i = ∑ k ∈ S, (βi k) * (αi k i) := by
      simp [h, Finset.sum_apply]
    rw [hh_entry]
    calc
      |∑ k ∈ S, (βi k) * (αi k i)| ≤ ∑ k ∈ S, |(βi k) * (αi k i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ S, |βi k| * |αi k i| := by
        refine Finset.sum_congr rfl (λ k hk => ?_)
        simp [abs_mul]
      _ ≤ ∑ k ∈ S, ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        refine Finset.sum_le_sum (λ k hk => ?_)
        have hi := hαi_bound k i
        have hβi := hβi_bound k
        have hi_abs : |αi k i| ≤ (M ^ (d+1) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hi
        have hβi_abs : |βi k| ≤ (M ^ (d+1) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hβi
        have h_mul : |βi k| * |αi k i| ≤ (M ^ (d+1) : ℤ) * (M ^ (d+1) : ℤ) :=
          mul_le_mul hβi_abs hi_abs (abs_nonneg _) (by positivity)
        simpa [abs_mul] using h_mul
      _ = (S.card : ℤ) • ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        simp [Finset.sum_const]
      _ = (S.card : ℤ) * ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by simp
      _ ≤ (m : ℤ) * ((M ^ (d+1)) * (M ^ (d+1)) : ℤ) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h_card : S.card ≤ Fintype.card (Fin m) := Finset.card_le_univ S
        have h_card' : (S.card : ℤ) ≤ (m : ℤ) := by simpa using h_card
        exact h_card'
      _ = (X : ℤ) := by
        dsimp [X]
        push_cast
        ring
      _ = X := by simp
  -- apply cramer_int_bound
  have h_cramer : ∀ l : Fin d, |(x l : ℝ)| ≤ (d.factorial : ℝ) * ((X : ℝ) ^ d) := by
    intro l
    apply cramer_int_bound G h X hG_bound hh_bound hdet (x : Fin d → ℝ) hGx_eq_h l
  -- now bound the norm: ‖x‖ ≤ √d * d! * X^d ≤ d^{d+1} * X^{d+1} = (d*X)^{d+1} = Rloc d m M
  have h_norm : ‖x‖ ≤ Real.sqrt (d : ℝ) * ((d.factorial : ℝ) * ((X : ℝ) ^ d)) := by
    rw [EuclideanSpace.norm_eq]
    -- ‖x‖ = √(∑ i, ‖x.ofLp i‖ ^ 2)
    -- simplify ‖x.ofLp i‖ to |x i|
    have h_norm_simp : ∀ i, ‖x.ofLp i‖ = |x i| := by
      intro i; simp
    simp only [h_norm_simp, sq_abs]
    -- Now goal is √(∑ i, (x i)^2) ≤ √d * (d! * X^d)
    have h_sq_bound : ∀ i, (x i)^2 ≤ (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2) := by
      intro i
      have h_abs : |(x i : ℝ)| ≤ (d.factorial : ℝ) * ((X : ℝ) ^ d) := h_cramer i
      have hB_nonneg : 0 ≤ (d.factorial : ℝ) * ((X : ℝ) ^ d) := by
        positivity
      have h_sq : (x i)^2 ≤ (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2) := by
        have h_abs' := abs_le.mp h_abs
        nlinarith
      exact h_sq
    have h_sum : (∑ i, (x i)^2) ≤ (d : ℝ) * (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2) := by
      calc
        (∑ i, (x i)^2) ≤ (∑ i : Fin d, ((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2) :=
          Finset.sum_le_sum (λ i _ => h_sq_bound i)
        _ = (d : ℝ) * (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2) := by
          simp [Finset.sum_const, Fintype.card_fin]
    have h_sqrt : Real.sqrt (∑ i, (x i)^2) ≤ Real.sqrt ((d : ℝ) * (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2)) :=
      Real.sqrt_le_sqrt h_sum
    have h_sqrt_sq : Real.sqrt ((d : ℝ) * (((d.factorial : ℝ) * ((X : ℝ) ^ d)) ^ 2)) =
        Real.sqrt (d : ℝ) * ((d.factorial : ℝ) * ((X : ℝ) ^ d)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (d : ℝ)), Real.sqrt_sq (by positivity : 0 ≤ (d.factorial : ℝ) * ((X : ℝ) ^ d))]
    rw [h_sqrt_sq] at h_sqrt
    exact h_sqrt
  have h_final : Real.sqrt (d : ℝ) * ((d.factorial : ℝ) * ((X : ℝ) ^ d)) ≤ Rloc d m M := by
    -- Rloc d m M = (d * m * M^{2(d+1)})^{d+1} = (d * X)^{d+1}
    have hX_ge_one : 1 ≤ (X : ℝ) := by
      exact_mod_cast hXpos_nat
    have h_sqrt_d_le_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
      have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
      have hd_ge_one : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      calc
        Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = |(d : ℝ)| := Real.sqrt_sq_eq_abs _
        _ = (d : ℝ) := abs_of_nonneg hd_nonneg
    have h_fact_le : (d.factorial : ℝ) ≤ (d : ℝ) ^ d := by
      have h_fact_nat : d.factorial ≤ d ^ d := Nat.factorial_le_pow _
      exact_mod_cast h_fact_nat
    calc
      Real.sqrt (d : ℝ) * ((d.factorial : ℝ) * ((X : ℝ) ^ d)) ≤ (d : ℝ) * ((d.factorial : ℝ) * ((X : ℝ) ^ d)) := by
        have hB_nonneg : 0 ≤ (d.factorial : ℝ) * ((X : ℝ) ^ d) := by positivity
        nlinarith
      _ ≤ (d : ℝ) * (((d : ℝ) ^ d) * ((X : ℝ) ^ d)) := by
        gcongr
      _ = ((d : ℝ) * (X : ℝ)) ^ d * (d : ℝ) := by
        ring
      _ ≤ ((d : ℝ) * (X : ℝ)) ^ d * ((d : ℝ) * (X : ℝ)) := by
        have h_le : (d : ℝ) ≤ (d : ℝ) * (X : ℝ) := by
          have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          have hX_ge_one' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos_nat
          nlinarith
        have h_nonneg : 0 ≤ ((d : ℝ) * (X : ℝ)) ^ d := by positivity
        gcongr
      _ = ((d : ℝ) * (X : ℝ)) ^ (d + 1) := by ring
      _ = Rloc d m M := by
        dsimp [Rloc, X]
        push_cast
        ring
  exact le_trans h_norm h_final

/-- G6, the localisation lemma: a compact polytope of height at most `M` lies in the closed ball of radius
`Rloc d m M`. -/
theorem polytope_sub_ball (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) {M : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hM : 1 ≤ M) (hH : HeightLE Am bv M) (hK : IsCompact (polytope Am bv)) :
    polytope Am bv ⊆ Metric.closedBall 0 (Rloc d m M) := by
  have hconv : Convex ℝ (polytope Am bv) := convex_polytope Am bv
  have hKreins : closure ((convexHull ℝ) (Set.extremePoints ℝ (polytope Am bv))) = polytope Am bv :=
    closure_convexHull_extremePoints hK hconv
  have hball_closed : IsClosed (Metric.closedBall (0 : E d) (Rloc d m M)) :=
    Metric.isClosed_closedBall
  have hball_convex : Convex ℝ (Metric.closedBall (0 : E d) (Rloc d m M)) :=
    convex_closedBall (0 : E d) (Rloc d m M)
  have h_extreme_subset : Set.extremePoints ℝ (polytope Am bv) ⊆ Metric.closedBall (0 : E d) (Rloc d m M) := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    exact extreme_norm_le Am bv hd hm hM hH hx
  have h_conv_hull_subset : (convexHull ℝ) (Set.extremePoints ℝ (polytope Am bv)) ⊆ Metric.closedBall (0 : E d) (Rloc d m M) :=
    convexHull_min h_extreme_subset hball_convex
  have h_closure_subset : closure ((convexHull ℝ) (Set.extremePoints ℝ (polytope Am bv))) ⊆ Metric.closedBall (0 : E d) (Rloc d m M) :=
    closure_minimal h_conv_hull_subset hball_closed
  rw [← hKreins]
  exact h_closure_subset

end AdversarialBco.Conj1Poly
