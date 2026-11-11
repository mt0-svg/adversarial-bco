/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# Proofs of the statements of `Df2Oracle.lean`

One theorem per `Prop` of `AdversarialBco/Poly/Df2Oracle.lean`, named after it in lower camel case, at the end of this
file: `lemmaCC`, `lemmaBALL`, `lemmaLINE`, `lemmaSEP`, `lemmaGAUGE`, `lemmaGVAL`, `lemmaGCAP`, `propELL`, `propELLcap`,
`propELL1`, `propAP`. The mathematics is Appendix E of the paper.

The helpers live in `AdversarialBco.Poly.LeanAp`. `ell1_acc` treats one case directly
(`ell1_acc_up`) and gets the other by the reflection `ellOne_neg`. The `d = 1` transfer in `propAP` goes through
`propAP_of_parts`.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly
namespace LeanAp

variable {d : ℕ}

/-! ## The Euclidean norm `oNorm` -/

theorem oNorm_eq (v : Fin d → ℝ) : oNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, oNorm]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, pow_two]

theorem oNorm_nonneg (v : Fin d → ℝ) : 0 ≤ oNorm v := Real.sqrt_nonneg _

theorem oNorm_sq (v : Fin d → ℝ) : oNorm v ^ 2 = v ⬝ᵥ v := by
  rw [oNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem oNorm_add_le (u v : Fin d → ℝ) : oNorm (u + v) ≤ oNorm u + oNorm v := by
  simp only [oNorm_eq, WithLp.toLp_add]; exact norm_add_le _ _

theorem oNorm_sub_le (u v : Fin d → ℝ) : oNorm (u - v) ≤ oNorm u + oNorm v := by
  simp only [oNorm_eq, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem oNorm_neg (v : Fin d → ℝ) : oNorm (-v) = oNorm v := by
  simp only [oNorm_eq, WithLp.toLp_neg, norm_neg]

theorem oNorm_sub_comm (u v : Fin d → ℝ) : oNorm (u - v) = oNorm (v - u) := by
  rw [← oNorm_neg, neg_sub]

theorem oNorm_smul (t : ℝ) (v : Fin d → ℝ) : oNorm (t • v) = |t| * oNorm v := by
  simp only [oNorm_eq, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem oNorm_zero : oNorm (0 : Fin d → ℝ) = 0 := by simp [oNorm]

theorem oNorm_eq_zero {v : Fin d → ℝ} : oNorm v = 0 ↔ v = 0 := by
  rw [oNorm_eq, norm_eq_zero]
  constructor
  · intro h; simpa using congrArg WithLp.ofLp h
  · rintro rfl; rfl

theorem oNorm_eq_zero_iff (v : Fin d → ℝ) : oNorm v = 0 ↔ v = 0 := oNorm_eq_zero

theorem oNorm_sub_sub_le (x y z : Fin d → ℝ) : oNorm (x - z) ≤ oNorm (x - y) + oNorm (y - z) := by
  have : x - z = (x - y) + (y - z) := by abel
  rw [this]; exact oNorm_add_le _ _

theorem abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ oNorm u * oNorm v := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 v)
  rw [oNorm_eq, oNorm_eq]
  convert h using 2
  simp [PiLp.inner_apply, dotProduct, mul_comm]

theorem dot_le (u v : Fin d → ℝ) : u ⬝ᵥ v ≤ oNorm u * oNorm v := (le_abs_self _).trans (abs_dot_le u v)

theorem oUnit_dot (i : Fin d) (v : Fin d → ℝ) : oUnit i ⬝ᵥ v = v i := by
  simp [oUnit, Pi.single_apply, dotProduct]

theorem oNorm_oUnit (i : Fin d) : oNorm (oUnit i) = 1 := by
  rw [oNorm, oUnit_dot]; simp [oUnit]

theorem abs_apply_le_oNorm (v : Fin d → ℝ) (i : Fin d) : |v i| ≤ oNorm v := by
  have := abs_dot_le (oUnit i) v
  rwa [oUnit_dot, oNorm_oUnit, one_mul] at this

theorem oNorm_le_l1 (v : Fin d → ℝ) : oNorm v ≤ ∑ i, |v i| := by
  rw [oNorm, Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  calc v ⬝ᵥ v = ∑ i, |v i| ^ 2 := by simp [dotProduct, pow_two]
    _ ≤ (∑ i, |v i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

theorem l1_le_sqrt_mul (v : Fin d → ℝ) : ∑ i, |v i| ≤ Real.sqrt d * oNorm v := by
  have h := abs_dot_le (fun _ => (1 : ℝ)) (fun i => |v i|)
  have h1 : oNorm (fun _ : Fin d => (1 : ℝ)) = Real.sqrt d := by simp [oNorm, dotProduct]
  have h2 : oNorm (fun i => |v i|) = oNorm v := by simp [oNorm, dotProduct, abs_mul_abs_self]
  rw [h1, h2] at h
  have h3 : (fun _ : Fin d => (1 : ℝ)) ⬝ᵥ (fun i => |v i|) = ∑ i, |v i| := by simp [dotProduct]
  rw [h3] at h
  exact (le_abs_self _).trans h

/-! ## The gauge, through Mathlib's `gauge` on `EuclideanSpace` -/

/-- The body seen from `a₀`, in `EuclideanSpace`. -/
def gSet (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | a0 + WithLp.ofLp v ∈ Q}

theorem oGauge_eq_gauge (Q : Set (Fin d → ℝ)) (a0 x : Fin d → ℝ) :
    oGauge Q a0 x = gauge (gSet Q a0) (WithLp.toLp 2 (x - a0)) := by
  rw [oGauge, gauge_def']
  rfl

theorem oNorm_ofLp (v : EuclideanSpace ℝ (Fin d)) : oNorm (WithLp.ofLp v) = ‖v‖ := by
  rw [oNorm_eq]

theorem gSet_convex {Q : Set (Fin d → ℝ)} (a0 : Fin d → ℝ) (hQ : Convex ℝ Q) : Convex ℝ (gSet Q a0) := by
  intro u hu v hv a b ha hb hab
  simp only [gSet, Set.mem_ofPred_eq, WithLp.ofLp_add, WithLp.ofLp_smul] at hu hv ⊢
  have := hQ hu hv ha hb hab
  convert this using 1
  rw [smul_add, smul_add, ← add_assoc, add_add_add_comm, ← add_smul, hab, one_smul]
  abel

theorem gSet_ball {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {r : ℝ} (hball : oBall a0 r ⊆ Q) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ gSet Q a0 := by
  intro v hv
  apply hball
  simp only [oBall, Set.mem_ofPred_eq, add_sub_cancel_left, oNorm_ofLp]
  simpa using (Metric.mem_ball.mp hv).le

theorem gSet_closedBall {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {R : ℝ} (ha0 : a0 ∈ Q) (hQR : Q ⊆ oBall 0 R) :
    gSet Q a0 ⊆ Metric.closedBall 0 (2 * R) := by
  intro v hv
  have h1 : oNorm (a0 + WithLp.ofLp v - 0) ≤ R := hQR hv
  have h2 : oNorm (a0 - 0) ≤ R := hQR ha0
  simp only [sub_zero] at h1 h2
  rw [Metric.mem_closedBall, dist_zero_right, ← oNorm_ofLp]
  have : WithLp.ofLp v = (a0 + WithLp.ofLp v) - a0 := by abel
  rw [this]
  linarith [oNorm_sub_le (a0 + WithLp.ofLp v) a0]

theorem gSet_isClosed {Q : Set (Fin d → ℝ)} (a0 : Fin d → ℝ) (hQ : IsClosed Q) : IsClosed (gSet Q a0) :=
  hQ.preimage (continuous_const.add (PiLp.continuous_ofLp 2 _))

/-- Lemma GAUGE. -/
theorem lemmaGAUGE : LemmaGAUGE := by
  intro d Q a0 r R hQ hcl hr hball hQR
  have ha0 : a0 ∈ Q := hball (by simp [oBall, oNorm_zero, hr.le])
  have hconv := gSet_convex a0 hQ
  have hb := gSet_ball hball
  have habs : Absorbent ℝ (gSet Q a0) := (absorbent_ball_zero hr).mono hb
  have hnhds : gSet Q a0 ∈ nhds (0 : EuclideanSpace ℝ (Fin d)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr) hb
  have hR : 0 ≤ R := le_trans (oNorm_nonneg _) (by simpa [oBall] using hQR ha0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb' hab => ?_⟩
    simp only [oGauge_eq_gauge, smul_eq_mul]
    have : WithLp.toLp 2 (a • x + b • y - a0) = a • WithLp.toLp 2 (x - a0) + b • WithLp.toLp 2 (y - a0) := by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
      congr 1
      rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
    rw [this]
    refine (gauge_add_le hconv habs _ _).trans ?_
    rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb']
    rfl
  · intro x y
    have hL := hconv.lipschitzWith_gauge (r := ⟨r, hr.le⟩) hr hb
    have := hL.dist_le_mul (WithLp.toLp 2 (x - a0)) (WithLp.toLp 2 (y - a0))
    rw [oGauge_eq_gauge, oGauge_eq_gauge, ← Real.dist_eq]
    refine this.trans (le_of_eq ?_)
    rw [dist_eq_norm, ← WithLp.toLp_sub, oNorm_eq]
    simp only [one_div]
    congr 3
    abel
  · intro x
    rw [oGauge_eq_gauge, oNorm_eq]
    constructor
    · exact le_gauge_of_subset_closedBall habs (by linarith) (gSet_closedBall ha0 hQR)
    · rw [le_div_iff₀ hr, mul_comm]
      exact mul_gauge_le_norm hb
  · intro x
    rw [oGauge_eq_gauge, gauge_le_one_iff_mem_closure hconv hnhds, (gSet_isClosed a0 hcl).closure_eq]
    simp [gSet]



/-- A recorded point is a point of `Q` of norm at most `R`. -/
def BestOK (Q : Set (Fin d → ℝ)) (R : ℝ) (b : Option (Fin d → ℝ)) : Prop :=
  b = none ∨ ∃ μ, b = some μ ∧ μ ∈ Q ∧ oNorm μ ≤ R

/-- The invariant of ELL-cap on every input. -/
def LoopOK (Q : Set (Fin d → ℝ)) (R : ℝ) (o : Option (EllSt d ⊕ (Fin d → ℝ))) : Prop :=
  o = none ∨ (∃ μ, o = some (.inr μ) ∧ μ ∈ Q ∧ oNorm μ ≤ R) ∨ ∃ st, o = some (.inl st) ∧ BestOK Q R st.best

theorem ellRecord_ok (Q : Set (Fin d → ℝ)) (R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ)
    (b : Option (Fin d → ℝ)) (a : Fin d → ℝ) (hb : BestOK Q R b) (ha : a ∈ Q) (haR : oNorm a ≤ R) :
    BestOK Q R (ellRecord P w b a) := by
  unfold ellRecord
  rcases b with _ | b
  · exact Or.inr ⟨a, rfl, ha, haR⟩
  · dsimp only
    split_ifs
    · exact Or.inr ⟨a, rfl, ha, haR⟩
    · exact hb

theorem ellStep_ok (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) (st : EllSt d) (h : BestOK Q R st.best) :
    LoopOK Q R (ellStep Q a0 r R P w k st) := by
  unfold ellStep
  by_cases h1 : R < oNorm st.a
  · rw [ite_eq_left h1]; exact Or.inr (Or.inr ⟨_, rfl, h⟩)
  rw [ite_eq_right h1]
  by_cases h2 : st.a ∉ Q
  · rw [ite_eq_left h2]
    split
    · exact Or.inl rfl
    · split_ifs
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨_, rfl, h⟩)
  rw [ite_eq_right h2]
  have hQ : st.a ∈ Q := not_not.mp h2
  by_cases h3 : P *ᵥ (st.a - w) = 0
  · rw [ite_eq_left h3]; exact Or.inr (Or.inl ⟨st.a, rfl, hQ, not_lt.mp h1⟩)
  · rw [ite_eq_right h3]; exact Or.inr (Or.inr ⟨_, rfl, ellRecord_ok Q R P w _ _ h hQ (not_lt.mp h1)⟩)

theorem ellLoop_ok (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) (j : ℕ) : LoopOK Q R (ellLoop Q a0 r R P w k j) := by
  induction j with
  | zero => exact Or.inr (Or.inr ⟨_, rfl, Or.inl rfl⟩)
  | succ j ih =>
    simp only [ellLoop]
    rcases ih with h | ⟨μ, h, hμ⟩ | ⟨st, h, hst⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr (Or.inl ⟨μ, rfl, hμ⟩)
    · rw [h]; exact ellStep_ok Q a0 r R P w k st hst

/-- Proposition ELL-cap (a). -/
theorem propELLcap : PropELLcap := by
  intro d Q a0 r R P w e
  unfold ellCap
  split_ifs
  · exact Or.inl rfl
  · dsimp only
    rcases ellLoop_ok Q a0 r R P w (ellConsts r R P w e) (ellConsts r R P w e).N with h | ⟨μ, h, hμ⟩ | ⟨st, h, hst⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr ⟨μ, rfl, hμ⟩
    · rw [h]
      rcases hst with hb | ⟨μ, hb, hμ⟩
      · exact Or.inl hb
      · exact Or.inr ⟨μ, hb, hμ⟩


/-! ## Lemma H1 -/

theorem line_h1 (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (p l : ℝ) (hl : 0 < l) :
    ((φ (p + l + 4 * (l / 4)) - φ (p + l + 3 * (l / 4))) - (φ (p + l + l / 4) - φ (p + l))) / (l / 4) +
        ((φ (p + 2 * l + 4 * (l / 4)) - φ (p + 2 * l + 3 * (l / 4))) - (φ (p + 2 * l + l / 4) - φ (p + 2 * l))) /
          (l / 4) ≤
      ((φ (p + 4 * l) - φ (p + 3 * l)) - (φ (p + l) - φ p)) / l ∧
    φ (p + 3 * l) + φ (p + l) - 2 * φ (p + 2 * l) ≤ (φ (p + 4 * l) - φ (p + 3 * l)) - (φ (p + l) - φ p) := by
  have hm : 0 < l / 4 := by linarith
  have hm_ne : l / 4 ≠ 0 := by linarith
  have hl_ne : l ≠ 0 := by linarith
  have huniv (x : ℝ) : x ∈ Set.univ := Set.mem_univ _
  -- σ₁ = (φ(p+l) - φ p)/l
  -- σ₄ = (φ(p+4l) - φ(p+3l))/l
  -- τ₁ = (φ(p+l+l/4) - φ(p+l))/(l/4)
  -- τ₂ = (φ(p+l+2*(l/4)) - φ(p+l+l/4))/(l/4)
  -- τ₃ = (φ(p+l+3*(l/4)) - φ(p+l+2*(l/4)))/(l/4)
  -- τ₄ = (φ(p+2l) - φ(p+l+3*(l/4)))/(l/4)
  -- τ₅ = (φ(p+2l+l/4) - φ(p+2l))/(l/4)
  -- τ₆ = (φ(p+2l+2*(l/4)) - φ(p+2l+l/4))/(l/4)
  -- τ₇ = (φ(p+2l+3*(l/4)) - φ(p+2l+2*(l/4)))/(l/4)
  -- τ₈ = (φ(p+3l) - φ(p+2l+3*(l/4)))/(l/4)
  -- Chain: σ₁ ≤ τ₁ ≤ τ₂ ≤ τ₃ ≤ τ₄ ≤ τ₅ ≤ τ₆ ≤ τ₇ ≤ τ₈ ≤ σ₄
  have hσ1_τ1 : (φ (p + l) - φ p) / l ≤ (φ (p + l + l / 4) - φ (p + l)) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p) (y := p + l) (z := p + l + l / 4)
      (huniv p) (huniv (p + l + l / 4)) (by nlinarith) (by nlinarith)
    simpa [show (p + l) - p = l by ring, show (p + l + l / 4) - (p + l) = l / 4 by ring] using h
  have hτ1_τ2 : (φ (p + l + l / 4) - φ (p + l)) / (l / 4) ≤
      (φ (p + l + 2 * (l / 4)) - φ (p + l + l / 4)) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + l) (y := p + l + l / 4) (z := p + l + 2 * (l / 4))
      (huniv (p + l)) (huniv (p + l + 2 * (l / 4))) (by nlinarith) (by nlinarith)
    simpa [show (p + l + l / 4) - (p + l) = l / 4 by ring,
      show (p + l + 2 * (l / 4)) - (p + l + l / 4) = l / 4 by ring] using h
  have hτ2_τ3 : (φ (p + l + 2 * (l / 4)) - φ (p + l + l / 4)) / (l / 4) ≤
      (φ (p + l + 3 * (l / 4)) - φ (p + l + 2 * (l / 4))) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + l + l / 4) (y := p + l + 2 * (l / 4))
      (z := p + l + 3 * (l / 4)) (huniv (p + l + l / 4)) (huniv (p + l + 3 * (l / 4))) (by nlinarith) (by nlinarith)
    simpa [show (p + l + 2 * (l / 4)) - (p + l + l / 4) = l / 4 by ring,
      show (p + l + 3 * (l / 4)) - (p + l + 2 * (l / 4)) = l / 4 by ring] using h
  have hτ3_τ4 : (φ (p + l + 3 * (l / 4)) - φ (p + l + 2 * (l / 4))) / (l / 4) ≤
      (φ (p + 2 * l) - φ (p + l + 3 * (l / 4))) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + l + 2 * (l / 4)) (y := p + l + 3 * (l / 4))
      (z := p + 2 * l) (huniv (p + l + 2 * (l / 4))) (huniv (p + 2 * l)) (by nlinarith) (by nlinarith)
    simpa [show (p + l + 3 * (l / 4)) - (p + l + 2 * (l / 4)) = l / 4 by ring,
      show p + 2 * l - (p + l + 3 * (l / 4)) = l / 4 by ring] using h
  have hτ4_τ5 : (φ (p + 2 * l) - φ (p + l + 3 * (l / 4))) / (l / 4) ≤
      (φ (p + 2 * l + l / 4) - φ (p + 2 * l)) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + l + 3 * (l / 4)) (y := p + 2 * l)
      (z := p + 2 * l + l / 4) (huniv (p + l + 3 * (l / 4))) (huniv (p + 2 * l + l / 4)) (by nlinarith) (by nlinarith)
    simpa [show p + 2 * l - (p + l + 3 * (l / 4)) = l / 4 by ring,
      show (p + 2 * l + l / 4) - (p + 2 * l) = l / 4 by ring] using h
  have hτ5_τ6 : (φ (p + 2 * l + l / 4) - φ (p + 2 * l)) / (l / 4) ≤
      (φ (p + 2 * l + 2 * (l / 4)) - φ (p + 2 * l + l / 4)) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + 2 * l) (y := p + 2 * l + l / 4)
      (z := p + 2 * l + 2 * (l / 4)) (huniv (p + 2 * l)) (huniv (p + 2 * l + 2 * (l / 4))) (by nlinarith) (by nlinarith)
    simpa [show (p + 2 * l + l / 4) - (p + 2 * l) = l / 4 by ring,
      show (p + 2 * l + 2 * (l / 4)) - (p + 2 * l + l / 4) = l / 4 by ring] using h
  have hτ6_τ7 : (φ (p + 2 * l + 2 * (l / 4)) - φ (p + 2 * l + l / 4)) / (l / 4) ≤
      (φ (p + 2 * l + 3 * (l / 4)) - φ (p + 2 * l + 2 * (l / 4))) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + 2 * l + l / 4) (y := p + 2 * l + 2 * (l / 4))
      (z := p + 2 * l + 3 * (l / 4)) (huniv (p + 2 * l + l / 4)) (huniv (p + 2 * l + 3 * (l / 4))) (by nlinarith) (by nlinarith)
    simpa [show (p + 2 * l + 2 * (l / 4)) - (p + 2 * l + l / 4) = l / 4 by ring,
      show (p + 2 * l + 3 * (l / 4)) - (p + 2 * l + 2 * (l / 4)) = l / 4 by ring] using h
  have hτ7_τ8 : (φ (p + 2 * l + 3 * (l / 4)) - φ (p + 2 * l + 2 * (l / 4))) / (l / 4) ≤
      (φ (p + 3 * l) - φ (p + 2 * l + 3 * (l / 4))) / (l / 4) := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + 2 * l + 2 * (l / 4)) (y := p + 2 * l + 3 * (l / 4))
      (z := p + 3 * l) (huniv (p + 2 * l + 2 * (l / 4))) (huniv (p + 3 * l)) (by nlinarith) (by nlinarith)
    simpa [show (p + 2 * l + 3 * (l / 4)) - (p + 2 * l + 2 * (l / 4)) = l / 4 by ring,
      show p + 3 * l - (p + 2 * l + 3 * (l / 4)) = l / 4 by ring] using h
  have hτ8_σ4 : (φ (p + 3 * l) - φ (p + 2 * l + 3 * (l / 4))) / (l / 4) ≤
      (φ (p + 4 * l) - φ (p + 3 * l)) / l := by
    have h := ConvexOn.slope_mono_adjacent hφ (x := p + 2 * l + 3 * (l / 4)) (y := p + 3 * l)
      (z := p + 4 * l) (huniv (p + 2 * l + 3 * (l / 4))) (huniv (p + 4 * l)) (by nlinarith) (by nlinarith)
    simpa [show p + 3 * l - (p + 2 * l + 3 * (l / 4)) = l / 4 by ring,
      show (p + 4 * l) - (p + 3 * l) = l by ring] using h
  have h_first : ((φ (p + l + 4 * (l / 4)) - φ (p + l + 3 * (l / 4))) - (φ (p + l + l / 4) - φ (p + l))) / (l / 4) +
      ((φ (p + 2 * l + 4 * (l / 4)) - φ (p + 2 * l + 3 * (l / 4))) - (φ (p + 2 * l + l / 4) - φ (p + 2 * l))) /
        (l / 4) ≤
    ((φ (p + 4 * l) - φ (p + 3 * l)) - (φ (p + l) - φ p)) / l := by
    have h_ring1 : p + l + 4 * (l / 4) = p + 2 * l := by
      have h : 4 * (l / 4) = l := by field_simp
      calc
        p + l + 4 * (l / 4) = p + l + l := by rw [h]
        _ = p + 2 * l := by ring
    have h_ring2 : p + 2 * l + 4 * (l / 4) = p + 3 * l := by
      have h : 4 * (l / 4) = l := by field_simp
      calc
        p + 2 * l + 4 * (l / 4) = p + 2 * l + l := by rw [h]
        _ = p + 3 * l := by ring
    rw [h_ring1, h_ring2]
    set σ₁ := (φ (p + l) - φ p) / l with hσ₁
    set σ₄ := (φ (p + 4 * l) - φ (p + 3 * l)) / l with hσ₄
    set τ₁ := (φ (p + l + l / 4) - φ (p + l)) / (l / 4) with hτ₁
    set τ₄ := (φ (p + 2 * l) - φ (p + l + 3 * (l / 4))) / (l / 4) with hτ₄
    set τ₅ := (φ (p + 2 * l + l / 4) - φ (p + 2 * l)) / (l / 4) with hτ₅
    set τ₈ := (φ (p + 3 * l) - φ (p + 2 * l + 3 * (l / 4))) / (l / 4) with hτ₈
    have hgoal : (τ₄ - τ₁) + (τ₈ - τ₅) ≤ σ₄ - σ₁ := by
      have hτ4_le_τ5 : τ₄ ≤ τ₅ := hτ4_τ5
      have hσ1_le_τ1 : σ₁ ≤ τ₁ := hσ1_τ1
      have hτ8_le_σ4 : τ₈ ≤ σ₄ := hτ8_σ4
      linarith
    have h_first_term : ((φ (p + 2 * l) - φ (p + l + 3 * (l / 4))) - (φ (p + l + l / 4) - φ (p + l))) / (l / 4) = τ₄ - τ₁ := by
      rw [sub_div, ← hτ₄, ← hτ₁]
    have h_second_term : ((φ (p + 3 * l) - φ (p + 2 * l + 3 * (l / 4))) - (φ (p + 2 * l + l / 4) - φ (p + 2 * l))) / (l / 4) = τ₈ - τ₅ := by
      rw [sub_div, ← hτ₈, ← hτ₅]
    have h_rhs : ((φ (p + 4 * l) - φ (p + 3 * l)) - (φ (p + l) - φ p)) / l = σ₄ - σ₁ := by
      rw [sub_div, ← hσ₄, ← hσ₁]
    rw [h_first_term, h_second_term, h_rhs]
    exact hgoal
  have h_second : φ (p + 3 * l) + φ (p + l) - 2 * φ (p + 2 * l) ≤ (φ (p + 4 * l) - φ (p + 3 * l)) - (φ (p + l) - φ p) := by
    have hσ1_σ2 : (φ (p + l) - φ p) / l ≤ (φ (p + 2 * l) - φ (p + l)) / l := by
      have h := ConvexOn.slope_mono_adjacent hφ (x := p) (y := p + l) (z := p + 2 * l)
        (huniv p) (huniv (p + 2 * l)) (by nlinarith) (by nlinarith)
      simpa [show (p + l) - p = l by ring, show (p + 2 * l) - (p + l) = l by ring] using h
    have hσ3_σ4 : (φ (p + 3 * l) - φ (p + 2 * l)) / l ≤ (φ (p + 4 * l) - φ (p + 3 * l)) / l := by
      have h := ConvexOn.slope_mono_adjacent hφ (x := p + 2 * l) (y := p + 3 * l) (z := p + 4 * l)
        (huniv (p + 2 * l)) (huniv (p + 4 * l)) (by nlinarith) (by nlinarith)
      simpa [show (p + 3 * l) - (p + 2 * l) = l by ring, show (p + 4 * l) - (p + 3 * l) = l by ring] using h
    have h1 : φ (p + 3 * l) - φ (p + 2 * l) ≤ φ (p + 4 * l) - φ (p + 3 * l) := by
      field_simp [hl_ne] at hσ3_σ4
      simpa [mul_comm] using hσ3_σ4
    have h2 : -(φ (p + 2 * l) - φ (p + l)) ≤ -(φ (p + l) - φ p) := by
      field_simp [hl_ne] at hσ1_σ2
      have htemp : φ (p + l) - φ p ≤ φ (p + 2 * l) - φ (p + l) := by simpa [mul_comm] using hσ1_σ2
      linarith
    linarith
  exact And.intro h_first h_second

/-! ## Powers and the cap `J` -/

theorem two_pow_ceil_logb {x : ℝ} (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := by
  have h1 : Real.logb 2 x ≤ (⌈Real.logb 2 x⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
  calc x = (2 : ℝ) ^ Real.logb 2 x := h2
    _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := Real.rpow_natCast _ _

theorem four_rpow_neg_nat (n : ℕ) : (4 : ℝ) ^ (-(n : ℝ)) = 1 / 4 ^ n := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

theorem four_rpow_neg_succ (n : ℕ) : (4 : ℝ) ^ (-((n : ℝ) + 1)) = 1 / 4 ^ (n + 1) := by
  have : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this, four_rpow_neg_nat]

/-! ## Windows -/

/-- The exact spread of the window at `p` with spacing `m`. -/
noncomputable def exSpread (φ : ℝ → ℝ) (p m : ℝ) : ℝ := ((φ (p + 4 * m) - φ (p + 3 * m)) - (φ (p + m) - φ p)) / m

/-- The values of a window have their errors: the outer ones `τλ/100`, the inner ones `τλ/400`. -/
def WinOK (φ : ℝ → ℝ) (τ : ℝ) (W : LineWin) : Prop :=
  0 < W.lam ∧ |W.v0 - φ W.p0| ≤ τ * W.lam / 100 ∧ |W.v1 - φ (W.p0 + W.lam)| ≤ τ * W.lam / 400 ∧
    |W.v2 - φ (W.p0 + 2 * W.lam)| ≤ τ * W.lam / 400 ∧ |W.v3 - φ (W.p0 + 3 * W.lam)| ≤ τ * W.lam / 400 ∧
    |W.v4 - φ (W.p0 + 4 * W.lam)| ≤ τ * W.lam / 100

theorem spread_close {φ : ℝ → ℝ} {τ : ℝ} {W : LineWin} (h : WinOK φ τ W) :
    |W.spread - exSpread φ W.p0 W.lam| ≤ τ / 40 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  rw [abs_le] at h0 h1 h3 h4
  unfold LineWin.spread exSpread
  rw [← sub_div, abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_le]
  constructor <;> nlinarith

theorem sd_close {φ : ℝ → ℝ} {τ : ℝ} {W : LineWin} (h : WinOK φ τ W) :
    φ (W.p0 + 3 * W.lam) + φ (W.p0 + W.lam) - 2 * φ (W.p0 + 2 * W.lam) ≤ W.sd + τ * W.lam / 100 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  rw [abs_le] at h1 h2 h3
  unfold LineWin.sd
  linarith

/-- The invariant of LINE after `i` halvings. -/
def LineInv (φ : ℝ → ℝ) (L ℓ τ : ℝ) (i : ℕ) (W : LineWin) : Prop :=
  WinOK φ τ W ∧ W.lam = ℓ / 4 ^ (i + 1) ∧ 0 ≤ W.p0 ∧ W.p0 + 4 * W.lam ≤ ℓ ∧
    W.spread ≤ (2 * L + τ / 40) / 2 ^ i + 3 * τ / 40

/-- The accuracy of the evaluator at the queries of LINE, in the form the proof uses. -/
def EvOK (φ : ℝ → ℝ) (ℓ τ : ℝ) (J : ℕ) (ev1 : ℝ → ℝ → Option ℝ) : Prop :=
  ∀ s η, 0 ≤ s → s ≤ ℓ → τ * ℓ / (1600 * 4 ^ J) ≤ η → ∃ v, ev1 s η = some v ∧ |v - φ s| ≤ η

theorem lineHalve_ok {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {L ℓ τ : ℝ} {J i : ℕ} {ev1 : ℝ → ℝ → Option ℝ}
    (hτ : 0 < τ) (hℓ : 0 < ℓ) (hev : EvOK φ ℓ τ J ev1) (hiJ : i < J) {W : LineWin} (hW : LineInv φ L ℓ τ i W) :
    ∃ W', lineHalve ev1 τ W = some W' ∧ LineInv φ L ℓ τ (i + 1) W' := by
  obtain ⟨hok, hlam, hp0, hp4, hsp⟩ := hW
  have hl : 0 < W.lam := hok.1
  have herr : τ * ℓ / (1600 * 4 ^ J) ≤ τ * W.lam / 1600 := by
    rw [hlam]
    have h4 : (4 : ℝ) ^ (i + 1) ≤ 4 ^ J := pow_le_pow_right₀ (by norm_num) hiJ
    have : ℓ / 4 ^ J ≤ ℓ / 4 ^ (i + 1) := div_le_div_of_nonneg_left hℓ.le (by positivity) h4
    calc τ * ℓ / (1600 * 4 ^ J) = τ * (ℓ / 4 ^ J) / 1600 := by ring
      _ ≤ τ * (ℓ / 4 ^ (i + 1)) / 1600 := by gcongr
  have hpt : ∀ c : ℝ, 0 ≤ c → c ≤ 3 → 0 ≤ W.p0 + c * W.lam ∧ W.p0 + c * W.lam ≤ ℓ := fun c hc0 hc3 =>
    ⟨by positivity, by nlinarith⟩
  obtain ⟨u1, hu1, eu1⟩ := hev (W.p0 + W.lam + W.lam / 4) (τ * W.lam / 1600)
    (by linarith [(hpt (5 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (5 / 4) (by norm_num) (by norm_num)).2]) herr
  obtain ⟨u2, hu2, eu2⟩ := hev (W.p0 + W.lam + 2 * (W.lam / 4)) (τ * W.lam / 1600)
    (by linarith [(hpt (6 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (6 / 4) (by norm_num) (by norm_num)).2]) herr
  obtain ⟨u3, hu3, eu3⟩ := hev (W.p0 + W.lam + 3 * (W.lam / 4)) (τ * W.lam / 1600)
    (by linarith [(hpt (7 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (7 / 4) (by norm_num) (by norm_num)).2]) herr
  obtain ⟨u5, hu5, eu5⟩ := hev (W.p0 + 2 * W.lam + W.lam / 4) (τ * W.lam / 1600)
    (by linarith [(hpt (9 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (9 / 4) (by norm_num) (by norm_num)).2]) herr
  obtain ⟨u6, hu6, eu6⟩ := hev (W.p0 + 2 * W.lam + 2 * (W.lam / 4)) (τ * W.lam / 1600)
    (by linarith [(hpt (10 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (10 / 4) (by norm_num) (by norm_num)).2]) herr
  obtain ⟨u7, hu7, eu7⟩ := hev (W.p0 + 2 * W.lam + 3 * (W.lam / 4)) (τ * W.lam / 1600)
    (by linarith [(hpt (11 / 4) (by norm_num) (by norm_num)).1])
    (by linarith [(hpt (11 / 4) (by norm_num) (by norm_num)).2]) herr
  set A : LineWin := ⟨W.p0 + W.lam, W.lam / 4, W.v1, u1, u2, u3, W.v2⟩ with hA
  set B : LineWin := ⟨W.p0 + 2 * W.lam, W.lam / 4, W.v2, u5, u6, u7, W.v3⟩ with hB
  have hcalc : lineHalve ev1 τ W = some (if B.spread < A.spread then B else A) := by
    simp only [lineHalve, hu1, hu2, hu3, hu5, hu6, hu7, Option.bind_eq_bind, Option.bind_some]
    rfl
  obtain ⟨-, e0, e1, e2, e3, e4⟩ := hok
  have hAok : WinOK φ τ A := by
    refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hA]; linarith
    · simp only [hA]; rw [show W.p0 + W.lam + W.lam / 4 = W.p0 + W.lam + W.lam / 4 by rfl]; linarith
    · simp only [hA]; linarith
    · simp only [hA]; linarith
    · simp only [hA]; rw [show W.p0 + W.lam + 4 * (W.lam / 4) = W.p0 + 2 * W.lam by ring]; linarith
  have hBok : WinOK φ τ B := by
    refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hB]; linarith
    · simp only [hB]; linarith
    · simp only [hB]; linarith
    · simp only [hB]; linarith
    · simp only [hB]; rw [show W.p0 + 2 * W.lam + 4 * (W.lam / 4) = W.p0 + 3 * W.lam by ring]; linarith
  have hH1 := (line_h1 φ hφ W.p0 W.lam hl).1
  have cA := spread_close hAok
  have cB := spread_close hBok
  have cW := spread_close ⟨hl, e0, e1, e2, e3, e4⟩
  have hexA : exSpread φ A.p0 A.lam = ((φ (W.p0 + W.lam + 4 * (W.lam / 4)) - φ (W.p0 + W.lam + 3 * (W.lam / 4))) -
      (φ (W.p0 + W.lam + W.lam / 4) - φ (W.p0 + W.lam))) / (W.lam / 4) := rfl
  have hexB : exSpread φ B.p0 B.lam = ((φ (W.p0 + 2 * W.lam + 4 * (W.lam / 4)) -
      φ (W.p0 + 2 * W.lam + 3 * (W.lam / 4))) - (φ (W.p0 + 2 * W.lam + W.lam / 4) - φ (W.p0 + 2 * W.lam))) /
      (W.lam / 4) := rfl
  have hsum : A.spread + B.spread ≤ W.spread + 3 * τ / 40 := by
    rw [abs_le] at cA cB cW
    have : exSpread φ A.p0 A.lam + exSpread φ B.p0 B.lam ≤ exSpread φ W.p0 W.lam := by
      rw [hexA, hexB]; exact hH1
    linarith
  have hlam' : W.lam / 4 = ℓ / 4 ^ (i + 1 + 1) := by rw [hlam, pow_succ (4 : ℝ) (i + 1), div_div]
  have hsp' : ∀ X : LineWin, X.spread ≤ (A.spread + B.spread) / 2 →
      X.spread ≤ (2 * L + τ / 40) / 2 ^ (i + 1) + 3 * τ / 40 := by
    intro X hX
    rw [pow_succ]
    have : (2 * L + τ / 40) / (2 ^ i * 2) = ((2 * L + τ / 40) / 2 ^ i) / 2 := by ring
    rw [this]
    linarith
  refine ⟨_, hcalc, ?_⟩
  split_ifs with hBA
  · refine ⟨hBok, hlam', by simp only [hB]; positivity, ?_, hsp' B (by linarith)⟩
    simp only [hB]; nlinarith
  · refine ⟨hAok, hlam', by simp only [hA]; positivity, ?_, hsp' A (by linarith [not_lt.mp hBA])⟩
    simp only [hA]; nlinarith

theorem sd_close' {φ : ℝ → ℝ} {τ : ℝ} {W : LineWin} (h : WinOK φ τ W) :
    W.sd ≤ φ (W.p0 + 3 * W.lam) + φ (W.p0 + W.lam) - 2 * φ (W.p0 + 2 * W.lam) + τ * W.lam / 100 := by
  obtain ⟨hl, h0, h1, h2, h3, h4⟩ := h
  rw [abs_le] at h1 h2 h3
  unfold LineWin.sd
  linarith

/-- At depth `J` the stopping test of LINE passes. -/
theorem test_passes {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {L ℓ τ : ℝ} {J : ℕ} (hτ : 0 < τ) (hτL : τ ≤ L)
    (hJ : 8 * L / τ ≤ 2 ^ J) {W : LineWin} (hW : LineInv φ L ℓ τ J W) : W.sd ≤ τ * W.lam / 2 := by
  obtain ⟨hok, -, -, -, hsp⟩ := hW
  have hl : 0 < W.lam := hok.1
  have hL : 0 < L := lt_of_lt_of_le hτ hτL
  have c1 := sd_close' hok
  have c2 := (line_h1 φ hφ W.p0 W.lam hl).2
  have c3 := spread_close hok
  rw [abs_le] at c3
  have hex : φ (W.p0 + 4 * W.lam) - φ (W.p0 + 3 * W.lam) - (φ (W.p0 + W.lam) - φ W.p0) =
      W.lam * exSpread φ W.p0 W.lam := by
    unfold exSpread; field_simp
  have hX : 0 ≤ 2 * L + τ / 40 := by positivity
  have hpow : (2 * L + τ / 40) / 2 ^ J ≤ (2 * L + τ / 40) * τ / (8 * L) := by
    rw [mul_div_assoc]
    calc (2 * L + τ / 40) / 2 ^ J ≤ (2 * L + τ / 40) / (8 * L / τ) :=
          div_le_div_of_nonneg_left hX (by positivity) hJ
      _ = (2 * L + τ / 40) * (τ / (8 * L)) := by field_simp
  have hq : (2 * L + τ / 40) * τ / (8 * L) ≤ τ / 4 + τ / 320 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hS : W.spread ≤ τ / 4 + τ / 320 + 3 * τ / 40 := by linarith
  have : exSpread φ W.p0 W.lam ≤ τ / 4 + τ / 320 + 3 * τ / 40 + τ / 40 := by linarith
  have h5 : W.lam * exSpread φ W.p0 W.lam ≤ W.lam * (τ / 4 + τ / 320 + 3 * τ / 40 + τ / 40) :=
    mul_le_mul_of_nonneg_left this hl.le
  nlinarith

/-- A window that passes the test gives the conclusions of Lemma E.2. -/
theorem ret_ok {φ : ℝ → ℝ} {L ℓ τ : ℝ} {J i : ℕ} (hℓ : 0 < ℓ) (hiJ : i ≤ J) {W : LineWin}
    (hW : LineInv φ L ℓ τ i W) (htest : W.sd ≤ τ * W.lam / 2) :
    0 ≤ W.p0 + 2 * W.lam ∧ W.p0 + 2 * W.lam ≤ ℓ ∧ ℓ / 4 ^ (J + 1) ≤ W.lam ∧ W.lam ≤ ℓ / 4 ∧
      φ (W.p0 + 2 * W.lam + W.lam) + φ (W.p0 + 2 * W.lam - W.lam) - 2 * φ (W.p0 + 2 * W.lam) ≤
        τ * W.lam / 2 + τ * W.lam / 100 := by
  obtain ⟨hok, hlam, hp0, hp4, -⟩ := hW
  have hl : 0 < W.lam := hok.1
  have c := sd_close hok
  refine ⟨by positivity, by linarith, ?_, ?_, ?_⟩
  · rw [hlam]
    exact div_le_div_of_nonneg_left hℓ.le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  · rw [hlam]
    exact div_le_div_of_nonneg_left hℓ.le (by norm_num) (le_self_pow₀ (by norm_num) (by omega))
  · rw [show W.p0 + 2 * W.lam + W.lam = W.p0 + 3 * W.lam by ring,
      show W.p0 + 2 * W.lam - W.lam = W.p0 + W.lam by ring]
    linarith

/-- The loop of LINE returns, with the conclusions of Lemma E.2. -/
theorem lineLoop_ok {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {L ℓ τ : ℝ} {J : ℕ} {ev1 : ℝ → ℝ → Option ℝ}
    (hτ : 0 < τ) (hτL : τ ≤ L) (hℓ : 0 < ℓ) (hev : EvOK φ ℓ τ J ev1) (hJ : 8 * L / τ ≤ 2 ^ J) :
    ∀ j i W, i + j = J → LineInv φ L ℓ τ i W → ∃ s δ, lineLoop ev1 τ j W = some (s, δ) ∧ 0 ≤ s ∧ s ≤ ℓ ∧
      ℓ / 4 ^ (J + 1) ≤ δ ∧ δ ≤ ℓ / 4 ∧ φ (s + δ) + φ (s - δ) - 2 * φ s ≤ τ * δ / 2 + τ * δ / 100 := by
  intro j
  induction j with
  | zero =>
    intro i W hij hW
    have hiJ : i = J := by omega
    subst hiJ
    have htest := test_passes hφ hτ hτL hJ hW
    refine ⟨_, _, ?_, ret_ok hℓ le_rfl hW htest⟩
    rw [lineLoop, ite_eq_left htest]
  | succ j ih =>
    intro i W hij hW
    by_cases htest : W.sd ≤ τ * W.lam / 2
    · refine ⟨_, _, ?_, ret_ok hℓ (by omega) hW htest⟩
      rw [lineLoop, ite_eq_left htest]
    · obtain ⟨W', hW', hinv⟩ := lineHalve_ok hφ hτ hℓ hev (by omega : i < J) hW
      obtain ⟨s, δ, hs, hrest⟩ := ih (i + 1) W' (by omega) hinv
      refine ⟨s, δ, ?_, hrest⟩
      rw [lineLoop, ite_eq_right htest]
      simp only [hW', Option.bind_eq_bind, Option.bind_some]
      exact hs

/-- The first window of LINE. -/
theorem lineFirst_ok {φ : ℝ → ℝ} {L ℓ τ : ℝ} {J : ℕ} {ev1 : ℝ → ℝ → Option ℝ}
    (hLip : ∀ x y, |φ x - φ y| ≤ L * |x - y|) (hτ : 0 < τ) (hℓ : 0 < ℓ) (hev : EvOK φ ℓ τ J ev1) :
    ∃ W, lineFirst ev1 ℓ τ = some W ∧ LineInv φ L ℓ τ 0 W := by
  have herr : τ * ℓ / (1600 * 4 ^ J) ≤ τ * (ℓ / 4) / 400 := by
    have h4 : (1 : ℝ) ≤ 4 ^ J := one_le_pow₀ (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hτ hℓ]
  obtain ⟨v0, h0, e0⟩ := hev 0 _ le_rfl hℓ.le herr
  obtain ⟨v1, h1, e1⟩ := hev (ℓ / 4) _ (by positivity) (by linarith) herr
  obtain ⟨v2, h2, e2⟩ := hev (2 * (ℓ / 4)) _ (by positivity) (by linarith) herr
  obtain ⟨v3, h3, e3⟩ := hev (3 * (ℓ / 4)) _ (by positivity) (by linarith) herr
  obtain ⟨v4, h4, e4⟩ := hev (4 * (ℓ / 4)) _ (by positivity) (by linarith) herr
  refine ⟨⟨0, ℓ / 4, v0, v1, v2, v3, v4⟩, ?_, ?_⟩
  · simp only [lineFirst, h0, h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_some]
    rfl
  · have hl : (0 : ℝ) < ℓ / 4 := by positivity
    have hτl : 0 ≤ τ * (ℓ / 4) := by positivity
    have hok : WinOK φ τ ⟨0, ℓ / 4, v0, v1, v2, v3, v4⟩ := by
      refine ⟨hl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [zero_add] <;> linarith
    refine ⟨hok, by simp, le_rfl, by simp only; linarith, ?_⟩
    have c := spread_close hok
    rw [abs_le] at c
    have hex : exSpread φ 0 (ℓ / 4) ≤ 2 * L := by
      unfold exSpread
      rw [div_le_iff₀ hl]
      have a1 := hLip (0 + 4 * (ℓ / 4)) (0 + 3 * (ℓ / 4))
      have a2 := hLip (0 + ℓ / 4) 0
      rw [abs_le] at a1 a2
      have b1 : |0 + 4 * (ℓ / 4) - (0 + 3 * (ℓ / 4))| = ℓ / 4 := by
        rw [show (0 : ℝ) + 4 * (ℓ / 4) - (0 + 3 * (ℓ / 4)) = ℓ / 4 by ring, abs_of_pos hl]
      have b2 : |0 + ℓ / 4 - 0| = ℓ / 4 := by rw [show (0 : ℝ) + ℓ / 4 - 0 = ℓ / 4 by ring, abs_of_pos hl]
      rw [b1] at a1; rw [b2] at a2
      linarith
    simp only [pow_zero, div_one]
    linarith

/-- Lemma E.2. -/
theorem lemmaLINE : LemmaLINE := by
  intro φ L ℓ τ ev1 hφ hLip hτ hτL hℓ hev
  set J := ⌈Real.logb 2 (8 * L / τ)⌉₊ with hJdef
  have hL : 0 < L := lt_of_lt_of_le hτ hτL
  have hJ : 8 * L / τ ≤ 2 ^ J := two_pow_ceil_logb (by positivity)
  have hev' : EvOK φ ℓ τ J ev1 := by
    intro s η hs0 hsl hη
    apply hev s η hs0 hsl
    rw [four_rpow_neg_nat]
    convert hη using 1
    field_simp
  obtain ⟨W, hW1, hW⟩ := lineFirst_ok hLip hτ hℓ hev'
  obtain ⟨s, δ, hs, h0, h1, h2, h3, h4⟩ := lineLoop_ok hφ hτ hτL hℓ hev' hJ J 0 W (by omega) hW
  refine ⟨s, δ, ?_, h0, h1, ?_, h3, h4⟩
  · rw [line, hW1]
    simpa only [Option.bind_eq_bind, Option.bind_some] using hs
  · rw [four_rpow_neg_succ]
    convert h2 using 1
    ring

/-! ## Procedure SEP -/

theorem fd_exact {d : ℕ} (h : (Fin d → ℝ) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (y δ : Fin d → ℝ) (hδ : ∀ i, 0 < δ i) (z : Fin d → ℝ) :
    h y + ∑ i, ((z i - y i) * ((h (y + δ i • oUnit i) - h (y - δ i • oUnit i)) / (2 * δ i)) -
      |z i - y i| * ((h (y + δ i • oUnit i) + h (y - δ i • oUnit i) - 2 * h y) / (2 * δ i))) ≤ h z := by
  classical
  set w : Fin d → ℝ := fun i => |z i - y i| / δ i with hw
  set ym : Fin d → (Fin d → ℝ) := fun i => if 0 ≤ z i - y i then y - δ i • oUnit i else y + δ i • oUnit i
    with hym
  set W := ∑ i, w i with hW
  have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (abs_nonneg _) (hδ i).le
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => hw0 i
  have hterm : ∀ i, (z i - y i) * ((h (y + δ i • oUnit i) - h (y - δ i • oUnit i)) / (2 * δ i)) -
      |z i - y i| * ((h (y + δ i • oUnit i) + h (y - δ i • oUnit i) - 2 * h y) / (2 * δ i)) =
      w i * (h y - h (ym i)) := by
    intro i
    have hδi := (hδ i).ne'
    by_cases hti : 0 ≤ z i - y i
    · simp only [hw, hym, hti, ite_true, abs_of_nonneg hti]
      field_simp; ring
    · simp only [hw, hym, hti, ite_false, abs_of_neg (not_le.mp hti)]
      field_simp; ring
  have hvec : ∀ i, w i • ym i = w i • y - (z i - y i) • oUnit i := by
    intro i
    have hδi := (hδ i).ne'
    by_cases hti : 0 ≤ z i - y i
    · simp only [hw, hym, hti, ite_true, abs_of_nonneg hti, smul_sub, smul_smul, div_mul_cancel₀ _ hδi]
    · simp only [hw, hym, hti, ite_false, abs_of_neg (not_le.mp hti), smul_add, smul_smul]
      rw [neg_div, neg_mul, div_mul_cancel₀ _ hδi]
      module
  have hsumt : ∑ i, (z i - y i) • oUnit i = z - y := by
    ext j; simp [oUnit, Finset.sum_apply, Pi.single_apply]
  have hW1 : 0 < 1 + W := by linarith
  set c : Option (Fin d) → ℝ := fun o => o.elim (1 + W)⁻¹ (fun i => (1 + W)⁻¹ * w i) with hc
  set p : Option (Fin d) → (Fin d → ℝ) := fun o => o.elim z ym with hp
  have hc0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ c o := by
    intro o _
    cases o with
    | none => exact (inv_pos.mpr hW1).le
    | some i => exact mul_nonneg (inv_pos.mpr hW1).le (hw0 i)
  have hc1 : ∑ o, c o = 1 := by
    rw [Fintype.sum_option]
    simp only [hc, Option.elim]
    rw [← Finset.mul_sum, ← hW, ← mul_one_add, inv_mul_cancel₀ hW1.ne']
  have hpt : ∑ o, c o • p o = y := by
    rw [Fintype.sum_option]
    simp only [hc, hp, Option.elim]
    simp_rw [mul_smul, ← Finset.smul_sum, hvec, Finset.sum_sub_distrib, hsumt, ← Finset.sum_smul, ← hW]
    rw [← smul_add, show z + (W • y - (z - y)) = (1 + W) • y by rw [add_smul, one_smul]; abel, smul_smul,
      inv_mul_cancel₀ hW1.ne', one_smul]
  have hJ := hh.map_sum_le hc0 hc1 (fun o _ => Set.mem_univ (p o))
  rw [hpt, Fintype.sum_option] at hJ
  simp only [hc, hp, Option.elim, smul_eq_mul] at hJ
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hmul : (1 + W) * h y ≤ h z + ∑ i, w i * h (ym i) := by
    have h1 := mul_le_mul_of_nonneg_left hJ hW1.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hW1.ne', one_mul, Finset.mul_sum] at h1
    simpa only [← mul_assoc, mul_inv_cancel₀ hW1.ne', one_mul] using h1
  have hsplit : ∑ i, w i * (h y - h (ym i)) = W * h y - ∑ i, w i * h (ym i) := by
    rw [hW, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  linarith

/-- The exact second difference of `h` at `y` along `e_i` with step `δ`. -/
noncomputable def sdiff (h : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (δ : ℝ) (i : Fin d) : ℝ :=
  h (y + δ • oUnit i) + h (y - δ • oUnit i) - 2 * h y

theorem sdiff_move {h : (Fin d → ℝ) → ℝ} {L : ℝ} (hLip : ∀ x y, |h x - h y| ≤ L * oNorm (x - y))
    (y y' : Fin d → ℝ) (δ : ℝ) (i : Fin d) : sdiff h y' δ i ≤ sdiff h y δ i + 4 * L * oNorm (y' - y) := by
  unfold sdiff
  have a1 := hLip (y' + δ • oUnit i) (y + δ • oUnit i)
  have a2 := hLip (y' - δ • oUnit i) (y - δ • oUnit i)
  have a3 := hLip y y'
  rw [show y' + δ • oUnit i - (y + δ • oUnit i) = y' - y by abel] at a1
  rw [show y' - δ • oUnit i - (y - δ • oUnit i) = y' - y by abel] at a2
  rw [oNorm_sub_comm] at a3
  rw [abs_le] at a1 a2 a3
  linarith

/-- The invariant of SEP after `k` coordinates. -/
def SepInv (h : (Fin d → ℝ) → ℝ) (L τ ℓ1 : ℝ) (J : ℕ) (y0 : Fin d → ℝ) (k : ℕ) (st : SepSt d) : Prop :=
  0 < st.2.1 ∧ ℓ1 / 2 ^ (3 * k * (J + 1)) ≤ st.2.1 ∧ oNorm (st.1 - y0) ≤ 64 / 63 * (ℓ1 - st.2.1) ∧
    ∀ i : Fin d, (i : ℕ) < k → 0 < st.2.2 i ∧ st.2.2 i ≤ ℓ1 / 4 ∧
      τ * ℓ1 / (1600 * 2 ^ (3 * d * (J + 1))) ≤ τ * st.2.2 i / 400 ∧
      sdiff h st.1 (st.2.2 i) i + 64 / 63 * (4 * L) * st.2.1 ≤
        51 / 100 * (τ * st.2.2 i) + 64 / 63 * (τ * st.2.2 i / 4)

/-- The accuracy of the evaluator at the queries of SEP, in the form the proof uses. -/
def SepEvOK (h : (Fin d → ℝ) → ℝ) (τ ℓ1 : ℝ) (J : ℕ) (y0 : Fin d → ℝ) (ev : (Fin d → ℝ) → ℝ → Option ℝ) :
    Prop :=
  ∀ x η, oNorm (x - y0) ≤ 2 * ℓ1 → τ * ℓ1 / (1600 * 2 ^ (3 * d * (J + 1))) ≤ η →
    ∃ v, ev x η = some v ∧ |v - h x| ≤ η

/-- The least error of SEP: `τ ℓ₁/(1600 · 2^{3d(J+1)}) ≤ τ ℓ/(1600 · 4^J)` when `ℓ ≥ ℓ₁/2^{3k(J+1)}`, `k < d`. -/
theorem sep_err_le {τ ℓ1 ℓ : ℝ} {d k J : ℕ} (hτ : 0 < τ) (hℓ1 : 0 < ℓ1) (hk : k < d)
    (hℓ : ℓ1 / 2 ^ (3 * k * (J + 1)) ≤ ℓ) :
    τ * ℓ1 / (1600 * 2 ^ (3 * d * (J + 1))) ≤ τ * ℓ / (1600 * 4 ^ J) := by
  have h4 : (4 : ℝ) ^ J = 2 ^ (2 * J) := by rw [pow_mul]; norm_num
  have hexp : 2 * J + 3 * k * (J + 1) ≤ 3 * d * (J + 1) := by
    have : (k + 1) * (J + 1) ≤ d * (J + 1) := Nat.mul_le_mul_right _ hk
    nlinarith
  have hp : (2 : ℝ) ^ (2 * J) * 2 ^ (3 * k * (J + 1)) ≤ 2 ^ (3 * d * (J + 1)) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hexp
  have hpos1 : (0 : ℝ) < 2 ^ (3 * k * (J + 1)) := by positivity
  have hpos2 : (0 : ℝ) < 2 ^ (2 * J) := by positivity
  rw [h4]
  calc τ * ℓ1 / (1600 * 2 ^ (3 * d * (J + 1))) ≤ τ * ℓ1 / (1600 * (2 ^ (2 * J) * 2 ^ (3 * k * (J + 1)))) := by
        gcongr
    _ = τ * (ℓ1 / 2 ^ (3 * k * (J + 1))) / (1600 * 2 ^ (2 * J)) := by field_simp
    _ ≤ τ * ℓ / (1600 * 2 ^ (2 * J)) := by gcongr

theorem sepCoord_ok {h : (Fin d → ℝ) → ℝ} {L τ ℓ1 : ℝ} {y0 : Fin d → ℝ} {ev : (Fin d → ℝ) → ℝ → Option ℝ}
    (hh : ConvexOn ℝ Set.univ h) (hLip : ∀ x y, |h x - h y| ≤ L * oNorm (x - y)) (hτ : 0 < τ) (hτL : τ ≤ L)
    (hℓ1 : 0 < ℓ1) (hev : SepEvOK h τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 ev) (k : ℕ) (hk : k < d) (st : SepSt d)
    (hst : SepInv h L τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 k st) :
    ∃ st', sepCoord ev τ L ⌈Real.logb 2 (8 * L / τ)⌉₊ ⟨k, hk⟩ st = some st' ∧
      SepInv h L τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 (k + 1) st' := by
  set J := ⌈Real.logb 2 (8 * L / τ)⌉₊ with hJdef
  have hL : 0 < L := lt_of_lt_of_le hτ hτL
  have hJ : 8 * L / τ ≤ 2 ^ J := two_pow_ceil_logb (by positivity)
  obtain ⟨y, ℓ', δv⟩ := st
  obtain ⟨hℓ', hℓ'low, hy, hold⟩ := hst
  simp only at hℓ' hℓ'low hy hold
  have hℓ'1 : ℓ' ≤ ℓ1 := by have := oNorm_nonneg (y - y0); linarith
  set e : Fin d → ℝ := oUnit ⟨k, hk⟩ with he
  set φ : ℝ → ℝ := fun t => h (y + t • e) with hφdef
  have hφ : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
    have := hh.2 (Set.mem_univ (y + a • e)) (Set.mem_univ (y + b • e)) hp hq hpq
    simp only [hφdef, smul_eq_mul]
    convert this using 2
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hpq, one_smul, smul_smul, smul_smul, ← add_smul]
  have hφL : ∀ a b, |φ a - φ b| ≤ L * |a - b| := by
    intro a b
    have := hLip (y + a • e) (y + b • e)
    rwa [show y + a • e - (y + b • e) = (a - b) • e by rw [sub_smul]; abel, oNorm_smul, he, oNorm_oUnit,
      mul_one] at this
  have herrJ := sep_err_le (J := J) hτ hℓ1 hk hℓ'low
  obtain ⟨s, δ, hline, hs0, hsℓ, hδlow, hδup, hsd⟩ := lemmaLINE φ L ℓ' τ (fun t η => ev (y + t • e) η) hφ hφL hτ
    hτL hℓ' (by
      intro t η ht0 htℓ hη
      have hη' : τ * ℓ1 / (1600 * 2 ^ (3 * d * (J + 1))) ≤ η := by
        refine herrJ.trans (le_trans (le_of_eq ?_) hη)
        rw [four_rpow_neg_nat, ← hJdef]; field_simp
      apply hev (y + t • e) η _ hη'
      calc oNorm (y + t • e - y0) ≤ oNorm (y - y0) + oNorm (t • e) := by
            rw [show y + t • e - y0 = (y - y0) + t • e by abel]; exact oNorm_add_le _ _
        _ ≤ 64 / 63 * (ℓ1 - ℓ') + ℓ' := by
            rw [oNorm_smul, he, oNorm_oUnit, mul_one, abs_of_nonneg ht0]; linarith
        _ ≤ 2 * ℓ1 := by linarith)
  rw [four_rpow_neg_succ, ← hJdef] at hδlow
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδlow
  set ℓ'' := τ * δ / (16 * L) with hℓ''
  have hℓ''pos : 0 < ℓ'' := by positivity
  have hℓ''64 : 64 * ℓ'' ≤ ℓ' := by
    rw [hℓ'']
    have : τ * δ ≤ L * δ := mul_le_mul_of_nonneg_right hτL hδpos.le
    rw [show 64 * (τ * δ / (16 * L)) = 4 * (τ * δ) / L by field_simp; ring, div_le_iff₀ hL]
    nlinarith
  refine ⟨(y + s • e, ℓ'', Function.update δv ⟨k, hk⟩ δ), ?_, ?_⟩
  · simp only [sepCoord, Option.bind_eq_bind]
    rw [show (fun s η => ev (y + s • oUnit ⟨k, hk⟩) η) = (fun t η => ev (y + t • e) η) from rfl, hline]
    rfl
  refine ⟨hℓ''pos, ?_, ?_, ?_⟩
  · -- `ℓ'' ≥ ℓ' 2^{-3(J+1)} ≥ ℓ₁ 2^{-3(k+1)(J+1)}`
    simp only
    have hJ1 : 16 * L / τ ≤ 2 ^ (J + 1) := by
      rw [pow_succ]; have : 16 * L / τ = 2 * (8 * L / τ) := by ring
      rw [this]; linarith
    have h1 : ℓ' / (4 ^ (J + 1) * 2 ^ (J + 1)) ≤ ℓ'' := by
      rw [hℓ'', div_le_div_iff₀ (by positivity) (by positivity)]
      have a : ℓ' / 4 ^ (J + 1) ≤ δ := by simpa [one_div, div_eq_mul_inv] using hδlow
      rw [div_le_iff₀ (by positivity)] at a
      have b : 16 * L ≤ 2 ^ (J + 1) * τ := by rwa [div_le_iff₀ hτ] at hJ1
      nlinarith [mul_le_mul_of_nonneg_left b (le_of_lt (show (0 : ℝ) < ℓ' by positivity)),
        pow_pos (show (0 : ℝ) < 4 by norm_num) (J + 1)]
    have h2 : (4 : ℝ) ^ (J + 1) * 2 ^ (J + 1) = 2 ^ (3 * (J + 1)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; ring
    rw [h2] at h1
    refine le_trans ?_ h1
    rw [show 3 * (k + 1) * (J + 1) = 3 * k * (J + 1) + 3 * (J + 1) by ring, pow_add, ← div_div]
    gcongr
  · simp only
    calc oNorm (y + s • e - y0) ≤ oNorm (y - y0) + oNorm (s • e) := by
          rw [show y + s • e - y0 = (y - y0) + s • e by abel]; exact oNorm_add_le _ _
      _ ≤ 64 / 63 * (ℓ1 - ℓ') + ℓ' := by rw [oNorm_smul, he, oNorm_oUnit, mul_one, abs_of_nonneg hs0]; linarith
      _ ≤ 64 / 63 * (ℓ1 - ℓ'') := by linarith
  · intro i hi
    simp only
    by_cases hik : i = ⟨k, hk⟩
    · subst hik
      rw [Function.update_self]
      refine ⟨hδpos, by linarith, ?_, ?_⟩
      · refine herrJ.trans (le_of_eq_of_le ?_ (?_ : τ * (ℓ' / 4 ^ (J + 1)) / 400 ≤ τ * δ / 400))
        · rw [pow_succ]; field_simp; ring
        · have : ℓ' / 4 ^ (J + 1) ≤ δ := by simpa [one_div, div_eq_mul_inv] using hδlow
          gcongr
      · have hsd' : sdiff h (y + s • e) δ ⟨k, hk⟩ = φ (s + δ) + φ (s - δ) - 2 * φ s := by
          simp only [sdiff, hφdef, ← he]
          rw [show y + s • e + δ • e = y + (s + δ) • e by rw [add_smul]; abel,
            show y + s • e - δ • e = y + (s - δ) • e by rw [sub_smul]; abel]
        rw [hsd', hℓ'']
        have : 64 / 63 * (4 * L) * (τ * δ / (16 * L)) = 64 / 63 * (τ * δ / 4) := by field_simp; ring
        rw [this]
        linarith
    · have hik' : (i : ℕ) < k := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h'
        · exact absurd (Fin.ext h') hik
      rw [Function.update_of_ne hik]
      obtain ⟨o1, o2, o3, o4⟩ := hold i hik'
      refine ⟨o1, o2, o3, ?_⟩
      have hmove := sdiff_move hLip y (y + s • e) (δv i) i
      rw [show y + s • e - y = s • e by abel, oNorm_smul, he, oNorm_oUnit, mul_one, abs_of_nonneg hs0] at hmove
      have : 4 * L * s ≤ 4 * L * ℓ' := by gcongr
      nlinarith

theorem sepCoords_ok {h : (Fin d → ℝ) → ℝ} {L τ ℓ1 : ℝ} {y0 : Fin d → ℝ} {ev : (Fin d → ℝ) → ℝ → Option ℝ}
    (hh : ConvexOn ℝ Set.univ h) (hLip : ∀ x y, |h x - h y| ≤ L * oNorm (x - y)) (hτ : 0 < τ) (hτL : τ ≤ L)
    (hℓ1 : 0 < ℓ1) (hev : SepEvOK h τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 ev) :
    ∀ k, k ≤ d → ∃ st, sepCoords ev y0 τ ℓ1 L ⌈Real.logb 2 (8 * L / τ)⌉₊ k = some st ∧
      SepInv h L τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 k st := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨(y0, ℓ1, 0), rfl, hℓ1, by simp, by simp [oNorm_zero], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨st, hst, hinv⟩ := ih (by omega)
    have hkd : k < d := by omega
    obtain ⟨st', hst', hinv'⟩ := sepCoord_ok hh hLip hτ hτL hℓ1 hev k hkd st hinv
    refine ⟨st', ?_, hinv'⟩
    simp only [sepCoords, hst, Option.bind_eq_bind, Option.bind_some, dite_eq_left hkd]
    exact hst'

theorem oValsAll_eq {ev : (Fin d → ℝ) → ℝ → Option ℝ} {x : Fin d → Fin d → ℝ} {η : Fin d → ℝ} {v : Fin d → ℝ}
    (hv : ∀ i, ev (x i) (η i) = some (v i)) : oValsAll ev x η = some v := by
  unfold oValsAll
  rw [dite_eq_left (fun i => by rw [hv i]; rfl)]
  congr 1
  funext i
  simp [hv i]

/-- Lemma E.3. -/
theorem lemmaSEP : LemmaSEP := by
  intro d h L τ ℓ1 y0 ev hd hh hLip hτ hτL hℓ1 hev
  have hL : 0 < L := lt_of_lt_of_le hτ hτL
  have hev' : SepEvOK h τ ℓ1 ⌈Real.logb 2 (8 * L / τ)⌉₊ y0 ev := by
    intro x η hx hη
    apply hev x η hx
    refine le_trans (le_of_eq ?_) hη
    rw [Real.rpow_neg (by norm_num)]
    have : (3 * (d : ℝ) * ((⌈Real.logb 2 (8 * L / τ)⌉₊ : ℝ) + 1)) =
        ((3 * d * (⌈Real.logb 2 (8 * L / τ)⌉₊ + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
    field_simp
  obtain ⟨st, hst, hinv⟩ := sepCoords_ok hh hLip hτ hτL hℓ1 hev' d le_rfl
  obtain ⟨y, ℓ', δv⟩ := st
  obtain ⟨hℓ', -, hy, hall⟩ := hinv
  simp only at hℓ' hy hall
  have hℓ'1 : ℓ' ≤ ℓ1 := by have := oNorm_nonneg (y - y0); linarith
  have hy2 : oNorm (y - y0) ≤ 64 / 63 * ℓ1 := by linarith
  set ηm := τ * ℓ1 / (1600 * 2 ^ (3 * d * (⌈Real.logb 2 (8 * L / τ)⌉₊ + 1))) with hηm
  -- the value at `y`
  have hd0 : 0 < d := hd
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) ⟨⟨0, hd0⟩, Finset.mem_univ _⟩ δv
  have hmin : oMin δv = δv i0 := by unfold oMin; rw [dite_eq_left hd0]; exact hi0
  obtain ⟨v0, hv0, -⟩ := hev' y (τ * oMin δv / 400) (by linarith) (by rw [hmin]; exact (hall i0 i0.2).2.2.1)
  -- the values at `y ± δ_i e_i`
  have hpt : ∀ i : Fin d, ∀ c : ℝ, |c| ≤ δv i → oNorm (y + c • oUnit i - y0) ≤ 2 * ℓ1 := by
    intro i c hc
    calc oNorm (y + c • oUnit i - y0) ≤ oNorm (y - y0) + oNorm (c • oUnit i) := by
          rw [show y + c • oUnit i - y0 = (y - y0) + c • oUnit i by abel]; exact oNorm_add_le _ _
      _ ≤ 64 / 63 * ℓ1 + ℓ1 / 4 := by
          rw [oNorm_smul, oNorm_oUnit, mul_one]; linarith [(hall i i.2).2.1]
      _ ≤ 2 * ℓ1 := by linarith
  have hp : ∀ i : Fin d, ∃ v, ev (y + δv i • oUnit i) (τ * δv i / 400) = some v ∧
      |v - h (y + δv i • oUnit i)| ≤ τ * δv i / 400 := fun i =>
    hev' _ _ (hpt i (δv i) (by rw [abs_of_pos (hall i i.2).1])) (hall i i.2).2.2.1
  have hm : ∀ i : Fin d, ∃ v, ev (y - δv i • oUnit i) (τ * δv i / 400) = some v ∧
      |v - h (y - δv i • oUnit i)| ≤ τ * δv i / 400 := fun i =>
    hev' _ _ (by have := hpt i (-δv i) (by rw [abs_neg, abs_of_pos (hall i i.2).1])
                 rwa [neg_smul, ← sub_eq_add_neg] at this) (hall i i.2).2.2.1
  choose vp hvp evp using hp
  choose vm hvm evm using hm
  refine ⟨y, fun i => (vp i - vm i) / (2 * δv i), ?_, hy2, ?_⟩
  · simp only [sep, hst, Option.bind_eq_bind, Option.bind_some, hv0, oValsAll_eq hvp, oValsAll_eq hvm]
    rfl
  · intro z
    have hfd := fd_exact h hh y δv (fun i => (hall i i.2).1) z
    have hterm : ∀ i : Fin d, (vp i - vm i) / (2 * δv i) * (z i - y i) - τ * |z i - y i| ≤
        (z i - y i) * ((h (y + δv i • oUnit i) - h (y - δv i • oUnit i)) / (2 * δv i)) -
          |z i - y i| * ((h (y + δv i • oUnit i) + h (y - δv i • oUnit i) - 2 * h y) / (2 * δv i)) := by
      intro i
      obtain ⟨o1, -, -, o4⟩ := hall i i.2
      have hδ2 : 0 < 2 * δv i := by positivity
      set t := z i - y i
      set gex := (h (y + δv i • oUnit i) - h (y - δv i • oUnit i)) / (2 * δv i)
      set D := h (y + δv i • oUnit i) + h (y - δv i • oUnit i) - 2 * h y
      have hD : D ≤ 51 / 100 * (τ * δv i) + 64 / 63 * (τ * δv i / 4) := by
        have : 0 ≤ 64 / 63 * (4 * L) * ℓ' := by positivity
        unfold sdiff at o4; linarith
      have hDq : D / (2 * δv i) ≤ 383 / 1000 * τ := by
        rw [div_le_iff₀ hδ2]; nlinarith
      have hg : |(vp i - vm i) / (2 * δv i) - gex| ≤ τ / 400 := by
        have e1 := evp i; have e2 := evm i
        rw [abs_le] at e1 e2
        rw [← sub_div, abs_div, abs_of_pos hδ2, div_le_iff₀ hδ2, abs_le]
        constructor <;> nlinarith
      have ht1 : (vp i - vm i) / (2 * δv i) * t ≤ gex * t + τ / 400 * |t| := by
        have : ((vp i - vm i) / (2 * δv i) - gex) * t ≤ τ / 400 * |t| := by
          calc ((vp i - vm i) / (2 * δv i) - gex) * t ≤ |((vp i - vm i) / (2 * δv i) - gex) * t| := le_abs_self _
            _ = |(vp i - vm i) / (2 * δv i) - gex| * |t| := abs_mul _ _
            _ ≤ τ / 400 * |t| := by gcongr
        linarith
      have ht2 : |t| * (D / (2 * δv i)) ≤ |t| * (383 / 1000 * τ) := by gcongr
      have hta : 0 ≤ |t| := abs_nonneg t
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have hdot : (fun i => (vp i - vm i) / (2 * δv i)) ⬝ᵥ (z - y) =
        ∑ i, (vp i - vm i) / (2 * δv i) * (z i - y i) := by simp [dotProduct]
    rw [hdot]
    linarith

/-! ## The central cut, the ball and the objective -/

theorem dot_mulVec_sq_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    (u v : Fin d → ℝ) : (u ⬝ᵥ A *ᵥ v) ^ 2 ≤ (u ⬝ᵥ A *ᵥ u) * (v ⬝ᵥ A *ᵥ v) := by
  let B := Matrix.toBilin' A
  have hB_symm : B.IsSymm := by
    have h_transpose : Aᵀ = A := by
      calc
        Aᵀ = Aᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial A).symm
        _ = A := hA.1
    have h_symm (i j : Fin d) : A i j = A j i := by
      calc
        A i j = (Aᵀ) j i := rfl
        _ = A j i := by rw [h_transpose]
    refine ⟨fun x y => ?_⟩
    rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
    have h_sum_product (f : Fin d → Fin d → ℝ) : (∑ i, ∑ j, f i j) = (∑ p : Fin d × Fin d, f p.1 p.2) := by
      calc
        (∑ i, ∑ j, f i j) = (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, f i j) := rfl
        _ = (∑ p ∈ (Finset.univ : Finset (Fin d)) ×ˢ (Finset.univ : Finset (Fin d)), f p.1 p.2) := by
          rw [Finset.sum_product]
        _ = (∑ p : Fin d × Fin d, f p.1 p.2) := rfl
    rw [h_sum_product (fun i j => x i * A i j * y j),
        h_sum_product (fun i j => y i * A i j * x j)]
    apply Finset.sum_bij (fun (p : Fin d × Fin d) _ => (p.2, p.1))
    · intro p hp
      exact Finset.mem_univ _
    · intro p₁ hp₁ p₂ hp₂ h
      have h1 : p₁.1 = p₂.1 := by
        have := congr_arg Prod.snd h
        simpa using this
      have h2 : p₁.2 = p₂.2 := by
        have := congr_arg Prod.fst h
        simpa using this
      exact Prod.ext h1 h2
    · intro q hq
      refine ⟨(q.2, q.1), Finset.mem_univ _, ?_⟩
      rfl
    · intro p hp
      rw [h_symm p.1 p.2]
      ring
  have hB_nonneg (x : Fin d → ℝ) : 0 ≤ B x x := by
    have := hA.dotProduct_mulVec_nonneg x
    rw [Matrix.toBilin'_apply]
    simpa [star_trivial, dotProduct, mulVec, Finset.mul_sum, mul_assoc] using this
  have h_symm_linear : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    exact hB_symm
  have h := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg h_symm_linear u v
  have hB_apply (x y : Fin d → ℝ) : B x y = x ⬝ᵥ A *ᵥ y := by
    rw [Matrix.toBilin'_apply]
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  simpa [hB_apply] using h

theorem trace_quad_le {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (v : Fin d → ℝ) : v ⬝ᵥ P *ᵥ v ≤ P.trace * (v ⬝ᵥ v) := by
  classical
  have hHerm : P.IsHermitian := hP.isHermitian
  have hEigNonneg : ∀ i, 0 ≤ hHerm.eigenvalues i := hP.eigenvalues_nonneg
  have hTrace : P.trace = ∑ i : Fin d, hHerm.eigenvalues i := by
    simpa using hHerm.trace_eq_sum_eigenvalues
  -- Work in EuclideanSpace for the inner product structure
  let v' : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
  have hInnerV : inner ℝ v' v' = v ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [v', dotProduct]
  -- The eigenvector basis
  let b := hHerm.eigenvectorBasis
  -- Express v in the eigenbasis: v = ∑_i c_i • b_i  (in Fin d → ℝ)
  have hSumRepr : ∑ i : Fin d, (inner ℝ (b i) v' : ℝ) • (b i : Fin d → ℝ) = v := by
    have := b.sum_repr' v'
    -- this gives ∑ i, inner ℝ (b i) v' • b i = v' in EuclideanSpace
    simpa [WithLp.toLp] using congrArg (fun x : EuclideanSpace ℝ (Fin d) => (x.ofLp : Fin d → ℝ)) this
  -- The coefficients c_i = inner ℝ (b i) v'
  let c : Fin d → ℝ := fun i => inner ℝ (b i) v'
  have hc_sq_sum : ∑ i : Fin d, (c i)^2 = v ⬝ᵥ v := by
    calc
      ∑ i : Fin d, (c i)^2 = ∑ i : Fin d, (inner ℝ (b i) v')^2 := rfl
      _ = ‖v'‖^2 := by
        simpa [c] using b.sum_sq_inner_right v'
      _ = inner ℝ v' v' := by simp
      _ = v ⬝ᵥ v := hInnerV
  -- Key: P *ᵥ b_i = λ_i • b_i
  have hMulVec : ∀ i, P *ᵥ (b i : Fin d → ℝ) = (hHerm.eigenvalues i : ℝ) • (b i : Fin d → ℝ) := by
    intro i
    -- hHerm.mulVec_eigenvectorBasis gives this in EuclideanSpace
    have h := hHerm.mulVec_eigenvectorBasis i
    -- h : P *ᵥ (hHerm.eigenvectorBasis i).ofLp = hHerm.eigenvalues i • (hHerm.eigenvectorBasis i).ofLp
    -- (b i).ofLp = (b i : Fin d → ℝ) since b i is EuclideanSpace
    simpa [b] using h
  -- Now compute v ⬝ᵥ P *ᵥ v
  have hMain : v ⬝ᵥ P *ᵥ v = ∑ i : Fin d, hHerm.eigenvalues i * (c i)^2 := by
    calc
      v ⬝ᵥ P *ᵥ v = (∑ i : Fin d, (c i : ℝ) • (b i : Fin d → ℝ)) ⬝ᵥ P *ᵥ v := by rw [hSumRepr]
      _ = (∑ i : Fin d, (c i : ℝ) • (b i : Fin d → ℝ)) ⬝ᵥ (∑ i : Fin d, (c i : ℝ) • (P *ᵥ (b i : Fin d → ℝ))) := by
        -- P *ᵥ v = P *ᵥ (∑ c_i • b_i) = ∑ c_i • (P *ᵥ b_i)
        have hPv : P *ᵥ v = ∑ i : Fin d, (c i : ℝ) • (P *ᵥ (b i : Fin d → ℝ)) := by
          rw [← hSumRepr]
          simp [Matrix.mulVec_sum, mulVec_smul, c]
        rw [hPv]
      _ = ∑ i : Fin d, ∑ j : Fin d, ((c i : ℝ) • (b i : Fin d → ℝ)) ⬝ᵥ ((c j : ℝ) • (P *ᵥ (b j : Fin d → ℝ))) := by
        -- Use sum_dotProduct for the left sum, dotProduct_sum for the right sum
        rw [sum_dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dotProduct_sum]
      _ = ∑ i : Fin d, ∑ j : Fin d, (c i * c j) * ((b i : Fin d → ℝ) ⬝ᵥ (P *ᵥ (b j : Fin d → ℝ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_left_comm, mul_assoc]
      _ = ∑ i : Fin d, ∑ j : Fin d, (c i * c j) * ((b i : Fin d → ℝ) ⬝ᵥ ((hHerm.eigenvalues j : ℝ) • (b j : Fin d → ℝ))) := by
        simp [hMulVec]
      _ = ∑ i : Fin d, ∑ j : Fin d, (c i * c j) * ((hHerm.eigenvalues j : ℝ) * ((b i : Fin d → ℝ) ⬝ᵥ (b j : Fin d → ℝ))) := by
        simp [dotProduct_smul]
      _ = ∑ i : Fin d, (c i)^2 * (hHerm.eigenvalues i : ℝ) := by
        -- The orthonormal basis property: b_i ⬝ᵥ b_j = δ_{ij}
        -- So only the diagonal terms survive
        have hOrthonormal : ∀ i j, (b i : Fin d → ℝ) ⬝ᵥ (b j : Fin d → ℝ) = if i = j then 1 else 0 := by
          intro i j
          have h_inner : inner ℝ (b i) (b j) = if i = j then 1 else 0 := by
            by_cases h : i = j
            · subst h
              rw [inner_self_eq_norm_sq_to_K]
              have h_norm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
              simp [h_norm]
            · rw [b.orthonormal.inner_eq_zero h]
              simp [h]
          rw [EuclideanSpace.inner_eq_star_dotProduct] at h_inner
          simpa [star, dotProduct_comm] using h_inner
        -- Now compute the double sum
        calc
          ∑ i : Fin d, ∑ j : Fin d, (c i * c j) * ((hHerm.eigenvalues j : ℝ) * ((b i : Fin d → ℝ) ⬝ᵥ (b j : Fin d → ℝ)))
              = ∑ i : Fin d, ∑ j : Fin d, (c i * c j) * ((hHerm.eigenvalues j : ℝ) * (if i = j then 1 else 0)) := by
            simp [hOrthonormal]
          _ = ∑ i : Fin d, (c i * c i) * ((hHerm.eigenvalues i : ℝ) * 1) := by
            -- Only diagonal terms survive: for each i, the j=i term contributes
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.sum_eq_single i (fun j _ hj_ne => ?_) (fun hi' => ?_)]
            · simp
            · -- j ≠ i, so the if condition gives 0
              rw [ite_eq_right (Ne.symm hj_ne)]
              simp
            · -- i ∉ Finset.univ (impossible)
              exfalso; exact hi' (Finset.mem_univ i)
          _ = ∑ i : Fin d, (c i)^2 * (hHerm.eigenvalues i : ℝ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
      _ = ∑ i : Fin d, hHerm.eigenvalues i * (c i)^2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  -- Now we have:
  -- v ⬝ᵥ P *ᵥ v = ∑ λ_i c_i^2
  -- v ⬝ᵥ v = ∑ c_i^2
  -- trace(P) = ∑ λ_i
  -- Need: ∑ λ_i c_i^2 ≤ (∑ λ_i) (∑ c_i^2)
  -- This follows from λ_i ≥ 0 and c_i^2 ≤ ∑_j c_j^2
  have hInequality : ∑ i : Fin d, hHerm.eigenvalues i * (c i)^2 ≤ (∑ i : Fin d, hHerm.eigenvalues i) * (∑ i : Fin d, (c i)^2) := by
    calc
      ∑ i : Fin d, hHerm.eigenvalues i * (c i)^2 ≤ ∑ i : Fin d, hHerm.eigenvalues i * (∑ j : Fin d, (c j)^2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        -- c_i^2 ≤ ∑_j c_j^2
        have h_single_le_sum : (c i)^2 ≤ ∑ j : Fin d, (c j)^2 := by
          have h_nonneg_sq : ∀ j, 0 ≤ (c j)^2 := fun j => by positivity
          -- Use Finset.single_le_sum
          refine Finset.single_le_sum (fun j hj => h_nonneg_sq j) (Finset.mem_univ i)
        -- Since λ_i ≥ 0, multiply both sides
        nlinarith [hEigNonneg i, h_single_le_sum]
      _ = (∑ i : Fin d, hHerm.eigenvalues i) * (∑ i : Fin d, (c i)^2) := by
        rw [Finset.sum_mul]
  -- Combine everything
  calc
    v ⬝ᵥ P *ᵥ v = ∑ i : Fin d, hHerm.eigenvalues i * (c i)^2 := hMain
    _ ≤ (∑ i : Fin d, hHerm.eigenvalues i) * (∑ i : Fin d, (c i)^2) := hInequality
    _ = P.trace * (v ⬝ᵥ v) := by rw [hTrace, hc_sq_sum]

theorem cc_inv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) (hd : 2 ≤ d)
    (hA : A.PosDef) (hc : c ≠ 0) :
    (ccUpdate A a c).1⁻¹ = (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) •
      (A⁻¹ + (2 / (((d : ℝ) - 1) * (c ⬝ᵥ A *ᵥ c))) • vecMulVec c c) := by
  have hq : 0 < c ⬝ᵥ A *ᵥ c := hA.dotProduct_mulVec_pos hc
  set q := c ⬝ᵥ A *ᵥ c with hq_def
  set s := Real.sqrt q with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs2 : s ^ 2 = q := Real.sq_sqrt hq.le
  set b := s⁻¹ • (A *ᵥ c) with hb_def
  have hdet : IsUnit A.det := hA.det_pos.ne'.isUnit
  have hAc : A *ᵥ c = s • b := by rw [hb_def, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hAinvb : A⁻¹ *ᵥ b = s⁻¹ • c := by
    rw [hb_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hbA : b ᵥ* A⁻¹ = s⁻¹ • c := by
    have hsymm : (A⁻¹)ᵀ = A⁻¹ := hA.1.inv.eq
    rw [← Matrix.mulVec_transpose, hsymm, hAinvb]
  have hbc : b ⬝ᵥ c = s := by
    rw [hb_def, smul_dotProduct, smul_eq_mul, dotProduct_comm, ← hq_def, ← hs2, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hs.ne', one_mul]
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hdp : (d : ℝ) + 1 ≠ 0 := by intro h; linarith
  have hd0 : (d : ℝ) ≠ 0 := by intro h; linarith
  have hdd : (d : ℝ) ^ 2 - 1 ≠ 0 := by intro h; nlinarith
  show (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • (A - (2 / ((d : ℝ) + 1)) • vecMulVec b b))⁻¹ = _
  apply Matrix.inv_eq_right_inv
  set β := 2 / ((d : ℝ) + 1) with hβ
  set γ' := 2 / (((d : ℝ) - 1) * q) with hγ'
  have hcoef : γ' * s - β * s⁻¹ - β * γ' * s = 0 := by
    rw [hγ', hβ, ← hs2]
    field_simp
    ring
  have key : (A - β • vecMulVec b b) * (A⁻¹ + γ' • vecMulVec c c) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMulVec_mul_vecMulVec, hAc, hbA, hbc, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
      Matrix.vecMulVec_smul]
    calc _ = 1 + (γ' * s - β * s⁻¹ - β * γ' * s) • vecMulVec b c := by module
      _ = 1 := by rw [hcoef, zero_smul, add_zero]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key,
    show (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) * (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) = 1 by field_simp, one_smul]

theorem cc_incl_scalar (d : ℕ) (N s : ℝ) (hd : 2 ≤ d) (hN : N ≤ 1) (hs : s ≤ 0)
    (hsN : s ^ 2 ≤ N) :
    ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2 *
      (N + 2 * s / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 1) ^ 2 + 2 / ((d : ℝ) - 1) * (s + 1 / ((d : ℝ) + 1)) ^ 2) ≤ 1 := by
  set x := (d : ℝ) with hx_def
  have hx : (2 : ℝ) ≤ x := by
    simpa [hx_def] using mod_cast hd
  have hxpos : 0 < x := by linarith
  have hx2pos : 0 < x ^ 2 := pow_pos hxpos 2
  have hx1pos : x + 1 ≠ 0 := by linarith
  have hx1neg : x - 1 ≠ 0 := by linarith
  have h_s_ge_neg_one : -1 ≤ s := by
    have hsq : s ^ 2 ≤ 1 := by linarith
    nlinarith
  have h_sprod : s * (s + 1) ≤ 0 := by
    nlinarith
  have h_ratio_pos : 0 < (x + 1) / (x - 1) := by
    have hx1 : 0 < x + 1 := by linarith
    have hx2 : 0 < x - 1 := by linarith
    positivity
  have h_coeff_pos : 0 < (x + 1) ^ 2 / x ^ 2 := by
    positivity
  -- Key identity: the bracket equals (N - s²) + (s + 1/(x+1))² * (x+1)/(x-1)
  have h_bracket_eq : N + 2 * s / (x + 1) + 1 / (x + 1) ^ 2 + 2 / (x - 1) * (s + 1 / (x + 1)) ^ 2 =
      (N - s ^ 2) + (s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1) := by
    field_simp [hx1pos, hx1neg]
    ring_nf
  -- Identity: ((x²-1)/x²) * (x+1)/(x-1) = (x+1)²/x²
  have h_coeff_id : ((x ^ 2 - 1) / x ^ 2) * ((x + 1) / (x - 1)) = (x + 1) ^ 2 / x ^ 2 := by
    field_simp [hxpos.ne', hx1neg]
    ring_nf
  -- Main identity: ((x²-1)/x²)(1 - s²) + ((x+1)²/x²)(s + 1/(x+1))² = 1 + (2(x+1)/x²) s (s + 1)
  have h_main_eq : ((x ^ 2 - 1) / x ^ 2) * (1 - s ^ 2) + ((x + 1) ^ 2 / x ^ 2) * (s + 1 / (x + 1)) ^ 2 =
      1 + (2 * (x + 1) / x ^ 2) * s * (s + 1) := by
    field_simp [hxpos.ne', hx1pos]
    ring_nf
  rw [h_bracket_eq, mul_add]
  have h1 : (x ^ 2 - 1) / x ^ 2 * (N - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1)) ≤
      (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1)) := by
    have h_nonneg : 0 ≤ (x ^ 2 - 1) / x ^ 2 := by
      have : 0 ≤ x ^ 2 - 1 := by nlinarith
      positivity
    have hNle : N - s ^ 2 ≤ 1 - s ^ 2 := by linarith
    nlinarith
  have h2 : (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1)) =
      (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + ((x + 1) ^ 2 / x ^ 2) * (s + 1 / (x + 1)) ^ 2 := by
    calc
      (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1))
          = (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + ((x ^ 2 - 1) / x ^ 2 * ((x + 1) / (x - 1))) * (s + 1 / (x + 1)) ^ 2 := by ring
      _ = (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + ((x + 1) ^ 2 / x ^ 2) * (s + 1 / (x + 1)) ^ 2 := by rw [h_coeff_id]
  calc
    (x ^ 2 - 1) / x ^ 2 * (N - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1))
        ≤ (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + (x ^ 2 - 1) / x ^ 2 * ((s + 1 / (x + 1)) ^ 2 * (x + 1) / (x - 1)) := h1
    _ = (x ^ 2 - 1) / x ^ 2 * (1 - s ^ 2) + ((x + 1) ^ 2 / x ^ 2) * (s + 1 / (x + 1)) ^ 2 := h2
    _ = 1 + (2 * (x + 1) / x ^ 2) * s * (s + 1) := h_main_eq
    _ ≤ 1 := by
      have h_nonpos : (2 * (x + 1) / x ^ 2) * s * (s + 1) ≤ 0 := by
        have h_nonneg : 0 ≤ 2 * (x + 1) / x ^ 2 := by positivity
        calc
          (2 * (x + 1) / x ^ 2) * s * (s + 1) = (2 * (x + 1) / x ^ 2) * (s * (s + 1)) := by ring
          _ ≤ (2 * (x + 1) / x ^ 2) * 0 := mul_le_mul_of_nonneg_left h_sprod h_nonneg
          _ = 0 := by ring
      linarith

theorem cc_factor_le (d : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / (d + 1)) ^ 2 ≤ Real.exp (-1 / ((d : ℝ) + 1)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_sq_sub_one_pos : 0 < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hd_add_one_pos : 0 < (d : ℝ) + 1 := by nlinarith
  have hd_sub_one_pos : 0 < (d : ℝ) - 1 := by nlinarith
  -- identity: d^2/(d^2-1) = 1 + 1/(d^2-1)
  have h_eq1 : (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) = 1 + 1 / ((d : ℝ) ^ 2 - 1) := by
    field_simp [hd_sq_sub_one_pos.ne']
    ring_nf
  -- identity: d/(d+1) = 1 + (-1/(d+1))
  have h_eq2 : (d : ℝ) / ((d : ℝ) + 1) = 1 + (-1 / ((d : ℝ) + 1)) := by
    field_simp [hd_add_one_pos.ne']
    ring_nf
  -- exp bound for first factor
  have h_exp_bound1 : 1 + 1 / ((d : ℝ) ^ 2 - 1) ≤ Real.exp (1 / ((d : ℝ) ^ 2 - 1)) := by
    have h := Real.add_one_le_exp (1 / ((d : ℝ) ^ 2 - 1))
    linarith
  -- exp bound for second factor
  have h_exp_bound2 : 1 + (-1 / ((d : ℝ) + 1)) ≤ Real.exp (-1 / ((d : ℝ) + 1)) := by
    have h := Real.add_one_le_exp (-1 / ((d : ℝ) + 1))
    linarith
  -- first factor bound
  have h_first : ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) ≤ Real.exp (1 / ((d : ℝ) + 1)) := by
    calc
      ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) = (1 + 1 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) := by rw [h_eq1]
      _ ≤ (Real.exp (1 / ((d : ℝ) ^ 2 - 1))) ^ (d - 1) := by
        refine pow_le_pow_left₀ (by positivity) h_exp_bound1 (d - 1)
      _ = Real.exp (((d - 1 : ℕ) : ℝ) * (1 / ((d : ℝ) ^ 2 - 1))) := by rw [Real.exp_nat_mul]
      _ = Real.exp (((d : ℝ) - 1) * (1 / ((d : ℝ) ^ 2 - 1))) := by
        have hd1 : 1 ≤ d := by omega
        simp [Nat.cast_sub hd1]
      _ = Real.exp (((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1)) := by ring_nf
      _ = Real.exp (1 / ((d : ℝ) + 1)) := by
        have h_eq_arg : ((d : ℝ) - 1) / ((d : ℝ) ^ 2 - 1) = 1 / ((d : ℝ) + 1) := by
          field_simp [hd_sq_sub_one_pos.ne', hd_sub_one_pos.ne']
          ring_nf
        rw [h_eq_arg]
  -- second factor bound
  have h_second : (((d : ℝ) / ((d : ℝ) + 1)) ^ 2) ≤ Real.exp (-2 / ((d : ℝ) + 1)) := by
    have hpos : 0 ≤ 1 + (-1 / ((d : ℝ) + 1)) := by
      have : 0 ≤ (d : ℝ) / ((d : ℝ) + 1) := by positivity
      rw [h_eq2] at this
      exact this
    calc
      ((d : ℝ) / ((d : ℝ) + 1)) ^ 2 = (1 + (-1 / ((d : ℝ) + 1))) ^ 2 := by rw [h_eq2]
      _ ≤ (Real.exp (-1 / ((d : ℝ) + 1))) ^ 2 := by
        refine pow_le_pow_left₀ hpos h_exp_bound2 2
      _ = Real.exp ((2 : ℝ) * (-1 / ((d : ℝ) + 1))) := by
        simpa using (Real.exp_nat_mul (-1 / ((d : ℝ) + 1)) (2 : ℕ)).symm
      _ = Real.exp (-2 / ((d : ℝ) + 1)) := by ring_nf
  -- multiply the two bounds
  calc
    ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / ((d : ℝ) + 1)) ^ 2
        ≤ Real.exp (1 / ((d : ℝ) + 1)) * Real.exp (-2 / ((d : ℝ) + 1)) := by
      refine mul_le_mul h_first h_second (by positivity) (by positivity)
    _ = Real.exp (1 / ((d : ℝ) + 1) + (-2 / ((d : ℝ) + 1))) := by rw [Real.exp_add]
    _ = Real.exp (-1 / ((d : ℝ) + 1)) := by ring_nf

lemma isSymm_toBilin_of_hermitian {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    LinearMap.IsSymm (Matrix.toBilin' A) := by
  refine ⟨?h⟩
  intro x y
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  have h_sym : ∀ i j, A i j = A j i := by
    intro i j
    have h := congr_fun (congr_fun hA i) j
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h.symm
  calc
    ∑ i, ∑ j, x i * A i j * y j = ∑ i, ∑ j, A i j * x i * y j := by
      refine Finset.sum_congr rfl (λ i _ => Finset.sum_congr rfl (λ j _ => ?_))
      ring
    _ = ∑ i, ∑ j, A j i * x i * y j := by
      refine Finset.sum_congr rfl (λ i _ => Finset.sum_congr rfl (λ j _ => ?_))
      rw [h_sym j i]
    _ = ∑ j, ∑ i, A j i * x i * y j := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, A i j * x j * y i := rfl
    _ = ∑ i, ∑ j, y i * A i j * x j := by
      refine Finset.sum_congr rfl (λ i _ => Finset.sum_congr rfl (λ j _ => ?_))
      ring

lemma cauchy_schwarz_posDef {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) (x y : n → ℝ) :
    (x ⬝ᵥ A.mulVec y) ^ 2 ≤ (x ⬝ᵥ A.mulVec x) * (y ⬝ᵥ A.mulVec y) := by
  let B := Matrix.toBilin' A
  have hB_eq : ∀ x y : n → ℝ, B x y = x ⬝ᵥ A.mulVec y := by
    intro x y
    rw [Matrix.toBilin'_apply]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hB_symm : LinearMap.IsSymm B := isSymm_toBilin_of_hermitian hA.isHermitian
  have hB_nonneg : ∀ x, 0 ≤ B x x := by
    intro x
    rw [hB_eq]
    exact hA.posSemidef.dotProduct_mulVec_nonneg x
  have h := LinearMap.BilinForm.apply_sq_le_of_symm B hB_nonneg hB_symm x y
  rw [hB_eq x x, hB_eq x y, hB_eq y y] at h
  exact h

lemma dotProduct_mulVec_eq_dotProduct_mulVec_of_hermitian {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (u v : n → ℝ) :
    u ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec u := by
  let B := Matrix.toBilin' A
  have hB_eq : ∀ x y : n → ℝ, B x y = x ⬝ᵥ A.mulVec y := by
    intro x y
    rw [Matrix.toBilin'_apply]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hB_symm : LinearMap.IsSymm B := isSymm_toBilin_of_hermitian hA
  have h := hB_symm.eq u v
  simpa [hB_eq] using h

theorem cc_posDef {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) (hd : 2 ≤ d)
    (hA : A.PosDef) (hc : c ≠ 0) : (ccUpdate A a c).1.PosDef := by
  -- Unfold ccUpdate
  unfold ccUpdate
  -- Let q = cᵀ A c > 0
  set q := c ⬝ᵥ (A *ᵥ c) with hq_def
  have hq_pos : 0 < q := by
    rw [hq_def]
    simpa [star] using hA.dotProduct_mulVec_pos hc
  -- Let b = q^{-1/2} • (A *ᵥ c)
  set b := (Real.sqrt q)⁻¹ • (A *ᵥ c) with hb_def
  -- Let k = d²/(d² - 1) > 0
  set k := ((d : ℝ) ^ 2) / (((d : ℝ) ^ 2) - 1) with hk_def
  have hk_pos : 0 < k := by
    rw [hk_def]
    have hd_sq : (1 : ℝ) < (d : ℝ) ^ 2 := by
      have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    refine div_pos ?_ ?_
    · nlinarith
    · nlinarith
  -- Let β = 2/(d + 1) < 1
  set β := 2 / ((d : ℝ) + 1) with hβ_def
  have hβ_lt_one : β < 1 := by
    rw [hβ_def]
    have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hpos : 0 < (d : ℝ) + 1 := by nlinarith
    exact (div_lt_one hpos).mpr (by nlinarith)
  -- The matrix M = k • (A - β • vecMulVec b b)
  -- We need to show M is positive definite
  -- Using Matrix.PosDef.of_dotProduct_mulVec_pos
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · -- Hermitian part
    have hA_herm : A.IsHermitian := hA.isHermitian
    have h_vec_herm : (vecMulVec b b).IsHermitian := by
      rw [Matrix.IsHermitian]
      ext i j; simp [Matrix.vecMulVec, Matrix.conjTranspose_apply, mul_comm]
    have h_sub_herm : (A - β • vecMulVec b b).IsHermitian :=
      Matrix.IsHermitian.sub hA_herm (Matrix.IsHermitian.smul h_vec_herm (by simp [IsSelfAdjoint]))
    have hk_selfadj : IsSelfAdjoint k := by
      simp [IsSelfAdjoint, star]
    exact Matrix.IsHermitian.smul h_sub_herm hk_selfadj
  · -- Positivity part: ∀ x ≠ 0, 0 < star x ⬝ᵥ M.mulVec x
    intro x hx_ne_zero
    -- star x = x for ℝ
    have h_star_x : star x = x := by simp
    rw [h_star_x]
    -- Symmetry lemma for A
    have h_symm : ∀ u v : Fin d → ℝ, u ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec u :=
      dotProduct_mulVec_eq_dotProduct_mulVec_of_hermitian hA.isHermitian
    -- Dot product with vecMulVec
    have h_dot_vec : ∀ u v : Fin d → ℝ, u ⬝ᵥ (vecMulVec v v).mulVec u = (v ⬝ᵥ u) * (v ⬝ᵥ u) := by
      intro u v
      rw [Matrix.vecMulVec_mulVec]
      simp [dotProduct, mul_comm, Finset.mul_sum, mul_assoc]
    have hx_dot_Ax_pos : 0 < x ⬝ᵥ A.mulVec x :=
      hA.dotProduct_mulVec_pos hx_ne_zero
    -- Cauchy-Schwarz: (c ⬝ᵥ A.mulVec x)² ≤ (x ⬝ᵥ A.mulVec x) * q
    have h_cauchy : (c ⬝ᵥ A.mulVec x) ^ 2 ≤ (x ⬝ᵥ A.mulVec x) * q := by
      rw [h_symm c x, hq_def]
      exact cauchy_schwarz_posDef hA x c
    -- Compute b ⬝ᵥ x
    have hb_dot_x : b ⬝ᵥ x = (Real.sqrt q)⁻¹ * (c ⬝ᵥ A.mulVec x) := by
      rw [hb_def]
      calc
        ((Real.sqrt q)⁻¹ • (A *ᵥ c)) ⬝ᵥ x = (Real.sqrt q)⁻¹ • ((A *ᵥ c) ⬝ᵥ x) := by rw [smul_dotProduct]
        _ = (Real.sqrt q)⁻¹ • (x ⬝ᵥ (A *ᵥ c)) := by rw [dotProduct_comm]
        _ = (Real.sqrt q)⁻¹ • (c ⬝ᵥ A.mulVec x) := by rw [h_symm c x]
        _ = (Real.sqrt q)⁻¹ * (c ⬝ᵥ A.mulVec x) := by simp
    -- (b ⬝ᵥ x)² ≤ x ⬝ᵥ A.mulVec x
    have hb_dot_x_sq : (b ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ A.mulVec x := by
      rw [hb_dot_x]
      have h_sqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt (by positivity)
      calc
        ((Real.sqrt q)⁻¹ * (c ⬝ᵥ A.mulVec x)) ^ 2 = ((Real.sqrt q)⁻¹) ^ 2 * (c ⬝ᵥ A.mulVec x) ^ 2 := by ring
        _ ≤ ((Real.sqrt q)⁻¹) ^ 2 * ((x ⬝ᵥ A.mulVec x) * q) := by
          nlinarith
        _ = ((Real.sqrt q)⁻¹) ^ 2 * q * (x ⬝ᵥ A.mulVec x) := by ring
        _ = ((Real.sqrt q) ^ 2)⁻¹ * q * (x ⬝ᵥ A.mulVec x) := by ring
        _ = q⁻¹ * q * (x ⬝ᵥ A.mulVec x) := by rw [h_sqrt_sq]
        _ = 1 * (x ⬝ᵥ A.mulVec x) := by field_simp [ne_of_gt hq_pos]
        _ = x ⬝ᵥ A.mulVec x := by simp
    -- Main computation
    have h_mulVec_smul : ((k • (A - β • vecMulVec b b))).mulVec x = k • ((A - β • vecMulVec b b).mulVec x) := by
      rw [Matrix.smul_mulVec]
    have h_mulVec_sub : (A - β • vecMulVec b b).mulVec x = A.mulVec x - (β • (vecMulVec b b)).mulVec x := by
      rw [Matrix.sub_mulVec]
    have h_mulVec_smul2 : (β • (vecMulVec b b)).mulVec x = β • ((vecMulVec b b).mulVec x) := by
      rw [Matrix.smul_mulVec]
    have h_dot_sub : x ⬝ᵥ (A.mulVec x - β • ((vecMulVec b b).mulVec x)) = (x ⬝ᵥ A.mulVec x) - β * (x ⬝ᵥ (vecMulVec b b).mulVec x) := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    calc
      x ⬝ᵥ ((k • (A - β • vecMulVec b b))).mulVec x
          = x ⬝ᵥ (k • ((A - β • vecMulVec b b).mulVec x)) := by rw [h_mulVec_smul]
      _ = k * (x ⬝ᵥ ((A - β • vecMulVec b b).mulVec x)) := by simp [dotProduct_smul]
      _ = k * (x ⬝ᵥ (A.mulVec x - (β • (vecMulVec b b)).mulVec x)) := by rw [h_mulVec_sub]
      _ = k * (x ⬝ᵥ (A.mulVec x - β • ((vecMulVec b b).mulVec x))) := by rw [h_mulVec_smul2]
      _ = k * ((x ⬝ᵥ A.mulVec x) - β * (x ⬝ᵥ (vecMulVec b b).mulVec x)) := by rw [h_dot_sub]
      _ = k * ((x ⬝ᵥ A.mulVec x) - β * ((b ⬝ᵥ x) * (b ⬝ᵥ x))) := by rw [h_dot_vec x b]
      _ = k * ((x ⬝ᵥ A.mulVec x) - β * ((b ⬝ᵥ x) ^ 2)) := by ring
      _ ≥ k * ((x ⬝ᵥ A.mulVec x) - β * (x ⬝ᵥ A.mulVec x)) := by
            have h_ineq : (x ⬝ᵥ A.mulVec x) - β * ((b ⬝ᵥ x) ^ 2) ≥ (x ⬝ᵥ A.mulVec x) - β * (x ⬝ᵥ A.mulVec x) := by
              have hβ_nonneg : 0 ≤ β := by
                rw [hβ_def]
                refine div_nonneg (by norm_num) (by nlinarith [show (0 : ℝ) ≤ d from by exact_mod_cast Nat.zero_le _])
              nlinarith
            exact mul_le_mul_of_nonneg_left h_ineq (by linarith [hk_pos])
      _ = k * ((1 - β) * (x ⬝ᵥ A.mulVec x)) := by ring
      _ > 0 := by
        have h_pos : 0 < (1 - β) * (x ⬝ᵥ A.mulVec x) := by
          have h_one_minus_β_pos : 0 < 1 - β := by linarith
          exact mul_pos h_one_minus_β_pos hx_dot_Ax_pos
        exact mul_pos hk_pos h_pos

theorem cc_det {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) (hd : 2 ≤ d)
    (hA : A.PosDef) (hc : c ≠ 0) :
    (ccUpdate A a c).1.det = A.det * ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) ^ (d - 1) * ((d : ℝ) / (d + 1)) ^ 2 := by
  -- Let q = c ⬝ᵥ (A *ᵥ c) > 0
  set q := c ⬝ᵥ (A *ᵥ c) with hq_def
  have hqpos : 0 < q := hA.dotProduct_mulVec_pos hc
  have hqpos_ne : q ≠ 0 := by linarith
  -- Let b = q^{-1/2} • (A *ᵥ c)
  set b := (Real.sqrt q)⁻¹ • (A *ᵥ c) with hb_def
  -- Let k = d²/(d² - 1), β = 2/(d + 1)
  set k := ((d : ℝ) ^ 2) / ((d : ℝ) ^ 2 - 1) with hk_def
  set β := 2 / ((d : ℝ) + 1) with hβ_def
  -- Unfold ccUpdate: (ccUpdate A a c).1 = k • (A - β • vecMulVec b b)
  have hM : (ccUpdate A a c).1 = k • (A - β • vecMulVec b b) := by
    dsimp [ccUpdate, k, β, b, q]
  rw [hM]
  -- det(k • M) = k^d * det(M)
  rw [Matrix.det_smul, Fintype.card_fin]
  -- Now compute det(A - β • vecMulVec b b)
  -- Use vecMulVec_eq to express as replicateCol * replicateRow
  have hvec : vecMulVec b b = (Matrix.replicateCol Unit b) * (Matrix.replicateRow Unit b) := by
    rw [Matrix.vecMulVec_eq Unit b b]
  rw [hvec]
  -- Prepare for det_add_replicateCol_mul_replicateRow
  have hA_det_unit : IsUnit A.det := ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hA_inv : Invertible A := Matrix.invertibleOfIsUnitDet A hA_det_unit
  have hA_symm : A.IsHermitian := hA.isHermitian
  have hA_transpose_eq : Aᵀ = A := hA_symm
  -- Rewrite A - β • (replicateCol Unit b * replicateRow Unit b) as A + replicateCol Unit (-β • b) * replicateRow Unit b
  have h_add : A - β • ((Matrix.replicateCol Unit b) * (Matrix.replicateRow Unit b)) =
      A + (Matrix.replicateCol Unit (-β • b)) * (Matrix.replicateRow Unit b) := by
    ext i j
    simp [Matrix.replicateCol, Matrix.replicateRow, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_apply]
    ring
  rw [h_add]
  -- Apply the matrix determinant lemma
  rw [Matrix.det_add_replicateCol_mul_replicateRow hA_det_unit (-β • b) b]
  -- Now we have A.det * (1 + replicateRow Unit b * A⁻¹ * replicateCol Unit (-β • b)).det
  -- Simplify the 1x1 determinant
  have h_det_one : ((1 : Matrix (Unit) (Unit) ℝ) + (Matrix.replicateRow Unit b) * A⁻¹ * (Matrix.replicateCol Unit (-β • b))).det =
      1 - β * (b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
    rw [Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.replicateRow_apply, Matrix.replicateCol_apply,
      Matrix.mul_apply, Matrix.dotProduct_mulVec, Pi.smul_apply, smul_eq_mul]
    simp
    -- Goal: 1 + -∑ x, (∑ j, b j * A⁻¹ j x) * (β * b x) = 1 - β * b ᵥ* A⁻¹ ⬝ᵥ b
    have h_sum : (∑ x : Fin d, (∑ j : Fin d, b j * A⁻¹ j x) * (β * b x)) = β * (b ᵥ* A⁻¹ ⬝ᵥ b) := by
      calc
        (∑ x : Fin d, (∑ j : Fin d, b j * A⁻¹ j x) * (β * b x))
            = β * ∑ x : Fin d, (∑ j : Fin d, b j * A⁻¹ j x) * b x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
        _ = β * (b ᵥ* A⁻¹ ⬝ᵥ b) := rfl
    rw [h_sum]
    ring
  rw [h_det_one]
  -- Now we have: k^d * A.det * (1 - β * (b ⬝ᵥ (A⁻¹ *ᵥ b)))
  -- Show that b ⬝ᵥ (A⁻¹ *ᵥ b) = 1
  have h_dot : b ⬝ᵥ (A⁻¹ *ᵥ b) = 1 := by
    -- A⁻¹ *ᵥ b = (Real.sqrt q)⁻¹ • c
    have h_inv_mul : A⁻¹ *ᵥ b = (Real.sqrt q)⁻¹ • c := by
      dsimp [b]
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible A, Matrix.one_mulVec]
    rw [h_inv_mul]
    dsimp [b]
    -- ((Real.sqrt q)⁻¹ • (A *ᵥ c)) ⬝ᵥ ((Real.sqrt q)⁻¹ • c) = 1
    calc
      ((Real.sqrt q)⁻¹ • (A *ᵥ c)) ⬝ᵥ ((Real.sqrt q)⁻¹ • c)
          = ((Real.sqrt q)⁻¹) • ((A *ᵥ c) ⬝ᵥ ((Real.sqrt q)⁻¹ • c)) := by
        rw [smul_dotProduct]
      _ = ((Real.sqrt q)⁻¹) • (((Real.sqrt q)⁻¹) • ((A *ᵥ c) ⬝ᵥ c)) := by
        rw [dotProduct_smul]
      _ = ((Real.sqrt q)⁻¹) * ((Real.sqrt q)⁻¹) * ((A *ᵥ c) ⬝ᵥ c) := by
        simp_rw [smul_eq_mul]; ring
      _ = ((Real.sqrt q)^2)⁻¹ * ((A *ᵥ c) ⬝ᵥ c) := by ring
      _ = q⁻¹ * ((A *ᵥ c) ⬝ᵥ c) := by rw [Real.sq_sqrt (by linarith)]
      _ = q⁻¹ * q := by
        have h_eq : (A *ᵥ c) ⬝ᵥ c = q := by
          dsimp [q]
          calc
            (A *ᵥ c) ⬝ᵥ c = (Matrix.vecMul c A) ⬝ᵥ c := by
              rw [← Matrix.vecMul_transpose A c, hA_transpose_eq]
            _ = c ⬝ᵥ (A *ᵥ c) := by rw [Matrix.dotProduct_mulVec c A c]
        rw [h_eq]
      _ = 1 := by field_simp [hqpos_ne]
  rw [h_dot]
  -- Now we have: k^d * A.det * (1 - β * 1)
  -- Simplify β * 1 to β
  simp
  -- Now we have: k^d * (A.det * (1 - β)) = A.det * k^(d-1) * (d/(d+1))^2
  -- 1 - β = 1 - 2/(d+1) = (d-1)/(d+1)
  have h_one_minus_β : 1 - β = ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
    dsimp [β]
    field_simp [show (d : ℝ) + 1 ≠ 0 from by
      intro hzero
      have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith]
    ring
  rw [h_one_minus_β]
  -- Now we have: k^d * A.det * ((d-1)/(d+1))
  -- Need to show: k^d * ((d-1)/(d+1)) = k^(d-1) * (d/(d+1))^2
  -- where k = d²/(d²-1)
  dsimp [k]
  -- Note: d² - 1 = (d-1)(d+1)
  have h_factor : (d : ℝ)^2 - 1 = ((d : ℝ) - 1) * ((d : ℝ) + 1) := by ring
  rw [h_factor]
  -- Cancel A.det on both sides (nonzero because A is positive definite)
  have hA_det_ne_zero : A.det ≠ 0 := by
    exact ne_of_gt hA.det_pos
  -- The goal is now:
  -- (d^2 / ((d-1)*(d+1)))^d * (A.det * ((d-1)/(d+1))) = A.det * (d^2 / ((d-1)*(d+1)))^(d-1) * (d/(d+1))^2
  -- Cancel A.det
  have h_goal : ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^d * (((d : ℝ) - 1) / ((d : ℝ) + 1)) =
      ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^(d-1) * (((d : ℝ) / ((d : ℝ) + 1))^2) := by
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      intro hzero
      have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hd2 : (d : ℝ) + 1 ≠ 0 := by
      intro hzero
      have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have h_denom : ((d : ℝ) - 1) * ((d : ℝ) + 1) ≠ 0 := mul_ne_zero hd1 hd2
    have hd_sq_ne_zero : (d : ℝ)^2 ≠ 0 := by
      intro hzero
      have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have : (d : ℝ) = 0 := by nlinarith
      linarith
    set K := ((d : ℝ)^2) / (((d : ℝ) - 1) * ((d : ℝ) + 1)) with hK
    have h_simple : K * (((d : ℝ) - 1) / ((d : ℝ) + 1)) = (((d : ℝ) / ((d : ℝ) + 1))^2) := by
      dsimp [K]
      field_simp [hd1, hd2]
    have h_pow : K^d = K^(d-1) * K := by
      have hd_pos : 1 ≤ d := by omega
      calc
        K^d = K^((d-1)+1) := by rw [Nat.sub_add_cancel hd_pos]
        _ = K^(d-1) * K := by rw [pow_succ]
    rw [h_pow]
    rw [mul_assoc]
    rw [h_simple]
  -- Now use h_goal to close the main goal
  have h_main : ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^d * (A.det * (((d : ℝ) - 1) / ((d : ℝ) + 1))) =
      A.det * ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^(d-1) * (((d : ℝ) / ((d : ℝ) + 1))^2) := by
    calc
      ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^d * (A.det * (((d : ℝ) - 1) / ((d : ℝ) + 1)))
          = A.det * (((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^d * (((d : ℝ) - 1) / ((d : ℝ) + 1))) := by ring
      _ = A.det * (((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^(d-1) * (((d : ℝ) / ((d : ℝ) + 1))^2)) := by rw [h_goal]
      _ = A.det * ((d : ℝ)^2 / (((d : ℝ) - 1) * ((d : ℝ) + 1)))^(d-1) * (((d : ℝ) / ((d : ℝ) + 1))^2) := by ring
  exact h_main

theorem cc_incl {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) (hd : 2 ≤ d)
    (hA : A.PosDef) (hc : c ≠ 0) (x : Fin d → ℝ) (hx : ellIn A a x) (hcx : c ⬝ᵥ (x - a) ≤ 0) :
    ellIn (ccUpdate A a c).1 (ccUpdate A a c).2 x := by
  have hq_pos : 0 < c ⬝ᵥ A *ᵥ c := hA.dotProduct_mulVec_pos hc
  set q := c ⬝ᵥ A *ᵥ c with hq_def
  set sqrt_q := Real.sqrt q with hsqrt_q_def
  have hsqrt_q_pos : 0 < sqrt_q := Real.sqrt_pos.mpr hq_pos
  have hsqrt_q_sq : sqrt_q ^ 2 = q := Real.sq_sqrt hq_pos.le
  set b := sqrt_q⁻¹ • (A *ᵥ c) with hb_def
  set u := x - a with hu_def
  have hN : u ⬝ᵥ (A⁻¹ *ᵥ u) ≤ 1 := hx
  set s := (c ⬝ᵥ u) / sqrt_q with hs_def
  have hs_nonpos : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcx hsqrt_q_pos.le
  have hA_inv_mul_b : A⁻¹ *ᵥ b = sqrt_q⁻¹ • c := by
    rw [hb_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.det_pos.ne'.isUnit,
      Matrix.one_mulVec]
  have h_dot_symm (v w : Fin d → ℝ) : v ⬝ᵥ (A⁻¹ *ᵥ w) = w ⬝ᵥ (A⁻¹ *ᵥ v) := by
    have := hA.inv.isHermitian.star_dotProduct_mulVec_comm v w
    simpa [star] using this
  have hc_dot_b : c ⬝ᵥ b = sqrt_q := by
    rw [hb_def, dotProduct_smul, smul_eq_mul, ← hq_def, ← hsqrt_q_sq, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hsqrt_q_pos.ne', one_mul]
  have hb_dot_Ainv_u : b ⬝ᵥ (A⁻¹ *ᵥ u) = s := by
    rw [h_dot_symm, hA_inv_mul_b, dotProduct_smul, smul_eq_mul, dotProduct_comm, hs_def, div_eq_inv_mul]
  have hb_dot_Ainv_b : b ⬝ᵥ (A⁻¹ *ᵥ b) = 1 := by
    rw [hA_inv_mul_b, dotProduct_smul, smul_eq_mul, dotProduct_comm, hc_dot_b, inv_mul_cancel₀ hsqrt_q_pos.ne']
  have hs_sq_le_N : s ^ 2 ≤ u ⬝ᵥ (A⁻¹ *ᵥ u) := by
    have h_cauchy := dot_mulVec_sq_le A⁻¹ hA.inv.posSemidef b u
    rw [hb_dot_Ainv_u, hb_dot_Ainv_b, one_mul] at h_cauchy
    exact h_cauchy
  have hx_minus_a' : x - (ccUpdate A a c).2 = u + ((d : ℝ) + 1)⁻¹ • b := by
    show x - (a - ((d : ℝ) + 1)⁻¹ • b) = u + ((d : ℝ) + 1)⁻¹ • b
    rw [hu_def]; abel
  unfold ellIn
  rw [hx_minus_a', cc_inv A a c hd hA hc]
  set β := ((d : ℝ) ^ 2 - 1) / ((d : ℝ) ^ 2) with hβ_def
  set α := ((d : ℝ) + 1)⁻¹ with hα_def
  set γ := 2 / (((d : ℝ) - 1) * q) with hγ_def
  have hvv : ∀ v, vecMulVec c c *ᵥ v = (c ⬝ᵥ v) • c := by
    intro v; ext i
    simp [vecMulVec, mulVec, dotProduct, mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
  have h_inner : (u + α • b) ⬝ᵥ (A⁻¹ *ᵥ (u + α • b)) = (u ⬝ᵥ (A⁻¹ *ᵥ u)) + 2 * s * α + α ^ 2 := by
    simp only [mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, h_dot_symm u b, hb_dot_Ainv_u, hb_dot_Ainv_b]
    ring
  have h_c_dot : c ⬝ᵥ (u + α • b) = sqrt_q * (s + α) := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hc_dot_b, hs_def]
    field_simp
  have h_expr : (u + α • b) ⬝ᵥ ((β • (A⁻¹ + γ • vecMulVec c c)) *ᵥ (u + α • b)) =
      β * ((u ⬝ᵥ (A⁻¹ *ᵥ u)) + 2 * s * α + α ^ 2 + γ * q * (s + α) ^ 2) := by
    rw [Matrix.smul_mulVec, add_mulVec, Matrix.smul_mulVec, hvv, dotProduct_smul, dotProduct_add, dotProduct_smul,
      dotProduct_smul, h_inner, dotProduct_comm (u + α • b) c, h_c_dot, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      ← hsqrt_q_sq]
    ring
  rw [h_expr]
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hγq : γ * q = 2 / ((d : ℝ) - 1) := by
    rw [hγ_def]; field_simp
  have hfin : β * ((u ⬝ᵥ (A⁻¹ *ᵥ u)) + 2 * s * α + α ^ 2 + γ * q * (s + α) ^ 2) =
        ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2 * ((u ⬝ᵥ (A⁻¹ *ᵥ u)) + 2 * s / ((d : ℝ) + 1) + 1 / ((d : ℝ) + 1) ^ 2 +
          2 / ((d : ℝ) - 1) * (s + 1 / ((d : ℝ) + 1)) ^ 2) := by
    rw [hγq, hβ_def, hα_def, one_div ((d : ℝ) + 1), one_div (((d : ℝ) + 1) ^ 2), ← inv_pow]; ring
  rw [hfin]
  exact cc_incl_scalar d (u ⬝ᵥ (A⁻¹ *ᵥ u)) s hd hN hs_nonpos hs_sq_le_N

theorem lemmaBALL : LemmaBALL := by
  intro d A a b ρ hA hρ hball
  have hA_herm : A.IsHermitian := hA.isHermitian
  have hA_det_pos : 0 < A.det := hA.det_pos
  have hA_isUnit : IsUnit A := hA.isUnit
  -- For each eigenvalue index j, we prove ρ² ≤ λ_j
  have h_eigenvalue_ge_rho_sq (j : Fin d) : ρ ^ 2 ≤ hA_herm.eigenvalues j := by
    -- Let v be the j-th eigenvector as a Fin d → ℝ
    let v : Fin d → ℝ := (hA_herm.eigenvectorBasis j).ofLp
    -- v is a unit vector: v ⬝ᵥ v = 1
    have h_dot_vv : v ⬝ᵥ v = 1 := by
      calc
        v ⬝ᵥ v = ∑ i : Fin d, v i ^ 2 := by simp [dotProduct, sq]
        _ = ∑ i : Fin d, ((hA_herm.eigenvectorBasis j : EuclideanSpace ℝ (Fin d)) i) ^ 2 := by
          simp [v]
        _ = ‖(hA_herm.eigenvectorBasis j : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
          simp
        _ = 1 ^ 2 := by rw [hA_herm.eigenvectorBasis.norm_eq_one j]
        _ = 1 := by norm_num
    have h_Anorm_v : oNorm v = 1 := by
      dsimp [oNorm]
      rw [h_dot_vv]
      exact Real.sqrt_one
    -- The eigenvalue equation: A *ᵥ v = λ • v
    have h_ev : A *ᵥ v = hA_herm.eigenvalues j • v :=
      hA_herm.mulVec_eigenvectorBasis j
    -- Since A is invertible, A⁻¹ *ᵥ v = λ⁻¹ • v
    have hA_inv_mulVec_v : A⁻¹ *ᵥ v = (hA_herm.eigenvalues j)⁻¹ • v := by
      have h_inv : Invertible A := Matrix.invertibleOfIsUnitDet A
        ((Matrix.isUnit_iff_isUnit_det A).mp hA_isUnit)
      have h_eq : hA_herm.eigenvalues j • v = A *ᵥ v := h_ev.symm
      have h := Matrix.inv_mulVec_eq_vec (A := A) (u := hA_herm.eigenvalues j • v) (v := v)
        (hM := h_eq)
      -- h : A⁻¹ *ᵥ (eigenvalue • v) = v
      rw [Matrix.mulVec_smul] at h
      -- h: eigenvalue • (A⁻¹ *ᵥ v) = v
      have heigen_ne_zero : hA_herm.eigenvalues j ≠ 0 := by
        have hpos := hA.eigenvalues_pos j
        linarith
      -- From h: λ • x = v, multiply both sides by λ⁻¹
      calc
        A⁻¹ *ᵥ v = (hA_herm.eigenvalues j)⁻¹ • (hA_herm.eigenvalues j • (A⁻¹ *ᵥ v)) := by
          simp [heigen_ne_zero, smul_smul]
        _ = (hA_herm.eigenvalues j)⁻¹ • v := by rw [h]
    -- Points b + ρ • v and b - ρ • v are in oBall b ρ
    have h_ball_add : b + ρ • v ∈ oBall b ρ := by
      dsimp [oBall]
      have : (b + ρ • v) - b = ρ • v := by simp
      rw [this]
      dsimp [oNorm]
      have h_sq : (ρ • v) ⬝ᵥ (ρ • v) = ρ ^ 2 := by
        calc
          (ρ • v) ⬝ᵥ (ρ • v) = ρ * (v ⬝ᵥ (ρ • v)) := by
            simp [dotProduct_smul]
          _ = ρ * (ρ * (v ⬝ᵥ v)) := by simp [dotProduct_smul]
          _ = ρ ^ 2 * (v ⬝ᵥ v) := by ring
          _ = ρ ^ 2 * 1 := by rw [h_dot_vv]
          _ = ρ ^ 2 := by ring
      rw [h_sq]
      rw [Real.sqrt_sq hρ]
    have h_ball_sub : b - ρ • v ∈ oBall b ρ := by
      dsimp [oBall]
      have : (b - ρ • v) - b = -ρ • v := by simp
      rw [this]
      dsimp [oNorm]
      have h_sq : (-ρ • v) ⬝ᵥ (-ρ • v) = ρ ^ 2 := by
        calc
          (-ρ • v) ⬝ᵥ (-ρ • v) = (-ρ) * (v ⬝ᵥ (-ρ • v)) := by
            simp [dotProduct_smul]
          _ = (-ρ) * ((-ρ) * (v ⬝ᵥ v)) := by simp [dotProduct_smul]
          _ = ρ ^ 2 * (v ⬝ᵥ v) := by ring
          _ = ρ ^ 2 * 1 := by rw [h_dot_vv]
          _ = ρ ^ 2 := by ring
      rw [h_sq]
      rw [Real.sqrt_sq hρ]
    -- Both points satisfy ellIn A a
    have h_ell_add : ellIn A a (b + ρ • v) := hball _ h_ball_add
    have h_ell_sub : ellIn A a (b - ρ • v) := hball _ h_ball_sub
    -- ellIn A a x means (x - a) ⬝ᵥ (A⁻¹ *ᵥ (x - a)) ≤ 1
    -- Let m = b - a
    let m := b - a
    have h_m_add : b + ρ • v - a = m + ρ • v := by
      simp [m, sub_add_eq_add_sub]
    have h_m_sub : b - ρ • v - a = m - ρ • v := by
      dsimp [m]
      abel
    have h_ell_add' : (m + ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m + ρ • v)) ≤ 1 := by
      dsimp [ellIn] at h_ell_add
      simpa [h_m_add] using h_ell_add
    have h_ell_sub' : (m - ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m - ρ • v)) ≤ 1 := by
      dsimp [ellIn] at h_ell_sub
      simpa [h_m_sub] using h_ell_sub
    -- Add the two inequalities
    have h_sum : (m + ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m + ρ • v)) +
                (m - ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m - ρ • v)) ≤ 2 := by
      linarith
    -- Expand the sum using linearity
    have h_expand : (m + ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m + ρ • v)) +
                   (m - ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m - ρ • v)) =
                   2 * (m ⬝ᵥ (A⁻¹ *ᵥ m) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v))) := by
      have h_add : (m + ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m + ρ • v)) =
        m ⬝ᵥ (A⁻¹ *ᵥ m) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ m) + m ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) := by
        simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_assoc]
      have h_sub : (m - ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (m - ρ • v)) =
        m ⬝ᵥ (A⁻¹ *ᵥ m) - (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ m) - m ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_assoc, Matrix.mulVec_neg, dotProduct_neg]
        ring
      rw [h_add, h_sub]
      ring
    rw [h_expand] at h_sum
    -- h_sum: 2 * (m ⬝ᵥ (A⁻¹ *ᵥ m) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v))) ≤ 2
    -- Divide by 2
    have h_ineq : m ⬝ᵥ (A⁻¹ *ᵥ m) + (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) ≤ 1 := by linarith
    -- m ⬝ᵥ (A⁻¹ *ᵥ m) ≥ 0 (positive semidefinite)
    have h_nonneg_m : 0 ≤ m ⬝ᵥ (A⁻¹ *ᵥ m) := by
      simpa using Matrix.PosSemidef.dotProduct_mulVec_nonneg (hA.inv.posSemidef) m
    -- So (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) ≤ 1
    have h_rho_v_ineq : (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) ≤ 1 := by
      linarith
    -- Expand (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) = ρ^2 * (v ⬝ᵥ (A⁻¹ *ᵥ v))
    have h_expand2 : (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) = ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
      calc
        (ρ • v) ⬝ᵥ (A⁻¹ *ᵥ (ρ • v)) = (ρ • v) ⬝ᵥ (ρ • (A⁻¹ *ᵥ v)) := by
          simp [Matrix.mulVec_smul]
        _ = ρ * (v ⬝ᵥ (ρ • (A⁻¹ *ᵥ v))) := by
          simp [smul_dotProduct]
        _ = ρ * (ρ * (v ⬝ᵥ (A⁻¹ *ᵥ v))) := by simp [dotProduct_smul]
        _ = ρ ^ 2 * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by ring
    rw [h_expand2] at h_rho_v_ineq
    -- Now v ⬝ᵥ (A⁻¹ *ᵥ v) = v ⬝ᵥ (λ⁻¹ • v) = λ⁻¹ * (v ⬝ᵥ v) = λ⁻¹
    have h_v_dot : v ⬝ᵥ (A⁻¹ *ᵥ v) = (hA_herm.eigenvalues j)⁻¹ := by
      rw [hA_inv_mulVec_v]
      simp [dotProduct_smul, h_dot_vv]
    rw [h_v_dot] at h_rho_v_ineq
    -- h_rho_v_ineq: ρ^2 * λ⁻¹ ≤ 1
    have h_eigen_pos : 0 < hA_herm.eigenvalues j := hA.eigenvalues_pos j
    -- From ρ^2 * λ⁻¹ ≤ 1 and λ > 0, we get ρ^2 ≤ λ
    have h_final : ρ ^ 2 ≤ hA_herm.eigenvalues j := by
      rw [← div_eq_mul_inv] at h_rho_v_ineq
      exact (div_le_one h_eigen_pos).mp h_rho_v_ineq
    exact h_final
  -- Now use the eigenvalue bound to bound the determinant
  have h_det_eq_prod : A.det = ∏ j : Fin d, hA_herm.eigenvalues j := by
    rw [hA_herm.det_eq_prod_eigenvalues]
    simp
  have h_prod_ge : (∏ j : Fin d, ρ ^ 2) ≤ ∏ j : Fin d, hA_herm.eigenvalues j := by
    refine Finset.prod_le_prod₀ ?_ ?_
    · intro i hi
      nlinarith [hρ]
    · intro i hi
      exact h_eigenvalue_ge_rho_sq i
  have h_prod_const : (∏ _j : Fin d, ρ ^ 2) = (ρ ^ 2) ^ d := by
    simp [Finset.prod_const]
  have h_pow_mul : (ρ ^ 2) ^ d = ρ ^ (2 * d) := by
    rw [← pow_mul, mul_comm]
  calc
    ρ ^ (2 * d) = (ρ ^ 2) ^ d := by rw [h_pow_mul]
    _ = ∏ _j : Fin d, ρ ^ 2 := by rw [h_prod_const]
    _ ≤ ∏ j : Fin d, hA_herm.eigenvalues j := h_prod_ge
    _ = A.det := by rw [h_det_eq_prod]

theorem lemmaGVAL : LemmaGVAL := by
  intro d Q a0 r R hQconv hr hball hQR x η hηpos
  by_cases hx_eq_a0 : x = a0
  · -- case x = a0: both sides are 0
    rw [hx_eq_a0]
    have ha0_in_Q : a0 ∈ Q := by
      have ha0_in_ball : a0 ∈ oBall a0 r := by
        dsimp [oBall, oNorm]
        have : oNorm (a0 - a0) = 0 := by simp [oNorm]
        simp [hr.le]
      exact hball ha0_in_ball
    have h_gauge_val : oGaugeVal Q a0 r R a0 η = 0 := by
      simp [oGaugeVal]
    have h_gauge : oGauge Q a0 a0 = 0 := by
      dsimp [oGauge]
      have h_set_eq : {t : ℝ | 0 < t ∧ a0 + t⁻¹ • (a0 - a0) ∈ Q} = Set.Ioi (0 : ℝ) := by
        ext t
        constructor
        · intro ⟨ht, _⟩; exact ht
        · intro ht
          refine ⟨ht, ?_⟩
          simp [ha0_in_Q]
      rw [h_set_eq]
      exact csInf_Ioi
    rw [h_gauge_val, h_gauge]
    have : |(0 : ℝ) - 0| ≤ η := by
      rw [sub_self, abs_zero]
      exact hηpos.le
    exact this
  · -- case x ≠ a0
    have hρ_pos : 0 < oNorm (x - a0) := by
      have h_nonneg := oNorm_nonneg (x - a0)
      have h_ne_zero : oNorm (x - a0) ≠ 0 := by
        intro hzero
        have hzero' := (oNorm_eq_zero_iff (x - a0)).mp hzero
        apply hx_eq_a0
        exact sub_eq_zero.mp hzero'
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    set ρ := oNorm (x - a0) with hρ_def
    have hρ_pos' : 0 < ρ := hρ_pos
    -- Define Pr and S
    set Pr := fun t : ℝ => 0 < t ∧ a0 + t⁻¹ • (x - a0) ∈ Q with hPr_def
    set S := {t : ℝ | Pr t} with hS_def
    have h_gauge_eq : oGauge Q a0 x = sInf S := by
      dsimp [oGauge, S, Pr]
    -- Monotonicity of Pr
    have ha0_in_Q : a0 ∈ Q := by
      have ha0_in_ball : a0 ∈ oBall a0 r := by
        dsimp [oBall, oNorm]
        have : oNorm (a0 - a0) = 0 := by simp [oNorm]
        simp [hr.le]
      exact hball ha0_in_ball
    have hPr_mono : ∀ t t', Pr t → t ≤ t' → Pr t' := by
      intro t t' ⟨ht_pos, ht_Q⟩ ht_le
      have ht'_pos : 0 < t' := by linarith
      refine ⟨ht'_pos, ?_⟩
      have h_comb : a0 + (t' : ℝ)⁻¹ • (x - a0) =
          ((t' - t) / t') • a0 + (t / t') • (a0 + t⁻¹ • (x - a0)) := by
        calc
          a0 + (t' : ℝ)⁻¹ • (x - a0) = (1 : ℝ) • a0 + (t'⁻¹) • (x - a0) := by simp
          _ = (((t' - t) / t' + t / t')) • a0 + (t'⁻¹) • (x - a0) := by
            have h_scalar : (1 : ℝ) = (t' - t) / t' + t / t' := by
              field_simp [ht'_pos.ne']
              ring
            simp [h_scalar]
          _ = ((t' - t) / t') • a0 + (t / t') • a0 + (t'⁻¹) • (x - a0) := by
            rw [add_smul]
          _ = ((t' - t) / t') • a0 + (t / t') • a0 + ((t / t') * t⁻¹) • (x - a0) := by
            have h_scalar : (t'⁻¹ : ℝ) = (t / t') * t⁻¹ := by
              field_simp [ht_pos.ne', ht'_pos.ne']
            simp [h_scalar]
          _ = ((t' - t) / t') • a0 + (t / t') • a0 + (t / t') • (t⁻¹ • (x - a0)) := by
            rw [smul_smul]
          _ = ((t' - t) / t') • a0 + (t / t') • (a0 + t⁻¹ • (x - a0)) := by
            rw [add_assoc, smul_add]
      rw [h_comb]
      have h_sum : (t' - t) / t' + t / t' = 1 := by
        field_simp [ht_pos.ne', ht'_pos.ne']
        ring
      have h1_nonneg : 0 ≤ (t' - t) / t' := div_nonneg (sub_nonneg.mpr ht_le) ht'_pos.le
      have h2_nonneg : 0 ≤ t / t' := div_nonneg ht_pos.le ht'_pos.le
      exact (convex_iff_add_mem.mp hQconv) ha0_in_Q ht_Q h1_nonneg h2_nonneg h_sum
    -- Pr (ρ/r) holds
    have hPr_ρ_div_r : Pr (ρ / r) := by
      have hpos : 0 < ρ / r := div_pos hρ_pos hr
      refine ⟨hpos, ?_⟩
      -- Show a0 + (ρ/r)⁻¹ • (x - a0) ∈ Q
      -- This point is at distance r from a0, so in oBall a0 r ⊆ Q
      have h_dist : oNorm (a0 + (ρ / r)⁻¹ • (x - a0) - a0) = r := by
        calc
          oNorm (a0 + (ρ / r)⁻¹ • (x - a0) - a0) = oNorm ((ρ / r)⁻¹ • (x - a0)) := by simp
          _ = |(ρ / r)⁻¹| * oNorm (x - a0) := oNorm_smul _ _
          _ = (ρ / r)⁻¹ * ρ := by
            rw [abs_of_pos (inv_pos.mpr hpos), hρ_def]
          _ = r := by
            field_simp [hr.ne', hρ_def]
      have h_in_ball : a0 + (ρ / r)⁻¹ • (x - a0) ∈ oBall a0 r := by
        dsimp [oBall]
        rw [h_dist]
      exact hball h_in_ball
    -- ¬ Pr (ρ/(2R)) holds
    have hR_pos : 0 < R := by
      have hR_nonneg : 0 ≤ R := by
        have ha0_in_ball : a0 ∈ oBall a0 r := by
          dsimp [oBall, oNorm]
          have : oNorm (a0 - a0) = 0 := by simp [oNorm]
          simp [hr.le]
        have ha0_in_Q : a0 ∈ Q := hball ha0_in_ball
        have ha0_in_QR : a0 ∈ oBall 0 R := hQR ha0_in_Q
        dsimp [oBall] at ha0_in_QR
        -- ha0_in_QR : oNorm a0 ≤ R
        -- oNorm a0 ≥ 0, so 0 ≤ R
        exact le_trans (oNorm_nonneg _) ha0_in_QR
      by_contra! hR_notpos
      have hR_zero : R = 0 := by linarith
      have ha0_zero : a0 = 0 := by
        have ha0_in_ball : a0 ∈ oBall a0 r := by
          dsimp [oBall, oNorm]
          have : oNorm (a0 - a0) = 0 := by simp [oNorm]
          simp [hr.le]
        have ha0_in_Q : a0 ∈ Q := hball ha0_in_ball
        have ha0_in_QR : a0 ∈ oBall 0 R := hQR ha0_in_Q
        rw [hR_zero] at ha0_in_QR
        have ha0_in_QR' : oNorm a0 ≤ 0 := by simpa [oBall, oNorm] using ha0_in_QR
        have h_norm_zero : oNorm a0 = 0 := by
          have h_nonneg := oNorm_nonneg a0
          linarith
        rw [oNorm_eq_zero_iff] at h_norm_zero
        exact h_norm_zero
      -- Now a0 = 0 and R = 0, so Q ⊆ oBall 0 0 = {0}
      -- But oBall a0 r = oBall 0 r contains nonzero points (since r > 0)
      -- This contradicts oBall a0 r ⊆ Q
      have h_nonzero_in_ball : ∃ y : Fin d → ℝ, y ∈ oBall a0 r ∧ y ≠ a0 := by
        -- If d = 0, then Fin 0 → ℝ has only one element, so x = a0, contradiction
        by_cases hd : d = 0
        · subst hd
          have : Subsingleton (Fin 0 → ℝ) := by infer_instance
          have hx_unique : x = a0 := Subsingleton.elim x a0
          exact (hx_eq_a0 hx_unique).elim
        · -- d ≥ 1, so there exists a nonzero basis vector
          have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
          -- Use the first basis vector e0
          let e0 : Fin d → ℝ := fun i => if i = ⟨0, hd_pos⟩ then 1 else 0
          refine ⟨a0 + r • e0, ?_, ?_⟩
          · dsimp [oBall, oNorm]
            have h_dist : oNorm ((a0 + r • e0) - a0) = r := by
              calc
                oNorm ((a0 + r • e0) - a0) = oNorm (r • e0) := by simp
                _ = |r| * oNorm e0 := oNorm_smul _ _
                _ = r * oNorm e0 := by rw [abs_of_pos hr]
                _ = r * Real.sqrt (e0 ⬝ᵥ e0) := rfl
                _ = r * Real.sqrt (1) := by
                  dsimp [e0, dotProduct]
                  simp
                _ = r := by simp
            exact h_dist.le
          · intro h_eq
            have : r • e0 = 0 := by
              apply add_left_cancel (a := a0)
              simpa using h_eq
            -- r > 0, so e0 = 0, contradiction
            have h_e0_zero : e0 = 0 := by
              rcases eq_zero_or_eq_zero_of_smul_eq_zero this with (hr_zero | h_e0_zero)
              · exact (hr.ne' hr_zero).elim
              · exact h_e0_zero
            -- But e0 is nonzero (it's 1 at index 0)
            have h_e0_one : e0 ⟨0, hd_pos⟩ = 1 := by simp [e0]
            rw [h_e0_zero] at h_e0_one
            simp at h_e0_one
      rcases h_nonzero_in_ball with ⟨y, hy_ball, hy_ne_a0⟩
      have hy_in_Q : y ∈ Q := hball hy_ball
      have hy_in_QR : y ∈ oBall 0 R := hQR hy_in_Q
      rw [hR_zero] at hy_in_QR
      have hy_in_QR' : oNorm y ≤ 0 := by simpa [oBall, oNorm] using hy_in_QR
      have hy_zero : y = 0 := by
        have h_norm_zero : oNorm y = 0 := by
          have h_nonneg := oNorm_nonneg y
          linarith
        rw [oNorm_eq_zero_iff] at h_norm_zero
        exact h_norm_zero
      -- Now y = 0 and a0 = 0, so y = a0, contradiction
      apply hy_ne_a0
      rw [hy_zero, ha0_zero]
    -- Now we know R > 0
    have hPr_not_ρ_div_2R : ¬ Pr (ρ / (2 * R)) := by
      intro hPr
      rcases hPr with ⟨hpos, hmem⟩
      -- hmem : a0 + (ρ / (2 * R))⁻¹ • (x - a0) ∈ Q
      -- Note: (ρ / (2 * R))⁻¹ = (2 * R) / ρ
      set p := a0 + ((2 * R) / ρ) • (x - a0) with hp_def
      have hp_in_Q : p ∈ Q := by
        -- rewrite hmem using the identity (ρ / (2 * R))⁻¹ = (2 * R) / ρ
        have h_eq : (ρ / (2 * R))⁻¹ • (x - a0) = ((2 * R) / ρ) • (x - a0) := by
          have h_inv_eq : (ρ / (2 * R))⁻¹ = (2 * R) / ρ := by
            field_simp [hρ_pos.ne']
          simp [h_inv_eq]
        simpa [p, h_eq] using hmem
      set q := a0 - (r / ρ) • (x - a0) with hq_def
      have hq_in_ball : q ∈ oBall a0 r := by
        dsimp [oBall, q]
        have h_dist : oNorm (a0 - (r / ρ) • (x - a0) - a0) = r := by
          calc
            oNorm (a0 - (r / ρ) • (x - a0) - a0) = oNorm (-((r / ρ) • (x - a0))) := by simp
            _ = oNorm ((r / ρ) • (x - a0)) := by
              dsimp [oNorm, dotProduct]
              simp
            _ = |r / ρ| * oNorm (x - a0) := oNorm_smul _ _
            _ = (r / ρ) * ρ := by
              rw [abs_of_pos (div_pos hr hρ_pos), hρ_def]
            _ = r := by field_simp [hρ_pos.ne']
        exact h_dist.le
      have hq_in_Q : q ∈ Q := hball hq_in_ball
      have hp_in_QR : p ∈ oBall 0 R := hQR hp_in_Q
      have hq_in_QR : q ∈ oBall 0 R := hQR hq_in_Q
      dsimp [oBall] at hp_in_QR hq_in_QR
      -- hp_in_QR : oNorm (p - 0) ≤ R, i.e., oNorm p ≤ R
      -- hq_in_QR : oNorm q ≤ R
      have hp_norm_le : oNorm p ≤ R := by simpa using hp_in_QR
      have hq_norm_le : oNorm q ≤ R := by simpa using hq_in_QR
      -- p - q = ((2R + r)/ρ) • (x - a0)
      have h_diff : p - q = ((2 * R + r) / ρ) • (x - a0) := by
        dsimp [p, q]
        calc
          (a0 + ((2 * R) / ρ) • (x - a0)) - (a0 - (r / ρ) • (x - a0))
              = ((2 * R) / ρ) • (x - a0) + (r / ρ) • (x - a0) := by ring
          _ = (((2 * R) / ρ) + (r / ρ)) • (x - a0) := by rw [add_smul]
          _ = ((2 * R + r) / ρ) • (x - a0) := by rw [add_div]
      have h_diff_norm : oNorm (p - q) = 2 * R + r := by
        rw [h_diff]
        rw [oNorm_smul]
        have h_pos : 0 ≤ (2 * R + r) / ρ := div_nonneg (by linarith) hρ_pos.le
        rw [abs_of_nonneg h_pos]
        field_simp [hρ_pos.ne']
        rw [hρ_def]
      -- Triangle inequality: oNorm (p - q) ≤ oNorm p + oNorm q
      have h_triangle : oNorm (p - q) ≤ oNorm p + oNorm q := by
        calc
          oNorm (p - q) = oNorm ((p - 0) - (q - 0)) := by simp
          _ ≤ oNorm (p - 0) + oNorm (q - 0) := oNorm_sub_le (p - 0) (q - 0)
          _ = oNorm p + oNorm q := by simp
      -- Now: 2R + r ≤ R + R = 2R, contradiction since r > 0
      have h_contra : 2 * R + r ≤ 2 * R := by
        calc
          2 * R + r = oNorm (p - q) := by symm; exact h_diff_norm
          _ ≤ oNorm p + oNorm q := h_triangle
          _ ≤ R + R := add_le_add hp_norm_le hq_norm_le
          _ = 2 * R := by ring
      linarith
    -- Prove r ≤ 2R to ensure the bisection interval is well-ordered
    have hr_le_2R : r ≤ 2 * R := by
      -- From oBall a0 r ⊆ Q ⊆ oBall 0 R, we have oBall a0 r ⊆ oBall 0 R
      -- Take y = a0 + r • e_i where e_i is a unit vector (exists since d ≥ 1, otherwise x = a0)
      by_cases hd : d = 0
      · subst hd
        have : Subsingleton (Fin 0 → ℝ) := by infer_instance
        have hx_unique : x = a0 := Subsingleton.elim x a0
        exact (hx_eq_a0 hx_unique).elim
      · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
        let e0 : Fin d → ℝ := fun i => if i = ⟨0, hd_pos⟩ then 1 else 0
        have h_norm_e0 : oNorm e0 = 1 := by
          dsimp [oNorm, e0, dotProduct]
          simp
        have h_in_ball : a0 + r • e0 ∈ oBall a0 r := by
          dsimp [oBall]
          have h_dist : oNorm ((a0 + r • e0) - a0) = r := by
            calc
              oNorm ((a0 + r • e0) - a0) = oNorm (r • e0) := by simp
              _ = |r| * oNorm e0 := oNorm_smul _ _
              _ = r * 1 := by rw [abs_of_pos hr, h_norm_e0]
              _ = r := by simp
          exact h_dist.le
        have h_in_QR : a0 + r • e0 ∈ oBall 0 R := hQR (hball h_in_ball)
        -- h_in_QR : a0 + r • e0 ∈ oBall 0 R, i.e., oNorm (a0 + r • e0 - 0) ≤ R
        -- By triangle inequality: r = oNorm (r • e0) = oNorm ((a0 + r • e0) - a0) ≤ oNorm (a0 + r • e0) + oNorm a0 ≤ R + R = 2R
        have h_in_QR_norm : oNorm (a0 + r • e0) ≤ R := by
          simpa [oBall] using h_in_QR
        have h_tri : oNorm ((a0 + r • e0) - a0) ≤ oNorm (a0 + r • e0) + oNorm a0 := oNorm_sub_le _ _
        have h_norm_a0_le_R : oNorm a0 ≤ R := by
          have ha0_in_ball : a0 ∈ oBall a0 r := by
            dsimp [oBall, oNorm]
            have : oNorm (a0 - a0) = 0 := by simp [oNorm]
            simp [hr.le]
          have ha0_in_QR : a0 ∈ oBall 0 R := hQR (hball ha0_in_ball)
          simpa [oBall] using ha0_in_QR
        calc
          r = oNorm (r • e0) := by
            rw [oNorm_smul, abs_of_pos hr, h_norm_e0]
            simp
          _ = oNorm ((a0 + r • e0) - a0) := by simp
          _ ≤ oNorm (a0 + r • e0) + oNorm a0 := h_tri
          _ ≤ R + R := add_le_add h_in_QR_norm h_norm_a0_le_R
          _ = 2 * R := by ring
    -- Now we have r ≤ 2R, so ρ/(2R) ≤ ρ/r
    have h_lo_le_hi : ρ / (2 * R) ≤ ρ / r := by
      have h_one_div : 1 / (2 * R) ≤ 1 / r :=
        (one_div_le_one_div (by linarith) hr).mpr hr_le_2R
      have h := mul_le_mul_of_nonneg_left h_one_div hρ_pos.le
      simpa [div_eq_mul_inv] using h
    -- Bisection invariant by induction on j
    have h_bisect_inv (j : ℕ) :
        (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 ≤ (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 ∧
        ¬ Pr (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 ∧
        Pr (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 ∧
        (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 =
        (ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ j) := by
      classical
      induction' j with j ih
      · -- j = 0: I = (ρ/(2R), ρ/r)
        dsimp [oBisect]
        refine ⟨h_lo_le_hi, hPr_not_ρ_div_2R, hPr_ρ_div_r, ?_⟩
        simp
      · -- j → j+1
        have h_prev := ih
        rcases h_prev with ⟨h_le, h_not_pr1, h_pr2, h_diff⟩
        -- The goal is about oBisect ... (j+1), which is defined as:
        -- (let I := oBisect ... j in if Pr ((I.1 + I.2)/2) then (I.1, (I.1+I.2)/2) else ((I.1+I.2)/2, I.2))
        -- We need to rewrite using the condition Pr at the midpoint.
        by_cases h_mid : Pr (((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 + (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) / 2)
        · -- Pr holds at midpoint: new I = (I_prev.1, midpoint)
          have h_if_pos : oBisect Pr (ρ / (2 * R)) (ρ / r) (j + 1) = ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1, ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 + (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) / 2) := by
            dsimp [oBisect]
            simp [h_mid]
          rw [h_if_pos]
          refine ⟨by linarith, h_not_pr1, h_mid, ?_⟩
          simp
          -- Goal: (I.1 + I.2)/2 - I.1 = (ρ/r - ρ/(2R)) / 2^(j+1)
          -- LHS = (I.2 - I.1)/2
          -- h_diff: I.2 - I.1 = (ρ/r - ρ/(2R)) / 2^j
          -- So RHS = ((ρ/r - ρ/(2R)) / 2^j) / 2 = (ρ/r - ρ/(2R)) / 2^(j+1)
          calc
            ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 + (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) / 2 -
                (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 =
              ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1) / 2 := by ring
            _ = ((ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ j)) / 2 := by rw [h_diff]
            _ = (ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ (j + 1)) := by ring
        · -- Pr does not hold at midpoint: new I = (midpoint, I_prev.2)
          have h_if_neg : oBisect Pr (ρ / (2 * R)) (ρ / r) (j + 1) = (((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 + (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) / 2, (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) := by
            dsimp [oBisect]
            simp [h_mid]
          rw [h_if_neg]
          refine ⟨by linarith, h_mid, h_pr2, ?_⟩
          simp
          -- Goal: I.2 - (I.1 + I.2)/2 = (ρ/r - ρ/(2R)) / 2^(j+1)
          -- LHS = (I.2 - I.1)/2
          calc
            (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 -
                ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 + (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2) / 2 =
              ((oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1) / 2 := by ring
            _ = ((ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ j)) / 2 := by rw [h_diff]
            _ = (ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ (j + 1)) := by ring
    -- Now use the bisection invariant to bound |oGaugeVal - oGauge|
    set j := oValSteps a0 r x η with hj_def
    have h_inv := h_bisect_inv j
    rcases h_inv with ⟨h_le, h_not_pr1, h_pr2, h_diff⟩
    -- oGaugeVal Q a0 r R x η = (oBisect ... j).2
    have h_gauge_val_eq : oGaugeVal Q a0 r R x η = (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 := by
      dsimp [oGaugeVal, Pr, ρ]
      rw [ite_eq_right hx_eq_a0]
    -- oGauge Q a0 x = sInf S = sInf {t | Pr t}
    have h_gauge_eq' : oGauge Q a0 x = sInf {t : ℝ | Pr t} := by
      dsimp [oGauge, S, Pr]
    -- We have: sInf S ≤ I.2 (since Pr I.2, so I.2 is in the set)
    have h_sInf_le : sInf {t : ℝ | Pr t} ≤ (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 := by
      apply csInf_le
      · -- the set is bounded below by 0
        refine ⟨0, fun t ht => ?_⟩
        rcases ht with ⟨ht_pos, _⟩
        exact ht_pos.le
      · -- Pr I.2, so I.2 ∈ {t | Pr t}
        exact h_pr2
    -- We have: I.1 ≤ sInf S (since every t ∈ S has t ≥ I.1)
    have h_le_sInf : (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 ≤ sInf {t : ℝ | Pr t} := by
      apply le_csInf
      · -- the set is nonempty (since Pr (ρ/r) holds)
        exact ⟨ρ / r, hPr_ρ_div_r⟩
      · -- for every t in the set, I.1 ≤ t
        intro t ht
        rcases ht with ⟨ht_pos, ht_mem⟩
        by_contra! h_lt
        -- t < I.1, and Pr t holds (since t ∈ S)
        -- By monotonicity, Pr I.1 holds, contradiction
        have h_pr_I1 : Pr (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 :=
          hPr_mono t (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 ⟨ht_pos, ht_mem⟩ (by linarith)
        exact h_not_pr1 h_pr_I1
    -- Now: |I.2 - sInf S| ≤ I.2 - I.1 ≤ ρ/(r 2^j)
    have h_diff_bound : |(oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - sInf {t : ℝ | Pr t}| ≤ ρ / (r * ((2 : ℝ) ^ j)) := by
      have h_nonneg : 0 ≤ (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - sInf {t : ℝ | Pr t} := by linarith
      rw [abs_of_nonneg h_nonneg]
      calc
        (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - sInf {t : ℝ | Pr t} ≤
            (oBisect Pr (ρ / (2 * R)) (ρ / r) j).2 - (oBisect Pr (ρ / (2 * R)) (ρ / r) j).1 :=
          sub_le_sub_left h_le_sInf _
        _ = (ρ / r - ρ / (2 * R)) / ((2 : ℝ) ^ j) := h_diff
        _ ≤ (ρ / r) / ((2 : ℝ) ^ j) := by
          have h_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          have h_nonneg_ρ_div_2R : 0 ≤ ρ / (2 * R) := div_nonneg hρ_pos.le (by linarith)
          linarith
        _ = ρ / (r * ((2 : ℝ) ^ j)) := by ring
    -- Now use j = oValSteps a0 r x η = ⌈Real.logb 2 (ρ/(r η))⌉₊
    -- We need: ρ/(r * 2^j) ≤ η
    have h_j_bound : ρ / (r * ((2 : ℝ) ^ j)) ≤ η := by
      have h_ratio_pos : 0 < ρ / (r * η) := div_pos hρ_pos (mul_pos hr hηpos)
      have h_j_ge_logb : Real.logb 2 (ρ / (r * η)) ≤ (j : ℝ) := by
        have h_ceil_eq : j = Nat.ceil (Real.logb 2 (ρ / (r * η))) := by
          dsimp [j, oValSteps, ρ]
        have h_ceil_le_j_nat : Nat.ceil (Real.logb 2 (ρ / (r * η))) ≤ j :=
          h_ceil_eq.symm.le
        exact (Nat.ceil_le.mp h_ceil_le_j_nat)
      have h_rpow : (2 : ℝ) ^ Real.logb 2 (ρ / (r * η)) ≤ (2 : ℝ) ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h_j_ge_logb
      have h_rpow_logb : (2 : ℝ) ^ Real.logb 2 (ρ / (r * η)) = ρ / (r * η) :=
        Real.rpow_logb (by norm_num) (by norm_num) h_ratio_pos
      rw [h_rpow_logb] at h_rpow
      have h_rpow_nat : (2 : ℝ) ^ (j : ℝ) = ((2 : ℝ) ^ j : ℝ) := by
        simp [Real.rpow_natCast]
      rw [h_rpow_nat] at h_rpow
      have h_pos_rη : 0 < r * η := mul_pos hr hηpos
      have h_pos_r2j : 0 < r * ((2 : ℝ) ^ j) := mul_pos hr (pow_pos (by norm_num) j)
      have h_mul : ρ ≤ (r * η) * ((2 : ℝ) ^ j) :=
        (div_le_iff₀' h_pos_rη).mp h_rpow
      have h_mul' : ρ ≤ (r * ((2 : ℝ) ^ j)) * η := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
      exact (div_le_iff₀' h_pos_r2j).mpr h_mul'
    -- Combine everything
    rw [h_gauge_val_eq, h_gauge_eq']
    linarith

theorem lemmaGCAP : LemmaGCAP := by
  intro d Q a0 r R ηmin B x η hr hηmin hB hxnorm hηle
  unfold oGaugeValCap oGaugeVal oValSteps
  by_cases hzero : oNorm (x - a0) = 0
  · -- case oNorm (x - a0) = 0: then oValSteps = 0 ≤ B
    have hzero_div : oNorm (x - a0) / (r * η) = (0 : ℝ) := by simp [hzero]
    have hlogb : Real.logb 2 (oNorm (x - a0) / (r * η)) = (0 : ℝ) := by simp [hzero_div]
    have hceil : ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊ = (0 : ℕ) := by simp [hlogb]
    have hnotlt : ¬ (B < ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊) := by
      rw [hceil]
      exact Nat.not_lt_zero _
    simp [hnotlt]
  · -- case oNorm (x - a0) > 0
    have hpos : 0 < oNorm (x - a0) := by
      have hnonneg : 0 ≤ oNorm (x - a0) := by
        unfold oNorm
        exact Real.sqrt_nonneg _
      by_contra! hle
      apply hzero
      linarith
    have hηpos : 0 < η := lt_of_lt_of_le hηmin hηle
    have h_rη_pos : 0 < r * η := mul_pos hr hηpos
    have h_rηmin_pos : 0 < r * ηmin := mul_pos hr hηmin
    have h_3R_nonneg : 0 ≤ 3 * R := by
      have hnonneg : 0 ≤ oNorm (x - a0) := by
        unfold oNorm
        exact Real.sqrt_nonneg _
      linarith
    -- show oNorm (x - a0) / (r * η) ≤ 3 * R / (r * ηmin)
    have h_div_le : oNorm (x - a0) / (r * η) ≤ 3 * R / (r * ηmin) := by
      have h1 : oNorm (x - a0) / (r * η) ≤ (3 * R) / (r * η) :=
        div_le_div_of_nonneg_right hxnorm (by positivity)
      have h2 : (3 * R) / (r * η) ≤ (3 * R) / (r * ηmin) :=
        div_le_div_of_nonneg_left h_3R_nonneg (by positivity) (by
          nlinarith)
      exact le_trans h1 h2
    have h_logb_le : Real.logb 2 (oNorm (x - a0) / (r * η)) ≤ Real.logb 2 (3 * R / (r * ηmin)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h_div_le
    have h_ceil_le : ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊ ≤ ⌈Real.logb 2 (3 * R / (r * ηmin))⌉₊ :=
      Nat.ceil_mono h_logb_le
    have h_ceil_le_B : ⌈Real.logb 2 (3 * R / (r * ηmin))⌉₊ ≤ B := hB
    have h_ceil_le_B' : ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊ ≤ B :=
      le_trans h_ceil_le h_ceil_le_B
    have hnotlt : ¬ (B < ⌈Real.logb 2 (oNorm (x - a0) / (r * η))⌉₊) :=
      not_lt.mpr h_ceil_le_B'
    simp [hnotlt]

theorem ellF_sub_le {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef)
    (w z p : Fin d → ℝ) (R : ℝ) (hz : oNorm z ≤ R) (hp : oNorm p ≤ R) :
    ellF P w z - ellF P w p ≤ P.trace * (R + oNorm w) * oNorm (z - p) := by
  -- Let u = z - w, v = p - w
  set u := z - w with hu
  set v := p - w with hv
  have h_symm : Pᵀ = P := hP.1.isSymm.eq
  have h_trace_nonneg : 0 ≤ P.trace := hP.trace_nonneg
  -- Key identity: ellF P w z - ellF P w p = (1/2) * ((u - v) ⬝ᵥ P *ᵥ (u + v))
  have h_diff : ellF P w z - ellF P w p = (1/2 : ℝ) * ((u - v) ⬝ᵥ P *ᵥ (u + v)) := by
    calc
      ellF P w z - ellF P w p
          = ((1/2 : ℝ) * ((z - w) ⬝ᵥ P *ᵥ (z - w))) - ((1/2 : ℝ) * ((p - w) ⬝ᵥ P *ᵥ (p - w))) := rfl
      _ = (1/2 : ℝ) * (((z - w) ⬝ᵥ P *ᵥ (z - w)) - ((p - w) ⬝ᵥ P *ᵥ (p - w))) := by ring
      _ = (1/2 : ℝ) * ((u - v) ⬝ᵥ P *ᵥ (u + v)) := by
        have h_id : (u - v) ⬝ᵥ P *ᵥ (u + v) = u ⬝ᵥ P *ᵥ u - v ⬝ᵥ P *ᵥ v := by
          calc
            (u - v) ⬝ᵥ P *ᵥ (u + v)
                = (u - v) ⬝ᵥ (P *ᵥ u + P *ᵥ v) := by rw [Matrix.mulVec_add]
            _ = (u - v) ⬝ᵥ (P *ᵥ u) + (u - v) ⬝ᵥ (P *ᵥ v) := by rw [dotProduct_add]
            _ = (u ⬝ᵥ (P *ᵥ u) - v ⬝ᵥ (P *ᵥ u)) + (u ⬝ᵥ (P *ᵥ v) - v ⬝ᵥ (P *ᵥ v)) := by
              simp [sub_dotProduct]
            _ = u ⬝ᵥ (P *ᵥ u) + u ⬝ᵥ (P *ᵥ v) - v ⬝ᵥ (P *ᵥ u) - v ⬝ᵥ (P *ᵥ v) := by ring
            _ = u ⬝ᵥ (P *ᵥ u) + u ⬝ᵥ (P *ᵥ v) - u ⬝ᵥ (P *ᵥ v) - v ⬝ᵥ (P *ᵥ v) := by
              have h_cross : v ⬝ᵥ P *ᵥ u = u ⬝ᵥ P *ᵥ v := by
                calc
                  v ⬝ᵥ P *ᵥ u = v ᵥ* P ⬝ᵥ u := by rw [dotProduct_mulVec]
                  _ = (v ᵥ* Pᵀ) ⬝ᵥ u := by rw [h_symm]
                  _ = (P *ᵥ v) ⬝ᵥ u := by rw [Matrix.vecMul_transpose]
                  _ = u ⬝ᵥ P *ᵥ v := by rw [dotProduct_comm]
              rw [h_cross]
            _ = u ⬝ᵥ (P *ᵥ u) - v ⬝ᵥ (P *ᵥ v) := by ring
        rw [h_id]
  rw [h_diff]
  -- Now we need to show: (1/2) * ((u - v) ⬝ᵥ P *ᵥ (u + v)) ≤ P.trace * (R + oNorm w) * oNorm (z - p)
  -- First, note that u - v = z - p
  have h_uz : u - v = z - p := by
    dsimp [u, v]
    abel
  rw [h_uz]
  -- Set X = (z - p) ⬝ᵥ P *ᵥ (u + v) for brevity
  set X := (z - p) ⬝ᵥ P *ᵥ (u + v) with hX
  -- We need to show: (1/2) * X ≤ P.trace * (R + oNorm w) * oNorm (z - p)
  -- Equivalently: X ≤ 2 * P.trace * (R + oNorm w) * oNorm (z - p)
  -- Since P.trace ≥ 0 and R + oNorm w ≥ 0 (from hz, hp, oNorm nonneg), the RHS is ≥ 0
  -- So it suffices to show X² ≤ (2 * P.trace * (R + oNorm w) * oNorm (z - p))²
  have h_nonneg_onorm_zp : 0 ≤ oNorm (z - p) := by
    rw [oNorm]
    exact Real.sqrt_nonneg _
  have h_onorm_z_nonneg : 0 ≤ oNorm z := by
    rw [oNorm]
    exact Real.sqrt_nonneg _
  have h_onorm_p_nonneg : 0 ≤ oNorm p := by
    rw [oNorm]
    exact Real.sqrt_nonneg _
  have h_onorm_w_nonneg : 0 ≤ oNorm w := by
    rw [oNorm]
    exact Real.sqrt_nonneg _
  have hR_nonneg : 0 ≤ R := by
    linarith
  have h_nonneg_R_plus_ow : 0 ≤ R + oNorm w := by
    nlinarith
  have h_nonneg_rhs : 0 ≤ 2 * P.trace * (R + oNorm w) * oNorm (z - p) := by
    have : 0 ≤ 2 * P.trace := by nlinarith
    have : 0 ≤ 2 * P.trace * (R + oNorm w) := by nlinarith
    nlinarith
  -- Apply Cauchy-Schwarz: X² ≤ ((z-p) ⬝ᵥ P *ᵥ (z-p)) * ((u+v) ⬝ᵥ P *ᵥ (u+v))
  have h_cauchy : X ^ 2 ≤ ((z - p) ⬝ᵥ P *ᵥ (z - p)) * ((u + v) ⬝ᵥ P *ᵥ (u + v)) := by
    rw [hX]
    exact LeanAp.dot_mulVec_sq_le P hP (z - p) (u + v)
  -- Apply trace bound to each term
  have h_trace1 : (z - p) ⬝ᵥ P *ᵥ (z - p) ≤ P.trace * ((z - p) ⬝ᵥ (z - p)) :=
    LeanAp.trace_quad_le P hP (z - p)
  have h_trace2 : (u + v) ⬝ᵥ P *ᵥ (u + v) ≤ P.trace * ((u + v) ⬝ᵥ (u + v)) :=
    LeanAp.trace_quad_le P hP (u + v)
  -- Relate dot products to oNorm
  have h_onorm_sq_zp : (oNorm (z - p)) ^ 2 = (z - p) ⬝ᵥ (z - p) := by
    rw [oNorm, Real.sq_sqrt (by
      have h := dotProduct_star_self_nonneg (z - p)
      simpa [star_id_of_comm] using h)]
  have h_onorm_sq_uv : (oNorm (u + v)) ^ 2 = (u + v) ⬝ᵥ (u + v) := by
    rw [oNorm, Real.sq_sqrt (by
      have h := dotProduct_star_self_nonneg (u + v)
      simpa [star_id_of_comm] using h)]
  -- Combine everything
  have h_sq_bound : X ^ 2 ≤ (P.trace * oNorm (z - p) * oNorm (u + v)) ^ 2 := by
    have h_mul : ((z - p) ⬝ᵥ P *ᵥ (z - p)) * ((u + v) ⬝ᵥ P *ᵥ (u + v)) ≤
        (P.trace * oNorm (z - p) * oNorm (u + v)) ^ 2 := by
      calc
        ((z - p) ⬝ᵥ P *ᵥ (z - p)) * ((u + v) ⬝ᵥ P *ᵥ (u + v))
            ≤ (P.trace * ((z - p) ⬝ᵥ (z - p))) * (P.trace * ((u + v) ⬝ᵥ (u + v))) := by
          have h1 : (z - p) ⬝ᵥ P *ᵥ (z - p) ≤ P.trace * ((z - p) ⬝ᵥ (z - p)) := h_trace1
          have h2 : (u + v) ⬝ᵥ P *ᵥ (u + v) ≤ P.trace * ((u + v) ⬝ᵥ (u + v)) := h_trace2
          have h_nonneg_1 : 0 ≤ (z - p) ⬝ᵥ P *ᵥ (z - p) := by
            have := hP.dotProduct_mulVec_nonneg (z - p)
            simpa [star_id_of_comm] using this
          have h_nonneg_2 : 0 ≤ (u + v) ⬝ᵥ P *ᵥ (u + v) := by
            have := hP.dotProduct_mulVec_nonneg (u + v)
            simpa [star_id_of_comm] using this
          nlinarith
        _ = (P.trace ^ 2) * (((z - p) ⬝ᵥ (z - p)) * ((u + v) ⬝ᵥ (u + v))) := by ring
        _ = (P.trace ^ 2) * ((oNorm (z - p)) ^ 2 * (oNorm (u + v)) ^ 2) := by
          rw [h_onorm_sq_zp, h_onorm_sq_uv]
        _ = (P.trace * oNorm (z - p) * oNorm (u + v)) ^ 2 := by ring
    have hX_sq : X ^ 2 ≤ ((z - p) ⬝ᵥ P *ᵥ (z - p)) * ((u + v) ⬝ᵥ P *ᵥ (u + v)) := h_cauchy
    nlinarith
  -- Now we need oNorm (u + v) ≤ 2 * (R + oNorm w)
  have h_onorm_uv_bound : oNorm (u + v) ≤ 2 * (R + oNorm w) := by
    calc
      oNorm (u + v) = oNorm ((z - w) + (p - w)) := by rw [hu, hv]
      _ = oNorm (z + p - (2 : ℝ) • w) := by
        congr 1
        ext i
        simp
        ring
      _ ≤ oNorm (z + p) + oNorm (-((2 : ℝ) • w)) := oNorm_add_le _ _
      _ = oNorm (z + p) + oNorm ((-2 : ℝ) • w) := by simp
      _ = oNorm (z + p) + |(-2 : ℝ)| * oNorm w := by rw [oNorm_smul]
      _ = oNorm (z + p) + 2 * oNorm w := by norm_num
      _ ≤ (oNorm z + oNorm p) + 2 * oNorm w := by
        nlinarith [oNorm_add_le z p]
      _ ≤ (R + R) + 2 * oNorm w := by nlinarith
      _ = 2 * (R + oNorm w) := by ring
  -- Now we have X² ≤ (P.trace * oNorm(z-p) * oNorm(u+v))² ≤ (P.trace * oNorm(z-p) * 2*(R+oNorm w))²
  have h_final_sq : X ^ 2 ≤ (2 * P.trace * (R + oNorm w) * oNorm (z - p)) ^ 2 := by
    have h_bound : P.trace * oNorm (z - p) * oNorm (u + v) ≤
        2 * P.trace * (R + oNorm w) * oNorm (z - p) := by
      have h_nonneg_Ptrace : 0 ≤ P.trace := h_trace_nonneg
      have h_nonneg_onorm_zp' : 0 ≤ oNorm (z - p) := h_nonneg_onorm_zp
      have h_nonneg_prod : 0 ≤ P.trace * oNorm (z - p) := by
        nlinarith
      calc
        P.trace * oNorm (z - p) * oNorm (u + v)
            = (P.trace * oNorm (z - p)) * oNorm (u + v) := by ring
        _ ≤ (P.trace * oNorm (z - p)) * (2 * (R + oNorm w)) := by
          nlinarith
        _ = P.trace * oNorm (z - p) * (2 * (R + oNorm w)) := by ring
        _ = 2 * P.trace * (R + oNorm w) * oNorm (z - p) := by ring
    have h_sq_nonneg : 0 ≤ P.trace * oNorm (z - p) * oNorm (u + v) := by
      have h_onorm_uv_nonneg : 0 ≤ oNorm (u + v) := by
        rw [oNorm]
        exact Real.sqrt_nonneg _
      have h_prod_nonneg : 0 ≤ P.trace * oNorm (z - p) := by
        nlinarith
      nlinarith
    nlinarith
  -- Since both sides are nonnegative, we can take square roots
  have h_final : X ≤ 2 * P.trace * (R + oNorm w) * oNorm (z - p) := by
    have := abs_le_of_sq_le_sq' h_final_sq h_nonneg_rhs
    rcases this with ⟨_, h_high⟩
    exact h_high
  -- Therefore (1/2) * X ≤ P.trace * (R + oNorm w) * oNorm (z - p)
  nlinarith

/-- Lemma E.4. -/
theorem lemmaCC : LemmaCC := by
  intro d A a c hd hA hc
  have hdet := cc_det A a c hd hA hc
  refine ⟨cc_posDef A a c hd hA hc, fun x hx hcx => cc_incl A a c hd hA hc x hx hcx, hdet, ?_⟩
  rw [hdet, mul_assoc]
  exact mul_le_mul_of_nonneg_left (cc_factor_le d hd) hA.det_pos.le

/-! ## Proposition ELL -/

theorem ellF_eq_zero {P : Matrix (Fin d) (Fin d) ℝ} {w a : Fin d → ℝ} (h : P *ᵥ (a - w) = 0) : ellF P w a = 0 := by
  simp [ellF, h]

theorem ellF_nonneg {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (w x : Fin d → ℝ) : 0 ≤ ellF P w x := by
  unfold ellF
  have := hP.dotProduct_mulVec_nonneg (x - w)
  simp only [star_trivial] at this
  linarith

/-- Convexity of `F` at `a`: `F(z) ≥ F(a) + ⟨P (a - w), z - a⟩`. -/
theorem ellF_ge {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (w a z : Fin d → ℝ) :
    ellF P w a + (P *ᵥ (a - w)) ⬝ᵥ (z - a) ≤ ellF P w z := by
  unfold ellF
  have hsym : Pᵀ = P := hP.1.eq
  have h0 := hP.dotProduct_mulVec_nonneg (z - a)
  simp only [star_trivial] at h0
  have hzw : z - w = (z - a) + (a - w) := by abel
  have hcross : (z - a) ⬝ᵥ (P *ᵥ (a - w)) = (a - w) ⬝ᵥ (P *ᵥ (z - a)) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  rw [hzw, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hcross, dotProduct_comm (P *ᵥ (a - w))]
  linarith

theorem trace_pos_of_posDef {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (hd : 1 ≤ d) : 0 < P.trace := by
  unfold Matrix.trace
  have hpos : ∀ i, 0 < P.diag i := by
    intro i
    have := hP.dotProduct_mulVec_pos (x := Pi.single i 1) (by simp)
    simpa [Matrix.diag, dotProduct, Pi.single_apply, Matrix.mulVec] using this
  exact Finset.sum_pos (fun i _ => hpos i) ⟨⟨0, hd⟩, Finset.mem_univ _⟩

/-- The ball `B(a₀, r)` in `B_R` gives `|a₀| + r ≤ R`. -/
theorem ball_in_ball {a0 : Fin d → ℝ} {r R : ℝ} (hd : 1 ≤ d) (hr : 0 < r) (h : oBall a0 r ⊆ oBall 0 R) :
    oNorm a0 + r ≤ R := by
  by_cases ha : a0 = 0
  · subst ha
    have := h (show (r • oUnit (⟨0, hd⟩ : Fin d)) ∈ oBall 0 r by
      simp [oBall, oNorm_smul, oNorm_oUnit, abs_of_pos hr])
    simp only [oBall, Set.mem_ofPred_eq, sub_zero, oNorm_smul, oNorm_oUnit, abs_of_pos hr, mul_one] at this
    simp [oNorm_zero, this]
  · have hn : 0 < oNorm a0 := lt_of_le_of_ne (oNorm_nonneg _) (fun h0 => ha (oNorm_eq_zero.mp h0.symm))
    set u := (r / oNorm a0) • a0
    have hu : oNorm u = r := by rw [oNorm_smul, abs_of_pos (by positivity)]; field_simp
    have := h (show a0 + u ∈ oBall a0 r by simp [oBall, hu])
    simp only [oBall, Set.mem_ofPred_eq, sub_zero] at this
    have heq : a0 + u = (1 + r / oNorm a0) • a0 := by rw [add_smul, one_smul]
    rw [heq, oNorm_smul, abs_of_pos (by positivity)] at this
    have : (1 + r / oNorm a0) * oNorm a0 = oNorm a0 + r := by field_simp
    linarith

/-- Step 2 of ELL-cap: at a centre `a ∉ Q` with `|a| ≤ R`, SEP on the gauge returns a vector `g ≠ 0` whose cut keeps
every point `z` with `B(z, ε_Q) ⊆ Q`. -/
theorem step2_cut {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {r R τ ℓ1 εQ : ℝ} {J B : ℕ} (hd : 1 ≤ d)
    (hQ : Convex ℝ Q) (hcl : IsClosed Q) (hr : 0 < r) (hball : oBall a0 r ⊆ Q) (hQR : Q ⊆ oBall 0 R)
    (hτ : 0 < τ) (hτr : τ ≤ 1 / r) (hℓ1 : 0 < ℓ1) (hεQ : 0 < εQ) (hεR : εQ ≤ R / 2)
    (hℓ1r : 2 * ℓ1 / r = εQ / (12 * R)) (hℓ1R : ℓ1 ≤ R / 48) (hℓ1ε : 2 * ℓ1 ≤ εQ / 12)
    (hτd : τ * (Real.sqrt d * (3 * R)) ≤ εQ / (12 * R))
    (hJ : J = ⌈Real.logb 2 (8 * (1 / r) / τ)⌉₊)
    (hB : ⌈Real.logb 2 (3 * R / (r * (τ * ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (J + 1))))))⌉₊ ≤ B)
    (a : Fin d → ℝ) (haR : oNorm a ≤ R) (haQ : a ∉ Q) :
    ∃ y g, sep (oGaugeValCap Q a0 r R B) a τ ℓ1 (1 / r) J = some (y, g) ∧ g ≠ 0 ∧
      ∀ z, oBall z εQ ⊆ Q → g ⬝ᵥ (z - a) < 0 := by
  subst hJ
  have hR : 0 < R := by linarith
  obtain ⟨hγconv, hγLip, hγbd, hγmem⟩ := lemmaGAUGE d Q a0 r R hQ hcl hr hball hQR
  have ha0 : a0 ∈ Q := hball (by simp [oBall, oNorm_zero, hr.le])
  have ha0R : oNorm a0 ≤ R := by simpa [oBall] using hQR ha0
  set γ := oGauge Q a0 with hγ
  have hev : ∀ x η, oNorm (x - a) ≤ 2 * ℓ1 →
      τ * ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (⌈Real.logb 2 (8 * (1 / r) / τ)⌉₊ + 1))) ≤ η →
      ∃ v, oGaugeValCap Q a0 r R B x η = some v ∧ |v - γ x| ≤ η := by
    intro x η hx hη
    have hηm : 0 < τ * ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (⌈Real.logb 2 (8 * (1 / r) / τ)⌉₊ + 1))) := by
      positivity
    have hx3 : oNorm (x - a0) ≤ 3 * R := by
      have h1 : oNorm (x - a0) ≤ oNorm (x - a) + oNorm (a - a0) := oNorm_sub_sub_le x a a0
      have h2 : oNorm (a - a0) ≤ oNorm a + oNorm a0 := oNorm_sub_le a a0
      linarith
    refine ⟨_, lemmaGCAP d Q a0 r R _ B x η hr hηm hB hx3 hη, ?_⟩
    exact lemmaGVAL d Q a0 r R hQ hr hball hQR x η (lt_of_lt_of_le hηm hη)
  obtain ⟨y, g, hsep, hy, hsub⟩ := lemmaSEP d γ (1 / r) τ ℓ1 a (oGaugeValCap Q a0 r R B) hd hγconv hγLip hτ hτr
    hℓ1 hev
  refine ⟨y, g, hsep, ?_⟩
  -- the gauge at `a`, `y`, `a₀`
  have hγa : 1 < γ a := lt_of_not_ge (fun h => haQ ((hγmem a).mp h))
  have hya : oNorm (y - a) ≤ 2 * ℓ1 := by linarith
  have hγy : 1 - εQ / (12 * R) ≤ γ y := by
    have := hγLip a y
    rw [abs_le, oNorm_sub_comm] at this
    have h2 : 1 / r * oNorm (y - a) ≤ 2 * ℓ1 / r := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hya hr.le
    linarith [this.1]
  have hγa0 : γ a0 = 0 := by
    have := hγbd a0
    simp only [sub_self, oNorm_zero, zero_div] at this
    linarith [this.1, this.2]
  have hyR : oNorm y ≤ R + 2 * ℓ1 := by
    have : oNorm y ≤ oNorm (y - a) + oNorm a := by
      have := oNorm_add_le (y - a) a; rwa [sub_add_cancel] at this
    linarith
  -- the cut inequality at points of `Q`
  have hcut : ∀ z ∈ Q, g ⬝ᵥ (z - y) ≤ εQ / (6 * R) := by
    intro z hz
    have hzR : oNorm z ≤ R := by simpa [oBall] using hQR hz
    have hγz : γ z ≤ 1 := (hγmem z).mpr hz
    have hl1 : ∑ i, |z i - y i| ≤ Real.sqrt d * (3 * R) := by
      have h1 := l1_le_sqrt_mul (z - y)
      simp only [Pi.sub_apply] at h1
      have h2 : oNorm (z - y) ≤ 3 * R := by have := oNorm_sub_le z y; linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    have h3 : τ * ∑ i, |z i - y i| ≤ εQ / (12 * R) := (mul_le_mul_of_nonneg_left hl1 hτ.le).trans hτd
    have h4 := hsub z
    have : εQ / (6 * R) = εQ / (12 * R) + εQ / (12 * R) := by field_simp; ring
    linarith
  -- `⟨g, y - a₀⟩ ≥ 11/12`
  have hga0 : 11 / 12 ≤ g ⬝ᵥ (y - a0) := by
    have hl1 : ∑ i, |a0 i - y i| ≤ Real.sqrt d * (3 * R) := by
      have h1 := l1_le_sqrt_mul (a0 - y)
      simp only [Pi.sub_apply] at h1
      have h2 : oNorm (a0 - y) ≤ 3 * R := by have := oNorm_sub_le a0 y; linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    have h3 : τ * ∑ i, |a0 i - y i| ≤ εQ / (12 * R) := (mul_le_mul_of_nonneg_left hl1 hτ.le).trans hτd
    have h4 := hsub a0
    rw [hγa0] at h4
    have h5 : g ⬝ᵥ (y - a0) = -(g ⬝ᵥ (a0 - y)) := by rw [← dotProduct_neg, neg_sub]
    have h6 : εQ / (12 * R) ≤ 1 / 24 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hya0 : oNorm (y - a0) ≤ 49 / 24 * R := by
    have h1 : oNorm (y - a0) ≤ oNorm (y - a) + oNorm (a - a0) := oNorm_sub_sub_le y a a0
    have h2 : oNorm (a - a0) ≤ oNorm a + oNorm a0 := oNorm_sub_le a a0
    linarith
  have hgn : 22 / (49 * R) ≤ oNorm g := by
    have h1 := dot_le g (y - a0)
    have h2 : oNorm g * oNorm (y - a0) ≤ oNorm g * (49 / 24 * R) :=
      mul_le_mul_of_nonneg_left hya0 (oNorm_nonneg g)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hgpos : 0 < oNorm g := lt_of_lt_of_le (by positivity) hgn
  refine ⟨fun h0 => by rw [h0, oNorm_zero] at hgpos; exact lt_irrefl 0 hgpos, ?_⟩
  intro z hzball
  set z' := z + (εQ / oNorm g) • g with hz'
  have hz'Q : z' ∈ Q := by
    apply hzball
    simp only [oBall, Set.mem_ofPred_eq, hz', add_sub_cancel_left, oNorm_smul]
    rw [abs_of_pos (by positivity)]
    field_simp
    rfl
  have h1 := hcut z' hz'Q
  have hgg : g ⬝ᵥ g = oNorm g ^ 2 := (oNorm_sq g).symm
  have h2 : g ⬝ᵥ (z' - y) = g ⬝ᵥ (z - y) + εQ * oNorm g := by
    rw [hz', show z + (εQ / oNorm g) • g - y = (z - y) + (εQ / oNorm g) • g by abel, dotProduct_add,
      dotProduct_smul, hgg, smul_eq_mul]
    field_simp
  have h3 : g ⬝ᵥ (y - a) ≤ oNorm g * (2 * ℓ1) :=
    (dot_le g (y - a)).trans (mul_le_mul_of_nonneg_left hya (oNorm_nonneg g))
  have h4 : g ⬝ᵥ (z - a) = g ⬝ᵥ (z - y) + g ⬝ᵥ (y - a) := by
    rw [← dotProduct_add]; congr 1; abel
  have h5 : oNorm g * (2 * ℓ1) ≤ oNorm g * (εQ / 12) := mul_le_mul_of_nonneg_left hℓ1ε (oNorm_nonneg g)
  have h6 : εQ / (6 * R) < 11 / 12 * εQ * (22 / (49 * R)) := by
    rw [div_lt_iff₀ (by positivity)]
    have : 11 / 12 * εQ * (22 / (49 * R)) * (6 * R) = 11 * 22 * 6 / (12 * 49) * εQ := by field_simp
    rw [this]; nlinarith
  have h7 : 11 / 12 * εQ * (22 / (49 * R)) ≤ 11 / 12 * εQ * oNorm g := by gcongr
  nlinarith

/-- The invariant of ELL-cap under the hypotheses of Proposition ELL: `B(c, ρ)` stays in the ellipsoid until a
recorded point reaches the target value. -/
def EllGood (Q : Set (Fin d → ℝ)) (P : Matrix (Fin d) (Fin d) ℝ) (w c : Fin d → ℝ) (ρ target X : ℝ)
    (st : EllSt d) : Prop :=
  st.A.PosDef ∧ st.A.det ≤ X ∧ (∀ b, st.best = some b → b ∈ Q) ∧
    ((∀ z ∈ oBall c ρ, ellIn st.A st.a z) ∨ ∃ b, st.best = some b ∧ ellF P w b ≤ target)

theorem cut_good {A : Matrix (Fin d) (Fin d) ℝ} {a v : Fin d → ℝ} (hd2 : 2 ≤ d) (hA : A.PosDef) (hv : v ≠ 0)
    {X : ℝ} (hX : A.det ≤ X) :
    (ccUpdate A a v).1.PosDef ∧ (ccUpdate A a v).1.det ≤ X * Real.exp (-1 / ((d : ℝ) + 1)) := by
  obtain ⟨h1, -, -, h4⟩ := lemmaCC d A a v hd2 hA hv
  exact ⟨h1, h4.trans (mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le)⟩

theorem ellRecord_best {P : Matrix (Fin d) (Fin d) ℝ} {w : Fin d → ℝ} {Q : Set (Fin d → ℝ)}
    (b : Option (Fin d → ℝ)) (a : Fin d → ℝ) (hb : ∀ x, b = some x → x ∈ Q) (ha : a ∈ Q) :
    ∃ x, ellRecord P w b a = some x ∧ x ∈ Q ∧ ellF P w x ≤ ellF P w a ∧
      ∀ y, b = some y → ellF P w x ≤ ellF P w y := by
  unfold ellRecord
  rcases b with _ | y
  · exact ⟨a, rfl, ha, le_rfl, fun y hy => by cases hy⟩
  · dsimp only
    split_ifs with hlt
    · exact ⟨a, rfl, ha, le_rfl, fun y' hy' => by cases hy'; exact hlt.le⟩
    · exact ⟨y, rfl, hb y rfl, not_lt.mp hlt, fun y' hy' => by cases hy'; exact le_rfl⟩

theorem ellStep_good {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {r R εQ : ℝ} {P : Matrix (Fin d) (Fin d) ℝ}
    {w c : Fin d → ℝ} {target X : ℝ} {k : EllConsts} (hd2 : 2 ≤ d)
    (hQ : Convex ℝ Q) (hcl : IsClosed Q) (hr : 0 < r) (hball : oBall a0 r ⊆ Q) (hQR : Q ⊆ oBall 0 R)
    (hP : P.PosDef) (hτ : 0 < k.τ) (hτr : k.τ ≤ 1 / r) (hℓ1 : 0 < k.ℓ1) (hεQ : 0 < εQ) (hεR : εQ ≤ R / 2)
    (hℓ1r : 2 * k.ℓ1 / r = εQ / (12 * R)) (hℓ1R : k.ℓ1 ≤ R / 48) (hℓ1ε : 2 * k.ℓ1 ≤ εQ / 12)
    (hτd : k.τ * (Real.sqrt d * (3 * R)) ≤ εQ / (12 * R))
    (hJ : k.J = ⌈Real.logb 2 (8 * (1 / r) / k.τ)⌉₊)
    (hB : ⌈Real.logb 2 (3 * R / (r * (k.τ * k.ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (k.J + 1))))))⌉₊ ≤ k.B)
    (hBQ : ∀ z ∈ oBall c εQ, oBall z εQ ⊆ Q) (hF : ∀ z ∈ oBall c εQ, ellF P w z ≤ target)
    (htarget : 0 ≤ target) (st : EllSt d) (hst : EllGood Q P w c εQ target X st) :
    (∃ μ, ellStep Q a0 r R P w k st = some (.inr μ) ∧ μ ∈ Q ∧ ellF P w μ ≤ target) ∨
      ∃ st', ellStep Q a0 r R P w k st = some (.inl st') ∧
        EllGood Q P w c εQ target (X * Real.exp (-1 / ((d : ℝ) + 1))) st' := by
  have hR : 0 < R := by linarith
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hA, hX, hbest, hgood⟩ := hst
  have hcQ : ∀ z ∈ oBall c εQ, z ∈ Q := fun z hz => hBQ z hz (by simp [oBall, oNorm_zero, hεQ.le])
  unfold ellStep
  by_cases h1 : R < oNorm st.a
  · -- step 1: cut by `a`
    rw [ite_eq_left h1]
    right
    have hv : st.a ≠ 0 := fun h0 => by rw [h0, oNorm_zero] at h1; linarith
    obtain ⟨hA', hdet'⟩ := cut_good (a := st.a) hd2 hA hv hX
    refine ⟨_, rfl, hA', hdet', hbest, ?_⟩
    rcases hgood with hin | hb
    · left
      intro z hz
      apply (lemmaCC d st.A st.a st.a hd2 hA hv).2.1 z (hin z hz)
      have hzR : oNorm z ≤ R := by simpa [oBall] using hQR (hcQ z hz)
      rw [dotProduct_sub, ← oNorm_sq]
      have := dot_le st.a z
      nlinarith [oNorm_nonneg st.a]
    · exact Or.inr hb
  rw [ite_eq_right h1]
  have haR : oNorm st.a ≤ R := not_lt.mp h1
  by_cases h2 : st.a ∉ Q
  · -- step 2: cut by the vector of SEP
    rw [ite_eq_left h2]
    right
    obtain ⟨y, g, hsep, hg, hcut⟩ := step2_cut hd1 hQ hcl hr hball hQR hτ hτr hℓ1 hεQ hεR hℓ1r hℓ1R hℓ1ε hτd
      hJ hB st.a haR h2
    rw [hsep]
    simp only [hg, ite_false]
    obtain ⟨hA', hdet'⟩ := cut_good (a := st.a) hd2 hA hg hX
    refine ⟨_, rfl, hA', hdet', hbest, ?_⟩
    rcases hgood with hin | hb
    · left
      intro z hz
      exact (lemmaCC d st.A st.a g hd2 hA hg).2.1 z (hin z hz) (hcut z (hBQ z hz)).le
    · exact Or.inr hb
  rw [ite_eq_right h2]
  have haQ : st.a ∈ Q := not_not.mp h2
  obtain ⟨x, hx, hxQ, hxa, hxb⟩ := ellRecord_best (P := P) (w := w) st.best st.a hbest haQ
  by_cases h3 : P *ᵥ (st.a - w) = 0
  · left
    refine ⟨st.a, ?_, haQ, by rw [ellF_eq_zero h3]; exact htarget⟩
    simp only [h3, ite_true]
  · right
    simp only [h3, ite_false]
    obtain ⟨hA', hdet'⟩ := cut_good (a := st.a) hd2 hA h3 hX
    refine ⟨_, rfl, hA', hdet', fun b hb => by rw [hx] at hb; cases hb; exact hxQ, ?_⟩
    simp only
    rcases hgood with hin | ⟨b, hb, hbt⟩
    · by_cases hall : ∀ z ∈ oBall c εQ, (P *ᵥ (st.a - w)) ⬝ᵥ (z - st.a) ≤ 0
      · left
        intro z hz
        exact (lemmaCC d st.A st.a _ hd2 hA h3).2.1 z (hin z hz) (hall z hz)
      · right
        push Not at hall
        obtain ⟨z, hz, hpos⟩ := hall
        have := ellF_ge hP.posSemidef w st.a z
        exact ⟨x, hx, by linarith [hF z hz]⟩
    · right
      exact ⟨x, hx, (hxb b hb).trans hbt⟩

theorem ellLoop_good {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {r R εQ : ℝ} {P : Matrix (Fin d) (Fin d) ℝ}
    {w c : Fin d → ℝ} {target : ℝ} {k : EllConsts} (hd2 : 2 ≤ d)
    (hQ : Convex ℝ Q) (hcl : IsClosed Q) (hr : 0 < r) (hball : oBall a0 r ⊆ Q) (hQR : Q ⊆ oBall 0 R)
    (hP : P.PosDef) (hτ : 0 < k.τ) (hτr : k.τ ≤ 1 / r) (hℓ1 : 0 < k.ℓ1) (hεQ : 0 < εQ) (hεR : εQ ≤ R / 2)
    (hℓ1r : 2 * k.ℓ1 / r = εQ / (12 * R)) (hℓ1R : k.ℓ1 ≤ R / 48) (hℓ1ε : 2 * k.ℓ1 ≤ εQ / 12)
    (hτd : k.τ * (Real.sqrt d * (3 * R)) ≤ εQ / (12 * R))
    (hJ : k.J = ⌈Real.logb 2 (8 * (1 / r) / k.τ)⌉₊)
    (hB : ⌈Real.logb 2 (3 * R / (r * (k.τ * k.ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (k.J + 1))))))⌉₊ ≤ k.B)
    (hBQ : ∀ z ∈ oBall c εQ, oBall z εQ ⊆ Q) (hF : ∀ z ∈ oBall c εQ, ellF P w z ≤ target)
    (htarget : 0 ≤ target) (j : ℕ) :
    (∃ μ, ellLoop Q a0 r R P w k j = some (.inr μ) ∧ μ ∈ Q ∧ ellF P w μ ≤ target) ∨
      ∃ st, ellLoop Q a0 r R P w k j = some (.inl st) ∧
        EllGood Q P w c εQ target (R ^ (2 * d) * Real.exp (-(j : ℝ) / ((d : ℝ) + 1))) st := by
  have hR : 0 < R := by linarith
  have hcQ : ∀ z ∈ oBall c εQ, z ∈ Q := fun z hz => hBQ z hz (by simp [oBall, oNorm_zero, hεQ.le])
  induction j with
  | zero =>
    right
    refine ⟨_, rfl, ?_⟩
    refine ⟨Matrix.PosDef.one.smul (by positivity), ?_, ?_, Or.inl ?_⟩
    rotate_left
    · intro b hb; cases hb
    rotate_right
    · simp only [CharP.cast_eq_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul]
    · intro z hz
      have hzR : oNorm z ≤ R := by simpa [oBall] using hQR (hcQ z hz)
      have hinv : ((R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = (R ^ 2)⁻¹ • 1 := by
        apply Matrix.inv_eq_left_inv
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ (by positivity),
          one_smul]
      unfold ellIn
      simp only [sub_zero, hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [← oNorm_sq, inv_mul_le_iff₀ (by positivity), mul_one]
      exact pow_le_pow_left₀ (oNorm_nonneg z) hzR 2
  | succ j ih =>
    simp only [ellLoop]
    rcases ih with ⟨μ, h, hμ⟩ | ⟨st, h, hst⟩
    · left; rw [h]; exact ⟨μ, rfl, hμ⟩
    · rw [h]
      rcases ellStep_good hd2 hQ hcl hr hball hQR hP hτ hτr hℓ1 hεQ hεR hℓ1r hℓ1R hℓ1ε hτd hJ hB hBQ hF htarget st
        hst with hret | ⟨st', hst', hgood⟩
      · exact Or.inl hret
      · right
        refine ⟨st', hst', ?_⟩
        have : R ^ (2 * d) * Real.exp (-(j : ℝ) / ((d : ℝ) + 1)) * Real.exp (-1 / ((d : ℝ) + 1)) =
            R ^ (2 * d) * Real.exp (-((j + 1 : ℕ) : ℝ) / ((d : ℝ) + 1)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
        rwa [this] at hgood

theorem ell_N_bound {d : ℕ} {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ)
    (hN : 2 * (d : ℝ) * (d + 1) * Real.log (R / ρ) < N) :
    R ^ (2 * d) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) < ρ ^ (2 * d) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h1 : Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) < Real.exp (-(((2 * d : ℕ) : ℝ) * Real.log (R / ρ))) := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_lt_neg_iff, lt_div_iff₀ hd1]
    push_cast; linarith
  have h2 : Real.exp (((2 * d : ℕ) : ℝ) * Real.log (R / ρ)) = (R / ρ) ^ (2 * d) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [Real.exp_neg, h2] at h1
  calc R ^ (2 * d) * Real.exp (-(N : ℝ) / ((d : ℝ) + 1)) < R ^ (2 * d) * ((R / ρ) ^ (2 * d))⁻¹ :=
        mul_lt_mul_of_pos_left h1 (by positivity)
    _ = ρ ^ (2 * d) := by rw [div_pow]; field_simp

/-- Proposition ELL. -/
theorem propELL : PropELL := by
  intro d Q a0 r R P w e hd2 hQ hcl hr hball hQR hP he
  have hd1 : 1 ≤ d := by omega
  have ha0 : a0 ∈ Q := hball (by simp [oBall, oNorm_zero, hr.le])
  have hrR : oNorm a0 + r ≤ R := ball_in_ball hd1 hr (hball.trans hQR)
  have hR : 0 < R := by linarith [oNorm_nonneg a0]
  have hrR' : r ≤ R := by linarith [oNorm_nonneg a0]
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact_mod_cast hd1
  -- the constants of ELL-cap
  set LF := P.trace * (R + oNorm w) with hLFdef
  have hLF : 0 < LF := mul_pos (trace_pos_of_posDef hP hd1) (by linarith [oNorm_nonneg w])
  set θ := min 1 (e / (3 * LF * R)) with hθdef
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθe : θ ≤ e / (3 * LF * R) := min_le_right _ _
  set εQ := θ * r / 2 with hεQdef
  set k := ellConsts r R P w e with hkdef
  have hkτ : k.τ = εQ / (36 * R ^ 2 * Real.sqrt d) := rfl
  have hkℓ : k.ℓ1 = r * εQ / (24 * R) := rfl
  have hkN : k.N = ⌈2 * (d : ℝ) * (d + 1) * Real.log (2 * R / (θ * r))⌉₊ + 1 := rfl
  have hkJ : k.J = ⌈Real.logb 2 (8 / (r * k.τ))⌉₊ := rfl
  have hkB : k.B = ⌈Real.logb 2 (3 * R / (r * (k.τ * k.ℓ1 / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * (k.J + 1))))))⌉₊ :=
    rfl
  have hεQ : 0 < εQ := by positivity
  have hεR : εQ ≤ R / 2 := by rw [hεQdef]; nlinarith
  have hτ : 0 < k.τ := by rw [hkτ]; positivity
  have hτr : k.τ ≤ 1 / r := by
    rw [hkτ, div_le_div_iff₀ (by positivity) hr]
    nlinarith [mul_le_mul hεR hrR' hr.le (by positivity), sq_nonneg R]
  have hℓ1 : 0 < k.ℓ1 := by rw [hkℓ]; positivity
  have hℓ1r : 2 * k.ℓ1 / r = εQ / (12 * R) := by rw [hkℓ]; field_simp; ring
  have hℓ1R : k.ℓ1 ≤ R / 48 := by
    rw [hkℓ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_le_mul hrR' hεR hεQ.le hR.le]
  have hℓ1ε : 2 * k.ℓ1 ≤ εQ / 12 := by
    rw [hkℓ, show 2 * (r * εQ / (24 * R)) = (r / R) * (εQ / 12) by field_simp; ring]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hR).mpr hrR')
  have hτd : k.τ * (Real.sqrt d * (3 * R)) ≤ εQ / (12 * R) := by
    rw [hkτ]; apply le_of_eq; field_simp; ring
  have hJ : k.J = ⌈Real.logb 2 (8 * (1 / r) / k.τ)⌉₊ := by rw [hkJ, mul_one_div, div_div]
  have hB := le_of_eq hkB.symm
  -- existence and the value, for every comparison point `x ∈ Q`
  have key : ∀ x ∈ Q, ∃ μ, ellCap Q a0 r R P w e = some μ ∧ μ ∈ Q ∧ ellF P w μ ≤ ellF P w x + e := by
    intro x hx
    have hxR : oNorm x ≤ R := by simpa [oBall] using hQR hx
    set c := (1 - θ) • x + θ • a0 with hc
    have hbig : oBall c (θ * r) ⊆ Q := by
      intro v hv
      have hv' : a0 + θ⁻¹ • (v - c) ∈ Q := by
        apply hball
        simp only [oBall, Set.mem_ofPred_eq, add_sub_cancel_left, oNorm_smul, abs_inv, abs_of_pos hθ0]
        rw [inv_mul_le_iff₀ hθ0]; exact hv
      have hcomb := hQ hx hv' (by linarith : 0 ≤ 1 - θ) hθ0.le (by ring)
      convert hcomb using 1
      rw [smul_add, smul_smul, mul_inv_cancel₀ hθ0.ne', one_smul, hc]
      abel
    have hBQ : ∀ z ∈ oBall c εQ, oBall z εQ ⊆ Q := by
      intro z hz u hu
      apply hbig
      simp only [oBall, Set.mem_ofPred_eq] at hz hu ⊢
      have := oNorm_sub_sub_le u z c
      linarith
    have hF : ∀ z ∈ oBall c εQ, ellF P w z ≤ ellF P w x + e := by
      intro z hz
      have hzQ : z ∈ Q := hBQ z hz (by simp [oBall, oNorm_zero, hεQ.le])
      have hzR : oNorm z ≤ R := by simpa [oBall] using hQR hzQ
      have h1 := ellF_sub_le P hP.posSemidef w z x R hzR hxR
      have h2 : oNorm (z - x) ≤ θ * (r / 2 + 2 * R) := by
        have a1 := oNorm_sub_sub_le z c x
        have a2 : oNorm (c - x) = θ * oNorm (a0 - x) := by
          rw [hc, show (1 - θ) • x + θ • a0 - x = θ • (a0 - x) by
            rw [smul_sub, sub_smul, one_smul]; abel, oNorm_smul, abs_of_pos hθ0]
        have a3 : oNorm (a0 - x) ≤ 2 * R := by have := oNorm_sub_le a0 x; linarith [oNorm_nonneg a0]
        simp only [oBall, Set.mem_ofPred_eq] at hz
        nlinarith
      have h3 : LF * (θ * (r / 2 + 2 * R)) ≤ e := by
        have : θ * (r / 2 + 2 * R) ≤ e / (3 * LF * R) * (5 / 2 * R) :=
          mul_le_mul hθe (by linarith) (by positivity) (by positivity)
        calc LF * (θ * (r / 2 + 2 * R)) ≤ LF * (e / (3 * LF * R) * (5 / 2 * R)) := by gcongr
          _ = 5 / 6 * e := by field_simp; ring
          _ ≤ e := by linarith
      have : LF * oNorm (z - x) ≤ LF * (θ * (r / 2 + 2 * R)) := by gcongr
      linarith
    have htarget : 0 ≤ ellF P w x + e := by linarith [ellF_nonneg hP.posSemidef w x]
    have hcap : ellCap Q a0 r R P w e = (match ellLoop Q a0 r R P w k k.N with
        | some (.inr μ) => some μ
        | some (.inl st) => st.best
        | none => none) := by
      unfold ellCap; rw [ite_eq_right (not_lt.mpr hrR')]; rfl
    rcases ellLoop_good hd2 hQ hcl hr hball hQR hP hτ hτr hℓ1 hεQ hεR hℓ1r hℓ1R hℓ1ε hτd hJ hB hBQ hF htarget k.N
      with ⟨μ, h, hμ⟩ | ⟨st, h, hA, hdet, hbest, hgood⟩
    · exact ⟨μ, by rw [hcap, h], hμ⟩
    · rcases hgood with hin | ⟨b, hb, hbt⟩
      · exfalso
        have hdetb := lemmaBALL d st.A st.a c εQ hA hεQ.le hin
        have hN : 2 * (d : ℝ) * (d + 1) * Real.log (R / εQ) < k.N := by
          rw [hkN, show R / εQ = 2 * R / (θ * r) by rw [hεQdef]; field_simp]
          push_cast
          linarith [Nat.le_ceil (2 * (d : ℝ) * (d + 1) * Real.log (2 * R / (θ * r)))]
        have := ell_N_bound hR hεQ k.N hN
        linarith
      · exact ⟨b, by rw [hcap, h]; exact hb, hbest b hb, hbt⟩
  obtain ⟨μ, hμ, hμQ, -⟩ := key a0 ha0
  refine ⟨μ, hμ, hμQ, fun x hx => ?_⟩
  obtain ⟨μ', hμ', -, hle⟩ := key x hx
  rw [hμ] at hμ'
  cases hμ'
  exact hle


/-! ## Proposition ELL-1 -/

/-- The invariant of `oBisectLo`: both components lie in `Set.uIcc lo hi`, and if `Pr lo` then the first
component satisfies `Pr`. -/
lemma oBisectLo_invariant (Pr : ℝ → Prop) (lo hi : ℝ) (j : ℕ) (hPr : Pr lo) :
    (oBisectLo Pr lo hi j).1 ∈ Set.uIcc lo hi ∧ (oBisectLo Pr lo hi j).2 ∈ Set.uIcc lo hi ∧
    Pr (oBisectLo Pr lo hi j).1 := by
  induction' j with j ih
  · -- base case j = 0
    exact ⟨Set.left_mem_uIcc, Set.right_mem_uIcc, hPr⟩
  · -- inductive step
    rcases ih with ⟨hfst, hsnd, hPr_fst⟩
    dsimp [oBisectLo]
    split
    · -- Pr mid holds, new pair is (mid, I.2)
      rename_i hmid
      have hmid_mem : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 ∈ Set.uIcc lo hi := by
        rcases hfst with ⟨hfst_l, hfst_u⟩
        rcases hsnd with ⟨hsnd_l, hsnd_u⟩
        have hlow : lo ⊓ hi ≤ ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 := by
          nlinarith
        have hhigh : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 ≤ lo ⊔ hi := by
          nlinarith
        exact ⟨hlow, hhigh⟩
      exact ⟨hmid_mem, hsnd, hmid⟩
    · -- Pr mid does not hold, new pair is (I.1, mid)
      rename_i hmid
      have hmid_mem : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 ∈ Set.uIcc lo hi := by
        rcases hfst with ⟨hfst_l, hfst_u⟩
        rcases hsnd with ⟨hsnd_l, hsnd_u⟩
        have hlow : lo ⊓ hi ≤ ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 := by
          nlinarith
        have hhigh : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 ≤ lo ⊔ hi := by
          nlinarith
        exact ⟨hlow, hhigh⟩
      exact ⟨hfst, hmid_mem, hPr_fst⟩

theorem ell1_total (Q : Set ℝ) (a0 r R p w e : ℝ) :
    ellOne Q a0 r R p w e = none ∨ ∃ μ, ellOne Q a0 r R p w e = some μ ∧ μ ∈ Q ∧ |μ| ≤ R := by
  unfold ellOne
  by_cases h1 : R < r ∨ R < |a0|
  · simp [h1]
  · by_cases h2 : a0 ∉ Q
    · simp [h1, h2]
    · have ha0Q : a0 ∈ Q := not_not.mp h2
      have hRa0 : |a0| ≤ R := by
        rcases em (R < r) with (hr | hr)
        · exfalso; exact h1 (Or.inl hr)
        · rcases em (R < |a0|) with (ha | ha)
          · exfalso; exact h1 (Or.inr ha)
          · exact le_of_not_gt ha
      have hR_nonneg : 0 ≤ R := by
        have := abs_nonneg a0; linarith
      let w' := max (-R) (min R w)
      have hw'_lower : -R ≤ w' := le_max_left _ _
      have hw'_upper : w' ≤ R := by
        apply max_le
        · linarith
        · exact min_le_left _ _
      have hw'_mem_Icc : w' ∈ Set.Icc (-R) R := ⟨hw'_lower, hw'_upper⟩
      have ha0_mem_Icc : a0 ∈ Set.Icc (-R) R := by
        rcases abs_le.mp hRa0 with ⟨h1', h2'⟩
        exact ⟨h1', h2'⟩
      by_cases hw'Q : w' ∈ Q
      · right
        simp [h1, h2, w', hw'Q]
        rw [abs_le]
        exact ⟨by linarith, hw'_upper⟩
      · right
        let n := ⌈Real.logb 2 (|w' - a0| / (e / (p * (R + |w|))))⌉₊
        have h_invariant := oBisectLo_invariant (· ∈ Q) a0 w' n ha0Q
        rcases h_invariant with ⟨hfst_mem, hsnd_mem, hfst_Q⟩
        have h_subset : Set.uIcc a0 w' ⊆ Set.Icc (-R) R :=
          Set.uIcc_subset_Icc ha0_mem_Icc hw'_mem_Icc
        have h_mem_Icc : (oBisectLo (· ∈ Q) a0 w' n).1 ∈ Set.Icc (-R) R :=
          h_subset hfst_mem
        rcases h_mem_Icc with ⟨hlow, hhigh⟩
        simp [h1, h2, w', hw'Q]
        -- goal is now: (oBisectLo (· ∈ Q) a0 w' ...).1 ∈ Q ∧ |(oBisectLo ...).1| ≤ R
        -- note: w' is definitionally max (-R) (min R w)
        exact And.intro hfst_Q (by
          rw [abs_le]
          exact ⟨hlow, hhigh⟩)

theorem oBisectLo_inv (Pr : ℝ → Prop) (lo hi : ℝ) (hPr_lo : Pr lo) (hPr_not_hi : ¬ Pr hi) (h_le : lo ≤ hi) (j : ℕ) :
    Pr (oBisectLo Pr lo hi j).1 ∧ ¬ Pr (oBisectLo Pr lo hi j).2 ∧ lo ≤ (oBisectLo Pr lo hi j).1 ∧ (oBisectLo Pr lo hi j).1 < (oBisectLo Pr lo hi j).2 ∧ (oBisectLo Pr lo hi j).2 ≤ hi ∧ (oBisectLo Pr lo hi j).2 - (oBisectLo Pr lo hi j).1 = (hi - lo) / ((2 : ℝ) ^ (j : ℝ)) := by
  induction' j with j ih
  · -- j = 0
    have h_lt : lo < hi := by
      by_contra! h_eq
      have h_eq' : lo = hi := by linarith
      subst h_eq'
      exact hPr_not_hi hPr_lo
    simp [oBisectLo]
    exact ⟨hPr_lo, hPr_not_hi, h_lt⟩
  · -- j+1
    rcases ih with ⟨hPr_I1, hPr_not_I2, h_le_I1, h_I1_lt_I2, h_I2_le_hi, h_diff⟩
    have h_pow : ((2 : ℝ) ^ (j : ℝ)) * (2 : ℝ) = (2 : ℝ) ^ ((j : ℝ) + 1) := by
      calc
        ((2 : ℝ) ^ (j : ℝ)) * (2 : ℝ) = ((2 : ℝ) ^ (j : ℝ)) * ((2 : ℝ) ^ (1 : ℝ)) := by simp
        _ = (2 : ℝ) ^ ((j : ℝ) + (1 : ℝ)) := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (j : ℝ) (1 : ℝ)]
        _ = (2 : ℝ) ^ ((j : ℝ) + 1) := by ring
    by_cases h_mid : Pr (((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2)
    · -- I' = ((I.1+I.2)/2, I.2)
      simp [oBisectLo, h_mid]
      have h_lower : lo ≤ ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 := by linarith
      have h_upper : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 < (oBisectLo Pr lo hi j).2 := by linarith
      have h_diff' : (oBisectLo Pr lo hi j).2 - ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 = (hi - lo) / ((2 : ℝ) ^ ((j : ℝ) + 1)) := by
        have h_left : (oBisectLo Pr lo hi j).2 - ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 =
          ((oBisectLo Pr lo hi j).2 - (oBisectLo Pr lo hi j).1) / 2 := by ring
        rw [h_left, h_diff]
        -- Now: ((hi - lo) / 2^j) / 2 = (hi - lo) / 2^(j+1)
        calc
          ((hi - lo) / ((2 : ℝ) ^ (j : ℝ))) / 2 = (hi - lo) / (((2 : ℝ) ^ (j : ℝ)) * 2) := by ring
          _ = (hi - lo) / ((2 : ℝ) ^ ((j : ℝ) + 1)) := by rw [h_pow]
      -- Now we need to provide the 6-tuple
      -- The goal is: ¬Pr (...) ∧ lo ≤ ... ∧ ... < ... ∧ ... ≤ hi ∧ ... - ... = ...
      -- Wait, simp simplified the first component (Pr) already
      -- Let me check what the goal actually is
      -- After simp [oBisectLo, h_mid], the goal should be:
      -- ¬Pr ((I.1+I.2)/2) ∧ lo ≤ ((I.1+I.2)/2) ∧ ((I.1+I.2)/2) < I.2 ∧ I.2 ≤ hi ∧ I.2 - ((I.1+I.2)/2) = (hi - lo) / 2^(j+1)
      -- But we also need Pr of the first component? No, simp already simplified it
      -- Let me just provide the components in order
      exact ⟨hPr_not_I2, h_lower, h_upper, h_I2_le_hi, h_diff'⟩
    · -- I' = (I.1, (I.1+I.2)/2)
      simp [oBisectLo, h_mid]
      have h_lower : lo ≤ (oBisectLo Pr lo hi j).1 := h_le_I1
      have h_upper : (oBisectLo Pr lo hi j).1 < ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 := by linarith
      have h_upper2 : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 ≤ hi := by linarith
      have h_diff' : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 - (oBisectLo Pr lo hi j).1 = (hi - lo) / ((2 : ℝ) ^ ((j : ℝ) + 1)) := by
        have h_left : ((oBisectLo Pr lo hi j).1 + (oBisectLo Pr lo hi j).2) / 2 - (oBisectLo Pr lo hi j).1 =
          ((oBisectLo Pr lo hi j).2 - (oBisectLo Pr lo hi j).1) / 2 := by ring
        rw [h_left, h_diff]
        calc
          ((hi - lo) / ((2 : ℝ) ^ (j : ℝ))) / 2 = (hi - lo) / (((2 : ℝ) ^ (j : ℝ)) * 2) := by ring
          _ = (hi - lo) / ((2 : ℝ) ^ ((j : ℝ) + 1)) := by rw [h_pow]
      exact ⟨hPr_I1, h_lower, h_upper, h_upper2, h_diff'⟩

/-- Proposition ELL-1 (b) when the clamped target lies on the right of `a₀`. -/
theorem ell1_acc_up (Q : Set ℝ) (a0 r R p w e : ℝ) (hQ : Q.OrdConnected)
    (hball : Set.Icc (a0 - r) (a0 + r) ⊆ Q) (hQR : Q ⊆ Set.Icc (-R) R) (hr : 0 < r) (hp : 0 < p) (he : 0 < e)
    (hup : a0 ≤ max (-R) (min R w)) :
    ∃ μ, ellOne Q a0 r R p w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, p * (μ - w) ^ 2 / 2 ≤ p * (x - w) ^ 2 / 2 + e := by
  have ha0_mem : a0 ∈ Q := by
    have ha0_in_ball : a0 ∈ Set.Icc (a0 - r) (a0 + r) := ⟨by linarith, by linarith⟩
    exact hball ha0_in_ball
  have hR_ge_r : r ≤ R := by
    have ha0r_mem : a0 + r ∈ Q := by
      have hmem : a0 + r ∈ Set.Icc (a0 - r) (a0 + r) := ⟨by linarith, by linarith⟩
      exact hball hmem
    have ha0l_mem : a0 - r ∈ Q := by
      have hmem : a0 - r ∈ Set.Icc (a0 - r) (a0 + r) := ⟨by linarith, by linarith⟩
      exact hball hmem
    have hmem_r : a0 + r ∈ Set.Icc (-R) R := hQR ha0r_mem
    have hmem_l : a0 - r ∈ Set.Icc (-R) R := hQR ha0l_mem
    rcases hmem_r with ⟨hl_r, hr_r⟩
    rcases hmem_l with ⟨hl_l, hr_l⟩
    linarith
  have hR_pos : 0 < R := by linarith
  have ha0_abs_le_R : |a0| ≤ R := by
    have ha0_mem' : a0 ∈ Set.Icc (-R) R := hQR ha0_mem
    rcases ha0_mem' with ⟨hl, hr'⟩
    rw [abs_le]
    constructor <;> linarith
  have h_cond1 : ¬ (R < r ∨ R < |a0|) := by
    rw [not_or]
    constructor <;> linarith
  have h_cond2 : a0 ∈ Q := ha0_mem
  classical
    unfold ellOne
    simp [h_cond1, h_cond2]
    let w' := max (-R) (min R w)
    by_cases hw'_mem : w' ∈ Q
    · -- Case w' ∈ Q: ellOne returns some w'
      refine ⟨w', ?_, hw'_mem, ?_⟩
      · simp [w', hw'_mem]
      · intro x hx
        have hx_in : x ∈ Set.Icc (-R) R := hQR hx
        rcases hx_in with ⟨hx_l, hx_r⟩
        have h_abs_le : |w' - w| ≤ |x - w| := by
          have hw'_def' : w' = max (-R) (min R w) := rfl
          rw [hw'_def']
          by_cases hw_le_negR : w ≤ -R
          · have hw_le_R : w ≤ R := by linarith
            have h_min : min R w = w := min_eq_right hw_le_R
            have h_max : max (-R) w = -R := max_eq_left hw_le_negR
            rw [h_min, h_max]
            have h_nonneg1 : 0 ≤ -R - w := by linarith
            have h_nonneg2 : 0 ≤ x - w := by linarith
            rw [abs_of_nonneg h_nonneg1, abs_of_nonneg h_nonneg2]
            linarith
          · by_cases hR_le_hw : R ≤ w
            · have h_min : min R w = R := min_eq_left hR_le_hw
              have h_max : max (-R) R = R := max_eq_right (by linarith [hR_pos])
              rw [h_min, h_max]
              have h_nonpos1 : R - w ≤ 0 := by linarith
              have h_nonpos2 : x - w ≤ 0 := by linarith
              rw [abs_of_nonpos h_nonpos1, abs_of_nonpos h_nonpos2]
              linarith
            · have h_min : min R w = w := min_eq_right (by linarith)
              have h_max : max (-R) w = w := max_eq_right (by linarith)
              rw [h_min, h_max]
              simp [abs_nonneg]
        have h_sq_le : (w' - w)^2 ≤ (x - w)^2 := sq_le_sq.mpr h_abs_le
        nlinarith
    · -- Case w' ∉ Q: ellOne does bisection
      have hw'_not_mem : w' ∉ Q := hw'_mem
      set ξ := e / (p * (R + |w|)) with hξ_def
      have hξ_pos : 0 < ξ := by
        rw [hξ_def]
        refine div_pos he ?_
        have h_sum_pos : 0 < R + |w| := by linarith [abs_nonneg w, hR_pos]
        exact mul_pos hp h_sum_pos
      set m := ⌈Real.logb 2 (|w' - a0| / ξ)⌉₊ with hm_def
      set μ := (oBisectLo (· ∈ Q) a0 w' m).1 with hμ_def
      by_cases h_a0_le_w' : a0 ≤ w'
      · -- Case a0 ≤ w'
        have h_diff_nonneg : 0 ≤ w' - a0 := by linarith
        have h_abs_eq : |w' - a0| = w' - a0 := abs_of_nonneg h_diff_nonneg
        have h_pos_diff : 0 < w' - a0 := by
          by_contra! h_nonpos
          have h_eq : w' = a0 := by linarith
          rw [h_eq] at hw'_not_mem
          exact hw'_not_mem ha0_mem
        have h_key_ineq : (w' - a0) / ((2 : ℝ) ^ (m : ℝ)) ≤ ξ := by
          have h_pos_pow : 0 < (2 : ℝ) ^ (m : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
          have hm_le : Real.logb 2 ((w' - a0) / ξ) ≤ (m : ℝ) := by
            rw [hm_def, h_abs_eq]
            exact Nat.le_ceil _
          have h_logb_eq : Real.logb 2 ((w' - a0) / ξ) = Real.log ((w' - a0) / ξ) / Real.log 2 := rfl
          rw [h_logb_eq] at hm_le
          have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          have h_mul : Real.log ((w' - a0) / ξ) ≤ (m : ℝ) * Real.log 2 :=
            (div_le_iff₀ h_log2_pos).mp hm_le
          have h_log_rpow : Real.log ((2 : ℝ) ^ (m : ℝ)) = (m : ℝ) * Real.log 2 := by
            rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
          have h_log_le : Real.log ((w' - a0) / ξ) ≤ Real.log ((2 : ℝ) ^ (m : ℝ)) := by
            rw [h_log_rpow]
            exact h_mul
          have h_pos_ratio : 0 < (w' - a0) / ξ := div_pos h_pos_diff hξ_pos
          have h_le := (Real.log_le_log_iff h_pos_ratio h_pos_pow).mp h_log_le
          have h_mul' : w' - a0 ≤ ((2 : ℝ) ^ (m : ℝ)) * ξ :=
            (div_le_iff₀ hξ_pos).mp h_le
          apply (div_le_iff₀ h_pos_pow).mpr
          rw [mul_comm]
          exact h_mul'
        have h_inv := oBisectLo_inv (· ∈ Q) a0 w' ha0_mem hw'_not_mem h_a0_le_w' m
        rcases h_inv with ⟨hμ_mem, h_not_mem, h_le1, h_lt, h_le2, h_diff⟩
        have h_diff_le_ξ : (oBisectLo (· ∈ Q) a0 w' m).2 - μ ≤ ξ := by
          rw [hμ_def, h_diff]
          exact h_key_ineq
        refine ⟨μ, ?_, hμ_mem, ?_⟩
        · rw [hμ_def]
          simp [w', hw'_mem]
        · intro x hx
          have hx_in : x ∈ Set.Icc (-R) R := hQR hx
          rcases hx_in with ⟨hx_l, hx_r⟩
          set I := (oBisectLo (· ∈ Q) a0 w' m).2 with hI_def
          have hI_not_mem : I ∉ Q := h_not_mem
          have hI_le_w' : I ≤ w' := h_le2
          have hx_lt_I : x < I := by
            by_contra! h_ge
            have h_interval : Set.Icc μ x ⊆ Q := hQ.out' hμ_mem hx
            have hI_mem : I ∈ Set.Icc μ x := by
              rw [hI_def]
              constructor
              · exact le_of_lt h_lt
              · exact h_ge
            exact hI_not_mem (h_interval hI_mem)
          by_cases hx_le_μ : x ≤ μ
          · -- x ≤ μ, need to show F(μ) ≤ F(x)
            have hw'_le_w : w' ≤ w := by
              by_contra! h_lt'
              -- w < w'
              have h_cases : w ≤ -R ∨ R ≤ w := by
                -- If neither, then -R < w < R, and w' = w, contradicting w < w'
                by_cases h : w ≤ -R
                · exact Or.inl h
                · by_cases h' : R ≤ w
                  · exact Or.inr h'
                  · -- -R < w < R
                    have hw'_eq_w : w' = w := by
                      dsimp [w']
                      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
                    linarith
              rcases h_cases with (hw_le_negR | hR_le_w)
              · -- w ≤ -R, so w' = -R
                have hw'_eq_negR : w' = -R := by
                  dsimp [w']
                  rw [min_eq_right (by linarith), max_eq_left hw_le_negR]
                -- Then a0 ≤ w' = -R and a0 ≥ -R, so a0 = -R = w'
                have ha0_le_negR : a0 ≤ -R := by linarith
                have ha0_ge_negR : -R ≤ a0 := (hQR ha0_mem).1
                have h_eq : a0 = -R := by linarith
                have hw'_eq_negR' : w' = -R := by
                  dsimp [w']
                  rw [min_eq_right (by linarith), max_eq_left hw_le_negR]
                have h_contra : a0 = w' := by linarith
                rw [h_contra] at ha0_mem
                exact hw'_not_mem ha0_mem
              · -- R ≤ w, so w' = R
                have hw'_eq_R : w' = R := by
                  dsimp [w']
                  rw [min_eq_left hR_le_w, max_eq_right (by linarith [hR_pos])]
                -- But w < w' = R, so w < R, contradicting R ≤ w
                linarith
            have h_F_mono : p * (μ - w) ^ 2 / 2 ≤ p * (x - w) ^ 2 / 2 := by
              have h_nonpos_μ : μ - w ≤ 0 := by linarith
              have h_nonpos_x : x - w ≤ 0 := by linarith
              have h_abs_le : |μ - w| ≤ |x - w| := by
                rw [abs_of_nonpos h_nonpos_μ, abs_of_nonpos h_nonpos_x]
                linarith
              have h_sq_le : (μ - w)^2 ≤ (x - w)^2 := sq_le_sq.mpr h_abs_le
              nlinarith
            nlinarith
          · -- μ < x < I
            have h_μ_lt_x : μ < x := by linarith
            -- Need to show F(μ) - F(x) ≤ e
            -- F(μ) - F(x) = p*(μ-x)*(μ+x-2w)/2
            have h_diff_F : p * (μ - w) ^ 2 / 2 - p * (x - w) ^ 2 / 2 = p * (μ - x) * (μ + x - 2 * w) / 2 := by
              ring
            -- Bound |μ+x-2w| ≤ 2(R+|w|) since μ, x ∈ [-R, R]
            have h_bound : |μ + x - 2 * w| ≤ 2 * (R + |w|) := by
              have hμ_in : μ ∈ Set.Icc (-R) R := hQR hμ_mem
              have h_abs_sum : |μ + x| ≤ |μ| + |x| := abs_add_le _ _
              have h_abs_μ : |μ| ≤ R := abs_le.mpr ⟨hμ_in.1, hμ_in.2⟩
              have h_abs_x : |x| ≤ R := abs_le.mpr ⟨hx_l, hx_r⟩
              have h_total : |(μ + x) - (2 * w)| ≤ |μ + x| + |2 * w| := abs_sub _ _
              have h_2w : |2 * w| = 2 * |w| := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              rw [h_2w] at h_total
              have h_sum_bound : |μ + x| ≤ 2 * R := by linarith
              linarith
            -- Since μ - x < 0, we have (μ-x)*(μ+x-2w) ≤ (x-μ)*|μ+x-2w|
            have h_le_abs : p * (μ - x) * (μ + x - 2 * w) / 2 ≤ p * (x - μ) * |μ + x - 2 * w| / 2 := by
              have hxμ_nonneg : 0 ≤ x - μ := by linarith
              have hp_nonneg : 0 ≤ p := by linarith
              have h_neg_ineq : -(μ + x - 2 * w) ≤ |μ + x - 2 * w| := by
                have h := neg_abs_le (μ + x - 2 * w)
                linarith
              have h_mul : (μ - x) * (μ + x - 2 * w) ≤ (x - μ) * |μ + x - 2 * w| := by
                have : μ - x = -(x - μ) := by ring
                rw [this]
                calc
                  (-(x - μ)) * (μ + x - 2 * w) = (x - μ) * (-(μ + x - 2 * w)) := by ring
                  _ ≤ (x - μ) * |μ + x - 2 * w| := mul_le_mul_of_nonneg_left h_neg_ineq hxμ_nonneg
              have h_mul' : p * ((μ - x) * (μ + x - 2 * w)) ≤ p * ((x - μ) * |μ + x - 2 * w|) :=
                mul_le_mul_of_nonneg_left h_mul hp_nonneg
              -- Now divide by 2
              linarith
            -- Now bound using x-μ ≤ ξ and |μ+x-2w| ≤ 2(R+|w|)
            have h_xμ_le_ξ : x - μ ≤ ξ := by
              have h_lt_I : x - μ < I - μ := by linarith
              have h_Iμ_le_ξ : I - μ ≤ ξ := h_diff_le_ξ
              linarith
            have h_main : p * (x - μ) * |μ + x - 2 * w| / 2 ≤ e := by
              have hp_nonneg : 0 ≤ p := by linarith
              have hxμ_nonneg : 0 ≤ x - μ := by linarith
              have hRw_nonneg : 0 ≤ R + |w| := by
                have hR_nonneg : 0 ≤ R := by linarith
                have h_abs_w : 0 ≤ |w| := abs_nonneg _
                linarith
              have h1 : p * (x - μ) * |μ + x - 2 * w| ≤ p * (x - μ) * (2 * (R + |w|)) := by
                have h_inner : (x - μ) * |μ + x - 2 * w| ≤ (x - μ) * (2 * (R + |w|)) :=
                  mul_le_mul_of_nonneg_left h_bound hxμ_nonneg
                calc
                  p * (x - μ) * |μ + x - 2 * w| = p * ((x - μ) * |μ + x - 2 * w|) := by ring
                  _ ≤ p * ((x - μ) * (2 * (R + |w|))) := mul_le_mul_of_nonneg_left h_inner hp_nonneg
                  _ = p * (x - μ) * (2 * (R + |w|)) := by ring
              have h2 : p * (x - μ) * (2 * (R + |w|)) / 2 = p * (x - μ) * (R + |w|) := by ring
              have h3 : p * (x - μ) * (R + |w|) ≤ p * ξ * (R + |w|) := by
                have h_mul : p * (x - μ) * (R + |w|) = (p * (R + |w|)) * (x - μ) := by ring
                have h_mul' : p * ξ * (R + |w|) = (p * (R + |w|)) * ξ := by ring
                rw [h_mul, h_mul']
                apply mul_le_mul_of_nonneg_left h_xμ_le_ξ
                positivity
              have h4 : p * ξ * (R + |w|) = e := by
                rw [hξ_def]
                field_simp [show p * (R + |w|) ≠ 0 from by positivity]
              -- Combine: p*(x-μ)*|...|/2 ≤ p*(x-μ)*(2*(R+|w|))/2 = p*(x-μ)*(R+|w|) ≤ p*ξ*(R+|w|) = e
              have h1_div2 : p * (x - μ) * |μ + x - 2 * w| / 2 ≤ p * (x - μ) * (2 * (R + |w|)) / 2 := by linarith
              rw [h2] at h1_div2
              have h3' : p * (x - μ) * (R + |w|) ≤ e := by
                -- h3 : p*(x-μ)*(R+|w|) ≤ p*ξ*(R+|w|)
                -- h4 : p*ξ*(R+|w|) = e
                -- So h3.trans h4.le gives the result
                -- Actually h3 gives ≤ p*ξ*(R+|w|), and h4 says that equals e
                -- So we can rewrite h4 at h3, or use h3.trans
                -- h3 : A ≤ B, h4 : B = e, so h3.trans h4.le gives A ≤ e
                -- But h4.le is B ≤ e (from B = e)
                -- Actually h3.trans (by rw [h4]) doesn't work directly
                -- Let me use: linarith
                linarith
              linarith
            -- Combine everything
            have h_goal : p * (μ - w) ^ 2 / 2 - p * (x - w) ^ 2 / 2 ≤ e := by
              rw [h_diff_F]
              linarith
            linarith
      · exact absurd hup h_a0_le_w'

theorem clamp_neg {R w : ℝ} (hR : 0 ≤ R) : max (-R) (min R (-w)) = -max (-R) (min R w) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem oBisectLo_neg (Q : Set ℝ) (lo hi : ℝ) (j : ℕ) :
    oBisectLo (· ∈ {x : ℝ | -x ∈ Q}) (-lo) (-hi) j =
      (-(oBisectLo (· ∈ Q) lo hi j).1, -(oBisectLo (· ∈ Q) lo hi j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [oBisectLo]
    rw [ih]
    generalize oBisectLo (· ∈ Q) lo hi j = I
    obtain ⟨u, v⟩ := I
    have hmid : -((-u + -v) / 2) = (u + v) / 2 := by ring
    by_cases h : (u + v) / 2 ∈ Q
    · have h' : (-u + -v) / 2 ∈ {x : ℝ | -x ∈ Q} := by
        simp only [Set.mem_ofPred_eq, hmid]; exact h
      rw [ite_eq_left h', ite_eq_left h]
      show ((-u + -v) / 2, -v) = (-((u + v) / 2), -v)
      rw [show (-u + -v) / 2 = -((u + v) / 2) by ring]
    · have h' : (-u + -v) / 2 ∉ {x : ℝ | -x ∈ Q} := by
        simp only [Set.mem_ofPred_eq, hmid]; exact h
      rw [ite_eq_right h', ite_eq_right h]
      show (-u, (-u + -v) / 2) = (-u, -((u + v) / 2))
      rw [show (-u + -v) / 2 = -((u + v) / 2) by ring]

theorem ellOne_neg (Q : Set ℝ) (a0 r R p w e : ℝ) :
    ellOne {x | -x ∈ Q} (-a0) r R p (-w) e = (ellOne Q a0 r R p w e).map Neg.neg := by
  unfold ellOne
  dsimp only
  simp only [abs_neg]
  by_cases h1 : R < r ∨ R < |a0|
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  rw [ite_eq_right h1, ite_eq_right h1]
  have hR : 0 ≤ R := by
    push Not at h1
    linarith [abs_nonneg a0, h1.2]
  by_cases h2 : a0 ∉ Q
  · rw [ite_eq_left h2, ite_eq_left (show -a0 ∉ {x : ℝ | -x ∈ Q} by simpa using h2)]; rfl
  rw [ite_eq_right h2, ite_eq_right (show ¬ -a0 ∉ {x : ℝ | -x ∈ Q} by simpa using h2)]
  rw [clamp_neg hR]
  by_cases h3 : max (-R) (min R w) ∈ Q
  · rw [ite_eq_left h3, ite_eq_left (show -max (-R) (min R w) ∈ {x : ℝ | -x ∈ Q} by simpa using h3)]; rfl
  rw [ite_eq_right h3, ite_eq_right (show -max (-R) (min R w) ∉ {x : ℝ | -x ∈ Q} by simpa using h3)]
  rw [show -max (-R) (min R w) - -a0 = -(max (-R) (min R w) - a0) by ring, abs_neg, oBisectLo_neg]
  rfl

theorem ell1_acc (Q : Set ℝ) (a0 r R p w e : ℝ) (hQ : Q.OrdConnected)
    (hball : Set.Icc (a0 - r) (a0 + r) ⊆ Q) (hQR : Q ⊆ Set.Icc (-R) R) (hr : 0 < r) (hp : 0 < p) (he : 0 < e) :
    ∃ μ, ellOne Q a0 r R p w e = some μ ∧ μ ∈ Q ∧ ∀ x ∈ Q, p * (μ - w) ^ 2 / 2 ≤ p * (x - w) ^ 2 / 2 + e := by
  have ha0 : a0 ∈ Q := hball ⟨by linarith, by linarith⟩
  have hR : 0 ≤ R := by have := hQR ha0; linarith [this.1, this.2]
  by_cases hup : a0 ≤ max (-R) (min R w)
  · exact ell1_acc_up Q a0 r R p w e hQ hball hQR hr hp he hup
  have hQ' : ({x : ℝ | -x ∈ Q}).OrdConnected :=
    ⟨fun x hx y hy z hz => hQ.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
  have hball' : Set.Icc (-a0 - r) (-a0 + r) ⊆ {x : ℝ | -x ∈ Q} := fun x hx =>
    hball ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hQR' : {x : ℝ | -x ∈ Q} ⊆ Set.Icc (-R) R := fun x hx => by
    have := hQR hx
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hup' : -a0 ≤ max (-R) (min R (-w)) := by rw [clamp_neg hR]; linarith
  obtain ⟨μ, hμ, hμQ, hμle⟩ := ell1_acc_up _ (-a0) r R p (-w) e hQ' hball' hQR' hr hp he hup'
  rw [ellOne_neg] at hμ
  obtain ⟨ν, hν, rfl⟩ := Option.map_eq_some_iff.mp hμ
  refine ⟨ν, hν, by simpa using hμQ, fun x hx => ?_⟩
  have h := hμle (-x) (by simpa using hx)
  rw [show (-ν - -w) ^ 2 = (ν - w) ^ 2 by ring, show (-x - -w) ^ 2 = (x - w) ^ 2 by ring] at h
  exact h

/-- Proposition ELL-1. -/
theorem propELL1 : PropELL1 := fun Q a0 r R p w e =>
  ⟨ell1_total Q a0 r R p w e, fun hQ hball hQR hr hp he => ell1_acc Q a0 r R p w e hQ hball hQR hr hp he⟩

/-! ## (SPEC-AP) for `apCall` -/

theorem oNorm_fin_one (v : Fin 1 → ℝ) : oNorm v = |v 0| := by
  unfold oNorm
  rw [show v ⬝ᵥ v = v 0 ^ 2 by simp [dotProduct, pow_two]]
  exact Real.sqrt_sq_eq_abs _

theorem ellF_fin_one (P : Matrix (Fin 1) (Fin 1) ℝ) (w x : Fin 1 → ℝ) :
    ellF P w x = P 0 0 * (x 0 - w 0) ^ 2 / 2 := by
  simp [ellF, dotProduct, mulVec, pow_two]
  ring

theorem const_fin_one (x : Fin 1 → ℝ) : (fun _ : Fin 1 => x 0) = x := by
  funext i; rw [Subsingleton.elim i 0]

/-- (SPEC-AP) for `apCall`: ELL-1 on the coordinate line for `d = 1`, ELL-cap for `d ≥ 2`. -/
theorem propAP : PropAP := by
  intro d Q a0 r R P w e
  by_cases hd : d = 1
  · subst hd
    have hap : apCall Q a0 r R P w e =
        (ellOne {x | (fun _ => x) ∈ Q} (a0 0) r R (P 0 0) (w 0) e).map fun x _ => x := by
      simp [apCall]
    rw [hap]
    refine ⟨?_, ?_⟩
    · intro _ hc _ hr hball hsub hP he
      have hord : ({x : ℝ | (fun _ : Fin 1 => x) ∈ Q}).OrdConnected := by
        apply Convex.ordConnected
        intro x hx y hy a b ha hb hab
        have := hc hx hy ha hb hab
        show (fun _ : Fin 1 => a • x + b • y) ∈ Q
        convert this using 1
      have hicc : Set.Icc (a0 0 - r) (a0 0 + r) ⊆ {x : ℝ | (fun _ : Fin 1 => x) ∈ Q} := by
        intro x hx
        apply hball
        show oNorm ((fun _ => x) - a0) ≤ r
        rw [oNorm_fin_one]
        simp only [Pi.sub_apply]
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have hsub1 : {x : ℝ | (fun _ : Fin 1 => x) ∈ Q} ⊆ Set.Icc (-R) R := by
        intro x hx
        have := hsub hx
        simp only [oBall, Set.mem_ofPred_eq, sub_zero, oNorm_fin_one] at this
        exact abs_le.mp this
      obtain ⟨μ, hμ, hμQ, hμmin⟩ := (propELL1 _ (a0 0) r R (P 0 0) (w 0) e).2 hord hicc hsub1 hr hP.diag_pos he
      refine ⟨fun _ => μ, by rw [hμ]; rfl, hμQ, ?_⟩
      intro x hx
      rw [ellF_fin_one, ellF_fin_one]
      have hx' : x 0 ∈ {x : ℝ | (fun _ : Fin 1 => x) ∈ Q} := by
        show (fun _ : Fin 1 => x 0) ∈ Q
        rw [const_fin_one]; exact hx
      exact hμmin (x 0) hx'
    · rcases (propELL1 {x | (fun _ => x) ∈ Q} (a0 0) r R (P 0 0) (w 0) e).1 with hn | ⟨μ, hμ, hμQ, hμR⟩
      · left; rw [hn]; rfl
      · right
        refine ⟨fun _ => μ, by rw [hμ]; rfl, hμQ, ?_⟩
        rw [oNorm_fin_one]; exact hμR
  · have hap : apCall Q a0 r R P w e = ellCap Q a0 r R P w e := by simp [apCall, hd]
    rw [hap]
    refine ⟨?_, propELLcap d Q a0 r R P w e⟩
    intro h1d hc hcl hr hball hsub hP he
    exact propELL d Q a0 r R P w e (by omega) hc hcl hr hball hsub hP he

end LeanAp

/-! ## The statements of `Df2Oracle.lean` -/

/-- Lemma E.4. -/
theorem lemmaCC : LemmaCC := LeanAp.lemmaCC

/-- Lemma E.5. -/
theorem lemmaBALL : LemmaBALL := LeanAp.lemmaBALL

/-- Lemma E.2. -/
theorem lemmaLINE : LemmaLINE := LeanAp.lemmaLINE

/-- Lemma E.3. -/
theorem lemmaSEP : LemmaSEP := LeanAp.lemmaSEP

/-- Lemma GAUGE. -/
theorem lemmaGAUGE : LemmaGAUGE := LeanAp.lemmaGAUGE

/-- Lemma GVAL. -/
theorem lemmaGVAL : LemmaGVAL := LeanAp.lemmaGVAL

/-- Lemma GCAP. -/
theorem lemmaGCAP : LemmaGCAP := LeanAp.lemmaGCAP

/-- Proposition ELL. -/
theorem propELL : PropELL := LeanAp.propELL

/-- Proposition ELL-cap. -/
theorem propELLcap : PropELLcap := LeanAp.propELLcap

/-- Proposition ELL-1. -/
theorem propELL1 : PropELL1 := LeanAp.propELL1

/-- (SPEC-AP) for `apCall`. -/
theorem propAP : PropAP := LeanAp.propAP

end AdversarialBco.Poly
