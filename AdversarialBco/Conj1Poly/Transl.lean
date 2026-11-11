/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Geom

@[expose] public section

/-!
# Theorem 1.3, translation of the body, the strategies and the regret (Section 8.6 of the paper)

The program of `TheoremConj1Upper` runs on `K - a₀` against `σ'(t, x, o)(y) = σ(t, x + a₀, o)(y + a₀)`.

* `transSet K a₀ = {y | y + a₀ ∈ K}`; it is compact and convex with `K` (`transSet_isCompact`, `transSet_convex`), it
  contains `B(0, r)` when `K` contains `B(a₀, r)` (`ball_transSet`), and it lies in `B(0, n)` when `a₀ ∈ K` and `K`
  has diameter at most `n` (`transSet_sub_ball`).
* `transStrat σ a₀` is in the class on `transSet K a₀` (`transStrat_mem`), and its observations and losses at points
  `x` are those of `σ` at `x + a₀` (`obsAd_trans`, `lossAd_trans`).
* The regret on `transSet K a₀` against translated losses at `x` is the regret on `K` at `x + a₀`
  (`regretPts_trans`).
-/

open MeasureTheory

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM

variable {d : ℕ}

/-- `K - a₀`. -/
def transSet (K : Set (E d)) (a0 : E d) : Set (E d) := {y | y + a0 ∈ K}

/-- `σ'(t, x, o)(y) = σ(t, x + a₀, o)(y + a₀)`. -/
def transStrat (σ : Strategy d) (a0 : E d) : Strategy d := fun t x o y => σ t (fun i => x i + a0) o (y + a0)

theorem transSet_isCompact {K : Set (E d)} (hK : IsCompact K) (a0 : E d) : IsCompact (transSet K a0) := by
  have h_eq : transSet K a0 = (fun y : E d => y - a0) '' K := by
    ext y
    constructor
    · intro hy
      rw [transSet] at hy
      refine ⟨y + a0, hy, ?_⟩
      simp
    · intro hy
      rcases hy with ⟨z, hz, hz_eq⟩
      dsimp at hz_eq
      rw [transSet, ← hz_eq]
      simp [hz]
  rw [h_eq]
  exact hK.image (continuous_sub_right a0)

theorem transSet_convex {K : Set (E d)} (hK : Convex ℝ K) (a0 : E d) : Convex ℝ (transSet K a0) := by
  simpa [transSet, add_comm, Set.preimage] using Convex.translate_preimage_right hK a0

theorem ball_transSet {K : Set (E d)} {a0 : E d} {r : ℝ} (h : Metric.closedBall a0 r ⊆ K) :
    Metric.closedBall 0 r ⊆ transSet K a0 := by
  intro y hy
  rw [Metric.mem_closedBall] at hy
  have hmem : y + a0 ∈ Metric.closedBall a0 r := by
    rw [Metric.mem_closedBall]
    calc
      dist (y + a0) a0 = ‖(y + a0) - a0‖ := by rw [dist_eq_norm]
      _ = ‖y‖ := by simp
      _ = dist y 0 := by rw [dist_eq_norm, sub_zero]
      _ ≤ r := hy
  have hK : y + a0 ∈ K := h hmem
  simp [transSet, hK]

theorem transSet_sub_ball {K : Set (E d)} {a0 : E d} {n : ℝ} (ha0 : a0 ∈ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ n) : transSet K a0 ⊆ Metric.closedBall 0 n := by
  intro y hy
  rw [AdversarialBco.Conj1Poly.transSet, Set.mem_ofPred_eq] at hy
  have hdist : dist (y + a0) a0 ≤ n := hdiam (y + a0) hy a0 ha0
  have hnorm : ‖y‖ ≤ n := by
    calc
      ‖y‖ = ‖(y + a0) - a0‖ := by simp
      _ = dist (y + a0) a0 := by rw [dist_eq_norm]
      _ ≤ n := hdist
  rw [mem_closedBall_zero_iff]
  exact hnorm

/-- T1a: the translated strategy is in the class on `K - a₀`. -/
theorem transStrat_mem {K : Set (E d)} {n : ℕ} {σ : Strategy d} (hσ : σ ∈ Strats K n) (a0 : E d) :
    transStrat σ a0 ∈ Strats (transSet K a0) n := by
  intro t ht
  have hσ' : ∀ t < n, (∀ x o, AdmLoss K (σ t x o)) ∧ ∀ y ∈ K, Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => σ t h.1 h.2 y := by
    simpa [Strats] using hσ
  rcases hσ' t ht with ⟨h_adm_val, h_meas⟩
  have h_adm_val' : ∀ x o, ConvexOn ℝ K (σ t x o) := fun x o => (h_adm_val x o).1
  have h_icc_val : ∀ x o y, y ∈ K → σ t x o y ∈ Set.Icc (0 : ℝ) 1 := fun x o y hy => (h_adm_val x o).2 y hy
  constructor
  · intro x o
    have h_conv : ConvexOn ℝ K (σ t (fun i => x i + a0) o) := h_adm_val' (fun i => x i + a0) o
    let g : E d →ᵃ[ℝ] E d := (AffineMap.id ℝ (E d) + AffineMap.const ℝ (E d) a0 : E d →ᵃ[ℝ] E d)
    have h_conv' : ConvexOn ℝ (transSet K a0) (σ t (fun i => x i + a0) o ∘ g) := by
      have := h_conv.comp_affineMap g
      -- this : ConvexOn ℝ (g ⁻¹' K) ((σ t (fun i => x i + a0) o) ∘ g)
      -- need: ConvexOn ℝ (transSet K a0) (σ t (fun i => x i + a0) o ∘ g)
      convert this using 1
      · ext y; simp [g, transSet]
    have h_conv'' : ConvexOn ℝ (transSet K a0) (transStrat σ a0 t x o) := by
      have : (σ t (fun i => x i + a0) o ∘ g) = transStrat σ a0 t x o := by
        ext y; simp [g, transStrat]
      simpa [this] using h_conv'
    have h_icc : ∀ y ∈ transSet K a0, (transStrat σ a0 t x o) y ∈ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      have hyK : y + a0 ∈ K := hy
      have hval := h_icc_val (fun i => x i + a0) o (y + a0) hyK
      simpa [transStrat] using hval
    exact ⟨h_conv'', h_icc⟩
  · intro y hy
    have hy' : y + a0 ∈ K := hy
    have h_meas_y : Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => σ t h.1 h.2 (y + a0) := h_meas (y + a0) hy'
    have h_map_meas : Measurable fun (h : (Fin t → E d) × (Fin t → ℝ)) => (fun i => h.1 i + a0, h.2) := by
      refine Measurable.prodMk ?_ measurable_snd
      refine Measurable.of_eval (fun i => ?_)
      have : Measurable fun (h : (Fin t → E d) × (Fin t → ℝ)) => h.1 i := by
        exact Measurable.comp (measurable_pi_apply i) measurable_fst
      exact Measurable.add_const this a0
    have : (fun h : (Fin t → E d) × (Fin t → ℝ) => (transStrat σ a0) t h.1 h.2 y) =
      (fun h => σ t h.1 h.2 (y + a0)) ∘ (fun (h : (Fin t → E d) × (Fin t → ℝ)) => (fun i => h.1 i + a0, h.2)) := by
      ext h; simp [transStrat]
    rw [this]
    exact h_meas_y.comp h_map_meas

/-- T1b: the observations of the translated strategy at `x` are those of `σ` at `x + a₀`. -/
theorem obsAd_trans (σ : Strategy d) (a0 : E d) (ε : ℕ → ℝ) (x : ℕ → E d) :
    ∀ t, obsAd (transStrat σ a0) ε x t = obsAd σ ε (fun u => x u + a0) t := by
  intro t
  induction t with
  | zero => ext i; exact i.elim0
  | succ t ih => simp only [obsAd, transStrat, ih]

/-- T1c: the losses of the translated strategy at `x` are those of `σ` at `x + a₀`, translated. -/
theorem lossAd_trans (σ : Strategy d) (a0 : E d) (ε : ℕ → ℝ) (x : ℕ → E d) (t : ℕ) (y : E d) :
    lossAd (transStrat σ a0) ε x t y = lossAd σ ε (fun u => x u + a0) t (y + a0) := by
  unfold lossAd
  simp [transStrat, obsAd_trans]

/-- T1d: the regret is invariant under the translation. -/
theorem regretPts_trans (K : Set (E d)) (a0 : E d) (f : ℕ → E d → ℝ) (x : ℕ → E d) (n : ℕ) :
    regretPts (transSet K a0) (fun t y => f t (y + a0)) x n = regretPts K f (fun u => x u + a0) n := by
  unfold regretPts
  have hsum : (∑ t ∈ Finset.range n, (fun t y => f t (y + a0)) t (x t)) =
             (∑ t ∈ Finset.range n, f t ((fun u => x u + a0) t)) := by
    simp
  rw [hsum]
  congr 1
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y + a0, hy, ?_⟩
    simp
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - a0, ?_, ?_⟩
    · dsimp [transSet]
      simpa [sub_add_cancel] using hz
    · simp

end AdversarialBco.Conj1Poly
