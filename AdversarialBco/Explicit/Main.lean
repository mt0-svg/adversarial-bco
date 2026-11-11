/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Lemmas
public import AdversarialBco.Explicit.Marg
public import AdversarialBco.StatementBody

@[expose] public section

/-!
# Theorem 1.5 and Corollary 1.6 on the interface `BodyHExplicit`

`theoremExplicit_of_bodyH` proves `TheoremExplicit` and `corollaryExplicit_of_bodyH` proves `CorollaryExplicit`
(`AdversarialBco/StatementExplicit.lean`), each from `BodySpec.BodyHExplicit` (`AdversarialBco/StatementBody.lean`,
hypothesis (H) of Proposition 2.2 on the inner body, proved in `AdversarialBco/Body2/PropBody.lean`). The net of Algorithm 7.1
(`ex_net_facts`, `ex_net_card`, `ex_net_two`), step 1 (`ex_solver_exists`, `ex_round_value`), the tree bound with
history-dependent losses (`ex_tree_adapt`), the comparator (`ex_comparator`), the regret against an adaptive
adversary (`ex_pseudo_main`) and the constants (`ex_const`, `ex_CX`). Corollary 1.6 uses Lemma 7.13
(`AdversarialBco/Explicit/Marg.lean`).
-/

open MeasureTheory Real

namespace AdversarialBco.Explicit

/-- The scan set is finite: each coordinate `k i` lies in a bounded interval of integers. -/
theorem ex_scanSet_finite {d : ℕ} (J : Set (E d)) (x0 : E d) (D h : ℝ) (hh : 0 < h) :
    (scanSet J x0 D h).Finite := by
  refine (Set.Finite.pi (t := fun i => Set.Icc (⌈(x0 i - D) / h⌉) (⌊(x0 i + D) / h⌋))
    fun i => Set.finite_Icc _ _).subset fun k hk i _ => ?_
  have h1 := abs_le.1 (hk.1 i)
  constructor
  · rw [Int.ceil_le, div_le_iff₀ hh]; linarith
  · rw [Int.le_floor, le_div_iff₀ hh]; linarith

theorem ex_scan_exists {d : ℕ} (J : Set (E d)) (x0 : E d) (D h : ℝ) (hh : 0 < h) :
    ∃ ord, IsScanOrder J x0 D h ord := by
  classical
  set F := (ex_scanSet_finite J x0 D h hh).toFinset
  exact ⟨F.toList, F.nodup_toList, fun k => by simp [F]⟩

/-- The two cases of a step of the greedy rule. -/
theorem ex_greedy_step {d : ℕ} (r : ℝ) (kept : List (E d)) (z : E d) :
    (greedyKeep r (kept ++ [z]) = greedyKeep r kept ++ [z] ∧ ∀ y ∈ greedyKeep r kept, r ≤ dist z y) ∨
      (greedyKeep r (kept ++ [z]) = greedyKeep r kept ∧ ∃ y ∈ greedyKeep r kept, dist z y < r) := by
  classical
  unfold greedyKeep
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases h : ∀ y ∈ List.foldl (fun kept z => if ∀ y ∈ kept, r ≤ dist z y then kept ++ [z] else kept) [] kept,
      r ≤ dist z y
  · left
    exact ⟨ite_eq_left h, h⟩
  · right
    refine ⟨ite_eq_right h, ?_⟩
    simp only [not_forall, not_le] at h
    obtain ⟨y, hy, hlt⟩ := h
    exact ⟨y, hy, hlt⟩

/-- The greedy rule only appends: the points kept from a prefix stay kept. -/
theorem ex_greedy_mono {d : ℕ} (r : ℝ) (pts rest : List (E d)) :
    ∀ y ∈ greedyKeep r pts, y ∈ greedyKeep r (pts ++ rest) := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest z ih =>
    intro y hy
    rw [← List.append_assoc]
    rcases ex_greedy_step r (pts ++ rest) z with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact List.mem_append_left _ (ih y hy)
    · rw [h1]; exact ih y hy

theorem ex_greedy_mem {d : ℕ} (r : ℝ) (pts : List (E d)) : ∀ z ∈ greedyKeep r pts, z ∈ pts := by
  induction pts using List.reverseRecOn with
  | nil => simp [greedyKeep]
  | append_singleton pts z ih =>
    intro y hy
    rcases ex_greedy_step r pts z with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ (ih y hy)
      · exact List.mem_append_right _ hy
    · rw [h1] at hy; exact List.mem_append_left _ (ih y hy)

theorem ex_greedy_sep {d : ℕ} (r : ℝ) (pts : List (E d)) :
    ∀ y ∈ greedyKeep r pts, ∀ z ∈ greedyKeep r pts, y ≠ z → r ≤ dist y z := by
  induction pts using List.reverseRecOn with
  | nil => simp [greedyKeep]
  | append_singleton pts z ih =>
    rcases ex_greedy_step r pts z with ⟨h1, h2⟩ | ⟨h1, -⟩
    · rw [h1]
      intro u hu v hv huv
      rcases List.mem_append.1 hu with hu | hu <;> rcases List.mem_append.1 hv with hv | hv
      · exact ih u hu v hv huv
      · rw [List.mem_singleton.1 hv, dist_comm]; exact h2 u hu
      · rw [List.mem_singleton.1 hu]; exact h2 v hv
      · exact absurd ((List.mem_singleton.1 hu).trans (List.mem_singleton.1 hv).symm) huv
    · rw [h1]; exact ih

theorem ex_greedy_cover {d : ℕ} (r : ℝ) (hr : 0 < r) (pts : List (E d)) :
    ∀ z ∈ pts, ∃ y ∈ greedyKeep r pts, dist z y < r := by
  induction pts using List.reverseRecOn with
  | nil => simp
  | append_singleton pts z ih =>
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨y, hy, hwy⟩ := ih w hw
      exact ⟨y, ex_greedy_mono r pts [z] y hy, hwy⟩
    · rw [List.mem_singleton.1 hw]
      rcases ex_greedy_step r pts z with ⟨h1, -⟩ | ⟨h1, y, hy, hzy⟩
      · exact ⟨z, by rw [h1]; exact List.mem_append_right _ (List.mem_singleton_self z), by simpa using hr⟩
      · exact ⟨y, by rw [h1]; exact hy, hzy⟩

theorem ex_round_point {d : ℕ} (hd : 1 ≤ d) (J : Set (E d)) (hJ : Convex ℝ J) (x0 : E d) (r0 D ε : ℝ)
    (hr0 : 1 / 2 ≤ r0) (hball : Metric.closedBall x0 r0 ⊆ J) (hJD : J ⊆ Metric.closedBall x0 D) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∀ x ∈ J, ∃ k ∈ scanSet J x0 D (mesh d ε D), dist x (latticePt (mesh d ε D) k) < ε / 2 := by
  intro x hx
  have hr0p : 0 < r0 := by linarith
  have hx0J : x0 ∈ J := hball (Metric.mem_closedBall_self hr0p.le)
  have hD : 0 ≤ D := by simpa using hJD hx0J
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : 1 ≤ √(d : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hd1
  set h := mesh d ε D with hh
  have hh0 : 0 < h := by rw [hh, mesh]; positivity
  set s := h * √(d : ℝ) / (2 * r0) with hs
  have hs_eq : s = ε / (4 * r0 * (D + 1)) := by
    rw [hs, hh, mesh]; field_simp; ring
  have hs0 : 0 < s := by rw [hs_eq]; positivity
  have hs1 : s ≤ 1 := by
    rw [hs_eq, div_le_one (by positivity)]; nlinarith
  set y : E d := (1 - s) • x + s • x0 with hy
  -- the ball of radius s r0 about y lies in J
  have hyball : Metric.closedBall y (s * r0) ⊆ J := by
    intro w hw
    set u : E d := x0 + s⁻¹ • (w - y) with hu
    have huJ : u ∈ J := by
      apply hball
      rw [Metric.mem_closedBall, dist_eq_norm, hu, add_sub_cancel_left, norm_smul, norm_inv,
        Real.norm_of_nonneg hs0.le, ← dist_eq_norm]
      rw [Metric.mem_closedBall] at hw
      rw [inv_mul_le_iff₀ hs0]; exact hw
    have hw' : w = (1 - s) • x + s • u := by
      rw [hu, smul_add, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, hy]; abel
    rw [hw']
    exact hJ hx huJ (by linarith) hs0.le (by ring)
  -- rounding y to the lattice
  let k : Fin d → ℤ := fun i => round (y i / h)
  have hk : ∀ i, |h * k i - y i| ≤ h / 2 := by
    intro i
    have h1 := abs_sub_round (y i / h)
    have h2 : h * (k i : ℝ) - y i = -(h * (y i / h - round (y i / h))) := by
      simp only [k]; field_simp; ring
    rw [h2, abs_neg, abs_mul, abs_of_pos hh0]
    calc h * |y i / h - round (y i / h)| ≤ h * (1 / 2) := mul_le_mul_of_nonneg_left h1 hh0.le
      _ = h / 2 := by ring
  set z := latticePt h k with hz
  have hzi : ∀ i, z i = h * k i := fun i => rfl
  have hzy : dist z y ≤ s * r0 := by
    rw [EuclideanSpace.dist_eq]
    have hsum : ∑ i, dist (z i) (y i) ^ 2 ≤ ∑ _i : Fin d, (h / 2) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Real.dist_eq, hzi]
      have := hk i
      have h0 : 0 ≤ |h * (k i : ℝ) - y i| := abs_nonneg _
      nlinarith
    have hval : s * r0 = √(∑ _i : Fin d, (h / 2) ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]
      field_simp
    rw [hval]
    exact Real.sqrt_le_sqrt hsum
  have hzJ : z ∈ J := hyball (Metric.mem_closedBall.2 hzy)
  refine ⟨k, ⟨fun i => ?_, hzJ⟩, ?_⟩
  · have h1 := PiLp.dist_apply_le z x0 i
    rw [Real.dist_eq, hzi] at h1
    exact h1.trans (Metric.mem_closedBall.1 (hJD hzJ))
  · have hxy : dist x y = s * dist x x0 := by
      rw [dist_eq_norm, dist_eq_norm, hy]
      have : x - ((1 - s) • x + s • x0) = s • (x - x0) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_of_nonneg hs0.le]
    have hxx0 : dist x x0 ≤ D := Metric.mem_closedBall.1 (hJD hx)
    calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ s * D + s * r0 := by
        rw [hxy, dist_comm y z]
        exact add_le_add (mul_le_mul_of_nonneg_left hxx0 hs0.le) hzy
      _ < ε / 2 := by
        rw [hs_eq]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_lt_div_iff₀ (by positivity) two_pos]
        have h2r : 0 ≤ 2 * r0 - 1 := by linarith
        nlinarith [mul_pos hε hr0p, mul_nonneg (mul_nonneg hε.le hD) h2r]

theorem ex_net_card {d : ℕ} (J : Set (E d)) (hJb : Bornology.IsBounded J) (C : Finset (E d)) (hCJ : ↑C ⊆ J)
    (ε D : ℝ) (hε : 0 < ε) (hεD : ε ≤ D) (hJD : Metric.diam J ≤ D)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε / 2 ≤ dist x y) : (C.card : ℝ) ≤ (5 * D / ε) ^ d := by
  have hpos : 0 < ε / 2 := by linarith
  have hcard := AdversarialBco.card_le_of_separated J hJb C hCJ (ε / 2) hpos hsep
  -- hcard : (C.card : ℝ) ≤ (1 + 2 * Metric.diam J / (ε / 2)) ^ d
  have hdiam_nonneg : 0 ≤ Metric.diam J := Metric.diam_nonneg
  have hdiv_eq : 2 * Metric.diam J / (ε / 2) = 4 * Metric.diam J / ε := by
    field_simp [ne_of_gt hε]
    ring
  have hdiv_le : 4 * Metric.diam J / ε ≤ 4 * D / ε := by
    gcongr
  have hone : (1 : ℝ) ≤ D / ε := by
    exact (one_le_div hε).mpr hεD
  have hsum : (1 : ℝ) + 4 * Metric.diam J / ε ≤ 5 * D / ε := by
    calc
      (1 : ℝ) + 4 * Metric.diam J / ε ≤ D / ε + 4 * D / ε := add_le_add hone hdiv_le
      _ = 5 * D / ε := by ring
  have hdiv_nonneg : 0 ≤ 4 * Metric.diam J / ε :=
    div_nonneg (by nlinarith) (by linarith)
  have hbase_nonneg : 0 ≤ (1 : ℝ) + 4 * Metric.diam J / ε := by
    nlinarith
  have hpow := pow_le_pow_left₀ hbase_nonneg hsum d
  calc
    (C.card : ℝ) ≤ (1 + 2 * Metric.diam J / (ε / 2)) ^ d := hcard
    _ = (1 + 4 * Metric.diam J / ε) ^ d := by rw [hdiv_eq]
    _ ≤ (5 * D / ε) ^ d := hpow

theorem ex_net_two {d : ℕ} (hd : 1 ≤ d) (J : Set (E d)) (x0 : E d) (hball : Metric.closedBall x0 (1 / 2) ⊆ J)
    (C : Finset (E d)) (ε : ℝ) (hε4 : ε ≤ 1 / 4) (hcov : ∀ x ∈ J, ∃ c ∈ C, dist x c < ε) : 2 ≤ C.card := by
  set e : E d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hne : ‖e‖ = 1 := by rw [he, PiLp.norm_single, norm_one]
  have h1 : x0 + (1 / 2 : ℝ) • e ∈ J := hball (by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hne]; norm_num)
  have h2 : x0 - (1 / 2 : ℝ) • e ∈ J := hball (by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hne]; norm_num)
  obtain ⟨c1, hc1, hd1⟩ := hcov _ h1
  obtain ⟨c2, hc2, hd2⟩ := hcov _ h2
  have hdist : dist (x0 + (1 / 2 : ℝ) • e) (x0 - (1 / 2 : ℝ) • e) = 1 := by
    rw [dist_eq_norm, show x0 + (1 / 2 : ℝ) • e - (x0 - (1 / 2 : ℝ) • e) = (1 : ℝ) • e by
      rw [one_smul]; module, one_smul, hne]
  have hc : c1 ≠ c2 := by
    rintro rfl
    have := dist_triangle_right (x0 + (1 / 2 : ℝ) • e) (x0 - (1 / 2 : ℝ) • e) c1
    linarith
  exact Finset.one_lt_card.2 ⟨c1, hc1, c2, hc2, hc⟩

/-- The net of Algorithm 7.1 lies in `J`, is `ε/2`-separated, and every point of `J` is within `ε` of it. -/
theorem ex_net_facts {d : ℕ} (hd : 1 ≤ d) (J : Set (E d)) (hJ : Convex ℝ J) (x0 : E d) (r0 D ε : ℝ)
    (hr0 : 1 / 2 ≤ r0) (hball : Metric.closedBall x0 r0 ⊆ J) (hJD : J ⊆ Metric.closedBall x0 D) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ord : List (Fin d → ℤ)) (hord : IsScanOrder J x0 D (mesh d ε D) ord) :
    ↑(net ε D ord) ⊆ J ∧ (∀ x ∈ net ε D ord, ∀ y ∈ net ε D ord, x ≠ y → ε / 2 ≤ dist x y) ∧
      ∀ x ∈ J, ∃ c ∈ net ε D ord, dist x c < ε := by
  classical
  have hmem : ∀ z, z ∈ net ε D ord ↔ z ∈ greedyKeep (ε / 2) (ord.map (latticePt (mesh d ε D))) := by
    intro z
    simp only [net, List.mem_toFinset]
  refine ⟨fun z hz => ?_, fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · have h1 := ex_greedy_mem (ε / 2) _ z ((hmem z).1 hz)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h1
    exact ((hord.2 k).1 hk).2
  · exact ex_greedy_sep (ε / 2) _ x ((hmem x).1 hx) y ((hmem y).1 hy) hxy
  · obtain ⟨k, hk, hxk⟩ := ex_round_point hd J hJ x0 r0 D ε hr0 hball hJD hε hε1 x hx
    have hz : latticePt (mesh d ε D) k ∈ ord.map (latticePt (mesh d ε D)) :=
      List.mem_map.2 ⟨k, (hord.2 k).2 hk, rfl⟩
    obtain ⟨c, hc, hzc⟩ := ex_greedy_cover (ε / 2) (by linarith) _ _ hz
    refine ⟨c, (hmem c).2 hc, ?_⟩
    calc dist x c ≤ dist x (latticePt (mesh d ε D) k) + dist (latticePt (mesh d ε D) k) c := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxk hzc
      _ = ε := by ring

/-! ## Step 1 -/

theorem ex_Rbar_lower {C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (hη : 0 < η) (q : C → ℝ) (hq : ∀ z, 0 < q z)
    (hq1 : ∑ z, q z = 1) (pg : (C → ℝ) × (C → Bool → C → ℝ)) (hpg : pg ∈ SetS η q) : ∃ y, 0 ≤ roundR pg 0 y := by
  set p := pg.1 with hp_def
  set g := pg.2 with hg_def
  have hp_prob : p ∈ probVecs C := hpg.1
  have hp_pos : ∀ x, 0 ≤ p x := hp_prob.1
  have hp_sum : ∑ x, p x = 1 := hp_prob.2
  have hpg_cond := hpg.2
  -- For each x, show 0 ≤ ∑ z, q z * g x false z
  have h_nonneg_sum : ∀ x, 0 ≤ ∑ z, q z * g x false z := by
    intro x
    by_cases hpx : p x > 0
    · -- case p x > 0
      have h_exp_bound : ∑ z, q z * Real.exp (-η * (g x false z / p x)) ≤ 1 := by
        have := hpg_cond x false
        rcases this with ⟨h1, h2⟩
        exact h1 hpx
      have h_exp_ineq : ∀ z, 1 - η * (g x false z / p x) ≤ Real.exp (-η * (g x false z / p x)) := by
        intro z
        have := Real.add_one_le_exp (-η * (g x false z / p x))
        linarith
      have h_sum_ineq : ∑ z, q z * (1 - η * (g x false z / p x)) ≤ ∑ z, q z * Real.exp (-η * (g x false z / p x)) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        have hqz_pos : 0 ≤ q z := le_of_lt (hq z)
        have h_ineq := h_exp_ineq z
        exact mul_le_mul_of_nonneg_left h_ineq hqz_pos
      have h_left : ∑ z, q z * (1 - η * (g x false z / p x)) = 1 - (η / p x) * (∑ z, q z * g x false z) := by
        calc
          ∑ z, q z * (1 - η * (g x false z / p x))
              = ∑ z, (q z - q z * η * (g x false z / p x)) := by
            refine Finset.sum_congr rfl (fun z _ => ?_)
            ring
          _ = (∑ z, q z) - (∑ z, q z * η * (g x false z / p x)) := by
            rw [Finset.sum_sub_distrib]
          _ = 1 - (∑ z, q z * η * (g x false z / p x)) := by rw [hq1]
          _ = 1 - (η / p x) * (∑ z, q z * g x false z) := by
            simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      rw [h_left] at h_sum_ineq
      have h_factor_pos : 0 < η / p x := div_pos hη hpx
      have h_nonneg'' : (η / p x) * (∑ z, q z * g x false z) ≥ 0 := by
        have : 1 - (η / p x) * (∑ z, q z * g x false z) ≤ 1 := by
          linarith
        linarith
      have h_nonneg_sum' : 0 ≤ ∑ z, q z * g x false z := by
        nlinarith
      exact h_nonneg_sum'
    · -- p x ≤ 0
      have hpx_nonpos : p x ≤ 0 := by linarith
      have hp_nonneg : 0 ≤ p x := hp_pos x
      have hpx_eq_zero : p x = 0 := by linarith
      -- From SetS condition, when p x = 0, we have g x false z ≥ 0 for all z
      have hg_nonneg : ∀ z, 0 ≤ g x false z := by
        have hcond := hpg_cond x false
        rcases hcond with ⟨hpos_cond, hzero_cond⟩
        exact hzero_cond hpx_eq_zero
      have hq_nonneg : ∀ z, 0 ≤ q z := fun z => le_of_lt (hq z)
      -- Then ∑ z, q z * g x false z ≥ 0
      refine Finset.sum_nonneg (fun z _ => ?_)
      exact mul_nonneg (hq_nonneg z) (hg_nonneg z)
  -- Now compute ∑ y, q y * roundR pg 0 y
  have h_total_nonneg : 0 ≤ ∑ y, q y * roundR pg 0 y := by
    have h_roundR_simp : ∀ y, roundR pg 0 y = ∑ x, g x false y := by
      intro y
      simp [roundR, hg_def]
    simp_rw [h_roundR_simp]
    -- target: 0 ≤ ∑ y, q y * (∑ x, g x false y)
    simp_rw [Finset.mul_sum]
    -- target: 0 ≤ ∑ y, ∑ x, q y * g x false y
    rw [Finset.sum_comm]
    -- target: 0 ≤ ∑ x, ∑ y, q y * g x false y
    exact Finset.sum_nonneg (fun x _ => h_nonneg_sum x)
  -- Now use contradiction: if all roundR pg 0 y < 0, then the sum would be < 0
  by_contra! h_all_neg
  -- h_all_neg : ∀ y, ¬ (0 ≤ roundR pg 0 y), i.e., roundR pg 0 y < 0 for all y
  have h_all_neg' : ∀ y, roundR pg 0 y < 0 := by
    intro y
    have h_not_nonneg := h_all_neg y
    linarith
  have h_sum_neg : ∑ y, q y * roundR pg 0 y < 0 := by
    have h_each_nonpos : ∀ y, q y * roundR pg 0 y ≤ 0 := by
      intro y
      have hy_nonpos : roundR pg 0 y ≤ 0 := le_of_lt (h_all_neg' y)
      have hy_pos : 0 ≤ q y := le_of_lt (hq y)
      exact mul_nonpos_of_nonneg_of_nonpos hy_pos hy_nonpos
    obtain ⟨y0⟩ := ‹Nonempty C›
    have h_strict : q y0 * roundR pg 0 y0 < 0 := by
      have hy0 : q y0 > 0 := hq y0
      have h_round0 : roundR pg 0 y0 < 0 := h_all_neg' y0
      nlinarith
    calc
      ∑ y, q y * roundR pg 0 y < ∑ y, (0 : ℝ) := by
        refine Finset.sum_lt_sum (fun y _ => h_each_nonpos y) ?_
        exact ⟨y0, Finset.mem_univ y0, h_strict⟩
      _ = 0 := by simp
  linarith

/-- `R(p, g; f, y)` is bounded over `f ∈ P_L` and `y`, by a bound of `(p, g)` alone. -/
theorem ex_roundR_le {d : ℕ} {C : Type*} [Fintype C] (pt : C → E d) (L : ℝ) (pg : (C → ℝ) × (C → Bool → C → ℝ)) :
    ∀ y, ∀ f ∈ PL pt L, roundR pg f y ≤
      ∑ x, |pg.1 x| + 1 + ∑ y' : C, ∑ x, (|pg.2 x false y'| + |pg.2 x true y'|) := by
  intro y f hf
  have hf01 := hf.1
  unfold roundR
  have h1 : ∑ x, pg.1 x * f x ≤ ∑ x, |pg.1 x| := Finset.sum_le_sum fun x _ => by
    have := hf01 x
    calc pg.1 x * f x ≤ |pg.1 x * f x| := le_abs_self _
      _ = |pg.1 x| * f x := by rw [abs_mul, abs_of_nonneg this.1]
      _ ≤ |pg.1 x| * 1 := mul_le_mul_of_nonneg_left this.2 (abs_nonneg _)
      _ = |pg.1 x| := mul_one _
  have h2 : -f y ≤ 1 := by linarith [(hf01 y).1, (hf01 y).2]
  have h3 : ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y) ≤
      ∑ x, (|pg.2 x false y| + |pg.2 x true y|) := Finset.sum_le_sum fun x _ => by
    obtain ⟨h0, h1⟩ := hf01 x
    have ha : (1 - f x) * pg.2 x false y ≤ |pg.2 x false y| := by
      calc (1 - f x) * pg.2 x false y ≤ |(1 - f x) * pg.2 x false y| := le_abs_self _
        _ = (1 - f x) * |pg.2 x false y| := by rw [abs_mul, abs_of_nonneg (by linarith)]
        _ ≤ 1 * |pg.2 x false y| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = |pg.2 x false y| := one_mul _
    have hb : f x * pg.2 x true y ≤ |pg.2 x true y| := by
      calc f x * pg.2 x true y ≤ |f x * pg.2 x true y| := le_abs_self _
        _ = f x * |pg.2 x true y| := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ 1 * |pg.2 x true y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |pg.2 x true y| := one_mul _
    linarith
  have h4 : ∑ x, (|pg.2 x false y| + |pg.2 x true y|) ≤
      ∑ y' : C, ∑ x, (|pg.2 x false y'| + |pg.2 x true y'|) :=
    Finset.single_le_sum (f := fun y' : C => ∑ x, (|pg.2 x false y'| + |pg.2 x true y'|))
      (fun y' _ => Finset.sum_nonneg fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ y)
  linarith

theorem ex_step1_exists {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] (pt : C → E d) (L η tol : ℝ) (hL : 0 ≤ L)
    (hη : 0 < η) (htol : 0 < tol) (q : C → ℝ) (hq : ∀ z, 0 < q z) (hq1 : ∑ z, q z = 1) :
    ∃ pg, IsStep1 pt L η tol q pg := by
  classical
  let U : (C → ℝ) × (C → Bool → C → ℝ) → Set ℝ := fun pg => {c | ∀ y, ∀ f ∈ PL pt L, roundR pg f y ≤ c}
  let Rb : (C → ℝ) × (C → Bool → C → ℝ) → ℝ := fun pg => sInf (U pg)
  have hUne : ∀ pg, (U pg).Nonempty := fun pg => ⟨_, ex_roundR_le pt L pg⟩
  have h0PL : (0 : C → ℝ) ∈ PL pt L :=
    ⟨fun _ => ⟨le_rfl, zero_le_one⟩, 0, fun _ => by simp [hL], fun x z => by simp⟩
  have hUlow : ∀ pg ∈ SetS η q, ∀ c ∈ U pg, 0 ≤ c := by
    intro pg hpg c hc
    obtain ⟨y0, hy0⟩ := ex_Rbar_lower η hη q hq hq1 pg hpg
    exact hy0.trans (hc y0 0 h0PL)
  have hUbdd : ∀ pg ∈ SetS η q, BddBelow (U pg) := fun pg hpg => ⟨0, fun c hc => hUlow pg hpg c hc⟩
  have hRb0 : ∀ pg ∈ SetS η q, 0 ≤ Rb pg := fun pg hpg => le_csInf (hUne pg) (hUlow pg hpg)
  have hRbge : ∀ pg, ∀ y, ∀ f ∈ PL pt L, roundR pg f y ≤ Rb pg :=
    fun pg y f hf => le_csInf (hUne pg) fun c hc => hc y f hf
  -- a pair of `S_q`
  have hcard : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpg0 : ((fun _ => 1 / (Fintype.card C : ℝ)), (fun _ _ _ => 0)) ∈ SetS η q := by
    refine ⟨⟨fun _ => by positivity, ?_⟩, fun x b => ⟨fun _ => ?_, fun _ _ => le_rfl⟩⟩
    · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    · simp [hq1]
  set V := Rb '' SetS η q with hV
  have hVne : V.Nonempty := ⟨_, Set.mem_image_of_mem Rb hpg0⟩
  have hVbdd : BddBelow V := ⟨0, by rintro _ ⟨pg, hpg, rfl⟩; exact hRb0 pg hpg⟩
  obtain ⟨_, ⟨pg, hpg, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hVne (lt_add_of_pos_right (sInf V) htol)
  refine ⟨pg, hpg, fun pg' hpg' c hc y f hf => ?_⟩
  have h1 : Rb pg' ≤ c := csInf_le (hUbdd pg' hpg') hc
  have h2 : sInf V ≤ Rb pg' := csInf_le hVbdd (Set.mem_image_of_mem Rb hpg')
  linarith [hRbge pg y f hf]

/-- A step-1 procedure exists. -/
theorem ex_solver_exists {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] (pt : C → E d) (L η tol : ℝ) (hL : 0 ≤ L)
    (hη : 0 < η) (htol : 0 < tol) : ∃ sol, IsSolver pt L η tol sol := by
  classical
  have h : ∀ q : C → ℝ, ∃ pg, (∀ z, 0 < q z) → ∑ z, q z = 1 → IsStep1 pt L η tol q pg := by
    intro q
    by_cases hq : (∀ z, 0 < q z) ∧ ∑ z, q z = 1
    · obtain ⟨pg, hpg⟩ := ex_step1_exists pt L η tol hL hη htol q hq.1 hq.2
      exact ⟨pg, fun _ _ => hpg⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hq⟩
  choose sol hsol using h
  exact ⟨sol, fun q hq hq1 => hsol q hq hq1⟩

theorem ex_setS_iff {C : Type*} [Fintype C] (η : ℝ) (q : C → ℝ) (pg : (C → ℝ) × (C → Bool → C → ℝ)) :
    pg ∈ SetS η q ↔ (pg.1 ∈ stdSimplex ℝ C ∧ ∀ x b,
      (0 < pg.1 x ∧ ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∨ (pg.1 x = 0 ∧ ∀ z, 0 ≤ pg.2 x b z)) := by
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun x b => ?_⟩
    rcases (hp.1 x).lt_or_eq with hx | hx
    · exact Or.inl ⟨hx, (h x b).1 hx⟩
    · exact Or.inr ⟨hx.symm, (h x b).2 hx.symm⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun x b => ?_⟩
    rcases h x b with ⟨hx, hS⟩ | ⟨hx, hg⟩
    · exact ⟨fun _ => hS, fun h0 => absurd h0 hx.ne'⟩
    · exact ⟨fun h0 => absurd hx h0.ne', fun _ => hg⟩

theorem ex_round_value {d : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C] (J : Set (E d))
    (hJc : Convex ℝ J) (hJm : MeasurableSet J) (L ε α β η tol : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hη : 0 < η) (hH : HypH J L 0 1 α β) (pt : C → E d) (hpt : ∀ x, pt x ∈ J) (pr : E d → C)
    (hprm : ∀ x, MeasurableSet (pr ⁻¹' {x})) (hpr : ∀ z ∈ J, ‖z - pt (pr z)‖ ≤ ε)
    (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) (hsol : IsSolver pt L η tol sol) (q : C → ℝ)
    (hq : ∀ z, 0 < q z) (hq1 : ∑ z, q z = 1) :
    ∀ y, ∀ f ∈ PL pt L, roundR (sol q) f y ≤ (1 + 2 * L * ε) * α + L * ε * (1 + √β) + η * β / 8 + tol := by
  intro y f hf
  have h0PL : (0 : C → ℝ) ∈ PL pt L :=
    ⟨fun _ => ⟨le_rfl, zero_le_one⟩, 0, fun _ => by simp [hL], fun x z => by simp⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hdual := AdversarialBco.value_dual J hJc hJm L ε α β η δ hL hε hβ hη hδ hH pt hpt pr hprm hpr q hq hq1
  obtain ⟨pg, hpg, hlt⟩ := AdversarialBco.round_exists η hη q hq (PL pt L) (AdversarialBco.convex_PL pt L)
    (AdversarialBco.isCompact_PL pt L) ⟨0, h0PL⟩ _ hdual
  have hpgS : pg ∈ SetS η q := (ex_setS_iff η q pg).2 hpg
  have h := (hsol q hq hq1).2 pg hpgS _ (fun y f hf => (hlt y f hf).le) y f hf
  linarith

/-! ## The learner and its law -/

/-- The weights of Algorithm 7.1 are the exponential weights `ewQ` of `Lemmas.lean`. -/
theorem ex_weights_eq {C : Type*} [Fintype C] (η : ℝ) (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) :
    ∀ (t : ℕ) (h : Fin t → C × Bool),
      weights η sol t h = AdversarialBco.ewQ η (fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1) t h
  | 0, h => rfl
  | t + 1, h => by
    funext y
    simp only [weights, AdversarialBco.ewQ, ex_weights_eq η sol t (Fin.init h)]

theorem ex_tree_adapt {C : Type*} [Fintype C] [Nonempty C] (η : ℝ) (hη : 0 < η)
    (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) (P : Set (C → ℝ)) (c : ℝ) (_hc : 0 ≤ c)
    (hsol : ∀ q : C → ℝ, (∀ z, 0 < q z) → ∑ z, q z = 1 → ((sol q).1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < (sol q).1 x ∧ ∑ z, q z * Real.exp (-η * ((sol q).2 x b z / (sol q).1 x)) ≤ 1) ∨
        ((sol q).1 x = 0 ∧ ∀ z, 0 ≤ (sol q).2 x b z)) ∧
      ∀ y, ∀ f ∈ P, ∑ x, (sol q).1 x * f x - f y +
        ∑ x, ((1 - f x) * (sol q).2 x false y + f x * (sol q).2 x true y) ≤ c)
    (n : ℕ) (a : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (ha : ∀ t h x, a t h x ∈ Set.Icc (0 : ℝ) 1)
    (haP : ∀ t < n, ∀ h, a t h ∈ P) (y : C) :
    ∑ h : Fin n → C × Bool,
        (∏ s : Fin n, (sol (AdversarialBco.ewQ η (fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1) s
            (fun i : Fin s => h (Fin.castLE s.2.le i)))).1 (h s).1 *
          (if (h s).2 then a s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1
            else 1 - a s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1)) *
        ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
          a t (fun i : Fin t => h (Fin.castLE t.2.le i)) y) ≤
      Real.log (Fintype.card C) / η + n * c := by
  let est := fun (q : C → ℝ) (τ : C × Bool) (z : C) => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1
  let Q := fun (t : ℕ) (h : Fin t → C × Bool) (z : C) => AdversarialBco.ewQ η est t h z
  let κ := fun (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) =>
    (sol (Q t h)).1 τ.1 * (if τ.2 then a t h τ.1 else 1 - a t h τ.1)
  let G := fun (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) =>
    a t h τ.1 - a t h y + est (Q t h) τ y + (1 / η) * Real.log (∑ z, Q t h z * Real.exp (-η * est (Q t h) τ z))
  have hQ (t : ℕ) (h : Fin t → C × Bool) : (∀ z, 0 < Q t h z) ∧ ∑ z, Q t h z = 1 :=
    AdversarialBco.ewQ_pos_sum η est t h
  have hstd (t : ℕ) (h : Fin t → C × Bool) : (sol (Q t h)).1 ∈ stdSimplex ℝ C :=
    (hsol (Q t h) (hQ t h).1 (hQ t h).2).1.1
  have hκ0 (t : ℕ) (h : Fin t → C × Bool) (τ : C × Bool) : 0 ≤ κ t h τ := by
    obtain ⟨hlo, hhi⟩ := ha t h τ.1
    refine mul_nonneg ((hstd t h).1 τ.1) ?_
    split <;> linarith
  have hκ1 (t : ℕ) (h : Fin t → C × Bool) : ∑ τ, κ t h τ = 1 := by
    simp only [κ, Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    calc ∑ x, ((sol (Q t h)).1 x * a t h x + (sol (Q t h)).1 x * (1 - a t h x))
        = ∑ x, (sol (Q t h)).1 x := Finset.sum_congr rfl fun x _ => by ring
      _ = 1 := (hstd t h).2
  have h_sum_prod : ∑ h : Fin n → C × Bool, ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) = 1 :=
    AdversarialBco.sum_prod_policy κ hκ1 n
  have h_path_G (h : Fin n → C × Bool) :
      ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
          a t (fun i : Fin t => h (Fin.castLE t.2.le i)) y) ≤
        Real.log (Fintype.card C) / η + ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
    have hpath := AdversarialBco.ew_path η hη est n h y
    have hG_sum : ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) =
        ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
          a t (fun i : Fin t => h (Fin.castLE t.2.le i)) y) +
        ∑ t : Fin n, (est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) y +
          (1 / η) * Real.log (∑ z, AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i)) z *
            Real.exp (-η * est (AdversarialBco.ewQ η est t (fun i : Fin t => h (Fin.castLE t.2.le i))) (h t) z))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [G, Q]
      ring
    rw [hG_sum]
    have : -Real.log (Fintype.card C) / η = -(Real.log (Fintype.card C) / η) := neg_div _ _
    linarith
  have hG (t : ℕ) (ht : t < n) (h : Fin t → C × Bool) : ∑ τ, κ t h τ * G t h τ ≤ c := by
    have hfeas := hsol (Q t h) (hQ t h).1 (hQ t h).2
    have hbr := AdversarialBco.br_step η hη (Q t h) (hQ t h).1 (sol (Q t h)).1 (sol (Q t h)).2 hfeas.1 (a t h)
      (ha t h) y
    exact hbr.trans (hfeas.2 y (a t h) (haP t ht h))
  have h_tower := AdversarialBco.tree_sum_le_round κ hκ0 hκ1 G (fun _ => c) n hG
  calc
    ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
        ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
          a t (fun i : Fin t => h (Fin.castLE t.2.le i)) y)
        ≤ ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          (Real.log (Fintype.card C) / η + ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t)) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (h_path_G h)
        (Finset.prod_nonneg fun s _ => hκ0 s _ (h s))
    _ = Real.log (Fintype.card C) / η +
        ∑ h : Fin n → C × Bool, (∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s)) *
          ∑ t : Fin n, G t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, h_sum_prod, one_mul]
    _ ≤ Real.log (Fintype.card C) / η + ∑ t ∈ Finset.range n, c := by gcongr
    _ = Real.log (Fintype.card C) / η + n * c := by simp [Finset.sum_const, Finset.card_range]

open AdversarialBco AdversarialBco.Explicit in
theorem ex_comparator {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (x0 : E d) (hx0 : Metric.closedBall x0 1 ⊆ K)
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (C : Finset (E d)) (hCJ : ↑C ⊆ innerBody K n)
    (hcov : ∀ x ∈ innerBody K n, ∃ c ∈ C, dist x c < ε) (x : E d) (hx : x ∈ K) :
    ∃ y ∈ C, ∀ g : E d → ℝ, AdmLoss K g → g y ≤ g x + 1 / n + n * ε := by
  set s := 1 / (n : ℝ) with hs_def
  have hn_pos : 0 < (n : ℝ) := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact h1.trans_le (by exact_mod_cast hn)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    refine div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le n)
  have hs1 : s ≤ 1 := by
    dsimp [s]
    have hpos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.one_pos.trans_le hn)
    exact ((div_le_one hpos).mpr (by exact_mod_cast hn))
  set x' := (1 - s) • x + s • x0 with hx'_def
  have hx0_mem_K : x0 ∈ K := hx0 (Metric.mem_closedBall_self zero_le_one)
  have hx'_inner : x' ∈ innerBody K n := by
    dsimp [innerBody, x']
    have hball : Metric.closedBall ((1 - s) • x + s • x0) s ⊆ K :=
      AdversarialBco.closedBall_shrink_subset K hK x0 hx0 x hx s hs0 hs1
    rw [hs_def]
    exact hball
  rcases hcov x' hx'_inner with ⟨y, hy_mem, hy_dist⟩
  refine ⟨y, hy_mem, ?_⟩
  intro g hg
  rcases hg with ⟨hg_conv, hg_range⟩
  have hy_mem_set : y ∈ (C : Set (E d)) := Finset.mem_coe.mpr hy_mem
  have hy_inner : y ∈ innerBody K n := hCJ hy_mem_set
  have h_abs : |g y - g x'| ≤ (n : ℝ) * ‖y - x'‖ :=
    AdversarialBco.abs_sub_le_inner K g hg_conv hg_range n hn y x' hy_inner hx'_inner
  have h_g_diff : g y - g x' ≤ (n : ℝ) * ε := by
    have h_right : g y - g x' ≤ (n : ℝ) * ‖y - x'‖ := by
      have := abs_le.mp h_abs
      exact this.right
    have h_norm_lt : ‖y - x'‖ < ε := by
      calc
        ‖y - x'‖ = dist y x' := by rw [dist_eq_norm]
        _ = dist x' y := by rw [dist_comm]
        _ < ε := hy_dist
    have h_norm_le : ‖y - x'‖ ≤ ε := le_of_lt h_norm_lt
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  have h_comb : g x' ≤ g x + s :=
    AdversarialBco.convex_comb_le K g hg_conv hg_range x x0 hx hx0_mem_K s hs0 hs1
  rw [hs_def] at h_comb
  linarith

theorem ex_coinLaw_sum {d : ℕ} {C : Type*} [Fintype C] (pt : C → E d) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ)
    (hP : ∀ t h, P t h ∈ probVecs C) (A : (t : ℕ) → (Fin t → E d × Bool) → E d → ℝ) (n : ℕ)
    (hA : ∀ t < n, ∀ χ x, A t χ (pt x) ∈ Set.Icc (0 : ℝ) 1) :
    (∀ h, 0 ≤ coinLaw pt P A n h) ∧ ∑ h, coinLaw pt P A n h = 1 := by
  have hP_nonneg : ∀ t h x, 0 ≤ P t h x := by
    intro t h x
    have hmem := hP t h
    rcases hmem with ⟨hnonneg, hsum⟩
    exact hnonneg x
  have hP_sum : ∀ t h, ∑ x : C, P t h x = 1 := by
    intro t h
    have hmem := hP t h
    rcases hmem with ⟨hnonneg, hsum⟩
    exact hsum
  have hA_range : ∀ t < n, ∀ χ x, 0 ≤ A t χ (pt x) ∧ A t χ (pt x) ≤ 1 := by
    intro t ht χ x
    have hmem := hA t ht χ x
    rcases hmem with ⟨hlo, hhi⟩
    exact ⟨hlo, hhi⟩
  have sum_bern : ∀ o : ℝ, ∑ b : Bool, bern o b = 1 := by
    intro o
    calc
      ∑ b : Bool, bern o b = bern o true + bern o false := by
        simp [Finset.sum_insert]
      _ = o + (1 - o) := rfl
      _ = 1 := by ring
  have nonneg_bern : ∀ o : ℝ, 0 ≤ o → o ≤ 1 → ∀ b : Bool, 0 ≤ bern o b := by
    intro o hlo hhi b
    dsimp [bern]
    split
    · exact hlo
    · linarith
  set κ : (t : ℕ) → (Fin t → C × Bool) → (C × Bool) → ℝ := fun t h τ =>
    P t h τ.1 * bern (A t (fun i => (pt (h i).1, (h i).2)) (pt τ.1)) τ.2
  with hκ
  have hκ_sum : ∀ t h, ∑ τ : C × Bool, κ t h τ = 1 := by
    intro t h
    dsimp [κ]
    calc
      ∑ τ : C × Bool, P t h τ.1 * bern (A t (fun i => (pt (h i).1, (h i).2)) (pt τ.1)) τ.2
          = ∑ x : C, ∑ b : Bool, P t h x * bern (A t (fun i => (pt (h i).1, (h i).2)) (pt x)) b := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : C, P t h x * (∑ b : Bool, bern (A t (fun i => (pt (h i).1, (h i).2)) (pt x)) b) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ x : C, P t h x * 1 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sum_bern]
      _ = ∑ x : C, P t h x := by simp
      _ = 1 := hP_sum t h
  have hκ_sum' : ∀ t h, ∑ τ : C × Bool, κ t h τ = 1 := hκ_sum
  have coinLaw_eq : ∀ h : Fin n → C × Bool, coinLaw pt P A n h = ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) := by
    intro h
    dsimp [coinLaw, κ, ptHist]
    refine Finset.prod_congr rfl fun s _ => ?_
    rfl
  refine ⟨?_, ?_⟩
  · intro h
    rw [coinLaw_eq h]
    refine Finset.prod_nonneg fun s _ => ?_
    dsimp [κ]
    have hP_nonneg_s := hP_nonneg s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1
    have hbern_nonneg : 0 ≤ bern (A s (fun i : Fin s => (pt (h (Fin.castLE s.2.le i)).1, (h (Fin.castLE s.2.le i)).2)) (pt (h s).1)) (h s).2 := by
      have hA_range_s := hA_range s (by
        have : s.1 < n := s.2
        exact this
      ) (fun i : Fin s => (pt (h (Fin.castLE s.2.le i)).1, (h (Fin.castLE s.2.le i)).2)) ((h s).1)
      exact nonneg_bern _ hA_range_s.1 hA_range_s.2 _
    nlinarith
  · calc
      ∑ h : Fin n → C × Bool, coinLaw pt P A n h
          = ∑ h : Fin n → C × Bool, ∏ s : Fin n, κ s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [coinLaw_eq h]
      _ = 1 := by
        simpa using AdversarialBco.sum_prod_policy κ hκ_sum' n

theorem ex_coinReg_of_pseudo {d : ℕ} {C : Type*} [Fintype C] (K : Set (E d)) (hK : K.Nonempty) (pt : C → E d)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (f : ℕ → E d → ℝ) (n : ℕ)
    (hsum : ∑ h, coinLaw pt P (fun t _ => f t) n h = 1) (B : ℝ)
    (hB : ∀ x ∈ K, pseudoReg pt P (fun t _ => f t) n x ≤ B) : coinReg K pt P f n ≤ B := by
  set W := fun (h : Fin n → C × Bool) => coinLaw pt P (fun t _ => f t) n h with hW
  set E := ∑ h : Fin n → C × Bool, W h * (∑ t : Fin n, f t (pt (h t).1)) with hE
  have h_sumW : ∑ h : Fin n → C × Bool, W h = 1 := hsum
  have h_pseudo_eq : ∀ x, pseudoReg pt P (fun t _ => f t) n x = E - (∑ t : Fin n, f t x) := by
    intro x
    dsimp [pseudoReg]
    calc
      ∑ h : Fin n → C × Bool, coinLaw pt P (fun t _ => f t) n h *
          ∑ t : Fin n, (f t (pt (h t).1) - f t x)
          = ∑ h : Fin n → C × Bool, (coinLaw pt P (fun t _ => f t) n h *
              ∑ t : Fin n, f t (pt (h t).1) - coinLaw pt P (fun t _ => f t) n h *
              ∑ t : Fin n, f t x) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_sub_distrib, mul_sub]
      _ = (∑ h : Fin n → C × Bool, coinLaw pt P (fun t _ => f t) n h *
              ∑ t : Fin n, f t (pt (h t).1)) -
          (∑ h : Fin n → C × Bool, coinLaw pt P (fun t _ => f t) n h *
              ∑ t : Fin n, f t x) := by
        rw [Finset.sum_sub_distrib]
      _ = E - (∑ h : Fin n → C × Bool, coinLaw pt P (fun t _ => f t) n h) *
              (∑ t : Fin n, f t x) := by
        simp [W, hE, Finset.sum_mul]
      _ = E - 1 * (∑ t : Fin n, f t x) := by rw [hsum]
      _ = E - (∑ t : Fin n, f t x) := by ring
  have h_coinReg_eq : coinReg K pt P f n = E - sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) := by
    dsimp [coinReg, W, E]
  have h_bound : ∀ x ∈ K, E - B ≤ ∑ t ∈ Finset.range n, f t x := by
    intro x hx
    have hpx := hB x hx
    rw [h_pseudo_eq x] at hpx
    have h_fin_sum : (∑ t : Fin n, f t x) = ∑ t ∈ Finset.range n, f t x :=
      Fin.sum_univ_eq_sum_range (fun t => f t x) n
    rw [h_fin_sum] at hpx
    linarith
  have h_image_nonempty : ((fun x => ∑ t ∈ Finset.range n, f t x) '' K).Nonempty := by
    apply Set.Nonempty.image
    exact hK
  have h_lower_bound : ∀ y, y ∈ ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) → E - B ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_bound x hx
  have h_sInf : E - B ≤ sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) :=
    le_csInf h_image_nonempty h_lower_bound
  rw [h_coinReg_eq]
  linarith

theorem ex_pseudo_le_n {d : ℕ} {C : Type*} [Fintype C] (K : Set (E d)) (pt : C → E d) (hpt : ∀ c, pt c ∈ K)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (hP : ∀ t h, P t h ∈ probVecs C)
    (A : (t : ℕ) → (Fin t → E d × Bool) → E d → ℝ) (n : ℕ) (hA : A ∈ AdaptAdv K n) (x : E d) (hx : x ∈ K) :
    pseudoReg pt P A n x ≤ n := by
  obtain ⟨h0, h1⟩ := ex_coinLaw_sum pt P hP A n fun t ht χ c => (hA t ht χ).2 _ (hpt c)
  have hterm : ∀ h : Fin n → C × Bool, ∑ t : Fin n, (A t (ptHist pt h t) (pt (h t).1) - A t (ptHist pt h t) x) ≤
      n := by
    intro h
    calc ∑ t : Fin n, (A t (ptHist pt h t) (pt (h t).1) - A t (ptHist pt h t) x) ≤ ∑ _t : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => by
            have ha := (hA t t.2 (ptHist pt h t)).2 _ (hpt (h t).1)
            have hb := (hA t t.2 (ptHist pt h t)).2 x hx
            linarith [ha.2, hb.1]
      _ = n := by simp
  unfold pseudoReg
  calc ∑ h, coinLaw pt P A n h * ∑ t : Fin n, (A t (ptHist pt h t) (pt (h t).1) - A t (ptHist pt h t) x)
      ≤ ∑ h, coinLaw pt P A n h * n := Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hterm h) (h0 h)
    _ = n := by rw [← Finset.sum_mul, h1, one_mul]

/-! ## Constants -/

theorem ex_params (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (D : ℝ) (hD : 2 ≤ D) (β ε : ℝ)
    (hβ : β = 1200000000 * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n)) (hε : ε = 1 / (n ^ 2 * √(2 * β))) :
    2 ≤ β ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧ ε ≤ D := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hDpos : (0 : ℝ) < D := by linarith
  have h_nonneg_n : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have h_nonneg_d : (0 : ℝ) ≤ (d : ℝ) := by linarith
  have h_nonneg_D : (0 : ℝ) ≤ D := by linarith
  -- n * d * D ≥ 4
  have hndD_ge_four : (4 : ℝ) ≤ (n : ℝ) * (d : ℝ) * D := by
    calc
      (4 : ℝ) = (2 : ℝ) * (1 : ℝ) * (2 : ℝ) := by norm_num
      _ ≤ (n : ℝ) * (d : ℝ) * D := by
        have h1 : (2 : ℝ) * (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) :=
          mul_le_mul hn' hd' (by norm_num) h_nonneg_n
        nlinarith
  -- 2 * n ≥ 4
  have h2n_ge_four : (4 : ℝ) ≤ (2 : ℝ) * (n : ℝ) := by
    nlinarith
  -- log(n*d*D) ≥ 1
  have hlog1_ge_one : (1 : ℝ) ≤ Real.log ((n : ℝ) * (d : ℝ) * D) := by
    have hpos : (0 : ℝ) < (n : ℝ) * (d : ℝ) * D := by
      have : (0 : ℝ) < (2 : ℝ) * (1 : ℝ) * (2 : ℝ) := by norm_num
      linarith
    have h_exp_lt : Real.exp 1 < (n : ℝ) * (d : ℝ) * D := by
      have h_exp_lt_three : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      nlinarith
    have h_log_le : Real.log (Real.exp 1) ≤ Real.log ((n : ℝ) * (d : ℝ) * D) :=
      Real.log_le_log (by positivity) h_exp_lt.le
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ ≤ Real.log ((n : ℝ) * (d : ℝ) * D) := h_log_le
  -- log(2*n) ≥ 1
  have hlog2_ge_one : (1 : ℝ) ≤ Real.log ((2 : ℝ) * (n : ℝ)) := by
    have hpos : (0 : ℝ) < (2 : ℝ) * (n : ℝ) := by nlinarith
    have h_exp_lt : Real.exp 1 < (2 : ℝ) * (n : ℝ) := by
      have h_exp_lt_three : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
      nlinarith
    have h_log_le : Real.log (Real.exp 1) ≤ Real.log ((2 : ℝ) * (n : ℝ)) :=
      Real.log_le_log (by positivity) h_exp_lt.le
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp 1]
      _ ≤ Real.log ((2 : ℝ) * (n : ℝ)) := h_log_le
  -- 2 ≤ β
  have hβ_ge_two : (2 : ℝ) ≤ β := by
    rw [hβ]
    have hd_sq_ge_one : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
      nlinarith
    have h_nonneg_d_sq : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    have h_nonneg_log1 : (0 : ℝ) ≤ Real.log ((n : ℝ) * (d : ℝ) * D) := by linarith
    have h_nonneg_log2 : (0 : ℝ) ≤ Real.log ((2 : ℝ) * (n : ℝ)) := by linarith
    have h_nonneg_1200000000 : (0 : ℝ) ≤ (1200000000 : ℝ) := by norm_num
    calc
      (2 : ℝ) ≤ (1200000000 : ℝ) * (1 : ℝ) * (1 : ℝ) * (1 : ℝ) := by
        have : (2 : ℝ) ≤ (1200000000 : ℝ) := by norm_num
        nlinarith
      _ ≤ (1200000000 : ℝ) * (d : ℝ) ^ 2 * Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log ((2 : ℝ) * (n : ℝ)) := by
        gcongr
  -- 0 < ε
  have hε_pos : (0 : ℝ) < ε := by
    rw [hε]
    have h_denom_pos : (0 : ℝ) < (n : ℝ) ^ 2 * Real.sqrt (2 * β) := by
      have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h_sqrt_pos : (0 : ℝ) < Real.sqrt (2 * β) :=
        Real.sqrt_pos.mpr (by nlinarith)
      positivity
    exact div_pos (by norm_num) h_denom_pos
  -- ε ≤ 1/4
  have hε_le_quarter : ε ≤ 1 / 4 := by
    rw [hε]
    have h_denom_ge_eight : (8 : ℝ) ≤ (n : ℝ) ^ 2 * Real.sqrt (2 * β) := by
      have hn_sq_ge_four : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
        nlinarith
      have h_sqrt_ge_two : (2 : ℝ) ≤ Real.sqrt (2 * β) := by
        have h_sq : (2 : ℝ) ^ 2 ≤ 2 * β := by nlinarith
        exact Real.le_sqrt_of_sq_le h_sq
      nlinarith
    have h_one_div_denom_le_eighth : (1 : ℝ) / ((n : ℝ) ^ 2 * Real.sqrt (2 * β)) ≤ (1 : ℝ) / 8 :=
      one_div_le_one_div_of_le (by norm_num) h_denom_ge_eight
    have h_eighth_le_quarter : (1 : ℝ) / 8 ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by norm_num)
    linarith
  -- ε ≤ D
  have hε_le_D : ε ≤ D := by
    have h_quarter_le_D : (1 : ℝ) / 4 ≤ D := by
      have : (1 : ℝ) / 4 ≤ 2 := by norm_num
      linarith
    linarith
  exact And.intro hβ_ge_two (And.intro hε_pos (And.intro hε_le_quarter hε_le_D))

theorem ex_sqrt_id (lm β n η : ℝ) (hlm : 0 < lm) (hβ : 0 < β) (hn : 0 < n) (hη : η = √(8 * lm / (n * β))) :
    lm / η + n * (η * β / 8) = √(β * n * lm / 2) := by
  set s := √(β * n * lm / 2) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = β * n * lm / 2 := Real.sq_sqrt (by positivity)
  have hη' : η = 2 * lm / s := by
    rw [hη, show 8 * lm / (n * β) = (2 * lm / s) ^ 2 by
      rw [div_pow, hs2]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hη']
  field_simp
  nlinarith [hs2]

theorem ex_const (n β ε : ℝ) (hn : 2 ≤ n) (hβ : 2 ≤ β) (hε : ε = 1 / (n ^ 2 * √(2 * β))) :
    1 + n * n * ε + n * ((1 + 2 * n * ε) * (1 / n) + n * ε * (1 + √β) + 1 / n) ≤ 671 / 100 := by
  have hnpos : 0 < n := by linarith
  have hβpos : 0 < β := by linarith
  have h2βpos : 0 < 2 * β := by nlinarith
  set r := √(2 * β) with hr_def
  have hrpos : 0 < r := Real.sqrt_pos.mpr h2βpos
  have hr_ge_two : 2 ≤ r := by
    have h4le2β : (4 : ℝ) ≤ 2 * β := by nlinarith
    calc
      (2 : ℝ) = √(4 : ℝ) := by norm_num
      _ ≤ √(2 * β) := Real.sqrt_le_sqrt h4le2β
      _ = r := rfl
  have hsqrtβ_div_r : √β / r = 1 / √2 := by
    calc
      √β / r = √β / √(2 * β) := rfl
      _ = √β / (√2 * √β) := by rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) from by norm_num)]
      _ = 1 / √2 := by
        field_simp [show √β ≠ 0 from by
          have hpos : 0 < √β := Real.sqrt_pos.mpr hβpos
          linarith]
  have h_expr : 1 + n * n * ε + n * ((1 + 2 * n * ε) * (1 / n) + n * ε * (1 + √β) + 1 / n) = 3 + 2 * n * ε + n ^ 2 * ε * (2 + √β) := by
    field_simp [hnpos.ne.symm]
    ring
  rw [h_expr]
  rw [hε]
  have h_simp : 3 + 2 * n * (1 / (n ^ 2 * r)) + n ^ 2 * (1 / (n ^ 2 * r)) * (2 + √β) = 3 + 2 / (n * r) + (2 + √β) / r := by
    field_simp [hnpos.ne.symm, hrpos.ne.symm]
  rw [h_simp]
  have h_split : (2 + √β) / r = 2 / r + √β / r := by ring
  rw [h_split]
  rw [hsqrtβ_div_r]
  have h_bound1 : 2 / (n * r) ≤ 1/2 := by
    have h_denom_le : (4 : ℝ) ≤ n * r := by nlinarith
    calc
      2 / (n * r) ≤ 2 / (4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h_denom_le
      _ = 1/2 := by norm_num
  have h_bound2 : 2 / r ≤ 1 := by
    calc
      2 / r ≤ 2 / (2 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr_ge_two
      _ = 1 := by norm_num
  have h_bound3 : 1 / √2 ≤ 1 := by
    have hpos_sqrt2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
    have h_sqrt2_ge_one : 1 ≤ √2 := by
      calc
        1 = √(1 : ℝ) := by norm_num
        _ ≤ √2 := Real.sqrt_le_sqrt (by norm_num)
    exact (div_le_one hpos_sqrt2).mpr h_sqrt2_ge_one
  have h_total : 3 + 2 / (n * r) + 2 / r + 1 / √2 ≤ 3 + (1/2 : ℝ) + 1 + 1 := by
    nlinarith
  have h_final : 3 + (1/2 : ℝ) + 1 + 1 ≤ 671/100 := by
    norm_num
  linarith

theorem ex_log_m (m d : ℕ) (X : ℝ) (hm : 1 ≤ m) (hX : (m : ℝ) ≤ X ^ d) : Real.log m ≤ d * Real.log X := by
  have hm_pos : 0 < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hX_pos : 0 < X ^ d := by linarith
  calc
    Real.log (m : ℝ) ≤ Real.log (X ^ d) := Real.log_le_log hm_pos hX
    _ = (d : ℝ) * Real.log X := by rw [Real.log_pow]
    _ = d * Real.log X := by simp

theorem ex_CX_beta (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hdn : d < n) (D : ℝ) (hD : 2 ≤ D) :
    0 < Real.log (n * d * D) * Real.log (2 * n) ∧
      Real.log (n * d * D) * Real.log (2 * n) ≤ 4 * Real.log (n * D) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnpos : 0 < (n : ℝ) := by linarith
  have hdpos : 0 < (d : ℝ) := by linarith
  have hDpos : 0 < D := by linarith
  have hD_one : 1 ≤ D := by linarith
  have hpos1 : 1 < (n : ℝ) * (d : ℝ) * D := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) * (d : ℝ) * D := by
      have : (2 : ℝ) * (1 : ℝ) * (2 : ℝ) ≤ (n : ℝ) * (d : ℝ) * D := by
        exact mul_le_mul (mul_le_mul hn2 hd1 (by norm_num) (by linarith)) hD (by norm_num) (by nlinarith)
      calc
        (4 : ℝ) = (2 : ℝ) * (1 : ℝ) * (2 : ℝ) := by norm_num
        _ ≤ (n : ℝ) * (d : ℝ) * D := this
    linarith
  have hpos2 : 1 < 2 * (n : ℝ) := by
    have h4 : (4 : ℝ) ≤ 2 * (n : ℝ) := by
      nlinarith
    linarith
  have hlog1 : 0 < Real.log ((n : ℝ) * (d : ℝ) * D) := Real.log_pos hpos1
  have hlog2 : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos hpos2
  have hprod_pos : 0 < Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) :=
    mul_pos hlog1 hlog2
  have hlog_nD_nonneg : 0 ≤ Real.log ((n : ℝ) * D) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ (n : ℝ) * D := by
      nlinarith
    exact this
  have hineq1 : Real.log ((n : ℝ) * (d : ℝ) * D) ≤ 2 * Real.log ((n : ℝ) * D) := by
    have h1 : (n : ℝ) * (d : ℝ) * D ≤ ((n : ℝ) * D) ^ 2 := by
      have hd_le_n : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hdn)
      calc
        (n : ℝ) * (d : ℝ) * D ≤ (n : ℝ) * (n : ℝ) * D := by
          gcongr
        _ = (n : ℝ) ^ 2 * D := by ring
        _ ≤ (n : ℝ) ^ 2 * (D ^ 2) := by
          have : D ≤ D ^ 2 := by
            nlinarith
          gcongr
        _ = ((n : ℝ) * D) ^ 2 := by ring
    have hpos_arg : 0 < (n : ℝ) * (d : ℝ) * D := by nlinarith
    have hlog_le : Real.log ((n : ℝ) * (d : ℝ) * D) ≤ Real.log (((n : ℝ) * D) ^ 2) :=
      Real.log_le_log hpos_arg h1
    calc
      Real.log ((n : ℝ) * (d : ℝ) * D) ≤ Real.log (((n : ℝ) * D) ^ 2) := hlog_le
      _ = 2 * Real.log ((n : ℝ) * D) := by
        rw [Real.log_pow, Nat.cast_ofNat]
  have hineq2 : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log ((n : ℝ) * D) := by
    have h2 : 2 * (n : ℝ) ≤ ((n : ℝ) * D) ^ 2 := by
      calc
        2 * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
          have : (2 : ℝ) ≤ (n : ℝ) := hn2
          nlinarith
        _ = (n : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) ^ 2 * (D ^ 2) := by
          have : (1 : ℝ) ≤ D ^ 2 := by
            nlinarith
          nlinarith
        _ = ((n : ℝ) * D) ^ 2 := by ring
    have hpos_arg : 0 < 2 * (n : ℝ) := by nlinarith
    have hlog_le : Real.log (2 * (n : ℝ)) ≤ Real.log (((n : ℝ) * D) ^ 2) :=
      Real.log_le_log hpos_arg h2
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log (((n : ℝ) * D) ^ 2) := hlog_le
      _ = 2 * Real.log ((n : ℝ) * D) := by
        rw [Real.log_pow, Nat.cast_ofNat]
  have hprod_le : Real.log ((n : ℝ) * (d : ℝ) * D) * Real.log (2 * (n : ℝ)) ≤
      (2 * Real.log ((n : ℝ) * D)) * (2 * Real.log ((n : ℝ) * D)) :=
    mul_le_mul hineq1 hineq2 hlog2.le (by nlinarith)
  have hfinal : (2 * Real.log ((n : ℝ) * D)) * (2 * Real.log ((n : ℝ) * D)) =
      4 * Real.log ((n : ℝ) * D) ^ 2 := by ring
  constructor
  · simpa using hprod_pos
  · simpa [hfinal] using hprod_le

theorem ex_CX_log (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hdn : d < n) (D : ℝ) (hD : 2 ≤ D) (β : ℝ) (hβ0 : 2 ≤ β)
    (hβ : β ≤ 4 * 1200000000 * d ^ 2 * Real.log (n * D) ^ 2) :
    0 ≤ Real.log (5 * n ^ 2 * √(2 * β) * D) ∧ Real.log (5 * n ^ 2 * √(2 * β) * D) ≤ 27 / 2 * Real.log (n * D) := by
  -- Precompute large constants
  have h2pow19 : (2 : ℝ) ^ (19 : ℕ) = (524288 : ℝ) := by norm_num
  have h2pow38 : ((2 : ℝ) ^ (19 : ℕ)) ^ 2 = (274877906944 : ℝ) := by norm_num
  -- Cast hypotheses to ℝ
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd_real : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdn_real : (d : ℝ) < (n : ℝ) := by exact_mod_cast hdn
  have hdpos : 0 ≤ (d : ℝ) := by linarith
  have hnpos : 0 < (n : ℝ) := by linarith
  have hDpos : 0 < D := by linarith
  have hβpos : 0 < β := by linarith
  -- n * D ≥ 4
  have hnD_ge4 : (4 : ℝ) ≤ (n : ℝ) * D := by
    have := mul_le_mul hn_real hD (by norm_num) hnpos.le
    linarith
  set L := Real.log ((n : ℝ) * D) with hLdef
  set X := (5 : ℝ) * ((n : ℝ) ^ 2) * Real.sqrt (2 * β) * D with hXdef
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.log_pos (by linarith)
  -- Lower bound: X ≥ 1, so log X ≥ 0
  have hsqrt2β_ge_2 : (2 : ℝ) ≤ Real.sqrt (2 * β) := by
    have h4le2β : (4 : ℝ) ≤ 2 * β := by linarith
    calc
      (2 : ℝ) = Real.sqrt (4 : ℝ) := by norm_num
      _ ≤ Real.sqrt (2 * β) := Real.sqrt_le_sqrt h4le2β
  have hX_ge_1 : (1 : ℝ) ≤ X := by
    rw [hXdef]
    have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
      (by linarith)
  have h_lower : 0 ≤ Real.log X :=
    Real.log_nonneg hX_ge_1
  -- Upper bound
  -- Step 1: 2*β ≤ 8*1200000000*d^2*L^2
  have h2β_le : 2 * β ≤ (8 : ℝ) * (1200000000 : ℝ) * ((d : ℝ) ^ 2) * (L ^ 2) := by
    linarith
  have h_nonneg_8_1200000000 : 0 ≤ (8 : ℝ) * (1200000000 : ℝ) := by norm_num
  -- Step 2: √(2*β) ≤ √(8*1200000000) * d * L
  have h_sqrt_bound : Real.sqrt (2 * β) ≤ Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (d : ℝ) * L := by
    calc
      Real.sqrt (2 * β) ≤ Real.sqrt ((8 : ℝ) * (1200000000 : ℝ) * ((d : ℝ) ^ 2) * (L ^ 2)) :=
        Real.sqrt_le_sqrt h2β_le
      _ = Real.sqrt (((8 : ℝ) * (1200000000 : ℝ)) * (((d : ℝ) ^ 2) * (L ^ 2))) := by ring
      _ = Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * Real.sqrt (((d : ℝ) ^ 2) * (L ^ 2)) := by
        rw [Real.sqrt_mul h_nonneg_8_1200000000]
      _ = Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (Real.sqrt ((d : ℝ) ^ 2) * Real.sqrt (L ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg (d : ℝ))]
      _ = Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * ((d : ℝ) * L) := by
        rw [Real.sqrt_sq hdpos, Real.sqrt_sq (by linarith : 0 ≤ L)]
      _ = Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (d : ℝ) * L := by ring
  -- Step 3: 5 * √(8*1200000000) ≤ 2^19
  have h_5_sqrt_le : (5 : ℝ) * Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) ≤ (2 : ℝ) ^ (19 : ℕ) := by
    have h_nonneg_left : 0 ≤ (5 : ℝ) * Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) := by positivity
    have h_nonneg_right : 0 ≤ (2 : ℝ) ^ (19 : ℕ) := by norm_num
    have h_sq : ((5 : ℝ) * Real.sqrt ((8 : ℝ) * (1200000000 : ℝ))) ^ 2 ≤ ((2 : ℝ) ^ (19 : ℕ)) ^ 2 := by
      calc
        ((5 : ℝ) * Real.sqrt ((8 : ℝ) * (1200000000 : ℝ))) ^ 2 =
            (25 : ℝ) * ((Real.sqrt ((8 : ℝ) * (1200000000 : ℝ))) ^ 2) := by ring
        _ = (25 : ℝ) * ((8 : ℝ) * (1200000000 : ℝ)) := by
          rw [Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ) * (1200000000 : ℝ))]
        _ = (240000000000 : ℝ) := by norm_num
        _ ≤ (274877906944 : ℝ) := by norm_num
        _ = ((2 : ℝ) ^ (19 : ℕ)) ^ 2 := by rw [h2pow38]
    exact (sq_le_sq₀ h_nonneg_left h_nonneg_right).mp h_sq
  -- X ≤ 2^19 * n^2 * d * D * L
  have hX_le : X ≤ (2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L := by
    rw [hXdef]
    have h_nonneg_a : 0 ≤ (5 : ℝ) * ((n : ℝ) ^ 2) := by positivity
    have h_nonneg_D : 0 ≤ D := by linarith
    have h1 : (5 : ℝ) * ((n : ℝ) ^ 2) * Real.sqrt (2 * β) ≤
        (5 : ℝ) * ((n : ℝ) ^ 2) * (Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (d : ℝ) * L) := by
      apply mul_le_mul_of_nonneg_left h_sqrt_bound h_nonneg_a
    have h2 : (5 : ℝ) * ((n : ℝ) ^ 2) * Real.sqrt (2 * β) * D ≤
        (5 : ℝ) * ((n : ℝ) ^ 2) * (Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (d : ℝ) * L) * D := by
      apply mul_le_mul_of_nonneg_right h1 h_nonneg_D
    calc
      (5 : ℝ) * ((n : ℝ) ^ 2) * Real.sqrt (2 * β) * D ≤
          (5 : ℝ) * ((n : ℝ) ^ 2) * (Real.sqrt ((8 : ℝ) * (1200000000 : ℝ)) * (d : ℝ) * L) * D := h2
      _ = ((5 : ℝ) * Real.sqrt ((8 : ℝ) * (1200000000 : ℝ))) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L := by ring
      _ ≤ (2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L := by
        gcongr
  -- Take logs
  have hpos_X : 0 < X := by
    rw [hXdef]
    positivity
  have hpos_rest : 0 < (2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L := by positivity
  have h_log_le : Real.log X ≤ Real.log ((2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L) :=
    Real.log_le_log hpos_X hX_le
  -- Expand log of product
  have h_log_prod : Real.log ((2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L) =
      Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d : ℝ) + Real.log D + Real.log L := by
    have h2 : (2 : ℝ) ^ (19 : ℕ) ≠ 0 := by norm_num
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := by positivity
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hD0 : D ≠ 0 := by linarith
    have hL0 : L ≠ 0 := by linarith
    have h_rest : ((n : ℝ) ^ 2) * (d : ℝ) * D * L ≠ 0 := by positivity
    have h_rest2 : (d : ℝ) * D * L ≠ 0 := by positivity
    have h_rest3 : D * L ≠ 0 := by positivity
    calc
      Real.log ((2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L) =
          Real.log ((2 : ℝ) ^ (19 : ℕ) * (((n : ℝ) ^ 2) * (d : ℝ) * D * L)) := by ring
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log (((n : ℝ) ^ 2) * (d : ℝ) * D * L) :=
        Real.log_mul h2 h_rest
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2 * ((d : ℝ) * D * L)) := by ring
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + (Real.log ((n : ℝ) ^ 2) + Real.log ((d : ℝ) * D * L)) := by
        rw [Real.log_mul hn2 h_rest2]
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log ((d : ℝ) * D * L) := by ring
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d * (D * L)) := by ring
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + (Real.log (d : ℝ) + Real.log (D * L)) := by
        rw [Real.log_mul hd0 h_rest3]
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d : ℝ) + Real.log (D * L) := by ring
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d : ℝ) + (Real.log D + Real.log L) := by
        rw [Real.log_mul hD0 hL0]
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d : ℝ) + Real.log D + Real.log L := by ring
  have h_log_pow2 : Real.log ((2 : ℝ) ^ (19 : ℕ)) = (19 : ℝ) * Real.log 2 := by
    rw [Real.log_pow, Nat.cast_ofNat]
  have h_log_pown : Real.log ((n : ℝ) ^ 2) = (2 : ℝ) * Real.log (n : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  -- log d ≤ log n (since d < n)
  have h_log_d_le_log_n : Real.log (d : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) (le_of_lt hdn_real)
  -- log D ≥ 0 (since D ≥ 2)
  have h_log_D_nonneg : 0 ≤ Real.log D :=
    Real.log_nonneg (by linarith)
  -- 2*log n + log d + log D ≤ 3*L
  have h_sum_le_3L : (2 : ℝ) * Real.log (n : ℝ) + Real.log (d : ℝ) + Real.log D ≤ 3 * L := by
    have h_log_n_add_log_D : Real.log (n : ℝ) + Real.log D = L := by
      rw [hLdef, Real.log_mul (by linarith : (n : ℝ) ≠ 0) (by linarith : D ≠ 0)]
    linarith
  -- log L ≤ L
  have h_log_L_le_L : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  -- 19*log 2 = (19/2)*log 4 ≤ (19/2)*L
  have h_19log2_le : (19 : ℝ) * Real.log 2 ≤ (19/2 : ℝ) * L := by
    have h_log4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
        _ = (2 : ℝ) * Real.log 2 := by rw [Real.log_pow, Nat.cast_ofNat]
    have h_log4_le_L : Real.log (4 : ℝ) ≤ L := by
      rw [hLdef]
      refine Real.log_le_log (by norm_num) hnD_ge4
    linarith
  -- Put it all together
  have h_upper : Real.log X ≤ 27 / 2 * Real.log ((n : ℝ) * D) := by
    calc
      Real.log X ≤ Real.log ((2 : ℝ) ^ (19 : ℕ) * ((n : ℝ) ^ 2) * (d : ℝ) * D * L) := h_log_le
      _ = Real.log ((2 : ℝ) ^ (19 : ℕ)) + Real.log ((n : ℝ) ^ 2) + Real.log (d : ℝ) + Real.log D + Real.log L := h_log_prod
      _ = ((19 : ℝ) * Real.log 2) + ((2 : ℝ) * Real.log (n : ℝ)) + Real.log (d : ℝ) + Real.log D + Real.log L := by
        rw [h_log_pow2, h_log_pown]
      _ = (19 : ℝ) * Real.log 2 + ((2 : ℝ) * Real.log (n : ℝ) + Real.log (d : ℝ) + Real.log D) + Real.log L := by ring
      _ ≤ (19 : ℝ) * Real.log 2 + (3 * L) + Real.log L := by linarith
      _ ≤ (19/2 : ℝ) * L + (3 * L) + L := by linarith
      _ = (27/2 : ℝ) * L := by ring
      _ = 27 / 2 * Real.log ((n : ℝ) * D) := by rw [hLdef]
  exact And.intro h_lower h_upper

theorem ex_CX_final (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (L β Λ : ℝ) (hL : Real.log 4 ≤ L) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 4 * 1200000000 * d ^ 2 * L ^ 2) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 27 / 2 * L) :
    671 / 100 + √(β * n * d * Λ / 2) ≤ 190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * L ^ (3 / 2 : ℝ) := by
  -- L ≥ 1 because log 4 > 1 (since exp 1 < 4)
  have hL1 : 1 ≤ L := by
    have hlog4_gt_one : 1 < Real.log 4 := by
      by_contra! hle
      have h_exp_ge_4 : (4 : ℝ) ≤ Real.exp 1 :=
        ((Real.log_le_iff_le_exp (by norm_num : 0 < (4 : ℝ))).mp hle)
      have hexp_lt_4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_three]
      linarith
    linarith
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hn1 : 1 ≤ (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := by linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hd_pos : 0 < (d : ℝ) := by linarith
  have hL_pos : 0 < L := by linarith
  set M := (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * L ^ (3 / 2 : ℝ) with hM
  have hM_nonneg : 0 ≤ M := by
    have hd_rpow_nonneg : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hd_nonneg _
    have hsqrt_n_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hL_rpow_nonneg : 0 ≤ L ^ (3 / 2 : ℝ) := Real.rpow_nonneg hL_nonneg _
    positivity
  have hM1 : 1 ≤ M := by
    have hd_rpow_ge_one : 1 ≤ (d : ℝ) ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow hd1 (by norm_num : 0 ≤ (3/2 : ℝ))
    have hsqrt_n_ge_one : 1 ≤ √(n : ℝ) := by
      calc
        1 = √(1 : ℝ) := by norm_num
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt hn1
    have hL_rpow_ge_one : 1 ≤ L ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow hL1 (by norm_num : 0 ≤ (3/2 : ℝ))
    have h_nonneg_rpow : 0 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hd_nonneg _
    have h_nonneg_sqrt : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have h_nonneg_Lrpow : 0 ≤ L ^ (3 / 2 : ℝ) := Real.rpow_nonneg hL_nonneg _
    have h_first : 1 * 1 ≤ (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) :=
      mul_le_mul hd_rpow_ge_one hsqrt_n_ge_one (by norm_num) h_nonneg_rpow
    have h_second : (1 * 1) * 1 ≤ ((d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ)) * L ^ (3 / 2 : ℝ) :=
      mul_le_mul h_first hL_rpow_ge_one (by norm_num) (mul_nonneg h_nonneg_rpow h_nonneg_sqrt)
    simpa [M, mul_assoc] using h_second
  have hM_sq_eq : M ^ 2 = (d : ℝ) ^ 3 * (n : ℝ) * L ^ 3 := by
    calc
      M ^ 2 = ((d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * L ^ (3 / 2 : ℝ)) ^ 2 := rfl
      _ = ((d : ℝ) ^ (3 / 2 : ℝ)) ^ 2 * (√(n : ℝ)) ^ 2 * (L ^ (3 / 2 : ℝ)) ^ 2 := by ring
      _ = ((d : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℝ) * ((n : ℝ) ^ (1/2 : ℝ)) ^ (2 : ℝ) * (L ^ (3 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [show ((d : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = ((d : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℝ) by simp,
          show (√(n : ℝ)) ^ 2 = ((n : ℝ) ^ (1/2 : ℝ)) ^ (2 : ℝ) by
            rw [Real.sqrt_eq_rpow]
            simp,
          show (L ^ (3 / 2 : ℝ)) ^ 2 = (L ^ (3 / 2 : ℝ)) ^ (2 : ℝ) by simp]
      _ = ((d : ℝ) ^ ((3 / 2 : ℝ) * (2 : ℝ))) * ((n : ℝ) ^ ((1/2 : ℝ) * (2 : ℝ))) * ((L : ℝ) ^ ((3 / 2 : ℝ) * (2 : ℝ))) := by
        rw [← Real.rpow_mul hd_nonneg (3/2) 2]
        rw [← Real.rpow_mul hn_nonneg (1/2) 2]
        rw [← Real.rpow_mul hL_nonneg (3/2) 2]
      _ = (d : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (1 : ℝ) * (L : ℝ) ^ (3 : ℝ) := by
        have h_exp1 : ((3 : ℝ) / 2) * (2 : ℝ) = (3 : ℝ) := by ring
        simp [h_exp1]
      _ = (d : ℝ) ^ 3 * (n : ℝ) * L ^ 3 := by simp
  have h_bound : β * (n : ℝ) * (d : ℝ) * Λ / 2 ≤ (180000 : ℝ)^2 * ((d : ℝ) ^ 3 * (n : ℝ) * L ^ 3) := by
    have hβ' : β ≤ 4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2 := by
      simpa [sq] using hβ
    have h_prod : β * (n : ℝ) * (d : ℝ) * Λ ≤
        (4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ) * (d : ℝ) * ((27 / 2) * L) := by
      have h_nonneg_n : 0 ≤ (n : ℝ) := hn_nonneg
      have h_nonneg_d : 0 ≤ (d : ℝ) := hd_nonneg
      have h1 : β * (n : ℝ) ≤ (4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hβ' h_nonneg_n
      have h2 : (β * (n : ℝ)) * (d : ℝ) ≤ ((4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right h1 h_nonneg_d
      have hRHS_nonneg : 0 ≤ ((4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ)) * (d : ℝ) := by
        positivity
      have h3 : ((β * (n : ℝ)) * (d : ℝ)) * Λ ≤ (((4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ)) * (d : ℝ)) * ((27 / 2) * L) :=
        mul_le_mul h2 hΛ hΛ0 hRHS_nonneg
      -- Now rewrite both sides to the expected form
      simpa [mul_assoc] using h3
    have h_const : (4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ) * (d : ℝ) * ((27 / 2) * L) / 2 =
        (180000 : ℝ)^2 * ((d : ℝ) ^ 3 * (n : ℝ) * L ^ 3) := by
      ring
    have h_div : β * (n : ℝ) * (d : ℝ) * Λ / 2 ≤
        (4 * 1200000000 * ((d : ℝ) ^ 2) * L ^ 2) * (n : ℝ) * (d : ℝ) * ((27 / 2) * L) / 2 := by
      linarith
    rw [h_const] at h_div
    exact h_div
  have h_sqrt_ineq : √(β * (n : ℝ) * (d : ℝ) * Λ / 2) ≤ 180000 * M := by
    have h_arg_nonneg : 0 ≤ β * (n : ℝ) * (d : ℝ) * Λ / 2 := by positivity
    have h_sq_ineq : (√(β * (n : ℝ) * (d : ℝ) * Λ / 2)) ^ 2 ≤ (180000 * M) ^ 2 := by
      rw [Real.sq_sqrt h_arg_nonneg]
      calc
        β * (n : ℝ) * (d : ℝ) * Λ / 2 ≤ (180000 : ℝ)^2 * ((d : ℝ) ^ 3 * (n : ℝ) * L ^ 3) := h_bound
        _ = (180000 : ℝ)^2 * (M ^ 2) := by rw [hM_sq_eq]
        _ = (180000 * M) ^ 2 := by ring
    have h_nonneg_sqrt : 0 ≤ √(β * (n : ℝ) * (d : ℝ) * Λ / 2) := Real.sqrt_nonneg _
    have h_nonneg_180000M : 0 ≤ 180000 * M := by nlinarith
    nlinarith
  have h_first : 671 / 100 ≤ 10000 * M := by
    have h10000M : 10000 ≤ 10000 * M := by nlinarith
    have h671 : 671 / 100 ≤ 10000 := by norm_num
    nlinarith
  calc
    671 / 100 + √(β * n * d * Λ / 2) ≤ 10000 * M + 180000 * M := by nlinarith
    _ = 190000 * M := by ring
    _ = 190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * L ^ (3 / 2 : ℝ) := by rw [hM]; ring

/-- The order bound for `d < n`. -/
theorem ex_CX (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) (hdn : d < n) (D : ℝ) (hD : 2 ≤ D) (β : ℝ)
    (hβ : β = 1200000000 * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n)) :
    671 / 100 + √(β * n * d * Real.log (5 * n ^ 2 * √(2 * β) * D) / 2) ≤
      190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ) := by
  obtain ⟨hp, hle⟩ := ex_CX_beta d n hd hn hdn D hD
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hβle : β ≤ 4 * 1200000000 * d ^ 2 * Real.log (n * D) ^ 2 := by
    rw [hβ]
    have : (0 : ℝ) ≤ 1200000000 * d ^ 2 := by positivity
    calc 1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n)
        = 1200000000 * d ^ 2 * (Real.log (n * d * D) * Real.log (2 * n)) := by ring
      _ ≤ 1200000000 * d ^ 2 * (4 * Real.log (n * D) ^ 2) := mul_le_mul_of_nonneg_left hle this
      _ = 4 * 1200000000 * d ^ 2 * Real.log (n * D) ^ 2 := by ring
  have hβ2 : 2 ≤ β := (ex_params d n hd hn D hD β (1 / (n ^ 2 * √(2 * β))) hβ rfl).1
  obtain ⟨hΛ0, hΛ⟩ := ex_CX_log d n hd hn hdn D hD β hβ2 hβle
  have hL : Real.log 4 ≤ Real.log (n * D) := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.log_le_log (by norm_num) (by nlinarith)
  exact ex_CX_final d n hd hn _ β _ hL (by linarith) hβle hΛ0 hΛ

/-! ## Theorem 7.2 for the learner of Algorithm 7.1, adaptive form -/

/-- The restriction to the net of an admissible loss lies in `P_L` with `L = n` (`PL_of_adm` of `Lemmas.lean` for
any finite index type). -/
theorem ex_PL_of_adm {d : ℕ} {C : Type*} [Fintype C] (K : Set (E d)) (hK : Convex ℝ K) (n : ℕ) (hn : 1 ≤ n)
    (pt : C → E d) (hpt : ∀ i, pt i ∈ innerBody K n) (hne : (innerBody K n).Nonempty) (f : E d → ℝ)
    (hf : AdmLoss K f) : (fun i => f (pt i)) ∈ PL pt n := by
  set J := innerBody K n with hJ_def
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hpos : 0 ≤ 1 / (n : ℝ) := div_nonneg (by norm_num) hn_nonneg
  have hJ_sub_K : J ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hpos)
  have hJ_conv : Convex ℝ J := AdversarialBco.convex_inner K hK (1 / (n : ℝ))
  have hf_lip : LipschitzOnWith (n : NNReal) f J := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hbound : |f x - f y| ≤ (n : ℝ) * ‖x - y‖ :=
      AdversarialBco.abs_sub_le_inner K f hf.1 hf.2 n hn x y hx hy
    calc dist (f x) (f y) = |f x - f y| := Real.dist_eq _ _
      _ ≤ (n : ℝ) * ‖x - y‖ := hbound
      _ = ((n : NNReal) : ℝ) * dist x y := by simp [dist_eq_norm, NNReal.coe_natCast]
  obtain ⟨s, hs_norm, hs_sub⟩ := AdversarialBco.PL_of_convex pt J hne hpt (n : NNReal) f
    (hf.1.subset hJ_sub_K hJ_conv) hf_lip (fun x hx => hf.2 x (hJ_sub_K hx))
  exact ⟨fun i => hf.2 _ (hJ_sub_K (hpt i)), s, fun i => by simpa [NNReal.coe_natCast] using hs_norm i, hs_sub⟩

/-- The laws of Algorithm 7.1 are probability vectors. -/
theorem ex_exoKernel_prob {d : ℕ} {C : Type*} [Fintype C] [Nonempty C] (pt : C → E d) (L η tol : ℝ)
    (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) (hsol : IsSolver pt L η tol sol) (t : ℕ)
    (h : Fin t → C × Bool) : exoKernel η sol t h ∈ probVecs C := by
  have hq := AdversarialBco.ewQ_pos_sum η (fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1) t h
  rw [← ex_weights_eq] at hq
  exact (hsol _ hq.1 hq.2).1.1

theorem ex_pseudo_main {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsCompact K) (x0 : E d)
    (hx0 : Metric.closedBall x0 1 ⊆ K) (n : ℕ) (hn : 2 ≤ n) (C : Finset (E d)) (hCJ : ↑C ⊆ innerBody K n)
    (hCne : C.Nonempty) (ε : ℝ) (hε : 0 < ε) (hcov : ∀ x ∈ innerBody K n, ∃ c ∈ C, dist x c < ε)
    (α β η tol : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hη : 0 < η) (htol : 0 ≤ tol)
    (hH : HypH (innerBody K n) n 0 1 α β) (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ))
    (hsol : IsSolver (Subtype.val : C → E d) n η tol sol) (A : (t : ℕ) → (Fin t → E d × Bool) → E d → ℝ)
    (hA : A ∈ AdaptAdv K n) (x : E d) (hx : x ∈ K) :
    pseudoReg Subtype.val (exoKernel η sol) A n x ≤
      1 + n * n * ε + Real.log C.card / η + n * ((1 + 2 * n * ε) * α + n * ε * (1 + √β) + η * β / 8 + tol) := by
  classical
  have : Nonempty C := hCne.coe_sort
  set J := innerBody K n with hJdef
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hinv0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hJc : Convex ℝ J := AdversarialBco.convex_inner K hK _
  have hJm : MeasurableSet J := (AdversarialBco.isCompact_inner K hKc _ hinv0).isClosed.measurableSet
  have hJK : J ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hinv0)
  have hJne : J.Nonempty := by
    obtain ⟨c, hc⟩ := hCne
    exact ⟨c, hCJ hc⟩
  -- the nearest point map of the net
  obtain ⟨pr0, hpr0m, hpr0C, hpr0⟩ := AdversarialBco.exists_measurable_nearest C hCne
  let pr : E d → C := fun z => ⟨pr0 z, hpr0C z⟩
  have hprm : ∀ c : C, MeasurableSet (pr ⁻¹' {c}) := by
    intro c
    have hpre : pr ⁻¹' {c} = pr0 ⁻¹' {(c : E d)} := by
      ext z
      simp [pr, Subtype.ext_iff]
    rw [hpre]
    exact hpr0m (measurableSet_singleton _)
  have hpr : ∀ z ∈ J, ‖z - ((pr z : C) : E d)‖ ≤ ε := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcov z hz
    rw [← dist_eq_norm]
    exact (hpr0 z c hc).trans hzc.le
  -- the value of a round
  set Γ0 : ℝ := (1 + 2 * n * ε) * α + n * ε * (1 + √β) + η * β / 8 with hΓ0
  have hΓ0nn : 0 ≤ Γ0 + tol := by
    have h1 : 0 ≤ (1 + 2 * n * ε) * α := mul_nonneg (by positivity) hα
    have h2 : 0 ≤ (n : ℝ) * ε * (1 + √β) := by positivity
    have h3 : 0 ≤ η * β / 8 := by positivity
    linarith
  set P : Set (C → ℝ) := PL (Subtype.val : C → E d) n with hP
  have hsol' : ∀ q : C → ℝ, (∀ z, 0 < q z) → ∑ z, q z = 1 → ((sol q).1 ∈ stdSimplex ℝ C ∧ ∀ x b,
        (0 < (sol q).1 x ∧ ∑ z, q z * Real.exp (-η * ((sol q).2 x b z / (sol q).1 x)) ≤ 1) ∨
        ((sol q).1 x = 0 ∧ ∀ z, 0 ≤ (sol q).2 x b z)) ∧
      ∀ y, ∀ f ∈ P, ∑ x, (sol q).1 x * f x - f y +
        ∑ x, ((1 - f x) * (sol q).2 x false y + f x * (sol q).2 x true y) ≤ Γ0 + tol := by
    intro q hq hq1
    exact ⟨(ex_setS_iff η q (sol q)).1 (hsol q hq hq1).1, fun y f hf =>
      ex_round_value J hJc hJm n ε α β η tol hnpos.le hε.le hβ hη hH (Subtype.val : C → E d)
        (fun z => hCJ z.2) pr hprm hpr sol hsol q hq hq1 y f hf⟩
  -- the comparator
  obtain ⟨yc, hyc, hyg⟩ := ex_comparator K hK x0 hx0 n hn1 ε C hCJ hcov x hx
  -- the losses of the rounds on the net, clamped into [0, 1] (no change for t < n)
  let a : (t : ℕ) → (Fin t → C × Bool) → C → ℝ := fun t hh z =>
    max 0 (min 1 (A t (fun i => (((hh i).1 : E d), (hh i).2)) z))
  have ha : ∀ t hh z, a t hh z ∈ Set.Icc (0 : ℝ) 1 := fun t hh z =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp : ∀ t < n, ∀ (χ : Fin t → E d × Bool) (z : E d), z ∈ K → max 0 (min 1 (A t χ z)) = A t χ z := by
    intro t ht χ z hz
    obtain ⟨h0, h1⟩ := (hA t ht χ).2 z hz
    rw [min_eq_right h1, max_eq_right h0]
  have haP : ∀ t < n, ∀ hh, a t hh ∈ P := by
    intro t ht hh
    have heq : a t hh = fun z : C => A t (fun i => (((hh i).1 : E d), (hh i).2)) (z : E d) := by
      funext z
      exact hclamp t ht _ _ (hJK (hCJ z.2))
    rw [heq]
    exact ex_PL_of_adm K hK n hn1 (Subtype.val : C → E d) (fun i => hCJ i.2) hJne _ (hA t ht _)
  have htree := ex_tree_adapt η hη sol P (Γ0 + tol) hΓ0nn hsol' n a ha haP ⟨yc, hyc⟩
  -- the law of the learner is the product of the tree
  have hAK : ∀ t < n, ∀ χ (z : C), A t χ (z : E d) ∈ Set.Icc (0 : ℝ) 1 := fun t ht χ z =>
    (hA t ht χ).2 _ (hJK (hCJ z.2))
  obtain ⟨hW0, hW1⟩ := ex_coinLaw_sum (Subtype.val : C → E d) (exoKernel η sol)
    (ex_exoKernel_prob _ n η tol sol hsol) A n hAK
  have hW : ∀ h : Fin n → C × Bool, coinLaw Subtype.val (exoKernel η sol) A n h =
      ∏ s : Fin n, (sol (AdversarialBco.ewQ η (fun q τ z => (sol q).2 τ.1 τ.2 z / (sol q).1 τ.1) s
          (fun i : Fin s => h (Fin.castLE s.2.le i)))).1 (h s).1 *
        (if (h s).2 then a s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1
          else 1 - a s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1) := by
    intro h
    unfold coinLaw
    refine Finset.prod_congr rfl fun s _ => ?_
    have hcl : a s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1 =
        A s (ptHist Subtype.val h s) ((h s).1 : E d) :=
      hclamp s s.2 _ _ (hJK (hCJ (h s).1.2))
    rw [hcl, exoKernel, ex_weights_eq]
    rfl
  -- the pathwise split at the comparator
  have hsplit : ∀ h : Fin n → C × Bool,
      ∑ t : Fin n, (A t (ptHist Subtype.val h t) ((h t).1 : E d) - A t (ptHist Subtype.val h t) x) ≤
        ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
          a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩) + n * (1 / n + n * ε) := by
    intro h
    have hterm : ∀ t : Fin n,
        A t (ptHist Subtype.val h t) ((h t).1 : E d) - A t (ptHist Subtype.val h t) x ≤
          (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
            a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩) + (1 / n + n * ε) := by
      intro t
      have h1 : a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 =
          A t (ptHist Subtype.val h t) ((h t).1 : E d) := hclamp t t.2 _ _ (hJK (hCJ (h t).1.2))
      have h2 : a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩ =
          A t (ptHist Subtype.val h t) yc := hclamp t t.2 _ _ (hJK (hCJ hyc))
      have h3 := hyg _ (hA t t.2 (ptHist Subtype.val h t))
      rw [h1, h2]
      linarith
    calc ∑ t : Fin n, (A t (ptHist Subtype.val h t) ((h t).1 : E d) - A t (ptHist Subtype.val h t) x)
        ≤ ∑ t : Fin n, ((a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
            a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩) + (1 / n + n * ε)) :=
          Finset.sum_le_sum fun t _ => hterm t
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : (Fintype.card C : ℝ) = (C.card : ℝ) := by rw [Fintype.card_coe]
  calc pseudoReg Subtype.val (exoKernel η sol) A n x
      ≤ ∑ h : Fin n → C × Bool, coinLaw Subtype.val (exoKernel η sol) A n h *
          (∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
            a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩) + n * (1 / n + n * ε)) :=
        Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hsplit h) (hW0 h)
    _ = (∑ h : Fin n → C × Bool, coinLaw Subtype.val (exoKernel η sol) A n h *
          ∑ t : Fin n, (a t (fun i : Fin t => h (Fin.castLE t.2.le i)) (h t).1 -
            a t (fun i : Fin t => h (Fin.castLE t.2.le i)) ⟨yc, hyc⟩)) + n * (1 / n + n * ε) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hW1, one_mul]
    _ ≤ Real.log (Fintype.card C) / η + n * (Γ0 + tol) + n * (1 / n + n * ε) := by
        have := htree
        simp only [← hW] at this
        linarith
    _ = 1 + n * n * ε + Real.log C.card / η + n * (Γ0 + tol) := by
        rw [hcard]
        field_simp
        ring

/-! ## Theorem 1.5 -/

theorem theoremExplicit_of_bodyH (hB : BodySpec.BodyHExplicit) : TheoremExplicit := by
  intro d hd n hn K hKc hK x0 hx0 D hD β ε hβ hε
  have hD2 : 2 ≤ D := (AdversarialBco.two_le_diam hd K hKc.isBounded x0 hx0).trans hD
  obtain ⟨hβ2, hε0, hε4, hεD⟩ := ex_params d n hd hn D hD2 β ε hβ hε
  set J := innerBody K n with hJdef
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2
  have hJc : Convex ℝ J := AdversarialBco.convex_inner K hK _
  have hJk : IsCompact J := AdversarialBco.isCompact_inner K hKc _ hinv0
  have hJK : J ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hinv0)
  have hx0K : x0 ∈ K := hx0 (Metric.mem_closedBall_self zero_le_one)
  have hball : Metric.closedBall x0 (1 - 1 / n) ⊆ J :=
    AdversarialBco.closedBall_subset_inner K x0 hx0 (1 / n) hinv0 (by linarith)
  have hball2 : Metric.closedBall x0 (1 / 2) ⊆ J :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hJD : J ⊆ Metric.closedBall x0 D := fun y hy =>
    Metric.mem_closedBall.2 ((Metric.dist_le_diam_of_mem hKc.isBounded (hJK hy) hx0K).trans hD)
  have hJdiam : Metric.diam J ≤ D := (Metric.diam_mono hJK hKc.isBounded).trans hD
  have hmesh : 0 < mesh d ε D := by
    have hd1 : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
    unfold mesh
    positivity
  refine ⟨ex_scan_exists J x0 D _ hmesh, fun ord hord C hC => ?_⟩
  -- the net
  obtain ⟨hCJ, hsep, hcov⟩ := ex_net_facts hd J hJc x0 (1 - 1 / n) D ε (by linarith) hball hJD hε0
    (by linarith) ord hord
  rw [← hC] at hCJ hsep hcov
  have hm2 : 2 ≤ C.card := ex_net_two hd J x0 hball2 C ε hε4 hcov
  have hmcard : (C.card : ℝ) ≤ (5 * n ^ 2 * √(2 * β) * D) ^ d := by
    have h := ex_net_card J hJk.isBounded C hCJ ε D hε0 hεD hJdiam hsep
    have hr : 0 < √(2 * β) := Real.sqrt_pos.2 (by linarith)
    have h5 : 5 * D / ε = 5 * n ^ 2 * √(2 * β) * D := by
      rw [hε]
      field_simp
    rwa [h5] at h
  refine ⟨hm2, hmcard, fun η hη => ?_⟩
  have hm1 : (1 : ℝ) < C.card := by exact_mod_cast hm2
  have hlm : 0 < Real.log C.card := Real.log_pos hm1
  have hβ0 : 0 < β := by linarith
  have hη0 : 0 < η := by
    rw [hη]
    exact Real.sqrt_pos.2 (by positivity)
  have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
  have : Nonempty C := hCne.coe_sort
  refine ⟨ex_solver_exists _ n η (1 / n) hnpos.le hη0 (by positivity), fun sol hsol => ?_⟩
  -- (H)[1/n, β] on the inner body
  have hH : HypH J n 0 1 (1 / n) β := by
    have h := hB d hd n hn K hKc hK x0 hx0 D hD
    rw [← hβ] at h
    exact h
  -- the first bound, for the adaptive form
  have hmain : ∀ A ∈ AdaptAdv K n, ∀ x ∈ K,
      pseudoReg Subtype.val (exoKernel η sol) A n x ≤ 671 / 100 + √(β * n * Real.log C.card / 2) := by
    intro A hA x hx
    have h := ex_pseudo_main K hK hKc x0 hx0 n hn C hCJ hCne ε hε0 hcov (1 / n) β η (1 / n) hinv0 hβ0.le hη0
      hinv0 hH sol hsol A hA x hx
    have hid := ex_sqrt_id (Real.log C.card) β n η hlm hβ0 hnpos hη
    have hc := ex_const n β ε hn2 hβ2 hε
    have hsplit : 1 + n * n * ε + Real.log C.card / η +
          n * ((1 + 2 * n * ε) * (1 / n) + n * ε * (1 + √β) + η * β / 8 + 1 / n) =
        (1 + n * n * ε + n * ((1 + 2 * n * ε) * (1 / n) + n * ε * (1 + √β) + 1 / n)) +
          (Real.log C.card / η + n * (η * β / 8)) := by ring
    linarith
  -- the second bound
  have hlogm : Real.log C.card ≤ d * Real.log (5 * n ^ 2 * √(2 * β) * D) :=
    ex_log_m C.card d _ (by omega) hmcard
  have hsec : 671 / 100 + √(β * n * Real.log C.card / 2) ≤
      671 / 100 + √(β * n * d * Real.log (5 * n ^ 2 * √(2 * β) * D) / 2) := by
    have hbn : 0 ≤ β * n := by positivity
    have : β * n * Real.log C.card / 2 ≤ β * n * d * Real.log (5 * n ^ 2 * √(2 * β) * D) / 2 := by
      have := mul_le_mul_of_nonneg_left hlogm hbn
      linarith
    linarith [Real.sqrt_le_sqrt this]
  -- the third bound
  have hthird : ∀ r : ℝ, r ≤ n → r ≤ 671 / 100 + √(β * n * d * Real.log (5 * n ^ 2 * √(2 * β) * D) / 2) →
      r ≤ 190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ) := by
    intro r hr1 hr2
    rcases le_or_gt n d with hdn | hdn
    · exact hr1.trans (AdversarialBco.thmC_c_large d n hn hdn D 190000 hD2 (by norm_num))
    · exact hr2.trans (ex_CX d n hd hn hdn D hD2 β hβ)
  have hpt : ∀ c : C, (c : E d) ∈ K := fun c => hJK (hCJ c.2)
  have hker := ex_exoKernel_prob (Subtype.val : C → E d) n η (1 / n) sol hsol
  refine ⟨fun f hf => ?_, fun A hA x hx => ?_⟩
  · have hA : (fun t (_ : Fin t → E d × Bool) => f t) ∈ AdaptAdv K n := fun t ht _ => hf t ht
    have hsum := (ex_coinLaw_sum (Subtype.val : C → E d) (exoKernel η sol) hker (fun t _ => f t) n
      (fun t ht _ z => (hf t ht).2 _ (hpt z))).2
    have hKne : K.Nonempty := ⟨x0, hx0K⟩
    have h1 := ex_coinReg_of_pseudo K hKne Subtype.val (exoKernel η sol) f n hsum _
      (fun x hx => hmain _ hA x hx)
    have hn' := ex_coinReg_of_pseudo K hKne Subtype.val (exoKernel η sol) f n hsum _
      (fun x hx => ex_pseudo_le_n K Subtype.val hpt (exoKernel η sol) hker _ n hA x hx)
    exact ⟨h1, h1.trans hsec, hthird _ hn' (h1.trans hsec)⟩
  · have h1 := hmain A hA x hx
    have hn' := ex_pseudo_le_n K Subtype.val hpt (exoKernel η sol) hker A n hA x hx
    exact ⟨h1, h1.trans hsec, hthird _ hn' (h1.trans hsec)⟩

/-! ## Corollary 1.6 -/

theorem ex_playLaw_sum {d : ℕ} (K : Set (E d)) (C : Finset (E d)) (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ)
    (hpol : IsCPolicy K C pol) (f : ℕ → E d → ℝ) (n : ℕ) (hf : f ∈ Advs K n) :
    (∀ y, 0 ≤ playLaw pol f n y) ∧ ∑ y, playLaw pol f n y = 1 := by
  have hCsubK : (C : Set (E d)) ⊆ K := hpol.1
  have hpol_vec (t : ℕ) (χ : Fin t → E d × ℝ) (hχ : ∀ i, (χ i).1 ∈ K ∧ (χ i).2 ∈ Set.Icc (0 : ℝ) 1) :
      pol t χ ∈ probVecs C := hpol.2 t χ hχ
  have h_adm_val (t : ℕ) (ht : t < n) (x : E d) (hx : x ∈ K) : f t x ∈ Set.Icc (0 : ℝ) 1 :=
    (hf t ht).2 x hx
  -- nonnegativity of each factor
  have h_nonneg_factor (y : Fin n → C) (t : Fin n) : 0 ≤ pol t (fun i : Fin t => ((y (Fin.castLE t.2.le i) : E d), f i (y (Fin.castLE t.2.le i)))) (y t) := by
    have hχ : ∀ i : Fin t, ((fun i' : Fin t => ((y (Fin.castLE t.2.le i') : E d), f i' (y (Fin.castLE t.2.le i')))) i).1 ∈ K ∧
        ((fun i' : Fin t => ((y (Fin.castLE t.2.le i') : E d), f i' (y (Fin.castLE t.2.le i')))) i).2 ∈ Set.Icc (0 : ℝ) 1 := by
      intro i
      have hi_val : (Fin.castLE t.2.le i).val < n :=
        lt_trans i.2 t.2
      have hxK : (y (Fin.castLE t.2.le i)).val ∈ K := hCsubK (y (Fin.castLE t.2.le i)).property
      have hfx : f (Fin.castLE t.2.le i).val (y (Fin.castLE t.2.le i)).val ∈ Set.Icc (0 : ℝ) 1 :=
        h_adm_val (Fin.castLE t.2.le i).val hi_val (y (Fin.castLE t.2.le i)).val hxK
      exact ⟨hxK, hfx⟩
    have hmem := hpol_vec t (fun i : Fin t => ((y (Fin.castLE t.2.le i) : E d), f i (y (Fin.castLE t.2.le i)))) hχ
    exact hmem.1 (y t)
  -- sum = 1 using a helper kernel κ that works for all t
  have h_sum_one : ∑ y : Fin n → C, playLaw pol f n y = 1 := by
    -- define κ : (t : ℕ) → (Fin t → C) → C → ℝ that extends pol uniformly for t ≥ n
    have hC_nonempty : C.Nonempty := by
      have h0 := hpol.2 0 (fun i => Fin.elim0 i) (by intro i; exact Fin.elim0 i)
      by_contra h_empty
      have h_empty' : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
      have hsum0 : ∑ x : C, pol 0 (fun i => Fin.elim0 i) x = 0 := by
        subst h_empty'
        simp
      rw [h0.2] at hsum0
      linarith
    have : Nonempty C := by
      obtain ⟨x, hx⟩ := hC_nonempty
      exact ⟨⟨x, hx⟩⟩
    have h_card_ne_zero : (Fintype.card C : ℝ) ≠ 0 := by
      have hpos : 0 < Fintype.card C := Fintype.card_pos (α := C)
      have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
      linarith
    let κ : (t : ℕ) → (Fin t → C) → C → ℝ := fun t h c =>
      if ht : t < n then
        pol t (fun i : Fin t => ((h i : E d), f i (h i))) c
      else
        1 / (Fintype.card C : ℝ)
    have hκ_sum (t : ℕ) (h : Fin t → C) : ∑ c : C, κ t h c = 1 := by
      dsimp [κ]
      by_cases ht : t < n
      · -- t < n case
        simp [ht]
        have hχ : ∀ i : Fin t, (((fun i' : Fin t => ((h i' : E d), f i' (h i'))) i).1 ∈ K ∧
            ((fun i' : Fin t => ((h i' : E d), f i' (h i'))) i).2 ∈ Set.Icc (0 : ℝ) 1) := by
          intro i
          have hi_val : i.val < n := lt_trans i.2 ht
          have hxK : (h i).val ∈ K := hCsubK (h i).property
          have hfx : f i (h i).val ∈ Set.Icc (0 : ℝ) 1 :=
            h_adm_val i.val hi_val (h i).val hxK
          exact ⟨hxK, hfx⟩
        have hmem := hpol_vec t (fun i : Fin t => ((h i : E d), f i (h i))) hχ
        simpa using hmem.2
      · -- t ≥ n case
        simp [ht]
        have hpos : 0 < Fintype.card C := Fintype.card_pos (α := C)
        field_simp [ne_of_gt hpos]
    have h_playLaw_eq : playLaw pol f n = fun y => ∏ t : Fin n, κ t (fun s : Fin t => y (Fin.castLE t.2.le s)) (y t) := by
      ext y
      dsimp [playLaw, κ]
      refine Finset.prod_congr rfl (fun t ht => ?_)
      have ht_n : t.val < n := t.2
      simp [ht_n]
    rw [h_playLaw_eq]
    -- now use the general sum_prod_policy from Work.Deps
    exact AdversarialBco.sum_prod_policy κ hκ_sum n
  have h_nonneg : ∀ y, 0 ≤ playLaw pol f n y := by
    intro y
    dsimp [playLaw]
    apply Finset.prod_nonneg
    intro t _
    exact h_nonneg_factor y t
  exact ⟨h_nonneg, h_sum_one⟩

theorem ex_policyReg_bounds {d : ℕ} (K : Set (E d)) (hK : K.Nonempty) (C : Finset (E d))
    (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ) (hpol : IsCPolicy K C pol) (n : ℕ) :
    (∀ f ∈ Advs K n, policyReg K C pol f n ≤ n) ∧ policyReg K C pol (fun _ _ => 0) n = 0 := by
  have hC_sub_K : (C : Set (E d)) ⊆ K := hpol.1
  have hsum := ex_playLaw_sum K C pol hpol
  constructor
  · intro f hf
    have hsumf := hsum f n hf
    rcases hsumf with ⟨hplay_nonneg, hplay_sum⟩
    have h_each_le_one : ∀ (t : ℕ) (ht : t < n) (x : E d) (hx : x ∈ K), f t x ≤ 1 := by
      intro t ht x hx
      rcases hf t ht with ⟨_, h_range⟩
      exact (h_range x hx).2
    have h_sInf_nonneg : 0 ≤ sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) := by
      refine Real.sInf_nonneg ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      refine Finset.sum_nonneg fun t ht => ?_
      have ht_range : t < n := by simpa [Finset.mem_range] using ht
      rcases hf t ht_range with ⟨_, h_range⟩
      exact (h_range x hx).1
    have h_sum_le_n : ∀ y : Fin n → C, (∑ t : Fin n, f t (y t : E d)) ≤ (n : ℝ) := by
      intro y
      calc
        (∑ t : Fin n, f t (y t : E d)) ≤ (∑ t : Fin n, (1 : ℝ)) :=
          Finset.sum_le_sum fun t _ => h_each_le_one t t.2 (y t : E d) (hC_sub_K (y t).2)
        _ = (n : ℝ) := by simp
    unfold policyReg
    have h1 : (∑ y : Fin n → C, playLaw pol f n y * (∑ t : Fin n, f t (y t : E d))) ≤ (n : ℝ) := by
      calc
        (∑ y : Fin n → C, playLaw pol f n y * (∑ t : Fin n, f t (y t : E d))) ≤
            (∑ y : Fin n → C, playLaw pol f n y * (n : ℝ)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h_sum_le_n y) (hplay_nonneg y)
        _ = ((∑ y : Fin n → C, playLaw pol f n y) * (n : ℝ)) := by rw [Finset.sum_mul]
        _ = (1 * (n : ℝ)) := by rw [hplay_sum]
        _ = (n : ℝ) := by simp
    have h2 : 0 ≤ sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K) := h_sInf_nonneg
    linarith
  · rw [policyReg]
    have h_sum1 : (∑ y : Fin n → C, playLaw pol (fun _ _ => 0) n y * (∑ t : Fin n, ((fun _ _ => 0 : ℕ → E d → ℝ) t (y t : E d)))) = 0 := by
      simp
    have h_sInf : sInf ((fun x => ∑ t ∈ Finset.range n, ((fun _ _ => 0 : ℕ → E d → ℝ) t x)) '' K) = 0 := by
      have h_image : ((fun x => ∑ t ∈ Finset.range n, ((fun _ _ => 0 : ℕ → E d → ℝ) t x)) '' K) = {0} := by
        ext z; simp [hK]
      rw [h_image, csInf_singleton]
    rw [h_sum1, h_sInf]
    simp

/-- The minimax regret over `C`-policies is at most the worst regret of one `C`-policy, for a bound `B ≥ 0` (with
`K` not convex and `n ≥ 1`, `Advs K n` is empty, every supremum is `0`, and a negative `B` would fail). -/
theorem ex_minimaxC_le {d : ℕ} (K : Set (E d)) (hK : K.Nonempty) (n : ℕ) (C : Finset (E d))
    (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ) (hpol : IsCPolicy K C pol) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ f ∈ Advs K n, policyReg K C pol f n ≤ B) : minimaxRegretC K n ≤ B := by
  have hzero : ∀ f ∈ Advs K n, (fun _ _ => (0 : ℝ)) ∈ Advs K n := fun f hf t ht =>
    ⟨convexOn_const 0 (hf t ht).1.1, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩
  have hlow : ∀ (C' : Finset (E d)) (pol' : (t : ℕ) → (Fin t → E d × ℝ) → C' → ℝ), IsCPolicy K C' pol' →
      0 ≤ sSup ((fun f => policyReg K C' pol' f n) '' Advs K n) := by
    intro C' pol' hpol'
    rcases (Advs K n).eq_empty_or_nonempty with h | ⟨f, hf⟩
    · simp [h]
    · obtain ⟨hle, h0⟩ := ex_policyReg_bounds K hK C' pol' hpol' n
      exact le_csSup ⟨(n : ℝ), by rintro _ ⟨g, hg, rfl⟩; exact hle g hg⟩ ⟨_, hzero f hf, h0⟩
  have hT : BddBelow {r | ∃ (C' : Finset (E d)) (pol' : (t : ℕ) → (Fin t → E d × ℝ) → C' → ℝ),
      IsCPolicy K C' pol' ∧ r = sSup ((fun f => policyReg K C' pol' f n) '' Advs K n)} :=
    ⟨0, by rintro r ⟨C', pol', hpol', rfl⟩; exact hlow C' pol' hpol'⟩
  calc minimaxRegretC K n ≤ sSup ((fun f => policyReg K C pol f n) '' Advs K n) :=
        csInf_le hT ⟨C, pol, hpol, rfl⟩
    _ ≤ B := by
      rcases (Advs K n).eq_empty_or_nonempty with h | hne
      · simp [h, hB0]
      · exact csSup_le (hne.image _) (by rintro _ ⟨f, hf, rfl⟩; exact hB f hf)

theorem ex_cor_one {d : ℕ} (hd : 1 ≤ d) (K : Set (E d)) (hKc : IsCompact K) (c : E d)
    (hc : Metric.closedBall c 1 ⊆ K) (n : ℕ) (hn : n = 1) :
    minimaxRegretC K n ≤
      190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * Metric.diam K) ^ (3 / 2 : ℝ) := by
  subst hn
  have hKne : K.Nonempty := by
    have hc_mem : c ∈ Metric.closedBall c 1 :=
      Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)
    exact ⟨c, hc hc_mem⟩
  have hKb : Bornology.IsBounded K := hKc.isBounded
  have hdiam : 2 ≤ Metric.diam K := AdversarialBco.two_le_diam hd K hKb c hc
  have hc_mem_ball : c ∈ Metric.closedBall c 1 :=
    Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)
  have hc_in_K : c ∈ K := hc hc_mem_ball
  let C : Finset (E d) := {c}
  let pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ := fun _ _ _ => 1
  have hpol : IsCPolicy K C pol := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have : x = c := by simpa [C] using hx
      subst this
      exact hc_in_K
    · intro t χ hχ
      refine ⟨fun x => by norm_num, ?_⟩
      calc
        ∑ x : C, pol t χ x = ∑ x : C, (1 : ℝ) := rfl
        _ = (Fintype.card C : ℝ) := by simp
        _ = (1 : ℝ) := by simp [C]
  have h_bound_raw : ∀ f ∈ Advs K 1, policyReg K C pol f 1 ≤ ((1 : ℕ) : ℝ) :=
    (AdversarialBco.Explicit.ex_policyReg_bounds K hKne C pol hpol 1).1
  have h_bound : ∀ f ∈ Advs K 1, policyReg K C pol f 1 ≤ (1 : ℝ) := by
    simpa [Nat.cast_one] using h_bound_raw
  have h_minimax : minimaxRegretC K 1 ≤ (1 : ℝ) :=
    AdversarialBco.Explicit.ex_minimaxC_le K hKne 1 C pol hpol (1 : ℝ) zero_le_one h_bound
  have h_num : (1 : ℝ) ≤ 190000 * ((d : ℝ) ^ (3 / 2 : ℝ)) * Real.sqrt (1 : ℝ) * Real.log ((1 : ℝ) * Metric.diam K) ^ (3 / 2 : ℝ) := by
    have hd_one : (1 : ℝ) ≤ (d : ℝ) := by exact mod_cast hd
    have h_sqrt_one : Real.sqrt (1 : ℝ) = 1 := by norm_num
    rw [h_sqrt_one, mul_one, one_mul]
    have h_log_two : (1/2 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have h_log_diam_ge : (1/2 : ℝ) ≤ Real.log (Metric.diam K) := by
      have hpos_diam : 0 < Metric.diam K := by
        have : 0 ≤ Metric.diam K := Metric.diam_nonneg
        linarith
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hdiam
      linarith
    have h_base_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
    have h_base_le_one : (1/2 : ℝ) ≤ (1 : ℝ) := by norm_num
    have h_exp_le : (3/2 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h_rpow_half : ((1/2 : ℝ) ^ (2 : ℝ)) ≤ ((1/2 : ℝ) ^ (3/2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge h_base_pos h_base_le_one h_exp_le
    have h_half_sq : ((1/2 : ℝ) ^ (2 : ℝ)) = (1/4 : ℝ) := by norm_num
    rw [h_half_sq] at h_rpow_half
    have h_d_pow : (1 : ℝ) ≤ (d : ℝ) ^ (3/2 : ℝ) := by
      have hx : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      have hy : (1 : ℝ) ≤ (d : ℝ) := hd_one
      have hz : (0 : ℝ) ≤ (3/2 : ℝ) := by norm_num
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3/2 : ℝ) := by norm_num
        _ ≤ (d : ℝ) ^ (3/2 : ℝ) := Real.rpow_le_rpow hx hy hz
    have h_log_pow : ((1/2 : ℝ) ^ (3/2 : ℝ)) ≤ Real.log (Metric.diam K) ^ (3/2 : ℝ) := by
      have h_log_nonneg : 0 ≤ Real.log (Metric.diam K) := by
        have h_diam_ge_one : (1 : ℝ) ≤ Metric.diam K := by linarith
        calc
          0 = Real.log (1 : ℝ) := by symm; exact Real.log_one
          _ ≤ Real.log (Metric.diam K) := Real.log_le_log (by norm_num) h_diam_ge_one
      have h_log_ge_half : (1/2 : ℝ) ≤ Real.log (Metric.diam K) := h_log_diam_ge
      exact Real.rpow_le_rpow (by norm_num) h_log_ge_half (by norm_num : (0 : ℝ) ≤ (3/2 : ℝ))
    have h_total : (1 : ℝ) ≤ 190000 * ((d : ℝ) ^ (3/2 : ℝ)) * Real.log (Metric.diam K) ^ (3/2 : ℝ) := by
      have h_prod : (1/4 : ℝ) ≤ ((d : ℝ) ^ (3/2 : ℝ)) * Real.log (Metric.diam K) ^ (3/2 : ℝ) := by
        nlinarith
      have h_base : (1 : ℝ) ≤ 190000 * (1/4 : ℝ) := by norm_num
      nlinarith
    exact h_total
  linarith

theorem corollaryExplicit_of_bodyH (hB : BodySpec.BodyHExplicit) : CorollaryExplicit := by
  intro d hd K hKc hK hball n hn
  obtain ⟨c, hc⟩ := hball
  rcases eq_or_lt_of_le hn with h1 | h2
  · exact ex_cor_one hd K hKc c hc n h1.symm
  have hn2 : 2 ≤ n := h2
  have hcK : c ∈ K := hc (Metric.mem_closedBall_self zero_le_one)
  set D := Metric.diam K with hDdef
  have hD2 : 2 ≤ D := AdversarialBco.two_le_diam hd K hKc.isBounded c hc
  set β : ℝ := 1200000000 * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n) with hβ
  set ε : ℝ := 1 / (n ^ 2 * √(2 * β)) with hε
  obtain ⟨-, hε0, hε4, -⟩ := ex_params d n hd hn2 D hD2 β ε hβ hε
  have hT := theoremExplicit_of_bodyH hB d hd n hn2 K hKc hK c hc D le_rfl β ε hβ hε
  obtain ⟨ord, hord⟩ := hT.1
  obtain ⟨hm2, -, hrest⟩ := hT.2 ord hord _ rfl
  obtain ⟨⟨sol, hsol⟩, hall⟩ := hrest _ rfl
  -- the net lies in K
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hinv0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hinv1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2r
  have hJK : innerBody K n ⊆ K := fun y hy => hy (Metric.mem_closedBall_self hinv0)
  have hJD : innerBody K n ⊆ Metric.closedBall c D := fun y hy =>
    Metric.mem_closedBall.2 (Metric.dist_le_diam_of_mem hKc.isBounded (hJK hy) hcK)
  obtain ⟨hCJ, -, -⟩ := ex_net_facts hd (innerBody K n) (AdversarialBco.convex_inner K hK _) c (1 - 1 / n) D ε
    (by linarith) (AdversarialBco.closedBall_subset_inner K c hc (1 / n) hinv0 (by linarith)) hJD hε0
    (by linarith) ord hord
  have hCK : ↑(net ε D ord) ⊆ K := hCJ.trans hJK
  have hCne : (net ε D ord).Nonempty := Finset.card_pos.1 (by omega)
  have : Nonempty (net ε D ord) := hCne.coe_sort
  -- the policy of Lemma 7.13 for the learner of Theorem 1.5
  have hP := ex_exoKernel_prob (Subtype.val : net ε D ord → E d) n _ (1 / n) sol hsol
  obtain ⟨hpol, -, hlaw⟩ := lemmaMarg d K (net ε D ord) hCK hCne _ hP
  have hlog : 0 ≤ Real.log (n * D) := Real.log_nonneg (by nlinarith)
  refine ex_minimaxC_le K ⟨c, hcK⟩ n (net ε D ord) _ hpol _
    (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (Real.rpow_nonneg hlog _)) fun f hf => ?_
  rw [(hlaw n f hf).2]
  exact ((hall sol hsol).1 f hf).2.2

end AdversarialBco.Explicit
