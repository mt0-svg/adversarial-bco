/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.Clamp

@[expose] public section

/-!
# CLAMP-NS, the filler of the clamp interface

The routine: the clamp as `cl(l) = m + (|l - a| - |l - b|)/2`, the absolute values by
Newton-Schulz sign iterations. For the shifts `c = a + e` and `c = b - e`: `M = S' - c I`, `X₀ = M/c₀`,
`X_{j+1} = X_j (3 I - X_j²)/2` for `j < J` (`nsIter`), `Y^c = M X_J` (`clampNSRoot`); then
`T' = m I + (Y^a - Y^b)/2` (`clampNSMat`). No inverse and no Gauss-Jordan elimination: every matrix is a polynomial
in `S'`. The count is computed from `k = cnK` (Clamp.lean): `J(k) = 2k + ⌈log₂ (3k + 3)⌉` (`cnsJ`, with `Nat.clog`).

NS0 and NS1 are the scalar facts and Lemma C; NS1' is the scalar form of
Lemma NS-1 (c), `0 ≤ t (1 - p_J(t)) ≤ 2^{-k-1}` on `[0, 1]`; NS2 says that the iteration is the scalar one on the
spectrum; NS3 and NS4a are Lemma N-S (i) and (ii) (the spectrum of `T'` in `[a + e/2, b - e/2]`, read here as the band
`[a, b]` of the interface; the distance `(3/2) e d^{1/2}` to the exact clamp of `S'`); NS4 adds Lemma N (iii)
(`clampExact_nonexp`); NS5 is measurability. `clampNSRoutine` is the interface filled by CLAMP-NS.

Everything here is proved. C2c-NS `cnsJ_le_pgNs` goes through `cnK_pg_le`: `c₀/(2e') ≤ N²` (`cnRatio_le`) and
`N² ≤ 2^(N/3 - 1)` (`sq_le_two_pow_div3`), as `N ≥ 250000 d` (`pgNs_ge_d`).

Junk values. `nsIter` has no division; `clampNSRoot` multiplies by `c₀⁻¹`, read at `a < b`, where `c₀ > 0`. `cnK` is
`0` when its logarithm is negative.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.PG Matrix
open scoped RealInnerProductSpace

namespace AdversarialBco.Conj1Arith

variable {d : ℕ}

/-- `p(x) = x (3 - x²)/2`. -/
noncomputable def nsP (x : ℝ) : ℝ := x * (3 - x ^ 2) / 2

/-- The Newton-Schulz sign iteration `X_{j+1} = X_j (3 I - X_j²)/2`. -/
noncomputable def nsIter (X : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => X
  | j + 1 => (1 / 2 : ℝ) • (nsIter X j * ((3 : ℝ) • 1 - nsIter X j * nsIter X j))

/-- `Y^c = M X_J`, `M = S - c I`, `X₀ = M/c₀`. -/
noncomputable def clampNSRoot (a b c : ℝ) (J : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (S - c • 1) * nsIter ((cnC0 d a b)⁻¹ • (S - c • 1)) J

/-- CLAMP-NS on the matrix part, with `J` steps: `T' = m I + (Y^a - Y^b)/2`. -/
noncomputable def clampNSMat (a b e : ℝ) (J : ℕ) (Y : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cnMid a b • 1 + (1 / 2 : ℝ) • (clampNSRoot a b (a + e) J (clipSym a b Y) - clampNSRoot a b (b - e) J (clipSym a b Y))

/-- `J(k) = 2k + ⌈log₂ (3k + 3)⌉`. -/
def nsCount (k : ℕ) : ℕ := 2 * k + Nat.clog 2 (3 * k + 3)

/-- The count of CLAMP-NS, `J(k)` at `k = cnK d a b e`. -/
noncomputable def cnsJ (d : ℕ) (a b e : ℝ) : ℕ := nsCount (cnK d a b e)

/-- NS0, the scalar facts of `p` on `[0, 1]`. -/
theorem nsP_facts (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ nsP x ∧ nsP x ≤ 1 ∧ x ≤ nsP x ∧ 1 - nsP x ≤ 3 / 2 * (1 - x) ^ 2 ∧ (x ≤ 1 / 2 → 11 / 8 * x ≤ nsP x) ∧
      ∀ y, x ≤ y → y ≤ 1 → nsP x ≤ nsP y := by
  have hx_sq_le_one : x ^ 2 ≤ 1 := by
    nlinarith
  have h_nonneg_3_minus_x_sq : 0 ≤ 3 - x ^ 2 := by
    nlinarith
  have hnsP_nonneg : 0 ≤ nsP x := by
    dsimp [nsP]
    nlinarith
  have hnsP_le_one : nsP x ≤ 1 := by
    dsimp [nsP]
    nlinarith
  have hx_le_nsP : x ≤ nsP x := by
    dsimp [nsP]
    nlinarith
  have h_one_minus_nsP_le : 1 - nsP x ≤ 3 / 2 * (1 - x) ^ 2 := by
    dsimp [nsP]
    nlinarith
  have h_eleventh_eighths : x ≤ 1 / 2 → 11 / 8 * x ≤ nsP x := by
    intro hx_half
    dsimp [nsP]
    nlinarith
  have h_mono : ∀ y, x ≤ y → y ≤ 1 → nsP x ≤ nsP y := by
    intro y hxy hy1
    have hy0 : 0 ≤ y := by linarith
    dsimp [nsP]
    have h_factor : y * (3 - y ^ 2) - x * (3 - x ^ 2) = (y - x) * (3 - (x ^ 2 + x * y + y ^ 2)) := by
      ring
    have h_diff_nonneg : 0 ≤ y * (3 - y ^ 2) - x * (3 - x ^ 2) := by
      rw [h_factor]
      have h_nonneg_factor1 : 0 ≤ y - x := by linarith
      have h_nonneg_factor2 : 0 ≤ 3 - (x ^ 2 + x * y + y ^ 2) := by
        nlinarith
      nlinarith
    linarith
  exact And.intro hnsP_nonneg (And.intro hnsP_le_one (And.intro hx_le_nsP (And.intro h_one_minus_nsP_le (And.intro h_eleventh_eighths h_mono))))

/-- NS1, phase 1 of Lemma C: from `x ≥ 2^{-k-1}`, `2k` steps reach `1/2`. -/
theorem nsP_phase1 (k : ℕ) (x : ℝ) (hx0 : 1 / 2 ^ (k + 1) ≤ x) (hx1 : x ≤ 1) : 1 / 2 ≤ nsP^[2 * k] x := by
  have hx_nonneg : 0 ≤ x := by
    have hpos : (0 : ℝ) ≤ 1 / 2 ^ (k + 1) := by positivity
    exact le_trans hpos hx0
  have hx_le_one : x ≤ 1 := hx1
  -- nsP preserves [0,1]
  have h_nsP_range (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ nsP z ∧ nsP z ≤ 1 := by
    have h := nsP_facts z hz0 hz1
    exact ⟨h.1, h.2.1⟩
  -- nsP is monotone on [0,1]
  have h_nsP_mono {y z : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz1 : z ≤ 1) (hyz : y ≤ z) : nsP y ≤ nsP z :=
    (nsP_facts y hy0 hy1).2.2.2.2.2 z hyz hz1
  -- nsP^[n] preserves [0,1]
  have h_iter_range (n : ℕ) : 0 ≤ nsP^[n] x ∧ nsP^[n] x ≤ 1 := by
    induction' n with n ih
    · exact ⟨hx_nonneg, hx_le_one⟩
    · rcases ih with ⟨hn0, hn1⟩
      rw [Function.iterate_succ_apply']
      exact h_nsP_range (nsP^[n] x) hn0 hn1
  -- Key claim: min(1/4, 2^m * x) ≤ nsP^[2m] x
  have h_claim : ∀ (m : ℕ), min (1/4 : ℝ) ((2 : ℝ)^m * x) ≤ nsP^[2*m] x := by
    intro m
    induction' m with m ih
    · -- m = 0
      simpa [Function.iterate_zero] using min_le_right (1/4 : ℝ) x
    · -- m → m+1
      have h_iter_succ : nsP^[2*(m+1)] x = nsP (nsP (nsP^[2*m] x)) := by
        have h_eq : 2*(m+1) = 2 + 2*m := by omega
        rw [h_eq, Function.iterate_add_apply]
        rfl
      rw [h_iter_succ]
      set y := nsP^[2*m] x with hy_def
      rcases h_iter_range (2*m) with ⟨hy_nonneg, hy_le_one⟩
      have h_facts_y := nsP_facts y hy_nonneg hy_le_one
      have h_nsP_y_ge_y : y ≤ nsP y := h_facts_y.2.2.1
      have h_nsP_y_nonneg : 0 ≤ nsP y := h_facts_y.1
      have h_nsP_y_le_one : nsP y ≤ 1 := h_facts_y.2.1
      have h_nsP_y_facts := nsP_facts (nsP y) h_nsP_y_nonneg h_nsP_y_le_one
      by_cases hy_ge_quarter : (1/4 : ℝ) ≤ y
      · -- y ≥ 1/4: nsP(nsP y) ≥ nsP y ≥ y ≥ 1/4
        have h_nsP_y_ge_quarter : (1/4 : ℝ) ≤ nsP y := by linarith
        have h_nsP_nsP_y_ge_quarter : (1/4 : ℝ) ≤ nsP (nsP y) := by
          have h := h_nsP_y_facts.2.2.1
          linarith
        have h_min : min (1/4 : ℝ) ((2 : ℝ)^(m+1) * x) ≤ (1/4 : ℝ) := min_le_left _ _
        linarith
      · -- y < 1/4
        have hy_lt_quarter : y < 1/4 := by linarith
        -- From ih: min(1/4, 2^m * x) ≤ y < 1/4, so 2^m * x ≤ 1/4
        have h_2m_x_le_quarter : (2 : ℝ)^m * x ≤ 1/4 := by
          by_contra! h_gt
          have h_min_eq_left : min (1/4 : ℝ) ((2 : ℝ)^m * x) = 1/4 := min_eq_left (by linarith)
          rw [h_min_eq_left] at ih
          linarith
        have h_min_eq : min (1/4 : ℝ) ((2 : ℝ)^m * x) = (2 : ℝ)^m * x :=
          min_eq_right h_2m_x_le_quarter
        have h_2m_x_le_y : (2 : ℝ)^m * x ≤ y := by linarith
        -- Ratio bound: for y ∈ [0, 1/4], nsP y ≥ (47/32) * y
        have h_ratio : (47/32 : ℝ) * y ≤ nsP y := by
          dsimp [nsP]
          by_cases hy0 : y = 0
          · rw [hy0]; simp
          · have hy_pos : 0 < y := by
              by_contra! h
              apply hy0
              linarith
            have h_div : (47/32 : ℝ) ≤ (3 - y^2)/2 := by
              have hy_sq_le : y^2 ≤ (1/4)^2 := by nlinarith
              nlinarith
            calc
              (47/32 : ℝ) * y ≤ ((3 - y^2)/2) * y := mul_le_mul_of_nonneg_right h_div hy_nonneg
              _ = y * (3 - y^2) / 2 := by ring
        by_cases h_nsP_y_ge_quarter : (1/4 : ℝ) ≤ nsP y
        · -- nsP y ≥ 1/4: nsP(nsP y) ≥ nsP y ≥ 1/4
          have h_nsP_nsP_y_ge_quarter : (1/4 : ℝ) ≤ nsP (nsP y) := by
            have h := h_nsP_y_facts.2.2.1
            linarith
          have h_min : min (1/4 : ℝ) ((2 : ℝ)^(m+1) * x) ≤ (1/4 : ℝ) := min_le_left _ _
          linarith
        · -- nsP y < 1/4: apply ratio bound again
          have h_nsP_y_lt_quarter : nsP y < 1/4 := by linarith
          have h_ratio2 : (47/32 : ℝ) * nsP y ≤ nsP (nsP y) := by
            by_cases h_nsP_y0 : nsP y = 0
            · rw [h_nsP_y0]
              dsimp [nsP]
              norm_num
            · have h_nsP_y_pos : 0 < nsP y := by
                by_contra! h
                apply h_nsP_y0
                linarith
              have h_div : (47/32 : ℝ) ≤ (3 - (nsP y)^2)/2 := by
                have h_nsP_y_sq_le : (nsP y)^2 ≤ (1/4)^2 := by nlinarith
                nlinarith
              calc
                (47/32 : ℝ) * nsP y ≤ ((3 - (nsP y)^2)/2) * nsP y :=
                  mul_le_mul_of_nonneg_right h_div h_nsP_y_nonneg
                _ = nsP (nsP y) := by dsimp [nsP]; ring
          have h_sq_gt_two : (2 : ℝ) < ((47 : ℝ)/32)^2 := by norm_num
          have h_nsP_nsP_y_ge_2y : (2 : ℝ) * y ≤ nsP (nsP y) := by
            nlinarith
          have h_target : (2 : ℝ)^(m+1) * x ≤ nsP (nsP y) := by
            calc
              (2 : ℝ)^(m+1) * x = (2 : ℝ) * ((2 : ℝ)^m * x) := by ring
              _ ≤ (2 : ℝ) * y := by nlinarith
              _ ≤ nsP (nsP y) := h_nsP_nsP_y_ge_2y
          have h_min : min (1/4 : ℝ) ((2 : ℝ)^(m+1) * x) ≤ (2 : ℝ)^(m+1) * x := min_le_right _ _
          linarith
  -- Now use h_claim to prove the target
  by_cases hk0 : k = 0
  · subst hk0
    simp [Function.iterate_zero]
    simpa using hx0
  · rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, hm⟩
    -- hm: k = m.succ = m+1
    subst hm
    -- Now we need 1/2 ≤ nsP^[2*(m+1)] x
    have h_claim_m := h_claim m
    -- Show 2^m * x ≥ 1/4 using hx0: 1/2^(m+2) ≤ x
    have hx0' : 1 / ((2 : ℝ)^(m+2)) ≤ x := by
      have h_exp_eq : (m.succ : ℕ) + 1 = m + 2 := by omega
      simpa [h_exp_eq] using hx0
    have h_pow_nonneg : 0 ≤ (2 : ℝ)^m := by positivity
    have h_pow_mul_ge_quarter : (1/4 : ℝ) ≤ (2 : ℝ)^m * x := by
      have h_eq : (2 : ℝ)^m * (1 / ((2 : ℝ)^(m+2))) = 1/4 := by
        calc
          (2 : ℝ)^m * (1 / ((2 : ℝ)^(m+2))) = ((2 : ℝ)^m) / ((2 : ℝ)^(m+2)) := by ring
          _ = ((2 : ℝ)^m) / ((2 : ℝ)^m * (2 : ℝ)^2) := by rw [pow_add]
          _ = 1 / ((2 : ℝ)^2) := by
            field_simp [pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0)]
          _ = 1/4 := by norm_num
      calc
        (1/4 : ℝ) = (2 : ℝ)^m * (1 / ((2 : ℝ)^(m+2))) := by rw [h_eq]
        _ ≤ (2 : ℝ)^m * x := mul_le_mul_of_nonneg_left hx0' h_pow_nonneg
    -- So min(1/4, 2^m * x) = 1/4
    have h_min_eq_quarter : min (1/4 : ℝ) ((2 : ℝ)^m * x) = (1/4 : ℝ) := by
      apply min_eq_left
      linarith
    rw [h_min_eq_quarter] at h_claim_m
    -- h_claim_m: 1/4 ≤ nsP^[2m] x
    set y := nsP^[2*m] x with hy_def
    have hy_range := h_iter_range (2*m)
    rcases hy_range with ⟨hy_nonneg, hy_le_one⟩
    -- Now nsP^[2*(m+1)] x = nsP^[2] (nsP^[2m] x) = nsP (nsP y)
    have h_iter_succ : nsP^[2*(m+1)] x = nsP (nsP y) := by
      have h_eq : 2*(m+1) = 2 + 2*m := by omega
      rw [h_eq, Function.iterate_add_apply]
      rfl
    rw [h_iter_succ]
    -- Use monotonicity: nsP^[2] is monotone on [0,1]
    have h_nsP2_mono {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hab : a ≤ b) :
        nsP (nsP a) ≤ nsP (nsP b) := by
      have h1 : nsP a ≤ nsP b := h_nsP_mono ha0 ha1 hb1 hab
      have h_nsP_a_nonneg : 0 ≤ nsP a := (nsP_facts a ha0 ha1).1
      have h_nsP_a_le_one : nsP a ≤ 1 := (nsP_facts a ha0 ha1).2.1
      have h_nsP_b_nonneg : 0 ≤ nsP b := (nsP_facts b (by linarith) hb1).1
      have h_nsP_b_le_one : nsP b ≤ 1 := (nsP_facts b (by linarith) hb1).2.1
      exact h_nsP_mono h_nsP_a_nonneg h_nsP_a_le_one h_nsP_b_le_one h1
    -- Compute nsP^[2] (1/4) = 2206321/4194304 ≥ 1/2
    have h_nsP_quarter : nsP (1/4 : ℝ) = 47/128 := by
      dsimp [nsP]; norm_num
    have h_nsP_nsP_quarter : nsP (47/128 : ℝ) = 2206321/4194304 := by
      dsimp [nsP]; norm_num
    have h_ge_half : (1/2 : ℝ) ≤ 2206321/4194304 := by norm_num
    have h_nsP2_quarter_ge_half : (1/2 : ℝ) ≤ nsP (nsP (1/4 : ℝ)) := by
      rw [h_nsP_quarter, h_nsP_nsP_quarter]
      exact h_ge_half
    -- Apply monotonicity with a = 1/4, b = y
    have h_nsP2_y_ge_nsP2_quarter : nsP (nsP (1/4 : ℝ)) ≤ nsP (nsP y) :=
      h_nsP2_mono (by norm_num) (by norm_num) hy_le_one h_claim_m
    linarith

/-- NS1, phase 2 of Lemma C: from `y ≥ 1/2`, `1 - p_i(y) ≤ (2/3)(3/4)^{2^i}`. -/
theorem nsP_phase2 (i : ℕ) (y : ℝ) (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    1 - nsP^[i] y ≤ 2 / 3 * (3 / 4 : ℝ) ^ (2 ^ i) := by
  have hy0' : 0 ≤ y := by linarith
  have hnsP_iter_range : ∀ k : ℕ, 1 / 2 ≤ nsP^[k] y ∧ nsP^[k] y ≤ 1 := by
    intro k
    induction' k with m ih
    · exact ⟨hy0, hy1⟩
    · rcases ih with ⟨hlo, hhi⟩
      have hpos : 0 ≤ nsP^[m] y := by linarith
      have hnsP_facts := nsP_facts (nsP^[m] y) hpos hhi
      rcases hnsP_facts with ⟨_, _, hx_le_nsP, _, _, _⟩
      have hnsP_lo : 1 / 2 ≤ nsP (nsP^[m] y) := by linarith
      have hnsP_hi : nsP (nsP^[m] y) ≤ 1 := by linarith
      rw [Function.iterate_succ_apply']
      exact ⟨hnsP_lo, hnsP_hi⟩
  induction' i with k ih
  · simp
    linarith
  · rw [Function.iterate_succ_apply']
    rcases hnsP_iter_range k with ⟨hlo_k, hhi_k⟩
    have hpos_k : 0 ≤ nsP^[k] y := by linarith
    have hnsP_facts_k := nsP_facts (nsP^[k] y) hpos_k hhi_k
    rcases hnsP_facts_k with ⟨_, _, _, hineq_k, _, _⟩
    -- hineq_k : 1 - nsP (nsP^[k] y) ≤ 3/2 * (1 - nsP^[k] y)^2
    -- ih : 1 - nsP^[k] y ≤ 2/3 * (3/4)^(2^k)
    -- Let f_k = (3/2) * (1 - nsP^[k] y), then f_k ≥ 0
    -- We have f_{k+1} ≤ f_k^2 and f_0 ≤ 3/4
    -- By induction f_k ≤ (3/4)^(2^k)
    -- Then 1 - nsP^[k] y = (2/3) * f_k ≤ (2/3) * (3/4)^(2^k)
    have h_fk_nonneg : 0 ≤ (3 / 2 : ℝ) * (1 - nsP^[k] y) := by
      nlinarith
    have h_f0_le : (3 / 2 : ℝ) * (1 - y) ≤ 3 / 4 := by
      nlinarith
    -- We need to show: 1 - nsP (nsP^[k] y) ≤ 2/3 * (3/4)^(2^(k+1))
    -- Note: 2^(k+1) = 2 * 2^k, so (3/4)^(2^(k+1)) = ((3/4)^(2^k))^2
    have h_pow_succ : ((3 / 4 : ℝ) ^ (2 ^ (k + 1))) = (((3 / 4 : ℝ) ^ (2 ^ k)) ^ 2) := by
      calc
        (3 / 4 : ℝ) ^ (2 ^ (k + 1)) = (3 / 4 : ℝ) ^ (2 * (2 ^ k)) := by ring
        _ = (3 / 4 : ℝ) ^ ((2 ^ k) * 2) := by rw [mul_comm]
        _ = ((3 / 4 : ℝ) ^ (2 ^ k)) ^ 2 := by rw [pow_mul]
    rw [h_pow_succ]
    -- Now we need: 1 - nsP (nsP^[k] y) ≤ 2/3 * ((3/4)^(2^k))^2
    -- Let f := (3/2) * (1 - nsP^[k] y), g := (3/4)^(2^k)
    -- We know: 1 - nsP (nsP^[k] y) ≤ (3/2) * (1 - nsP^[k] y)^2 = (2/3) * ((3/2)*(1 - nsP^[k] y))^2 = (2/3) * f^2
    -- And by IH: 1 - nsP^[k] y ≤ 2/3 * g, so f = (3/2)*(1 - nsP^[k] y) ≤ g
    -- Since f ≥ 0, g ≥ 0, we have f^2 ≤ g^2
    -- So: 1 - nsP (nsP^[k] y) ≤ (2/3) * f^2 ≤ (2/3) * g^2
    set f := (3 / 2 : ℝ) * (1 - nsP^[k] y) with hf_def
    set g := (3 / 4 : ℝ) ^ (2 ^ k) with hg_def
    have h_f_sq_le : f ^ 2 ≤ g ^ 2 := by
      have h_f_le_g : f ≤ g := by
        -- f = (3/2)*(1 - nsP^[k] y) ≤ (3/2)*(2/3 * g) = g
        -- From ih: 1 - nsP^[k] y ≤ 2/3 * g
        have : 1 - nsP^[k] y ≤ 2 / 3 * g := ih
        nlinarith
      nlinarith
    have h_main : 1 - nsP (nsP^[k] y) ≤ 2 / 3 * f ^ 2 := by
      -- From hineq_k: 1 - nsP x ≤ 3/2 * (1 - x)^2
      -- So 1 - nsP x ≤ 3/2 * (1 - x)^2 = 3/2 * ((2/3)*f)^2 = 3/2 * (4/9) * f^2 = (2/3) * f^2
      have h_eq : (1 - nsP^[k] y) = (2 / 3 : ℝ) * f := by
        dsimp [f]
        ring
      rw [h_eq] at hineq_k
      -- hineq_k : 1 - nsP (nsP^[k] y) ≤ 3/2 * ((2/3) * f)^2
      -- ((2/3) * f)^2 = (4/9) * f^2
      -- 3/2 * (4/9) * f^2 = (12/18) * f^2 = (2/3) * f^2
      nlinarith
    nlinarith

/-- NS1, Lemma C. -/
theorem nsP_count (k J : ℕ) (hJ : nsCount k ≤ J) (x : ℝ) (hx0 : 1 / 2 ^ (k + 1) ≤ x) (hx1 : x ≤ 1) :
    1 - nsP^[J] x ≤ 2 / 3 * (1 / 2 ^ (k + 1)) := by
  -- Let i = J - 2k.  From nsCount k ≤ J we have 2k ≤ J and Nat.clog 2 (3k+3) ≤ i.
  have h2kJ : 2 * k ≤ J := by
    have : 2 * k ≤ nsCount k := Nat.le_add_right _ _
    exact this.trans hJ
  set i := J - 2 * k with hi_def
  have hJ_eq : J = i + 2 * k := by
    rw [hi_def]
    exact (Nat.sub_add_cancel h2kJ).symm
  -- nsP^[J] x = nsP^[i] (nsP^[2k] x)
  have h_iter : nsP^[J] x = nsP^[i] (nsP^[2 * k] x) := by
    rw [hJ_eq, Function.iterate_add_apply]
  rw [h_iter]
  set y := nsP^[2 * k] x with hy_def
  -- y is in [1/2, 1]
  have hy_half : 1 / 2 ≤ y := nsP_phase1 k x hx0 hx1
  -- By nsP_facts, nsP maps [0,1] into [0,1]; iterate to get 0 ≤ y ∧ y ≤ 1
  have hy_facts : 0 ≤ y ∧ y ≤ 1 := by
    have hx0' : 0 ≤ x := by
      have : (0 : ℝ) ≤ 1 / 2 ^ (k + 1) := by norm_num
      exact this.trans hx0
    have h_iter_facts : ∀ n, 0 ≤ nsP^[n] x ∧ nsP^[n] x ≤ 1 := by
      intro n
      induction' n with m ih
      · exact ⟨hx0', hx1⟩
      · rcases ih with ⟨h0, h1⟩
        rw [Function.iterate_succ_apply']
        have h := nsP_facts (nsP^[m] x) h0 h1
        exact ⟨h.1, h.2.1⟩
    exact h_iter_facts (2 * k)
  have hy1 : y ≤ 1 := hy_facts.2
  -- Apply nsP_phase2
  have h_phase2 := nsP_phase2 i y hy_half hy1
  -- h_phase2 : 1 - nsP^[i] y ≤ 2 / 3 * (3 / 4 : ℝ) ^ (2 ^ i)
  -- Now we need to show (3/4)^(2^i) ≤ 1/2^(k+1)
  have h_clog_le_i : Nat.clog 2 (3 * k + 3) ≤ i := by
    have h_nsCount : nsCount k = 2 * k + Nat.clog 2 (3 * k + 3) := rfl
    rw [h_nsCount] at hJ
    rw [hJ_eq] at hJ
    omega
  have h_exp_le : (3 * k + 3 : ℕ) ≤ 2 ^ i := by
    have h_clog_pow : 3 * k + 3 ≤ 2 ^ (Nat.clog 2 (3 * k + 3)) :=
      Nat.le_pow_clog (by norm_num) (3 * k + 3)
    have h_pow_pow : 2 ^ (Nat.clog 2 (3 * k + 3)) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) h_clog_le_i
    exact h_clog_pow.trans h_pow_pow
  have h_base_nonneg : (0 : ℝ) ≤ 3/4 := by norm_num
  have h_base_le_one : (3/4 : ℝ) ≤ 1 := by norm_num
  have h_pow_le : (3/4 : ℝ) ^ (2 ^ i) ≤ (1 / 2 ^ (k + 1) : ℝ) := by
    calc
      (3/4 : ℝ) ^ (2 ^ i) ≤ (3/4 : ℝ) ^ (3 * k + 3) :=
        pow_le_pow_of_le_one h_base_nonneg h_base_le_one h_exp_le
      _ = ((3/4 : ℝ) ^ 3) ^ (k + 1) := by
        rw [show (3 * k + 3 : ℕ) = 3 * (k + 1) by ring, pow_mul]
      _ = (27/64 : ℝ) ^ (k + 1) := by norm_num
      _ ≤ (1/2 : ℝ) ^ (k + 1) := by
        refine pow_le_pow_left₀ (by norm_num) (by norm_num) (k + 1)
      _ = 1 / 2 ^ (k + 1) := by rw [one_div_pow (a := 2)]
  -- Combine everything
  have h_nonneg_two_thirds : (0 : ℝ) ≤ 2/3 := by norm_num
  calc
    1 - nsP^[i] y ≤ 2 / 3 * ((3/4 : ℝ) ^ (2 ^ i)) := h_phase2
    _ ≤ 2 / 3 * (1 / 2 ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left h_pow_le h_nonneg_two_thirds

/-- NS1', Lemma NS-1 (c), scalar form: `0 ≤ t (1 - p_J(t)) ≤ 2^{-k-1}` on `[0, 1]`. -/
theorem nsP_absErr (k J : ℕ) (hJ : nsCount k ≤ J) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ t * (1 - nsP^[J] t) ∧ t * (1 - nsP^[J] t) ≤ 1 / 2 ^ (k + 1) := by
  have h_iter_range : 0 ≤ nsP^[J] t ∧ nsP^[J] t ≤ 1 := by
    refine Nat.rec ?base ?step J
    · exact ⟨ht0, ht1⟩
    · intro j ih
      rw [Function.iterate_succ_apply']
      have h := nsP_facts (nsP^[j] t) ih.1 ih.2
      exact ⟨h.1, h.2.1⟩
  have h_left : 0 ≤ t * (1 - nsP^[J] t) := by
    nlinarith
  have h_right : t * (1 - nsP^[J] t) ≤ 1 / 2 ^ (k + 1) := by
    by_cases h : t < 1 / 2 ^ (k + 1)
    · -- t < 1/2^(k+1)
      have h_mul : t * (1 - nsP^[J] t) ≤ t := by
        nlinarith
      nlinarith
    · -- 1/2^(k+1) ≤ t
      have hx0 : 1 / 2 ^ (k + 1) ≤ t := by linarith
      have h_nsP_count := nsP_count k J hJ t hx0 ht1
      have h_mul : t * (1 - nsP^[J] t) ≤ 1 - nsP^[J] t := by
        nlinarith
      have h_bound : ((2 : ℝ) / 3) * ((1 : ℝ) / ((2 : ℝ) ^ (k + 1))) ≤ (1 : ℝ) / ((2 : ℝ) ^ (k + 1)) := by
        have h := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) / 3 ≤ (1 : ℝ))
          (by positivity : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ (k + 1)))
        simpa [one_mul] using h
      nlinarith
  exact And.intro h_left h_right

/-- NS1'', Lemma NS-1 (c) scaled by `c₀`: the branch `g(y) = y p_J(y/c₀)` lies within `e` below `|y|` on
`[-c₀, c₀]` when `c₀ 2^{-k} ≤ 2 e`. -/
theorem nsG_bounds (k J : ℕ) (hJ : nsCount k ≤ J) (c0 e : ℝ) (hc0 : 0 < c0) (hk : c0 / 2 ^ k ≤ 2 * e) (y : ℝ)
    (hy : |y| ≤ c0) : |y| - e ≤ y * nsP^[J] (y / c0) ∧ y * nsP^[J] (y / c0) ≤ |y| := by
  set t := |y| / c0 with ht
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) (by linarith)
  have ht1 : t ≤ 1 := (div_le_one hc0).mpr hy
  have h_nsP_odd : ∀ x : ℝ, nsP (-x) = -nsP x := by
    intro x
    dsimp [nsP]
    ring
  have h_nsP_iter_odd : ∀ (n : ℕ) (x : ℝ), nsP^[n] (-x) = -nsP^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih x, h_nsP_odd]
  have h_eq : y * nsP^[J] (y / c0) = |y| * nsP^[J] t := by
    dsimp [t]
    by_cases hy_nonneg : 0 ≤ y
    · have h_abs_eq : |y| = y := abs_of_nonneg hy_nonneg
      simp [h_abs_eq]
    · have hy_neg : y < 0 := by linarith
      have h_abs_eq : |y| = -y := abs_of_neg hy_neg
      have h_div_eq : y / c0 = -((-y) / c0) := by simp [neg_div, neg_neg]
      calc
        y * nsP^[J] (y / c0) = y * nsP^[J] (-((-y) / c0)) := by rw [h_div_eq]
        _ = y * (-nsP^[J] ((-y) / c0)) := by rw [h_nsP_iter_odd J ((-y) / c0)]
        _ = (-y) * nsP^[J] ((-y) / c0) := by ring
        _ = |y| * nsP^[J] ((-y) / c0) := by rw [h_abs_eq]
        _ = |y| * nsP^[J] (|y| / c0) := by rw [h_abs_eq]
  have h_nsP_iter_bounds : ∀ n, 0 ≤ nsP^[n] t ∧ nsP^[n] t ≤ 1 := by
    intro n
    induction' n with m ih
    · exact ⟨ht0, ht1⟩
    · rcases ih with ⟨h_nonneg, h_le_one⟩
      have h_facts := nsP_facts (nsP^[m] t) h_nonneg h_le_one
      rw [Function.iterate_succ_apply']
      exact ⟨h_facts.1, h_facts.2.1⟩
  have h_absErr := nsP_absErr k J hJ t ht0 ht1
  rcases h_absErr with ⟨_, h_bound⟩
  have h_yt : |y| = c0 * t := by
    dsimp [t]
    field_simp [hc0.ne.symm]
  have h_first : |y| - e ≤ |y| * nsP^[J] t := by
    have h_diff : |y| - |y| * nsP^[J] t = c0 * (t * (1 - nsP^[J] t)) := by
      rw [h_yt]
      ring
    have h_bound' : c0 * (t * (1 - nsP^[J] t)) ≤ e := by
      calc
        c0 * (t * (1 - nsP^[J] t)) ≤ c0 * (1 / 2 ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h_bound (by linarith)
        _ = (c0 / 2 ^ k) / 2 := by ring
        _ = (c0 / 2 ^ k) * (1/2) := by ring
        _ ≤ (2 * e) * (1/2) := mul_le_mul_of_nonneg_right hk (by norm_num)
        _ = e := by ring
    linarith
  have h_second : |y| * nsP^[J] t ≤ |y| := by
    have h_iter_le_one := (h_nsP_iter_bounds J).2
    have := mul_le_mul_of_nonneg_left h_iter_le_one (abs_nonneg y)
    simpa [mul_one] using this
  rw [h_eq]
  exact ⟨h_first, h_second⟩

/-- NS3', the scalar step of Lemma N-S: with `g_a`, `g_b` within `e` below `|l - a - e|`, `|l - b + e|`,
`φ = m + (g_a - g_b)/2` lies in `[a + e/2, b - e/2]` and within `(3/2) e` of the clamp of `l` to `[a, b]`. -/
theorem nsPhi_bounds (a b e l ga gb : ℝ) (hab : a < b) (he : 0 < e) (hew : e < cnHalf a b)
    (hga : |l - (a + e)| - e ≤ ga ∧ ga ≤ |l - (a + e)|) (hgb : |l - (b - e)| - e ≤ gb ∧ gb ≤ |l - (b - e)|) :
    a + e / 2 ≤ cnMid a b + (ga - gb) / 2 ∧ cnMid a b + (ga - gb) / 2 ≤ b - e / 2 ∧
      |cnMid a b + (ga - gb) / 2 - max a (min b l)| ≤ 3 / 2 * e := by
  rcases hga with ⟨hga_low, hga_high⟩
  rcases hgb with ⟨hgb_low, hgb_high⟩
  have h_ae_lt_be : a + e < b - e := by
    have hcnHalf : cnHalf a b = (b - a) / 2 := rfl
    linarith
  set m := cnMid a b with hm
  set φ := m + (ga - gb) / 2 with hφ
  set cl' := m + (|l - (a + e)| - |l - (b - e)|) / 2 with hcl'
  have hφ_cl'_low : cl' - e / 2 ≤ φ := by
    rw [hφ, hcl', hm]
    linarith
  have hφ_cl'_high : φ ≤ cl' + e / 2 := by
    rw [hφ, hcl', hm]
    linarith
  have h_abs_φ_cl' : |φ - cl'| ≤ e / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h_cl'_range : a + e ≤ cl' ∧ cl' ≤ b - e := by
    by_cases h1 : l ≤ a + e
    · have habs1 : |l - (a + e)| = (a + e) - l := by
        have h := abs_of_nonpos (show l - (a + e) ≤ 0 from by linarith)
        rw [h]
        ring
      have habs2 : |l - (b - e)| = (b - e) - l := by
        have h := abs_of_nonpos (show l - (b - e) ≤ 0 from by linarith)
        rw [h]
        ring
      have hcl'_val : cl' = a + e := by
        rw [hcl', hm, habs1, habs2]
        dsimp [cnMid]
        ring_nf
      rw [hcl'_val]
      constructor <;> linarith
    · by_cases h2 : l ≤ b - e
      · have habs1 : |l - (a + e)| = l - (a + e) :=
          abs_of_nonneg (show 0 ≤ l - (a + e) from by linarith)
        have habs2 : |l - (b - e)| = (b - e) - l := by
          have h := abs_of_nonpos (show l - (b - e) ≤ 0 from by linarith)
          rw [h]
          ring
        have hcl'_val : cl' = l := by
          rw [hcl', hm, habs1, habs2]
          dsimp [cnMid]
          ring_nf
        rw [hcl'_val]
        constructor <;> linarith
      · have habs1 : |l - (a + e)| = l - (a + e) :=
          abs_of_nonneg (show 0 ≤ l - (a + e) from by linarith)
        have habs2 : |l - (b - e)| = l - (b - e) :=
          abs_of_nonneg (show 0 ≤ l - (b - e) from by linarith)
        have hcl'_val : cl' = b - e := by
          rw [hcl', hm, habs1, habs2]
          dsimp [cnMid]
          ring_nf
        rw [hcl'_val]
        constructor <;> linarith
  have h_left : a + e / 2 ≤ φ := by
    linarith
  have h_mid : φ ≤ b - e / 2 := by
    linarith
  have h_abs_cl_max : |cl' - max a (min b l)| ≤ e := by
    by_cases h1 : l ≤ a + e
    · have habs1 : |l - (a + e)| = (a + e) - l := by
        have h := abs_of_nonpos (show l - (a + e) ≤ 0 from by linarith)
        rw [h]
        ring
      have habs2 : |l - (b - e)| = (b - e) - l := by
        have h := abs_of_nonpos (show l - (b - e) ≤ 0 from by linarith)
        rw [h]
        ring
      have hcl'_val : cl' = a + e := by
        rw [hcl', hm, habs1, habs2]
        dsimp [cnMid]
        ring_nf
      rw [hcl'_val]
      have hmin : min b l = l := min_eq_right (show l ≤ b from by linarith)
      rw [hmin]
      by_cases hla : l ≤ a
      · have hmax : max a l = a := max_eq_left hla
        rw [hmax]
        have : (a + e) - a = e := by ring
        rw [this, abs_of_pos he]
      · have hmax : max a l = l := max_eq_right (show a ≤ l from by linarith)
        rw [hmax]
        have h_nonneg : 0 ≤ (a + e) - l := by linarith
        have h_le_e : (a + e) - l ≤ e := by linarith
        rw [abs_of_nonneg h_nonneg]
        exact h_le_e
    · by_cases h2 : l ≤ b - e
      · have habs1 : |l - (a + e)| = l - (a + e) :=
          abs_of_nonneg (show 0 ≤ l - (a + e) from by linarith)
        have habs2 : |l - (b - e)| = (b - e) - l := by
          have h := abs_of_nonpos (show l - (b - e) ≤ 0 from by linarith)
          rw [h]
          ring
        have hcl'_val : cl' = l := by
          rw [hcl', hm, habs1, habs2]
          dsimp [cnMid]
          ring_nf
        rw [hcl'_val]
        have hmin : min b l = l := min_eq_right (show l ≤ b from by linarith)
        rw [hmin]
        have hmax : max a l = l := max_eq_right (show a ≤ l from by linarith)
        rw [hmax]
        rw [sub_self, abs_zero]
        exact he.le
      · have habs1 : |l - (a + e)| = l - (a + e) :=
          abs_of_nonneg (show 0 ≤ l - (a + e) from by linarith)
        have habs2 : |l - (b - e)| = l - (b - e) :=
          abs_of_nonneg (show 0 ≤ l - (b - e) from by linarith)
        have hcl'_val : cl' = b - e := by
          rw [hcl', hm, habs1, habs2]
          dsimp [cnMid]
          ring_nf
        rw [hcl'_val]
        by_cases hl_b : l ≤ b
        · have hmin : min b l = l := min_eq_right hl_b
          rw [hmin]
          have hmax : max a l = l := max_eq_right (show a ≤ l from by linarith)
          rw [hmax]
          have h_nonpos : (b - e) - l ≤ 0 := by linarith
          rw [abs_of_nonpos h_nonpos]
          have : -( (b - e) - l) = l - b + e := by ring
          rw [this]
          linarith
        · have hmin : min b l = b := min_eq_left (show b ≤ l from by linarith)
          rw [hmin]
          have hmax : max a b = b := max_eq_right (show a ≤ b from by linarith)
          rw [hmax]
          have : (b - e) - b = -e := by ring
          rw [this, abs_neg, abs_of_pos he]
  have h_third : |φ - max a (min b l)| ≤ 3 / 2 * e := by
    have h_tri : |φ - max a (min b l)| ≤ |φ - cl'| + |cl' - max a (min b l)| := by
      calc
        |φ - max a (min b l)| = |(φ - cl') + (cl' - max a (min b l))| := by ring
        _ ≤ |φ - cl'| + |cl' - max a (min b l)| := abs_add_le _ _
    have h_sum : |φ - cl'| + |cl' - max a (min b l)| ≤ e / 2 + e := by
      have h1 : |φ - cl'| ≤ e / 2 := h_abs_φ_cl'
      have h2 : |cl' - max a (min b l)| ≤ e := h_abs_cl_max
      linarith
    have h_sum' : e / 2 + e = 3 / 2 * e := by ring
    linarith
  exact And.intro h_left (And.intro h_mid h_third)

/-- NS2: the iteration is the scalar one on the spectrum. -/
theorem clampNSRoot_eq_cfc (a b c : ℝ) (J : ℕ) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsHermitian) :
    clampNSRoot a b c J S = cfc (fun l => (l - c) * nsP^[J] ((l - c) / cnC0 d a b)) S := by
  set c0 := cnC0 d a b with hc0
  have h_nsIter_eq : ∀ j : ℕ, nsIter ((c0)⁻¹ • (S - c • (1 : Matrix (Fin d) (Fin d) ℝ))) j =
      cfc (fun l => nsP^[j] ((l - c) / c0)) S := by
    intro j
    induction' j with j ih
    · -- j = 0
      simp [nsIter, Function.iterate_zero]
      calc
        (c0)⁻¹ • (S - c • (1 : Matrix (Fin d) (Fin d) ℝ))
            = (c0)⁻¹ • S - (c0)⁻¹ • (c • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
          rw [smul_sub]
        _ = (c0)⁻¹ • S - ((c0)⁻¹ * c) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
          rw [smul_smul]
        _ = (c0)⁻¹ • S + (-((c0)⁻¹ * c)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
          rw [sub_eq_add_neg, neg_smul]
        _ = cfc (fun x : ℝ => (c0)⁻¹ * x + (-((c0)⁻¹ * c))) S := by
          rw [cfc_affine_of_isHermitian S hS (c0)⁻¹ (-((c0)⁻¹ * c))]
        _ = cfc (fun l => ((l - c) / c0)) S := by
          refine congrArg (cfc · S) (funext fun x => ?_)
          ring
    · -- j → j+1
      rw [nsIter, ih]
      set f := fun l : ℝ => nsP^[j] ((l - c) / c0) with hf
      have h_nsP : ∀ u : ℝ, nsP u = (1/2 : ℝ) * (u * (3 - u * u)) := by
        intro u; dsimp [nsP]; ring
      have h_cfc_one : cfc (fun _ : ℝ => (1 : ℝ)) S = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        calc
          cfc (fun _ : ℝ => (1 : ℝ)) S = cfc (fun x : ℝ => (0 : ℝ) * x + (1 : ℝ)) S := by
            refine congrArg (cfc · S) (funext fun x => ?_)
            simp
          _ = (0 : ℝ) • S + (1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) :=
            cfc_affine_of_isHermitian S hS (0 : ℝ) (1 : ℝ)
          _ = (1 : Matrix (Fin d) (Fin d) ℝ) := by simp
      have h_cfc_three_sub : cfc (fun l : ℝ => (3 : ℝ) - f l * f l) S =
          (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - cfc f S * cfc f S := by
        calc
          cfc (fun l : ℝ => (3 : ℝ) - f l * f l) S
              = cfc (fun l : ℝ => (3 : ℝ) * ((fun _ : ℝ => (1 : ℝ)) l) + (-1) * (f l * f l)) S := by
            refine congrArg (cfc · S) (funext fun x => ?_)
            ring
          _ = (3 : ℝ) • cfc (fun _ : ℝ => (1 : ℝ)) S + (-1) • cfc (fun l : ℝ => f l * f l) S :=
            cfc_lin_of_isHermitian S hS (fun _ => (1 : ℝ)) (fun l => f l * f l) (3 : ℝ) (-1)
          _ = (3 : ℝ) • (cfc (fun _ : ℝ => (1 : ℝ)) S) + (-1 : ℝ) • (cfc f S * cfc f S) :=
            congrArg (fun t => (3 : ℝ) • (cfc (fun _ : ℝ => (1 : ℝ)) S) + (-1 : ℝ) • t)
              (cfc_mul_of_isHermitian S hS f f)
          _ = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) + (-1 : ℝ) • (cfc f S * cfc f S) := by
            rw [h_cfc_one]
          _ = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - cfc f S * cfc f S := by
            rw [sub_eq_add_neg, neg_smul, one_smul]
      calc
        (1/2 : ℝ) • (cfc f S * ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - cfc f S * cfc f S))
            = (1/2 : ℝ) • (cfc f S * cfc (fun l : ℝ => (3 : ℝ) - f l * f l) S) := by
          rw [h_cfc_three_sub]
        _ = (1/2 : ℝ) • cfc (fun l : ℝ => f l * ((3 : ℝ) - f l * f l)) S := by
          rw [cfc_mul_of_isHermitian S hS f (fun l => (3 : ℝ) - f l * f l)]
        _ = cfc (fun l : ℝ => (1/2 : ℝ) * (f l * ((3 : ℝ) - f l * f l))) S := by
          have := cfc_lin_of_isHermitian S hS (fun l => f l * ((3 : ℝ) - f l * f l)) (fun _ => (0 : ℝ)) (1/2 : ℝ) (0 : ℝ)
          -- this : cfc (fun x => (1/2) * g x + 0 * 0) S = (1/2) • cfc g S + 0 • cfc (fun _ => 0) S
          -- we want: (1/2) • cfc g S = cfc (fun x => (1/2) * g x) S
          -- which is the reverse direction after simplification
          calc
            (1/2 : ℝ) • cfc (fun l : ℝ => f l * ((3 : ℝ) - f l * f l)) S
                = (1/2 : ℝ) • cfc (fun l : ℝ => f l * ((3 : ℝ) - f l * f l)) S + (0 : ℝ) • cfc (fun _ : ℝ => (0 : ℝ)) S := by
              simp [add_zero]
            _ = cfc (fun l : ℝ => (1/2 : ℝ) * (f l * ((3 : ℝ) - f l * f l)) + (0 : ℝ) * ((fun _ : ℝ => (0 : ℝ)) l)) S := by
              rw [cfc_lin_of_isHermitian S hS (fun l => f l * ((3 : ℝ) - f l * f l)) (fun _ => (0 : ℝ)) (1/2 : ℝ) (0 : ℝ)]
            _ = cfc (fun l : ℝ => (1/2 : ℝ) * (f l * ((3 : ℝ) - f l * f l))) S := by
              refine congrArg (cfc · S) (funext fun x => ?_)
              simp
        _ = cfc (fun l => nsP (f l)) S := by
          refine congrArg (cfc · S) (funext fun x => ?_)
          rw [h_nsP]
        _ = cfc (fun l => nsP^[j+1] ((l - c) / c0)) S := by
          dsimp [f]
          refine congrArg (cfc · S) (funext fun x => ?_)
          calc
            nsP (nsP^[j] ((x - c) / c0)) = nsP^[j+1] ((x - c) / c0) := by rw [Function.iterate_succ_apply']
            _ = nsP^[j] (nsP ((x - c) / c0)) := by rw [Function.iterate_succ_apply]
  -- main result
  have h_sub_eq : (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)) = cfc (fun l => l - c) S := by
    calc
      (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)) = (1 : ℝ) • S + (-c) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        rw [sub_eq_add_neg, neg_smul, one_smul]
      _ = cfc (fun x : ℝ => (1 : ℝ) * x + (-c)) S := by
        rw [cfc_affine_of_isHermitian S hS (1 : ℝ) (-c)]
      _ = cfc (fun l => l - c) S := by
        refine congrArg (cfc · S) (funext fun x => ?_)
        ring
  calc
    clampNSRoot a b c J S
        = (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)) *
          nsIter ((c0)⁻¹ • (S - c • (1 : Matrix (Fin d) (Fin d) ℝ))) J := rfl
    _ = (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)) *
          cfc (fun l => nsP^[J] ((l - c) / c0)) S := by rw [h_nsIter_eq J]
    _ = cfc (fun l => l - c) S * cfc (fun l => nsP^[J] ((l - c) / c0)) S := by
      rw [h_sub_eq]
    _ = cfc (fun l => (l - c) * nsP^[J] ((l - c) / c0)) S := by
      rw [cfc_mul_of_isHermitian S hS (fun l => l - c) (fun l => nsP^[J] ((l - c) / c0))]


/-- NS2': CLAMP-NS is a function of `S'` by the functional calculus. -/
theorem clampNSMat_eq_cfc (a b e : ℝ) (J : ℕ) (Y : Matrix (Fin d) (Fin d) ℝ) (hS : (clipSym a b Y).IsHermitian) :
    clampNSMat a b e J Y = cfc (fun l => cnMid a b + ((l - (a + e)) * nsP^[J] ((l - (a + e)) / cnC0 d a b) -
      (l - (b - e)) * nsP^[J] ((l - (b - e)) / cnC0 d a b)) / 2) (clipSym a b Y) := by
  set S := clipSym a b Y with hSdef
  have hS_herm : S.IsHermitian := hS
  set f := fun (l : ℝ) => (l - (a + e)) * nsP^[J] ((l - (a + e)) / cnC0 d a b) with hf
  set g := fun (l : ℝ) => (l - (b - e)) * nsP^[J] ((l - (b - e)) / cnC0 d a b) with hg
  unfold clampNSMat
  rw [clampNSRoot_eq_cfc a b (a + e) J S hS_herm, clampNSRoot_eq_cfc a b (b - e) J S hS_herm]
  -- LHS: cnMid a b • 1 + (1/2) • (cfc f S - cfc g S)
  -- RHS: cfc (fun l => cnMid a b + (f l - g l) / 2) S
  have h_smul_sub : cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + (1/2 : ℝ) • (cfc f S - cfc g S) =
      cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + ((1/2 : ℝ) • cfc f S + (-1/2 : ℝ) • cfc g S) := by
    rw [smul_sub, sub_eq_add_neg, ← neg_smul (1/2 : ℝ) (cfc g S)]
    have h : (-(1/2 : ℝ)) = ((-1 : ℝ)/2) := by ring
    rw [h]
  have h_rhs : cfc (fun l => cnMid a b + (f l - g l) / 2) S =
      cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + ((1/2 : ℝ) • cfc f S + (-1/2 : ℝ) • cfc g S) := by
    calc
      cfc (fun l => cnMid a b + (f l - g l) / 2) S
          = cfc (fun l => cnMid a b + ((1/2 : ℝ) * f l + (-1/2 : ℝ) * g l)) S := by
        refine congrArg (fun h => cfc h S) (funext fun l => ?_)
        ring
      _ = cfc (fun l => (1 : ℝ) * (cnMid a b) + (1 : ℝ) * ((1/2 : ℝ) * f l + (-1/2 : ℝ) * g l)) S := by
        refine congrArg (fun h => cfc h S) (funext fun l => ?_)
        ring
      _ = (1 : ℝ) • cfc (fun _ => cnMid a b) S + (1 : ℝ) • cfc (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) S := by
        rw [cfc_lin_of_isHermitian S hS_herm (fun _ => cnMid a b) (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) (1 : ℝ) (1 : ℝ)]
      _ = cfc (fun _ => cnMid a b) S + cfc (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) S := by simp
      _ = cfc (fun x => (0 : ℝ) * x + cnMid a b) S + cfc (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) S := by
        refine congrArg (fun h => cfc h S + _) (funext fun x => ?_)
        simp
      _ = ((0 : ℝ) • S + cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ)) + cfc (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) S := by
        rw [cfc_affine_of_isHermitian S hS_herm 0 (cnMid a b)]
      _ = cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + cfc (fun l => (1/2 : ℝ) * f l + (-1/2 : ℝ) * g l) S := by simp
      _ = cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + ((1/2 : ℝ) • cfc f S + (-1/2 : ℝ) • cfc g S) := by
        rw [cfc_lin_of_isHermitian S hS_herm f g (1/2 : ℝ) (-1/2 : ℝ)]
  rw [h_smul_sub, h_rhs]

/-- NS3, Lemma N-S (i), read as the interface field `bounds`. -/
theorem clampNS_bounds (d : ℕ) (a b e : ℝ) (Y : Matrix (Fin d) (Fin d) ℝ) (hab : a < b) (he : 0 < e)
    (hew : e < cnHalf a b) : InBand a b (clampNSMat a b e (cnsJ d a b e) Y) := by
  have hab_le : a ≤ b := by linarith
  have hcnMid_ge_a : a ≤ cnMid a b := by
    unfold cnMid; linarith
  have hcnMid_le_b : cnMid a b ≤ b := by
    unfold cnMid; linarith
  -- Get eigenvalue bounds from clipSym_spec for both a+e and b-e
  have hae_ge_a : a ≤ a + e := by linarith
  have hae_le_b : a + e ≤ b := by
    unfold AdversarialBco.Conj1Arith.cnHalf at hew
    linarith
  have hspec_ae := AdversarialBco.Conj1Arith.clipSym_spec a b (a + e) hab_le hae_ge_a hae_le_b Y
  rcases hspec_ae with ⟨hS_ae, hbound_ae⟩
  have hbe_ge_a : a ≤ b - e := by
    unfold AdversarialBco.Conj1Arith.cnHalf at hew
    linarith
  have hbe_le_b : b - e ≤ b := by linarith
  have hspec_be := AdversarialBco.Conj1Arith.clipSym_spec a b (b - e) hab_le hbe_ge_a hbe_le_b Y
  rcases hspec_be with ⟨hS_be, hbound_be⟩
  -- Use hS_ae for the cfc_inBand_of_isHermitian call
  have h_eq := AdversarialBco.Conj1Arith.clampNSMat_eq_cfc a b e (AdversarialBco.Conj1Arith.cnsJ d a b e) Y hS_ae
  rw [h_eq]
  apply AdversarialBco.Conj1Arith.cfc_inBand_of_isHermitian (clipSym a b Y) hS_ae _ a b
  intro i
  let c0 := AdversarialBco.Conj1Arith.cnC0 d a b
  let k := AdversarialBco.Conj1Arith.cnK d a b e
  let J := AdversarialBco.Conj1Arith.cnsJ d a b e
  have hJ : AdversarialBco.Conj1Arith.nsCount k ≤ J := by
    unfold J AdversarialBco.Conj1Arith.cnsJ
    rfl
  have hc0_pos : 0 < c0 := by
    unfold c0 AdversarialBco.Conj1Arith.cnC0 AdversarialBco.Conj1Arith.cnR0 AdversarialBco.Conj1Arith.cnHalf
    have hpos : 0 < b - a := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hk_bound : c0 / ((2 : ℝ) ^ k) ≤ 2 * e := by
    unfold c0 k
    exact AdversarialBco.Conj1Arith.cnK_spec a b e hab he
  -- Now we need to prove the hf condition: a ≤ f(hS_ae.eigenvalues i) ≤ b
  -- We have hbound_ae i : |hS_ae.eigenvalues i - (a + e)| ≤ c0
  -- We have hbound_be i : |hS_be.eigenvalues i - (b - e)| ≤ c0
  -- Use proof_irrel to relate hS_be.eigenvalues to hS_ae.eigenvalues
  have h_eq_eigen_be : hS_be.eigenvalues i = hS_ae.eigenvalues i := by
    have h_irrel : hS_be = hS_ae := proof_irrel hS_be hS_ae
    rw [h_irrel]
  have hy1 : |hS_ae.eigenvalues i - (a + e)| ≤ c0 := hbound_ae i
  have hy2 : |hS_ae.eigenvalues i - (b - e)| ≤ c0 := by
    rw [h_eq_eigen_be]
    exact hbound_be i
  -- Apply nsG_bounds
  set y1 := hS_ae.eigenvalues i - (a + e) with hy1_def
  set y2 := hS_ae.eigenvalues i - (b - e) with hy2_def
  set ga := y1 * (AdversarialBco.Conj1Arith.nsP^[J] (y1 / c0)) with hga_def
  set gb := y2 * (AdversarialBco.Conj1Arith.nsP^[J] (y2 / c0)) with hgb_def
  have hga_bound : |y1| - e ≤ ga ∧ ga ≤ |y1| := by
    rw [hga_def]
    exact AdversarialBco.Conj1Arith.nsG_bounds k J hJ c0 e hc0_pos hk_bound y1 hy1
  have hgb_bound : |y2| - e ≤ gb ∧ gb ≤ |y2| := by
    rw [hgb_def]
    exact AdversarialBco.Conj1Arith.nsG_bounds k J hJ c0 e hc0_pos hk_bound y2 hy2
  -- Apply nsPhi_bounds
  have hphi := AdversarialBco.Conj1Arith.nsPhi_bounds a b e (hS_ae.eigenvalues i) ga gb
    hab he hew hga_bound hgb_bound
  rcases hphi with ⟨hlo, hhi, _⟩
  -- hlo : a + e / 2 ≤ cnMid a b + (ga - gb) / 2
  -- hhi : cnMid a b + (ga - gb) / 2 ≤ b - e / 2
  -- Now rewrite ga and gb back
  rw [hga_def, hgb_def] at hlo hhi
  -- Now hlo : a + e / 2 ≤ cnMid a b + ((y1 * nsP^[J] (y1 / c0)) - (y2 * nsP^[J] (y2 / c0))) / 2
  -- hhi : cnMid a b + ((y1 * nsP^[J] (y1 / c0)) - (y2 * nsP^[J] (y2 / c0))) / 2 ≤ b - e / 2
  rw [hy1_def, hy2_def] at hlo hhi
  have hlo' : a ≤ cnMid a b + (((hS_ae.eigenvalues i - (a + e)) *
    (AdversarialBco.Conj1Arith.nsP^[J] ((hS_ae.eigenvalues i - (a + e)) / c0)) -
    ((hS_ae.eigenvalues i - (b - e)) *
    (AdversarialBco.Conj1Arith.nsP^[J] ((hS_ae.eigenvalues i - (b - e)) / c0)))) / 2) := by
    linarith
  have hhi' : cnMid a b + (((hS_ae.eigenvalues i - (a + e)) *
    (AdversarialBco.Conj1Arith.nsP^[J] ((hS_ae.eigenvalues i - (a + e)) / c0)) -
    ((hS_ae.eigenvalues i - (b - e)) *
    (AdversarialBco.Conj1Arith.nsP^[J] ((hS_ae.eigenvalues i - (b - e)) / c0)))) / 2) ≤ b := by
    linarith
  exact ⟨hlo', hhi'⟩

/-- NS4a, Lemma N-S (ii): `|T' - cl(S')|_F ≤ (3/2) e d^{1/2}`. -/
theorem clampNSMat_dist (d : ℕ) (a b e : ℝ) (Y : Matrix (Fin d) (Fin d) ℝ) (hab : a < b) (he : 0 < e)
    (hew : e < cnHalf a b) :
    frobNorm (clampNSMat a b e (cnsJ d a b e) Y - cfc (fun x : ℝ => max a (min b x)) (clipSym a b Y)) ≤
      3 / 2 * e * Real.sqrt d := by
  have hab_le : a ≤ b := le_of_lt hab
  have ha_le_ae : a ≤ a + e := by linarith
  have hae_le_b : a + e ≤ b := by
    have : cnHalf a b = (b - a) / 2 := rfl
    dsimp [cnHalf] at hew
    linarith
  have hb_minus_e_le_b : b - e ≤ b := by linarith
  have ha_le_b_minus_e : a ≤ b - e := by
    have : cnHalf a b = (b - a) / 2 := rfl
    dsimp [cnHalf] at hew
    linarith
  rcases clipSym_spec a b (a + e) hab_le ha_le_ae hae_le_b Y with ⟨hS1, hS_bound1⟩
  rcases clipSym_spec a b (b - e) hab_le ha_le_b_minus_e hb_minus_e_le_b Y with ⟨hS2, hS_bound2⟩
  have hS : (clipSym a b Y).IsHermitian := hS1
  have hS_bound_ae : ∀ i, |hS1.eigenvalues i - (a + e)| ≤ cnC0 d a b := hS_bound1
  have hS_bound_be : ∀ i, |hS2.eigenvalues i - (b - e)| ≤ cnC0 d a b := hS_bound2
  have h_eq : clampNSMat a b e (cnsJ d a b e) Y =
      cfc (fun l => cnMid a b + ((l - (a + e)) * nsP^[cnsJ d a b e] ((l - (a + e)) / cnC0 d a b) -
        (l - (b - e)) * nsP^[cnsJ d a b e] ((l - (b - e)) / cnC0 d a b)) / 2) (clipSym a b Y) := by
    rw [clampNSMat_eq_cfc a b e (cnsJ d a b e) Y hS]
  rw [h_eq]
  apply frobNorm_cfc_sub_le (clipSym a b Y) hS _ _ (3 / 2 * e)
  intro i
  set l := hS.eigenvalues i with hl
  set k := cnK d a b e with hk_def
  set J := cnsJ d a b e with hJ_def
  set c0 := cnC0 d a b with hc0_def
  have hc0_pos : 0 < c0 := by
    dsimp [c0, cnC0, cnR0, cnHalf]
    have hhalf : 0 < (b - a) / 2 := by linarith
    have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    nlinarith
  have hcnK_spec : c0 / 2 ^ k ≤ 2 * e := cnK_spec a b e hab he
  have hnsCount : nsCount k ≤ J := by
    dsimp [J, hJ_def, cnsJ, k, hk_def, nsCount]
    rfl
  have hS_bound_ae_i : |l - (a + e)| ≤ c0 := by
    simpa [hl] using hS_bound_ae i
  have hS_bound_be_i : |l - (b - e)| ≤ c0 := by
    simpa [hl] using hS_bound_be i
  set ga := (l - (a + e)) * nsP^[J] ((l - (a + e)) / c0) with hga_def
  set gb := (l - (b - e)) * nsP^[J] ((l - (b - e)) / c0) with hgb_def
  have hga := nsG_bounds k J hnsCount c0 e hc0_pos hcnK_spec (l - (a + e)) hS_bound_ae_i
  have hgb := nsG_bounds k J hnsCount c0 e hc0_pos hcnK_spec (l - (b - e)) hS_bound_be_i
  rcases hga with ⟨hga_low, hga_high⟩
  rcases hgb with ⟨hgb_low, hgb_high⟩
  have hphi := nsPhi_bounds a b e l ga gb hab he hew ⟨hga_low, hga_high⟩ ⟨hgb_low, hgb_high⟩
  rcases hphi with ⟨_, _, hphi_bound⟩
  simpa [hl, hga_def, hgb_def] using hphi_bound

/-- NS4, the interface field `near` (from NS4a, `clampExact_nonexp` and the triangle inequality). -/
theorem clampNS_near (d : ℕ) (a b e : ℝ) (Y Z : Matrix (Fin d) (Fin d) ℝ) (hab : a < b) (he : 0 < e)
    (hew : e < cnHalf a b) (hZ : InBand a b Z) :
    frobNorm (clampNSMat a b e (cnsJ d a b e) Y - Z) ≤ frobNorm (Y - Z) + 2 * e * Real.sqrt d := by
  set B := cfc (fun x : ℝ => max a (min b x)) (clipSym a b Y) with hB
  have h1 : frobNorm (clampNSMat a b e (cnsJ d a b e) Y - Z) ≤
      frobNorm (clampNSMat a b e (cnsJ d a b e) Y - B) + frobNorm (B - Z) :=
    frobNorm_sub_le_add (clampNSMat a b e (cnsJ d a b e) Y) B Z
  have h2 : frobNorm (clampNSMat a b e (cnsJ d a b e) Y - B) ≤ 3 / 2 * e * Real.sqrt d := by
    simpa [hB] using clampNSMat_dist d a b e Y hab he hew
  have h3 : frobNorm (B - Z) ≤ frobNorm (Y - Z) := by
    simpa [hB] using clampExact_nonexp a b hab Y Z hZ
  have h4 : 3 / 2 * e * Real.sqrt d ≤ 2 * e * Real.sqrt d := by
    nlinarith [Real.sqrt_nonneg (d : ℝ), he]
  linarith

/-- NS5, the interface field `meas`: every entry is a polynomial in the entries of `S'`, itself measurable. -/
theorem clampNS_meas (d : ℕ) (a b e : ℝ) :
    Measurable fun Y : Fin d → Fin d → ℝ => (clampNSMat a b e (cnsJ d a b e) (Matrix.of Y) : Fin d → Fin d → ℝ) := by
  let J := cnsJ d a b e
  -- Step 1: frobNorm is continuous, hence measurable
  have h_frobNorm_cont : Continuous (frobNorm : Matrix (Fin d) (Fin d) ℝ → ℝ) := by
    unfold frobNorm
    refine Continuous.sqrt ?_
    refine continuous_finset_sum _ fun i _ => ?_
    refine continuous_finset_sum _ fun j _ => ?_
    have h_entry : Continuous fun (W : Matrix (Fin d) (Fin d) ℝ) => W i j :=
      (continuous_apply j).comp (continuous_apply i)
    have h_sq_eq : (fun (W : Matrix (Fin d) (Fin d) ℝ) => W i j) ^ 2 = fun (W : Matrix (Fin d) (Fin d) ℝ) => (W i j) ^ 2 := by
      ext W; simp [sq]
    simpa [h_sq_eq] using h_entry.pow 2
  have h_frobNorm_meas : Measurable frobNorm := h_frobNorm_cont.measurable
  -- Step 2: frobClip R is measurable (using Measurable.ite)
  have h_frobClip_meas (R : ℝ) : Measurable (frobClip R : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
    unfold frobClip
    refine Measurable.ite ?_ ?_ ?_
    · exact h_frobNorm_meas (measurableSet_Ioi (a := R))
    · have h_scalar : Measurable fun (W : Matrix (Fin d) (Fin d) ℝ) => R / frobNorm W :=
        Measurable.div measurable_const h_frobNorm_meas
      have h_vec : Measurable fun (W : Matrix (Fin d) (Fin d) ℝ) => W := measurable_id
      exact Measurable.smul h_scalar h_vec
    · exact measurable_id
  -- Step 3: symPart is continuous, hence measurable
  have h_symPart_cont : Continuous (symPart : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
    unfold symPart
    have h_add : Continuous fun (A : Matrix (Fin d) (Fin d) ℝ) => A + A.transpose :=
      Continuous.add continuous_id (continuous_id.matrix_transpose)
    exact Continuous.const_smul h_add (1/2 : ℝ)
  have h_symPart_meas : Measurable symPart := h_symPart_cont.measurable
  -- Step 4: clipSym a b is measurable, expressed as composition of measurable/continuous functions
  have h_clipSym_meas (a b : ℝ) : Measurable (clipSym a b : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
    unfold clipSym
    -- clipSym a b M = cnMid a b • 1 + frobClip (cnR0 d a b) (symPart M - cnMid a b • 1)
    -- = (fun X => cnMid a b • 1 + X) ∘ (frobClip (cnR0 d a b)) ∘ (fun M => symPart M - cnMid a b • 1)
    let g : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ := fun M => symPart M - cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ)
    have hg_cont : Continuous g := Continuous.sub h_symPart_cont continuous_const
    have hg_meas : Measurable g := hg_cont.measurable
    let f : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ := frobClip (cnR0 d a b)
    have hf_meas : Measurable f := h_frobClip_meas (cnR0 d a b)
    let h : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ := fun X => cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + X
    have hh_cont : Continuous h := Continuous.add continuous_const continuous_id
    have hh_meas : Measurable h := hh_cont.measurable
    -- clipSym a b M = h (f (g M))
    -- So clipSym a b = h ∘ f ∘ g
    -- We need to check: h (f (g M)) = cnMid a b • 1 + frobClip (cnR0 d a b) (symPart M - cnMid a b • 1)
    -- g M = symPart M - cnMid a b • 1
    -- f (g M) = frobClip (cnR0 d a b) (g M) = frobClip (cnR0 d a b) (symPart M - cnMid a b • 1)
    -- h (f (g M)) = cnMid a b • 1 + f (g M) = cnMid a b • 1 + frobClip (cnR0 d a b) (symPart M - cnMid a b • 1)
    -- = clipSym a b M ✓
    exact hh_meas.comp (hf_meas.comp hg_meas)
  -- Step 5: nsIter is continuous in its first argument, hence measurable
  have h_nsIter_cont (j : ℕ) : Continuous (fun (X : Matrix (Fin d) (Fin d) ℝ) => nsIter X j) := by
    induction' j with j ih
    · unfold nsIter; exact continuous_id
    · unfold nsIter
      have h_body : Continuous fun (X : Matrix (Fin d) (Fin d) ℝ) => (1/2 : ℝ) • (nsIter X j * ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - nsIter X j * nsIter X j)) := by
        refine Continuous.const_smul ?_ (1/2 : ℝ)
        refine Continuous.mul ih ?_
        refine Continuous.sub continuous_const ?_
        refine Continuous.mul ih ih
      exact h_body
  have h_nsIter_meas (j : ℕ) : Measurable (fun (X : Matrix (Fin d) (Fin d) ℝ) => nsIter X j) :=
    (h_nsIter_cont j).measurable
  -- Step 6: clampNSRoot a b c J is continuous in its last argument, hence measurable
  have h_clampNSRoot_cont (a b c : ℝ) : Continuous (fun (S : Matrix (Fin d) (Fin d) ℝ) => clampNSRoot a b c J S) := by
    unfold clampNSRoot
    refine Continuous.mul ?_ ?_
    · refine Continuous.sub continuous_id continuous_const
    · refine (h_nsIter_cont J).comp ?_
      have h_sub_cont : Continuous fun (S : Matrix (Fin d) (Fin d) ℝ) => S - c • (1 : Matrix (Fin d) (Fin d) ℝ) :=
        Continuous.sub continuous_id continuous_const
      refine Continuous.const_smul h_sub_cont (cnC0 d a b)⁻¹
  have h_clampNSRoot_meas (a b c : ℝ) : Measurable (fun (S : Matrix (Fin d) (Fin d) ℝ) => clampNSRoot a b c J S) :=
    (h_clampNSRoot_cont a b c).measurable
  -- Step 7: Build clampNSMat a b e J as a composition of measurable functions
  -- Let G(S) = clampNSRoot a b (a+e) J S - clampNSRoot a b (b-e) J S (continuous, hence measurable)
  have h_G_cont : Continuous fun (S : Matrix (Fin d) (Fin d) ℝ) =>
    clampNSRoot a b (a+e) J S - clampNSRoot a b (b-e) J S :=
    Continuous.sub (h_clampNSRoot_cont a b (a+e)) (h_clampNSRoot_cont a b (b-e))
  have h_G_meas : Measurable fun (S : Matrix (Fin d) (Fin d) ℝ) =>
    clampNSRoot a b (a+e) J S - clampNSRoot a b (b-e) J S :=
    h_G_cont.measurable
  -- Let H(X) = cnMid a b • 1 + (1/2) • X (continuous, hence measurable)
  have h_H_cont : Continuous fun (X : Matrix (Fin d) (Fin d) ℝ) =>
    cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + (1/2 : ℝ) • X :=
    Continuous.add continuous_const (Continuous.const_smul continuous_id (1/2 : ℝ))
  have h_H_meas : Measurable fun (X : Matrix (Fin d) (Fin d) ℝ) =>
    cnMid a b • (1 : Matrix (Fin d) (Fin d) ℝ) + (1/2 : ℝ) • X :=
    h_H_cont.measurable
  -- Then clampNSMat a b e J = H ∘ G ∘ (clipSym a b)
  -- Because: (H ∘ G ∘ clipSym a b) (Y) = H(G(clipSym a b Y))
  -- = cnMid a b • 1 + (1/2) • (G(clipSym a b Y))
  -- = cnMid a b • 1 + (1/2) • (clampNSRoot a b (a+e) J (clipSym a b Y) - clampNSRoot a b (b-e) J (clipSym a b Y))
  -- = clampNSMat a b e J Y
  -- So we need: h_H_meas.comp (h_G_meas.comp (h_clipSym_meas a b))
  have h_clampNSMat_meas : Measurable (fun (Y : Matrix (Fin d) (Fin d) ℝ) => clampNSMat a b e J Y) :=
    h_H_meas.comp (h_G_meas.comp (h_clipSym_meas a b))
  -- Step 8: Compose with Matrix.of
  have h_matrixOf_cont : Continuous (Matrix.of : (Fin d → Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) :=
    continuous_id
  have h_matrixOf_meas : Measurable (Matrix.of : (Fin d → Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) :=
    h_matrixOf_cont.measurable
  -- Final composition: Y ↦ Matrix.of Y ↦ clampNSMat a b e J (Matrix.of Y)
  -- = (clampNSMat a b e J) ∘ Matrix.of
  exact h_clampNSMat_meas.comp h_matrixOf_meas

/-- CLAMP-NS as a clamp routine. -/
noncomputable def clampNSRoutine : ClampRoutine where
  run d a b e Y := clampNSMat a b e (cnsJ d a b e) Y
  bounds d a b e Y hab he hew := clampNS_bounds d a b e Y hab he hew
  near d a b e Y Z hab he hew hZ := clampNS_near d a b e Y Z hab he hew hZ
  meas d a b e := clampNS_meas d a b e

/-- C2b-NS: `J(k) ≤ 3k + 2` (`2^{k+2} ≥ 3k + 3`), for the cost bound of the code. -/
theorem nsCount_le (k : ℕ) : nsCount k ≤ 3 * k + 2 := by
  unfold nsCount
  have h : 3 * k + 3 ≤ 2 ^ (k + 2) := by
    induction' k with k ih
    · norm_num
    · have h_eq : 3 * (k + 1) + 3 = (3 * k + 3) + 3 := by omega
      rw [h_eq]
      have h_add : (3 * k + 3) + 3 ≤ 2 ^ (k + 2) + 3 := Nat.add_le_add_right ih 3
      have h_bound : 2 ^ (k + 2) + 3 ≤ 2 ^ (k + 3) := by
        have h3 : 3 ≤ 2 ^ (k + 2) := by
          calc
            3 ≤ 4 := by norm_num
            _ = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h_eq : 2 * 2 ^ (k + 2) = 2 ^ (k + 3) := by
          have h : 2 ^ (k + 3) = 2 ^ (k + 2) * 2 := by
            rw [show 2 ^ (k + 3) = 2 ^ ((k + 2) + 1) by ring, pow_succ]
          rw [h]
          exact mul_comm _ _
        calc
          2 ^ (k + 2) + 3 ≤ 2 ^ (k + 2) + 2 ^ (k + 2) := Nat.add_le_add_left h3 _
          _ = 2 * 2 ^ (k + 2) := by ring
          _ = 2 ^ (k + 3) := h_eq
      exact le_trans h_add h_bound
  have hclog : Nat.clog 2 (3 * k + 3) ≤ k + 2 :=
    Nat.clog_le_of_le_pow h
  omega

/-- `16 q² ≤ 2^(q-1)` from `q = 21` on. -/
theorem sq_le_two_pow_aux (q : ℕ) (hq : 21 ≤ q) : 16 * q ^ 2 ≤ 2 ^ (q - 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
      have e : q + 1 - 1 = (q - 1) + 1 := by omega
      rw [e, pow_succ 2 (q - 1)]
      nlinarith

/-- `N² ≤ 2^(N/3 - 1)` for `N ≥ 64`. -/
theorem sq_le_two_pow_div3 (N : ℕ) (hN : 64 ≤ N) : N ^ 2 ≤ 2 ^ (N / 3 - 1) := by
  have h := sq_le_two_pow_aux (N / 3) (by omega)
  have h3 : N ≤ 4 * (N / 3) := by omega
  calc N ^ 2 ≤ (4 * (N / 3)) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 16 * (N / 3) ^ 2 := by ring
    _ ≤ 2 ^ (N / 3 - 1) := h

theorem pgLam_ge_one {ρ : ℝ} (hρ : 1 ≤ ρ) : 1 ≤ pgLam ρ := by
  rw [pgLam, Real.le_sqrt (by norm_num) (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + ρ by linarith); linarith)]
  have h2 := Real.log_two_gt_d9
  have : Real.log 2 ≤ Real.log (1 + ρ) := Real.log_le_log (by norm_num) (by linarith)
  nlinarith

theorem pgDelta_sq (d ρ : ℝ) (hd : 0 ≤ d) : pgDelta d ρ ^ 2 = pgLD ρ ^ 2 * d + ρ ^ 2 / 16 := by
  rw [pgDelta, mul_pow, Real.sq_sqrt (by norm_num [pgPB]; positivity), pgLD, pgKappa, pgPB]; ring

theorem pgG2_eq (d ρ : ℝ) (hd : 0 < d) (hl : 0 < pgLam ρ) :
    pgG2 d ρ = (5 * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * (1 / 8) ^ 2 / d) * (81 * d ^ 2 * pgLam ρ ^ 2) := by
  rw [pgG2, pgTmin, pgKappa]; field_simp; ring

theorem pgEh_inv (d ρ : ℝ) (hd : 0 < d) (hl : 0 < pgLam ρ) (hb : 0 < pgLD ρ) :
    (pgEh d ρ)⁻¹ = 59008 * d ^ 2 * pgLam ρ ^ 2 * pgLD ρ := by
  rw [pgEh, pgKappa]; field_simp; ring

/-- The arithmetic core of `N ≥ 250000 d`. -/
theorem pgNs_ge_aux (d b D2 G ei : ℝ) (hd : 1 ≤ d) (hb : 1 / 8 ≤ b) (hD : b ^ 2 ≤ D2)
    (hG : 7290 * b ^ 2 * d ≤ G) (he : 59008 * b ≤ ei) : 250000 * d ≤ 16 * D2 * G * ei ^ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hD0 : 0 ≤ D2 := le_trans (sq_nonneg b) hD
  have hG0 : 0 ≤ G := le_trans (by positivity) hG
  have h59 : (59008 * b) ^ 2 ≤ ei ^ 2 := pow_le_pow_left₀ (by positivity) he 2
  have h1 : 16 * b ^ 2 * (7290 * b ^ 2 * d) ≤ 16 * D2 * G :=
    mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) hG (by positivity) (by positivity)
  have h2 : 16 * b ^ 2 * (7290 * b ^ 2 * d) * (59008 * b) ^ 2 ≤ 16 * D2 * G * ei ^ 2 :=
    mul_le_mul h1 h59 (by positivity) (by positivity)
  have hb6 : (1 / 8 : ℝ) ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ (by norm_num) hb 6
  have e : 16 * b ^ 2 * (7290 * b ^ 2 * d) * (59008 * b) ^ 2 = (16 * 7290 * 59008 ^ 2 * b ^ 6) * d := by ring
  have h3 : (250000 : ℝ) ≤ 16 * 7290 * 59008 ^ 2 * b ^ 6 := by nlinarith
  have h4 : 250000 * d ≤ (16 * 7290 * 59008 ^ 2 * b ^ 6) * d := mul_le_mul_of_nonneg_right h3 (by linarith)
  linarith

/-- `16 Δ² G e_h⁻² ≤ N`. -/
theorem pgNs_ge_real (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    16 * pgDelta d ρ ^ 2 * pgG2 d ρ * (pgEh d ρ)⁻¹ ^ 2 ≤ (pgNs d ρ : ℝ) := by
  have h1 : pgNreal d ρ ≤ pgNs d ρ := Nat.le_ceil _
  rw [pgNreal] at h1
  have heh := pgEh_pos d ρ hd hρ
  calc 16 * pgDelta d ρ ^ 2 * pgG2 d ρ * (pgEh d ρ)⁻¹ ^ 2 = 16 * pgDelta d ρ ^ 2 * pgG2 d ρ / pgEh d ρ ^ 2 := by
        field_simp
    _ ≤ _ := h1

/-- `N ≥ 250000 d`. -/
theorem pgNs_ge_d (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 250000 * (d : ℝ) ≤ pgNs d ρ := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := pgLam_ge_one hρ
  have hb8 : 1 / 8 ≤ pgLD ρ := by rw [pgLD, pgKappa, pgPB]; nlinarith
  have hb0 : 0 < pgLD ρ := by linarith
  refine le_trans (pgNs_ge_aux d (pgLD ρ) _ _ _ hd1 hb8 ?_ ?_ ?_) (pgNs_ge_real d ρ hd hρ)
  · rw [pgDelta_sq d ρ (by linarith)]; nlinarith [sq_nonneg ρ, sq_nonneg (pgLD ρ)]
  · rw [pgG2_eq d ρ (by linarith) (by linarith)]
    have h18 : 18 * (d : ℝ) ≤ d * (d + 2) * (d + 5) := by
      have h' : (18 : ℝ) ≤ (d + 2) * (d + 5) := by nlinarith
      have := mul_le_mul_of_nonneg_left h' (by linarith : (0 : ℝ) ≤ d)
      linarith
    have h81 : (1 : ℝ) ≤ d ^ 2 * pgLam ρ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) (one_le_pow₀ hl)
    have hA : 90 * pgLD ρ ^ 2 * d ≤ 5 * pgLD ρ ^ 2 * d * (d + 2) * (d + 5) + 2 * (1 / 8) ^ 2 / d := by
      have : 0 ≤ 2 * (1 / 8 : ℝ) ^ 2 / d := by positivity
      have : 90 * pgLD ρ ^ 2 * d ≤ 5 * pgLD ρ ^ 2 * (d * (d + 2) * (d + 5)) := by
        have := mul_le_mul_of_nonneg_left h18 (by positivity : (0 : ℝ) ≤ 5 * pgLD ρ ^ 2)
        linarith
      linarith
    calc 7290 * pgLD ρ ^ 2 * d = (90 * pgLD ρ ^ 2 * d) * (81 * 1) := by ring
      _ ≤ _ := mul_le_mul hA (by rw [show (81 : ℝ) * d ^ 2 * pgLam ρ ^ 2 = 81 * (d ^ 2 * pgLam ρ ^ 2) by ring]; linarith)
          (by norm_num) (by positivity)
  · rw [pgEh_inv d ρ (by linarith) (by linarith) hb0]
    have h81 : (1 : ℝ) ≤ d ^ 2 * pgLam ρ ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd1) (one_le_pow₀ hl)
    calc 59008 * pgLD ρ = 59008 * pgLD ρ * 1 := by ring
      _ ≤ 59008 * pgLD ρ * (d ^ 2 * pgLam ρ ^ 2) := mul_le_mul_of_nonneg_left h81 (by positivity)
      _ = _ := by ring

/-- `0 < c₀ ≤ d^{1/2} t_max` at the parameters of PG. -/
theorem cnC0_pg_bounds {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    0 < cnC0 d (pgTmin d ρ) (pgLD ρ) ∧ cnC0 d (pgTmin d ρ) (pgLD ρ) ≤ Real.sqrt d * pgLD ρ := by
  obtain ⟨hab, -, -⟩ := pgEpr_bounds hd hρ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hl := pgLam_ge_one hρ
  have ha0 : 0 < pgTmin d ρ := by rw [pgTmin]; positivity
  have hs1 : 1 ≤ Real.sqrt d := by rw [Real.le_sqrt (by norm_num) hd0.le]; exact_mod_cast hd
  have hw : 0 < (pgLD ρ - pgTmin d ρ) / 2 := by linarith
  unfold cnC0 cnR0 cnHalf
  constructor
  · positivity
  · nlinarith

/-- The arithmetic core of `c₀/(2e') ≤ N²`. -/
theorem cnRatio_aux (c d G N e D2 : ℝ) (hd1 : 1 ≤ d) (hd : 0 < d) (hG : 0 < G) (hN : 1 ≤ N) (he : 0 < e) (hc0 : 0 ≤ c)
    (hc2 : c ^ 2 ≤ D2) (hk : 16 * D2 * G * e⁻¹ ^ 2 ≤ N) (hNd : 250000 * d ≤ N) :
    c * Real.sqrt d * 10 ^ 6 * Real.sqrt G * Real.sqrt N * e⁻¹ ≤ N ^ 2 := by
  have hx0 : 0 ≤ c * Real.sqrt d * 10 ^ 6 * Real.sqrt G * Real.sqrt N * e⁻¹ := by positivity
  refine (pow_le_pow_iff_left₀ hx0 (by positivity) two_ne_zero).1 ?_
  have e2 : (c * Real.sqrt d * 10 ^ 6 * Real.sqrt G * Real.sqrt N * e⁻¹) ^ 2 =
      (c ^ 2 * G * e⁻¹ ^ 2) * (10 ^ 12 * d * N) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hG.le,
      Real.sq_sqrt (by linarith)]
    ring
  have hk' : 16 * (c ^ 2 * G * e⁻¹ ^ 2) ≤ N := by
    have := mul_le_mul_of_nonneg_right hc2 (by positivity : (0 : ℝ) ≤ 16 * G * e⁻¹ ^ 2)
    linarith
  have hNd2 : 10 ^ 12 * d * N ≤ 16 * N * N * N := by
    have h25 : (250000 * d) * 250000 ≤ N * N := mul_le_mul hNd (by linarith) (by norm_num) (by linarith)
    have : 10 ^ 12 * d ≤ 16 * N * N := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  rw [e2]
  have h1 : (16 * (c ^ 2 * G * e⁻¹ ^ 2)) * (10 ^ 12 * d * N) ≤ N * (16 * N * N * N) :=
    mul_le_mul hk' hNd2 (by positivity) (by linarith)
  nlinarith

/-- `x = c₀/(2e') ≤ N²`. -/
theorem cnRatio_le {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    cnC0 d (pgTmin d ρ) (pgLD ρ) / (2 * pgEpr d ρ) ≤ (pgNs d ρ : ℝ) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hl := pgLam_ge_one hρ
  have hN1 : (1 : ℝ) ≤ pgNs d ρ := by exact_mod_cast pgNs_pos d ρ hd hρ
  have heh := pgEh_pos d ρ hd hρ
  have hG0 : 0 < pgG2 d ρ := by rw [pgG2_eq d ρ hd0 (by linarith)]; positivity
  obtain ⟨hc0, hc1⟩ := cnC0_pg_bounds hd hρ
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hsG : 0 < Real.sqrt (pgG2 d ρ) := Real.sqrt_pos.mpr hG0
  have hsN : 0 < Real.sqrt (pgNs d ρ) := Real.sqrt_pos.mpr (by linarith)
  have hx : cnC0 d (pgTmin d ρ) (pgLD ρ) / (2 * pgEpr d ρ) = cnC0 d (pgTmin d ρ) (pgLD ρ) * Real.sqrt d *
      10 ^ 6 * Real.sqrt (pgG2 d ρ) * Real.sqrt (pgNs d ρ) * (pgEh d ρ)⁻¹ := by
    rw [pgEpr, pgEP]
    field_simp
  have hc2 : cnC0 d (pgTmin d ρ) (pgLD ρ) ^ 2 ≤ pgDelta d ρ ^ 2 := by
    have h1 := pow_le_pow_left₀ hc0.le hc1 2
    rw [mul_pow, Real.sq_sqrt hd0.le] at h1
    rw [pgDelta_sq d ρ hd0.le]; nlinarith [sq_nonneg ρ]
  rw [hx]
  exact cnRatio_aux _ _ _ _ _ _ (by exact_mod_cast hd) hd0 hG0 hN1 heh hc0.le hc2 (pgNs_ge_real d ρ hd hρ) (pgNs_ge_d d ρ hd hρ)

theorem cnK_pg_le {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    3 * cnK d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) + 2 ≤ pgNs d ρ := by
  have hNd := pgNs_ge_d d ρ hd hρ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN64 : 64 ≤ pgNs d ρ := by
    have : (64 : ℝ) ≤ pgNs d ρ := le_trans (by linarith) hNd
    exact_mod_cast this
  have hpow := sq_le_two_pow_div3 _ hN64
  obtain ⟨c0, -⟩ := cnC0_pg_bounds hd hρ
  obtain ⟨-, he, -⟩ := pgEpr_bounds hd hρ
  have hx0 : 0 < cnC0 d (pgTmin d ρ) (pgLD ρ) / (2 * pgEpr d ρ) := by positivity
  have hk : cnK d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) ≤ pgNs d ρ / 3 - 1 := by
    unfold cnK
    rw [Nat.ceil_le, Real.logb_le_iff_le_rpow (by norm_num) hx0, Real.rpow_natCast]
    calc _ ≤ (pgNs d ρ : ℝ) ^ 2 := cnRatio_le hd hρ
      _ ≤ 2 ^ (pgNs d ρ / 3 - 1) := by exact_mod_cast hpow
  omega

/-- C2c-NS, the size of the count in PG: at most `N`. -/
theorem cnsJ_le_pgNs {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : cnsJ d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) ≤ pgNs d ρ := by
  unfold cnsJ
  exact (nsCount_le _).trans (cnK_pg_le hd hρ)

end AdversarialBco.Conj1Arith
