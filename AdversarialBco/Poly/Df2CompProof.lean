/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2RowsProof
public import AdversarialBco.Poly.Df2LawProof

@[expose] public section

/-!
# The last step of the measure clause

`df2CompOf_holds : Df2CompOf` (proof of part A). In the regime `ε ≤ 1/2`, the
regret of the learner exceeds `C d^{3/2} n^{1/2} log^5(2 d n/δ)` only if the position is bad (Theorem 8.3 through the
law of the positioning block, `df2oOmega_law`), or, in the case of the analysis, the regret of DJ exceeds `B + 1`
with `B = 2 ρ/η + n ε + (2 n log(7/δ_e))^{1/2}`; Proposition G passes to D0 at the cost `δ₁`, Lemma 8.10 with
the regret reduces D0 to the union of the `n` virtual epochs and the Azuma event. The budget is
`2 δ₁ + n (149/168) δ_e + δ_e/7 ≤ 3 δ₁ ≤ δ`. Outside the regime the learner is off, its regret is at most `n`, and
`Df2Trivial` bounds `n`.
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Leaves -/

/-- The confidence of an epoch against the scale `log(2dn/δ)`: `0 < log(1/δ_e) ≤ 25 log(2dn/δ)`. -/
theorem log_inv_de_le (d n δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (1 / (4 * min (δ / 3) (Real.exp (-14) / (d * n) ^ 3) / (5 * n))) ∧
      Real.log (1 / (4 * min (δ / 3) (Real.exp (-14) / (d * n) ^ 3) / (5 * n))) ≤
        25 * Real.log (2 * d * n / δ) := by
  set x := d * n with hx
  have hx1 : 1 ≤ x := by nlinarith
  set E := Real.exp 14 with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hEm : Real.exp (-14) = 1 / E := by rw [Real.exp_neg, hE, one_div]
  have hn0 : 0 < n := by linarith
  set q := δ / (3 * E * x ^ 3) with hq
  have hq0 : 0 < q := by positivity
  have hd1 : q ≤ min (δ / 3) (Real.exp (-14) / x ^ 3) := by
    refine le_min ?_ ?_
    · rw [hq]
      apply div_le_div_of_nonneg_left hδ0.le (by norm_num)
      have : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ hx1
      nlinarith
    · rw [hq, hEm, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hEx : 0 < E * x ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hδ1.le hEx.le]
  set δ1 := min (δ / 3) (Real.exp (-14) / x ^ 3) with hδ1def
  have hδ1pos : 0 < δ1 := lt_of_lt_of_le hq0 hd1
  set δe := 4 * δ1 / (5 * n) with hδe
  have hδepos : 0 < δe := by positivity
  have hδ1le : δ1 ≤ δ / 3 := min_le_left _ _
  have hδelt : δe < 1 := by
    rw [hδe, div_lt_one (by positivity)]
    nlinarith
  have hpos : 0 < Real.log (1 / δe) := by
    apply Real.log_pos
    rw [one_div]; exact one_lt_inv₀ hδepos |>.mpr hδelt
  refine ⟨hpos, ?_⟩
  have hΛ : 2 * d * n / δ = 2 * x / δ := by rw [hx]; ring
  rw [hΛ]
  have hz : 2 ≤ 2 * x / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hlog2 : 2 / 3 ≤ Real.log (2 * x / δ) := by
    have h2 : 2 / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    linarith [Real.log_le_log (by norm_num) hz]
  -- `1/δe ≤ E (2x/δ)^4`
  have hkey : 1 / δe ≤ E * (2 * x / δ) ^ 4 := by
    rw [div_le_iff₀ hδepos]
    have h1 : 4 * q / (5 * n) ≤ δe := by
      rw [hδe]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 1 ≤ E * (2 * x / δ) ^ 4 * (4 * q / (5 * n)) := by
      rw [hq]
      have e : E * (2 * x / δ) ^ 4 * (4 * (δ / (3 * E * x ^ 3)) / (5 * n)) = 64 * x / (15 * n * δ ^ 3) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ0.le hδ1.le
      have hxn : n ≤ x := by rw [hx]; nlinarith
      nlinarith
    calc (1 : ℝ) ≤ E * (2 * x / δ) ^ 4 * (4 * q / (5 * n)) := h2
      _ ≤ E * (2 * x / δ) ^ 4 * δe := by gcongr
  have hl := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) (by positivity), hE, Real.log_exp, Real.log_pow] at hl
  push_cast at hl
  linarith

theorem comp_thresh (p : Df2OPar) (d n : ℕ) (δ : ℝ) (H : RowHyp p d n) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (h1 : p.δ1 = min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)) (he : p.δe = 4 * p.δ1 / (5 * n)) :
    2 * (p.rho / p.eta) + n * p.eps + Real.sqrt (2 * n * Real.log (7 / p.δe)) + 1 ≤
      10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  obtain ⟨-, hle⟩ := log_inv_de_le d n δ hd1 hn1 hδ0 hδ1
  have hLΛ : p.Le ≤ 900 * Real.log (2 * d * n / δ) := by
    rw [H.Le, he, h1]; linarith
  have hde := H.de_pos
  have hlog7 : Real.log (7 / p.δe) ≤ 6 + p.Le / 36 := by
    rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity), H.Le]
    have : Real.log 7 ≤ 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hd32 : (d : ℝ) ^ (3 / 2 : ℝ) = d * Real.sqrt d := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [H.rho, H.eta, H.eps, hd32]
  set Λ := Real.log (2 * d * n / δ)
  set L := p.Le with hLdef
  have hL : (504 : ℝ) ≤ L := H.L504
  set s := Real.sqrt d with hs
  set t := Real.sqrt n with ht
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hd1
  have ht1 : 1 ≤ t := Real.one_le_sqrt.mpr hn1
  have hss : s ^ 2 = d := Real.sq_sqrt (by linarith)
  have htt : t ^ 2 = n := Real.sq_sqrt (by linarith)
  have hL4 : L ^ 4 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL1 : 1 ≤ L ^ 5 := one_le_pow₀ (by linarith)
  have hds : 1 ≤ d * s := by nlinarith
  have hP : 0 ≤ d * s * t := by positivity
  -- the four terms
  have hT1 : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) ≤ 2900 * (d * s) * L ^ 5 * t := by
    have e : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) = 2900 * (d * s) * L ^ 4 * t := by
      have hs0 : s ≠ 0 := by positivity
      field_simp
      rw [← hss]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ 2900 * (d * s))
    nlinarith
  have hT2 : (n : ℝ) * (20 * 725 * (d * s) * L ^ 5 / t) = 14500 * (d * s) * L ^ 5 * t := by
    have ht0 : t ≠ 0 := by positivity
    field_simp
    rw [← htt]; ring
  have hT3 : Real.sqrt (2 * n * Real.log (7 / p.δe)) ≤ (d * s) * L ^ 5 * t := by
    have h2 : 2 * n * Real.log (7 / p.δe) ≤ (L * t) ^ 2 := by
      rw [mul_pow, htt]
      have : 2 * Real.log (7 / p.δe) ≤ L ^ 2 := by nlinarith
      nlinarith
    calc Real.sqrt (2 * n * Real.log (7 / p.δe)) ≤ Real.sqrt ((L * t) ^ 2) := Real.sqrt_le_sqrt h2
      _ = L * t := Real.sqrt_sq (by positivity)
      _ ≤ (d * s) * L ^ 5 * t := by
        have hLL : L ≤ L ^ 5 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have : L ≤ (d * s) * L ^ 5 := le_trans hLL (le_mul_of_one_le_left (by positivity) hds)
        nlinarith
  have hT4 : (1 : ℝ) ≤ (d * s) * L ^ 5 * t := by
    have : 1 ≤ (d * s) * L ^ 5 := one_le_mul_of_one_le_of_one_le hds hL1
    nlinarith
  have hsum : 2 * (2 * 725 * (d : ℝ) ^ 2 * L ^ 3 / (s / (L * t))) + n * (20 * 725 * (d * s) * L ^ 5 / t) +
      Real.sqrt (2 * n * Real.log (7 / p.δe)) + 1 ≤ 17402 * (d * s * t) * L ^ 5 := by
    rw [hT2]; nlinarith
  have hL5 : L ^ 5 ≤ (900 * Λ) ^ 5 := pow_le_pow_left₀ (by linarith) hLΛ 5
  calc _ ≤ 17402 * (d * s * t) * L ^ 5 := hsum
    _ ≤ 17402 * (d * s * t) * (900 * Λ) ^ 5 := by gcongr
    _ = 17402 * 900 ^ 5 * ((d * s * t) * Λ ^ 5) := by ring
    _ ≤ 10 ^ 22 * ((d * s * t) * Λ ^ 5) := by
      gcongr
      · have : 0 ≤ Λ := by linarith
        positivity
      · norm_num
    _ = 10 ^ 22 * (d * s) * t * Λ ^ 5 := by ring

theorem comp_trivial (TR : Df2Trivial) (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (h : 1 / 2 < (df2oPar d n δ).eps) :
    (n : ℝ) ≤ 10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hpos, hle⟩ := log_inv_de_le d n δ hd1 hn1 hδ0 hδ1
  set Λ := Real.log (2 * d * n / δ) with hΛ
  set L := (df2oPar d n δ).Le with hL
  have hLdef : L = 36 * Real.log (1 / (4 * min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) / (5 * n))) := by
    rw [hL]; simp only [df2oPar, df2C0]
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hLΛ : L ≤ 900 * Λ := by rw [hLdef]; linarith
  have heps : (df2oPar d n δ).eps = 20 * 725 * (d * Real.sqrt d) * L ^ 5 / Real.sqrt n := by
    rw [hL]; simp only [df2oPar, df2oClam]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  -- `√n < 29000 d √d L⁵`, hence `n < 4 · 14500² d³ L¹⁰`
  have h1 : Real.sqrt n < 29000 * (d * Real.sqrt d) * L ^ 5 := by
    rw [heps, lt_div_iff₀ hsn] at h; linarith
  have h2 : (n : ℝ) < 4 * 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 := by
    have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
    have hsqd : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by linarith)
    have := pow_lt_pow_left₀ h1 hsn.le (two_ne_zero)
    rw [hsq] at this
    calc (n : ℝ) < (29000 * (d * Real.sqrt d) * L ^ 5) ^ 2 := this
      _ = 4 * 14500 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 := by
        rw [show (29000 * (d * Real.sqrt d) * L ^ 5) ^ 2 = 29000 ^ 2 * d ^ 2 * Real.sqrt d ^ 2 * L ^ 10 by ring,
          hsqd]; ring
  have h3 := TR d n 14500 L hd1 hn1 (by norm_num) hL0 h2
  have hL5 : L ^ 5 ≤ (900 * Λ) ^ 5 := pow_le_pow_left₀ hL0.le hLΛ 5
  have hΛ0 : 0 ≤ Λ := by
    have : 0 < L := hL0
    linarith
  have hd32 : 0 ≤ (d : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  calc (n : ℝ) ≤ 2 * 14500 * (d : ℝ) ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n := h3
    _ ≤ 2 * 14500 * (d : ℝ) ^ ((3 : ℝ) / 2) * (900 * Λ) ^ 5 * Real.sqrt n := by gcongr
    _ = 2 * 14500 * 900 ^ 5 * ((d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt n * Λ ^ 5) := by ring
    _ ≤ 10 ^ 22 * ((d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt n * Λ ^ 5) := by
      gcongr
      norm_num
    _ = 10 ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Λ ^ 5 := by ring

/-! ## The parameters -/

theorem par_δ1_pos (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) : 0 < (df2oPar d n δ).δ1 := by
  have hdn : (0 : ℝ) < (d : ℝ) * n := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  show 0 < min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)
  exact lt_min (by positivity) (by positivity)

theorem par_δ1_le (d n : ℕ) (δ : ℝ) : (df2oPar d n δ).δ1 ≤ δ / 3 := min_le_left _ _

theorem comp_prob (d n : ℕ) (δ : ℝ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hδ0 : 0 < δ) :
    2 * (df2oPar d n δ).δ1 + n * (149 / 168 * (df2oPar d n δ).δe) + (df2oPar d n δ).δe / 7 ≤ δ := by
  have h0 := par_δ1_pos d n δ hd hn hδ0
  have h1 := par_δ1_le d n δ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (df2oPar d n δ).δe = 4 * (df2oPar d n δ).δ1 / (5 * n) := rfl
  rw [he]
  have e1 : (n : ℝ) * (149 / 168 * (4 * (df2oPar d n δ).δ1 / (5 * n))) = 596 / 840 * (df2oPar d n δ).δ1 := by
    field_simp
    ring
  have e2 : 4 * (df2oPar d n δ).δ1 / (5 * n) / 7 ≤ 4 * (df2oPar d n δ).δ1 / 35 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [e1]
  linarith

/-! ## The plays of DJ and the trivial bound -/

theorem df2oPlay_mem (n : ℕ) (r0 R0 δ : ℝ) (w : World d) (h0 : (0 : E d) ∈ w.K) (t : ℕ) :
    df2oPlay d n r0 R0 δ w t ∈ w.K := by
  unfold df2oPlay df2oRoundAt
  rcases df2oMode d n r0 R0 δ w t with _ | _ | st
  all_goals simp only [df2Round]
  all_goals first
    | exact h0
    | (split_ifs with h
       · exact h
       · exact h0)

theorem regret_le_n (K : Set (E d)) (n : ℕ) (f : ℕ → E d → ℝ) (hf : f ∈ Advs K n) (x : ℕ → E d)
    (hx : ∀ t < n, x t ∈ K) (hK : K.Nonempty) : regretPts K f x n ≤ n := by
  unfold regretPts
  have h1 : ∑ t ∈ Finset.range n, f t (x t) ≤ ∑ t ∈ Finset.range n, (1 : ℝ) :=
    Finset.sum_le_sum fun t ht => ((hf t (Finset.mem_range.mp ht)).2 _ (hx t (Finset.mem_range.mp ht))).2
  have h2 : 0 ≤ sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) := by
    apply le_csInf (hK.image _)
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg fun t ht => ((hf t (Finset.mem_range.mp ht)).2 _ hy).1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  linarith

theorem df2oOmega_measurable (d n : ℕ) (r0 R0 δ1 : ℝ) : Measurable (df2oOmega d n r0 R0 δ1) := by
  unfold df2oOmega
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun r => ?_
  refine Measurable.prodMk (measurable_pi_iff.mpr fun k => ?_)
    (measurable_pi_iff.mpr fun v => measurable_pi_iff.mpr fun k => ?_)
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)

/-! ## The composition -/

/-- The last step: the measure clause from Lemma 8.8 and (iii), the Azuma event, Proposition G, Theorem 8.3 and
the trivial bound. -/
theorem df2CompOf_holds : Df2CompOf := by
  intro VE AZ WD PG PGT _ _ TR
  refine ⟨10 ^ 22, ?_⟩
  intro d hd n hn r0 R0 δ hr0 hr0R0 hδ0 hδ1 K hKc hKcv hball hKR f hf ν hν
  have hW : Df2WorldHyp d n r0 R0 δ K f := ⟨hd, hn, hr0, hr0R0, hδ0, hδ1, hKc, hKcv, hball, hKR, hf⟩
  have := hν.1
  have h0K : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self hr0.le)
  have hδ1pos := par_δ1_pos d n δ hd hn hδ0
  have hδ1le := par_δ1_le d n δ
  set thr := (10 : ℝ) ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 with hthr
  by_cases heps : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · -- outside the regime the regret is at most `n ≤ thr`
    have hn' := comp_trivial TR d n δ hd hn hδ0 hδ1 (lt_of_not_ge heps)
    have : {ω : (ℕ → ℝ) × (ℕ → ℝ) | thr < regretPts K f (df2oPlay d n r0 R0 δ ⟨K, f, ω.2, ω.1⟩) n} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := regret_le_n K n f hf _ (fun t _ => df2oPlay_mem n r0 R0 δ ⟨K, f, ω.2, ω.1⟩ h0K t) ⟨0, h0K⟩
      linarith
    rw [this, measure_empty]
    simp
  -- the regime
  set B := 2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) + n * (df2oPar d n δ).eps +
    Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe)) with hB
  have RH := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hBt : B + 1 ≤ thr := comp_thresh _ d n δ RH hδ0 hδ1 rfl rfl
  set μ := gaussStream.prod ν with hμ
  -- the bad positions
  set S : Set (ℕ → ℕ → PgRound d) := {x | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (pg d K r0 R0 (df2oPar d n δ).δ1 x)} with hS
  have hpos : μ {ω | ¬ Df2Case d n r0 R0 δ (df2World K f ω)} ≤ ENNReal.ofReal (df2oPar d n δ).δ1 := by
    have hsub : {ω : (ℕ → ℝ) × (ℕ → ℝ) | ¬ Df2Case d n r0 R0 δ (df2World K f ω)} ⊆
        (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) ×ˢ Set.univ := by
      intro ω hω
      refine ⟨fun hg => hω ⟨hg, heps⟩, Set.mem_univ _⟩
    calc μ _ ≤ μ ((df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) ×ˢ Set.univ) := measure_mono hsub
      _ = gaussStream (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) := by
          rw [hμ, Measure.prod_prod, measure_univ, mul_one]
      _ ≤ (gaussStream.map (df2oOmega d n r0 R0 (df2oPar d n δ).δ1)) S :=
          Measure.le_map_apply (df2oOmega_measurable d n r0 R0 _).aemeasurable S
      _ = pgMeasure d S := by rw [df2oOmega_law]
      _ ≤ ENNReal.ofReal (df2oPar d n δ).δ1 :=
          PGT d K r0 R0 _ hd hKcv hKc.isClosed hr0 hr0R0 hball hKR hδ1pos (by linarith)
  -- D0 in the case of the analysis
  have hD0 : μ {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧ B < regretPts K f (df2zPlay d n r0 R0 δ (df2World K f ω)) n} ≤
      ∑ a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
        ENNReal.ofReal ((df2oPar d n δ).δe / 7) := by
    have hsub : {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
        B < regretPts K f (df2zPlay d n r0 R0 δ (df2World K f ω)) n} ⊆
        (⋃ a ∈ Finset.range n, {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
          ¬ (df2zCtx d n r0 R0 δ (df2World K f ω)).EpochOK (df2zPath d n r0 R0 δ (df2World K f ω) a) (n - a)}) ∪
        {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧ ¬ Df2AzPath d n r0 R0 δ (df2World K f ω)} := by
      rintro ω ⟨hc, hlt⟩
      by_contra hno
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, not_or, not_exists,
        not_and, not_not] at hno
      have := WD d n r0 R0 δ K f hW (df2World K f ω) rfl rfl hc (fun a ha => hno.1 a ha hc) (hno.2 hc)
      linarith
    calc _ ≤ _ := measure_mono hsub
      _ ≤ μ (⋃ a ∈ Finset.range n, {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
            ¬ (df2zCtx d n r0 R0 δ (df2World K f ω)).EpochOK (df2zPath d n r0 R0 δ (df2World K f ω) a) (n - a)}) +
          μ {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧ ¬ Df2AzPath d n r0 R0 δ (df2World K f ω)} :=
          measure_union_le _ _
      _ ≤ _ := by
          gcongr
          · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
            exact VE d n r0 R0 δ K f hW ν hν a (Finset.mem_range.mp ha)
          · exact AZ d n r0 R0 δ K f hW ν hν
  have hG := PG d n r0 R0 δ K f hW ν hν B
  have hsub : {ω : (ℕ → ℝ) × (ℕ → ℝ) | thr < regretPts K f (df2oPlay d n r0 R0 δ ⟨K, f, ω.2, ω.1⟩) n} ⊆
      {ω | ¬ Df2Case d n r0 R0 δ (df2World K f ω)} ∪
        {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧ B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n} := by
    intro ω hω
    by_cases hc : Df2Case d n r0 R0 δ (df2World K f ω)
    · exact Or.inr ⟨hc, lt_of_le_of_lt hBt hω⟩
    · exact Or.inl hc
  have he0 : 0 ≤ (df2oPar d n δ).δe := by
    show 0 ≤ 4 * (df2oPar d n δ).δ1 / (5 * n)
    positivity
  calc μ _ ≤ μ {ω | ¬ Df2Case d n r0 R0 δ (df2World K f ω)} +
        μ {ω | Df2Case d n r0 R0 δ (df2World K f ω) ∧
          B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (df2oPar d n δ).δ1 + ((∑ a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
          ENNReal.ofReal ((df2oPar d n δ).δe / 7)) + ENNReal.ofReal (df2oPar d n δ).δ1) := by
        gcongr
        exact hG.trans (by gcongr)
    _ = ENNReal.ofReal (2 * (df2oPar d n δ).δ1 + n * (149 / 168 * (df2oPar d n δ).δe) +
          (df2oPar d n δ).δe / 7) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (comp_prob d n δ hd hn hδ0)

end Layer2

end AdversarialBco.Poly
