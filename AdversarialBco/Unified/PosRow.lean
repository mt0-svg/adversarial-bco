/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PosCore
public import AdversarialBco.Bit.TriSamp2

@[expose] public section

/-!
# UNI-POS part 3: the row (R) with the τ-subgradient slack, and the parameters of TRI-OGD-O

UNI-POS (the paper's section on the position), part 3.
The row of the core gains `(G_b Δ + τ_s)` in the Hoeffding term and `2 τ_s` (`hpSgdTau`). Its budget: `e_lo/8` to the
rounding `β Δ`, `e_lo/8` to the coupling `2 ε_G`, `e_lo/8` to `2 τ_s` (`τ_s ≤ e_lo/16`), and `5 e_lo/8` to the two
descent terms; the bound of the field grows from `G_up` to `G_up' = (65/64) G_up` (the selection has
`‖g‖ ≤ 1 + τ√d ≤ 65/64`). Against v2.1 (`tri_par_row`, Bit/TriSamp2.lean) the horizon doubles: `N' = 2^{n + 1}`,
`n = triNe d ℓ`, and the step is that of the same rule at the new `N'` and `G_up'`.

* `triGuT`, `triNeT`, `triJsT`: `G_up' = G_up + G_up/64`, `n' = n + 1`, `j_s'` the least `j` with
  `4^j ≥ (G_up' + β_up)² N'/Δ²`.
* `tri_row_tau`: the five terms of the row against `e_lo`, generic (the analogue of `tri_row_main`).
* `tri_par_row_tau`: the row at the parameters of dimension `d`, for every `τ_s ∈ [0, e_lo/16]`.
* `tri_par_GuT`: `(1 + a_s)² + ((1 + a_s) M_d + κ/(√d a))² ≤ G_up'²` for `0 ≤ a_s ≤ 1/64` (the hypothesis `hGb` of
  `triCoreTau`).
* `triETau`, `triE1`, `tri_par_tau`: a choice of the SEP parameters, `τ = 2^{-e_τ}`, `ℓ_1 = 2^{-e_1}`, with
  `τ_s = τ√d (1 + M_d) Δ + (2 + 2τ√d)(64/63) ℓ_1 ≤ e_lo/16` and `τ√d ≤ 1/64` (m2: the sup of `|z - y⁰|` over the box
  is bounded through its diameter, `(1 + M_d) Δ`).
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.UniPos

open AdversarialBco.Poly AdversarialBco.Bit

/-- `G_up' = G_up + G_up/64`, the bound of the field of TRI-OGD-O. -/
noncomputable def triGuT (d : ℕ) : ℝ := triGu d + triGu d / 64

/-- `n' = n + 1`: the horizon `N' = 2^{n'}` of TRI-OGD-O, one doubling of v2.1's. -/
noncomputable def triNeT (d ℓ : ℕ) : ℕ := triNe d ℓ + 1

/-- `j_s'`: the step `2^{-j_s'}`, the largest power of two with `s'² (G_up' + β_up)² N' ≤ Δ²`. -/
noncomputable def triJsT (d ℓ : ℕ) : ℕ := Nat.clog 4 ⌈(triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ / triD2 d⌉₊

/-- The facts on the parameters that the rows read: `Δ² ≥ 1/16`, `0 < e_lo ≤ 1`, `e_lo ≤ e_h(ρ_h)`. -/
theorem tri_par_basic (d : ℕ) (hd : 1 ≤ d) :
    1 / 16 ≤ triD2 d ∧ 0 < triElo d ∧ triElo d ≤ 1 ∧ triElo d ≤ pgEh d (triRh d) := by
  obtain ⟨hRa1, -, hkR, -, -, -, -, -⟩ := tri_par_box d hd
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 1 / 8 ≤ triR d := by
    have : (1 / 8 : ℝ) ≤ pgKappa * triRa d := by unfold pgKappa; linarith
    linarith
  have hD2 : 1 / 16 ≤ triD2 d := by
    unfold triD2
    have hr2 : (1 / 8 : ℝ) ^ 2 ≤ triR d ^ 2 := pow_le_pow_left₀ (by norm_num) hR 2
    have h1 : triR d ^ 2 ≤ d * triR d ^ 2 := le_mul_of_one_le_left (by positivity) hd0
    have h2 : 0 ≤ (d : ℝ) * (triB d - triA d) ^ 2 := by positivity
    have h3 : 0 ≤ 2 * (d : ℝ) * (d - 1) * triB d ^ 2 := by
      have : (0 : ℝ) ≤ d - 1 := by linarith
      positivity
    have e : 4 * (d : ℝ) * triR d ^ 2 = 4 * (d * triR d ^ 2) := by ring
    linarith
  have hs4 : 4 ≤ triS d := (Nat.find_spec (pg_par_exists d)).1
  have hs16 : 16 ≤ triS d ^ 2 := by nlinarith
  have hLh1 : 1 ≤ triLh (triS d) := by unfold triLh; omega
  have hRh1 : (1 : ℝ) ≤ triRh d := by
    have : (2 : ℝ) ≤ 2 ^ triLh (triS d) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hLh1
    show (1 : ℝ) ≤ 2 ^ triLh (triS d) - 1
    linarith
  have hLhr : (1 : ℝ) ≤ triLh (triS d) := by exact_mod_cast hLh1
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hd0
  have hden : 922 * (7 / 5) * (627 / 4000) ≤
      922 * (d : ℝ) ^ 2 * (7 / 5 * triLh (triS d)) * (627 / 4000 * triRh d) := by
    have h1 : (922 : ℝ) ≤ 922 * (d : ℝ) ^ 2 := by linarith
    have h2 : (7 / 5 : ℝ) ≤ 7 / 5 * triLh (triS d) := by linarith
    have h3 : (627 / 4000 : ℝ) ≤ 627 / 4000 * triRh d := by linarith
    exact mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by positivity)) h3 (by norm_num) (by positivity)
  have hden0 : (0 : ℝ) < 922 * (d : ℝ) ^ 2 * (7 / 5 * triLh (triS d)) * (627 / 4000 * triRh d) :=
    lt_of_lt_of_le (by norm_num) hden
  have helo0 : 0 < triElo d := by
    unfold triElo pgKappa
    exact div_pos (by norm_num) hden0
  have helo1 : triElo d ≤ 1 := by
    unfold triElo pgKappa
    rw [div_le_one hden0]
    linarith
  exact ⟨hD2, helo0, helo1, tri_elo_le d (triLh (triS d)) hd hLh1⟩

/-- **The row (R) with the slack `τ_s`**, generic: the analogue of `tri_row_main` (Bit/TriLeaves.lean) for the bound
of `hpSgdTau`. -/
theorem tri_row_tau (Δ Δu Gb Gu β βu ℓ ℓu s N εG elo τs : ℝ) (hΔ : 0 < Δ) (hΔu : Δ ≤ Δu)
    (hGb : 0 ≤ Gb) (hGu : Gb ≤ Gu) (hβ : 0 ≤ β) (hβu : β ≤ βu) (hℓ : 0 ≤ ℓ) (hℓu : ℓ ≤ ℓu) (hN : 0 < N)
    (hs : 0 < s) (hs1 : Δ ^ 2 < 4 * s ^ 2 * (Gu + βu) ^ 2 * N) (hs2 : s ^ 2 * (Gu + βu) ^ 2 * N ≤ Δ ^ 2)
    (hNc : Δu ^ 2 * (2 * (3 / 2 * (Gu + βu)) ^ 2 + 2 * (2 * (9 / 8 * Gu) ^ 2 * ℓu)) ≤ 25 / 64 * elo ^ 2 * N)
    (hβc : βu ^ 2 * Δu ^ 2 ≤ elo ^ 2 / 64) (hεc : 2 * εG ≤ elo / 8) (helo : 0 ≤ elo)
    (hτe : 16 * τs ≤ elo) (hτG : 8 * τs ≤ Gu * Δ) :
    Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + β * Δ + (Gb * Δ + τs) * Real.sqrt (2 * ℓ / N) + 2 * τs +
      2 * εG ≤ elo := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = Gu + βu := ⟨_, rfl⟩
  rw [← hGdef] at hs1 hs2 hNc
  have hGu0 : 0 ≤ Gu := le_trans hGb hGu
  have hβu0 : 0 ≤ βu := le_trans hβ hβu
  have hG0 : 0 ≤ G := by rw [hGdef]; exact add_nonneg hGu0 hβu0
  have hΔ2 : 0 < Δ ^ 2 := pow_pos hΔ 2
  have hGpos : 0 < G := by
    rcases hG0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hs1
      have : 4 * s ^ 2 * (0 : ℝ) ^ 2 * N = 0 := by ring
      linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsN2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hGsN : 0 < G * Real.sqrt N := mul_pos hGpos hsN
  -- the step rule
  have hb1 : s ≤ Δ / (G * Real.sqrt N) := by
    rw [le_div_iff₀ hGsN]
    have h : (s * (G * Real.sqrt N)) ^ 2 ≤ Δ ^ 2 := by
      have e : (s * (G * Real.sqrt N)) ^ 2 = s ^ 2 * G ^ 2 * N := by rw [mul_pow, mul_pow, hsN2]; ring
      rw [e]; exact hs2
    exact le_of_sq_le_sq h hΔ.le
  have hb2 : Δ / (G * Real.sqrt N) / 2 < s := by
    rw [div_div, div_lt_iff₀ (mul_pos hGsN two_pos)]
    have h : Δ ^ 2 < (s * (G * Real.sqrt N * 2)) ^ 2 := by
      have e : (s * (G * Real.sqrt N * 2)) ^ 2 = 4 * s ^ 2 * G ^ 2 * N := by rw [mul_pow, mul_pow, mul_pow, hsN2]; ring
      rw [e]; exact hs1
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h
  have hstep := sp_step_rule Δ G N s hΔ hGpos hN hb2 hb1
  have hGbβ : (Gb + β) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by positivity) (by rw [hGdef]; linarith) 2
  have hT1 : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 ≤ 3 / 2 * Δ * G / Real.sqrt N := by
    have : s / 2 * (Gb + β) ^ 2 ≤ s / 2 * G ^ 2 := mul_le_mul_of_nonneg_left hGbβ (by positivity)
    linarith
  -- the Hoeffding term
  have hsq_mono : Real.sqrt (2 * ℓ / N) ≤ Real.sqrt (2 * ℓu / N) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hN.le)
  have hH0 : Gb * Δ + τs ≤ 9 / 8 * Gu * Δu := by
    have h1 : Gb * Δ ≤ Gu * Δu := mul_le_mul hGu hΔu hΔ.le hGu0
    have h2 : Gu * Δ ≤ Gu * Δu := mul_le_mul_of_nonneg_left hΔu hGu0
    linarith
  have hH : (Gb * Δ + τs) * Real.sqrt (2 * ℓ / N) ≤ 9 / 8 * Gu * Δu * Real.sqrt (2 * ℓu / N) :=
    mul_le_mul hH0 hsq_mono (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hGu0) (hΔ.le.trans hΔu))
  -- the horizon
  have hℓu0 : 0 ≤ ℓu := le_trans hℓ hℓu
  obtain ⟨X, hX⟩ : ∃ X, X = 3 / 2 * G := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.sqrt (2 * (9 / 8 * Gu) ^ 2 * ℓu) := ⟨_, rfl⟩
  have hY2 : Y ^ 2 = 2 * (9 / 8 * Gu) ^ 2 * ℓu := by rw [hY]; exact Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; exact Real.sqrt_nonneg _
  have hXY : (Δu * (X + Y)) ^ 2 ≤ (5 / 8 * elo * Real.sqrt N) ^ 2 := by
    have h1 : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by linarith [sq_nonneg (X - Y)]
    have h2 : Δu ^ 2 * (X + Y) ^ 2 ≤ Δu ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have e1 : (Δu * (X + Y)) ^ 2 = Δu ^ 2 * (X + Y) ^ 2 := by ring
    have e2 : Δu ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) =
        Δu ^ 2 * (2 * (3 / 2 * G) ^ 2 + 2 * (2 * (9 / 8 * Gu) ^ 2 * ℓu)) := by rw [hY2, hX]
    have e3 : (5 / 8 * elo * Real.sqrt N) ^ 2 = 25 / 64 * elo ^ 2 * N := by rw [mul_pow, mul_pow, hsN2]; ring
    rw [e1, e3]
    linarith
  have hXY' : Δu * (X + Y) ≤ 5 / 8 * elo * Real.sqrt N := le_of_sq_le_sq hXY (by positivity)
  have hYN : Y / Real.sqrt N = 9 / 8 * Gu * Real.sqrt (2 * ℓu / N) := by
    rw [hY, ← Real.sqrt_div' _ hN.le]
    have e : 2 * (9 / 8 * Gu) ^ 2 * ℓu / N = (9 / 8 * Gu) ^ 2 * (2 * ℓu / N) := by ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hmain : Δ ^ 2 / (2 * s * N) + s / 2 * (Gb + β) ^ 2 + (Gb * Δ + τs) * Real.sqrt (2 * ℓ / N) ≤
      5 / 8 * elo := by
    have h1 : 3 / 2 * Δ * G / Real.sqrt N ≤ Δu * X / Real.sqrt N := by
      refine div_le_div_of_nonneg_right ?_ hsN.le
      have := mul_le_mul_of_nonneg_right hΔu hG0
      rw [hX]; linarith
    have h2 : 9 / 8 * Gu * Δu * Real.sqrt (2 * ℓu / N) = Δu * Y / Real.sqrt N := by
      rw [mul_div_assoc Δu Y (Real.sqrt N), hYN]; ring
    have h3 : Δu * X / Real.sqrt N + Δu * Y / Real.sqrt N = Δu * (X + Y) / Real.sqrt N := by ring
    have h4 : Δu * (X + Y) / Real.sqrt N ≤ 5 / 8 * elo := by
      rw [div_le_iff₀ hsN]; exact hXY'
    linarith
  -- the rounding
  have hβΔ : β * Δ ≤ elo / 8 := by
    have h1 : β * Δ ≤ βu * Δu := mul_le_mul hβu hΔu hΔ.le hβu0
    have h2 : (βu * Δu) ^ 2 ≤ (elo / 8) ^ 2 := by
      have e1 : (βu * Δu) ^ 2 = βu ^ 2 * Δu ^ 2 := by ring
      have e2 : (elo / 8) ^ 2 = elo ^ 2 / 64 := by ring
      rw [e1, e2]; exact hβc
    have h3 : βu * Δu ≤ elo / 8 := le_of_sq_le_sq h2 (by positivity)
    linarith
  linarith

open AdversarialBco.Bit.Aux_tri_par_row in
/-- **The row (R) of TRI-OGD-O at the parameters of dimension `d`**: for every `τ_s ∈ [0, e_lo/16]`, the five terms of
`triCoreTau`'s row at `Δ = (triD2 d)^{1/2}`, `G_b = G_up'`, `β = β_up`, `s = 2^{-j_s'}`, `N = 2^{n'}` and an integer
`ℓ ≥ log(1/δ)` are at most `e_h(ρ_h)`. -/
theorem tri_par_row_tau (d ℓ : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hℓ : Real.log (1 / δ) ≤ ℓ) (τs : ℝ) (hτe : 16 * τs ≤ triElo d) :
    0 < triD2 d ∧
      Real.sqrt (triD2 d) ^ 2 / (2 * (1 / 2 ^ triJsT d ℓ) * (2 ^ triNeT d ℓ : ℕ)) +
          (1 / 2 ^ triJsT d ℓ) / 2 * (triGuT d + triBu d) ^ 2 + triBu d * Real.sqrt (triD2 d) +
          (triGuT d * Real.sqrt (triD2 d) + τs) *
            Real.sqrt (2 * Real.log (1 / δ) / (2 ^ triNeT d ℓ : ℕ)) +
          2 * τs + 2 * triEpsG d ≤ pgEh d (triRh d) := by
  obtain ⟨hD2, helo0, helo1, heloEh⟩ := tri_par_basic d hd
  have hD20 : 0 < triD2 d := lt_of_lt_of_le (by norm_num) hD2
  refine ⟨hD20, ?_⟩
  have hℓ0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hℓr : (0 : ℝ) ≤ ℓ := hℓ0.trans hℓ
  have hβ0 : 0 ≤ triBu d := by unfold triBu; positivity
  have hG2 : 2 ≤ triGu d := by
    unfold triGu
    have : (0 : ℝ) ≤ 2 ^ triJa d / 8 := by positivity
    have : (0 : ℝ) ≤ (Nat.sqrt (8 * d * triKg d) : ℝ) := Nat.cast_nonneg _
    linarith
  have hGT : triGuT d = 65 / 64 * triGu d := by unfold triGuT; ring
  have hGT2 : 2 ≤ triGuT d := by rw [hGT]; linarith
  have hsq : Real.sqrt (triD2 d) ^ 2 = triD2 d := Real.sq_sqrt hD20.le
  have hNc' : ((2 ^ triNeT d ℓ : ℕ) : ℝ) = 2 ^ triNeT d ℓ := by push_cast; ring
  have hNT : (2 : ℝ) ^ triNeT d ℓ = 2 * 2 ^ triNe d ℓ := by unfold triNeT; rw [pow_succ]; ring
  -- the horizon of v2.1
  have hNY : 16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) / (9 * triElo d ^ 2) ≤
      (2 : ℝ) ^ triNe d ℓ := by
    have := tpr_clog_le 2 (by norm_num)
      (16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) / (9 * triElo d ^ 2))
    simp only [Nat.cast_ofNat] at this
    exact this
  rw [div_le_iff₀ (by positivity)] at hNY
  -- the rounding grid
  have hBv : 64 * (d + 1) ^ 2 * triD2 d / triElo d ^ 2 ≤ (4 : ℝ) ^ triBv d := by
    have := tpr_clog_le 4 (by norm_num) (64 * (d + 1) ^ 2 * triD2 d / triElo d ^ 2)
    simp only [Nat.cast_ofNat] at this
    exact this
  rw [div_le_iff₀ (by positivity)] at hBv
  -- the sampler bits
  have hKg : 16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d ≤ (2 : ℝ) ^ triKg d := by
    have := tpr_clog_le 2 (by norm_num) (16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d)
    simp only [Nat.cast_ofNat] at this
    refine this.trans (pow_le_pow_right₀ (by norm_num) ?_)
    unfold triKg
    exact le_max_right _ _
  rw [div_le_iff₀ helo0] at hKg
  -- the two facts of the horizon in the monomials `A = Δ² (G_up + β_up)²`, `B = Δ² G_up² ℓ`, `E = e_lo² 2^n`
  have hel2 : triElo d ^ 2 ≤ 1 := pow_le_one₀ helo0.le helo1
  have hA0 : 0 ≤ triD2 d * (triGu d + triBu d) ^ 2 := by positivity
  have hB0 : 0 ≤ triD2 d * (triGu d ^ 2 * ℓ) := by positivity
  have hNY' : 72 * (triD2 d * (triGu d + triBu d) ^ 2) + 64 * (triD2 d * (triGu d ^ 2 * ℓ)) ≤
      9 * (triElo d ^ 2 * 2 ^ triNe d ℓ) := by
    have e1 : 16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) =
        72 * (triD2 d * (triGu d + triBu d) ^ 2) + 64 * (triD2 d * (triGu d ^ 2 * ℓ)) := by ring
    have e2 : (2 : ℝ) ^ triNe d ℓ * (9 * triElo d ^ 2) = 9 * (triElo d ^ 2 * 2 ^ triNe d ℓ) := by ring
    rw [← e1, ← e2]; exact hNY
  have hE1 : triElo d ^ 2 * 2 ^ triNe d ℓ ≤ 2 ^ triNe d ℓ := by
    have := mul_le_mul_of_nonneg_right hel2 (by positivity : (0 : ℝ) ≤ 2 ^ triNe d ℓ)
    linarith
  -- the step
  have hX1 : 1 < (triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ / triD2 d := by
    rw [one_lt_div hD20, hNT]
    have hG' : 4 ≤ (triGu d + triBu d) ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) (show (2 : ℝ) ≤ triGu d + triBu d by linarith) 2
      norm_num at this; exact this
    have hGT' : 4 ≤ (triGuT d + triBu d) ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num) (show (2 : ℝ) ≤ triGuT d + triBu d by linarith) 2
      norm_num at this; exact this
    have h4A : 4 * triD2 d ≤ triD2 d * (triGu d + triBu d) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hG' hD20.le; linarith
    have h8 : 32 * triD2 d ≤ 2 ^ triNe d ℓ := by linarith
    have hA : 4 * (32 * triD2 d) ≤ (triGuT d + triBu d) ^ 2 * 2 ^ triNe d ℓ :=
      mul_le_mul hGT' h8 (by positivity) (by positivity)
    linarith
  have hJs := tpr_clog_le 4 (by norm_num) ((triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ / triD2 d)
  have hJs' := tpr_clog_lt 4 (by norm_num) ((triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ / triD2 d) hX1
  simp only [Nat.cast_ofNat] at hJs hJs'
  change _ ≤ (4 : ℝ) ^ triJsT d ℓ at hJs
  change (4 : ℝ) ^ triJsT d ℓ < _ at hJs'
  have h4 : ((2 : ℝ) ^ triJsT d ℓ) ^ 2 = 4 ^ triJsT d ℓ := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4p : (0 : ℝ) < 4 ^ triJsT d ℓ := by positivity
  have hsD : (1 / 4 : ℝ) ≤ Real.sqrt (triD2 d) := by
    rw [Real.le_sqrt (by norm_num) hD20.le]; linarith
  refine (tri_row_tau (Real.sqrt (triD2 d)) (Real.sqrt (triD2 d)) (triGuT d) (triGuT d) (triBu d) (triBu d)
    (Real.log (1 / δ)) ℓ (1 / 2 ^ triJsT d ℓ) ((2 ^ triNeT d ℓ : ℕ) : ℝ) (triEpsG d) (triElo d) τs
    (Real.sqrt_pos.2 hD20) le_rfl (by linarith) le_rfl hβ0 le_rfl hℓ0 hℓ (by positivity) (by positivity)
    ?_ ?_ ?_ ?_ ?_ helo0.le hτe ?_).trans heloEh
  · -- hs1
    rw [hsq, div_pow, one_pow, h4, hNc']
    rw [mul_div_assoc', lt_div_iff₀ hD20] at hJs'
    rw [show 4 * (1 / 4 ^ triJsT d ℓ) * (triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ =
      4 * ((triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ) / 4 ^ triJsT d ℓ by ring, lt_div_iff₀ h4p]
    linarith
  · -- hs2
    rw [hsq, div_pow, one_pow, h4, hNc']
    rw [div_le_iff₀ hD20] at hJs
    rw [show 1 / 4 ^ triJsT d ℓ * (triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ =
      (triGuT d + triBu d) ^ 2 * 2 ^ triNeT d ℓ / 4 ^ triJsT d ℓ by ring, div_le_iff₀ h4p]
    linarith
  · -- hNc: one doubling of v2.1's horizon absorbs `G_up' = (65/64) G_up` and the slack in the Hoeffding term
    rw [hsq, hNc', hNT]
    have hGTb : (triGuT d + triBu d) ^ 2 ≤ (65 / 64) ^ 2 * (triGu d + triBu d) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hGT]; linarith) 2
    have hC : triD2 d * (triGuT d + triBu d) ^ 2 ≤ (65 / 64) ^ 2 * (triD2 d * (triGu d + triBu d) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hGTb hD20.le; linarith
    have e : triD2 d * (2 * (3 / 2 * (triGuT d + triBu d)) ^ 2 + 2 * (2 * (9 / 8 * triGuT d) ^ 2 * ℓ)) =
        9 / 2 * (triD2 d * (triGuT d + triBu d) ^ 2) + 81 / 16 * (65 / 64) ^ 2 * (triD2 d * (triGu d ^ 2 * ℓ)) := by
      rw [hGT]; ring
    have e2 : 25 / 64 * triElo d ^ 2 * (2 * 2 ^ triNe d ℓ) = 25 / 32 * (triElo d ^ 2 * 2 ^ triNe d ℓ) := by ring
    rw [e, e2]
    linarith
  · -- hβc
    rw [hsq]
    unfold triBu
    rw [div_pow, show ((2 : ℝ) ^ triBv d) ^ 2 = 4 ^ triBv d by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    have h4b : (0 : ℝ) < 4 ^ triBv d := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ h4b]
    linarith
  · -- hεc
    unfold triEpsG
    have h2k : (0 : ℝ) < 2 ^ triKg d := by positivity
    rw [mul_div_assoc', div_le_iff₀ h2k]
    linarith
  · -- hτG
    have h1 : 2 * (1 / 4) ≤ triGuT d * Real.sqrt (triD2 d) := mul_le_mul hGT2 hsD (by norm_num) (by positivity)
    linarith

/-- `G_up'` bounds the field of TRI-OGD-O: `(1 + a_s)² + ((1 + a_s) M_d + κ/(√d a))² ≤ G_up'²` for
`0 ≤ a_s ≤ 1/64`, `M_d = (8 d k_g)^{1/2}` (the hypothesis `hGb` of `triCoreTau`). -/
theorem tri_par_GuT (d : ℕ) (hd : 1 ≤ d) (as : ℝ) (has0 : 0 ≤ as) (has : as ≤ 1 / 64) :
    0 ≤ triGuT d ∧ (1 + as) ^ 2 + ((1 + as) * Real.sqrt (8 * d * triKg d) + pgKappa / (Real.sqrt d * triA d)) ^ 2 ≤
      triGuT d ^ 2 := by
  obtain ⟨hGu0, hGu⟩ := tri_par_Gu d hd
  obtain ⟨-, -, -, hA0, -, -, -, -⟩ := tri_par_box d hd
  have hGT : triGuT d = 65 / 64 * triGu d := by unfold triGuT; ring
  refine ⟨by rw [hGT]; positivity, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M, M = Real.sqrt (8 * d * triKg d) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = pgKappa / (Real.sqrt d * triA d) := ⟨_, rfl⟩
  rw [← hM, ← hk] at hGu ⊢
  have hk0 : 0 ≤ k := by rw [hk]; unfold pgKappa; positivity
  have hM0 : 0 ≤ M := by rw [hM]; exact Real.sqrt_nonneg _
  have h1 : (1 + as) * M + k ≤ (1 + as) * (M + k) := by
    have := mul_nonneg has0 hk0; linarith
  have h2 : ((1 + as) * M + k) ^ 2 ≤ ((1 + as) * (M + k)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (1 + as) ^ 2 ≤ (65 / 64) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h4 : (1 + as) ^ 2 * (1 + (M + k) ^ 2) ≤ (65 / 64) ^ 2 * triGu d ^ 2 :=
    mul_le_mul h3 hGu (by positivity) (by positivity)
  have e1 : ((1 + as) * (M + k)) ^ 2 = (1 + as) ^ 2 * (M + k) ^ 2 := by ring
  have e2 : (65 / 64 * triGu d) ^ 2 = (65 / 64) ^ 2 * triGu d ^ 2 := by ring
  rw [hGT, e2]
  linarith

/-! ## The SEP parameters -/

/-- `e_1`: `ℓ_1 = 2^{-e_1} ≤ e_lo/64`. -/
noncomputable def triE1 (d : ℕ) : ℕ := Nat.clog 2 ⌈64 / triElo d⌉₊

/-- `e_τ`: `τ = 2^{-e_τ}` with `64 τ d (1 + 8 d k_g)(Δ² + 1) ≤ e_lo`, a rational majorant of
`64 τ √d (1 + M_d) Δ ≤ e_lo`. -/
noncomputable def triETau (d : ℕ) : ℕ :=
  Nat.clog 2 ⌈64 * d * (1 + 8 * d * triKg d) * (triD2 d + 1) / triElo d⌉₊

/-- The slope of (SEP0) at the choice `τ = 2^{-e_τ}`: `a_s = τ √d`. -/
noncomputable def triAs (d : ℕ) : ℝ := (1 / 2 ^ triETau d) * Real.sqrt d

/-- The offset of (SEP0) at the choice: `c_s = (2 L + 2 τ √d) (64/63) ℓ_1` with `L = 1`. -/
noncomputable def triCs (d : ℕ) : ℝ := (2 * 1 + 2 * triAs d) * (64 / 63 * (1 / 2 ^ triE1 d))

/-- The slack `τ_s = a_s (1 + M_d) Δ + c_s` of the row. -/
noncomputable def triTauS (d : ℕ) : ℝ :=
  triAs d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) + triCs d

open AdversarialBco.Bit.Aux_tri_par_row in
/-- **The SEP parameters close the row**: at `τ = 2^{-e_τ}`, `ℓ_1 = 2^{-e_1}`, the slope `a_s = τ√d` is in
`[0, 1/64]`, the offset is nonnegative, and `τ_s = a_s (1 + M_d) Δ + c_s ≤ e_lo/16`. -/
theorem tri_par_tau (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ triAs d ∧ triAs d ≤ 1 / 64 ∧ 0 ≤ triCs d ∧ 0 ≤ triTauS d ∧ 16 * triTauS d ≤ triElo d := by
  obtain ⟨hD2, helo0, helo1, -⟩ := tri_par_basic d hd
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hkg : (2 : ℝ) ≤ triKg d := by
    have : 2 ≤ triKg d := le_max_left _ _
    exact_mod_cast this
  obtain ⟨e, he⟩ : ∃ e, e = (1 : ℝ) / 2 ^ triETau d := ⟨_, rfl⟩
  obtain ⟨l1, hl1⟩ : ∃ l1, l1 = (1 : ℝ) / 2 ^ triE1 d := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  have hl10 : 0 < l1 := by rw [hl1]; positivity
  -- `ℓ_1 ≤ e_lo/64`
  have hE1 : 64 / triElo d ≤ (2 : ℝ) ^ triE1 d := by
    have := tpr_clog_le 2 (by norm_num) (64 / triElo d)
    simp only [Nat.cast_ofNat] at this
    exact this
  have hl1e : 64 * l1 ≤ triElo d := by
    rw [div_le_iff₀ helo0] at hE1
    have h2 : (0 : ℝ) < 2 ^ triE1 d := by positivity
    rw [hl1, mul_one_div, div_le_iff₀ h2]
    linarith
  -- `64 τ d (1 + 8 d k_g)(Δ² + 1) ≤ e_lo`
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (d : ℝ) * ((1 + 8 * d * triKg d) * (triD2 d + 1)) := ⟨_, rfl⟩
  have hET : 64 * d * (1 + 8 * d * triKg d) * (triD2 d + 1) / triElo d ≤ (2 : ℝ) ^ triETau d := by
    have := tpr_clog_le 2 (by norm_num) (64 * d * (1 + 8 * d * triKg d) * (triD2 d + 1) / triElo d)
    simp only [Nat.cast_ofNat] at this
    exact this
  have heT : 64 * (e * Z) ≤ triElo d := by
    rw [div_le_iff₀ helo0] at hET
    have h2 : (0 : ℝ) < 2 ^ triETau d := by positivity
    have e1 : 64 * (e * Z) = (64 * d * (1 + 8 * d * triKg d) * (triD2 d + 1)) / 2 ^ triETau d := by
      rw [he, hZ]; ring
    rw [e1, div_le_iff₀ h2]
    linarith
  -- the majorants `√d ≤ d`, `1 + M_d ≤ 1 + 8 d k_g`, `Δ ≤ Δ² + 1`
  have h8 : (1 : ℝ) ≤ 8 * d * triKg d := by
    have := mul_le_mul hd0 hkg (by norm_num) (by positivity)
    linarith
  have hsd : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by positivity)]; exact le_self_pow₀ hd0 (by norm_num)
  have hM : 1 + Real.sqrt (8 * d * triKg d) ≤ 1 + 8 * d * triKg d := by
    have : Real.sqrt (8 * d * triKg d) ≤ 8 * d * triKg d := by
      rw [Real.sqrt_le_left (by positivity)]; exact le_self_pow₀ h8 (by norm_num)
    linarith
  have hD20 : 0 ≤ triD2 d := by linarith
  have hΔ : Real.sqrt (triD2 d) ≤ triD2 d + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (triD2 d)]
  have hM0 : 0 ≤ 1 + Real.sqrt (8 * d * triKg d) := by positivity
  have hΔ0 : 0 ≤ Real.sqrt (triD2 d) := Real.sqrt_nonneg _
  have hprod : Real.sqrt d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) ≤ Z := by
    rw [hZ]
    exact mul_le_mul hsd (mul_le_mul hM hΔ hΔ0 (by positivity)) (by positivity) (by positivity)
  have hZ1 : (d : ℝ) ≤ Z := by
    rw [hZ]
    have h1 : (1 : ℝ) ≤ (1 + 8 * d * triKg d) * (triD2 d + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    exact le_mul_of_one_le_right (by positivity) h1
  -- the slope
  have hAs : triAs d = e * Real.sqrt d := by unfold triAs; rw [he]
  have hAs0 : 0 ≤ triAs d := by rw [hAs]; positivity
  have hAsT : 64 * (triAs d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d))) ≤ triElo d := by
    have h1 : e * (Real.sqrt d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d))) ≤ e * Z :=
      mul_le_mul_of_nonneg_left hprod he0.le
    have e1 : triAs d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d)) =
        e * (Real.sqrt d * ((1 + Real.sqrt (8 * d * triKg d)) * Real.sqrt (triD2 d))) := by rw [hAs]; ring
    rw [e1]
    linarith
  have hAs1 : triAs d ≤ 1 / 64 := by
    have h1 : e * Real.sqrt d ≤ e * Z := mul_le_mul_of_nonneg_left (hsd.trans hZ1) he0.le
    rw [hAs]
    linarith
  have hCs : triCs d = (2 * 1 + 2 * triAs d) * (64 / 63 * l1) := by unfold triCs; rw [hl1]
  have hCs0 : 0 ≤ triCs d := by rw [hCs]; positivity
  refine ⟨hAs0, hAs1, hCs0, ?_, ?_⟩
  · unfold triTauS; positivity
  · have hc : triCs d ≤ 65 / 32 * (triElo d / 63) := by
      rw [hCs]
      have h1 : (2 * 1 + 2 * triAs d) ≤ 65 / 32 := by linarith
      have h2 : 64 / 63 * l1 ≤ triElo d / 63 := by linarith
      exact mul_le_mul h1 h2 (by positivity) (by norm_num)
    unfold triTauS
    linarith

end AdversarialBco.UniPos
