/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.BoxMuller
public import AdversarialBco.StatementBitRAM

@[expose] public section

/-!
# Lemmas of Procedure BM-INT, the Gaussian pair from `2B` fair coins in integer arithmetic

The definitions of Procedure BM-INT come first: `gsm_powq` and `gsm_mercq` (the fixed-point powers and
Mercator sum), `gsm_LLq` (step 4, the scaled value of `-log u'`), `gsm_chainq` (the integer half-angle chain),
`gsm_cmulq` (one rounded complex product).

* Lemma MERC and LOG in fixed point: `gsm_powq_err` (the powers stay within `3 · 2^{-q}` below `x^{i+1}`),
  `gsm_mercq_sum_err` (the truncated sum within `4n · 2^{-q}`) and `gsm_mercq_log_err` (`-log(1 - x)` minus the
  fixed-point sum).
* Lemma ROOT: `gsm_sqrt_lip` (`|√a - √b| ≤ √|a - b|`); Corollary RAD: `gsm_radius_err` (the integer square root of
  `2 LL` against `√(2L)`).
* Lemma CHAIN: `gsm_half_angle`, `gsm_cos_pi_succ` (the half-angle identities) and `gsm_chainq_err` (the chain within
  `1.547 · 2^{-p}` for the cosine, one-sided, and `8.97 · 2^{-p}` for the sine).
* Lemma ANGLE: `gsm_angle_digits` (`2π J/2^B` over the binary digits of `J`); Lemma PROD: `gsm_cmulq_err` (one rounded
  complex product).
* The integer routines of the program: `gsm_X_floor` (step 2: `X` is the floor of `2^q x` for
  `x = 1 - 2^e/N ∈ [0, 1/2)`, and `log(N/2^e) = -log(1 - x)`), `gsm_LLq_err` (step 4: `LL/2^q` within
  `B (4q + 1) 2^{-q}` of `-log u'`).
* LAW-3: `gsm_readCoins_law` (a block of `k` coins read as an integer is uniform on `[0, 2^k)`).

Each lemma sits in a
namespace `AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at `AdversarialBco.Bit.<name>`.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

/-- fixed-point powers: `gsm_powq q X i = P_{i+1}` -/
def gsm_powq (q X : ℕ) : ℕ → ℕ
  | 0 => X
  | i + 1 => gsm_powq q X i * X / 2 ^ q

/-- the fixed-point Mercator sum `S_n` -/
def gsm_mercq (q X n : ℕ) : ℕ := ∑ i ∈ Finset.range n, gsm_powq q X i / (i + 1)

/-- step 4 of Procedure BM-INT: the scaled value of `-log u'` -/
def gsm_LLq (B q U : ℕ) : ℤ :=
  max (((B : ℤ) - Nat.log 2 (U + 1)) * gsm_mercq q (2 ^ (q - 1)) q
        - gsm_mercq q ((U + 1 - 2 ^ Nat.log 2 (U + 1)) * 2 ^ q / (U + 1)) q) 0

/-- the half-angle chain: `gsm_chainq p k` approximates `2^p (cos, sin)(π/2^(k+1))` -/
def gsm_chainq (p : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 2 ^ p)
  | k + 1 => let cs := gsm_chainq p k; let c := Nat.sqrt (2 ^ (p - 1) * (2 ^ p + cs.1)); (c, cs.2 * 2 ^ (p - 1) / c)

/-- one rounded complex product at scale `2^p` -/
def gsm_cmulq (p : ℕ) (z f : ℤ × ℤ) : ℤ × ℤ :=
  ((z.1 * f.1 - z.2 * f.2) / 2 ^ p, (z.1 * f.2 + z.2 * f.1) / 2 ^ p)

end AdversarialBco.Bit

namespace AdversarialBco.Bit.Aux_gsm_powq_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_powq_err (q X : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hX : (X : ℝ) ≤ 2 ^ q * x) (hX' : 2 ^ q * x < X + 1) (i : ℕ) :
    0 ≤ x ^ (i + 1) - (AdversarialBco.Bit.gsm_powq q X i : ℝ) / 2 ^ q ∧ x ^ (i + 1) - (AdversarialBco.Bit.gsm_powq q X i : ℝ) / 2 ^ q < 3 / 2 ^ q := by
  have hpos2q : 0 < (2 ^ q : ℝ) := pow_pos (by norm_num) q
  have hpos2q' : 0 ≤ (2 ^ q : ℝ) := le_of_lt hpos2q
  set d := (2 ^ q : ℝ) with hd
  set a := λ (k : ℕ) => (AdversarialBco.Bit.gsm_powq q X k : ℝ) / d with ha
  set xq := (X : ℝ) / d with hxq
  have hxq_le_x : xq ≤ x := by
    dsimp [xq]
    calc
      (X : ℝ) / d ≤ (d * x) / d := div_le_div_of_nonneg_right hX (by dsimp [d]; exact hpos2q')
      _ = x := by field_simp [hpos2q.ne']
  have hx_sub_xq_lt : x - xq < 1 / d := by
    dsimp [xq]
    calc
      x - (X : ℝ) / d = (d * x - (X : ℝ)) / d := by
        field_simp [hpos2q.ne']
      _ < ((X : ℝ) + 1 - (X : ℝ)) / d := by
        apply div_lt_div_of_pos_right ?_ hpos2q
        linarith
      _ = 1 / d := by ring
  have hx_sub_xq_nonneg : 0 ≤ x - xq := by
    linarith
  -- helper lemma: for any n : ℕ, ((n / 2^q : ℕ) : ℝ) ≤ (n : ℝ) / d
  have hdiv_upper (n : ℕ) : ((n / 2 ^ q : ℕ) : ℝ) ≤ (n : ℝ) / d := by
    simpa [d] using Nat.cast_div_le (m := n) (n := 2 ^ q)
  -- helper lemma: for any n : ℕ, ((n / 2^q : ℕ) : ℝ) > (n : ℝ) / d - 1
  have hdiv_lower (n : ℕ) : ((n / 2 ^ q : ℕ) : ℝ) > (n : ℝ) / d - 1 := by
    have hmod : n % 2 ^ q < 2 ^ q := Nat.mod_lt n (pow_pos (by norm_num) q)
    have h_eq := Nat.div_add_mod n (2 ^ q)
    -- h_eq: (2 ^ q) * (n / (2 ^ q)) + n % (2 ^ q) = n  (in ℕ)
    have h_eq' : (d * ((n / 2 ^ q : ℕ) : ℝ) + ((n % 2 ^ q : ℕ) : ℝ) = (n : ℝ)) := by
      simpa [d, mul_comm] using congrArg (fun t : ℕ => (t : ℝ)) h_eq
    have h_mod_lt : ((n % 2 ^ q : ℕ) : ℝ) < d := by
      dsimp [d]
      have : (n % 2 ^ q : ℕ) < 2 ^ q := hmod
      exact_mod_cast this
    calc
      ((n / 2 ^ q : ℕ) : ℝ) = ((n : ℝ) - ((n % 2 ^ q : ℕ) : ℝ)) / d := by
        field_simp [hpos2q.ne']
        linarith
      _ = (n : ℝ) / d - ((n % 2 ^ q : ℕ) : ℝ) / d := by ring
      _ > (n : ℝ) / d - 1 := by
        apply sub_lt_sub_left ?_ ((n : ℝ) / d)
        apply (div_lt_one hpos2q).mpr
        exact h_mod_lt
  -- recurrence relations for a
  have ha_succ_upper (k : ℕ) : a (k + 1) ≤ a k * xq := by
    dsimp [a, xq, d, AdversarialBco.Bit.gsm_powq]
    have h := hdiv_upper (AdversarialBco.Bit.gsm_powq q X k * X)
    -- h: ((gsm_powq q X k * X / 2^q : ℕ) : ℝ) ≤ (gsm_powq q X k * X : ℝ) / d
    -- goal: ((gsm_powq q X k * X / 2^q : ℕ) : ℝ) / (2 ^ q : ℝ) ≤ ((gsm_powq q X k : ℝ) / (2 ^ q : ℝ)) * ((X : ℝ) / (2 ^ q : ℝ))
    -- Note: d is (2 ^ q : ℝ), so h is about / d, goal is about / (2 ^ q : ℝ). They are the same.
    -- But the RHS of the goal uses (2 ^ q : ℝ) while h uses d.
    -- Let's use h directly with dsimp [d] at h
    have h' : ((AdversarialBco.Bit.gsm_powq q X k * X / 2 ^ q : ℕ) : ℝ) ≤ (AdversarialBco.Bit.gsm_powq q X k * X : ℝ) / (2 ^ q : ℝ) := by
      simpa [d] using h
    calc
      ((AdversarialBco.Bit.gsm_powq q X k * X / 2 ^ q : ℕ) : ℝ) / (2 ^ q : ℝ)
          ≤ ((AdversarialBco.Bit.gsm_powq q X k * X : ℝ) / (2 ^ q : ℝ)) / (2 ^ q : ℝ) := by
        apply div_le_div_of_nonneg_right h' hpos2q'
      _ = ((AdversarialBco.Bit.gsm_powq q X k : ℝ) / (2 ^ q : ℝ)) * ((X : ℝ) / (2 ^ q : ℝ)) := by ring
  have ha_succ_lower (k : ℕ) : a k * xq - 1 / d < a (k + 1) := by
    dsimp [a, xq, d, AdversarialBco.Bit.gsm_powq]
    have h := hdiv_lower (AdversarialBco.Bit.gsm_powq q X k * X)
    -- h: ((gsm_powq q X k * X / 2^q : ℕ) : ℝ) > (gsm_powq q X k * X : ℝ) / d - 1
    have h' : ((AdversarialBco.Bit.gsm_powq q X k * X / 2 ^ q : ℕ) : ℝ) > (AdversarialBco.Bit.gsm_powq q X k * X : ℝ) / (2 ^ q : ℝ) - 1 := by
      simpa [d] using h
    calc
      (((AdversarialBco.Bit.gsm_powq q X k : ℝ) / (2 ^ q : ℝ)) * ((X : ℝ) / (2 ^ q : ℝ))) - 1 / (2 ^ q : ℝ)
          = (((AdversarialBco.Bit.gsm_powq q X k * X : ℝ) / (2 ^ q : ℝ)) - 1) / (2 ^ q : ℝ) := by ring
      _ < ((AdversarialBco.Bit.gsm_powq q X k * X / 2 ^ q : ℕ) : ℝ) / (2 ^ q : ℝ) := by
        apply div_lt_div_of_pos_right ?_ hpos2q
        simpa using h'
  have ha_nonneg (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    apply div_nonneg (Nat.cast_nonneg _) hpos2q'
  -- main induction
  induction' i with i ih
  · -- base case i = 0
    have ha0 : a 0 = xq := by
      dsimp [a, xq, d, AdversarialBco.Bit.gsm_powq]
    have h_nonneg : 0 ≤ x ^ (0 + 1) - a 0 := by
      rw [ha0, pow_one]
      exact hx_sub_xq_nonneg
    have h_lt : x ^ (0 + 1) - a 0 < 3 / d := by
      rw [ha0, pow_one]
      have h : 1 / d ≤ 3 / d := by
        apply div_le_div_of_nonneg_right (by norm_num) hpos2q'
      linarith
    exact And.intro h_nonneg h_lt
  · -- inductive step
    rcases ih with ⟨h_nonneg, h_lt⟩
    have ha_le_xpow : a i ≤ x ^ (i + 1) := by
      linarith
    have hxpow_le_x : x ^ (i + 1) ≤ x := by
      have hx1' : x ≤ 1 := by linarith
      have h_exp : 1 ≤ i + 1 := by omega
      have h := pow_le_pow_of_le_one hx0 hx1' h_exp
      simpa [pow_one] using h
    -- identity: x^(i+2) - a(i+1) = x*(x^(i+1) - a i) + (a i * xq - a(i+1)) + a i * (x - xq)
    have h_eq : x ^ (i + 1 + 1) - a (i + 1) =
        x * (x ^ (i + 1) - a i) + (a i * xq - a (i + 1)) + a i * (x - xq) := by
      calc
        x ^ (i + 1 + 1) - a (i + 1) = x * (x ^ (i + 1)) - a (i + 1) := by rw [pow_succ, mul_comm]
        _ = x * (x ^ (i + 1) - a i) + x * a i - a (i + 1) := by ring
        _ = x * (x ^ (i + 1) - a i) + (a i * xq - a (i + 1)) + (x * a i - a i * xq) := by ring
        _ = x * (x ^ (i + 1) - a i) + (a i * xq - a (i + 1)) + a i * (x - xq) := by ring
    have h_lower : 0 ≤ x ^ (i + 1 + 1) - a (i + 1) := by
      rw [h_eq]
      have h1 : 0 ≤ x * (x ^ (i + 1) - a i) := by
        apply mul_nonneg hx0
        linarith
      have h2 : 0 ≤ a i * xq - a (i + 1) := by
        linarith [ha_succ_upper i]
      have h3 : 0 ≤ a i * (x - xq) := by
        apply mul_nonneg (ha_nonneg i)
        linarith
      nlinarith
    have h_upper : x ^ (i + 1 + 1) - a (i + 1) < 3 / d := by
      rw [h_eq]
      have hd' : d ≠ 0 := by linarith
      field_simp [hd']
      -- goal: (x * (x^(i+1) - a i) + (a i * xq - a(i+1)) + a i * (x - xq)) * d < 3
      have h1' : x * (x ^ (i + 1) - a i) * d ≤ x * 3 := by
        calc
          x * (x ^ (i + 1) - a i) * d ≤ (x * (3 / d)) * d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_lt.le hx0) (by linarith)
          _ = x * 3 := by field_simp [hd']
      have h2' : a i * (x - xq) * d ≤ x * 1 := by
        calc
          a i * (x - xq) * d ≤ (x * (1 / d)) * d := by
            apply mul_le_mul_of_nonneg_right ?_ (by linarith)
            calc
              a i * (x - xq) ≤ x ^ (i + 1) * (x - xq) :=
                mul_le_mul_of_nonneg_right ha_le_xpow hx_sub_xq_nonneg
              _ ≤ x * (x - xq) := mul_le_mul_of_nonneg_right hxpow_le_x hx_sub_xq_nonneg
              _ ≤ x * (1 / d) := mul_le_mul_of_nonneg_left (by linarith) hx0
          _ = x * 1 := by field_simp [hd']
      have h3' : (a i * xq - a (i + 1)) * d < 1 := by
        calc
          (a i * xq - a (i + 1)) * d < (1 / d) * d :=
            mul_lt_mul_of_pos_right (by linarith [ha_succ_lower i]) hpos2q
          _ = 1 := by field_simp [hd']
      nlinarith
    exact And.intro h_lower h_upper

end AdversarialBco.Bit.Aux_gsm_powq_err

namespace AdversarialBco.Bit.Aux_gsm_mercq_sum_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

/-- One term of the fixed-point Mercator sum is within `[0, 4/2^q]` of `x^(i+1)/(i+1)`. -/
theorem _root_.AdversarialBco.Bit.gmse_term (q X : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hX : (X : ℝ) ≤ 2 ^ q * x) (hX' : 2 ^ q * x < X + 1) (i : ℕ) :
    0 ≤ x ^ (i + 1) / ((i : ℝ) + 1) - ((AdversarialBco.Bit.gsm_powq q X i / (i + 1) : ℕ) : ℝ) / 2 ^ q ∧
      x ^ (i + 1) / ((i : ℝ) + 1) - ((AdversarialBco.Bit.gsm_powq q X i / (i + 1) : ℕ) : ℝ) / 2 ^ q ≤
        4 / 2 ^ q := by
  obtain ⟨h0, h3⟩ := AdversarialBco.Bit.gsm_powq_err q X x hx0 hx1 hX hX' i
  set P := AdversarialBco.Bit.gsm_powq q X i
  set r := P / (i + 1)
  have hk : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hr1 : (r : ℝ) * ((i : ℝ) + 1) ≤ P := by
    have := Nat.div_mul_le_self P (i + 1)
    exact_mod_cast this
  have hr2 : (P : ℝ) < (r : ℝ) * ((i : ℝ) + 1) + ((i : ℝ) + 1) := by
    have h1 := Nat.div_add_mod P (i + 1)
    have h2 := Nat.mod_lt P (Nat.succ_pos i)
    have h3 : P < r * (i + 1) + (i + 1) := by
      calc P = (i + 1) * r + P % (i + 1) := h1.symm
        _ < (i + 1) * r + (i + 1) := Nat.add_lt_add_left h2 _
        _ = r * (i + 1) + (i + 1) := by ring
    exact_mod_cast h3
  have hP0 : (P : ℝ) ≤ x ^ (i + 1) * 2 ^ q := by
    have : (P : ℝ) / 2 ^ q ≤ x ^ (i + 1) := by linarith
    rwa [div_le_iff₀ hq] at this
  have hP3 : x ^ (i + 1) * 2 ^ q < P + 3 := by
    have h' := mul_lt_mul_of_pos_right h3 hq
    rw [sub_mul, div_mul_cancel₀ _ hq.ne', div_mul_cancel₀ _ hq.ne'] at h'
    linarith
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ hq hk]
    linarith
  · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hk hq]
    have e : (4 + (r : ℝ)) * ((i : ℝ) + 1) = 4 * ((i : ℝ) + 1) + (r : ℝ) * ((i : ℝ) + 1) := by ring
    rw [e]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith

theorem _root_.AdversarialBco.Bit.gsm_mercq_sum_err (q X : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hX : (X : ℝ) ≤ 2 ^ q * x) (hX' : 2 ^ q * x < X + 1) (n : ℕ) :
    0 ≤ (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q ∧
      (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q ≤ 4 * n / 2 ^ q := by
  have hcast : (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q =
      ∑ i ∈ Finset.range n, ((AdversarialBco.Bit.gsm_powq q X i / (i + 1) : ℕ) : ℝ) / 2 ^ q := by
    simp only [AdversarialBco.Bit.gsm_mercq, Nat.cast_sum, Finset.sum_div]
  rw [hcast, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun i _ => (AdversarialBco.Bit.gmse_term q X x hx0 hx1 hX hX' i).1
  · calc _ ≤ ∑ i ∈ Finset.range n, (4 : ℝ) / 2 ^ q :=
          Finset.sum_le_sum fun i _ => (AdversarialBco.Bit.gmse_term q X x hx0 hx1 hX hX' i).2
      _ = 4 * n / 2 ^ q := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end AdversarialBco.Bit.Aux_gsm_mercq_sum_err

namespace AdversarialBco.Bit.Aux_gsm_mercq_log_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_mercq_log_err (q X : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hX : (X : ℝ) ≤ 2 ^ q * x) (hX' : 2 ^ q * x < X + 1) (n : ℕ) :
    0 ≤ -Real.log (1 - x) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q ∧
      -Real.log (1 - x) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q ≤ 4 * n / 2 ^ q + (1 / 2) ^ n := by
  have hx_abs : |x| < 1 := by
    rw [abs_of_nonneg hx0]
    linarith
  have h_hasSum : HasSum (fun i : ℕ => x ^ (i + 1) / ((i : ℝ) + 1)) (-Real.log (1 - x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hx_abs
  have h_nonneg_terms : ∀ i : ℕ, 0 ≤ x ^ (i + 1) / ((i : ℝ) + 1) := by
    intro i
    have hpow : 0 ≤ x ^ (i + 1) := pow_nonneg hx0 (i + 1)
    have hdenom : 0 ≤ (i : ℝ) + 1 := by
      have : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
      linarith
    exact div_nonneg hpow hdenom
  have h_partial_sum_le : (∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1)) ≤ -Real.log (1 - x) := by
    have h := sum_le_hasSum (Finset.range n) (by
      intro i hi
      exact h_nonneg_terms i) h_hasSum
    exact h
  have h_sum_err := AdversarialBco.Bit.gsm_mercq_sum_err q X x hx0 hx1 hX hX' n
  rcases h_sum_err with ⟨h_err_lower, h_err_upper⟩
  have h_nonneg : 0 ≤ -Real.log (1 - x) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q := by
    linarith
  have h_upper : -Real.log (1 - x) - (AdversarialBco.Bit.gsm_mercq q X n : ℝ) / 2 ^ q ≤ 4 * n / 2 ^ q + (1 / 2) ^ n := by
    have h_abs := Real.abs_log_sub_add_sum_range_le hx_abs n
    have h_abs' := abs_le.mp h_abs
    rcases h_abs' with ⟨h_le, h_ge⟩
    -- h_le : ∑ ... + log(1-x) ≤ |x|^(n+1) / (1-|x|)
    -- h_ge : -(|x|^(n+1) / (1-|x|)) ≤ ∑ ... + log(1-x)
    have hx_abs_eq : |x| = x := abs_of_nonneg hx0
    rw [hx_abs_eq] at h_le h_ge
    -- h_le : ∑ ... + log(1-x) ≤ x^(n+1) / (1-x)
    -- From h_le: -log(1-x) - ∑ ... ≤ x^(n+1) / (1-x)
    have h_tail : -Real.log (1 - x) - (∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1)) ≤ x ^ (n + 1) / (1 - x) := by
      linarith
    have h_tail_bound : x ^ (n + 1) / (1 - x) ≤ ((1 : ℝ) / 2) ^ n := by
      have h_pow : x ^ (n + 1) ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
        refine Nat.rec ?_ (fun k ih => ?_) n
        · simpa using hx1
        · rw [pow_succ, pow_succ]
          have hhalf_nonneg : 0 ≤ (1 : ℝ) / 2 := by norm_num
          have hhalf_pow_nonneg : 0 ≤ ((1 : ℝ) / 2) ^ (k + 1) := pow_nonneg hhalf_nonneg (k + 1)
          exact mul_le_mul ih hx1 hx0 hhalf_pow_nonneg
      have h_denom_pos : 0 < 1 - x := by linarith
      have hhalf_pos : 0 < (1 : ℝ) / 2 := by norm_num
      have h_denom2 : (1 : ℝ) / 2 ≤ 1 - x := by linarith
      have h_pow_nonneg : 0 ≤ ((1 : ℝ) / 2) ^ (n + 1) := pow_nonneg (by norm_num) (n + 1)
      calc
        x ^ (n + 1) / (1 - x) ≤ ((1 : ℝ) / 2) ^ (n + 1) / (1 - x) :=
          div_le_div_of_nonneg_right h_pow (by linarith)
        _ ≤ ((1 : ℝ) / 2) ^ (n + 1) / ((1 : ℝ) / 2) :=
          div_le_div_of_nonneg_left h_pow_nonneg hhalf_pos h_denom2
        _ = ((1 : ℝ) / 2) ^ n := by ring
    have h_total : -Real.log (1 - x) - (∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1)) ≤ ((1 : ℝ) / 2) ^ n := by
      linarith
    linarith
  exact And.intro h_nonneg h_upper

end AdversarialBco.Bit.Aux_gsm_mercq_log_err

namespace AdversarialBco.Bit.Aux_gsm_sqrt_lip


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_sqrt_lip (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  by_cases h : b ≤ a
  · -- case b ≤ a
    have h_sqrt : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h
    have h_nonneg : 0 ≤ Real.sqrt a - Real.sqrt b := sub_nonneg.mpr h_sqrt
    have h_abs_sqrt : |Real.sqrt a - Real.sqrt b| = Real.sqrt a - Real.sqrt b := abs_of_nonneg h_nonneg
    have h_abs_ab : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr h)
    rw [h_abs_sqrt, h_abs_ab]
    -- need to show: Real.sqrt a - Real.sqrt b ≤ Real.sqrt (a - b)
    have h_sq : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a - b := by
      have h_sq_sqrt_a : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
      have h_sq_sqrt_b : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
      have h_sqrt_nonneg : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
      have h_mul : b ≤ Real.sqrt a * Real.sqrt b := by
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
      nlinarith
    -- Now use Real.abs_le_sqrt and abs_of_nonneg
    have h_abs_le := Real.abs_le_sqrt h_sq
    -- h_abs_le : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt (a - b)
    rwa [abs_of_nonneg h_nonneg] at h_abs_le
  · -- case a < b, i.e., ¬ b ≤ a
    have h' : a ≤ b := by linarith
    have h_sqrt : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h'
    have h_nonneg : 0 ≤ Real.sqrt b - Real.sqrt a := sub_nonneg.mpr h_sqrt
    have h_abs_sqrt : |Real.sqrt a - Real.sqrt b| = Real.sqrt b - Real.sqrt a := by
      rw [abs_sub_comm, abs_of_nonneg h_nonneg]
    have h_abs_ab : |a - b| = |b - a| := abs_sub_comm a b
    rw [h_abs_sqrt, h_abs_ab]
    rw [abs_of_nonneg (sub_nonneg.mpr h')]
    -- need to show: Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b - a)
    have h_sq : (Real.sqrt b - Real.sqrt a) ^ 2 ≤ b - a := by
      have h_sq_sqrt_a : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
      have h_sq_sqrt_b : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
      have h_sqrt_nonneg : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
      have h_mul : a ≤ Real.sqrt a * Real.sqrt b := by
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
      nlinarith
    have h_abs_le := Real.abs_le_sqrt h_sq
    rwa [abs_of_nonneg h_nonneg] at h_abs_le

end AdversarialBco.Bit.Aux_gsm_sqrt_lip

namespace AdversarialBco.Bit.Aux_gsm_radius_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_radius_err (p : ℕ) (LL : ℕ) (L e : ℝ) (hL : 0 ≤ L) (he : |(LL : ℝ) / 2 ^ (2 * p) - L| ≤ e) :
    |(Nat.sqrt (2 * LL) : ℝ) / 2 ^ p - Real.sqrt (2 * L)| ≤ Real.sqrt (2 * e) + 1 / 2 ^ p := by
  -- convenience: 2^p as ℝ
  set q := (2 : ℝ) ^ p with hq_def
  have hq_pos : 0 < q := by
    dsimp [q]
    exact pow_pos (by norm_num) p
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hq_sq_nonneg : 0 ≤ q ^ 2 := by nlinarith
  have hq_sq_eq : q ^ 2 = (2 : ℝ) ^ (2 * p) := by
    dsimp [q]
    calc
      ((2 : ℝ) ^ p) ^ 2 = (2 : ℝ) ^ (p * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * p) := by rw [mul_comm]
  -- Step 1: bound the integer sqrt difference
  have h_int_sqrt_le : (Nat.sqrt (2 * LL) : ℝ) ≤ Real.sqrt (2 * (LL : ℝ)) := by
    simpa [Nat.cast_mul, Nat.cast_ofNat] using Real.nat_sqrt_le_real_sqrt (a := 2 * LL)
  have h_real_sqrt_lt : Real.sqrt (2 * (LL : ℝ)) < (Nat.sqrt (2 * LL) : ℝ) + 1 := by
    simpa [Nat.cast_mul, Nat.cast_ofNat] using Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * LL)
  have h_diff_bound : |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * (LL : ℝ)) / q| ≤ 1 / q := by
    have h_nonneg : 0 ≤ Real.sqrt (2 * (LL : ℝ)) / q - (Nat.sqrt (2 * LL) : ℝ) / q := by
      have h := div_le_div_of_nonneg_right h_int_sqrt_le hq_nonneg
      nlinarith
    have h_lt : Real.sqrt (2 * (LL : ℝ)) / q - (Nat.sqrt (2 * LL) : ℝ) / q < 1 / q := by
      have h := div_lt_div_of_pos_right h_real_sqrt_lt hq_pos
      rw [add_div] at h
      nlinarith
    have h_abs_eq : |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * (LL : ℝ)) / q| =
        Real.sqrt (2 * (LL : ℝ)) / q - (Nat.sqrt (2 * LL) : ℝ) / q := by
      rw [abs_sub_comm, abs_of_nonneg h_nonneg]
    rw [h_abs_eq]
    nlinarith
  -- Step 2: relate Real.sqrt(2*LL)/q to Real.sqrt(2*LL / 2^(2*p))
  have h_sqrt_div_eq : Real.sqrt (2 * (LL : ℝ)) / q = Real.sqrt (2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p))) := by
    calc
      Real.sqrt (2 * (LL : ℝ)) / q = Real.sqrt (2 * (LL : ℝ)) / Real.sqrt (q ^ 2) := by
        rw [Real.sqrt_sq hq_nonneg]
      _ = Real.sqrt ((2 * (LL : ℝ)) / (q ^ 2)) := by
        rw [← Real.sqrt_div' (2 * (LL : ℝ)) hq_sq_nonneg]
      _ = Real.sqrt (2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p))) := by
        rw [hq_sq_eq]
  -- Step 3: apply gsm_sqrt_lip
  have h_lip : |Real.sqrt (2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p))) - Real.sqrt (2 * L)| ≤
      Real.sqrt |2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - 2 * L| := by
    apply gsm_sqrt_lip (2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p))) (2 * L)
    · positivity
    · nlinarith
  -- Step 4: bound the inner absolute value
  have h_inner_bound : Real.sqrt |2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - 2 * L| ≤ Real.sqrt (2 * e) := by
    refine Real.sqrt_le_sqrt ?_
    have h_eq : |2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - 2 * L| = 2 * |(LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - L| := by
      have h_inner : 2 * (LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - 2 * L = 2 * ((LL : ℝ) / ((2 : ℝ) ^ (2 * p)) - L) := by
        field_simp
      rw [h_inner, abs_mul, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    rw [h_eq]
    nlinarith
  -- Step 5: combine everything
  have h_target : |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * L)| ≤ Real.sqrt (2 * e) + 1 / q := by
    have h_tri : |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * L)| ≤
        |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * (LL : ℝ)) / q| +
        |Real.sqrt (2 * (LL : ℝ)) / q - Real.sqrt (2 * L)| := by
      calc
        |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * L)| =
            |((Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * (LL : ℝ)) / q) +
              (Real.sqrt (2 * (LL : ℝ)) / q - Real.sqrt (2 * L))| := by
          simp [sub_add_sub_cancel]
        _ ≤ |(Nat.sqrt (2 * LL) : ℝ) / q - Real.sqrt (2 * (LL : ℝ)) / q| +
            |Real.sqrt (2 * (LL : ℝ)) / q - Real.sqrt (2 * L)| :=
          abs_add_le _ _
    have h_second_bound : |Real.sqrt (2 * (LL : ℝ)) / q - Real.sqrt (2 * L)| ≤ Real.sqrt (2 * e) := by
      rw [h_sqrt_div_eq]
      nlinarith
    nlinarith
  -- Convert back from q to 2^p
  simpa [q] using h_target

end AdversarialBco.Bit.Aux_gsm_radius_err

namespace AdversarialBco.Bit.Aux_gsm_half_angle


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_half_angle (m : ℕ) (hm : 1 ≤ m) :
    Real.cos (Real.pi / 2 ^ (m + 1)) = Real.sqrt ((1 + Real.cos (Real.pi / 2 ^ m)) / 2) ∧
      Real.sin (Real.pi / 2 ^ (m + 1)) = Real.sin (Real.pi / 2 ^ m) / (2 * Real.cos (Real.pi / 2 ^ (m + 1))) := by
  set θ := Real.pi / 2 ^ m with hθ
  have hpow_pos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθ_lt_pi : θ < Real.pi := by
    dsimp [θ]
    have hm0 : 0 < m := Nat.lt_of_lt_of_le (by norm_num : 0 < 1) hm
    have h : (1 : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast Nat.pow_lt_pow_right (by norm_num : 1 < 2) hm0
    exact div_lt_self (by positivity : 0 < Real.pi) h
  have hθle : θ ≤ Real.pi := by linarith
  have hneg : -Real.pi ≤ θ := by linarith
  have hcos_half : Real.cos (θ / 2) = Real.sqrt ((1 + Real.cos θ) / 2) :=
    Real.cos_half hneg hθle
  have hcos_pos : 0 < Real.cos (θ / 2) := by
    have hmem : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have hhalfpos : 0 < θ / 2 := by linarith
      have hhalf_lt : θ / 2 < Real.pi / 2 := by
        have : θ ≤ Real.pi := hθle
        linarith
      exact ⟨by linarith, hhalf_lt⟩
    exact Real.cos_pos_of_mem_Ioo hmem
  have h_sin_eq : Real.sin (θ / 2) = Real.sin θ / (2 * Real.cos (θ / 2)) := by
    have hsin_two := Real.sin_two_mul (θ / 2)
    have hsinθ : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      calc
        Real.sin θ = Real.sin (2 * (θ / 2)) := by
          congr 1
          field_simp
        _ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by simpa using hsin_two
    apply (eq_div_iff (by nlinarith)).mpr
    calc
      Real.sin (θ / 2) * (2 * Real.cos (θ / 2)) = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by ring
      _ = Real.sin θ := by rw [hsinθ]
  have hθdiv : Real.pi / 2 ^ (m + 1) = θ / 2 := by
    dsimp [θ]
    calc
      Real.pi / 2 ^ (m + 1) = Real.pi / (2 ^ m * 2) := by rw [pow_succ]
      _ = (Real.pi / 2 ^ m) / 2 := by rw [div_div]
  rw [hθdiv]
  exact And.intro hcos_half h_sin_eq

end AdversarialBco.Bit.Aux_gsm_half_angle

namespace AdversarialBco.Bit.Aux_gsm_cos_pi_succ


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_cos_pi_succ (m : ℕ) :
    Real.cos (Real.pi / 2 ^ (m + 1)) = Real.sqrt ((1 + Real.cos (Real.pi / 2 ^ m)) / 2) := by
  have h : Real.pi / 2 ^ (m + 1) = Real.pi / 2 ^ m / 2 := by rw [pow_succ, div_div]
  have h0 : 0 < Real.pi / 2 ^ m := by positivity
  have h1 : Real.pi / 2 ^ m ≤ Real.pi := div_le_self Real.pi_pos.le (one_le_pow₀ (by norm_num))
  rw [h, Real.cos_half (by linarith) h1]

end AdversarialBco.Bit.Aux_gsm_cos_pi_succ

namespace AdversarialBco.Bit.Aux_gsm_chainq_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem chq_sqrt2_gt : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem chq_sqrt2_lt : Real.sqrt 2 < (141422 / 100000 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem chq_angle_le (j : ℕ) (hj : 2 ≤ j) : Real.pi / 2 ^ j ≤ Real.pi / 4 := by
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
  calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj

theorem chq_cos_ge (j : ℕ) (hj : 2 ≤ j) : Real.sqrt 2 / 2 ≤ Real.cos (Real.pi / 2 ^ j) := by
  rw [← Real.cos_pi_div_four]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (chq_angle_le j hj)

theorem chq_sin_le (j : ℕ) (hj : 2 ≤ j) : Real.sin (Real.pi / 2 ^ j) ≤ Real.sqrt 2 / 2 := by
  rw [← Real.sin_pi_div_four]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have : 0 ≤ Real.pi / 2 ^ j := by positivity
    linarith [Real.pi_pos]
  · linarith [Real.pi_pos]
  · exact chq_angle_le j hj

theorem chq_sin_nonneg' (j : ℕ) : 0 ≤ Real.sin (Real.pi / 2 ^ j) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
  apply div_le_self Real.pi_pos.le
  exact one_le_pow₀ (by norm_num)

set_option maxHeartbeats 1000000 in
theorem _root_.AdversarialBco.Bit.gsm_chainq_err (p k : ℕ) (hp : 20 ≤ p) :
    0 ≤ Real.cos (Real.pi / 2 ^ (k + 1)) - ((AdversarialBco.Bit.gsm_chainq p k).1 : ℝ) / 2 ^ p ∧
      Real.cos (Real.pi / 2 ^ (k + 1)) - ((AdversarialBco.Bit.gsm_chainq p k).1 : ℝ) / 2 ^ p ≤ 1547 / 1000 / 2 ^ p ∧
      |Real.sin (Real.pi / 2 ^ (k + 1)) - ((AdversarialBco.Bit.gsm_chainq p k).2 : ℝ) / 2 ^ p| ≤ 897 / 100 / 2 ^ p ∧
      (1 ≤ k → 7 / 10 * 2 ^ p ≤ ((AdversarialBco.Bit.gsm_chainq p k).1 : ℝ)) := by
  have hP20 : (2 : ℝ) ^ 20 ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  have hP0 : (0 : ℝ) < 2 ^ p := by positivity
  have hhalf : ((2 ^ (p - 1) : ℕ) : ℝ) = 2 ^ p / 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    conv_rhs => rw [show p = (p - 1) + 1 by omega, pow_succ]
    field_simp
  induction k with
  | zero =>
    simp only [AdversarialBco.Bit.gsm_chainq, zero_add, pow_one, Nat.cast_zero, zero_div, sub_zero, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, div_self hP0.ne', sub_self, abs_zero]
    exact ⟨le_refl _, by positivity, by positivity, by omega⟩
  | succ k ih =>
    obtain ⟨hγ0, hγ1, hσ, -⟩ := ih
    -- the previous pair and the new one
    set C := (AdversarialBco.Bit.gsm_chainq p k).1 with hC
    set S := (AdversarialBco.Bit.gsm_chainq p k).2 with hS
    set N := 2 ^ (p - 1) * (2 ^ p + C) with hN
    set C' := Nat.sqrt N with hC'
    have hstep : AdversarialBco.Bit.gsm_chainq p (k + 1) = (C', S * 2 ^ (p - 1) / C') := rfl
    rw [hstep]
    simp only
    set P : ℝ := 2 ^ p with hP
    set c := Real.cos (Real.pi / 2 ^ (k + 1)) with hc
    set s := Real.sin (Real.pi / 2 ^ (k + 1)) with hs
    set c' := Real.cos (Real.pi / 2 ^ (k + 1 + 1)) with hc'
    set s' := Real.sin (Real.pi / 2 ^ (k + 1 + 1)) with hs'
    -- the cosine step
    have hcc : c' = Real.sqrt ((1 + c) / 2) := AdversarialBco.Bit.gsm_cos_pi_succ (k + 1)
    have hNr : (N : ℝ) = P ^ 2 * ((1 + (C : ℝ) / P) / 2) := by
      rw [hN, Nat.cast_mul, hhalf, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      ring
    have hy0 : 1 / 2 ≤ (1 + (C : ℝ) / P) / 2 := by
      have : 0 ≤ (C : ℝ) / P := by positivity
      linarith
    have hsqN : Real.sqrt N = P * Real.sqrt ((1 + (C : ℝ) / P) / 2) := by
      rw [hNr, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP0.le]
    have hC'le : (C' : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    have hC'lt : Real.sqrt N < C' + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    have hc1 : -1 ≤ c := Real.neg_one_le_cos _
    have hyx : (1 + (C : ℝ) / P) / 2 ≤ (1 + c) / 2 := by linarith
    have hsy_le : Real.sqrt ((1 + (C : ℝ) / P) / 2) ≤ Real.sqrt ((1 + c) / 2) := Real.sqrt_le_sqrt hyx
    -- γ' ≥ 0
    have hg0 : 0 ≤ c' - (C' : ℝ) / P := by
      rw [hcc, sub_nonneg, div_le_iff₀ hP0]
      calc (C' : ℝ) ≤ Real.sqrt N := hC'le
        _ = P * Real.sqrt ((1 + (C : ℝ) / P) / 2) := hsqN
        _ ≤ P * Real.sqrt ((1 + c) / 2) := mul_le_mul_of_nonneg_left hsy_le hP0.le
        _ = Real.sqrt ((1 + c) / 2) * P := mul_comm _ _
    -- √x - √y ≤ γ/(2√2)
    set u := Real.sqrt ((1 + c) / 2) - Real.sqrt ((1 + (C : ℝ) / P) / 2) with hu
    have hu0 : 0 ≤ u := sub_nonneg.mpr hsy_le
    have hsum : Real.sqrt 2 ≤ Real.sqrt ((1 + c) / 2) + Real.sqrt ((1 + (C : ℝ) / P) / 2) := by
      have h12 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
        rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]
      have h1 : Real.sqrt 2 / 2 ≤ Real.sqrt ((1 + (C : ℝ) / P) / 2) := by
        rw [← h12]; exact Real.sqrt_le_sqrt hy0
      linarith
    have hprod : u * (Real.sqrt ((1 + c) / 2) + Real.sqrt ((1 + (C : ℝ) / P) / 2)) =
        (c - (C : ℝ) / P) / 2 := by
      rw [hu]
      have ha : Real.sqrt ((1 + c) / 2) ^ 2 = (1 + c) / 2 := Real.sq_sqrt (by linarith)
      have hb : Real.sqrt ((1 + (C : ℝ) / P) / 2) ^ 2 = (1 + (C : ℝ) / P) / 2 := Real.sq_sqrt (by linarith)
      nlinarith [ha, hb]
    have hur : u * Real.sqrt 2 ≤ (c - (C : ℝ) / P) / 2 := by
      rw [← hprod]; exact mul_le_mul_of_nonneg_left hsum hu0
    -- γ' < u + 1/P
    have hg_lt : c' - (C' : ℝ) / P < u + 1 / P := by
      have h1 : (Real.sqrt N - 1) / P < (C' : ℝ) / P := div_lt_div_of_pos_right (by linarith) hP0
      have h2 : (Real.sqrt N - 1) / P = Real.sqrt ((1 + (C : ℝ) / P) / 2) - 1 / P := by
        rw [hsqN]; field_simp
      rw [hcc, hu]; linarith
    -- the scaled quantities
    have hPγ : P * (c - (C : ℝ) / P) ≤ 1547 / 1000 := by
      have := mul_le_mul_of_nonneg_left hγ1 hP0.le
      rwa [mul_div_cancel₀ _ hP0.ne'] at this
    have hr := chq_sqrt2_gt
    have hPu : P * u ≤ 54696 / 100000 := by
      have h1 : P * u * Real.sqrt 2 ≤ 1547 / 2000 := by nlinarith [hur, hP0]
      have h2 : P * u * (14142 / 10000) ≤ P * u * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hr.le (mul_nonneg hP0.le hu0)
      nlinarith
    have hg1 : c' - (C' : ℝ) / P ≤ 1547 / 1000 / P := by
      rw [le_div_iff₀ hP0]
      have := mul_lt_mul_of_pos_left hg_lt hP0
      rw [mul_add, mul_one_div_cancel hP0.ne'] at this
      calc (c' - (C' : ℝ) / P) * P = P * (c' - (C' : ℝ) / P) := mul_comm _ _
        _ ≤ 1547 / 1000 := by linarith
    -- C' ≥ 0.7 P
    have hc'ge : Real.sqrt 2 / 2 ≤ c' := chq_cos_ge (k + 1 + 1) (by omega)
    have hC'big : 7 / 10 * P ≤ (C' : ℝ) := by
      have h1 : P * (c' - (C' : ℝ) / P) ≤ 1547 / 1000 := by
        have := mul_le_mul_of_nonneg_left hg1 hP0.le
        rwa [mul_div_cancel₀ _ hP0.ne'] at this
      have h2 : P * (c' - (C' : ℝ) / P) = P * c' - C' := by field_simp
      have h3 : (2 : ℝ) ^ 20 ≤ P := hP20
      have h4 : P * (7071 / 10000) ≤ P * c' :=
        mul_le_mul_of_nonneg_left (by linarith [chq_sqrt2_gt]) hP0.le
      have h5 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
      linarith
    refine ⟨hg0, hg1, ?_, fun _ => hC'big⟩
    -- the sine step
    have hss : s' = s / (2 * c') := (AdversarialBco.Bit.gsm_half_angle (k + 1) (by omega)).2
    have hC'pos : 0 < (C' : ℝ) := by
      have : (0 : ℝ) < 7 / 10 * P := by positivity
      exact lt_of_lt_of_le this hC'big
    have hC'posn : 0 < C' := by exact_mod_cast hC'pos
    generalize hQ : S * 2 ^ (p - 1) = Q
    have hQr : (Q : ℝ) = S * (P / 2) := by rw [← hQ, Nat.cast_mul, hhalf]
    have hdiv_le : ((Q / C' : ℕ) : ℝ) ≤ (Q : ℝ) / C' := Nat.cast_div_le
    have hdiv_gt : (Q : ℝ) / C' < ((Q / C' : ℕ) : ℝ) + 1 := by
      have h := Nat.lt_div_mul_add (a := Q) hC'posn
      have h' : (Q : ℝ) < ((Q / C' : ℕ) : ℝ) * C' + C' := by exact_mod_cast h
      rw [div_lt_iff₀ hC'pos]; linarith
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (S : ℝ) / (2 * C') := ⟨_, rfl⟩
    have hQT : (Q : ℝ) / C' / P = T := by
      rw [hQr, hT]; field_simp
    have hlow : T - 1 / P < ((Q / C' : ℕ) : ℝ) / P := by
      have := div_lt_div_of_pos_right hdiv_gt hP0
      rw [hQT, add_div] at this; linarith
    have hhigh : ((Q / C' : ℕ) : ℝ) / P ≤ T := by
      have := div_le_div_of_nonneg_right hdiv_le hP0.le
      rwa [hQT] at this
    obtain ⟨ct, hct⟩ : ∃ ct : ℝ, ct = (C' : ℝ) / P := ⟨_, rfl⟩
    have hct7 : 7 / 10 ≤ ct := by rw [hct, le_div_iff₀ hP0]; linarith
    have hctpos : 0 < ct := by linarith
    have hc'pos : 0 < c' := by
      have : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
      linarith
    obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = s - (S : ℝ) / P := ⟨_, rfl⟩
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ℝ, γ' = c' - ct := ⟨_, rfl⟩
    have hTct : T = ((S : ℝ) / P) / (2 * ct) := by
      rw [hT, hct]; field_simp
    have hident : s' - T = σ / (2 * ct) - s' * γ' / ct := by
      have hct0 := hctpos.ne'
      have hc'0 := hc'pos.ne'
      rw [hTct, hσdef, hγ', hss]
      field_simp
      ring
    have hs'0 : 0 ≤ s' := chq_sin_nonneg' _
    have hs'le : s' ≤ Real.sqrt 2 / 2 := chq_sin_le (k + 1 + 1) (by omega)
    have hr2 := chq_sqrt2_lt
    have hγ'0 : 0 ≤ γ' := by rw [hγ', hct]; exact hg0
    have hγ'1 : P * γ' ≤ 1547 / 1000 := by
      have := mul_le_mul_of_nonneg_left hg1 hP0.le
      rw [mul_div_cancel₀ _ hP0.ne'] at this
      rw [hγ', hct]; exact this
    have hPσ : P * |σ| ≤ 897 / 100 := by
      have := mul_le_mul_of_nonneg_left hσ hP0.le
      rw [mul_div_cancel₀ _ hP0.ne'] at this
      rw [hσdef]; exact this
    have hA : P * |σ / (2 * ct)| ≤ 897 / 140 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * ct), ← mul_div_assoc,
        div_le_iff₀ (by linarith : (0 : ℝ) < 2 * ct)]
      have h1 : 897 / 140 * (14 / 10 : ℝ) ≤ 897 / 140 * (2 * ct) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      have h2 : 897 / 140 * (14 / 10 : ℝ) = 897 / 100 := by norm_num
      linarith
    have hB : P * |s' * γ' / ct| ≤ 70711 / 100000 * (1547 / 1000) / (7 / 10) := by
      rw [abs_of_nonneg (div_nonneg (mul_nonneg hs'0 hγ'0) hctpos.le), ← mul_div_assoc,
        div_le_iff₀ hctpos]
      have h1 : s' ≤ 70711 / 100000 := by linarith
      have h2 : P * (s' * γ') ≤ 70711 / 100000 * (1547 / 1000) := by
        calc P * (s' * γ') = s' * (P * γ') := by ring
          _ ≤ 70711 / 100000 * (1547 / 1000) :=
            mul_le_mul h1 hγ'1 (mul_nonneg hP0.le hγ'0) (by norm_num)
      have h3 : 70711 / 100000 * (1547 / 1000) / (7 / 10) * (7 / 10) ≤
          70711 / 100000 * (1547 / 1000) / (7 / 10) * ct :=
        mul_le_mul_of_nonneg_left hct7 (by norm_num)
      have h4 : 70711 / 100000 * (1547 / 1000) / (7 / 10) * (7 / 10) =
          (70711 / 100000 * (1547 / 1000) : ℝ) := by norm_num
      linarith
    have hfin : s' - ((Q / C' : ℕ) : ℝ) / P = (s' - T) + (T - ((Q / C' : ℕ) : ℝ) / P) := by ring
    have hlast : P * |s' - ((Q / C' : ℕ) : ℝ) / P| ≤ 897 / 100 := by
      rw [hfin]
      have e1 : |s' - T| ≤ |σ / (2 * ct)| + |s' * γ' / ct| := by rw [hident]; exact abs_sub _ _
      have e2 : |T - ((Q / C' : ℕ) : ℝ) / P| ≤ 1 / P := by
        rw [abs_le]; constructor <;> linarith
      have e3 := abs_add_le (s' - T) (T - ((Q / C' : ℕ) : ℝ) / P)
      have e4 : P * (1 / P) = 1 := mul_one_div_cancel hP0.ne'
      calc P * |s' - T + (T - ((Q / C' : ℕ) : ℝ) / P)|
          ≤ P * (|σ / (2 * ct)| + |s' * γ' / ct| + 1 / P) :=
            mul_le_mul_of_nonneg_left (by linarith) hP0.le
        _ = P * |σ / (2 * ct)| + P * |s' * γ' / ct| + 1 := by rw [mul_add, mul_add, e4]
        _ ≤ 897 / 140 + 70711 / 100000 * (1547 / 1000) / (7 / 10) + 1 := by linarith
        _ ≤ 897 / 100 := by norm_num
    rw [le_div_iff₀ hP0, mul_comm]
    exact hlast

end AdversarialBco.Bit.Aux_gsm_chainq_err

namespace AdversarialBco.Bit.Aux_gsm_angle_digits


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_angle_digits (B J : ℕ) (hJ : J < 2 ^ B) :
    2 * Real.pi * J / 2 ^ B = ∑ k ∈ Finset.range B, if J.testBit (B - 1 - k) then Real.pi / 2 ^ k else 0 := by
  induction' B with B ih generalizing J
  · -- B = 0: then J < 2^0 = 1, so J = 0
    have hJ0 : J = 0 := by omega
    subst hJ0
    simp
  · -- inductive step: J < 2^(B+1)
    set q := J / 2 ^ B with hq_def
    set r := J % 2 ^ B with hr_def
    have hr_lt : r < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hq_lt_two : q < 2 := by
      rw [hq_def]
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hJ)
    have hJ_eq : J = q * 2 ^ B + r := by
      rw [hq_def, hr_def, mul_comm]
      exact (Nat.div_add_mod J (2 ^ B)).symm
    -- relate testBit B to q: (J.testBit B).toNat = q
    have h_testBit_q : (J.testBit B).toNat = q := by
      rw [hJ_eq, mul_comm q (2 ^ B)]
      rw [Nat.testBit_two_pow_mul_add q hr_lt B]
      simp
      rcases Nat.eq_zero_or_pos q with (hq0 | hqpos)
      · simp [hq0]
      · have hq1 : q = 1 := by omega
        simp [hq1]
    -- Now compute LHS and RHS
    have hLHS : 2 * Real.pi * (J : ℝ) / ((2 : ℝ) ^ (B + 1)) = Real.pi * (q : ℝ) + Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by
      rw [hJ_eq]
      push_cast
      field_simp
      ring
    have hRHS : (∑ k ∈ Finset.range (B + 1), if J.testBit (B - k) then Real.pi / ((2 : ℝ) ^ k) else 0) =
        Real.pi * (q : ℝ) + Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by
      -- Use sum_range_succ' to split off the k=0 term
      rw [Finset.sum_range_succ']
      have hsub0 : (B : ℕ) - 0 = B := by omega
      simp [hsub0]
      -- goal: (∑ k ∈ range B, (if J.testBit (B - (k+1)) then π / 2^(k+1) else 0)) +
      --       (if J.testBit B then π else 0) = π*q + π*r/2^B
      -- handle the second term by cases on J.testBit B
      by_cases hbitB : J.testBit B
      · -- J.testBit B = true, so q = 1
        have hq1 : q = 1 := by
          have : (J.testBit B).toNat = 1 := by simp [hbitB]
          rw [h_testBit_q] at this
          exact this
        simp [hbitB, hq1]
        -- goal: (∑ ...) + Real.pi = Real.pi + Real.pi * ↑r / 2 ^ B
        -- So we need to show S = π*r/2^B
        have hsum : (∑ x ∈ Finset.range B, if J.testBit (B - (x + 1)) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0) =
            Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by
          calc
            (∑ x ∈ Finset.range B, if J.testBit (B - (x + 1)) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0)
                = (∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hx_lt_B : x < B := Finset.mem_range.1 hx
              have : B - (x + 1) = B - 1 - x := by omega
              rw [this]
            _ = (∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then (Real.pi / ((2 : ℝ) ^ x)) / 2 else 0) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              by_cases hbit : J.testBit (B - 1 - x)
              · simp [hbit, div_div, pow_succ]
              · simp [hbit]
            _ = ((∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ x) else 0)) / 2 := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun x hx => ?_
              by_cases hbit : J.testBit (B - 1 - x)
              · simp [hbit]
              · simp [hbit]
            _ = ((∑ x ∈ Finset.range B, if r.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ x) else 0)) / 2 := by
              refine congrArg (· / 2) (Finset.sum_congr rfl fun x hx => ?_)
              have hx_lt_B : x < B := Finset.mem_range.1 hx
              have h_testBit_eq : J.testBit (B - 1 - x) = r.testBit (B - 1 - x) := by
                rw [hr_def, Nat.testBit_mod_two_pow]
                have h_lt : B - 1 - x < B := by omega
                simp [h_lt]
              rw [h_testBit_eq]
            _ = (2 * Real.pi * (r : ℝ) / ((2 : ℝ) ^ B)) / 2 := by
              have ih_r := ih r hr_lt
              rw [ih_r.symm]
            _ = Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by ring
        rw [hsum]
        ring
      · -- J.testBit B = false, so q = 0
        have hq0 : q = 0 := by
          have : (J.testBit B).toNat = 0 := by simp [hbitB]
          rw [h_testBit_q] at this
          exact this
        simp [hbitB, hq0]
        -- goal: S = π*r/2^B
        have hsum : (∑ x ∈ Finset.range B, if J.testBit (B - (x + 1)) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0) =
            Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by
          calc
            (∑ x ∈ Finset.range B, if J.testBit (B - (x + 1)) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0)
                = (∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ (x + 1)) else 0) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hx_lt_B : x < B := Finset.mem_range.1 hx
              have : B - (x + 1) = B - 1 - x := by omega
              rw [this]
            _ = (∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then (Real.pi / ((2 : ℝ) ^ x)) / 2 else 0) := by
              refine Finset.sum_congr rfl fun x hx => ?_
              by_cases hbit : J.testBit (B - 1 - x)
              · simp [hbit, div_div, pow_succ]
              · simp [hbit]
            _ = ((∑ x ∈ Finset.range B, if J.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ x) else 0)) / 2 := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun x hx => ?_
              by_cases hbit : J.testBit (B - 1 - x)
              · simp [hbit]
              · simp [hbit]
            _ = ((∑ x ∈ Finset.range B, if r.testBit (B - 1 - x) then Real.pi / ((2 : ℝ) ^ x) else 0)) / 2 := by
              refine congrArg (· / 2) (Finset.sum_congr rfl fun x hx => ?_)
              have hx_lt_B : x < B := Finset.mem_range.1 hx
              have h_testBit_eq : J.testBit (B - 1 - x) = r.testBit (B - 1 - x) := by
                rw [hr_def, Nat.testBit_mod_two_pow]
                have h_lt : B - 1 - x < B := by omega
                simp [h_lt]
              rw [h_testBit_eq]
            _ = (2 * Real.pi * (r : ℝ) / ((2 : ℝ) ^ B)) / 2 := by
              have ih_r := ih r hr_lt
              rw [ih_r.symm]
            _ = Real.pi * (r : ℝ) / ((2 : ℝ) ^ B) := by ring
        rw [hsum]
    -- Combine hLHS and hRHS
    have h_eq : 2 * Real.pi * (J : ℝ) / ((2 : ℝ) ^ (B + 1)) =
        (∑ k ∈ Finset.range (B + 1), if J.testBit (B - k) then Real.pi / ((2 : ℝ) ^ k) else 0) := by
      rw [hLHS, hRHS]
    -- Simplify the goal to match h_eq
    simpa using h_eq

end AdversarialBco.Bit.Aux_gsm_angle_digits

namespace AdversarialBco.Bit.Aux_gsm_cmulq_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

lemma int_div_eq (x : ℤ) (d : ℕ) (hd : d ≠ 0) : (x : ℂ) / (d : ℂ) = ((x / (d : ℤ) : ℤ) : ℂ) + ((x % (d : ℤ) : ℤ) : ℂ) / (d : ℂ) := by
  have h := Int.ediv_mul_add_emod x (d : ℤ)
  have hcast : (x : ℂ) = ((x / (d : ℤ) : ℤ) : ℂ) * ((d : ℤ) : ℂ) + ((x % (d : ℤ) : ℤ) : ℂ) := by
    simpa using congrArg (fun t : ℤ => (t : ℂ)) h.symm
  have hd' : (d : ℂ) ≠ 0 := by
    intro hzero
    apply hd
    exact_mod_cast hzero
  calc
    (x : ℂ) / (d : ℂ) = (((x / (d : ℤ) : ℤ) : ℂ) * ((d : ℤ) : ℂ) + ((x % (d : ℤ) : ℤ) : ℂ)) / (d : ℂ) := by rw [hcast]
    _ = ((x / (d : ℤ) : ℤ) : ℂ) * ((d : ℤ) : ℂ) / (d : ℂ) + ((x % (d : ℤ) : ℤ) : ℂ) / (d : ℂ) := by rw [add_div]
    _ = ((x / (d : ℤ) : ℤ) : ℂ) * (((d : ℤ) : ℂ) / (d : ℂ)) + ((x % (d : ℤ) : ℤ) : ℂ) / (d : ℂ) := by rw [mul_div_assoc]
    _ = ((x / (d : ℤ) : ℤ) : ℂ) * 1 + ((x % (d : ℤ) : ℤ) : ℂ) / (d : ℂ) := by
      have : ((d : ℤ) : ℂ) / (d : ℂ) = 1 := by
        field_simp [hd']
        simp
      rw [this]
    _ = ((x / (d : ℤ) : ℤ) : ℂ) + ((x % (d : ℤ) : ℤ) : ℂ) / (d : ℂ) := by ring

theorem _root_.AdversarialBco.Bit.gsm_cmulq_err (p : ℕ) (z f : ℤ × ℤ) (ζ φ : ℂ) (hζ : ‖ζ‖ = 1) (hφ : ‖φ‖ = 1) (D ε : ℝ)
    (hz : ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / 2 ^ p - ζ‖ ≤ D)
    (hf : ‖((f.1 : ℂ) + (f.2 : ℂ) * Complex.I) / 2 ^ p - φ‖ ≤ ε) :
    ‖(((AdversarialBco.Bit.gsm_cmulq p z f).1 : ℂ) + ((AdversarialBco.Bit.gsm_cmulq p z f).2 : ℂ) * Complex.I) / 2 ^ p - ζ * φ‖ ≤
      D * (1 + ε) + ε + Real.sqrt 2 / 2 ^ p := by
  -- Extract nonnegativity of D and ε from the norm bounds
  have hD : 0 ≤ D := by
    have := norm_nonneg (((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / 2 ^ p - ζ)
    linarith
  have hε : 0 ≤ ε := by
    have := norm_nonneg (((f.1 : ℂ) + (f.2 : ℂ) * Complex.I) / 2 ^ p - φ)
    linarith
  -- Define z' and f' for readability
  set z' := ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / ((2 : ℕ) ^ p : ℂ) with hz'
  set f' := ((f.1 : ℂ) + (f.2 : ℂ) * Complex.I) / ((2 : ℕ) ^ p : ℂ) with hf'
  have hz' : ‖z' - ζ‖ ≤ D := hz
  have hf' : ‖f' - φ‖ ≤ ε := hf
  -- The exact product z' * f'
  set prod_exact := z' * f' with hprod_exact
  -- The rounded product
  set prod_round := (((AdversarialBco.Bit.gsm_cmulq p z f).1 : ℂ) + ((AdversarialBco.Bit.gsm_cmulq p z f).2 : ℂ) * Complex.I) / ((2 : ℕ) ^ p : ℂ) with hprod_round
  -- Bound prod_exact - ζ * φ
  have h_main : ‖prod_exact - ζ * φ‖ ≤ D * (1 + ε) + ε := by
    have hff : ‖f'‖ ≤ ε + 1 := by
      calc
        ‖f'‖ = ‖(f' - φ) + φ‖ := by simp
        _ ≤ ‖f' - φ‖ + ‖φ‖ := norm_add_le _ _
        _ ≤ ε + 1 := by simp [hφ, hf']
    have hprod_error : ‖(z' - ζ) * f' + ζ * (f' - φ)‖ ≤ ‖z' - ζ‖ * ‖f'‖ + ‖ζ‖ * ‖f' - φ‖ := by
      calc
        ‖(z' - ζ) * f' + ζ * (f' - φ)‖ ≤ ‖(z' - ζ) * f'‖ + ‖ζ * (f' - φ)‖ := norm_add_le _ _
        _ = ‖z' - ζ‖ * ‖f'‖ + ‖ζ‖ * ‖f' - φ‖ := by rw [norm_mul, norm_mul]
    calc
      ‖prod_exact - ζ * φ‖ = ‖(z' * f') - ζ * φ‖ := rfl
      _ = ‖(z' - ζ) * f' + ζ * (f' - φ)‖ := by ring_nf
      _ ≤ ‖z' - ζ‖ * ‖f'‖ + ‖ζ‖ * ‖f' - φ‖ := hprod_error
      _ ≤ D * ‖f'‖ + 1 * ε := by
        have h1 : ‖z' - ζ‖ * ‖f'‖ ≤ D * ‖f'‖ := by
          have hpos : 0 ≤ ‖f'‖ := norm_nonneg _
          nlinarith
        have h2 : ‖ζ‖ * ‖f' - φ‖ ≤ 1 * ε := by
          rw [hζ]
          have hpos : 0 ≤ ‖f' - φ‖ := norm_nonneg _
          nlinarith
        nlinarith
      _ = D * ‖f'‖ + ε := by ring
      _ ≤ D * (ε + 1) + ε := by nlinarith
      _ = D * (1 + ε) + ε := by ring
  -- Bound the rounding error: prod_round - prod_exact
  have h_round : ‖prod_round - prod_exact‖ ≤ Real.sqrt 2 / ((2 : ℕ) ^ p : ℝ) := by
    set d_nat := (2 : ℕ) ^ p with hd_nat
    have hd_pos_nat : 0 < d_nat := by
      rw [hd_nat]
      apply pow_pos (by norm_num) p
    have hd_ne_zero : d_nat ≠ 0 := by linarith
    set a := z.1 * f.1 - z.2 * f.2 with ha
    set b := z.1 * f.2 + z.2 * f.1 with hb
    -- Express prod_exact and prod_round in terms of a, b
    have hprod_exact_eq : prod_exact = ((a : ℂ) + (b : ℂ) * Complex.I) / ((d_nat : ℂ) * (d_nat : ℂ)) := by
      dsimp [prod_exact, z', f', a, b, d_nat]
      push_cast
      field_simp [show (2 : ℂ) ^ p ≠ 0 from by
        apply pow_ne_zero
        norm_num]
      ring_nf
      simp [Complex.I_sq]
      ring
    have hprod_round_eq : prod_round = (((a / (d_nat : ℤ) : ℤ) : ℂ) + (((b / (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)) / (d_nat : ℂ) := by
      dsimp [prod_round, AdversarialBco.Bit.gsm_cmulq, a, b, d_nat]
      push_cast
      field_simp [show (2 : ℂ) ^ p ≠ 0 from by
        apply pow_ne_zero
        norm_num]
    -- Compute the difference
    have h_diff : prod_exact - prod_round = (((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)) / ((d_nat : ℂ) * (d_nat : ℂ)) := by
      rw [hprod_exact_eq, hprod_round_eq]
      have ha_eq := int_div_eq a d_nat hd_ne_zero
      have hb_eq := int_div_eq b d_nat hd_ne_zero
      calc
        ((a : ℂ) + (b : ℂ) * Complex.I) / ((d_nat : ℂ) * (d_nat : ℂ)) - (((a / (d_nat : ℤ) : ℤ) : ℂ) + (((b / (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)) / (d_nat : ℂ)
            = (((a : ℂ) + (b : ℂ) * Complex.I) / (d_nat : ℂ) - (((a / (d_nat : ℤ) : ℤ) : ℂ) + (((b / (d_nat : ℤ) : ℤ) : ℂ) * Complex.I))) / (d_nat : ℂ) := by ring
        _ = (((a : ℂ) / (d_nat : ℂ) - ((a / (d_nat : ℤ) : ℤ) : ℂ)) + ((b : ℂ) / (d_nat : ℂ) - ((b / (d_nat : ℤ) : ℤ) : ℂ)) * Complex.I) / (d_nat : ℂ) := by ring
        _ = ((((a % (d_nat : ℤ) : ℤ) : ℂ) / (d_nat : ℂ)) + (((b % (d_nat : ℤ) : ℤ) : ℂ) / (d_nat : ℂ)) * Complex.I) / (d_nat : ℂ) := by rw [ha_eq, hb_eq]; ring
        _ = (((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)) / ((d_nat : ℂ) * (d_nat : ℂ)) := by ring
    -- Use norm_sub_rev to flip the subtraction
    rw [norm_sub_rev, h_diff]
    -- Now we need: ‖((a%d) + (b%d)*I) / (d_nat^2)‖ ≤ Real.sqrt 2 / d_nat
    rw [norm_div]
    -- Goal: ‖...‖ / ‖(d_nat : ℂ) * (d_nat : ℂ)‖ ≤ Real.sqrt 2 / (d_nat : ℝ)
    have h_denom : ‖(d_nat : ℂ) * (d_nat : ℂ)‖ = (d_nat : ℝ) * (d_nat : ℝ) := by
      simp
    rw [h_denom]
    -- Goal: ‖...‖ / ((d_nat : ℝ) * (d_nat : ℝ)) ≤ Real.sqrt 2 / (d_nat : ℝ)
    have h_d_pos : 0 < (d_nat : ℝ) := by exact_mod_cast hd_pos_nat
    have h_num_bound : ‖((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 * ((d_nat : ℝ) - 1) := by
      have ha_rem_nonneg : 0 ≤ (a % (d_nat : ℤ) : ℤ) :=
        Int.emod_nonneg a (by exact_mod_cast hd_ne_zero : (d_nat : ℤ) ≠ 0)
      have ha_rem_lt : (a % (d_nat : ℤ) : ℤ) < (d_nat : ℤ) :=
        Int.emod_lt_of_pos a (by exact_mod_cast hd_pos_nat : (0 : ℤ) < d_nat)
      have hb_rem_nonneg : 0 ≤ (b % (d_nat : ℤ) : ℤ) :=
        Int.emod_nonneg b (by exact_mod_cast hd_ne_zero : (d_nat : ℤ) ≠ 0)
      have hb_rem_lt : (b % (d_nat : ℤ) : ℤ) < (d_nat : ℤ) :=
        Int.emod_lt_of_pos b (by exact_mod_cast hd_pos_nat : (0 : ℤ) < d_nat)
      -- Convert to ℝ bounds
      have ha_rem_le : ((a % (d_nat : ℤ) : ℤ) : ℝ) ≤ (d_nat : ℝ) - 1 := by
        have h : (a % (d_nat : ℤ) : ℤ) ≤ (d_nat : ℤ) - 1 := by omega
        have h_cast : ((a % (d_nat : ℤ) : ℤ) : ℝ) ≤ ((d_nat : ℤ) - 1 : ℝ) := by exact_mod_cast h
        simpa using h_cast
      have hb_rem_le : ((b % (d_nat : ℤ) : ℤ) : ℝ) ≤ (d_nat : ℝ) - 1 := by
        have h : (b % (d_nat : ℤ) : ℤ) ≤ (d_nat : ℤ) - 1 := by omega
        have h_cast : ((b % (d_nat : ℤ) : ℤ) : ℝ) ≤ ((d_nat : ℤ) - 1 : ℝ) := by exact_mod_cast h
        simpa using h_cast
      have ha_rem_nonneg' : 0 ≤ ((a % (d_nat : ℤ) : ℤ) : ℝ) := by
        have h_cast : ((0 : ℤ) : ℝ) ≤ ((a % (d_nat : ℤ) : ℤ) : ℝ) := by exact_mod_cast ha_rem_nonneg
        simpa using h_cast
      have hb_rem_nonneg' : 0 ≤ ((b % (d_nat : ℤ) : ℤ) : ℝ) := by
        have h_cast : ((0 : ℤ) : ℝ) ≤ ((b % (d_nat : ℤ) : ℤ) : ℝ) := by exact_mod_cast hb_rem_nonneg
        simpa using h_cast
      set x := ((a % (d_nat : ℤ) : ℤ) : ℝ) with hx
      set y := ((b % (d_nat : ℤ) : ℤ) : ℝ) with hy
      have h_norm_sq : Complex.normSq (((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)) = x^2 + y^2 := by
        dsimp [x, y]
        simp [Complex.normSq_add, Complex.normSq_I, mul_comm]
        ring
      rw [Complex.norm_def, h_norm_sq]
      -- Goal: √(x^2 + y^2) ≤ √2 * ((d_nat : ℝ) - 1)
      have h_sq_bound : x^2 + y^2 ≤ 2 * ((d_nat : ℝ) - 1)^2 := by
        nlinarith
      have h_nonneg_d : 0 ≤ (d_nat : ℝ) - 1 := by
        have : 1 ≤ (d_nat : ℝ) := by
          have h := Nat.one_le_two_pow (n := p)
          exact_mod_cast h
        nlinarith
      calc
        Real.sqrt (x^2 + y^2) ≤ Real.sqrt (2 * ((d_nat : ℝ) - 1)^2) := Real.sqrt_le_sqrt h_sq_bound
        _ = Real.sqrt 2 * Real.sqrt (((d_nat : ℝ) - 1)^2) := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
        _ = Real.sqrt 2 * |(d_nat : ℝ) - 1| := by rw [Real.sqrt_sq_eq_abs]
        _ = Real.sqrt 2 * ((d_nat : ℝ) - 1) := by rw [abs_of_nonneg h_nonneg_d]
    -- Now use the bound to finish
    have h_num_le : ‖((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)‖ ≤ Real.sqrt 2 * (d_nat : ℝ) := by
      apply le_trans h_num_bound
      have h_nonneg_sqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      gcongr
      nlinarith
    -- Need: num / (d_nat^2) ≤ sqrt(2) / 2^p
    -- We prove this by clearing denominators
    have h_mul : ‖((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)‖ * (d_nat : ℝ) ≤
        (d_nat : ℝ)^2 * Real.sqrt 2 := by
      calc
        ‖((a % (d_nat : ℤ) : ℤ) : ℂ) + (((b % (d_nat : ℤ) : ℤ) : ℂ) * Complex.I)‖ * (d_nat : ℝ) ≤
            (Real.sqrt 2 * (d_nat : ℝ)) * (d_nat : ℝ) :=
          mul_le_mul_of_nonneg_right h_num_le (by positivity)
        _ = (d_nat : ℝ)^2 * Real.sqrt 2 := by ring
    -- Now convert h_mul to the division inequality
    field_simp [h_d_pos.ne.symm]
    simpa [hd_nat] using h_mul
  -- Combine by triangle inequality
  have h_triangle : ‖prod_round - ζ * φ‖ ≤ ‖prod_round - prod_exact‖ + ‖prod_exact - ζ * φ‖ := by
    calc
      ‖prod_round - ζ * φ‖ = ‖(prod_round - prod_exact) + (prod_exact - ζ * φ)‖ := by ring_nf
      _ ≤ ‖prod_round - prod_exact‖ + ‖prod_exact - ζ * φ‖ := norm_add_le _ _
  calc
    ‖prod_round - ζ * φ‖ ≤ ‖prod_round - prod_exact‖ + ‖prod_exact - ζ * φ‖ := h_triangle
    _ ≤ (Real.sqrt 2 / ((2 : ℕ) ^ p : ℝ)) + (D * (1 + ε) + ε) := by nlinarith
    _ = D * (1 + ε) + ε + Real.sqrt 2 / 2 ^ p := by
      push_cast
      ring

end AdversarialBco.Bit.Aux_gsm_cmulq_err

namespace AdversarialBco.Bit.Aux_gsm_digits_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

open AdversarialBco.Bit

lemma eq_of_testBit_eq_of_lt_two_pow {x y K : ℕ} (hx : x < 2 ^ K) (hy : y < 2 ^ K)
    (hbits : ∀ i < K, Nat.testBit x i = Nat.testBit y i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · exact hbits i hi
  · have hx' : x.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      have h_le : K ≤ i := Nat.le_of_not_lt hi
      have h_pow_le : 2 ^ K ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num : 0 < 2) h_le
      exact Nat.lt_of_lt_of_le hx h_pow_le
    have hy' : y.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      have h_le : K ≤ i := Nat.le_of_not_lt hi
      have h_pow_le : 2 ^ K ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num : 0 < 2) h_le
      exact Nat.lt_of_lt_of_le hy h_pow_le
    rw [hx', hy']

lemma exists_nat_with_bits (K : ℕ) (c : ℕ → Bool) : ∃ n0 : ℕ, n0 < 2 ^ K ∧ ∀ i < K, Nat.testBit n0 i = c i := by
  induction' K with K ih
  · refine ⟨0, by norm_num, λ i hi => ?_⟩
    exact (Nat.not_lt_zero _ hi).elim
  · rcases ih with ⟨n0', hn0'_lt, hn0'_bits⟩
    by_cases hcK : c K
    · refine ⟨2 ^ K + n0', ?_, λ i hi => ?_⟩
      · calc
          2 ^ K + n0' < 2 ^ K + 2 ^ K := Nat.add_lt_add_left hn0'_lt (2 ^ K)
          _ = 2 ^ (K + 1) := by ring
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hi_lt | hi_eq)
        · rw [Nat.testBit_two_pow_add_gt hi_lt n0', hn0'_bits i hi_lt]
        · rw [hi_eq]
          rw [Nat.testBit_two_pow_add_eq n0' K]
          rw [Nat.testBit_eq_false_of_lt hn0'_lt]
          simp [hcK]
    · refine ⟨n0', ?_, λ i hi => ?_⟩
      · calc
          n0' < 2 ^ K := hn0'_lt
          _ < 2 ^ (K + 1) := by
            apply Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self K)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with (hi_lt | hi_eq)
        · exact hn0'_bits i hi_lt
        · rw [hi_eq]
          rw [Nat.testBit_eq_false_of_lt hn0'_lt]
          simp [hcK]

end AdversarialBco.Bit.Aux_gsm_digits_law

namespace AdversarialBco.Bit.Aux_gsm_X_floor


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

theorem _root_.AdversarialBco.Bit.gsm_X_floor (q N : ℕ) (hN : 1 ≤ N) :
    0 ≤ 1 - (2 : ℝ) ^ Nat.log 2 N / N ∧ 1 - (2 : ℝ) ^ Nat.log 2 N / N < 1 / 2 ∧
      (((N - 2 ^ Nat.log 2 N) * 2 ^ q / N : ℕ) : ℝ) ≤ 2 ^ q * (1 - (2 : ℝ) ^ Nat.log 2 N / N) ∧
      2 ^ q * (1 - (2 : ℝ) ^ Nat.log 2 N / N) < (((N - 2 ^ Nat.log 2 N) * 2 ^ q / N : ℕ) : ℝ) + 1 ∧
      Real.log ((N : ℝ) / 2 ^ Nat.log 2 N) = -Real.log (1 - (1 - (2 : ℝ) ^ Nat.log 2 N / N)) := by
  have hNpos : N ≠ 0 := by omega
  have hNpos' : 0 < N := Nat.pos_of_ne_zero hNpos
  have h_two_gt_one : 1 < (2 : ℕ) := by norm_num
  set e := Nat.log 2 N with he
  have hpow_le : (2 : ℕ) ^ e ≤ N := Nat.pow_log_le_self 2 hNpos
  have h_lt : N < (2 : ℕ) ^ (e.succ) := Nat.lt_pow_succ_log_self h_two_gt_one N
  have hpow_le' : (2 : ℝ) ^ e ≤ (N : ℝ) := by exact_mod_cast hpow_le
  have h_lt' : (N : ℝ) < (2 : ℝ) ^ (e.succ) := by exact_mod_cast h_lt
  have h_div_pos : 0 < (N : ℝ) := by exact_mod_cast hNpos'
  have h_div_le_one : (2 : ℝ) ^ e / (N : ℝ) ≤ 1 := by
    refine (div_le_one ?_).mpr hpow_le'
    exact h_div_pos
  have h_div_gt_half : 1 / 2 < (2 : ℝ) ^ e / (N : ℝ) := by
    have h_ineq : (N : ℝ) < 2 * (2 : ℝ) ^ e := by
      simpa [pow_succ, mul_comm] using h_lt'
    field_simp [h_div_pos.ne.symm]
    exact h_ineq
  set n := (N - 2 ^ e) * 2 ^ q with hn
  have h_div_eq : 2 ^ q * (1 - (2 : ℝ) ^ e / (N : ℝ)) = (n : ℝ) / (N : ℝ) := by
    dsimp [n]
    calc
      2 ^ q * (1 - (2 : ℝ) ^ e / (N : ℝ)) = ((2 ^ q : ℝ) * ((N : ℝ) - (2 : ℝ) ^ e)) / (N : ℝ) := by
        field_simp [h_div_pos.ne.symm]
      _ = ((N : ℝ) - (2 : ℝ) ^ e) * (2 ^ q : ℝ) / (N : ℝ) := by ring
      _ = (↑((N - 2 ^ e) * 2 ^ q) : ℝ) / (N : ℝ) := by
        simp [Nat.cast_sub hpow_le, Nat.cast_mul, Nat.cast_pow]
  have h_floor_le : ((n / N : ℕ) : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
    exact_mod_cast Nat.cast_div_le (m := n) (n := N)
  have h_lt_floor_add_one : (n : ℝ) / (N : ℝ) < ((n / N : ℕ) : ℝ) + 1 := by
    have h_eq_nat : (n / N) * N + n % N = n := by
      simpa [mul_comm] using Nat.div_add_mod n N
    have h_eq : (n : ℝ) = ((n / N : ℕ) : ℝ) * (N : ℝ) + ((n % N : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_mul] using (congrArg (fun x : ℕ => (x : ℝ)) h_eq_nat).symm
    have h_mod_lt_nat : n % N < N := Nat.mod_lt n hNpos'
    have h_mod_lt : ((n % N : ℕ) : ℝ) < (N : ℝ) := Nat.cast_lt.mpr h_mod_lt_nat
    calc
      (n : ℝ) / (N : ℝ) = (((n / N : ℕ) : ℝ) * (N : ℝ) + ((n % N : ℕ) : ℝ)) / (N : ℝ) := by rw [h_eq]
      _ = ((n / N : ℕ) : ℝ) + ((n % N : ℕ) : ℝ) / (N : ℝ) := by
        field_simp [h_div_pos.ne.symm]
      _ < ((n / N : ℕ) : ℝ) + 1 := by
        apply add_lt_add_right
        exact (div_lt_one h_div_pos).mpr h_mod_lt
  have h_log_eq : Real.log ((N : ℝ) / (2 : ℝ) ^ e) = -Real.log (1 - (1 - (2 : ℝ) ^ e / (N : ℝ))) := by
    calc
      Real.log ((N : ℝ) / (2 : ℝ) ^ e) = Real.log (((2 : ℝ) ^ e / (N : ℝ))⁻¹) := by
        field_simp [h_div_pos.ne.symm]
      _ = -Real.log ((2 : ℝ) ^ e / (N : ℝ)) := by rw [Real.log_inv]
      _ = -Real.log (1 - (1 - (2 : ℝ) ^ e / (N : ℝ))) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 0 ≤ 1 - 2^e/N
    linarith
  · -- 1 - 2^e/N < 1/2
    linarith
  · -- floor ≤ real division
    simpa [n, h_div_eq] using h_floor_le
  · -- real division < floor + 1
    simpa [n, h_div_eq] using h_lt_floor_add_one
  · -- log equality
    simpa [e] using h_log_eq

end AdversarialBco.Bit.Aux_gsm_X_floor

namespace AdversarialBco.Bit.Aux_gsm_LLq_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

set_option maxHeartbeats 800000

-- helper lemma: |max t 0 - L| ≤ |t - L| when L ≥ 0
lemma abs_max_sub_nonneg_le_abs_sub {t L : ℝ} (hL : 0 ≤ L) : |max t 0 - L| ≤ |t - L| := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
  · rw [max_eq_right (by linarith)]
    have hzero : |0 - L| = L := by
      rw [show (0 : ℝ) - L = -L by ring, abs_neg, abs_of_nonneg hL]
    rw [hzero]
    have h' : t - L ≤ 0 := by linarith
    have h'' : |t - L| = -(t - L) := abs_of_nonpos h'
    rw [h'']
    linarith

-- helper lemma: max a 0 / c = max (a / c) 0 when c > 0
lemma max_div_max_of_pos {a c : ℝ} (hc : 0 < c) : max a 0 / c = max (a / c) 0 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_left (div_nonneg ha hc.le)]
  · rw [max_eq_right (by linarith), max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)]
    simp

theorem _root_.AdversarialBco.Bit.gsm_LLq_err (B q U : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (hU : U < 2 ^ B) :
    |(AdversarialBco.Bit.gsm_LLq B q U : ℝ) / 2 ^ q + Real.log (((U : ℝ) + 1) / 2 ^ B)| ≤ B * (4 * q + 1) / 2 ^ q := by
  -- setup notation
  set N := U + 1 with hN
  set e := Nat.log 2 N with he
  have h1_lt_2 : 1 < 2 := by norm_num
  have hNpos : N ≠ 0 := by omega
  have hNpos' : 0 < N := Nat.pos_of_ne_zero hNpos
  have hN_le : N ≤ 2 ^ B := by omega
  have he_le_B : e ≤ B := by
    calc
      e = Nat.log 2 N := rfl
      _ ≤ Nat.log 2 (2 ^ B) := Nat.log_mono_right hN_le
      _ = B := Nat.log_pow h1_lt_2 B
  have h_pow_log_le_N : 2 ^ e ≤ N := Nat.pow_log_le_self 2 hNpos
  have hN_lt_pow_succ_log : N < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self h1_lt_2 N
  have hN_le_pow_succ : N ≤ 2 ^ (e + 1) := by omega
  -- define x = 1 - 2^e/N
  set x := 1 - ((2 : ℝ) ^ e : ℝ) / (N : ℝ) with hx
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    have hdiv : ((2 : ℝ) ^ e : ℝ) / (N : ℝ) ≤ 1 := by
      refine (div_le_one ?_).mpr ?_
      · exact mod_cast hNpos'
      · exact mod_cast h_pow_log_le_N
    linarith
  have hx_le_half : x ≤ 1/2 := by
    rw [hx]
    have hN_le_two_mul : (N : ℝ) ≤ 2 * ((2 : ℝ) ^ e) := by
      have htemp : (2 : ℕ) ^ (e + 1) = 2 * (2 ^ e) := by
        rw [pow_succ, mul_comm]
      have hN_le' : N ≤ 2 * (2 ^ e) := by
        rw [← htemp]
        exact hN_le_pow_succ
      exact mod_cast hN_le'
    have hdiv : 1/2 ≤ ((2 : ℝ) ^ e : ℝ) / (N : ℝ) := by
      have hpos : 0 < (N : ℝ) := by exact mod_cast hNpos'
      field_simp [hpos.ne.symm]
      nlinarith
    linarith
  -- define X = (N - 2^e) * 2^q / N (natural division)
  set X := (N - 2 ^ e) * 2 ^ q / N with hX
  have hX_floor := gsm_X_floor q N (by omega)
  have hX_le : (X : ℝ) ≤ ((2 : ℝ) ^ q) * x := by
    simpa [hX, hx] using hX_floor.2.2.1
  have hX_lt : ((2 : ℝ) ^ q) * x < (X : ℝ) + 1 := by
    simpa [hX, hx] using hX_floor.2.2.2.1
  have h_log_eq : Real.log ((N : ℝ) / ((2 : ℝ) ^ e)) = -Real.log (1 - (1 - ((2 : ℝ) ^ e) / (N : ℝ))) := by
    simpa [hx] using hX_floor.2.2.2.2
  have h_log_eq' : Real.log ((N : ℝ) / ((2 : ℝ) ^ e)) = -Real.log (1 - x) := by
    have htemp : 1 - (1 - ((2 : ℝ) ^ e) / (N : ℝ)) = ((2 : ℝ) ^ e) / (N : ℝ) := by ring
    rw [htemp] at h_log_eq
    have htemp2 : 1 - x = ((2 : ℝ) ^ e) / (N : ℝ) := by
      rw [hx]
      ring
    rw [htemp2]
    exact h_log_eq
  -- apply gsm_mercq_log_err with x and X
  have h_merc_x := gsm_mercq_log_err q X x hx_nonneg hx_le_half hX_le hX_lt q
  rcases h_merc_x with ⟨hδ1_low, hδ1_high⟩
  set S := gsm_mercq q X q with hS
  have hδ1_high' : -Real.log (1 - x) - (S : ℝ) / ((2 : ℝ) ^ q) ≤ 4 * (q : ℝ) / ((2 : ℝ) ^ q) + ((1 : ℝ) / 2) ^ q := by
    simpa using hδ1_high
  -- apply gsm_mercq_log_err with x = 1/2, X = 2^(q-1)
  set Y := 2 ^ (q - 1) with hY
  have h_pow_eq : ((2 : ℝ) ^ q) = 2 * ((2 : ℝ) ^ (q - 1)) := by
    calc
      ((2 : ℝ) ^ q) = ((2 : ℝ) ^ ((q - 1) + 1)) := by rw [Nat.sub_add_cancel hq]
      _ = ((2 : ℝ) ^ (q - 1)) * 2 := by rw [pow_succ]
      _ = 2 * ((2 : ℝ) ^ (q - 1)) := by ring
  have hY_eq : ((Y : ℕ) : ℝ) = ((2 : ℝ) ^ q) * (1/2 : ℝ) := by
    calc
      ((Y : ℕ) : ℝ) = ((2 : ℝ) ^ (q - 1)) := by norm_cast
      _ = ((2 : ℝ) ^ q) * (1/2 : ℝ) := by
        have h : ((2 : ℝ) ^ (q - 1)) = ((2 : ℝ) ^ q) * (1/2 : ℝ) := by linarith
        rw [h]
  have hY_le : ((Y : ℕ) : ℝ) ≤ ((2 : ℝ) ^ q) * (1/2 : ℝ) := by
    rw [hY_eq]
  have hY_lt : ((2 : ℝ) ^ q) * (1/2 : ℝ) < ((Y : ℕ) : ℝ) + 1 := by
    rw [hY_eq]
    linarith
  have h_merc_half := gsm_mercq_log_err q Y (1/2 : ℝ) (by norm_num) (by norm_num) hY_le hY_lt q
  rcases h_merc_half with ⟨hδ2_low, hδ2_high⟩
  set Λ := gsm_mercq q Y q with hΛ
  have h_neg_log_half : -Real.log (1 - (1/2 : ℝ)) = Real.log 2 := by
    have h : (1 - (1/2 : ℝ)) = (1/2 : ℝ) := by ring
    rw [h]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  have hδ2_low' : 0 ≤ Real.log 2 - (Λ : ℝ) / ((2 : ℝ) ^ q) := by
    rw [h_neg_log_half] at hδ2_low
    exact hδ2_low
  have hδ2_high' : Real.log 2 - (Λ : ℝ) / ((2 : ℝ) ^ q) ≤ 4 * (q : ℝ) / ((2 : ℝ) ^ q) + ((1 : ℝ) / 2) ^ q := by
    rw [h_neg_log_half] at hδ2_high
    exact hδ2_high
  -- define ε = (4q+1)/2^q
  set ε := (4 * (q : ℝ) + 1) / ((2 : ℝ) ^ q) with hε
  have h_one_div_pow : 1 / ((2 : ℝ) ^ q) = ((1 : ℝ) / 2) ^ q := by
    simpa using (one_div_pow (2 : ℝ) q).symm
  have hε_eq : ε = 4 * (q : ℝ) / ((2 : ℝ) ^ q) + ((1 : ℝ) / 2) ^ q := by
    rw [hε]
    calc
      (4 * (q : ℝ) + 1) / ((2 : ℝ) ^ q) = 4 * (q : ℝ) / ((2 : ℝ) ^ q) + 1 / ((2 : ℝ) ^ q) := by ring
      _ = 4 * (q : ℝ) / ((2 : ℝ) ^ q) + ((1 : ℝ) / 2) ^ q := by rw [h_one_div_pow]
  -- define δ1, δ2
  set δ1 := -Real.log (1 - x) - (S : ℝ) / ((2 : ℝ) ^ q) with hδ1
  set δ2 := Real.log 2 - (Λ : ℝ) / ((2 : ℝ) ^ q) with hδ2
  have hδ1_low' : 0 ≤ δ1 := hδ1_low
  have hδ1_high' : δ1 ≤ ε := by
    rw [hδ1, hε_eq]
    exact hδ1_high'
  have hδ2_low' : 0 ≤ δ2 := hδ2_low'
  have hδ2_high' : δ2 ≤ ε := by
    rw [hδ2, hε_eq]
    exact hδ2_high'
  -- define t and L
  set t := (((B : ℝ) - (e : ℝ)) * (Λ : ℝ) - (S : ℝ)) / ((2 : ℝ) ^ q) with ht
  set L := ((B : ℝ) - (e : ℝ)) * Real.log 2 - Real.log ((N : ℝ) / ((2 : ℝ) ^ e)) with hL
  -- key identity: t - L = δ1 - (B-e)*δ2
  have h_t_sub_L : t - L = δ1 - ((B : ℝ) - (e : ℝ)) * δ2 := by
    rw [ht, hL, hδ1, hδ2]
    have h_log_eq'' : -Real.log (1 - x) = Real.log ((N : ℝ) / ((2 : ℝ) ^ e)) := by linarith
    rw [h_log_eq'']
    ring
  -- L ≥ 0 because N ≤ 2^B
  have hL_nonneg : 0 ≤ L := by
    rw [hL]
    have h_log_nonpos : Real.log ((N : ℝ) / ((2 : ℝ) ^ B)) ≤ 0 := by
      apply Real.log_nonpos
      · positivity
      · refine (div_le_one ?_).mpr ?_
        · positivity
        · exact mod_cast hN_le
    have h_log_div_B : Real.log ((N : ℝ) / ((2 : ℝ) ^ B)) = Real.log (N : ℝ) - (B : ℝ) * Real.log 2 := by
      rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity : ((2 : ℝ) ^ B) ≠ 0), Real.log_pow]
    have h_log_div_e : Real.log ((N : ℝ) / ((2 : ℝ) ^ e)) = Real.log (N : ℝ) - (e : ℝ) * Real.log 2 := by
      rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity : ((2 : ℝ) ^ e) ≠ 0), Real.log_pow]
    rw [h_log_div_e]
    ring_nf
    have h_eq : (B : ℝ) * Real.log 2 - Real.log (N : ℝ) = -(Real.log ((N : ℝ) / ((2 : ℝ) ^ B))) := by
      rw [h_log_div_B]
      ring
    rw [h_eq]
    linarith
  -- bound |t - L|
  have h_abs_t_sub_L : |t - L| ≤ (B : ℝ) * ε := by
    rw [h_t_sub_L]
    have hBe_nonneg : 0 ≤ (B : ℝ) - (e : ℝ) := by
      have : (e : ℝ) ≤ (B : ℝ) := by exact mod_cast he_le_B
      linarith
    have hε_nonneg : 0 ≤ ε := by
      rw [hε]
      refine div_nonneg ?_ (by positivity)
      nlinarith
    have h_abs_le_max : |δ1 - ((B : ℝ) - (e : ℝ)) * δ2| ≤ max (((B : ℝ) - (e : ℝ)) * ε) ε := by
      apply abs_le.mpr
      constructor
      · by_cases h_cases : ((B : ℝ) - (e : ℝ)) * ε ≤ ε
        · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ε := max_eq_right h_cases
          rw [h_max]
          have h_low : -(((B : ℝ) - (e : ℝ)) * ε) ≤ δ1 - ((B : ℝ) - (e : ℝ)) * δ2 := by
            nlinarith
          nlinarith
        · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ((B : ℝ) - (e : ℝ)) * ε := max_eq_left (by linarith)
          rw [h_max]
          nlinarith
      · by_cases h_cases : ((B : ℝ) - (e : ℝ)) * ε ≤ ε
        · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ε := max_eq_right h_cases
          rw [h_max]
          nlinarith
        · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ((B : ℝ) - (e : ℝ)) * ε := max_eq_left (by linarith)
          rw [h_max]
          nlinarith
    have h_max_le : max (((B : ℝ) - (e : ℝ)) * ε) ε ≤ (B : ℝ) * ε := by
      by_cases h_cases : ((B : ℝ) - (e : ℝ)) * ε ≤ ε
      · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ε := max_eq_right h_cases
        rw [h_max]
        -- Need: ε ≤ B*ε
        by_cases hεzero : ε = 0
        · rw [hεzero]
          simp
        · have hεpos : 0 < ε := by
            by_contra! h
            apply hεzero
            linarith
          have hBge1 : (1 : ℝ) ≤ (B : ℝ) := by exact mod_cast hB
          nlinarith
      · have h_max : max (((B : ℝ) - (e : ℝ)) * ε) ε = ((B : ℝ) - (e : ℝ)) * ε := max_eq_left (by linarith)
        rw [h_max]
        have hBe_le_B : (B : ℝ) - (e : ℝ) ≤ (B : ℝ) := by
          have he_nonneg : 0 ≤ (e : ℝ) := by exact mod_cast Nat.zero_le e
          linarith
        nlinarith
    apply le_trans h_abs_le_max
    exact h_max_le
  -- relate the target to |max(t,0) - L|
  have h_left_eq : (AdversarialBco.Bit.gsm_LLq B q U : ℝ) / 2 ^ q + Real.log (((U : ℝ) + 1) / 2 ^ B) = max t 0 - L := by
    -- Express (gsm_LLq B q U : ℝ) in terms of t
    have h_gsm_eq : (AdversarialBco.Bit.gsm_LLq B q U : ℝ) = max (((B : ℝ) - (e : ℝ)) * (Λ : ℝ) - (S : ℝ)) 0 := by
      dsimp [AdversarialBco.Bit.gsm_LLq, N, e, X, S, Y, Λ]
      simp [Int.cast_max, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    -- Express Real.log (((U : ℝ) + 1) / 2 ^ B) in terms of L
    have h_log_eq : Real.log (((U : ℝ) + 1) / 2 ^ B) = -L := by
      have h1 : ((U : ℝ) + 1) = (N : ℝ) := by simpa [hN]
      rw [h1, hL]
      rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity : ((2 : ℝ) ^ B) ≠ 0), Real.log_pow]
      rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity : ((2 : ℝ) ^ e) ≠ 0), Real.log_pow]
      ring
    rw [h_gsm_eq, h_log_eq]
    have hpos : 0 < ((2 : ℝ) ^ q) := by positivity
    rw [max_div_max_of_pos hpos, ht]
    ring
  rw [h_left_eq]
  -- Now we need |max t 0 - L| ≤ B*(4q+1)/2^q
  have h_target_eq' : B * (4 * q + 1) / 2 ^ q = (B : ℝ) * ε := by
    rw [hε]
    ring
  rw [h_target_eq']
  -- Now apply the helper lemma
  apply le_trans (abs_max_sub_nonneg_le_abs_sub hL_nonneg)
  -- Need |t - L| ≤ B*ε
  exact h_abs_t_sub_L

end AdversarialBco.Bit.Aux_gsm_LLq_err

namespace AdversarialBco.Bit.Aux_gsm_readCoins_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

-- Helper: coinLaw applied to a singleton
lemma coinLaw_singleton (b : Bool) : AdversarialBco.BitRAM.coinLaw {b} = (2⁻¹ : ℝ≥0∞) := by
  rw [AdversarialBco.BitRAM.coinLaw]
  simp [Measure.dirac_apply', Set.indicator]
  cases b <;> simp

-- Key lemma: 2*x + e = 2*y + f with e,f ∈ {0,1} implies x = y and e = f
lemma eq_of_mul_two_add_bit {x y e f : ℤ} (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1)
    (h : 2 * x + e = 2 * y + f) : x = y ∧ e = f := by
  rcases he with (he | he) <;> rcases hf with (hf | hf) <;> subst he <;> subst hf <;> omega

-- Characterize readCoins in terms of testBit
lemma readCoins_eq_iff (cs : ℕ → Bool) (c k : ℕ) (z : ℤ) (hz0 : 0 ≤ z) (hz : z < 2 ^ k) :
    AdversarialBco.BitRAM.readCoins cs c k = z ↔
    ∀ i < k, cs (c + i) = (Nat.testBit z.toNat (k - 1 - i)) := by
  induction' k with k ih generalizing cs c z
  · -- k = 0
    have hz0' : z = 0 := by
      have : (2 : ℤ) ^ 0 = 1 := by norm_num
      omega
    subst hz0'
    simp [AdversarialBco.BitRAM.readCoins]
  · -- k = k+1
    have hz_div_lt : z / 2 < (2 : ℤ) ^ k := by
      have : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by ring
      rw [this] at hz
      omega
    have hz_div_nonneg : 0 ≤ z / 2 := Int.ediv_nonneg hz0 (by norm_num)
    have hz_mod_two : z % 2 = 0 ∨ z % 2 = 1 := Int.emod_two_eq z
    have h_eq : 2 * (z / 2) + z % 2 = z := Int.mul_ediv_add_emod z 2
    have h_div_toNat_eq : z.toNat / 2 = (z / 2).toNat := by omega
    simp [AdversarialBco.BitRAM.readCoins]
    -- Goal: (2 * readCoins cs c k + (if cs (c + k) then 1 else 0)) = z ↔
    --   ∀ i < k + 1, cs (c + i) = Nat.testBit z.toNat (k - i)
    constructor
    · intro h
      -- Rewrite z as 2*(z/2) + z%2
      rw [← h_eq] at h
      have h_bit_cases : (if cs (c + k) then (1 : ℤ) else 0) = 0 ∨ (if cs (c + k) then (1 : ℤ) else 0) = 1 := by
        split <;> simp
      rcases eq_of_mul_two_add_bit h_bit_cases hz_mod_two h with ⟨h_read_eq, h_bit_eq⟩
      have h_ih := (ih cs c (z / 2) hz_div_nonneg hz_div_lt).mp h_read_eq
      -- h_ih : ∀ i < k, cs (c + i) = Nat.testBit ((z/2).toNat) (k - 1 - i)
      -- Goal: ∀ i ≤ k, cs (c + i) = Nat.testBit z.toNat (k - i)
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with (h_lt | h_eq')
      · -- i < k
        have h_eq_sub : k - i = (k - 1 - i) + 1 := by omega
        rw [h_eq_sub]
        rw [h_ih i h_lt]
        rw [Nat.testBit_add_one, h_div_toNat_eq]
      · -- i = k
        rw [h_eq']
        have : k - k = 0 := by omega
        rw [this]
        rw [Nat.testBit_zero]
        rcases hz_mod_two with (h0 | h1)
        · rw [h0] at h_bit_eq
          have h_cs_false : cs (c + k) = false := by
            by_contra! h_true
            simp [h_true] at h_bit_eq
          rw [h_cs_false]
          have h_mod : z.toNat % 2 = 0 := by
            have h := Int.toNat_emod hz0 (by norm_num : 0 ≤ (2 : ℤ))
            -- h: (z % 2).toNat = z.toNat % (Int.toNat 2)
            -- simplify Int.toNat 2 to 2
            simp at h
            -- h: (z % 2).toNat = z.toNat % 2
            rw [← h, h0]
            simp
          simp [h_mod]
        · rw [h1] at h_bit_eq
          have h_cs_true : cs (c + k) = true := by
            by_contra! h_false
            simp [h_false] at h_bit_eq
          rw [h_cs_true]
          have h_mod : z.toNat % 2 = 1 := by
            have h := Int.toNat_emod hz0 (by norm_num : 0 ≤ (2 : ℤ))
            simp at h
            rw [← h, h1]
            simp
          simp [h_mod]
    · intro h
      -- h : ∀ i < k+1, cs (c + i) = Nat.testBit z.toNat (k - i)
      have h_prev : ∀ i < k, cs (c + i) = Nat.testBit z.toNat (k - i) := by
        intro i hi
        exact h i (by omega)
      have h_last : cs (c + k) = Nat.testBit z.toNat 0 := by
        have hk := h k (by omega)
        simpa using hk
      have h_prev' : ∀ i < k, cs (c + i) = Nat.testBit ((z / 2).toNat) (k - 1 - i) := by
        intro i hi
        have hi_eq := h_prev i hi
        rw [hi_eq]
        have h_eq_sub : k - i = (k - 1 - i) + 1 := by omega
        rw [h_eq_sub]
        rw [Nat.testBit_add_one, h_div_toNat_eq]
      have h_read_eq : AdversarialBco.BitRAM.readCoins cs c k = z / 2 :=
        (ih cs c (z / 2) hz_div_nonneg hz_div_lt).mpr h_prev'
      have h_bit_eq : (if cs (c + k) then (1 : ℤ) else 0) = z % 2 := by
        rw [Nat.testBit_zero] at h_last
        rcases hz_mod_two with (h0 | h1)
        · have : z.toNat % 2 = 0 := by
            have h := Int.toNat_emod hz0 (by norm_num : 0 ≤ (2 : ℤ))
            simp at h
            rw [← h, h0]
            simp
          rw [this] at h_last
          simp [h_last, h0]
        · have : z.toNat % 2 = 1 := by
            have h := Int.toNat_emod hz0 (by norm_num : 0 ≤ (2 : ℤ))
            simp at h
            rw [← h, h1]
            simp
          rw [this] at h_last
          simp [h_last, h1]
      calc
        2 * AdversarialBco.BitRAM.readCoins cs c k + (if cs (c + k) then 1 else 0) =
        2 * (z / 2) + z % 2 := by rw [h_read_eq, h_bit_eq]
        _ = z := h_eq

-- Helper: coinLaw is a probability measure
theorem coinLaw_isProb : IsProbabilityMeasure AdversarialBco.BitRAM.coinLaw where
  measure_univ := by
    rw [AdversarialBco.BitRAM.coinLaw]
    simp [Measure.dirac_apply', Set.indicator]
    calc
      (2⁻¹ : ENNReal) + (2⁻¹ : ENNReal) = (2⁻¹ : ENNReal) * 2 := by ring
      _ = 1 := by
        rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ∞)]

theorem _root_.AdversarialBco.Bit.gsm_readCoins_law (c k : ℕ) (z : ℤ) (hz0 : 0 ≤ z) (hz : z < 2 ^ k) :
    AdversarialBco.BitRAM.coinStream {cs | AdversarialBco.BitRAM.readCoins cs c k = z} = (2⁻¹ : ℝ≥0∞) ^ k := by
  haveI := coinLaw_isProb
  -- Express the event as Set.pi on the shifted index set
  let S : Finset ℕ := (Finset.range k).image (c + ·)
  have hS_card : S.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h; exact Nat.add_left_cancel h
  -- Define the bits of z (most significant first)
  let b : ℕ → Bool := λ j =>
    if h : j ∈ S then
      let i := j - c
      Nat.testBit z.toNat (k - 1 - i)
    else false
  -- Prove that the event equals Set.pi S (fun j => {b j})
  have h_event_eq : {cs | AdversarialBco.BitRAM.readCoins cs c k = z} =
      Set.pi (S : Set ℕ) (fun j => {b j}) := by
    ext cs
    constructor
    · intro h j hj
      have hjS : j ∈ S := hj
      rcases Finset.mem_image.mp hjS with ⟨i, hi, rfl⟩
      have hi_lt_k : i < k := Finset.mem_range.mp hi
      have h_char := (readCoins_eq_iff cs c k z hz0 hz).mp h
      -- h_char i hi_lt_k : cs (c + i) = Nat.testBit z.toNat (k - 1 - i)
      -- b (c + i) = Nat.testBit z.toNat (k - 1 - ((c + i) - c)) = Nat.testBit z.toNat (k - 1 - i)
      have h_mem : c + i ∈ S := by
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_range.mpr hi_lt_k, rfl⟩
      have h_sub : (c + i) - c = i := by omega
      have hb : b (c + i) = Nat.testBit z.toNat (k - 1 - i) := by
        simp [b, h_mem, h_sub]
      -- Goal: cs (c + i) ∈ (fun j => {b j}) (c + i)
      -- i.e., cs (c + i) = b (c + i)
      simpa [hb] using h_char i hi_lt_k
    · intro h
      -- h: cs ∈ Set.pi S (fun j => {b j})
      -- So ∀ j ∈ S, cs j = b j
      have h_char : ∀ i < k, cs (c + i) = Nat.testBit z.toNat (k - 1 - i) := by
        intro i hi
        have hj : c + i ∈ (S : Set ℕ) := by
          apply Finset.mem_coe.mpr
          apply Finset.mem_image.mpr
          exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
        have h_cs := h (c + i) hj
        -- h_cs : cs (c + i) ∈ {b (c + i)}
        -- So cs (c + i) = b (c + i)
        have h_eq : cs (c + i) = b (c + i) := by simpa using h_cs
        -- Now compute b (c + i)
        have h_mem : c + i ∈ S := by
          apply Finset.mem_image.mpr
          exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
        have h_sub : (c + i) - c = i := by omega
        have h_b_eq : b (c + i) = Nat.testBit z.toNat (k - 1 - i) := by
          simp [b, h_mem, h_sub]
        rw [h_eq, h_b_eq]
      -- Now use readCoins_eq_iff to conclude
      exact (readCoins_eq_iff cs c k z hz0 hz).mpr h_char
  rw [h_event_eq]
  rw [AdversarialBco.BitRAM.coinStream]
  rw [Measure.infinitePi_pi]
  · simp [coinLaw_singleton, Finset.prod_const, hS_card]
  · intro i hi
    exact measurableSet_singleton _

end AdversarialBco.Bit.Aux_gsm_readCoins_law
