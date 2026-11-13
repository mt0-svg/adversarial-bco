/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.GsM

@[expose] public section

/-!
# The theorem BM-INT on the integer function of Procedure BM-INT

`gsm_prec B = B + 2 len B + 4` is the working precision `p`, `gsm_prodq` the product loop of step 7 on the binary
digits of the angle, and `gsSpec B U W` the integer pair `(Γ_c, Γ_s)` that Procedure BM-INT returns on the coin blocks
`U, W < 2^B`; the draws are `Γ/2^q`, `q = 2p`.

`gsSpec_err` (the theorem BM-INT): for `B ≥ 8` each draw is within `2^{-B}` of the Box-Muller
value `(-2 log u')^{1/2} (cos, sin)(2π w')` at `u' = (U + 1)/2^B`, `w' = (W + 1)/2^B`, and at most `(2B)^{1/2}` in
absolute value; on every value of the coins.

The steps, from the lemmas of Bit/GsM.lean: `gss_chain` (one factor of the chain in the plane,
from `gsm_chainq_err`), `gss_prod` (Lemma PROD by induction on the steps, from `gsm_cmulq_err`, in the form
`Δ_k ≤ 2 k (ε + 2^{1/2} 2^{-p})` while `2 B ε ≤ 1`), `gss_theta_end` (Lemma ANGLE, from `gsm_angle_digits`),
`gss_wrap` (`W + 1 = 2^B` gives the angle `0`), `gss_L` (`0 ≤ -log u' ≤ B log 2`), `gss_prec` (`20 ≤ p ≤ 3B + 4` and
`16 B² 2^B ≤ 2^p`), `gss_combine`, `gss_final`, `gss_sure`, `gss_sure_abs` (the final arithmetic); Lemma LOG
is `gsm_LLq_err`, Corollary RAD `gsm_radius_err`.
-/

open scoped ENNReal NNReal

namespace AdversarialBco.Bit
/-- The working precision `p = B + 2 len B + 4` of Procedure BM-INT. -/
def gsm_prec (B : ℕ) : ℕ := B + 2 * Nat.size B + 4

/-- Step 7 of Procedure BM-INT: the pair after the steps `0, ..., k` of the product loop on the digits of `J`
(digit `B - 1 - m` at step `m`), at scale `2^p`. -/
def gsm_prodq (p B J : ℕ) : ℕ → ℤ × ℤ
  | 0 => (if J.testBit (B - 1) then -2 ^ p else 2 ^ p, 0)
  | k + 1 =>
    if J.testBit (B - 1 - (k + 1)) then
      gsm_cmulq p (gsm_prodq p B J k) (((gsm_chainq p k).1 : ℤ), ((gsm_chainq p k).2 : ℤ))
    else gsm_prodq p B J k

/-- Procedure BM-INT on the coin blocks `U, W < 2^B`: the integer pair `(Γ_c, Γ_s)`, the draws being
`Γ/2^q`, `q = 2p`. -/
def gsSpec (B U W : ℕ) : ℤ × ℤ :=
  ((Nat.sqrt (2 * (gsm_LLq B (2 * gsm_prec B) U).toNat) : ℤ) *
      (gsm_prodq (gsm_prec B) B ((W + 1) % 2 ^ B) (B - 1)).1,
    (Nat.sqrt (2 * (gsm_LLq B (2 * gsm_prec B) U).toNat) : ℤ) *
      (gsm_prodq (gsm_prec B) B ((W + 1) % 2 ^ B) (B - 1)).2)

/-- One computed factor of the chain against `exp(iπ/2^(k+1))`, in the complex plane. -/
theorem gss_chain (p k : ℕ) (hp : 20 ≤ p) :
    ‖((((gsm_chainq p k).1 : ℤ) : ℂ) + (((gsm_chainq p k).2 : ℤ) : ℂ) * Complex.I) / 2 ^ p -
        Complex.exp (((Real.pi / 2 ^ (k + 1) : ℝ) : ℂ) * Complex.I)‖ ≤ 10517 / 1000 / 2 ^ p := by
  obtain ⟨h1, h2, h3, -⟩ := gsm_chainq_err p k hp
  set C := (gsm_chainq p k).1
  set S := (gsm_chainq p k).2
  set x : ℝ := Real.pi / 2 ^ (k + 1)
  have e : (((C : ℤ) : ℂ) + ((S : ℤ) : ℂ) * Complex.I) / 2 ^ p - Complex.exp ((x : ℂ) * Complex.I) =
      (((C : ℝ) / 2 ^ p - Real.cos x : ℝ) : ℂ) + (((S : ℝ) / 2 ^ p - Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have a1 : |(C : ℝ) / 2 ^ p - Real.cos x| ≤ 1547 / 1000 / 2 ^ p := by
    rw [abs_sub_comm, abs_le]; constructor <;> linarith [show (0 : ℝ) < 1547 / 1000 / 2 ^ p by positivity]
  have a2 : |(S : ℝ) / 2 ^ p - Real.sin x| ≤ 897 / 100 / 2 ^ p := by rw [abs_sub_comm]; exact h3
  have : (1547 / 1000 / 2 ^ p : ℝ) + 897 / 100 / 2 ^ p = 10517 / 1000 / 2 ^ p := by ring
  linarith


/-- The exact angle after the steps `0, ..., k`: `θ_k = Σ_{j ≤ k} b_j π/2^j`, `b_j` the digit `B - 1 - j` of `J`. -/
noncomputable def gss_theta (B J k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), if J.testBit (B - 1 - j) then Real.pi / 2 ^ j else 0

/-- Lemma PROD: after `k ≤ B` steps the computed pair is within `2 k a` of `exp(i θ_k)`, `a = ε + √2/2^p`. -/
theorem gss_prod (p B J : ℕ) (hp : 20 ≤ p) (hBε : 2 * B * (10517 / 1000 / 2 ^ p : ℝ) ≤ 1) :
    ∀ k, k ≤ B → ‖(((gsm_prodq p B J k).1 : ℂ) + ((gsm_prodq p B J k).2 : ℂ) * Complex.I) / 2 ^ p -
        Complex.exp ((gss_theta B J k : ℂ) * Complex.I)‖ ≤
      2 * k * (10517 / 1000 / 2 ^ p + Real.sqrt 2 / 2 ^ p) := by
  set ε : ℝ := 10517 / 1000 / 2 ^ p with hε
  set a : ℝ := ε + Real.sqrt 2 / 2 ^ p with ha
  have hε0 : 0 ≤ ε := by positivity
  have ha0 : 0 ≤ a := by positivity
  intro k
  induction k with
  | zero =>
    intro _
    by_cases h : J.testBit (B - 1) = true
    · simp [gsm_prodq, gss_theta, h, Complex.exp_pi_mul_I]
    · simp [gsm_prodq, gss_theta, h]
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hθ : gss_theta B J (k + 1) =
        gss_theta B J k + (if J.testBit (B - 1 - (k + 1)) then Real.pi / 2 ^ (k + 1) else 0) := by
      unfold gss_theta
      rw [Finset.sum_range_succ]
    have hkε : 2 * (k : ℝ) * ε ≤ 1 := by
      have : (k : ℝ) ≤ B := by exact_mod_cast (show k ≤ B by omega)
      nlinarith
    have hstep : 2 * (k : ℝ) * a * (1 + ε) + ε + Real.sqrt 2 / 2 ^ p ≤ 2 * ((k + 1 : ℕ) : ℝ) * a := by
      have : 2 * (k : ℝ) * a * ε ≤ a := by nlinarith
      push_cast
      nlinarith
    by_cases hb : J.testBit (B - 1 - (k + 1)) = true
    · rw [hθ, ite_eq_left hb]
      have hrec : gsm_prodq p B J (k + 1) =
          gsm_cmulq p (gsm_prodq p B J k) (((gsm_chainq p k).1 : ℤ), ((gsm_chainq p k).2 : ℤ)) := by
        rw [gsm_prodq, ite_eq_left hb]
      rw [hrec]
      have hexp : Complex.exp (((gss_theta B J k + Real.pi / 2 ^ (k + 1) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((gss_theta B J k : ℂ) * Complex.I) *
            Complex.exp (((Real.pi / 2 ^ (k + 1) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; push_cast; ring_nf
      rw [hexp]
      have hc := gsm_cmulq_err p (gsm_prodq p B J k) (((gsm_chainq p k).1 : ℤ), ((gsm_chainq p k).2 : ℤ))
        (Complex.exp ((gss_theta B J k : ℂ) * Complex.I))
        (Complex.exp (((Real.pi / 2 ^ (k + 1) : ℝ) : ℂ) * Complex.I))
        (Complex.norm_exp_ofReal_mul_I _) (Complex.norm_exp_ofReal_mul_I _) (2 * k * a) ε ihk
        (gss_chain p k hp)
      exact hc.trans hstep
    · rw [hθ, ite_eq_right hb]
      have hrec : gsm_prodq p B J (k + 1) = gsm_prodq p B J k := by
        rw [gsm_prodq, ite_eq_right hb]
      rw [hrec]
      simp only [add_zero]
      refine ihk.trans ?_
      have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      nlinarith


theorem gss_theta_end (B J : ℕ) (hB : 1 ≤ B) (hJ : J < 2 ^ B) :
    gss_theta B J (B - 1) = 2 * Real.pi * J / 2 ^ B := by
  unfold gss_theta
  rw [Nat.sub_add_cancel hB]
  exact (gsm_angle_digits B J hJ).symm

/-- `J' = (W + 1) mod 2^B` and `W + 1` give the same point of the circle. -/
theorem gss_wrap (B W : ℕ) (hW : W < 2 ^ B) :
    Real.cos (2 * Real.pi * (((W + 1) % 2 ^ B : ℕ) : ℝ) / 2 ^ B) =
        Real.cos (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B)) ∧
      Real.sin (2 * Real.pi * (((W + 1) % 2 ^ B : ℕ) : ℝ) / 2 ^ B) =
        Real.sin (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B)) := by
  have h2 : (2 : ℝ) ^ B ≠ 0 := pow_ne_zero _ two_ne_zero
  rcases Nat.lt_or_ge (W + 1) (2 ^ B) with h | h
  · rw [Nat.mod_eq_of_lt h]
    push_cast
    constructor <;> ring_nf
  · have he : W + 1 = 2 ^ B := by omega
    have hW' : (W : ℝ) + 1 = 2 ^ B := by exact_mod_cast he
    rw [he, Nat.mod_self, hW', div_self h2]
    simp

/-- The real and imaginary parts are bounded by the modulus. -/
theorem gss_re_im (a b : ℝ) :
    |a| ≤ ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ∧ |b| ≤ ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := by
  constructor
  · simpa using Complex.abs_re_le_norm ((a : ℂ) + (b : ℂ) * Complex.I)
  · simpa using Complex.abs_im_le_norm ((a : ℂ) + (b : ℂ) * Complex.I)

/-- `|r x - ρ c| ≤ e_R (1 + δ) + ρ δ` from `|r - ρ| ≤ e_R`, `|x - c| ≤ δ`, `|c| ≤ 1`. -/
theorem gss_combine (r ρ x c eR δ : ℝ) (hr : |r - ρ| ≤ eR) (hx : |x - c| ≤ δ) (hc : |c| ≤ 1) (hρ : 0 ≤ ρ) :
    |r * x - ρ * c| ≤ eR * (1 + δ) + ρ * δ := by
  have e : r * x - ρ * c = (r - ρ) * x + ρ * (x - c) := by ring
  have hxa : |x| ≤ 1 + δ := by
    have := abs_sub_abs_le_abs_sub x c
    linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hρ]
  have h1 : |r - ρ| * |x| ≤ eR * (1 + δ) :=
    mul_le_mul hr hxa (abs_nonneg _) ((abs_nonneg _).trans hr)
  have h2 : ρ * |x - c| ≤ ρ * δ := mul_le_mul_of_nonneg_left hx hρ
  linarith

/-- The precision: `20 ≤ p`, `p ≤ 3B + 4` and `16 B² 2^B ≤ 2^p` for `B ≥ 8`. -/
theorem gss_prec (B : ℕ) (hB : 8 ≤ B) :
    20 ≤ gsm_prec B ∧ gsm_prec B ≤ 3 * B + 4 ∧ 16 * B ^ 2 * 2 ^ B ≤ 2 ^ gsm_prec B := by
  have hs4 : 4 ≤ Nat.size B := Nat.lt_size.2 (by
    calc 2 ^ 3 = 8 := by norm_num
      _ ≤ B := hB)
  have hsB : Nat.size B ≤ B := Nat.size_le.2 Nat.lt_two_pow_self
  have hlt : B < 2 ^ Nat.size B := Nat.lt_size_self B
  refine ⟨by unfold gsm_prec; omega, by unfold gsm_prec; omega, ?_⟩
  have e : 2 ^ gsm_prec B = 2 ^ B * (2 ^ Nat.size B) ^ 2 * 16 := by
    unfold gsm_prec; ring
  rw [e]
  have : B ^ 2 ≤ (2 ^ Nat.size B) ^ 2 := Nat.pow_le_pow_left hlt.le 2
  nlinarith [Nat.zero_le (2 ^ B)]


/-- The radius: `-log u' ∈ [0, B log 2]` for `u' = (U + 1)/2^B`, `U < 2^B`. -/
theorem gss_L (B U : ℕ) (hU : U < 2 ^ B) :
    0 ≤ -Real.log (((U : ℝ) + 1) / 2 ^ B) ∧ -Real.log (((U : ℝ) + 1) / 2 ^ B) ≤ B * Real.log 2 := by
  have h2 : (0 : ℝ) < 2 ^ B := by positivity
  have hU1 : (U : ℝ) + 1 ≤ 2 ^ B := by exact_mod_cast hU
  have hy0 : 0 < ((U : ℝ) + 1) / 2 ^ B := by positivity
  constructor
  · have := Real.log_nonpos hy0.le ((div_le_one h2).2 hU1)
    linarith
  · have hlo : 1 / (2 : ℝ) ^ B ≤ ((U : ℝ) + 1) / 2 ^ B :=
      div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg U : (0 : ℝ) ≤ U)]) h2.le
    have := Real.log_le_log (by positivity) hlo
    rw [one_div, Real.log_inv, Real.log_pow] at this
    linarith

/-- The final arithmetic of the theorem BM-INT: `e_R (1 + δ) + ρ δ ≤ 2^{-B}`. -/
theorem gss_final (B : ℕ) (P eR δ ρ : ℝ) (hB : 8 ≤ B) (hP : 16 * (B : ℝ) ^ 2 * 2 ^ B ≤ P)
    (heR0 : 0 ≤ eR) (heR : eR ≤ 9 * B / P) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 25 * B / P) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ B / 2) :
    eR * (1 + δ) + ρ * δ ≤ 1 / 2 ^ B := by
  have hB' : (8 : ℝ) ≤ B := by exact_mod_cast hB
  have h2 : (0 : ℝ) < 2 ^ B := by positivity
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have h1 : eR * (1 + δ) ≤ 18 * B / P := by
    have : eR * (1 + δ) ≤ eR * 2 := mul_le_mul_of_nonneg_left (by linarith) heR0
    have e : (18 : ℝ) * B / P = 9 * B / P * 2 := by ring
    rw [e]; nlinarith
  have h3 : ρ * δ ≤ B / 2 * (25 * B / P) := mul_le_mul hρ hδ hδ0 (by positivity)
  have h4 : 18 * (B : ℝ) / P + B / 2 * (25 * B / P) ≤ 16 * B ^ 2 / P := by
    have e : 18 * (B : ℝ) / P + B / 2 * (25 * B / P) = (18 * B + 25 / 2 * B ^ 2) / P := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hP0.le
    nlinarith
  have h5 : 16 * (B : ℝ) ^ 2 / P ≤ 1 / 2 ^ B := by
    rw [div_le_div_iff₀ hP0 h2]; linarith
  linarith


/-- The sure bound: `ρ' + 2^{-B} ≤ (2B)^{1/2}` when `ρ'² ≤ 2 B log 2`, `B ≥ 8`. -/
theorem gss_sure (B : ℕ) (hB : 8 ≤ B) (L : ℝ) (hL : L ≤ B * Real.log 2) :
    Real.sqrt (2 * L) + 1 / 2 ^ B ≤ Real.sqrt (2 * B) := by
  have hBr : (8 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog := Real.log_two_lt_d9
  have h1 : Real.sqrt (2 * L) ≤ 84 / 100 * Real.sqrt (2 * B) := by
    rw [show (84 / 100 : ℝ) * Real.sqrt (2 * B) = Real.sqrt ((84 / 100) ^ 2 * (2 * B)) by
      rw [Real.sqrt_mul (x := (84 / 100) ^ 2) (by norm_num) (2 * B), Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    nlinarith
  have h4 : 4 ≤ Real.sqrt (2 * B) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by linarith)
  have h2 : 1 / (2 : ℝ) ^ B ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- `|g| ≤ S` from `|g - ρ c| ≤ e`, `|c| ≤ 1`, `ρ + e ≤ S`. -/
theorem gss_sure_abs (g ρ c e S : ℝ) (h : |g - ρ * c| ≤ e) (hc : |c| ≤ 1) (hρ : 0 ≤ ρ) (hS : ρ + e ≤ S) :
    |g| ≤ S := by
  have h1 := abs_sub_abs_le_abs_sub g (ρ * c)
  have h2 : |ρ * c| ≤ ρ := by
    rw [abs_mul, abs_of_nonneg hρ]
    exact mul_le_of_le_one_right hρ hc
  linarith

/-- **The theorem BM-INT** on the integer function `gsSpec`: for `B ≥ 8` and coin blocks
`U, W < 2^B`, each output, read as `Γ/2^q`, is within `2^{-B}` of the Box-Muller value at `u' = (U + 1)/2^B`,
`w' = (W + 1)/2^B`, and at most `(2B)^{1/2}` in absolute value. -/
theorem gsSpec_err (B U W : ℕ) (hB : 8 ≤ B) (hU : U < 2 ^ B) (hW : W < 2 ^ B) :
    |((gsSpec B U W).1 : ℝ) / 2 ^ (2 * gsm_prec B) -
        Real.sqrt (-2 * Real.log (((U : ℝ) + 1) / 2 ^ B)) * Real.cos (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤
      1 / 2 ^ B ∧
    |((gsSpec B U W).2 : ℝ) / 2 ^ (2 * gsm_prec B) -
        Real.sqrt (-2 * Real.log (((U : ℝ) + 1) / 2 ^ B)) * Real.sin (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤
      1 / 2 ^ B ∧
    |((gsSpec B U W).1 : ℝ) / 2 ^ (2 * gsm_prec B)| ≤ Real.sqrt (2 * B) ∧
    |((gsSpec B U W).2 : ℝ) / 2 ^ (2 * gsm_prec B)| ≤ Real.sqrt (2 * B) := by
  have hspec : gsSpec B U W =
      ((Nat.sqrt (2 * (gsm_LLq B (2 * gsm_prec B) U).toNat) : ℤ) *
          (gsm_prodq (gsm_prec B) B ((W + 1) % 2 ^ B) (B - 1)).1,
        (Nat.sqrt (2 * (gsm_LLq B (2 * gsm_prec B) U).toNat) : ℤ) *
          (gsm_prodq (gsm_prec B) B ((W + 1) % 2 ^ B) (B - 1)).2) := rfl
  rw [hspec]
  obtain ⟨hp20, hp3, hpow⟩ := gss_prec B hB
  set p := gsm_prec B with hp
  set q := 2 * p with hq
  have hB1 : 1 ≤ B := by omega
  have hBr : (8 : ℝ) ≤ B := by exact_mod_cast hB
  have h2p : (0 : ℝ) < 2 ^ p := by positivity
  have h2B : (0 : ℝ) < 2 ^ B := by positivity
  have h2B1 : (1 : ℝ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have hpowR : 16 * (B : ℝ) ^ 2 * 2 ^ B ≤ 2 ^ p := by exact_mod_cast hpow
  have hBB : 16 * (B : ℝ) ^ 2 ≤ 16 * (B : ℝ) ^ 2 * 2 ^ B := le_mul_of_one_le_right (by positivity) h2B1
  -- the radius (Lemma LOG, Corollary RAD)
  set L : ℝ := -Real.log (((U : ℝ) + 1) / 2 ^ B) with hLdef
  obtain ⟨hL0, hLB⟩ := gss_L B U hU
  have hLL0 : 0 ≤ gsm_LLq B q U := by unfold gsm_LLq; exact le_max_right _ _
  set LL : ℕ := (gsm_LLq B q U).toNat with hLLdef
  have hcast : ((LL : ℕ) : ℝ) = (gsm_LLq B q U : ℝ) := by
    rw [hLLdef, ← Int.cast_natCast, Int.toNat_of_nonneg hLL0]
  have he : |(LL : ℝ) / 2 ^ (2 * p) - L| ≤ B * (4 * q + 1) / 2 ^ q := by
    have h := gsm_LLq_err B q U hB1 (by omega) hU
    have e : (LL : ℝ) / 2 ^ (2 * p) - L =
        (gsm_LLq B q U : ℝ) / 2 ^ q + Real.log (((U : ℝ) + 1) / 2 ^ B) := by
      rw [hcast, hLdef]; ring
    rw [e]
    exact_mod_cast h
  have hrad := gsm_radius_err p LL L (B * (4 * q + 1) / 2 ^ q) hL0 he
  set eR : ℝ := Real.sqrt (2 * (B * (4 * q + 1) / 2 ^ q)) + 1 / 2 ^ p with heRdef
  have heR0 : 0 ≤ eR := by positivity
  have heR : eR ≤ 9 * B / 2 ^ p := by
    have hs : Real.sqrt (2 * (B * (4 * q + 1) / 2 ^ q)) ≤ 8 * B / 2 ^ p := by
      rw [show (8 * (B : ℝ) / 2 ^ p) = Real.sqrt ((8 * B / 2 ^ p) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      have hq2 : (2 : ℝ) ^ q = (2 ^ p) ^ 2 := by rw [hq]; ring
      have e1 : 2 * ((B : ℝ) * (4 * q + 1) / 2 ^ q) = 2 * B * (4 * q + 1) / (2 ^ p) ^ 2 := by
        rw [hq2]; ring
      have e2 : (8 * (B : ℝ) / 2 ^ p) ^ 2 = 64 * B ^ 2 / (2 ^ p) ^ 2 := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hqr : (q : ℝ) ≤ 6 * B + 8 := by
        have : q ≤ 6 * B + 8 := by omega
        exact_mod_cast this
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ B) (by linarith : (0 : ℝ) ≤ 6 * B + 8 - q),
        mul_nonneg (by linarith : (0 : ℝ) ≤ B) (by linarith : (0 : ℝ) ≤ B - 8)]
    have h1 : 1 / (2 : ℝ) ^ p ≤ B / 2 ^ p := div_le_div_of_nonneg_right (by linarith) h2p.le
    have e : (9 : ℝ) * B / 2 ^ p = 8 * B / 2 ^ p + B / 2 ^ p := by ring
    rw [heRdef, e]; linarith
  -- the angle (Lemmas CHAIN, ANGLE, PROD)
  set J : ℕ := (W + 1) % 2 ^ B with hJdef
  have hJ : J < 2 ^ B := Nat.mod_lt _ (by positivity)
  have hBε : 2 * B * (10517 / 1000 / 2 ^ p : ℝ) ≤ 1 := by
    have e : 2 * (B : ℝ) * (10517 / 1000 / 2 ^ p) = 2 * B * (10517 / 1000) / 2 ^ p := by ring
    rw [e, div_le_one h2p]
    nlinarith
  have hprod := gss_prod p B J hp20 hBε (B - 1) (by omega)
  rw [gss_theta_end B J hB1 hJ] at hprod
  set ZX := (gsm_prodq p B J (B - 1)).1 with hZX
  set ZY := (gsm_prodq p B J (B - 1)).2 with hZY
  set θ : ℝ := 2 * Real.pi * J / 2 ^ B with hθ
  have hdiff : ((ZX : ℂ) + (ZY : ℂ) * Complex.I) / 2 ^ p - Complex.exp ((θ : ℂ) * Complex.I) =
      (((ZX : ℝ) / 2 ^ p - Real.cos θ : ℝ) : ℂ) + (((ZY : ℝ) / 2 ^ p - Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
  rw [hdiff] at hprod
  obtain ⟨hX, hY⟩ := gss_re_im ((ZX : ℝ) / 2 ^ p - Real.cos θ) ((ZY : ℝ) / 2 ^ p - Real.sin θ)
  set δ : ℝ := 2 * ((B - 1 : ℕ) : ℝ) * (10517 / 1000 / 2 ^ p + Real.sqrt 2 / 2 ^ p) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 25 * B / 2 ^ p := by
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hB1r : ((B - 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast Nat.sub_le B 1
    have e : δ = 2 * ((B - 1 : ℕ) : ℝ) * (10517 / 1000 + Real.sqrt 2) / 2 ^ p := by rw [hδdef]; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ h2p.le
    have := mul_le_mul hB1r (by linarith : 10517 / 1000 + Real.sqrt 2 ≤ 12017 / 1000)
      (by positivity) (by positivity)
    linarith
  have hδ1 : δ ≤ 1 := by
    refine hδ.trans ?_
    rw [div_le_one h2p]
    nlinarith
  obtain ⟨hcw, hsw⟩ := gss_wrap B W hW
  have hXc : |(ZX : ℝ) / 2 ^ p - Real.cos (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤ δ := by
    rw [← hcw]; exact hX.trans hprod
  have hYs : |(ZY : ℝ) / 2 ^ p - Real.sin (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤ δ := by
    rw [← hsw]; exact hY.trans hprod
  -- the assembly
  have hρ : Real.sqrt (-2 * Real.log (((U : ℝ) + 1) / 2 ^ B)) = Real.sqrt (2 * L) := by
    rw [hLdef]; ring_nf
  have hρ0 : 0 ≤ Real.sqrt (2 * L) := Real.sqrt_nonneg _
  have hρle : Real.sqrt (2 * L) ≤ B / 2 := by
    rw [show ((B : ℝ) / 2) = Real.sqrt ((B / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have hlog := Real.log_two_lt_d9
    nlinarith
  have hG : ∀ Z : ℤ, ((Nat.sqrt (2 * LL) : ℝ) * (Z : ℝ)) / 2 ^ q =
      ((Nat.sqrt (2 * LL) : ℝ) / 2 ^ p) * ((Z : ℝ) / 2 ^ p) := by
    intro Z; rw [hq]; ring
  have hfin := gss_final B (2 ^ p) eR δ (Real.sqrt (2 * L)) hB hpowR heR0 heR hδ0 hδ hδ1 hρle
  have hc1 : |((Nat.sqrt (2 * LL) : ℝ) * (ZX : ℝ)) / 2 ^ q -
      Real.sqrt (2 * L) * Real.cos (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤ 1 / 2 ^ B := by
    have := hG ZX
    rw [this]
    exact (gss_combine _ _ _ _ eR δ hrad hXc (Real.abs_cos_le_one _) hρ0).trans hfin
  have hs1 : |((Nat.sqrt (2 * LL) : ℝ) * (ZY : ℝ)) / 2 ^ q -
      Real.sqrt (2 * L) * Real.sin (2 * Real.pi * (((W : ℝ) + 1) / 2 ^ B))| ≤ 1 / 2 ^ B := by
    have := hG ZY
    rw [this]
    exact (gss_combine _ _ _ _ eR δ hrad hYs (Real.abs_sin_le_one _) hρ0).trans hfin
  have hsure := gss_sure B hB L hLB
  push_cast
  rw [hρ]
  exact ⟨hc1, hs1, gss_sure_abs _ _ _ _ _ hc1 (Real.abs_cos_le_one _) hρ0 hsure,
    gss_sure_abs _ _ _ _ _ hs1 (Real.abs_sin_le_one _) hρ0 hsure⟩

end AdversarialBco.Bit
