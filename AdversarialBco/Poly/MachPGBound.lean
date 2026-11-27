/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPG
public import AdversarialBco.Poly.PgArithProof

@[expose] public section

/-! # The step bound of the code of PG: the parameters of a stage

The bounds that the step bound of PG-N (`kPGNS_boundL`, Conj1Arith/MachN/Bound.lean) reads: each parameter of a stage
(`ρ_i ≤ 26244 d²`, `N`, `n_T`, `j_b` by powers of `d`; `J`, `m_T` through `log (1/δ₁)` and the number of stages, at
most `2 (2 + log (R₀/r₀))`), and `log (1/δ₁) ≤ 15 + 4 log (2dn/δ)` (`pgb_rho_le` to `pgb_MT_le`, `pgb_stages_le`,
`pgb_delta1`); the bounds `PB` by a power of one variable `y` combine them, and `kPGpoly` is the step count of the
code with the step count of a stage as a variable.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL

namespace AdversarialBco.Poly.PG

/-! ## Bounds on the parameters -/

theorem pgb_ceil_le {x B : ℝ} (h : x + 1 ≤ B) (hB : 0 ≤ B) : (⌈x⌉₊ : ℝ) ≤ B := by
  rcases le_or_gt 0 x with hx | hx
  · exact (Nat.ceil_lt_add_one hx).le.trans h
  · rw [Nat.ceil_eq_zero.mpr hx.le]; simpa using hB

theorem pgb_logb_le {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 2 * Real.log x := by
  have h2 := Real.log_two_gt_d9
  have hl := Real.log_nonneg hx
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

theorem pgb_pow_le {X c : ℝ} {j : ℕ} (hX : 1 ≤ X) (hc0 : 0 ≤ c) (hc : c ≤ 10 ^ 52)
    (hj : j ≤ 28) : c * X ^ j ≤ 10 ^ 52 * X ^ 28 :=
  mul_le_mul hc (pow_le_pow_right₀ hX hj) (pow_nonneg (by linarith) _) (by norm_num)

theorem pgb_log_le_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx; linarith

theorem pgb_stages_le {r0 R0 : ℝ} (h0 : 0 < r0) (h : r0 ≤ R0) :
    (pgStages r0 R0 : ℝ) ≤ 2 * (2 + Real.log (R0 / r0)) := by
  have hy : 1 ≤ R0 / r0 := by rw [le_div_iff₀ h0]; linarith
  have hl := Real.log_nonneg hy
  have hlb := pgb_logb_le hy
  have hlb0 : 0 ≤ Real.logb 2 (R0 / r0) := Real.logb_nonneg (by norm_num) hy
  have hc : (⌈Real.logb 2 (R0 / r0)⌉₊ : ℝ) ≤ Real.logb 2 (R0 / r0) + 1 := (Nat.ceil_lt_add_one hlb0).le
  unfold pgStages
  rw [Nat.cast_max]
  apply max_le <;> push_cast <;> linarith

theorem pgb_delta1 {d n : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h0 : 0 < δ) (h1 : δ < 1) :
    0 < min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) ∧ min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) ≤ 1 ∧
      Real.log (1 / min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)) ≤ 15 + 4 * Real.log (2 * d * n / δ) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have hDp : (0 : ℝ) < (d : ℝ) * n := by linarith
  have hpos : 0 < Real.exp (-14) / ((d : ℝ) * n) ^ 3 := div_pos (Real.exp_pos _) (pow_pos hDp 3)
  have hq : 2 * (d : ℝ) * n / δ = 2 * ((d : ℝ) * n) / δ := by ring
  have hDle : (d : ℝ) * n ≤ 2 * d * n / δ := by
    rw [hq, le_div_iff₀ h0]; nlinarith
  have hL0 : 0 ≤ Real.log (2 * d * n / δ) := Real.log_nonneg (by linarith)
  refine ⟨lt_min (by linarith) hpos, (min_le_left _ _).trans (by linarith), ?_⟩
  rcases min_choice (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) with h | h <;> rw [h]
  · have e : 1 / (δ / 3) ≤ 2 * (2 * d * n / δ) := by
      rw [hq, div_le_iff₀ (by linarith)]
      field_simp
      nlinarith
    have := Real.log_le_log (by positivity) e
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    have h2 := Real.log_two_lt_d9
    linarith
  · have e : 1 / (Real.exp (-14) / ((d : ℝ) * n) ^ 3) = Real.exp 14 * ((d : ℝ) * n) ^ 3 := by
      rw [one_div_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_comm]
    rw [e, Real.log_mul (Real.exp_pos _).ne' (pow_pos hDp 3).ne', Real.log_exp, Real.log_pow]
    have := Real.log_le_log hDp hDle
    push_cast
    linarith

theorem pgb_rho_le {d : ℕ} (hd : 1 ≤ d) (i : ℕ) :
    1 ≤ pgRhoStage d i ∧ pgRhoStage d i ≤ 26244 * (d : ℝ) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  induction i with
  | zero => simp only [pgRhoStage]; constructor <;> nlinarith
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [pgRhoStage]
    have hl0 : Real.log 2 ≤ Real.log (1 + pgRhoStage d i) := Real.log_le_log (by norm_num) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlu : Real.log (1 + pgRhoStage d i) ≤ 26244 * (d : ℝ) ^ 2 := by
      have := pgb_log_le_self (x := 1 + pgRhoStage d i) (by linarith)
      have := Real.log_le_sub_one_of_pos (x := 1 + pgRhoStage d i) (by linarith)
      linarith
    have hs1 : 1 / 162 ≤ Real.sqrt (Real.log (1 + pgRhoStage d i)) := by
      rw [Real.le_sqrt (by norm_num)] <;> nlinarith
    have hs2 : Real.sqrt (Real.log (1 + pgRhoStage d i)) ≤ 162 * d := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    constructor <;> nlinarith

theorem pgb_Jb_le (hB : PgBisectSteps) {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (h1 : 1 ≤ ρ)
    (h2 : ρ ≤ 26244 * (d : ℝ) ^ 2) : (pgJb d ρ : ℝ) ≤ 2 ^ 20 * (d : ℝ) ^ 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := hB d ρ hd' h1
  have e1 := pgb_logb_le hd'
  have e2 := pgb_logb_le h1
  have e3 := pgb_log_le_self (x := (d : ℝ)) (by linarith)
  have e4 := pgb_log_le_self (x := ρ) (by linarith)
  unfold pgJb
  refine pgb_ceil_le ?_ (by positivity)
  nlinarith

theorem pgb_Ns_le (hN : PgNSize) {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (h1 : 1 ≤ ρ)
    (h2 : ρ ≤ 26244 * (d : ℝ) ^ 2) : (pgNs d ρ : ℝ) ≤ 1.8e11 * 26244 ^ 9 * (d : ℝ) ^ 28 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := hN d ρ hd' h1
  have hl0 : 0 ≤ Real.log (1 + ρ) := Real.log_nonneg (by linarith)
  have hl : Real.log (1 + ρ) ≤ ρ := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ρ) (by linarith); linarith
  have h3 : Real.log (1 + ρ) ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hl0 hl 3
  have h9 : ρ ^ 9 ≤ (26244 * (d : ℝ) ^ 2) ^ 9 := pow_le_pow_left₀ (by linarith) h2 9
  unfold pgNs
  refine pgb_ceil_le ?_ (by positivity)
  calc pgNreal d ρ + 1 ≤ 1.8e11 * (d : ℝ) ^ 10 * ρ ^ 6 * Real.log (1 + ρ) ^ 3 := hb
    _ ≤ 1.8e11 * (d : ℝ) ^ 10 * ρ ^ 6 * ρ ^ 3 := by gcongr
    _ = 1.8e11 * (d : ℝ) ^ 10 * ρ ^ 9 := by ring
    _ ≤ 1.8e11 * (d : ℝ) ^ 10 * (26244 * (d : ℝ) ^ 2) ^ 9 := by gcongr
    _ = 1.8e11 * 26244 ^ 9 * (d : ℝ) ^ 28 := by ring

theorem pgb_NT_le (hNT : PgNTSize) {d : ℕ} {ρ : ℝ} (hd : 1 ≤ d) (h1 : 1 ≤ ρ)
    (h2 : ρ ≤ 26244 * (d : ℝ) ^ 2) : (pgNT d ρ : ℝ) ≤ 3.7e6 * 26244 ^ 3 * (d : ℝ) ^ 11 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb := hNT d ρ hd' h1
  have hl : Real.log (1 + ρ) ≤ ρ := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ρ) (by linarith); linarith
  have h3 : ρ ^ 3 ≤ (26244 * (d : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
  unfold pgNT
  refine pgb_ceil_le ?_ (by positivity)
  calc pgNTreal d ρ + 1 ≤ 3.7e6 * (d : ℝ) ^ 5 * ρ ^ 2 * Real.log (1 + ρ) := hb
    _ ≤ 3.7e6 * (d : ℝ) ^ 5 * ρ ^ 2 * ρ := by gcongr
    _ = 3.7e6 * (d : ℝ) ^ 5 * ρ ^ 3 := by ring
    _ ≤ 3.7e6 * (d : ℝ) ^ 5 * (26244 * (d : ℝ) ^ 2) ^ 3 := by gcongr
    _ = 3.7e6 * 26244 ^ 3 * (d : ℝ) ^ 11 := by ring

theorem pgb_Jr_le {δ₁ : ℝ} {m : ℕ} (h0 : 0 < δ₁) (h1 : δ₁ ≤ 1) (hm : 1 ≤ m) :
    1 ≤ pgJr (δ₁ / m) ∧ (pgJr (δ₁ / m) : ℝ) ≤ 2 * (2 + m + Real.log (1 / δ₁)) + 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have e : 4 / (δ₁ / m) = 4 * (m * (1 / δ₁)) := by field_simp
  have hge : 4 ≤ 4 / (δ₁ / m) := by
    rw [e]; have : 1 ≤ 1 / δ₁ := by rw [le_div_iff₀ h0]; linarith
    nlinarith
  have hlb := pgb_logb_le (x := 4 / (δ₁ / m)) (by linarith)
  have hlog : Real.log (4 / (δ₁ / m)) = Real.log 4 + (Real.log m + Real.log (1 / δ₁)) := by
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hlm := Real.log_le_sub_one_of_pos (x := (m : ℝ)) (by linarith)
  constructor
  · unfold pgJr
    rw [Nat.one_le_ceil_iff]
    exact Real.logb_pos (by norm_num) (by linarith)
  · unfold pgJr
    refine pgb_ceil_le ?_ ?_
    · rw [hlog, h4] at hlb; linarith
    · have := Real.log_nonneg (show 1 ≤ 1 / δ₁ by rw [le_div_iff₀ h0]; linarith); linarith

theorem pgb_MT_le {δ₁ : ℝ} {m : ℕ} (h0 : 0 < δ₁) (h1 : δ₁ ≤ 1) (hm : 1 ≤ m) :
    (pgMT (δ₁ / m) : ℝ) ≤ 8 * (1 + pgJr (δ₁ / m) + m + Real.log (1 / δ₁)) + 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hJ : (1 : ℝ) ≤ pgJr (δ₁ / m) := by exact_mod_cast (pgb_Jr_le h0 h1 hm).1
  have e : 2 * (pgJr (δ₁ / m) : ℝ) / (δ₁ / m) = 2 * ((pgJr (δ₁ / m) : ℝ) * ((m : ℝ) * (1 / δ₁))) := by
    field_simp
  have hlog : Real.log (2 * (pgJr (δ₁ / m) : ℝ) / (δ₁ / m)) =
      Real.log 2 + (Real.log (pgJr (δ₁ / m) : ℝ) + (Real.log m + Real.log (1 / δ₁))) := by
    rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hl2 := Real.log_two_lt_d9
  have hlJ := Real.log_le_sub_one_of_pos (x := (pgJr (δ₁ / m) : ℝ)) (by linarith)
  have hlm := Real.log_le_sub_one_of_pos (x := (m : ℝ)) (by linarith)
  have hl1 := Real.log_nonneg (show 1 ≤ 1 / δ₁ by rw [le_div_iff₀ h0]; linarith)
  unfold pgMT
  refine pgb_ceil_le ?_ (by linarith)
  rw [hlog]; linarith

/-! ## Polynomial bounds by a power of one variable -/

/-- `f ≤ c y^k`. -/
def PB (y f c k : ℕ) : Prop := f ≤ c * y ^ k

theorem PB.var {y v : ℕ} (h : v ≤ y) : PB y v 1 1 := by simpa [PB] using h

theorem PB.const (y c : ℕ) : PB y c c 0 := by simp [PB]

theorem PB.add {y a b c1 c2 k1 k2 : ℕ} (hy : 1 ≤ y) (ha : PB y a c1 k1) (hb : PB y b c2 k2) :
    PB y (a + b) (c1 + c2) (max k1 k2) := by
  unfold PB at *
  have e1 : y ^ k1 ≤ y ^ max k1 k2 := Nat.pow_le_pow_right hy (le_max_left _ _)
  have e2 : y ^ k2 ≤ y ^ max k1 k2 := Nat.pow_le_pow_right hy (le_max_right _ _)
  calc a + b ≤ c1 * y ^ k1 + c2 * y ^ k2 := Nat.add_le_add ha hb
    _ ≤ c1 * y ^ max k1 k2 + c2 * y ^ max k1 k2 := Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * y ^ max k1 k2 := by ring

theorem PB.mul {y a b c1 c2 k1 k2 : ℕ} (ha : PB y a c1 k1) (hb : PB y b c2 k2) :
    PB y (a * b) (c1 * c2) (k1 + k2) := by
  unfold PB at *
  calc a * b ≤ (c1 * y ^ k1) * (c2 * y ^ k2) := Nat.mul_le_mul ha hb
    _ = (c1 * c2) * y ^ (k1 + k2) := by ring

theorem PB.mono {y f c c' k k' : ℕ} (hy : 1 ≤ y) (h : PB y f c k) (hc : c ≤ c') (hk : k ≤ k') : PB y f c' k' :=
  h.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hy hk))

macro "pb_tac" hy:term : tactic =>
  `(tactic| repeat (first
    | with_reducible apply PB.add $hy
    | with_reducible apply PB.mul
    | (apply PB.var; assumption)
    | with_reducible apply PB.const))

macro "pb_tac2" hy:term:max hS:term:max : tactic =>
  `(tactic| repeat (first
    | with_reducible apply PB.add $hy
    | with_reducible apply PB.mul
    | (apply PB.var; assumption)
    | exact $hS
    | with_reducible apply PB.const))

/-- The step count of the code of PG: the caps `kCaps`, the setup, and `m` stages of `S` steps each. -/
def kPGpoly (d m0 J mT m S : ℕ) : ℕ :=
  kCaps d m0 J mT + (1 + (1 + (d * 5 + 3 + (d * d * 5 + 3 + (d * 7 + 4 + (1 + (1 + (m * (S + 3) + 3))))))))


theorem df2oPar_δ1 (d n : ℕ) (δ : ℝ) :
    (df2oPar d n δ).δ1 = min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3) := rfl

end AdversarialBco.Poly.PG
