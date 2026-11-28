/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Regime
public import Mathlib
public import AdversarialBco.Bit.BLBasic

@[expose] public section

/-!
# Piece A: the leaves of Procedure PARAM

The leaves of PARAM against the reals: `lnQ` encloses `ln N` within `lnErr` (twice Lemma LOG, `gsm_LLq_err`),
`sqrtDn` and `sqrtUp` enclose the square root (steps 2 and 3); the roundings over `ℝ` (`rnd_errR`, `le_upR`,
`upR_le`, `dnR_le`, `sub_le_dnR`); and the bounds `2^20 d^3 ≤ N_e`, `4 d ≤ N_e` (`NeN_ge`).
-/

namespace AdversarialBco.Bit.PieceA

open AdversarialBco.Bit.BLP (po par lnQ lnErr sqrtDn sqrtUp rnd up dn)

open AdversarialBco.Bit.Asm (RunCase)

/-! ## The leaves -/

theorem lnQ_err (q N : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    |((lnQ q N : ℚ) : ℝ) - Real.log N| ≤ ((lnErr q N : ℚ) : ℝ) := by
  have hs : 1 ≤ N.size := Nat.size_pos.mpr hN
  have h1 := AdversarialBco.Bit.gsm_LLq_err 1 q 0 le_rfl hq (by norm_num)
  have h2 := AdversarialBco.Bit.gsm_LLq_err N.size q (N - 1) hs hq
    (by have := Nat.lt_size_self N; omega)
  have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by rw [Nat.cast_sub hN]; push_cast; ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hN1, Real.log_div hN0.ne' (by positivity), Real.log_pow] at h2
  simp only [Nat.cast_zero, zero_add, pow_one, one_div, Real.log_inv, Nat.cast_one, one_mul] at h1
  have hq0 : (0 : ℝ) < 2 ^ q := by positivity
  set A := (AdversarialBco.Bit.gsm_LLq 1 q 0 : ℝ) / 2 ^ q + -Real.log 2
  set B := (AdversarialBco.Bit.gsm_LLq N.size q (N - 1) : ℝ) / 2 ^ q + (Real.log N - N.size * Real.log 2)
  have hkey : ((lnQ q N : ℚ) : ℝ) - Real.log N = N.size * A - B := by
    simp only [A, B, lnQ]; push_cast; field_simp; ring
  have hE : ((lnErr q N : ℚ) : ℝ) = N.size * ((4 * q + 1) / 2 ^ q) + N.size * (4 * q + 1) / 2 ^ q := by
    simp only [lnErr]; push_cast; ring
  rw [hkey, hE]
  have hsz : (0 : ℝ) ≤ N.size := by positivity
  calc |N.size * A - B| ≤ |N.size * A| + |B| := abs_sub _ _
    _ = N.size * |A| + |B| := by rw [abs_mul, abs_of_nonneg hsz]
    _ ≤ _ := by gcongr

theorem sqrtDn_le_sqrt (k : ℕ) {x : ℚ} (hx : 0 ≤ x) : (sqrtDn k x : ℝ) ≤ Real.sqrt x := by
  have h := BLP.sqrtDn_sq_le k hx
  have h0 : (0 : ℝ) ≤ sqrtDn k x := by exact_mod_cast BLP.sqrtDn_nonneg k x
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

theorem sqrt_le_sqrtDn_add (k : ℕ) (x : ℚ) : Real.sqrt x ≤ (sqrtDn k x : ℝ) + 1 / 2 ^ k := by
  have h := BLP.lt_sqrtDn_succ_sq k x
  have h0 : (0 : ℝ) ≤ (sqrtDn k x : ℝ) + 1 / 2 ^ k := by
    have := BLP.sqrtDn_nonneg k x
    have : (0 : ℝ) ≤ sqrtDn k x := by exact_mod_cast this
    positivity
  have h' : ((x : ℚ) : ℝ) ≤ (((sqrtDn k x + 1 / 2 ^ k) ^ 2 : ℚ) : ℝ) := by exact_mod_cast h.le
  push_cast at h'
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt h'

theorem one_le_sqrtDn (k : ℕ) {x : ℚ} (hx : 1 ≤ x) : (1 : ℝ) ≤ sqrtDn k x := by
  unfold sqrtDn
  have h4 : (4 : ℚ) ^ k = ((2 ^ k : ℕ) : ℚ) * ((2 ^ k : ℕ) : ℚ) := by
    push_cast; rw [← mul_pow]; norm_num
  have hm : 2 ^ k * 2 ^ k ≤ ⌊x * 4 ^ k⌋₊ := by
    apply Nat.le_floor
    rw [h4]; push_cast
    nlinarith [show (0 : ℚ) < 2 ^ k * 2 ^ k by positivity]
  have hs : 2 ^ k ≤ Nat.sqrt ⌊x * 4 ^ k⌋₊ := Nat.le_sqrt.mpr hm
  have hs' : (2 : ℝ) ^ k ≤ (Nat.sqrt ⌊x * 4 ^ k⌋₊ : ℝ) := by exact_mod_cast hs
  push_cast
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem sqrt_le_sqrtUp (k : ℕ) (x : ℚ) : Real.sqrt x ≤ (sqrtUp k x : ℝ) := by
  have h := BLP.le_sqrtUp_sq k x
  have h0 : (0 : ℝ) ≤ sqrtUp k x := by unfold sqrtUp; push_cast; positivity
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

theorem sqrtUp_le (k : ℕ) (x : ℚ) : (sqrtUp k x : ℝ) ≤ Real.sqrt x + 2 / 2 ^ k := by
  unfold sqrtUp
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  push_cast
  rw [div_le_iff₀ hk]
  rcases le_or_gt 0 x with hx | hx
  · have hm1 : ((⌈x * 4 ^ k⌉₊ : ℕ) : ℝ) < (x : ℝ) * 4 ^ k + 1 := by
      have h1 := Nat.ceil_lt_add_one (show 0 ≤ x * 4 ^ k by positivity)
      have h2 : (((⌈x * 4 ^ k⌉₊ : ℕ) : ℚ) : ℝ) < ((x * 4 ^ k + 1 : ℚ) : ℝ) := by exact_mod_cast h1
      push_cast at h2; exact h2
    generalize ⌈x * 4 ^ k⌉₊ = m at hm1 ⊢
    have hs : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ m := by exact_mod_cast Nat.sqrt_le' m
    have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    have h4 : Real.sqrt ((x : ℝ) * 4 ^ k) = Real.sqrt x * 2 ^ k := by
      rw [Real.sqrt_mul hx', show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        Real.sqrt_sq hk.le]
    have hsx := Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) * 4 ^ k by positivity)
    have hsq0 := Real.sqrt_nonneg ((x : ℝ) * 4 ^ k)
    -- `Nat.sqrt m ≤ √(x 4^k) + 1`
    have hle : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt ((x : ℝ) * 4 ^ k) + 1 := by
      nlinarith [show (0 : ℝ) ≤ ((Nat.sqrt m : ℕ) : ℝ) by positivity]
    rw [h4] at hle
    have h2k : 2 / (2 : ℝ) ^ k * 2 ^ k = 2 := by field_simp
    nlinarith
  · have hm : ⌈x * 4 ^ k⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by
      have : (0 : ℚ) < 4 ^ k := by positivity
      nlinarith)
    rw [hm]
    simp only [Nat.sqrt_zero, CharP.cast_eq_zero, zero_add]
    have h2k : 2 / (2 : ℝ) ^ k * 2 ^ k = 2 := by field_simp
    nlinarith [Real.sqrt_nonneg (x : ℝ)]

/-! ## The roundings over `ℝ` -/

theorem rnd_errR (k : ℕ) (x : ℚ) : |((rnd k x : ℚ) : ℝ) - (x : ℝ)| ≤ (1 / 2 ^ k) / 2 := by
  have h := BLP.rnd_err k x
  have h' : ((|rnd k x - x| : ℚ) : ℝ) ≤ ((1 / 2 ^ (k + 1) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  rw [pow_succ] at h'
  linarith [show (1 : ℝ) / (2 ^ k * 2) = 1 / 2 ^ k / 2 by ring]

theorem le_upR (k : ℕ) (x : ℚ) : (x : ℝ) ≤ ((up k x : ℚ) : ℝ) := by exact_mod_cast BLP.le_up k x

theorem upR_le (k : ℕ) (x : ℚ) : ((up k x : ℚ) : ℝ) ≤ (x : ℝ) + 1 / 2 ^ k := by
  have h := (BLP.up_lt k x).le
  have h' : ((up k x : ℚ) : ℝ) ≤ ((x + 1 / 2 ^ k : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'; exact h'

theorem dnR_le (k : ℕ) (x : ℚ) : ((dn k x : ℚ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast BLP.dn_le k x

theorem sub_le_dnR (k : ℕ) (x : ℚ) : (x : ℝ) - 1 / 2 ^ k ≤ ((dn k x : ℚ) : ℝ) := by
  have h := (BLP.sub_lt_dn k x).le
  have h' : ((x - 1 / 2 ^ k : ℚ) : ℝ) ≤ ((dn k x : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'; exact h'

/-! ## The precisions of PARAM -/

theorem NeN_ge (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 2 ^ 20 * d ^ 3 ≤ NeN d n ∧ 4 * d ≤ NeN d n := by
  have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
  have h4 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
  have hd3 : d ≤ d ^ 3 := Nat.le_self_pow (by norm_num) d
  unfold NeN
  constructor
  · calc 2 ^ 20 * d ^ 3 ≤ 15 * 2 ^ 17 * d ^ 3 := by gcongr; norm_num
      _ = 15 * 2 ^ 17 * d ^ 3 * 1 := by ring
      _ ≤ 15 * 2 ^ 17 * d ^ 3 * n ^ 4 := by gcongr
  · calc 4 * d ≤ 15 * 2 ^ 17 * d ^ 3 := by nlinarith
      _ = 15 * 2 ^ 17 * d ^ 3 * 1 := by ring
      _ ≤ 15 * 2 ^ 17 * d ^ 3 * n ^ 4 := by gcongr

end AdversarialBco.Bit.PieceA
