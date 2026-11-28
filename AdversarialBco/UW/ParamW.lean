/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgRec
public import AdversarialBco.UW.ParamT4U
public import AdversarialBco.Unified.BudEnc

@[expose] public section

/-!
# Lemma PARAM-W (ii), (iv): `SchedUW` for BL-OW

Lemma PARAM-W, in the case of the assembly `ε(u_δ) ≤ 1/8` (`RunCaseUW`), for the program without the cap `u_cap`
(UW/ProgPure.lean): the reference at PARAM-W's values
`(u', b0, y0, δ_c)` is in its regime `RegimeW`, and `u_δ ≤ u' ≤ u(k_δ + 1)`.

The leaves are Theorem U's: the logarithm enclosures `|lnQ_q N - ln N| ≤ lnErr_q N ≤ 2^{-p-16}` at Theorem U's working
bits `q` (`lnQ_err`, `BudK.lnErr_le`, here at `N = N_0` and `N = 2`), the roots `sqrtDn`, `sqrtUp`, the roundings
`up_p`, and `2^{160} N^{10} d^{16} 2^{-p} ≤ 1` (`BudK.gen_u`, `N = N_e(k_δ)`). The arithmetic is on plain reals:
`u_bracket` (the scaling), `iota_bracket` (`ι⁺` within a relative `16·2^{-p}` above `1/ε(u')`).
-/

namespace AdversarialBco.UW.BLOW

open AdversarialBco AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (lnQ lnErr sqrtDn sqrtUp up)
open AdversarialBco.Bit.PieceA (lnQ_err sqrtDn_le_sqrt sqrt_le_sqrtDn_add one_le_sqrtDn sqrt_le_sqrtUp sqrtUp_le
  le_upR upR_le)

/-! ## The arithmetic on plain reals -/

/-- **The scaling's bracket** (Lemma PARAM-W (ii) without the cap): `u_δ ≤ u' ≤ u(k_δ + 1)` from the enclosures
`Λ_0 - 2e ≤ L_00 ≤ Λ_0`, `A ≤ l_2 ≤ A + 2 e_2` (`A = ln 2`) and `u' ∈ [x, x + 2^{-p}]`, `x = 1 + k l_2/(7 d L_00)`. -/
theorem u_bracket (d k Λ0 A e e2 tp lf0 l2 u : ℝ) (hd : 1 ≤ d) (hk : 0 ≤ k) (hΛ : 1 ≤ Λ0) (hA0 : 0 ≤ A)
    (hA1 : A ≤ 1) (he : 0 ≤ e) (he2 : 0 ≤ e2) (htp : 0 ≤ tp) (he4 : 4 * e ≤ Λ0) (hlf0 : Λ0 - 2 * e ≤ lf0)
    (hlf0' : lf0 ≤ Λ0) (hl2 : A ≤ l2) (hl2' : l2 ≤ A + 2 * e2) (hu : 1 + k * l2 / (7 * d * lf0) ≤ u)
    (hu' : u ≤ 1 + k * l2 / (7 * d * lf0) + tp) (hsm : 2 * k * e2 + 7 * tp * d * Λ0 + 2 * (k + 1) * e ≤ A) :
    1 + k * A / (7 * d * Λ0) ≤ u ∧ u ≤ 1 + (k + 1) * A / (7 * d * Λ0) := by
  have hlf0pos : 0 < lf0 := by linarith
  have hD : 0 < 7 * d * lf0 := by positivity
  have hD' : 0 < 7 * d * Λ0 := by positivity
  constructor
  · refine le_trans ?_ hu
    have : k * A / (7 * d * Λ0) ≤ k * l2 / (7 * d * lf0) :=
      div_le_div₀ (by nlinarith) (mul_le_mul_of_nonneg_left hl2 hk) hD
        (mul_le_mul_of_nonneg_left hlf0' (by positivity))
    linarith
  · refine le_trans hu' ?_
    have key : (k * l2 + 7 * tp * d * lf0) * Λ0 ≤ (k + 1) * A * lf0 := by
      have f1 : k * l2 * Λ0 ≤ k * (A + 2 * e2) * Λ0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2' hk) (by linarith)
      have f2 : 7 * tp * d * lf0 * Λ0 ≤ 7 * tp * d * Λ0 * Λ0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlf0' (by positivity)) (by linarith)
      have f3 : (k + 1) * A * (Λ0 - 2 * e) ≤ (k + 1) * A * lf0 :=
        mul_le_mul_of_nonneg_left hlf0 (by positivity)
      have f4 : (k + 1) * A * e ≤ (k + 1) * e * Λ0 := by
        have : A * e ≤ e * Λ0 := by nlinarith
        have hk1 : 0 ≤ k + 1 := by linarith
        nlinarith
      have f5 : (2 * k * e2 + 7 * tp * d * Λ0 + 2 * (k + 1) * e) * Λ0 ≤ A * Λ0 :=
        mul_le_mul_of_nonneg_right hsm (by linarith)
      nlinarith
    have e1 : k * l2 / (7 * d * lf0) + tp = (k * l2 + 7 * tp * d * lf0) / (7 * d * lf0) := by
      field_simp
    have h2 : (k * l2 + 7 * tp * d * lf0) / (7 * d * lf0) ≤ (k + 1) * A / (7 * d * Λ0) := by
      rw [div_le_div_iff₀ hD hD']
      calc (k * l2 + 7 * tp * d * lf0) * (7 * d * Λ0) = 7 * d * ((k * l2 + 7 * tp * d * lf0) * Λ0) := by ring
        _ ≤ 7 * d * ((k + 1) * A * lf0) := by gcongr
        _ = (k + 1) * A * (7 * d * lf0) := by ring
    linarith

/-- **`ι⁺` against `1/ε(u')`** (Lemma PARAM-W (iv), its relative error): with `r_n, r_d, r_u` the floor roots of
`n, d, u'` at the step `q2 = 2^{-q} ≤ tp`, `L0 = 36 L_00 ∈ [L_f (1 - tp), L_f]`, the quotient
`I0 = (r_n + q2)/(14500 d r_d L0^5 r_u)` lies between `1/ε(u') = n^{1/2}/(14500 d^{3/2} L_f^5 u'^{1/2})` and
`(1 + 16 tp)/ε(u')`. -/
theorem iota_bracket (n d u Lf rn rd ru L0 tp q2 : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hu : 1 ≤ u) (hLf : 0 < Lf)
    (htp : 0 ≤ tp) (htp1 : tp ≤ 1 / 100) (hq2 : 0 ≤ q2) (hq2' : q2 ≤ tp) (hrn : rn ≤ Real.sqrt n)
    (hrn' : Real.sqrt n ≤ rn + q2) (hrd : rd ≤ Real.sqrt d) (hrd' : Real.sqrt d ≤ rd + q2) (hru : ru ≤ Real.sqrt u)
    (hru' : Real.sqrt u ≤ ru + q2) (hL0 : L0 ≤ Lf) (hL0' : Lf * (1 - tp) ≤ L0) :
    Real.sqrt n / (14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u) ≤
        (rn + q2) / (14500 * d * rd * L0 ^ 5 * ru) ∧
      (rn + q2) / (14500 * d * rd * L0 ^ 5 * ru) ≤
        Real.sqrt n / (14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u) * (1 + 16 * tp) := by
  have hsn : 1 ≤ Real.sqrt n := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn
  have hsd : 1 ≤ Real.sqrt d := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hd
  have hsu : 1 ≤ Real.sqrt u := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hu
  have h1tp : 0 < 1 - tp := by linarith
  have hrd1 : Real.sqrt d * (1 - tp) ≤ rd := by nlinarith
  have hru1 : Real.sqrt u * (1 - tp) ≤ ru := by nlinarith
  have hrd0 : 0 < rd := lt_of_lt_of_le (by positivity) hrd1
  have hru0 : 0 < ru := lt_of_lt_of_le (by positivity) hru1
  have hL00 : 0 < L0 := lt_of_lt_of_le (by positivity) hL0'
  have hd0 : 0 < d := by linarith
  set DR := 14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u with hDR
  set DM := 14500 * d * rd * L0 ^ 5 * ru with hDM
  have hDR0 : 0 < DR := by positivity
  have hDM0 : 0 < DM := by positivity
  have hDM : DM ≤ DR := by
    rw [hDM, hDR]
    gcongr
  have hDM' : DR * (1 - tp) ^ 7 ≤ DM := by
    have h5 : (Lf * (1 - tp)) ^ 5 ≤ L0 ^ 5 := pow_le_pow_left₀ (by positivity) hL0' 5
    calc DR * (1 - tp) ^ 7 = 14500 * d * (Real.sqrt d * (1 - tp)) * (Lf * (1 - tp)) ^ 5 * (Real.sqrt u * (1 - tp)) := by
          rw [hDR]; ring
      _ ≤ 14500 * d * rd * L0 ^ 5 * ru := by gcongr
  constructor
  · exact div_le_div₀ (le_trans (Real.sqrt_nonneg _) hrn') hrn' hDM0 hDM
  · have hnum : rn + q2 ≤ Real.sqrt n * (1 + tp) := by nlinarith
    have hpow : 1 - 7 * tp ≤ (1 - tp) ^ 7 := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -tp by linarith) 7
      push_cast at this
      linarith
    have hfac : 1 + tp ≤ (1 + 16 * tp) * (1 - tp) ^ 7 := by
      have h7 : 0 ≤ 1 - 7 * tp := by linarith
      calc 1 + tp ≤ (1 + 16 * tp) * (1 - 7 * tp) := by nlinarith
        _ ≤ (1 + 16 * tp) * (1 - tp) ^ 7 := by gcongr
    rw [div_le_iff₀ hDM0]
    calc rn + q2 ≤ Real.sqrt n * (1 + tp) := hnum
      _ ≤ Real.sqrt n * ((1 + 16 * tp) * (1 - tp) ^ 7) := by gcongr
      _ = Real.sqrt n / DR * (1 + 16 * tp) * (DR * (1 - tp) ^ 7) := by field_simp
      _ ≤ Real.sqrt n / DR * (1 + 16 * tp) * DM := by gcongr

/-! ## The leaves at the input -/

section Leaves

variable {d n : ℕ} {δ : ℚ}

theorem n0O_le (d n k : ℕ) : n0O d n ≤ NeO d n k := by
  unfold n0O NeO
  have : 2 ^ (17 + 0) ≤ 2 ^ (17 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  gcongr

theorem lam0_eq (d n : ℕ) : lam0 d n = Real.log (n0O d n : ℝ) := rfl

/-- The working bits are at least the precision. -/
theorem p_le_q (d n : ℕ) (δ : ℚ) : (parO d n δ).p ≤ (parO d n δ).q := by
  rw [parO_q]; omega

/-- `tp = 2^{-p}`, and `2^{160} N^{10} d^{16} tp ≤ 1` at `N = N_e(k_δ)`. -/
theorem tp_small (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (NeO d n (kDel δ) : ℝ) * d * (1 / 2 ^ (parO d n δ).p) ≤ 1 / 2 ^ 160 := by
  have h := Unified.BudK.gen_u (NeO d n (kDel δ)) d
  have hp : (parO d n δ).p = 10 * (NeO d n (kDel δ)).size + 16 * d.size + 160 := rfl
  rw [hp]
  set N : ℝ := (NeO d n (kDel δ) : ℝ)
  set t : ℝ := 1 / 2 ^ (10 * (NeO d n (kDel δ)).size + 16 * d.size + 160)
  have hN : 1 ≤ N := by
    show (1 : ℝ) ≤ ((NeO d n (kDel δ) : ℕ) : ℝ); exact_mod_cast Unified.BudK.NeO_pos d n (kDel δ) hd hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : 0 ≤ t := by positivity
  have hN10 : N ≤ N ^ 10 := le_self_pow₀ hN (by norm_num)
  have hd16 : (d : ℝ) ≤ (d : ℝ) ^ 16 := le_self_pow₀ hd' (by norm_num)
  have h1 : N * d * t ≤ N ^ 10 * (d : ℝ) ^ 16 * t := by gcongr
  rw [le_div_iff₀ (by positivity)]
  calc N * d * t * 2 ^ 160 ≤ N ^ 10 * (d : ℝ) ^ 16 * t * 2 ^ 160 := by gcongr
    _ = 2 ^ 160 * N ^ 10 * (d : ℝ) ^ 16 * t := by ring
    _ ≤ 1 := h

/-- The logarithm enclosures: `|lnQ_q N - ln N| ≤ lnErr_q N ≤ 2^{-p-16}` for `N ≤ N_e(k_δ)`. -/
theorem ln_enc (hd : 1 ≤ d) (hn : 1 ≤ n) (N : ℕ) (hN1 : 1 ≤ N) (hN : N ≤ NeO d n (kDel δ)) :
    |((lnQ (parO d n δ).q N : ℚ) : ℝ) - Real.log N| ≤ ((lnErr (parO d n δ).q N : ℚ) : ℝ) ∧
      ((lnErr (parO d n δ).q N : ℚ) : ℝ) ≤ 1 / 2 ^ (parO d n δ).p / 2 ^ 16 := by
  have hq : 1 ≤ (parO d n δ).q := by rw [parO_q]; omega
  refine ⟨lnQ_err _ N hq hN1, ?_⟩
  exact Unified.BudK.lnErr_le d n (kDel δ) N hd hn (Nat.size_le_size hN)

end Leaves

/-! ## Lemma PARAM-W -/

set_option maxHeartbeats 1000000 in
/-- **Lemma PARAM-W (ii), (iv)** for BL-OW, in the case: the reference at PARAM-W's values is in its regime, and
`u_δ ≤ u' ≤ u(k_δ + 1)`. -/
theorem schedW (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hcase : RunCaseUW d n δ) :
    RegimeW d n (refW d n δ) ∧ uF d n (kDel δ) ≤ (uOW d n δ : ℝ) ∧ (uOW d n δ : ℝ) ≤ uF d n (kDel δ + 1) := by
  set k := kDel δ with hkdef
  set P := parO d n δ with hPdef
  set tp : ℝ := 1 / 2 ^ P.p with htpdef
  set q2 : ℝ := 1 / 2 ^ P.q with hq2def
  set Λ0 := lam0 d n with hΛdef
  set A := Real.log 2 with hAdef
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by linarith
  have htp0 : 0 ≤ tp := by positivity
  have hq20 : 0 ≤ q2 := by positivity
  have hq2tp : q2 ≤ tp := by
    rw [hq2def, htpdef]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (p_le_q d n δ))
  -- the sizes: `N_0 ≤ N`, `k ≤ N`, `n ≤ N`, `Λ_0 ≤ N`, `N d tp ≤ 2^{-160}`
  set N : ℝ := (NeO d n k : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    show (1 : ℝ) ≤ ((NeO d n k : ℕ) : ℝ); exact_mod_cast Unified.BudK.NeO_pos d n k hd hn
  have hNtp : N * d * tp ≤ 1 / 2 ^ 160 := tp_small hd hn
  have hN0N : (n0O d n : ℝ) ≤ N := by
    show ((n0O d n : ℕ) : ℝ) ≤ ((NeO d n k : ℕ) : ℝ); exact_mod_cast n0O_le d n k
  have htp1 : tp ≤ 1 := by
    rw [htpdef, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hN01 : (1 : ℝ) ≤ (n0O d n : ℝ) := by exact_mod_cast Unified.BudK.NeO_pos d n 0 hd hn
  have hkN : (k : ℝ) ≤ N := by
    have h1 : (2 : ℝ) ^ k ≤ N := by
      rw [hNdef, Unified.BudK.NeO_cast]
      have : (1 : ℝ) ≤ Bit.PieceA.Ne d n := Unified.BudK.Ne0_pos d n hd hn
      nlinarith [show (0 : ℝ) < 2 ^ k by positivity]
    have h2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    linarith
  have hnN : (n : ℝ) ≤ N := by
    have : n ≤ n0O d n := by
      unfold n0O NeO
      have h4 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
      have : 1 ≤ 15 * 2 ^ (17 + 0) * d ^ 3 := by
        have h3 := Nat.one_le_pow 3 d hd
        have e15 : (15 * 2 ^ (17 + 0) : ℕ) = 1966080 := by norm_num
        rw [e15]; omega
      nlinarith
    exact le_trans (by exact_mod_cast this) hN0N
  have hΛN : Λ0 ≤ N := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n0O d n by linarith)
    rw [hΛdef, lam0_eq]; linarith
  -- the case: `L_f ≥ 17467`, so `Λ_0 ≥ 485`
  have hA0 : 0 < A := Real.log_pos (by norm_num)
  have hA1 : A < 1 := by have := Real.log_two_lt_d9; linarith
  have hΛ0 : 0 ≤ Λ0 := Real.log_nonneg hN01
  have huδ : 1 ≤ uF d n k := by
    unfold uF
    have : 0 ≤ (k : ℝ) * Real.log 2 / (7 * d * lam0 d n) := by positivity
    linarith
  have hcase' : (parW d n (uF d n k)).eps ≤ 1 / 4 := le_trans hcase (by norm_num)
  have hLf : 17467 ≤ Bit.PieceA.Le d n := regW_Le hd hn huδ hcase'
  have hLfΛ : Bit.PieceA.Le d n = 36 * Λ0 := rfl
  have hΛ485 : 485 ≤ Λ0 := by linarith
  -- the logarithm of `N_0`
  obtain ⟨hL, he⟩ := ln_enc (δ := δ) hd hn (n0O d n) (by exact_mod_cast hN01) (n0O_le d n k)
  set L : ℝ := ((lnQ P.q (n0O d n) : ℚ) : ℝ) with hLdef
  set e : ℝ := ((lnErr P.q (n0O d n) : ℚ) : ℝ) with hedef
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) hL
  rw [← lam0_eq] at hL
  have hLlo := (abs_le.1 hL).1
  have hLhi := (abs_le.1 hL).2
  have hetp : e ≤ tp := by
    have : tp / 2 ^ 16 ≤ tp := div_le_self htp0 (by norm_num)
    linarith
  have hlf0 : ((lf0 d n δ : ℚ) : ℝ) = L - e := by simp [lf0, hLdef, hedef, hPdef]
  have hlf1 : ((lf1 d n δ : ℚ) : ℝ) = L + e := by simp [lf1, hLdef, hedef, hPdef]
  -- the logarithm of `2`
  obtain ⟨hL2, he2⟩ := ln_enc (δ := δ) hd hn 2 (by norm_num) (by
    have := Unified.BudK.NeO_ge d n (kDel δ) hd hn
    omega)
  set e2 : ℝ := ((lnErr P.q 2 : ℚ) : ℝ) with he2def
  have he20 : 0 ≤ e2 := le_trans (abs_nonneg _) hL2
  have he2tp : e2 ≤ tp := by
    have : tp / 2 ^ 16 ≤ tp := div_le_self htp0 (by norm_num)
    linarith
  have hl2 : ((l2O d n δ : ℚ) : ℝ) = ((lnQ P.q 2 : ℚ) : ℝ) + e2 := by simp [l2O, he2def, hPdef]
  have hl2lo : A ≤ ((l2O d n δ : ℚ) : ℝ) := by
    rw [hl2]; have := (abs_le.1 hL2).1; push_cast at this ⊢; rw [← hPdef, ← hAdef] at this; linarith
  have hl2hi : ((l2O d n δ : ℚ) : ℝ) ≤ A + 2 * e2 := by
    rw [hl2]; have := (abs_le.1 hL2).2; push_cast at this ⊢; rw [← hPdef, ← hAdef] at this; linarith
  -- the scaling
  have hsm : 2 * (k : ℝ) * e2 + 7 * tp * d * Λ0 + 2 * ((k : ℝ) + 1) * e ≤ A := by
    have h1 : 2 * (k : ℝ) * e2 ≤ 2 * N * d * tp := by
      have : (k : ℝ) * e2 ≤ N * tp := mul_le_mul hkN he2tp he20 (by linarith)
      have b : N * tp ≤ N * tp * d := le_mul_of_one_le_right (mul_nonneg (by linarith) htp0) hd'
      have c : N * tp * d = N * d * tp := by ring
      have e' : 2 * (k : ℝ) * e2 = 2 * ((k : ℝ) * e2) := by ring
      have f' : 2 * N * d * tp = 2 * (N * d * tp) := by ring
      rw [e', f']; linarith
    have h2 : 7 * tp * d * Λ0 ≤ 7 * N * d * tp := by
      have : tp * d * Λ0 ≤ tp * d * N := mul_le_mul_of_nonneg_left hΛN (by positivity)
      linarith
    have h3 : 2 * ((k : ℝ) + 1) * e ≤ 4 * N * d * tp := by
      have hk1 : (k : ℝ) + 1 ≤ 2 * N := by linarith
      have : ((k : ℝ) + 1) * e ≤ 2 * N * tp := mul_le_mul hk1 hetp he0 (by linarith)
      have b : N * tp ≤ N * tp * d := le_mul_of_one_le_right (mul_nonneg (by linarith) htp0) hd'
      have c : N * tp * d = N * d * tp := by ring
      have e' : 2 * ((k : ℝ) + 1) * e = 2 * (((k : ℝ) + 1) * e) := by ring
      have e'' : 2 * N * tp = 2 * (N * tp) := by ring
      have f' : 4 * N * d * tp = 4 * (N * d * tp) := by ring
      rw [e', f']; linarith
    have h4 : N * d * tp ≤ 1 / 2 ^ 160 := hNtp
    have h5 : (13 : ℝ) / 2 ^ 160 ≤ 1 / 2 := by norm_num
    have h6 : (1 : ℝ) / 2 < A := by have := Real.log_two_gt_d9; linarith
    linarith
  have hu_lo : 1 + (k : ℝ) * ((l2O d n δ : ℚ) : ℝ) / (7 * d * ((lf0 d n δ : ℚ) : ℝ)) ≤ (uOW d n δ : ℝ) := by
    have := le_upR P.p (1 + kDel δ * l2O d n δ / (7 * d * lf0 d n δ))
    push_cast at this
    exact this
  have hu_hi : (uOW d n δ : ℝ) ≤ 1 + (k : ℝ) * ((l2O d n δ : ℚ) : ℝ) / (7 * d * ((lf0 d n δ : ℚ) : ℝ)) + tp := by
    have := upR_le P.p (1 + kDel δ * l2O d n δ / (7 * d * lf0 d n δ))
    push_cast at this
    exact this
  obtain ⟨hU1, hU2⟩ := u_bracket d k Λ0 A e e2 tp ((lf0 d n δ : ℚ) : ℝ) ((l2O d n δ : ℚ) : ℝ) (uOW d n δ : ℝ) hd'
    (by positivity) (by linarith) hA0.le hA1.le he0 he20 htp0 (by linarith) (by rw [hlf0]; linarith)
    (by rw [hlf0]; linarith) hl2lo hl2hi hu_lo hu_hi hsm
  have huF : uF d n k = 1 + (k : ℝ) * A / (7 * d * Λ0) := rfl
  have huF1 : uF d n (k + 1) = 1 + ((k : ℝ) + 1) * A / (7 * d * Λ0) := by
    rw [show uF d n (k + 1) = 1 + ((k + 1 : ℕ) : ℝ) * Real.log 2 / (7 * d * lam0 d n) from rfl]
    push_cast; rfl
  have hUlo : uF d n k ≤ (uOW d n δ : ℝ) := by rw [huF]; exact hU1
  have hUhi : (uOW d n δ : ℝ) ≤ uF d n (k + 1) := by rw [huF1]; exact hU2
  have hu1 : (1 : ℝ) ≤ (uOW d n δ : ℝ) := le_trans huδ hUlo
  -- `ε(u') ≤ 1/4`
  have heps : (parW d n (uOW d n δ : ℝ)).eps ≤ 1 / 4 := by
    have hstep : ((k : ℝ) + 1) * A / (7 * d * Λ0) ≤ (k : ℝ) * A / (7 * d * Λ0) + 1 := by
      have : A / (7 * d * Λ0) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have e' : ((k : ℝ) + 1) * A / (7 * d * Λ0) = (k : ℝ) * A / (7 * d * Λ0) + A / (7 * d * Λ0) := by ring
      linarith
    have h2u : (uOW d n δ : ℝ) ≤ 4 * uF d n k := by rw [huF] at huδ ⊢; linarith
    have hsq : Real.sqrt (uOW d n δ : ℝ) ≤ 2 * Real.sqrt (uF d n k) := by
      calc Real.sqrt (uOW d n δ : ℝ) ≤ Real.sqrt (4 * uF d n k) := Real.sqrt_le_sqrt h2u
        _ = 2 * Real.sqrt (uF d n k) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hc := hcase
    unfold RunCaseUW at hc
    rw [parW_eps] at hc ⊢
    have he1 : 0 ≤ Bit.PieceA.eps d n := by
      unfold Bit.PieceA.eps; rw [hLfΛ]; positivity
    calc Bit.PieceA.eps d n * Real.sqrt (uOW d n δ : ℝ) ≤ Bit.PieceA.eps d n * (2 * Real.sqrt (uF d n k)) := by gcongr
      _ = 2 * (Bit.PieceA.eps d n * Real.sqrt (uF d n k)) := by ring
      _ ≤ 2 * (1 / 8) := by gcongr
      _ = 1 / 4 := by norm_num
  -- `1/ε(u')` and `ι⁺`
  set u' : ℝ := (uOW d n δ : ℝ) with hu'def
  set Lf := Bit.PieceA.Le d n with hLfdef
  have hEps : (parW d n u').eps = 14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u' / Real.sqrt n := by
    rw [parW_eps, Bit.PieceA.eps]; ring
  have hrn := sqrtDn_le_sqrt P.q (show (0 : ℚ) ≤ (n : ℚ) by positivity)
  have hrn' := sqrt_le_sqrtDn_add P.q (n : ℚ)
  have hrd := sqrtDn_le_sqrt P.q (show (0 : ℚ) ≤ (d : ℚ) by positivity)
  have hrd' := sqrt_le_sqrtDn_add P.q (d : ℚ)
  have hu0 : (0 : ℚ) ≤ uOW d n δ := by
    have h : (0 : ℝ) ≤ u' := by linarith
    rw [hu'def] at h
    exact_mod_cast h
  have hru := sqrtDn_le_sqrt P.q hu0
  have hru' := sqrt_le_sqrtDn_add P.q (uOW d n δ)
  push_cast at hrn hrn' hrd hrd' hru hru'
  have hq2e : (1 : ℝ) / 2 ^ P.q = q2 := rfl
  have hlf0R : Lf * (1 - tp) ≤ 36 * ((lf0 d n δ : ℚ) : ℝ) := by
    rw [hlf0, hLfΛ]
    have : 2 * e ≤ Λ0 * tp := by
      have h2 : 2 * tp ≤ Λ0 * tp := mul_le_mul_of_nonneg_right (by linarith) htp0
      linarith
    have e' : 36 * Λ0 * (1 - tp) = 36 * Λ0 - 36 * (Λ0 * tp) := by ring
    have hLlo' : -e ≤ L - Λ0 := hLlo
    rw [e']
    linarith
  have hlf0R' : 36 * ((lf0 d n δ : ℚ) : ℝ) ≤ Lf := by rw [hlf0, hLfΛ]; linarith
  have htp1 : tp ≤ 1 / 100 := by
    have : tp ≤ N * d * tp := le_mul_of_one_le_left htp0 (one_le_mul_of_one_le_of_one_le hN1 hd')
    have : (1 : ℝ) / 2 ^ 160 ≤ 1 / 100 := by norm_num
    linarith
  obtain ⟨hI1, hI2⟩ := iota_bracket n d u' Lf (sqrtDn P.q n : ℝ) (sqrtDn P.q d : ℝ) (ruOW d n δ : ℝ)
    (36 * ((lf0 d n δ : ℚ) : ℝ)) tp q2 hn' hd' hu1 (by linarith) htp0 htp1 hq20 hq2tp hrn hrn' hrd hrd' hru hru'
    hlf0R' hlf0R
  set iε : ℝ := Real.sqrt n / (14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u') with hiεdef
  have hiε : 18 / (parW d n u').eps = 18 * iε := by
    rw [hEps, hiεdef]; field_simp
  have hiεn : iε ≤ n := by
    have hsn : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hDen : 1 ≤ 14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u' := by
      have hsd : 1 ≤ Real.sqrt d := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hd'
      have hsu : 1 ≤ Real.sqrt u' := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hu1
      have hL5 : 1 ≤ Lf ^ 5 := one_le_pow₀ (by linarith)
      have : (1 : ℝ) ≤ 14500 * d := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
        _ ≤ 14500 * d * Real.sqrt d * Lf ^ 5 * Real.sqrt u' := by gcongr
    rw [hiεdef, div_le_iff₀ (by linarith)]
    nlinarith
  have hiota_lo : iε ≤ (iotaOW d n δ : ℝ) := by
    have h := le_upR P.p ((sqrtDn P.q n + 1 / 2 ^ P.q) /
      (14500 * d * sqrtDn P.q d * (36 * lf0 d n δ) ^ 5 * ruOW d n δ))
    push_cast at h
    rw [← hq2def] at h
    exact le_trans hI1 h
  have hiota_hi : (iotaOW d n δ : ℝ) ≤ iε * (1 + 16 * tp) + tp := by
    have h := upR_le P.p ((sqrtDn P.q n + 1 / 2 ^ P.q) /
      (14500 * d * sqrtDn P.q d * (36 * lf0 d n δ) ^ 5 * ruOW d n δ))
    push_cast at h
    rw [← hq2def, ← htpdef] at h
    exact le_trans h (by linarith)
  -- the root of `12 L_01`
  have hlf1R : Λ0 ≤ ((lf1 d n δ : ℚ) : ℝ) := by rw [hlf1]; linarith
  have hlf1R' : ((lf1 d n δ : ℚ) : ℝ) ≤ Λ0 + 2 * e := by rw [hlf1]; linarith
  have hsU := sqrt_le_sqrtUp P.q (12 * lf1 d n δ)
  have hsU' := sqrtUp_le P.q (12 * lf1 d n δ)
  push_cast at hsU hsU'
  have hsU2 : ((sqrtUp P.q (12 * lf1 d n δ) : ℚ) : ℝ) ≤ Real.sqrt (12 * ((lf1 d n δ : ℚ) : ℝ)) + 2 * q2 := by
    have e : (2 : ℝ) / 2 ^ P.q = 2 * q2 := by rw [hq2def]; ring
    linarith
  have hs12 : Real.sqrt (12 * Λ0) ≤ Real.sqrt (12 * ((lf1 d n δ : ℚ) : ℝ)) := Real.sqrt_le_sqrt (by linarith)
  have hs36 : Real.sqrt (12 * ((lf1 d n δ : ℚ) : ℝ)) ≤ Real.sqrt (36 * Λ0) := Real.sqrt_le_sqrt (by linarith)
  -- the sizes of the slack
  have hiεtp : iε * tp ≤ N * d * tp := by
    have : iε ≤ N * d := by
      have h1 : N ≤ N * d := le_mul_of_one_le_right (by linarith) hd'
      linarith
    exact mul_le_mul_of_nonneg_right this htp0
  have htpN : tp ≤ N * d * tp := le_mul_of_one_le_left htp0 (one_le_mul_of_one_le_of_one_le hN1 hd')
  have h2160 : (400 : ℝ) / 2 ^ 160 ≤ 1 / 2 := by norm_num
  -- the regime
  have hy0 := le_upR P.p (10 + 18 * iotaOW d n δ + 10 * sqrtUp P.q (12 * lf1 d n δ))
  have hy0' := upR_le P.p (10 + 18 * iotaOW d n δ + 10 * sqrtUp P.q (12 * lf1 d n δ))
  push_cast at hy0 hy0'
  rw [← htpdef] at hy0'
  have hb0 := le_upR P.p (2 * d + 2 + 36 * lf1 d n δ)
  have hb0' := upR_le P.p (2 * d + 2 + 36 * lf1 d n δ)
  push_cast at hb0 hb0'
  rw [← htpdef] at hb0'
  have hNk : N = 2 ^ k * (n0O d n : ℝ) := Unified.BudK.NeO_cast d n k
  have hdc : deltaC d n k = 1 / N := rfl
  refine ⟨⟨hd, hn, hu1, heps, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hUlo, hUhi⟩
  · -- `b0 ≥ 2d + 36 Λ_0 + 2`
    show 2 * (d : ℝ) + 36 * lam0 d n + 2 ≤ (b0OW d n δ : ℝ)
    try rw [← hΛdef]
    have : 2 * (d : ℝ) + 2 + 36 * ((lf1 d n δ : ℚ) : ℝ) ≤ (b0OW d n δ : ℝ) := hb0
    linarith
  · -- `b0 ≤ 2d + 36 Λ_0 + 3`
    show (b0OW d n δ : ℝ) ≤ 2 * (d : ℝ) + 36 * lam0 d n + 3
    try rw [← hΛdef]
    have : (b0OW d n δ : ℝ) ≤ 2 * (d : ℝ) + 2 + 36 * ((lf1 d n δ : ℚ) : ℝ) + tp := hb0'
    linarith
  · -- `y0 ≥ 10 + 18/ε + 10 (12 Λ_0)^{1/2}`
    show 10 + 18 / (parW d n u').eps + 10 * Real.sqrt (12 * lam0 d n) ≤ (y0OW d n δ : ℝ)
    try rw [← hΛdef]
    rw [hiε]
    have : 10 + 18 * (iotaOW d n δ : ℝ) + 10 * (sqrtUp P.q (12 * lf1 d n δ) : ℝ) ≤ (y0OW d n δ : ℝ) := hy0
    linarith
  · -- `y0 ≤ 11 + 18/ε + 10 (36 Λ_0)^{1/2}`
    show (y0OW d n δ : ℝ) ≤ 11 + 18 / (parW d n u').eps + 10 * Real.sqrt (36 * lam0 d n)
    try rw [← hΛdef]
    rw [hiε]
    have : (y0OW d n δ : ℝ) ≤ 10 + 18 * (iotaOW d n δ : ℝ) + 10 * (sqrtUp P.q (12 * lf1 d n δ) : ℝ) + tp := hy0'
    have hq2tp2 : q2 ≤ tp := hq2tp
    linarith [hiota_hi, hiεtp, hNtp, hsU2, hs36, h2160, htp1]
  · -- `δ_c > 0`
    show 0 < deltaC d n k
    rw [hdc]; positivity
  · -- `δ_c ≤ δ_0`
    show deltaC d n k ≤ 1 / (n0W d n : ℝ)
    rw [hdc]
    exact one_div_le_one_div_of_le (by have h1 : (1 : ℝ) ≤ (n0W d n : ℝ) := hN01; linarith) hN0N
  · -- `ln(1/δ_c) = k ln 2 + Λ_0 ≤ ℓ_c(u')`
    show Real.log (1 / deltaC d n k) ≤ lvl d n u'
    rw [hdc, one_div_one_div, hNk, Real.log_mul (by positivity) (ne_of_gt (by linarith)), Real.log_pow, ← lam0_eq]
    unfold lvl
    rw [← hΛdef]
    have hΛpos : 0 < Λ0 := by linarith
    have h1 : (k : ℝ) * A / (7 * d * Λ0) ≤ u' - 1 := by rw [huF] at hUlo; linarith
    have h2 : (k : ℝ) * A ≤ 7 * d * Λ0 * (u' - 1) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    linarith

/-- **`SchedUW` for BL-OW**, for every program text and cost constants. -/
theorem schedUW (P : List BitRAMO.InstrO) (C' : ℝ) (k : ℕ) : SchedUW (implW P C' k) :=
  fun d n δ hd hn _ _ hcase => schedW d n δ hd hn hcase

end AdversarialBco.UW.BLOW
