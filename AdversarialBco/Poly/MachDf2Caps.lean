/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2AP
public import AdversarialBco.Poly.MachDf2Cost

@[expose] public section

/-!
# DF2-O as a program of VL

`df2oMachine`: the statement `Df2OMachine`. The caps `df2Cap1`, `df2Cap2` of the two calls of AP in a round
(`df2oMode_apRules`) are polynomial in `d n log(2dn/δ)` (`df2Caps_bound`): every input of the cap bound `kAPcap` of
AP is at most `10¹⁸ X¹⁴` with `X = 2dn/δ` (`capin_*`), so the constants `N`, `J`, `B` of ELL-cap and the count of
ELL-1 are `O(d² log X)` (`bars_le`), and `kAPcap` is a polynomial of degree `5` in them (`kAPcap_le_pow`).
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.Poly

/-! ## Real bounds on the inputs of the caps -/

theorem capCeil_le (x U : ℝ) (hU : 0 ≤ U) (h : x ≤ U) : (⌈x⌉₊ : ℝ) ≤ U + 1 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Nat.ceil_eq_zero.2 hx]; push_cast; linarith
  · linarith [Nat.ceil_lt_add_one hx.le]

theorem capTheta_ge (B Rb T W eb : ℝ) (hB : 1 ≤ B) (hRb0 : 0 < Rb) (hW : 0 ≤ W) (heb : 0 < eb)
    (hRb : Rb ≤ B) (hT : max T 1 ≤ B) (hRW : Rb + W ≤ B) (he : 1 / eb ≤ B) :
    1 / (3 * B ^ 4) ≤ min 1 (eb / (3 * (max T 1 * (Rb + W)) * Rb)) := by
  have hT1 : 1 ≤ max T 1 := le_max_right _ _
  have hB4 : 1 ≤ B ^ 4 := one_le_pow₀ hB
  refine le_min ?_ ?_
  · rw [div_le_one (by positivity)]; linarith
  · have hebB : 1 ≤ B * eb := by rw [div_le_iff₀ heb] at he; linarith
    have hp : max T 1 * (Rb + W) * Rb ≤ B * B * B :=
      mul_le_mul (mul_le_mul hT hRW (by positivity) (by positivity)) hRb (by positivity) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hebB (show 0 ≤ B ^ 3 by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem capYN_le (B Rb rb θ : ℝ) (hB : 1 ≤ B) (hrb : 0 < rb) (hθ : 1 / (3 * B ^ 4) ≤ θ) (hRb : Rb ≤ B)
    (hr : 1 / rb ≤ B) : 2 * Rb / (θ * rb) ≤ 6 * B ^ 6 := by
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have h1 : 1 ≤ 3 * B ^ 4 * θ := by rw [div_le_iff₀ (by positivity)] at hθ; linarith
  have h2 : 1 ≤ B * rb := by rw [div_le_iff₀ hrb] at hr; linarith
  have h3 : 1 ≤ (3 * B ^ 4 * θ) * (B * rb) := one_le_mul_of_one_le_of_one_le h1 h2
  have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * B by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem capYJ_le (B Rb rb θ d : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d) (hRb0 : 0 < Rb) (hrb : 0 < rb)
    (hθ : 1 / (3 * B ^ 4) ≤ θ) (hRb : Rb ≤ B) (hr : 1 / rb ≤ B) :
    576 * Rb ^ 2 * Real.sqrt d / (θ * rb ^ 2) ≤ 1728 * B ^ 8 * d := by
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have h1 : 1 ≤ 3 * B ^ 4 * θ := by rw [div_le_iff₀ (by positivity)] at hθ; linarith
  have h2 : 1 ≤ B * rb := by rw [div_le_iff₀ hrb] at hr; linarith
  have hsd : Real.sqrt d ≤ d := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have h4 : 1 ≤ (3 * B ^ 4 * θ) * (B * rb) ^ 2 := one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h2)
  have hRb2 : Rb ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hRb0.le hRb 2
  have h5 : Rb ^ 2 * Real.sqrt d ≤ B ^ 2 * d := mul_le_mul hRb2 hsd (Real.sqrt_nonneg _) (by positivity)
  have h6 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 576 * (B ^ 2 * d) by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem capYB_le (B Rb rb θ d : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d) (hRb0 : 0 < Rb) (hrb : 0 < rb)
    (hθ : 1 / (3 * B ^ 4) ≤ θ) (hRb : Rb ≤ B) (hr : 1 / rb ≤ B) :
    16588800 * Rb ^ 4 * Real.sqrt d / (θ ^ 2 * rb ^ 4) ≤ 149299200 * B ^ 16 * d := by
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have h1 : 1 ≤ 3 * B ^ 4 * θ := by rw [div_le_iff₀ (by positivity)] at hθ; linarith
  have h2 : 1 ≤ B * rb := by rw [div_le_iff₀ hrb] at hr; linarith
  have hsd : Real.sqrt d ≤ d := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have h4 : 1 ≤ (3 * B ^ 4 * θ) ^ 2 * (B * rb) ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1) (one_le_pow₀ h2)
  have hRb4 : Rb ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ hRb0.le hRb 4
  have h5 : Rb ^ 4 * Real.sqrt d ≤ B ^ 4 * d := mul_le_mul hRb4 hsd (Real.sqrt_nonneg _) (by positivity)
  have h6 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 16588800 * (B ^ 4 * d) by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem capYcnt_le (B Rb T W eb : ℝ) (hB : 1 ≤ B) (hRb0 : 0 < Rb) (hT0 : 0 < T) (hW : 0 ≤ W)
    (heb : 0 < eb) (hRb : Rb ≤ B) (hT : max T 1 ≤ B) (hRW : Rb + W ≤ B) (he : 1 / eb ≤ B) :
    2 * Rb * T * (Rb + W) / eb ≤ 2 * B ^ 4 := by
  have hTB : T ≤ B := (le_max_left T 1).trans hT
  have h2 : 1 ≤ B * eb := by rw [div_le_iff₀ heb] at he; linarith
  have hp : Rb * T * (Rb + W) ≤ B * B * B :=
    mul_le_mul (mul_le_mul hRb hTB hT0.le (by linarith)) hRW (by positivity) (by positivity)
  have h6 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ B ^ 3 by positivity)
  rw [div_le_iff₀ heb]
  nlinarith

theorem capin_R {X R : ℝ} (hX : 2 ≤ X) (hR : R ≤ 268 * X ^ 2) : R ≤ 10 ^ 18 * X ^ 14 := by
  have hX2 : X ^ 2 ≤ X ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have : 0 ≤ X ^ 14 := by positivity
  linarith

theorem capin_rb {X R δe sb : ℝ} (hX : 2 ≤ X) (hR1 : 1 ≤ R) (hR : R ≤ 268 * X ^ 2) (hδe0 : 0 < δe)
    (hδe : 1 / δe ≤ 10 ^ 5 * X ^ 4) (hsb0 : 0 < sb) (hsb : 1 / sb ≤ (R + 1) ^ 2 * (1 / δe) ^ 2) :
    1 / (sb / 2) ≤ 10 ^ 18 * X ^ 14 := by
  have hX1 : 1 ≤ X := by linarith
  have e1 : 1 / (sb / 2) = 2 * (1 / sb) := by field_simp
  have hXX : 1 ≤ X ^ 2 := one_le_pow₀ hX1
  have hR1' : R + 1 ≤ 269 * X ^ 2 := by linarith
  have hA : (R + 1) ^ 2 ≤ (269 * X ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hR1' 2
  have hBq : (1 / δe) ^ 2 ≤ (10 ^ 5 * X ^ 4) ^ 2 := pow_le_pow_left₀ (by positivity) hδe 2
  have hprod : (R + 1) ^ 2 * (1 / δe) ^ 2 ≤ (269 * X ^ 2) ^ 2 * (10 ^ 5 * X ^ 4) ^ 2 :=
    mul_le_mul hA hBq (by positivity) (by positivity)
  have hX12 : X ^ 12 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have : 0 ≤ X ^ 12 := by positivity
  rw [e1]
  nlinarith

theorem capin_T {X d δe : ℝ} (hX : 2 ≤ X) (hdX : d ≤ X / 2) (hδe0 : 0 < δe) (hδe : 1 / δe ≤ 10 ^ 5 * X ^ 4) :
    max (d / δe) 1 ≤ 10 ^ 18 * X ^ 14 := by
  have hX1 : 1 ≤ X := by linarith
  have h1 : d / δe ≤ (X / 2) * (10 ^ 5 * X ^ 4) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hdX hδe (by positivity) (by linarith)
  have hX5 : X ^ 5 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX14 : 1 ≤ X ^ 14 := one_le_pow₀ hX1
  refine max_le ?_ ?_ <;> nlinarith

theorem capin_W1 {X R δe : ℝ} (hX : 2 ≤ X) (hR1 : 1 ≤ R) (hR : R ≤ 268 * X ^ 2) (hδe0 : 0 < δe)
    (hδe : 1 / δe ≤ 10 ^ 5 * X ^ 4) : R + R / δe ^ 3 ≤ 10 ^ 18 * X ^ 14 := by
  have hX1 : 1 ≤ X := by linarith
  have h3 : (1 / δe) ^ 3 ≤ (10 ^ 5 * X ^ 4) ^ 3 := pow_le_pow_left₀ (by positivity) hδe 3
  have e : R / δe ^ 3 = R * (1 / δe) ^ 3 := by field_simp
  have h4 : R * (1 / δe) ^ 3 ≤ (268 * X ^ 2) * (10 ^ 5 * X ^ 4) ^ 3 :=
    mul_le_mul hR h3 (by positivity) (by positivity)
  have hX2 : X ^ 2 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have : 0 ≤ X ^ 14 := by positivity
  rw [e]
  nlinarith

theorem capin_W2 {X d n R δe eta Le : ℝ} (hX : 2 ≤ X) (hd : 1 ≤ d) (hn : 1 ≤ n) (hdX : d ≤ X / 2)
    (hdn : d * n ≤ X / 2) (hR : R ≤ 268 * X ^ 2) (hδe0 : 0 < δe) (hδe : 1 / δe ≤ 10 ^ 5 * X ^ 4)
    (heta : eta ≤ d) (hLe0 : 0 ≤ Le) (hLe : Le ≤ 36 / δe) :
    R + (R + eta * Real.sqrt (16 * d * n * Le / δe)) ≤ 10 ^ 18 * X ^ 14 := by
  have hX1 : 1 ≤ X := by linarith
  have hs0 : 0 ≤ 16 * d * n * Le / δe := by positivity
  have hLe' : Le ≤ 36 * (10 ^ 5 * X ^ 4) := by
    have : 36 / δe = 36 * (1 / δe) := by ring
    nlinarith
  have hs : 16 * d * n * Le / δe ≤ 288 * X * (10 ^ 5 * X ^ 4) ^ 2 := by
    have e : 16 * d * n * Le / δe = 16 * (d * n) * Le * (1 / δe) := by field_simp
    rw [e]
    calc 16 * (d * n) * Le * (1 / δe) ≤ 16 * (X / 2) * (36 * (10 ^ 5 * X ^ 4)) * (10 ^ 5 * X ^ 4) := by
          gcongr
      _ = 288 * X * (10 ^ 5 * X ^ 4) ^ 2 := by ring
  have hsq : Real.sqrt (16 * d * n * Le / δe) ≤ 1 + 16 * d * n * Le / δe :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have h1 : eta * Real.sqrt (16 * d * n * Le / δe) ≤ (X / 2) * (1 + 288 * X * (10 ^ 5 * X ^ 4) ^ 2) :=
    mul_le_mul (heta.trans hdX) (hsq.trans (by linarith)) (Real.sqrt_nonneg _) (by positivity)
  have hX2 : X ^ 2 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX10 : X ^ 10 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX' : X ≤ X ^ 14 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have : 0 ≤ X ^ 14 := by positivity
  nlinarith

theorem capin_e2 {X d n R δe : ℝ} (hX : 2 ≤ X) (hd : 1 ≤ d) (hn : 1 ≤ n) (hdX : d ≤ X / 2) (hnX : n ≤ X / 2)
    (hR1 : 1 ≤ R) (hR : R ≤ 268 * X ^ 2) (hδe0 : 0 < δe) (hδe : 1 / δe ≤ 10 ^ 5 * X ^ 4) :
    1 / (1 / (16 * n ^ 2 * max 1 (4 * R ^ 2 * (d / δe)))) ≤ 10 ^ 18 * X ^ 14 := by
  have hX1 : 1 ≤ X := by linarith
  rw [one_div_one_div]
  have hn2 : n ^ 2 ≤ (X / 2) ^ 2 := pow_le_pow_left₀ (by linarith) hnX 2
  have hR2 : R ^ 2 ≤ (268 * X ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hR 2
  have hdδ : d / δe ≤ (X / 2) * (10 ^ 5 * X ^ 4) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul hdX hδe (by positivity) (by linarith)
  have hm : max 1 (4 * R ^ 2 * (d / δe)) ≤ 1 + 4 * (268 * X ^ 2) ^ 2 * ((X / 2) * (10 ^ 5 * X ^ 4)) := by
    have h0 : 0 ≤ 4 * (268 * X ^ 2) ^ 2 * ((X / 2) * (10 ^ 5 * X ^ 4)) := by positivity
    refine max_le (by linarith) ?_
    have : 4 * R ^ 2 * (d / δe) ≤ 4 * (268 * X ^ 2) ^ 2 * ((X / 2) * (10 ^ 5 * X ^ 4)) := by
      gcongr
    linarith
  have hX2 : X ^ 2 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX11 : X ^ 11 ≤ X ^ 14 := pow_le_pow_right₀ hX1 (by norm_num)
  have : 0 ≤ X ^ 14 := by positivity
  calc 16 * n ^ 2 * max 1 (4 * R ^ 2 * (d / δe))
        ≤ 16 * (X / 2) ^ 2 * (1 + 4 * (268 * X ^ 2) ^ 2 * ((X / 2) * (10 ^ 5 * X ^ 4))) :=
          mul_le_mul (by linarith) hm (by positivity) (by positivity)
    _ ≤ 10 ^ 18 * X ^ 14 := by nlinarith

/-! ## The step bound of AP as a polynomial -/

/-- The steps of ELL-cap are at most `2535 M⁵` when `d, Kq, N, J, B ≤ M`. -/
theorem kCap_le_pow {d Kq N J B M : ℕ} (hM : 1 ≤ M) (hd : d ≤ M) (hK : Kq ≤ M) (hN : N ≤ M) (hJ : J ≤ M)
    (hB : B ≤ M) : AP.kCap d Kq N J B ≤ 2535 * M ^ 5 := by
  have h1 : AP.kCap d Kq N J B ≤ AP.kCap M M M M M := by
    unfold AP.kCap AP.kCons AP.kES AP.kESq AP.kSC AP.kST AP.kLC AP.kLF AP.kLB AP.kLH AP.kTail AP.kPL AP.kPT AP.kML
      AP.kMT AP.kEV AP.kGV AP.kInit AP.kFin AP.kS3 AP.kCut
    gcongr
  refine h1.trans ?_
  unfold AP.kCap AP.kCons AP.kES AP.kESq AP.kSC AP.kST AP.kLC AP.kLF AP.kLB AP.kLH AP.kTail AP.kPL AP.kPT AP.kML
    AP.kMT AP.kEV AP.kGV AP.kInit AP.kFin AP.kS3 AP.kCut
  have hs : M - 1 ≤ M := Nat.sub_le M 1
  generalize M - 1 = x at hs ⊢
  have p1 : M ≤ M ^ 5 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p2 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p3 : M ^ 3 ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p4 : M ^ 4 ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p0 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ hM
  ring_nf
  nlinarith

/-- The steps of ELL-1 are at most `77 M⁵` when `Kq, c ≤ M`. -/
theorem kOne_le_pow {Kq c M : ℕ} (hM : 1 ≤ M) (hK : Kq ≤ M) (hc : c ≤ M) : AP.kOne Kq c ≤ 77 * M ^ 5 := by
  have h1 : AP.kOne Kq c ≤ AP.kOne M M := by
    unfold AP.kOne AP.kOneA AP.kOneB AP.kOneC
    gcongr
  refine h1.trans ?_
  unfold AP.kOne AP.kOneA AP.kOneB AP.kOneC
  have p1 : M ≤ M ^ 5 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p2 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM (by norm_num)
  have p0 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ hM
  ring_nf
  nlinarith

/-- The cap bound of AP is at most `2536 M⁵` when `d`, `Kq` and the constants of ELL-cap and ELL-1 are at most `M`. -/
theorem kAPcap_le_pow {d Kq M : ℕ} {rb Rb T W eb : ℝ} (hM : 1 ≤ M) (hd : d ≤ M) (hK : Kq ≤ M)
    (hN : AP.nBar d rb Rb T W eb ≤ M) (hJ : AP.jBar d rb Rb T W eb ≤ M) (hB : AP.bBar d rb Rb T W eb ≤ M)
    (hc : AP.cntBar Rb T W eb ≤ M) : AP.kAPcap d Kq rb Rb T W eb ≤ 2536 * M ^ 5 := by
  unfold AP.kAPcap
  have p0 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ hM
  split_ifs
  · have := kOne_le_pow hM hK hc; omega
  · have := kCap_le_pow hM hd hK hN hJ hB; omega

/-- The constant of the logarithms of the caps of AP when its inputs are at most `c₀ X^m`. -/
noncomputable def capA (c0 : ℝ) (m : ℕ) : ℝ :=
  Real.log (149299200 * c0 ^ 16) / Real.log 2 + ((16 * m + 1 : ℕ) : ℝ)

theorem capA_nonneg {c0 : ℝ} (hc0 : 1 ≤ c0) (m : ℕ) : 0 ≤ capA c0 m := by
  unfold capA
  have h16 : 1 ≤ c0 ^ 16 := one_le_pow₀ hc0
  have : 0 ≤ Real.log (149299200 * c0 ^ 16) := Real.log_nonneg (by nlinarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem capA_log {c0 X y : ℝ} {m : ℕ} (hc0 : 1 ≤ c0) (hX : 2 ≤ X) (hy : 0 < y)
    (h : y ≤ 149299200 * c0 ^ 16 * X ^ (16 * m + 1)) : Real.log y ≤ capA c0 m * Real.log X :=
  df2_log_le_of_le_pow hX (by have : 1 ≤ c0 ^ 16 := one_le_pow₀ hc0; nlinarith) hy h

theorem capA_logb {c0 X y : ℝ} {m : ℕ} (hc0 : 1 ≤ c0) (hX : 2 ≤ X) (hy : 0 < y)
    (h : y ≤ 149299200 * c0 ^ 16 * X ^ (16 * m + 1)) : Real.logb 2 y ≤ 2 * capA c0 m * Real.log X := by
  have h1 := capA_log hc0 hX hy h
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hAL : 0 ≤ capA c0 m * Real.log X := mul_nonneg (capA_nonneg hc0 m) (Real.log_nonneg (by linarith))
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hl2.le hAL]

/-- The constants of ELL-cap and ELL-1 when every input of the cap bound is at most `c₀ Xᵐ`. -/
theorem bars_le {d : ℕ} (hd : 1 ≤ d) {X c0 rb Rb T W eb : ℝ} {m : ℕ} (hX : 2 ≤ X) (hc0 : 1 ≤ c0)
    (hdX : (d : ℝ) ≤ X) (hrb : 0 < rb) (hRb0 : 0 < Rb) (hT0 : 0 < T) (hW : 0 ≤ W) (heb : 0 < eb)
    (hRb : Rb ≤ c0 * X ^ m) (hr : 1 / rb ≤ c0 * X ^ m) (hT : max T 1 ≤ c0 * X ^ m)
    (hRW : Rb + W ≤ c0 * X ^ m) (he : 1 / eb ≤ c0 * X ^ m) :
    (AP.nBar d rb Rb T W eb : ℝ) ≤ 2 * d * (d + 1) * (capA c0 m * Real.log X) + 2 ∧
    (AP.jBar d rb Rb T W eb : ℝ) ≤ 2 * capA c0 m * Real.log X + 1 ∧
    (AP.bBar d rb Rb T W eb : ℝ) ≤ 2 * capA c0 m * Real.log X + 3 * d * (2 * capA c0 m * Real.log X + 2) + 1 ∧
    (AP.cntBar Rb T W eb : ℝ) ≤ 2 * capA c0 m * Real.log X + 1 := by
  have hX1 : 1 ≤ X := by linarith
  have hXm : 1 ≤ X ^ m := one_le_pow₀ hX1
  have hB : 1 ≤ c0 * X ^ m := by nlinarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hθ := capTheta_ge _ Rb T W eb hB hRb0 hW heb hRb hT hRW he
  have hθ0 : 0 < AP.thetaLo Rb T W eb := lt_of_lt_of_le (by positivity) hθ
  have hA := capA_nonneg hc0 m
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hAL : 0 ≤ capA c0 m * Real.log X := mul_nonneg hA hL
  have hK : 149299200 * c0 ^ 16 * X ^ (16 * m + 1) = 149299200 * ((c0 * X ^ m) ^ 16 * X) := by ring
  have hy : ∀ y : ℝ, 0 < y → ∀ k : ℝ, ∀ j ≤ 16, 0 ≤ k → k ≤ 149299200 → y ≤ k * (c0 * X ^ m) ^ j * X →
      y ≤ 149299200 * c0 ^ 16 * X ^ (16 * m + 1) := fun y _ k j hj hk0 hk h => by
    rw [hK]
    refine h.trans ?_
    rw [mul_assoc]
    exact mul_le_mul hk (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hj) (by positivity)) (by positivity)
      (by norm_num)
  have hdB : ∀ k : ℝ, 0 ≤ k → ∀ j, k * (c0 * X ^ m) ^ j * d ≤ k * (c0 * X ^ m) ^ j * X := fun k hk j => by
    gcongr
  have hXB : ∀ k : ℝ, 0 ≤ k → ∀ j, k * (c0 * X ^ m) ^ j ≤ k * (c0 * X ^ m) ^ j * X := fun k hk j =>
    le_mul_of_one_le_right (by positivity) hX1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
  have hJ : (AP.jBar d rb Rb T W eb : ℝ) ≤ 2 * capA c0 m * Real.log X + 1 := by
    have yp : 0 < 576 * Rb ^ 2 * Real.sqrt d / (AP.thetaLo Rb T W eb * rb ^ 2) := by positivity
    have h1 := capA_logb hc0 hX yp (hy _ yp 1728 8 (by norm_num) (by norm_num) (by norm_num)
      ((capYJ_le _ Rb rb _ d hB hd1 hRb0 hrb hθ hRb hr).trans (hdB _ (by norm_num) 8)))
    exact capCeil_le _ _ (by positivity) h1
  refine ⟨?_, hJ, ?_, ?_⟩
  · have yp : 0 < 2 * Rb / (AP.thetaLo Rb T W eb * rb) := by positivity
    have h1 := capA_log hc0 hX yp (hy _ yp 6 6 (by norm_num) (by norm_num) (by norm_num)
      ((capYN_le _ Rb rb _ hB hrb hθ hRb hr).trans (hXB _ (by norm_num) 6)))
    unfold AP.nBar
    push_cast
    have := capCeil_le (2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * Rb / (AP.thetaLo Rb T W eb * rb)))
      (2 * d * (d + 1) * (capA c0 m * Real.log X)) (by positivity) (by gcongr)
    linarith
  · have yp : 0 < 16588800 * Rb ^ 4 * Real.sqrt d / (AP.thetaLo Rb T W eb ^ 2 * rb ^ 4) := by positivity
    have h1 := capA_logb hc0 hX yp (hy _ yp 149299200 16 le_rfl (by norm_num) le_rfl
      ((capYB_le _ Rb rb _ d hB hd1 hRb0 hrb hθ hRb hr).trans (hdB _ (by norm_num) 16)))
    unfold AP.bBar
    refine capCeil_le _ _ (by positivity) ?_
    have : 3 * (d : ℝ) * ((AP.jBar d rb Rb T W eb : ℝ) + 1) ≤ 3 * d * (2 * capA c0 m * Real.log X + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · have yp : 0 < 2 * Rb * T * (Rb + W) / eb := by positivity
    have h1 := capA_logb hc0 hX yp (hy _ yp 2 4 (by norm_num) (by norm_num) (by norm_num)
      ((capYcnt_le _ Rb T W eb hB hRb0 hT0 hW heb hRb hT hRW he).trans (hXB _ (by norm_num) 4)))
    exact capCeil_le _ _ (by positivity) h1

/-! ## The caps of the calls of AP in DF2-O -/

/-- The steps of the membership codes of the regions. -/
theorem kMemR_le (d : ℕ) : ((kMemR d : ℕ) : ℝ) ≤ 134 * (d : ℝ) ^ 2 + 134 := by
  have : kMemR d ≤ 134 * d ^ 2 + 134 := by unfold kMemR kMemKeps; nlinarith
  exact_mod_cast this

/-- The cap bound of AP as a polynomial of degree `15` in `Λ ≥ max(1, d, log X)`. -/
theorem kAPcap_poly {d : ℕ} (hd : 1 ≤ d) {Kq : ℕ} (hKq : (Kq : ℝ) ≤ 134 * (d : ℝ) ^ 2 + 134)
    {X c0 Λ rb Rb T W eb : ℝ} {m : ℕ} (hX : 2 ≤ X) (hc0 : 1 ≤ c0) (hdX : (d : ℝ) ≤ X) (hΛ : 1 ≤ Λ)
    (hdΛ : (d : ℝ) ≤ Λ) (hLΛ : Real.log X ≤ Λ) (hrb : 0 < rb) (hRb0 : 0 < Rb) (hT0 : 0 < T) (hW : 0 ≤ W)
    (heb : 0 < eb) (hRb : Rb ≤ c0 * X ^ m) (hr : 1 / rb ≤ c0 * X ^ m) (hT : max T 1 ≤ c0 * X ^ m)
    (hRW : Rb + W ≤ c0 * X ^ m) (he : 1 / eb ≤ c0 * X ^ m) :
    (AP.kAPcap d Kq rb Rb T W eb : ℝ) ≤ 2536 * (2 * ((8 * capA c0 m + 300) * Λ ^ 3)) ^ 5 := by
  obtain ⟨hN, hJ, hB, hc⟩ := bars_le hd hX hc0 hdX hrb hRb0 hT0 hW heb hRb hr hT hRW he
  have hA := capA_nonneg hc0 m
  have hL : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : Λ ≤ Λ ^ 2 := by nlinarith
  have h3 : Λ ^ 2 ≤ Λ ^ 3 := by nlinarith
  have hP0 : 0 ≤ capA c0 m * Λ ^ 3 := by positivity
  have hAL : capA c0 m * Real.log X ≤ capA c0 m * Λ ^ 3 :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have hdAL : (d : ℝ) * (capA c0 m * Real.log X) ≤ capA c0 m * Λ ^ 3 := by
    calc (d : ℝ) * (capA c0 m * Real.log X) ≤ Λ * (capA c0 m * Λ) :=
          mul_le_mul hdΛ (mul_le_mul_of_nonneg_left hLΛ hA) (by positivity) (by linarith)
      _ = capA c0 m * Λ ^ 2 := by ring
      _ ≤ capA c0 m * Λ ^ 3 := mul_le_mul_of_nonneg_left h3 hA
  have hddAL : (d : ℝ) * d * (capA c0 m * Real.log X) ≤ capA c0 m * Λ ^ 3 := by
    calc (d : ℝ) * d * (capA c0 m * Real.log X) ≤ Λ * Λ * (capA c0 m * Λ) :=
          mul_le_mul (mul_le_mul hdΛ hdΛ (by positivity) (by linarith)) (mul_le_mul_of_nonneg_left hLΛ hA)
            (by positivity) (by positivity)
      _ = capA c0 m * Λ ^ 3 := by ring
  have hdd : (d : ℝ) ^ 2 ≤ Λ ^ 3 := (pow_le_pow_left₀ (by positivity) hdΛ 2).trans h3
  have hΛ3 : 1 ≤ Λ ^ 3 := by linarith
  have hU1 : 1 ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by nlinarith
  have hU' : (8 * capA c0 m + 300) * Λ ^ 3 = 8 * (capA c0 m * Λ ^ 3) + 300 * Λ ^ 3 := by ring
  have hdU : (d : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  have hKU : (Kq : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  have hNU : (AP.nBar d rb Rb T W eb : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  have hJU : (AP.jBar d rb Rb T W eb : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  have hBU : (AP.bBar d rb Rb T W eb : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  have hcU : (AP.cntBar Rb T W eb : ℝ) ≤ (8 * capA c0 m + 300) * Λ ^ 3 := by linarith
  generalize (8 * capA c0 m + 300) * Λ ^ 3 = U at hU1 hdU hKU hNU hJU hBU hcU ⊢
  have hM1 : 1 ≤ ⌈U⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.2 (by linarith)).ne'
  have toM : ∀ k : ℕ, (k : ℝ) ≤ U → k ≤ ⌈U⌉₊ := fun k h => by exact_mod_cast h.trans (Nat.le_ceil U)
  have key := kAPcap_le_pow hM1 (toM d hdU) (toM Kq hKU) (toM _ hNU) (toM _ hJU) (toM _ hBU) (toM _ hcU)
  have hM : (⌈U⌉₊ : ℝ) ≤ 2 * U := (Nat.ceil_lt_add_one (by linarith)).le.trans (by linarith)
  calc (AP.kAPcap d Kq rb Rb T W eb : ℝ) ≤ 2536 * (⌈U⌉₊ : ℝ) ^ 5 := by exact_mod_cast key
    _ ≤ 2536 * (2 * U) ^ 5 := by gcongr

/-- The bound of the caps of the two calls of AP in DF2-O. -/
theorem df2Cap_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (df2Cap1 d n δ : ℝ) ≤ 2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * n * Real.log (2 * d * n / δ))) ^ 3)) ^ 5 ∧
    (df2Cap2 d n δ : ℝ) ≤ 2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * n * Real.log (2 * d * n / δ))) ^ 3)) ^ 5 := by
  unfold df2Cap1 df2Cap2 apCap1 apCap2
  obtain ⟨hdnX, hdX, hnX, hX⟩ := df2_X_bounds d n hd hn δ hδ hδ1
  obtain ⟨hR0, hR⟩ := df2oPar_R_bound d n hd δ
  have hR1 := df2oPar_R_ge_one d n hd δ
  obtain ⟨he0, -, he⟩ := df2oPar_δe_bounds d n hd hn δ hδ hδ1
  obtain ⟨hs0, -, hs⟩ := df2oPar_sb_bounds d n hd hn δ hδ hδ1
  obtain ⟨heta0, heta⟩ := df2oPar_eta_le d n hd hn δ hδ
  have hLe0 : 0 ≤ (df2oPar d n δ).Le := by linarith [df2oPar_Le_ge d n hd hn δ hδ]
  have hLe := df2oPar_Le_le d n hd hn δ hδ hδ1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdX' : (d : ℝ) ≤ 2 * d * n / δ := by linarith
  have hR' : (df2oPar d n δ).R ≤ 268 * (2 * d * n / δ) ^ 2 := by
    have : (d : ℝ) ^ 2 ≤ (2 * d * n / δ) ^ 2 := pow_le_pow_left₀ (by positivity) hdX' 2
    linarith
  have cR := capin_R hX hR'
  have cRb := capin_rb hX hR1 hR' he0 he hs0 hs
  have cT := capin_T hX hdX he0 he
  have cW1 := capin_W1 hX hR1 hR' he0 he
  have cW2 := capin_W2 hX hd1 hn1 hdX hdnX hR' he0 he heta hLe0 hLe
  have ce2 := capin_e2 hX hd1 hn1 hdX hnX hR1 hR' he0 he
  have hL := df2_log_ge d n hd hn δ hδ hδ1
  have hL0 : 0 ≤ Real.log (2 * d * n / δ) := by linarith
  have hdn1 : (1 : ℝ) ≤ d * n := one_le_mul_of_one_le_of_one_le hd1 hn1
  have hΛ1 : 1 ≤ 2 * ((d : ℝ) * n * Real.log (2 * d * n / δ)) := by
    have := mul_le_mul hdn1 hL (by norm_num) (by positivity)
    linarith
  have hdΛ : (d : ℝ) ≤ 2 * ((d : ℝ) * n * Real.log (2 * d * n / δ)) := by
    have h1 := mul_le_mul hn1 hL (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (n * Real.log (2 * d * n / δ)) by linarith)
      (show (0 : ℝ) ≤ d by positivity)
    linarith
  have hLΛ : Real.log (2 * d * n / δ) ≤ 2 * ((d : ℝ) * n * Real.log (2 * d * n / δ)) := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * (d * n) by linarith) hL0
    linarith
  have hT0 : 0 < (d : ℝ) / (df2oPar d n δ).δe := div_pos (by linarith) he0
  have hrb : 0 < (df2oPar d n δ).sb / 2 := by linarith
  constructor
  · refine kAPcap_poly hd (kMemR_le d) hX (by norm_num) hdX' hΛ1 hdΛ hLΛ hrb hR0 hT0 (by positivity) one_pos
      cR cRb cT cW1 ?_
    rw [div_one]; linarith
  · have hW : 0 ≤ (df2oPar d n δ).R + (df2oPar d n δ).eta *
        Real.sqrt (16 * d * n * (df2oPar d n δ).Le / (df2oPar d n δ).δe) := by positivity
    have heb : 0 < 1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * (df2oPar d n δ).R ^ 2 * ((d : ℝ) / (df2oPar d n δ).δe))) :=
      one_div_pos.2 (mul_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _)))
    exact kAPcap_poly hd (kMemR_le d) hX (by norm_num) hdX' hΛ1 hdΛ hLΛ hrb hR0 hT0 hW heb cR cRb cT cW2 ce2

/-- The caps of the two calls of AP in DF2-O are polynomial in `d n log(2dn/δ)`. -/
theorem df2Caps_bound : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ((df2Cap1 d n δ + df2Cap2 d n δ : ℕ) : ℝ) ≤ C * ((d : ℝ) * n * Real.log (2 * d * n / δ)) ^ k := by
  refine ⟨2 * 2536 * (2 * (8 * capA (10 ^ 18) 14 + 300)) ^ 5 * 2 ^ 15, 15, fun d n hd hn δ hδ hδ1 => ?_⟩
  obtain ⟨h1, h2⟩ := df2Cap_le d n hd hn δ hδ hδ1
  push_cast
  calc _ ≤ 2 * (2536 * (2 * ((8 * capA (10 ^ 18) 14 + 300) *
        (2 * ((d : ℝ) * n * Real.log (2 * d * n / δ))) ^ 3)) ^ 5) := by linarith
    _ = _ := by ring

/-- DF2-O runs as a program of VL within a polynomial number of steps. -/
theorem df2oMachine : Df2OMachine :=
  df2oMachine_of_ap df2Cap1 df2Cap2 df2Caps_bound
    (fun d hd n hn r0 R0 δ _ _ hδ hδ1 _ _ _ _ _ _ _ _ _ t _ st h =>
      df2oMode_apRules d hd n hn r0 R0 δ hδ hδ1 _ t st h _ _ _)

end AdversarialBco.Poly.Mach.VL
