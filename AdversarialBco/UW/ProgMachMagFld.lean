/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachTailSpec
public import AdversarialBco.Unified.PrmKV
public import AdversarialBco.Unified.BudInst

@[expose] public section

/-!
# The fields of PARAM-W are bounded for every `d, n ≥ 1`

PARAM-W (`parOW`, UW/ProgPure.lean) is BL-O's PARAM at `N_e = NeO d n (kDel δ)` with `Le` replaced by the floor
`36 lf0 ≥ 36`, with the root `r_u = ruOW` in `η'` and with `r_u + 1/2^q` in `ε'`. The fields that the magnitude
bounds of the run read are bounded here with no hypothesis beyond `1 ≤ d` and `1 ≤ n`:

* `|λ'| ≤ 1/2`, `|ν'| ≤ 3`, `|κ_c'| ≤ d * 2^q + 2`, `|A_0| ≤ 4`, `|B_0| ≤ 2^q + 1`;
* `|η'| ≤ d * 2^q + 1`: the root `r_u` is a multiple of `1/2^q`, so either `r_u = 0` (and `η' = 0`) or
  `r_u ≥ 1/2^q`;
* `|1/ε'| ≤ 2^{p_F}` and `0 ≤ y0`, from `ε' > 0` (`parOW_eps_pos`) and the rounding `up`.

The lower bound `lf0 ≥ 1` is `fldW_lf0`, a self-contained copy of the lemma `one_le_lf0` of UW/PrmWLink.lean.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco
open AdversarialBco.Unified.BLO (NeO kDel parO)
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.Unified.PrmK (qK_ge NeK_pos)
open AdversarialBco.Bit.BLP (rnd up sqrtDn sqrtUp lnQ lnErr)
open AdversarialBco.Bit.Transfer.BLM (rnd_abs_le)
open AdversarialBco.UW.BLOW (parOW lf0 lf1 ruOW iotaOW y0OW uOW)

/-! ## `lf0 ≥ 1` (copy of `one_le_lf0`) -/

theorem fldW_NeO0_le (d n e : ℕ) : NeO d n 0 ≤ NeO d n e := by
  unfold NeO
  have : 2 ^ (17 + 0) ≤ 2 ^ (17 + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  gcongr

theorem fldW_size_N0 (d n e : ℕ) : (NeO d n 0).size ≤ (NeO d n e).size :=
  Nat.size_le_size (fldW_NeO0_le d n e)

/-- `lf0 ≥ 1`: `ln N_0 ≥ 20 ln 2` and `lnErr_q N_0 ≤ 2^{-16}`. -/
theorem fldW_lf0 (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ lf0 d n δ := by
  set e := kDel δ
  have hq1 : 1 ≤ (parK d n e).q := by have := qK_ge d n e; omega
  have hL0 := AdversarialBco.Bit.PieceA.lnQ_err (parK d n e).q (NeO d n 0) hq1 (NeK_pos hd hn)
  have hee := AdversarialBco.Unified.BudK.lnErr_le d n e (NeO d n 0) hd hn (fldW_size_N0 d n e)
  have hu : AdversarialBco.Unified.BudK.tp d n e ≤ 1 := by
    rw [AdversarialBco.Unified.BudK.tp_eq, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hN20 : (2 : ℝ) ^ 20 ≤ (NeO d n 0 : ℝ) := by
    have h1 := (AdversarialBco.Unified.BudK.NeO_ge d n 0 hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 2 ^ 20 ≤ NeO d n 0 := le_trans (by nlinarith) h1
    exact_mod_cast h2
  have hlog : 20 * Real.log 2 ≤ Real.log (NeO d n 0) := by
    have h20 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [Real.log_le_log (by positivity) hN20]
  have h2 := Real.log_two_gt_d9
  obtain ⟨hA, -⟩ := abs_le.mp hL0
  have h : (1 : ℝ) ≤ ((lf0 d n δ : ℚ) : ℝ) := by
    show (1 : ℝ) ≤ (((lnQ (parK d n e).q (NeO d n 0) - lnErr (parK d n e).q (NeO d n 0) : ℚ)) : ℝ)
    push_cast
    have : (AdversarialBco.Unified.BudK.tp d n e) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  exact_mod_cast h

/-! ## The parameters of PARAM-W -/

theorem fW_lam_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).lam =
    rnd (parO d n δ).pF (1 / (725 * d * (36 * lf0 d n δ) ^ 2)) := rfl

theorem fW_eta_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).eta =
    rnd (parO d n δ).pF (sqrtDn (parO d n δ).q d /
      (36 * lf0 d n δ * sqrtDn (parO d n δ).q n * ruOW d n δ)) := rfl

theorem fW_nu_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).nu =
    rnd (parO d n δ).pF (1 / (1 - (parOW d n δ).lam)) := rfl

theorem fW_kapc_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).kapc =
    rnd (parO d n δ).pF ((parOW d n δ).eta * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2)) := rfl

/-- `σ²' = rnd_{p_F}(1/(8 L_f'))` at PARAM-W. -/
def fW_sig2 (d n : ℕ) (δ : ℚ) : ℚ := rnd (parO d n δ).pF (1 / (8 * (36 * lf0 d n δ)))

/-- `s' = sqrtUp_q σ²'`, the value whose rounding is `A_0` and whose inverse rounds to `B_0`. -/
def fW_s (d n : ℕ) (δ : ℚ) : ℚ := sqrtUp (parO d n δ).q (fW_sig2 d n δ)

theorem fW_A0_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).A0 = rnd (parO d n δ).p (fW_s d n δ) := rfl

theorem fW_B0_eq (d n : ℕ) (δ : ℚ) : (parOW d n δ).B0 = rnd (parO d n δ).p (1 / fW_s d n δ) := rfl

theorem fW_pF_two (d n : ℕ) (δ : ℚ) : 2 ≤ (parO d n δ).pF := by
  rw [AdversarialBco.Unified.BudK.parO_eq, AdversarialBco.Unified.BudK.parK_pF]
  omega

/-! ## Bounds on `λ'`, `ν'`, `η'`, `κ_c'` -/

theorem fW_lam_bnd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).lam| ≤ 1 / 2 := by
  have hL := fldW_lf0 d n δ hd hn
  have hpF := fW_pF_two d n δ
  have hA : (1 : ℚ) ≤ (36 * lf0 d n δ) ^ 2 := one_le_pow₀ (by linarith)
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hdA : (1 : ℚ) ≤ d * (36 * lf0 d n δ) ^ 2 := by nlinarith
  have hpos : (0 : ℚ) < 725 * d * (36 * lf0 d n δ) ^ 2 := by nlinarith
  have hx0 : 0 ≤ 1 / (725 * d * (36 * lf0 d n δ) ^ 2) := div_nonneg zero_le_one hpos.le
  have hx1 : 1 / (725 * d * (36 * lf0 d n δ) ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  have he := AdversarialBco.Bit.BLP.rnd_err (parO d n δ).pF (1 / (725 * d * (36 * lf0 d n δ) ^ 2))
  have hp : (1 : ℚ) / 2 ^ ((parO d n δ).pF + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℚ) ^ 2 ≤ 2 ^ ((parO d n δ).pF + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  rw [fW_lam_eq]
  rw [abs_le] at he ⊢
  constructor <;> linarith [he.1, he.2]

theorem fW_nu_bnd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).nu| ≤ 3 := by
  have hl := abs_le.mp (fW_lam_bnd d n δ hd hn)
  have hpos : (0 : ℚ) < 1 - (parOW d n δ).lam := by linarith [hl.2]
  have hx : |1 / (1 - (parOW d n δ).lam)| ≤ 2 := by
    rw [abs_of_pos (div_pos one_pos hpos), div_le_iff₀ hpos]
    linarith [hl.2]
  rw [fW_nu_eq]
  have := rnd_abs_le (parO d n δ).pF (1 / (1 - (parOW d n δ).lam))
  linarith

/-- `0 ≤ √d (rounded down) ≤ d`. -/
theorem fW_rd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) :
    0 ≤ sqrtDn (parO d n δ).q d ∧ sqrtDn (parO d n δ).q d ≤ d :=
  AdversarialBco.Unified.MagO.rd_bnd d n (kDel δ) hd

/-- `1 ≤ √n (rounded down)`. -/
theorem fW_rn (d n : ℕ) (δ : ℚ) (hn : 1 ≤ n) : 1 ≤ sqrtDn (parO d n δ).q n :=
  AdversarialBco.Unified.MagO.rn_ge d n (kDel δ) hn

/-- The root `r_u` is a multiple of `1/2^q`, so a nonzero `r_u` is at least `1/2^q`. -/
theorem fW_ru_grid (d n : ℕ) (δ : ℚ) (h : ruOW d n δ ≠ 0) : 1 / 2 ^ (parO d n δ).q ≤ ruOW d n δ := by
  have hN : ruOW d n δ = ((Nat.sqrt ⌊uOW d n δ * 4 ^ (parO d n δ).q⌋₊ : ℕ) : ℚ) / 2 ^ (parO d n δ).q := rfl
  have hN0 : Nat.sqrt ⌊uOW d n δ * 4 ^ (parO d n δ).q⌋₊ ≠ 0 := by
    intro h0
    apply h
    rw [hN, h0]
    simp
  have hN1 : (1 : ℚ) ≤ ((Nat.sqrt ⌊uOW d n δ * 4 ^ (parO d n δ).q⌋₊ : ℕ) : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  rw [hN]
  gcongr

theorem fW_eta_bnd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    |(parOW d n δ).eta| ≤ d * 2 ^ (parO d n δ).q + 1 := by
  rw [fW_eta_eq]
  have hL := fldW_lf0 d n δ hd hn
  have hrn := fW_rn d n δ hn
  obtain ⟨hr0, hr1⟩ := fW_rd d n δ hd
  have hru0 := AdversarialBco.UW.BLOW.ruOW_nonneg d n δ
  have hq : (0 : ℚ) < 2 ^ (parO d n δ).q := by positivity
  have hd' : (0 : ℚ) ≤ d := by positivity
  have hd0 : (0 : ℚ) ≤ d * 2 ^ (parO d n δ).q := by positivity
  have hmain : |sqrtDn (parO d n δ).q d /
      (36 * lf0 d n δ * sqrtDn (parO d n δ).q n * ruOW d n δ)| ≤ d * 2 ^ (parO d n δ).q := by
    rcases eq_or_ne (ruOW d n δ) 0 with h0 | h0
    · rw [h0, mul_zero, div_zero, abs_zero]
      exact hd0
    · have hg := fW_ru_grid d n δ h0
      have hpos : 0 < ruOW d n δ := lt_of_le_of_ne hru0 (Ne.symm h0)
      have hlr : (1 : ℚ) ≤ lf0 d n δ * sqrtDn (parO d n δ).q n := by nlinarith
      have hA : (1 : ℚ) ≤ 36 * lf0 d n δ * sqrtDn (parO d n δ).q n := by nlinarith
      have hB : (1 : ℚ) ≤ 2 ^ (parO d n δ).q * ruOW d n δ := by
        have := mul_le_mul_of_nonneg_left hg hq.le
        rwa [mul_one_div_cancel hq.ne'] at this
      have hDen : 0 < 36 * lf0 d n δ * sqrtDn (parO d n δ).q n * ruOW d n δ := by
        nlinarith [mul_le_mul_of_nonneg_right hA hpos.le]
      have hC : (1 : ℚ) ≤ 2 ^ (parO d n δ).q * (36 * lf0 d n δ * sqrtDn (parO d n δ).q n * ruOW d n δ) := by
        nlinarith [mul_le_mul hA hB zero_le_one (by linarith)]
      rw [abs_of_nonneg (div_nonneg hr0 hDen.le), div_le_iff₀ hDen]
      nlinarith [mul_le_mul_of_nonneg_left hC hd']
  have hX := rnd_abs_le (parO d n δ).pF
    (sqrtDn (parO d n δ).q d / (36 * lf0 d n δ * sqrtDn (parO d n δ).q n * ruOW d n δ))
  linarith

theorem fW_kapc_bnd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    |(parOW d n δ).kapc| ≤ d * 2 ^ (parO d n δ).q + 2 := by
  rw [fW_kapc_eq]
  have he := fW_eta_bnd d n δ hd hn
  have hl := fW_lam_bnd d n δ hd hn
  have hl' := abs_le.mp hl
  have h4 : (1 : ℚ) ≤ 4 * (1 - (parOW d n δ).lam) ^ 2 := by
    nlinarith [mul_nonneg (by linarith [hl'.2] : (0 : ℚ) ≤ 1 - 2 * (parOW d n δ).lam)
      (by linarith [hl'.2] : (0 : ℚ) ≤ 3 - 2 * (parOW d n δ).lam)]
  have hpos4 : (0 : ℚ) < 4 * (1 - (parOW d n δ).lam) ^ 2 := by linarith
  have hd0 : (0 : ℚ) ≤ d * 2 ^ (parO d n δ).q := by positivity
  have hE : (0 : ℚ) ≤ (d * 2 ^ (parO d n δ).q + 1) / 2 := by positivity
  have hx : |(parOW d n δ).eta * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2)|
      ≤ ((d : ℚ) * 2 ^ (parO d n δ).q + 1) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpos4, div_le_iff₀ hpos4]
    have hm : |(parOW d n δ).eta| * |(parOW d n δ).lam| ≤ ((d : ℚ) * 2 ^ (parO d n δ).q + 1) * (1 / 2) :=
      mul_le_mul he hl (abs_nonneg _) (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 h4) hE]
  have := rnd_abs_le (parO d n δ).pF
    ((parOW d n δ).eta * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2))
  linarith

/-! ## Bounds on `A_0`, `B_0` -/

theorem fW_sig2_le (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : fW_sig2 d n δ ≤ 1 := by
  have hL := fldW_lf0 d n δ hd hn
  have hpF := fW_pF_two d n δ
  have he := AdversarialBco.Bit.BLP.rnd_err (parO d n δ).pF (1 / (8 * (36 * lf0 d n δ)))
  have hp : (1 : ℚ) / 2 ^ ((parO d n δ).pF + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℚ) ^ 2 ≤ 2 ^ ((parO d n δ).pF + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hx : 1 / (8 * (36 * lf0 d n δ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  rw [abs_le] at he
  unfold fW_sig2
  linarith [he.2]

theorem fW_s_pos (d n : ℕ) (δ : ℚ) : 0 < fW_s d n δ := by
  unfold fW_s sqrtUp
  positivity

theorem fW_s_le (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : fW_s d n δ ≤ 3 := by
  have h1 := fW_sig2_le d n δ hd hn
  have h := AdversarialBco.Bit.PieceA.sqrtUp_le (parO d n δ).q (fW_sig2 d n δ)
  have hs : Real.sqrt ((fW_sig2 d n δ : ℚ) : ℝ) ≤ 1 := Real.sqrt_le_one.mpr (by exact_mod_cast h1)
  have hq : (2 : ℝ) / 2 ^ (parO d n δ).q ≤ 2 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have : ((fW_s d n δ : ℚ) : ℝ) ≤ 3 := by
    unfold fW_s
    linarith
  exact_mod_cast this

theorem fW_s_ge (d n : ℕ) (δ : ℚ) : 1 / 2 ^ (parO d n δ).q ≤ fW_s d n δ := by
  have h0 : (0 : ℚ) ≤ ((Nat.sqrt ⌈fW_sig2 d n δ * 4 ^ (parO d n δ).q⌉₊ : ℕ) : ℚ) := Nat.cast_nonneg _
  unfold fW_s sqrtUp
  gcongr
  linarith

theorem fW_inv_s_le (d n : ℕ) (δ : ℚ) : 1 / fW_s d n δ ≤ 2 ^ (parO d n δ).q := by
  have hq : (0 : ℚ) < 2 ^ (parO d n δ).q := by positivity
  rw [div_le_iff₀ (fW_s_pos d n δ)]
  have := mul_le_mul_of_nonneg_left (fW_s_ge d n δ) hq.le
  rw [mul_one_div_cancel hq.ne'] at this
  linarith

theorem fW_A0_bnd (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).A0| ≤ 4 := by
  rw [fW_A0_eq]
  have h := rnd_abs_le (parO d n δ).p (fW_s d n δ)
  rw [abs_of_pos (fW_s_pos d n δ)] at h
  linarith [fW_s_le d n δ hd hn]

theorem fW_B0_bnd (d n : ℕ) (δ : ℚ) : |(parOW d n δ).B0| ≤ 2 ^ (parOW d n δ).q + 1 := by
  rw [AdversarialBco.UW.BLOW.parOW_q, fW_B0_eq]
  have h := rnd_abs_le (parO d n δ).p (1 / fW_s d n δ)
  rw [abs_of_pos (div_pos one_pos (fW_s_pos d n δ))] at h
  linarith [fW_inv_s_le d n δ]

/-! ## Bounds on `1/ε'` and `y0` -/

/-- `|1/x| ≤ 2^k` for `x = up_k y > 0`: the numerator of `x` is a positive integer. -/
theorem fW_inv_up_le (k : ℕ) (x : ℚ) (h : 0 < up k x) : |(up k x)⁻¹| ≤ 2 ^ k := by
  unfold up at h ⊢
  have hk : (0 : ℚ) < 2 ^ k := by positivity
  have hC : (0 : ℚ) < ((⌈x * 2 ^ k⌉ : ℤ) : ℚ) := (div_pos_iff_of_pos_right hk).mp h
  have hC' : (0 : ℤ) < ⌈x * 2 ^ k⌉ := by exact_mod_cast hC
  have hC1 : (1 : ℚ) ≤ ((⌈x * 2 ^ k⌉ : ℤ) : ℚ) := by
    have : (1 : ℤ) ≤ ⌈x * 2 ^ k⌉ := by omega
    exact_mod_cast this
  rw [inv_div, abs_of_pos (div_pos hk (by linarith))]
  exact div_le_self hk.le hC1

theorem fldW_epsI (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    |(parOW d n δ).eps⁻¹| ≤ 2 ^ (parOW d n δ).pF := by
  have hpos := parOW_eps_pos d n δ hd hn
  rw [AdversarialBco.UW.BLOW.parOW_eps] at hpos ⊢
  rw [AdversarialBco.UW.BLOW.parOW_pF]
  exact fW_inv_up_le _ _ hpos

theorem fW_iota_nonneg (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ iotaOW d n δ := by
  have hL := fldW_lf0 d n δ hd hn
  unfold iotaOW
  apply AdversarialBco.Unified.BLO.up_nonneg
  apply div_nonneg
  · exact add_nonneg (AdversarialBco.Bit.BLP.sqrtDn_nonneg _ _) (by positivity)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (AdversarialBco.Bit.BLP.sqrtDn_nonneg _ _)) (pow_nonneg (by linarith) 5))
      (AdversarialBco.UW.BLOW.ruOW_nonneg d n δ)

/-! ## The eight fields -/

/-- `|λ'| ≤ 1/2` at PARAM-W. -/
theorem fldW_lam (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).lam| ≤ 1 / 2 :=
  fW_lam_bnd d n δ hd hn

/-- `|ν'| ≤ 3` at PARAM-W. -/
theorem fldW_nu (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).nu| ≤ 3 :=
  fW_nu_bnd d n δ hd hn

/-- `|κ_c'| ≤ d 2^q + 2` at PARAM-W. -/
theorem fldW_kapc (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    |(parOW d n δ).kapc| ≤ d * 2 ^ (parOW d n δ).q + 2 := by
  rw [AdversarialBco.UW.BLOW.parOW_q]
  exact fW_kapc_bnd d n δ hd hn

/-- `|A_0| ≤ 4` at PARAM-W. -/
theorem fldW_A0 (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parOW d n δ).A0| ≤ 4 :=
  fW_A0_bnd d n δ hd hn

/-- `|B_0| ≤ 2^q + 1` at PARAM-W. -/
theorem fldW_B0 (d n : ℕ) (δ : ℚ) (_hd : 1 ≤ d) (_hn : 1 ≤ n) :
    |(parOW d n δ).B0| ≤ 2 ^ (parOW d n δ).q + 1 :=
  fW_B0_bnd d n δ

/-- `0 ≤ y0` at PARAM-W. -/
theorem fldW_y0 (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ y0OW d n δ := by
  have hi := fW_iota_nonneg d n δ hd hn
  have hs : 0 ≤ sqrtUp (parO d n δ).q (12 * lf1 d n δ) := by
    unfold sqrtUp
    positivity
  unfold y0OW
  apply AdversarialBco.Unified.BLO.up_nonneg
  linarith

end AdversarialBco.UW.ProgW
