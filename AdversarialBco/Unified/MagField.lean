/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudEnc
public import AdversarialBco.Bit.Transfer.XBLExp
public import AdversarialBco.Unified.BLOParam
public import AdversarialBco.Unified.ProgOBL

@[expose] public section

/-!
# The magnitudes of BL-O's run, part A: PARAM's fields at `k`

PARAM's fields bounded directly at `parK d n k = parN (N_e(k)) d n`, on every `d, n ≥ 1` and `k` (no case
`ε ≤ 1/4`): `1 ≤ Le ≤ 25 ℓe` (`LeQ_bnd`, from `lnQ_err`), `|λ'| ≤ 1/2`, `|ν'| ≤ 3`, `|η'| ≤ d + 1`, `|κ_c'| ≤ d + 2`,
`|A_0| ≤ 4`, `|B_0| ≤ 400 ℓe + 1`, `0 ≤ R ≤ 1000 d²`, `0 ≤ ε'`, `|1/ε'| ≤ 2^{pF}` (the grid), and the unit
`T = 2^{K}`, `K = pF + 8`, bounds them all with `d`, `n`, `N_e`, `Λ`, `B`, `R_int`, `2^{q_O - p}` (`fld_unit`).
`K ≤ 528 W` with `W = wU d n δ r0 R0 a` at `k = kDel δ` (`Kunit_le`).
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (Par lnQ lnErr sqrtDn sqrtUp rnd up dn)
open AdversarialBco.Bit.PieceA (ld lnQ_err one_le_sqrtDn sqrt_le_sqrtUp sqrtUp_le)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM

/-! ## `Le` and the roots -/

theorem q_ge (d n k : ℕ) : 1 ≤ (parK d n k).q := by rw [parK_q]; omega

theorem tp_le_one (d n k : ℕ) : tp d n k ≤ 1 := by
  rw [tp_eq]; exact div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)

/-- PARAM's `Le = 36 (L0 - η_e)` at `k`: `1 ≤ Le ≤ 25 ℓe`, and `0 ≤ L0 + η_e`. -/
theorem LeQ_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (1 : ℚ) ≤ (parK d n k).Le ∧ (parK d n k).Le ≤ 25 * leK d n k ∧ 0 ≤ L0 d n k + ee d n k := by
  have hN := NeO_pos d n k hd hn
  have h1 : |((L0 d n k : ℚ) : ℝ) - Real.log (BudK.Ne d n k)| ≤ ((ee d n k : ℚ) : ℝ) :=
    lnQ_err (parK d n k).q (NeO d n k) (q_ge d n k) hN
  have h2 : ((ee d n k : ℚ) : ℝ) ≤ tp d n k / 2 ^ 16 := lnErr_le d n k (NeO d n k) hd hn le_rfl
  have htp := tp_le_one d n k
  have hLe := Le_le_size d n k hd hn
  rw [Le_eq d n k hd hn] at hLe
  have h20 : (2 : ℝ) ^ 20 ≤ BudK.Ne d n k := by
    have h0 := (NeO_ge d n k hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have : 2 ^ 20 ≤ NeO d n k := le_trans (Nat.le_mul_of_pos_right _ h3) h0
    unfold BudK.Ne; exact_mod_cast this
  have hlog : 13 ≤ Real.log (BudK.Ne d n k) := by
    have h := Real.log_le_log (by positivity) h20
    rw [Real.log_pow] at h
    have := Real.log_two_gt_d9
    push_cast at h
    linarith
  rw [abs_le] at h1
  have hL : (((parK d n k).Le : ℚ) : ℝ) = 36 * (((L0 d n k : ℚ) : ℝ) - ((ee d n k : ℚ) : ℝ)) := by
    rw [parK_Le]; push_cast; ring
  have hee : ((ee d n k : ℚ) : ℝ) ≤ 1 / 2 ^ 16 := by
    calc ((ee d n k : ℚ) : ℝ) ≤ tp d n k / 2 ^ 16 := h2
      _ ≤ 1 / 2 ^ 16 := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ (((parK d n k).Le : ℚ) : ℝ) := by rw [hL]; linarith [h1.1, h1.2]
    exact_mod_cast this
  · have : (((parK d n k).Le : ℚ) : ℝ) ≤ 25 * (leK d n k : ℝ) := by rw [hL]; linarith [h1.1, h1.2]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ ((L0 d n k : ℚ) : ℝ) + ((ee d n k : ℚ) : ℝ) := by linarith [h1.1, h1.2]
    exact_mod_cast this

/-- `0 ≤ √d (rounded down) ≤ d`. -/
theorem rd_bnd (d n k : ℕ) (hd : 1 ≤ d) : 0 ≤ sqrtDn (parK d n k).q d ∧ sqrtDn (parK d n k).q d ≤ d := by
  have h0 := Bit.BLP.sqrtDn_nonneg (parK d n k).q (d : ℚ)
  have h1 := Bit.BLP.sqrtDn_sq_le (parK d n k).q (show (0 : ℚ) ≤ d by positivity)
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  refine ⟨h0, ?_⟩
  nlinarith

/-- `1 ≤ √n (rounded down)`. -/
theorem rn_ge (d n k : ℕ) (hn : 1 ≤ n) : (1 : ℚ) ≤ sqrtDn (parK d n k).q n := by
  have h := one_le_sqrtDn (parK d n k).q (show (1 : ℚ) ≤ n by exact_mod_cast hn)
  exact_mod_cast h

theorem pF_ge (d n k : ℕ) :
    10 * leK d n k + 16 * ld d + 160 ≤ (parK d n k).p ∧ (parK d n k).p ≤ (parK d n k).pF ∧
      (parK d n k).pF = (parK d n k).p + 2 * leK d n k + 4 * ld d + 40 := by
  refine ⟨le_rfl, ?_, ?_⟩
  · rw [parK_pF, parK_p]; omega
  · rw [parK_pF, parK_p]

/-! ## The fields -/

theorem lam_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).lam| ≤ 1 / 2 := by
  obtain ⟨hL1, -, -⟩ := LeQ_bnd d n k hd hn
  have he := Bit.BLP.rnd_err (parK d n k).pF (1 / (725 * d * (parK d n k).Le ^ 2))
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hL2 : (1 : ℚ) ≤ (parK d n k).Le ^ 2 := one_le_pow₀ hL1
  have hx0 : 0 ≤ 1 / (725 * (d : ℚ) * (parK d n k).Le ^ 2) := by positivity
  have hx1 : 1 / (725 * (d : ℚ) * (parK d n k).Le ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hp : (1 : ℚ) / 2 ^ ((parK d n k).pF + 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℚ) ^ 2 ≤ 2 ^ ((parK d n k).pF + 1) := pow_le_pow_right₀ (by norm_num) (by rw [parK_pF]; omega)
    linarith
  rw [parK_lam]
  rw [abs_le] at he ⊢
  constructor <;> linarith [he.1, he.2]

theorem one_sub_lam (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / 2 ≤ 1 - (parK d n k).lam ∧ 1 - (parK d n k).lam ≤ 3 / 2 := by
  have h := lam_bnd d n k hd hn
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem nu_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).nu| ≤ 3 := by
  obtain ⟨h1, -⟩ := one_sub_lam d n k hd hn
  have hx : |1 / (1 - (parK d n k).lam)| ≤ 2 := by
    rw [abs_of_pos (div_pos one_pos (by linarith)), div_le_iff₀ (by linarith)]; linarith
  rw [parK_nu]
  have := rnd_abs_le (parK d n k).pF (1 / (1 - (parK d n k).lam))
  linarith

theorem eta_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).eta| ≤ d + 1 := by
  obtain ⟨hL1, -, -⟩ := LeQ_bnd d n k hd hn
  obtain ⟨hr0, hr1⟩ := rd_bnd d n k hd
  have hn1 := rn_ge d n k hn
  have hpos : (0 : ℚ) < (parK d n k).Le * sqrtDn (parK d n k).q n := mul_pos (by linarith) (by linarith)
  have hx : |sqrtDn (parK d n k).q d / ((parK d n k).Le * sqrtDn (parK d n k).q n)| ≤ d := by
    rw [abs_of_nonneg (div_nonneg hr0 hpos.le), div_le_iff₀ hpos]
    have : (1 : ℚ) ≤ (parK d n k).Le * sqrtDn (parK d n k).q n := by nlinarith
    have hd0 : (0 : ℚ) ≤ d := by positivity
    nlinarith
  rw [parK_eta]
  have := rnd_abs_le (parK d n k).pF (sqrtDn (parK d n k).q d / ((parK d n k).Le * sqrtDn (parK d n k).q n))
  linarith

theorem kapc_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).kapc| ≤ d + 2 := by
  have he := eta_bnd d n k hd hn
  have hl := lam_bnd d n k hd hn
  obtain ⟨h1, -⟩ := one_sub_lam d n k hd hn
  have h4 : (1 : ℚ) ≤ 4 * (1 - (parK d n k).lam) ^ 2 := by nlinarith
  have hx : |(parK d n k).eta * (parK d n k).lam / (4 * (1 - (parK d n k).lam) ^ 2)| ≤ ((d : ℚ) + 1) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℚ) < 4 * (1 - (parK d n k).lam) ^ 2),
      div_le_iff₀ (by linarith)]
    have hm : |(parK d n k).eta| * |(parK d n k).lam| ≤ ((d : ℚ) + 1) * (1 / 2) :=
      mul_le_mul he hl (abs_nonneg _) (by positivity)
    have h0 : (0 : ℚ) ≤ ((d : ℚ) + 1) / 2 := by positivity
    nlinarith
  rw [parK_kapc]
  have := rnd_abs_le (parK d n k).pF ((parK d n k).eta * (parK d n k).lam / (4 * (1 - (parK d n k).lam) ^ 2))
  linarith

/-- `16 · 25 ℓe ≤ 2^{pF + 1}`. -/
theorem le_pF (d n k : ℕ) : (16 * (25 * leK d n k) : ℚ) ≤ 2 ^ ((parK d n k).pF + 1) := by
  have h1 : (leK d n k : ℚ) < 2 ^ leK d n k := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℚ) ^ (leK d n k + 9) ≤ 2 ^ ((parK d n k).pF + 1) :=
    pow_le_pow_right₀ (by norm_num) (by rw [parK_pF]; omega)
  have h3 : (2 : ℚ) ^ (leK d n k + 9) = 512 * 2 ^ leK d n k := by rw [pow_add]; ring
  linarith

theorem sig2_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 ≤ 16 * (parK d n k).Le * (parK d n k).sig2 ∧ (parK d n k).sig2 ≤ 1 := by
  obtain ⟨hL1, hL2, -⟩ := LeQ_bnd d n k hd hn
  have he := Bit.BLP.rnd_err (parK d n k).pF (1 / (8 * (parK d n k).Le))
  have hp := le_pF d n k
  have hL0 : (0 : ℚ) < (parK d n k).Le := by linarith
  have hP0 : (0 : ℚ) < 2 ^ ((parK d n k).pF + 1) := by positivity
  have hq : 1 / (2 : ℚ) ^ ((parK d n k).pF + 1) ≤ 1 / (16 * (parK d n k).Le) := by
    rw [div_le_div_iff₀ hP0 (by positivity)]; linarith
  have hx : 1 / (8 * (parK d n k).Le) = 2 * (1 / (16 * (parK d n k).Le)) := by field_simp; ring
  have hx1 : 1 / (16 * (parK d n k).Le) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [parK_sig2]
  rw [abs_le] at he
  have hlo : 1 / (16 * (parK d n k).Le) ≤ rnd (parK d n k).pF (1 / (8 * (parK d n k).Le)) := by linarith [he.1]
  refine ⟨?_, by linarith [he.2]⟩
  have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℚ) ≤ 16 * (parK d n k).Le)
  rwa [mul_one_div_cancel (by positivity)] at this

theorem s_pos (d n k : ℕ) : 0 < sqrtUp (parK d n k).q (parK d n k).sig2 := by unfold sqrtUp; positivity

theorem s_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : sqrtUp (parK d n k).q (parK d n k).sig2 ≤ 3 := by
  obtain ⟨-, h1⟩ := sig2_bnd d n k hd hn
  have h := sqrtUp_le (parK d n k).q (parK d n k).sig2
  have hs : Real.sqrt (((parK d n k).sig2 : ℚ) : ℝ) ≤ 1 := Real.sqrt_le_one.mpr (by exact_mod_cast h1)
  have hq : (2 : ℝ) / 2 ^ (parK d n k).q ≤ 2 := div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  have : ((sqrtUp (parK d n k).q (parK d n k).sig2 : ℚ) : ℝ) ≤ 3 := by linarith
  exact_mod_cast this

theorem s_inv_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / sqrtUp (parK d n k).q (parK d n k).sig2 ≤ 16 * (parK d n k).Le := by
  obtain ⟨h1, h2⟩ := sig2_bnd d n k hd hn
  obtain ⟨hL1, -, -⟩ := LeQ_bnd d n k hd hn
  have hs := s_pos d n k
  have hsq := Bit.BLP.le_sqrtUp_sq (parK d n k).q (parK d n k).sig2
  rw [div_le_iff₀ hs]
  set s := sqrtUp (parK d n k).q (parK d n k).sig2
  rcases le_total 1 s with h | h
  · nlinarith
  · have : s ^ 2 ≤ s := by nlinarith
    nlinarith

theorem A0_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).A0| ≤ 4 := by
  have h := rnd_abs_le (parK d n k).p (sqrtUp (parK d n k).q (parK d n k).sig2)
  rw [abs_of_pos (s_pos d n k)] at h
  rw [parK_A0]; linarith [s_le d n k hd hn]

theorem B0_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : |(parK d n k).B0| ≤ 400 * leK d n k + 1 := by
  have h := rnd_abs_le (parK d n k).p (1 / sqrtUp (parK d n k).q (parK d n k).sig2)
  rw [abs_of_pos (div_pos one_pos (s_pos d n k))] at h
  obtain ⟨-, hL2, -⟩ := LeQ_bnd d n k hd hn
  rw [parK_B0]; linarith [s_inv_le d n k hd hn]

theorem l1Q_le (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : ((l1Q d n k : ℚ) : ℝ) ≤ 2 * d + 3 := by
  have hN : 1 ≤ 2 * d + 2 := by omega
  have h1 := lnQ_err (parK d n k).q (2 * d + 2) (q_ge d n k) hN
  have hsz := (size_facts d n k hd hn).2.2.2.2.2.2
  have h2 := lnErr_le d n k (2 * d + 2) hd hn hsz
  have htp := tp_le_one d n k
  have hlog : Real.log ((2 * d + 2 : ℕ) : ℝ) ≤ ((2 * d + 2 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have he : ((lnErr (parK d n k).q (2 * d + 2) : ℚ) : ℝ) ≤ 1 := by
    have : tp d n k / 2 ^ 16 ≤ 1 := by
      calc tp d n k / 2 ^ 16 ≤ tp d n k := div_le_self (by rw [tp_eq]; positivity) (by norm_num)
        _ ≤ 1 := htp
    linarith
  rw [abs_le] at h1
  have e : ((l1Q d n k : ℚ) : ℝ) = ((lnQ (parK d n k).q (2 * d + 2) : ℚ) : ℝ) +
      ((lnErr (parK d n k).q (2 * d + 2) : ℚ) : ℝ) := by unfold l1Q; push_cast; ring
  push_cast at hlog h1
  rw [e]; linarith [h1.2]

theorem R_bnd (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ (parK d n k).R ∧ (parK d n k).R ≤ 1000 * d ^ 2 := by
  have hl := l1Q_le d n k hd hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : ((sqrtUp (parK d n k).q (l1Q d n k) : ℚ) : ℝ) ≤ 2 * d + 4 := by
    have h := sqrtUp_le (parK d n k).q (l1Q d n k)
    have hq : (2 : ℝ) / 2 ^ (parK d n k).q ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (parK d n k).q := pow_le_pow_right₀ (by norm_num) (q_ge d n k)
      linarith
    have hsq : Real.sqrt ((l1Q d n k : ℚ) : ℝ) ≤ 2 * d + 3 := by
      calc Real.sqrt ((l1Q d n k : ℚ) : ℝ) ≤ Real.sqrt ((2 * (d : ℝ) + 3) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * d + 3 := Real.sqrt_sq (by positivity)
    linarith
  have hsQ : sqrtUp (parK d n k).q (l1Q d n k) ≤ 2 * d + 4 := by exact_mod_cast hs
  have hs0 : 0 < sqrtUp (parK d n k).q (l1Q d n k) := by unfold sqrtUp; positivity
  have hdQ : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hup := Bit.BLP.up_lt (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
  have hlo := Bit.BLP.le_up (parK d n k).pF (134 * d * sqrtUp (parK d n k).q (l1Q d n k))
  have hp : (1 : ℚ) / 2 ^ (parK d n k).pF ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
  rw [parK_R]
  refine ⟨le_trans (by positivity) hlo, ?_⟩
  have : 134 * (d : ℚ) * sqrtUp (parK d n k).q (l1Q d n k) ≤ 134 * d * (2 * d + 4) :=
    mul_le_mul_of_nonneg_left hsQ (by positivity)
  nlinarith

theorem eps_nonneg (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ (parK d n k).eps := by
  obtain ⟨-, -, hL⟩ := LeQ_bnd d n k hd hn
  obtain ⟨hr0, -⟩ := rd_bnd d n k hd
  have hn1 := rn_ge d n k hn
  rw [parK_eps]
  refine le_trans ?_ (Bit.BLP.le_up _ _)
  apply div_nonneg _ (by linarith)
  have : (0 : ℚ) ≤ 36 * (L0 d n k + ee d n k) := by linarith
  positivity

theorem eps_inv (d n k : ℕ) : |(parK d n k).eps⁻¹| ≤ 2 ^ (parK d n k).pF :=
  inv_grid (by rw [parK_eps]; exact onG_up _ _)

/-! ## The unit `2^K` -/

/-- The exponent of the unit. -/
def Ku (d n k : ℕ) : ℕ := (parK d n k).pF + 8

theorem NeO_lt (d n k : ℕ) : NeO d n k < 2 ^ leK d n k := Nat.lt_size_self _

theorem n_le_NeO (d n k : ℕ) (hd : 1 ≤ d) : n ≤ NeO d n k := by
  unfold NeO
  have h1 : 0 < 15 * 2 ^ (17 + k) * d ^ 3 := Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity)) (pow_pos hd 3)
  calc n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    _ ≤ 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := Nat.le_mul_of_pos_left _ h1

theorem nd2_le_NeO (d n k : ℕ) (hd : 1 ≤ d) : n * (d + 2) ≤ NeO d n k := by
  unfold NeO
  have h3 : d + 2 ≤ 15 * 2 ^ (17 + k) * d ^ 3 := by
    have h1 : d ≤ d ^ 3 := Nat.le_self_pow (by norm_num) d
    have h2 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    calc d + 2 ≤ 15 * 1 * d ^ 3 := by omega
      _ ≤ 15 * 2 ^ (17 + k) * d ^ 3 := by gcongr; exact Nat.one_le_two_pow
  calc n * (d + 2) ≤ n ^ 4 * (15 * 2 ^ (17 + k) * d ^ 3) := Nat.mul_le_mul (Nat.le_self_pow (by norm_num) n) h3
    _ = 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := by ring

/-- **PARAM's fields at the unit `2^K`.** -/
theorem fld_unit (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (4 : ℚ) ≤ 2 ^ Ku d n k ∧ (d : ℚ) ≤ 2 ^ Ku d n k ∧ (n : ℚ) ≤ 2 ^ Ku d n k ∧
    ((NeO d n k : ℕ) : ℚ) ≤ 2 ^ Ku d n k ∧ 0 ≤ (parK d n k).eps ∧ |(parK d n k).eps⁻¹| ≤ 2 ^ Ku d n k ∧
    |(parK d n k).lam| ≤ 2 ^ Ku d n k ∧ |(parK d n k).kapc| ≤ 2 ^ Ku d n k ∧ |(parK d n k).nu| ≤ 2 ^ Ku d n k ∧
    ((parK d n k).Lam : ℚ) ≤ 2 ^ Ku d n k ∧ |(parK d n k).A0| ≤ 2 ^ Ku d n k ∧ |(parK d n k).B0| ≤ 2 ^ Ku d n k ∧
    ((parK d n k).Rint : ℚ) ≤ 2 ^ Ku d n k ∧ |(parK d n k).R| ≤ 2 ^ Ku d n k ∧
    ((parK d n k).B : ℚ) ≤ 2 ^ Ku d n k ∧ (parK d n k).p ≤ Ku d n k ∧ 2 * (2 : ℚ) ^ (parK d n k).pF ≤ 2 ^ Ku d n k := by
  obtain ⟨-, hp2, hp3⟩ := pF_ge d n k
  have hlam := lam_bnd d n k hd hn
  have hkap := kapc_bnd d n k hd hn
  have hnu := nu_bnd d n k hd hn
  have hA0 := A0_bnd d n k hd hn
  have hB0 := B0_bnd d n k hd hn
  have hR := R_bnd d n k hd hn
  have he0 := eps_nonneg d n k hd hn
  have heI := eps_inv d n k
  have hLam : ((parK d n k).Lam : ℚ) = d * NeO d n k := by
    show (((d * NeO d n k : ℕ) : ℚ)) = _; push_cast; ring
  have hB : (parK d n k).B = 2 * ((parK d n k).p + (n * (d + 2)).size + 2) := rfl
  have hRint : ((parK d n k).Rint : ℚ) < (parK d n k).R + 1 := Nat.ceil_lt_add_one hR.1
  have hs : (n * (d + 2)).size ≤ leK d n k := Nat.size_le_size (nd2_le_NeO d n k hd)
  have hdl : (d : ℚ) ≤ 2 ^ ld d := by exact_mod_cast (Nat.lt_size_self d).le
  have hnN : (n : ℚ) ≤ NeO d n k := by exact_mod_cast n_le_NeO d n k hd
  have hNe : ((NeO d n k : ℕ) : ℚ) ≤ 2 ^ leK d n k := by exact_mod_cast (NeO_lt d n k).le
  have hle : (leK d n k : ℚ) ≤ 2 ^ leK d n k := by exact_mod_cast Nat.lt_two_pow_self.le
  have hpF : ((parK d n k).pF : ℚ) ≤ 2 ^ (parK d n k).pF := by exact_mod_cast Nat.lt_two_pow_self.le
  have hBQ : ((parK d n k).B : ℚ) ≤ 4 * (parK d n k).pF + 4 := by
    have : (parK d n k).B ≤ 4 * (parK d n k).pF + 4 := by rw [hB]; omega
    exact_mod_cast this
  have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast hd
  unfold Ku
  rw [hLam]
  clear hB hLam
  generalize parK d n k = P at *
  generalize hX : (2 : ℚ) ^ P.pF = X at *
  have hT : (2 : ℚ) ^ (P.pF + 8) = 256 * X := by rw [pow_add, hX]; ring
  have hK : ∀ m, m ≤ P.pF → (2 : ℚ) ^ m ≤ X := fun m h => hX ▸ pow_le_pow_right₀ (by norm_num) h
  have hX1 : (1 : ℚ) ≤ X := hX ▸ one_le_pow₀ (by norm_num)
  rw [hT]
  have ha := hK (ld d) (by omega)
  have hb := hK (leK d n k) (by omega)
  have hab : (2 : ℚ) ^ ld d * 2 ^ leK d n k ≤ X := by rw [← pow_add]; exact hK _ (by omega)
  have ha2 : (2 : ℚ) ^ ld d * 2 ^ ld d ≤ X := by rw [← pow_add]; exact hK _ (by omega)
  have hb0 : (0 : ℚ) ≤ 2 ^ leK d n k := by positivity
  have ha0 : (0 : ℚ) ≤ 2 ^ ld d := by positivity
  have hdd : (d : ℚ) ^ 2 ≤ 2 ^ ld d * 2 ^ ld d := by rw [sq]; exact mul_le_mul hdl hdl (by positivity) ha0
  have hb1 : 2 * (2 : ℚ) ^ leK d n k ≤ X := by rw [← pow_succ']; exact hK _ (by omega)
  have ha4 : 4 * ((2 : ℚ) ^ ld d * 2 ^ ld d) ≤ X := by
    rw [← pow_add, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]; exact hK _ (by omega)
  have hdN : (d : ℚ) * NeO d n k ≤ 2 ^ ld d * 2 ^ leK d n k := mul_le_mul hdl hNe (by positivity) ha0
  refine ⟨by linarith, by linarith, by linarith, by linarith, he0, by linarith, by linarith [hlam],
    by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_, by linarith, by omega, by linarith⟩
  · linarith [hR.2]
  · rw [abs_of_nonneg hR.1]; linarith [hR.2]

theorem size_14 (d n k : ℕ) (hd : 1 ≤ d) : (14 * n * NeO d n k).size ≤ 2 * leK d n k + 4 := by
  apply Nat.size_le.mpr
  have hN := NeO_lt d n k
  have hnN := n_le_NeO d n k hd
  have h1 : 14 * n < 2 ^ 4 * 2 ^ leK d n k := by omega
  calc 14 * n * NeO d n k < 2 ^ 4 * 2 ^ leK d n k * 2 ^ leK d n k := Nat.mul_lt_mul'' h1 hN
    _ = 2 ^ (2 * leK d n k + 4) := by ring

/-- `2^{q_O} ≤ 2^p 2^K` for the clipped reading. -/
theorem qO_le {d : ℕ} (c : CfgO d) (d' n k : ℕ) (hd : 1 ≤ d') (hc : c.par = parK d' n k) (hcn : c.n = n) :
    c.qO ≤ c.par.p + Ku d' n k := by
  unfold CfgO.qO
  rw [hc, hcn]
  apply Nat.add_le_add_left
  apply Nat.clog_le_of_le_pow
  have h1 := Nat.sqrt_le_self (14 * n * (parK d' n k).Ne).size
  have h2 := Nat.sqrt_le_self (2 * (parK d' n k).B)
  have hNe : (parK d' n k).Ne = NeO d' n k := rfl
  have hB : (parK d' n k).B = 2 * ((parK d' n k).p + (n * (d' + 2)).size + 2) := rfl
  have hs := size_14 d' n k hd
  have hs2 : (n * (d' + 2)).size ≤ leK d' n k := Nat.size_le_size (nd2_le_NeO d' n k hd)
  obtain ⟨-, hp2, hp3⟩ := pF_ge d' n k
  have hpF : (parK d' n k).pF ≤ 2 ^ (parK d' n k).pF := Nat.lt_two_pow_self.le
  rw [hNe] at h1 ⊢
  unfold Ku
  rw [pow_add, show (2 : ℕ) ^ 8 = 256 by norm_num]
  clear hNe
  generalize parK d' n k = P at *
  generalize (2 : ℕ) ^ P.pF = X at *
  omega

/-! ## The unit against the work term -/

theorem kDel_le_den {δ : ℚ} (h0 : 0 < δ) : kDel δ ≤ δ.den.size := by
  rw [kDel_eq h0]
  apply Nat.size_le_size
  have hnum : 0 < δ.num := Rat.num_pos.2 h0
  have hn1 : 1 ≤ δ.num.toNat := by omega
  have hd1 : 1 ≤ δ.den := δ.den_pos
  apply Nat.div_le_of_le_mul
  have : δ.den + δ.num.toNat ≤ δ.num.toNat * δ.den + 1 := by nlinarith
  omega

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_pow_le (a m : ℕ) (hm : m ≠ 0) : (a ^ m).size ≤ m * a.size := by
  apply Nat.size_le.mpr
  rw [mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left (Nat.lt_size_self a) hm

/-- `ℓe(k) ≤ k + 3 size d + 4 size n + 22`. -/
theorem leK_le (d n k : ℕ) : leK d n k ≤ k + 3 * d.size + 4 * n.size + 22 := by
  unfold leK NeO
  have h1 := size_mul_le (15 * 2 ^ (17 + k) * d ^ 3) (n ^ 4)
  have h2 := size_mul_le (15 * 2 ^ (17 + k)) (d ^ 3)
  have h3 := size_mul_le 15 (2 ^ (17 + k))
  have h4 := size_pow_le d 3 (by norm_num)
  have h5 := size_pow_le n 4 (by norm_num)
  have h6 : (2 ^ (17 + k)).size = 18 + k := by rw [Nat.size_pow]; ring
  have h7 : (15 : ℕ).size = 4 := by decide
  omega

/-- **`K ≤ 528 W`** at `k = kDel δ`, `W = wU d n δ r0 R0 a`. -/
theorem Ku_le (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (hδ : 0 < δ) :
    Ku d n (kDel δ) ≤ 528 * Unified.ProgO.wU d n δ r0 R0 a := by
  have hk := kDel_le_den hδ
  have hle := leK_le d n (kDel δ)
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  have hden : δ.den.size ≤ Unified.ProgO.sizeN δ r0 R0 a := by
    have e : δ.den.size = BitRAM.len (δ.den : ℤ) := by unfold BitRAM.len; rw [Int.natAbs_natCast]
    rw [e]
    unfold Unified.ProgO.sizeN
    omega
  have hp := (pF_ge d n (kDel δ)).2.2
  rw [parK_p] at hp
  unfold Ku Unified.ProgO.wU
  rw [hp]
  unfold pK ld
  omega

end AdversarialBco.Unified.MagO
