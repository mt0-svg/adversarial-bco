/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Inst
public import AdversarialBco.Bit.PieceA.Maj
public import AdversarialBco.Bit.PieceA.EncR
public import AdversarialBco.Bit.BLBasic

@[expose] public section

/-!
# Piece A: Procedure PARAM as an `EncR`

The leaves of PARAM against the reals: `lnQ` encloses `ln N` within `lnErr` (twice Lemma LOG, `gsm_LLq_err`),
`sqrtDn` and `sqrtUp` enclose the square root (steps 2 and 3). The precisions: `η_e, η_1 ≤
2^{-p-16}`, `2^{-q}(1 + Le) ≤ 2^{-p-18}`, `2^{-pF} 2^40 N_e^2 d^4 ≤ 2^{-p}`. Then `encR d n` reads PARAM's values at
`par d n` and `encR_ok` proves `EncR.OK (encR d n)` in `RunCase`.
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

theorem par_q (d n : ℕ) : (par d n).q = pB d n + 2 * (le d n).size + 24 := rfl

theorem par_pF (d n : ℕ) : (par d n).pF = pB d n + 2 * le d n + 4 * ld d + 40 := rfl

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

theorem size_facts (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    21 ≤ le d n ∧ 3 * ld d + 18 ≤ le d n ∧ NeN d n < 2 ^ le d n ∧ d < 2 ^ ld d ∧ (le d n).size ≤ le d n ∧
      le d n < 2 ^ (le d n).size ∧ (2 * d + 2).size ≤ le d n := by
  obtain ⟨h1, h2⟩ := NeN_ge d n hd hn
  have hN := Nat.lt_size_self (NeN d n)
  have hl1 : 1 ≤ ld d := Nat.size_pos.mpr hd
  have hld : 2 ^ (ld d - 1) ≤ d := Nat.lt_size.mp (by unfold ld at hl1 ⊢; omega)
  refine ⟨?_, ?_, hN, Nat.lt_size_self d, Nat.size_le.mpr Nat.lt_two_pow_self, Nat.lt_size_self _, ?_⟩
  · have h20 : 2 ^ 20 ≤ 2 ^ 20 * d ^ 3 := by
      have : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
      calc 2 ^ 20 = 2 ^ 20 * 1 := by ring
        _ ≤ 2 ^ 20 * d ^ 3 := by gcongr
    have : 20 < (NeN d n).size := Nat.lt_size.mpr (le_trans h20 h1)
    unfold le; omega
  · have h3 : 2 ^ (3 * ld d + 17) ≤ NeN d n := by
      calc 2 ^ (3 * ld d + 17) = 2 ^ 20 * (2 ^ (ld d - 1)) ^ 3 := by
            rw [← pow_mul, ← pow_add]; congr 1; omega
        _ ≤ 2 ^ 20 * d ^ 3 := by gcongr
        _ ≤ NeN d n := h1
    have : 3 * ld d + 17 < (NeN d n).size := Nat.lt_size.mpr h3
    unfold le; omega
  · apply Nat.size_le.mpr
    calc 2 * d + 2 ≤ 4 * d := by omega
      _ ≤ NeN d n := h2
      _ < 2 ^ le d n := hN

/-- `2 s (4q + 1) 2^{p+16} ≤ 2^q` for `s ≤ ℓe`. -/
theorem lnErr_nat (d n s : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hs : s ≤ le d n) :
    2 * s * (4 * (par d n).q + 1) * (2 ^ pB d n * 2 ^ 16) ≤ 2 ^ (par d n).q := by
  obtain ⟨h21, hld, -, -, hls, hlX, -⟩ := size_facts d n hd hn
  rw [par_q] at *
  have hq : 4 * (pB d n + 2 * (le d n).size + 24) + 1 ≤ 128 * le d n := by unfold pB; omega
  set X := 2 ^ (le d n).size with hXd
  have hX : 2 ^ (pB d n + 2 * (le d n).size + 24) = 2 ^ pB d n * 2 ^ 16 * (2 ^ 8 * X * X) := by
    rw [hXd, show pB d n + 2 * (le d n).size + 24 = pB d n + 16 + 8 + (le d n).size + (le d n).size by ring]
    simp only [pow_add]; ring
  rw [hX]
  have h1 : 2 * s * (4 * (pB d n + 2 * (le d n).size + 24) + 1) ≤ 2 ^ 8 * X * X := by
    calc 2 * s * (4 * (pB d n + 2 * (le d n).size + 24) + 1) ≤ 2 * le d n * (128 * le d n) := by gcongr
      _ = 2 ^ 8 * le d n * le d n := by ring
      _ ≤ 2 ^ 8 * X * X := by gcongr
  calc 2 * s * (4 * (pB d n + 2 * (le d n).size + 24) + 1) * (2 ^ pB d n * 2 ^ 16)
      = (2 ^ pB d n * 2 ^ 16) * (2 * s * (4 * (pB d n + 2 * (le d n).size + 24) + 1)) := by ring
    _ ≤ 2 ^ pB d n * 2 ^ 16 * (2 ^ 8 * X * X) := by gcongr

theorem lnErr_le (d n N : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (hN : N.size ≤ le d n) :
    ((lnErr (par d n).q N : ℚ) : ℝ) ≤ u d n / 2 ^ 16 := by
  have h := lnErr_nat d n N.size hd hn hN
  have h' : (2 * N.size * (4 * (par d n).q + 1) * (2 ^ pB d n * 2 ^ 16) : ℝ) ≤ 2 ^ (par d n).q := by
    exact_mod_cast h
  simp only [lnErr, u]
  push_cast
  rw [div_le_iff₀ (by positivity), div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem Le_le_size (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : Le d n ≤ 25 * le d n := by
  obtain ⟨-, -, hN, -⟩ := size_facts d n hd hn
  have hN0 : (0 : ℝ) < Ne d n := by
    unfold Ne NeN; have : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd; positivity
  have hlt : Ne d n < 2 ^ le d n := by unfold Ne; exact_mod_cast hN
  have hlog : Real.log (Ne d n) < le d n * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_lt_log hN0 hlt
  have h2 := Real.log_two_lt_d9
  have hl0 : (0 : ℝ) ≤ le d n := by positivity
  unfold Le; nlinarith

theorem eq_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (2 : ℝ) ^ (par d n).q * (1 + Le d n) ≤ u d n / 2 ^ 18 := by
  obtain ⟨h21, -, -, -, -, hlX, -⟩ := size_facts d n hd hn
  have hL := Le_le_size d n hd hn
  have hX : (2 : ℝ) ^ (par d n).q =
      2 ^ pB d n * 2 ^ 18 * (2 ^ 6 * (2 : ℝ) ^ (le d n).size * (2 : ℝ) ^ (le d n).size) := by
    rw [par_q, show pB d n + 2 * (le d n).size + 24 = pB d n + 18 + 6 + (le d n).size + (le d n).size by ring]
    simp only [pow_add]; ring
  have hlX' : (le d n : ℝ) + 1 ≤ (2 : ℝ) ^ (le d n).size := by exact_mod_cast hlX
  have h21' : (21 : ℝ) ≤ le d n := by exact_mod_cast h21
  set X : ℝ := (2 : ℝ) ^ (le d n).size
  have hXX : (le d n : ℝ) + 1 ≤ X * X := by nlinarith
  have hnum : 1 + Le d n ≤ 2 ^ 6 * X * X := by nlinarith
  have hX0 : 0 < X * X := by positivity
  rw [hX, u]
  calc 1 / (2 ^ pB d n * 2 ^ 18 * (2 ^ 6 * X * X)) * (1 + Le d n)
      ≤ 1 / (2 ^ pB d n * 2 ^ 18 * (2 ^ 6 * X * X)) * (2 ^ 6 * X * X) := by gcongr
    _ = 1 / 2 ^ pB d n / 2 ^ 18 := by
      have : X ≠ 0 := by positivity
      field_simp

theorem eF_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    1 / (2 : ℝ) ^ (par d n).pF * (2 ^ 40 * Ne d n ^ 2 * (d : ℝ) ^ 4) ≤ u d n := by
  obtain ⟨-, -, hN, hdl, -⟩ := size_facts d n hd hn
  have hN' : Ne d n ≤ 2 ^ le d n := by unfold Ne; exact_mod_cast hN.le
  have hd' : (d : ℝ) ≤ 2 ^ ld d := by exact_mod_cast hdl.le
  have hN0 : (0 : ℝ) ≤ Ne d n := by unfold Ne; positivity
  have hX : (2 : ℝ) ^ (par d n).pF = 2 ^ pB d n * (2 ^ 40 * (2 ^ le d n) ^ 2 * (2 ^ ld d) ^ 4) := by
    rw [par_pF]; simp only [pow_add, ← pow_mul]; ring
  rw [hX, u, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have : 2 ^ 40 * Ne d n ^ 2 * (d : ℝ) ^ 4 ≤ 2 ^ 40 * (2 ^ le d n) ^ 2 * (2 ^ ld d) ^ 4 := by gcongr
  have h0 : (0 : ℝ) < 2 ^ pB d n := by positivity
  nlinarith
/-! ## PARAM's values as an `EncR` -/

/-- `L0 = LOGINT_q(N_e)/2^q`, `η_e`, `L1 + η_1`. -/
def L0 (d n : ℕ) : ℚ := lnQ (par d n).q (BLP.Ne d n)
def ee (d n : ℕ) : ℚ := lnErr (par d n).q (BLP.Ne d n)
def l1Q (d n : ℕ) : ℚ := lnQ (par d n).q (2 * d + 2) + lnErr (par d n).q (2 * d + 2)

theorem par_Le (d n : ℕ) : (par d n).Le = 36 * (L0 d n - ee d n) := rfl
theorem par_eps (d n : ℕ) : (par d n).eps = up (par d n).pF (14500 * d * (sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q) *
    (36 * (L0 d n + ee d n)) ^ 5 / sqrtDn (par d n).q n) := rfl
theorem par_lam (d n : ℕ) : (par d n).lam = rnd (par d n).pF (1 / (725 * d * (par d n).Le ^ 2)) := rfl
theorem par_eta (d n : ℕ) :
    (par d n).eta = rnd (par d n).pF (sqrtDn (par d n).q d / ((par d n).Le * sqrtDn (par d n).q n)) := rfl
theorem par_sig2 (d n : ℕ) : (par d n).sig2 = rnd (par d n).pF (1 / (8 * (par d n).Le)) := rfl
theorem par_rho (d n : ℕ) : (par d n).rho = dn (par d n).pF (1450 * d ^ 2 * (par d n).Le ^ 3) := rfl
theorem par_kapc (d n : ℕ) :
    (par d n).kapc = rnd (par d n).pF ((par d n).eta * (par d n).lam / (4 * (1 - (par d n).lam) ^ 2)) := rfl
theorem par_nu (d n : ℕ) : (par d n).nu = rnd (par d n).pF (1 / (1 - (par d n).lam)) := rfl
theorem par_R (d n : ℕ) : (par d n).R = up (par d n).pF (134 * d * sqrtUp (par d n).q (l1Q d n)) := rfl
theorem par_sb (d n : ℕ) :
    (par d n).sb = dn (par d n).pF (1 / ((BLP.Ne d n : ℚ) ^ 2 * (par d n).R * ((par d n).R + 1))) := rfl
theorem par_W (d n : ℕ) :
    (par d n).W = up (par d n).pF ((par d n).R + 4 * d * sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le)) := rfl
theorem par_A0 (d n : ℕ) : (par d n).A0 = rnd (par d n).p (sqrtUp (par d n).q (par d n).sig2) := rfl
theorem par_B0 (d n : ℕ) : (par d n).B0 = rnd (par d n).p (1 / sqrtUp (par d n).q (par d n).sig2) := rfl

/-- PARAM's values at `(d, n)` and their references. -/
noncomputable def encR (d n : ℕ) : EncR where
  d := d
  n := n
  Ne := Ne d n
  Le := Le d n
  la := Real.log (2 * d + 2)
  tp := u d n
  eq := 1 / 2 ^ (par d n).q
  eF := 1 / 2 ^ (par d n).pF
  Lp := (par d n).Le
  Lh := ((36 * (L0 d n + ee d n) : ℚ) : ℝ)
  l1 := l1Q d n
  rd := sqrtDn (par d n).q d
  rn := sqrtDn (par d n).q n
  sR := sqrtUp (par d n).q (l1Q d n)
  sW := sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le)
  sU := sqrtUp (par d n).q (par d n).sig2
  ep := (par d n).eps
  lm := (par d n).lam
  et := (par d n).eta
  sg := (par d n).sig2
  ro := (par d n).rho
  kp := (par d n).kapc
  nu := (par d n).nu
  Rp := (par d n).R
  sb := (par d n).sb
  Wp := (par d n).W
  A0 := (par d n).A0
  B0 := (par d n).B0
theorem encR_ok (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCase d n) : (encR d n).OK := by
  have hR := reg_ok d n hd hn h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLeq : (reg d n).Le = Le d n := bud_Le d n hd hn
  have hL1 : 17467 ≤ Le d n := hLeq ▸ hR.hL1
  have hq1 : 1 ≤ (par d n).q := by rw [par_q]; unfold pB; omega
  have hsz := size_facts d n hd hn
  have hNe1 : 1 ≤ BLP.Ne d n := by
    have := (NeN_ge d n hd hn).2; unfold NeN at this; unfold BLP.Ne; omega
  -- the logarithms
  have hL0 : |(L0 d n : ℝ) - Real.log (Ne d n)| ≤ (ee d n : ℝ) := lnQ_err _ _ hq1 hNe1
  have hee : (ee d n : ℝ) ≤ u d n / 2 ^ 16 := lnErr_le d n _ hd hn le_rfl
  have hL1q : |(lnQ (par d n).q (2 * d + 2) : ℝ) - Real.log (2 * d + 2)| ≤
      (lnErr (par d n).q (2 * d + 2) : ℝ) := by
    have := lnQ_err (par d n).q (2 * d + 2) hq1 (by omega); push_cast at this; exact this
  have he1 : (lnErr (par d n).q (2 * d + 2) : ℝ) ≤ u d n / 2 ^ 16 := lnErr_le d n _ hd hn hsz.2.2.2.2.2.2
  have hLpR : ((par d n).Le : ℝ) = 36 * ((L0 d n : ℝ) - (ee d n : ℝ)) := by rw [par_Le]; push_cast; ring
  have hl1R : ((l1Q d n : ℚ) : ℝ) = (lnQ (par d n).q (2 * d + 2) : ℝ) + (lnErr (par d n).q (2 * d + 2) : ℝ) := by
    unfold l1Q; push_cast; ring
  have hLeR : Le d n = 36 * Real.log (Ne d n) := rfl
  have h9 : u d n / 2 ^ 9 = 128 * (u d n / 2 ^ 16) := by ring
  have h15 : u d n / 2 ^ 15 = 2 * (u d n / 2 ^ 16) := by ring
  obtain ⟨hA1, hA2⟩ := abs_le.mp hL0
  obtain ⟨hB1, hB2⟩ := abs_le.mp hL1q
  have hu0 : 0 < u d n := by unfold u; positivity
  -- the regime fact `Le^4 d n ≤ N_e`
  obtain ⟨hQ17, hQL, hQn, -, -, hQd⟩ := hR.Q_bd
  have hQ1 : (1 : ℝ) ≤ (reg d n).Q := le_trans (by norm_num) hQ17
  have hsm : Le d n ^ 4 * d * n ≤ Ne d n := by
    have hLQ : Le d n ≤ (reg d n).Q := by rw [← hLeq]; linarith
    have hnQ : (n : ℝ) ≤ (reg d n).Q ^ 10 := by
      have : (reg d n).n = n := rfl
      linarith
    have hdQ : (d : ℝ) ≤ (reg d n).Q ^ 3 := hQd
    calc Le d n ^ 4 * d * n ≤ (reg d n).Q ^ 4 * (reg d n).Q ^ 3 * (reg d n).Q ^ 10 := by
          gcongr
      _ = (reg d n).Q ^ 17 := by ring
      _ ≤ (reg d n).Q ^ 40 := pow_le_pow_right₀ hQ1 (by norm_num)
      _ = Ne d n := hR.hQ
  refine
    { hd := hd'
      hn := hn'
      hNe := by show Ne d n = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4; unfold Ne NeN; push_cast; ring
      hLe := hL1
      hsm := hsm
      hla1 := ?_
      hla2 := ?_
      htp0 := hu0
      htp1 := ?_
      heq0 := by show (0 : ℝ) < 1 / 2 ^ (par d n).q; positivity
      heq1 := eq_le d n hd hn
      heF0 := by show (0 : ℝ) < 1 / 2 ^ (par d n).pF; positivity
      heF1 := eF_le d n hd hn
      hLp1 := ?_
      hLp2 := ?_
      hLh1 := ?_
      hLh2 := ?_
      hl1a := ?_
      hl1b := ?_
      hrd0 := one_le_sqrtDn _ (by exact_mod_cast hd)
      hrd1 := ?_
      hrd2 := ?_
      hrn0 := one_le_sqrtDn _ (by exact_mod_cast hn)
      hrn1 := ?_
      hrn2 := ?_
      hsR1 := sqrt_le_sqrtUp _ _
      hsR2 := ?_
      hsW1 := ?_
      hsW2 := ?_
      hsU1 := sqrt_le_sqrtUp _ _
      hsU2 := ?_
      hep1 := ?_
      hep2 := ?_
      hlm := ?_
      het := ?_
      hsg := ?_
      hro1 := ?_
      hro2 := ?_
      hkp := ?_
      hnu := ?_
      hRp1 := ?_
      hRp2 := ?_
      hsb1 := ?_
      hsb2 := ?_
      hWp1 := ?_
      hWp2 := ?_
      hA0 := ?_
      hB0 := ?_ }
  · show 1 ≤ Real.log (2 * (d : ℝ) + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ 2 * d + 1
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d + 2 by positivity)
    linarith
  · show u d n ≤ 1 / 2 ^ 160
    unfold u
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by unfold pB; omega))
  · show Le d n - u d n / 2 ^ 9 ≤ ((par d n).Le : ℝ)
    rw [hLpR, hLeR]; linarith
  · show ((par d n).Le : ℝ) ≤ Le d n
    rw [hLpR, hLeR]; have : (0 : ℝ) ≤ ee d n := le_trans (abs_nonneg _) hL0; linarith
  · show Le d n ≤ ((36 * (L0 d n + ee d n) : ℚ) : ℝ)
    push_cast; rw [hLeR]; linarith
  · show ((36 * (L0 d n + ee d n) : ℚ) : ℝ) ≤ Le d n + u d n / 2 ^ 9
    push_cast; rw [hLeR]; linarith
  · show Real.log (2 * (d : ℝ) + 2) ≤ ((l1Q d n : ℚ) : ℝ)
    rw [hl1R]; linarith
  · show ((l1Q d n : ℚ) : ℝ) ≤ Real.log (2 * (d : ℝ) + 2) + u d n / 2 ^ 15
    rw [hl1R]; linarith
  · show (sqrtDn (par d n).q (d : ℚ) : ℝ) ≤ Real.sqrt (d : ℝ)
    have := sqrtDn_le_sqrt (par d n).q (x := (d : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (d : ℝ) ≤ (sqrtDn (par d n).q (d : ℚ) : ℝ) + 1 / 2 ^ (par d n).q
    have := sqrt_le_sqrtDn_add (par d n).q (d : ℚ); push_cast at this; exact this
  · show (sqrtDn (par d n).q (n : ℚ) : ℝ) ≤ Real.sqrt (n : ℝ)
    have := sqrtDn_le_sqrt (par d n).q (x := (n : ℚ)) (by positivity); push_cast at this; exact this
  · show Real.sqrt (n : ℝ) ≤ (sqrtDn (par d n).q (n : ℚ) : ℝ) + 1 / 2 ^ (par d n).q
    have := sqrt_le_sqrtDn_add (par d n).q (n : ℚ); push_cast at this; exact this
  · show (sqrtUp (par d n).q (l1Q d n) : ℝ) ≤ Real.sqrt ((l1Q d n : ℚ) : ℝ) + 2 * (1 / 2 ^ (par d n).q)
    have := sqrtUp_le (par d n).q (l1Q d n); rw [mul_one_div]; exact this
  · show Real.sqrt (Ne d n / ((par d n).Le : ℝ)) ≤ (sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le) : ℝ)
    have := sqrt_le_sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le); push_cast at this; exact this
  · show (sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le) : ℝ) ≤
      Real.sqrt (Ne d n / ((par d n).Le : ℝ)) + 2 * (1 / 2 ^ (par d n).q)
    have := sqrtUp_le (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le); push_cast at this; rw [mul_one_div]; exact this
  · show (sqrtUp (par d n).q (par d n).sig2 : ℝ) ≤ Real.sqrt ((par d n).sig2 : ℝ) + 2 * (1 / 2 ^ (par d n).q)
    have := sqrtUp_le (par d n).q (par d n).sig2; rw [mul_one_div]; exact this
  · show 14500 * (d : ℝ) * ((sqrtDn (par d n).q (d : ℚ) : ℝ) + 1 / 2 ^ (par d n).q) *
      ((36 * (L0 d n + ee d n) : ℚ) : ℝ) ^ 5 / (sqrtDn (par d n).q (n : ℚ) : ℝ) ≤ ((par d n).eps : ℝ)
    have := le_upR (par d n).pF (14500 * d * (sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q) *
      (36 * (L0 d n + ee d n)) ^ 5 / sqrtDn (par d n).q n)
    rw [← par_eps] at this; push_cast at this ⊢; exact this
  · show ((par d n).eps : ℝ) ≤ 14500 * (d : ℝ) * ((sqrtDn (par d n).q (d : ℚ) : ℝ) + 1 / 2 ^ (par d n).q) *
      ((36 * (L0 d n + ee d n) : ℚ) : ℝ) ^ 5 / (sqrtDn (par d n).q (n : ℚ) : ℝ) + 1 / 2 ^ (par d n).pF
    have := upR_le (par d n).pF (14500 * d * (sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q) *
      (36 * (L0 d n + ee d n)) ^ 5 / sqrtDn (par d n).q n)
    rw [← par_eps] at this; push_cast at this ⊢; exact this
  · show |((par d n).lam : ℝ) - 1 / (725 * (d : ℝ) * ((par d n).Le : ℝ) ^ 2)| ≤ 1 / 2 ^ (par d n).pF / 2
    have := rnd_errR (par d n).pF (1 / (725 * d * (par d n).Le ^ 2))
    rw [← par_lam] at this; push_cast at this; exact this
  · show |((par d n).eta : ℝ) - (sqrtDn (par d n).q (d : ℚ) : ℝ) / (((par d n).Le : ℝ) *
      (sqrtDn (par d n).q (n : ℚ) : ℝ))| ≤ 1 / 2 ^ (par d n).pF / 2
    have := rnd_errR (par d n).pF (sqrtDn (par d n).q d / ((par d n).Le * sqrtDn (par d n).q n))
    rw [← par_eta] at this; push_cast at this; exact this
  · show |((par d n).sig2 : ℝ) - 1 / (8 * ((par d n).Le : ℝ))| ≤ 1 / 2 ^ (par d n).pF / 2
    have := rnd_errR (par d n).pF (1 / (8 * (par d n).Le))
    rw [← par_sig2] at this; push_cast at this; exact this
  · show 1450 * (d : ℝ) ^ 2 * ((par d n).Le : ℝ) ^ 3 - 1 / 2 ^ (par d n).pF ≤ ((par d n).rho : ℝ)
    have := sub_le_dnR (par d n).pF (1450 * d ^ 2 * (par d n).Le ^ 3)
    rw [← par_rho] at this; push_cast at this; exact this
  · show ((par d n).rho : ℝ) ≤ 1450 * (d : ℝ) ^ 2 * ((par d n).Le : ℝ) ^ 3
    have := dnR_le (par d n).pF (1450 * d ^ 2 * (par d n).Le ^ 3)
    rw [← par_rho] at this; push_cast at this; exact this
  · show |((par d n).kapc : ℝ) - ((par d n).eta : ℝ) * ((par d n).lam : ℝ) / (4 * (1 - ((par d n).lam : ℝ)) ^ 2)| ≤
      1 / 2 ^ (par d n).pF / 2
    have := rnd_errR (par d n).pF ((par d n).eta * (par d n).lam / (4 * (1 - (par d n).lam) ^ 2))
    rw [← par_kapc] at this; push_cast at this; exact this
  · show |((par d n).nu : ℝ) - 1 / (1 - ((par d n).lam : ℝ))| ≤ 1 / 2 ^ (par d n).pF / 2
    have := rnd_errR (par d n).pF (1 / (1 - (par d n).lam))
    rw [← par_nu] at this; push_cast at this; exact this
  · show 134 * (d : ℝ) * (sqrtUp (par d n).q (l1Q d n) : ℝ) ≤ ((par d n).R : ℝ)
    have := le_upR (par d n).pF (134 * d * sqrtUp (par d n).q (l1Q d n))
    rw [← par_R] at this; push_cast at this; exact this
  · show ((par d n).R : ℝ) ≤ 134 * (d : ℝ) * (sqrtUp (par d n).q (l1Q d n) : ℝ) + 1 / 2 ^ (par d n).pF
    have := upR_le (par d n).pF (134 * d * sqrtUp (par d n).q (l1Q d n))
    rw [← par_R] at this; push_cast at this; exact this
  · show 1 / (Ne d n ^ 2 * ((par d n).R : ℝ) * (((par d n).R : ℝ) + 1)) - 1 / 2 ^ (par d n).pF ≤ ((par d n).sb : ℝ)
    have := sub_le_dnR (par d n).pF (1 / ((BLP.Ne d n : ℚ) ^ 2 * (par d n).R * ((par d n).R + 1)))
    rw [← par_sb] at this; push_cast at this; exact this
  · show ((par d n).sb : ℝ) ≤ 1 / (Ne d n ^ 2 * ((par d n).R : ℝ) * (((par d n).R : ℝ) + 1))
    have := dnR_le (par d n).pF (1 / ((BLP.Ne d n : ℚ) ^ 2 * (par d n).R * ((par d n).R + 1)))
    rw [← par_sb] at this; push_cast at this; exact this
  · show ((par d n).R : ℝ) + 4 * (d : ℝ) * (sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le) : ℝ) ≤
      ((par d n).W : ℝ)
    have := le_upR (par d n).pF ((par d n).R + 4 * d * sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le))
    rw [← par_W] at this; push_cast at this; exact this
  · show ((par d n).W : ℝ) ≤ ((par d n).R : ℝ) + 4 * (d : ℝ) *
      (sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le) : ℝ) + 1 / 2 ^ (par d n).pF
    have := upR_le (par d n).pF ((par d n).R + 4 * d * sqrtUp (par d n).q ((BLP.Ne d n : ℚ) / (par d n).Le))
    rw [← par_W] at this; push_cast at this; exact this
  · show |((par d n).A0 : ℝ) - (sqrtUp (par d n).q (par d n).sig2 : ℝ)| ≤ u d n / 2
    have := rnd_errR (par d n).p (sqrtUp (par d n).q (par d n).sig2)
    rw [← par_A0] at this; exact this
  · show |((par d n).B0 : ℝ) - 1 / (sqrtUp (par d n).q (par d n).sig2 : ℝ)| ≤ u d n / 2
    have := rnd_errR (par d n).p (1 / sqrtUp (par d n).q (par d n).sig2)
    rw [← par_B0] at this; push_cast at this; exact this
end AdversarialBco.Bit.PieceA
