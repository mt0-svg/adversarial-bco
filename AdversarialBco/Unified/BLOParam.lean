/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOSpec
public import AdversarialBco.Unified.LeafFrozen

@[expose] public section

/-!
# BL-O: the confidence, the schedule, the clipped reading and the play's shift

Proofs of the `Prop`s of Unified/BLOSpec.lean that need only the parameters and real arithmetic:

* `deltaO_holds : DeltaO` (UNI-DELTA): `1/δ < 2^{k_δ} ≤ 4/δ`, BL-O's confidence
  `δ_BL = 2^{-19-k_δ}/(dn)³` below `2^{-19} δ/(dn)³`, `N_e δ_BL = 15n/4` (BL's), `log(2dn/δ_BL) ≤ 22 log(2dn/δ)`
  (the route's `21` is for `⌈log₂(1/δ)⌉`; the bit length of `⌈1/δ⌉` exceeds it by one at powers of two), and the
  integer form of `k_δ`;
* `schedOKO : SchedOKO`: the layout is a schedule of the extension;
* `obsClipO : ObsClipO` (UNI-OBS, Sec. 3.10): the range `qO` covers `4 + 4 (ln(14 n N_e))^{1/2} + (2B)^{1/2}`;
* `playRatioO : PlayRatioO`, `playMeanO : PlayMeanO` (UNI-PLAY, Sec. 3.6 with m5's corrected display);
* `tau_shift`: E17's form `τ(m, r) ≤ 2(|r - 1| + |μ|) + 2|r - 1||ε|` for `m = (r - 1)ε + μ`, `r ≥ 1/2`.
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Uni

variable {d : ℕ}

/-! ## UNI-DELTA -/

theorem one_lt_inv_rat {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) : (1 : ℚ) < δ⁻¹ := (one_lt_inv₀ h0).2 h1

/-- `1/δ < 2^{k_δ} ≤ 4/δ`. -/
theorem kDel_bounds {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) :
    1 / (δ : ℝ) < 2 ^ kDel δ ∧ (2 : ℝ) ^ kDel δ ≤ 4 / δ := by
  have hNge : (δ⁻¹ : ℚ) ≤ ⌈δ⁻¹⌉₊ := Nat.le_ceil _
  have hNlt : (⌈δ⁻¹⌉₊ : ℚ) < δ⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlt : ⌈δ⁻¹⌉₊ < 2 ^ (⌈δ⁻¹⌉₊).size := Nat.lt_size_self _
  have hi := one_lt_inv_rat h0 h1
  have hN1 : 1 ≤ ⌈δ⁻¹⌉₊ := by
    have : (1 : ℚ) ≤ ⌈δ⁻¹⌉₊ := by linarith
    exact_mod_cast this
  have hpos : 0 < (⌈δ⁻¹⌉₊).size := Nat.size_pos.2 (by omega)
  have hle : 2 ^ ((⌈δ⁻¹⌉₊).size - 1) ≤ ⌈δ⁻¹⌉₊ := Nat.lt_size.1 (by omega)
  have hD0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hD1 : (δ : ℝ) < 1 := by exact_mod_cast h1
  have hinv : ((δ⁻¹ : ℚ) : ℝ) = 1 / (δ : ℝ) := by push_cast; ring
  unfold kDel
  generalize hN : ⌈δ⁻¹⌉₊ = N at hNge hNlt hlt hN1 hpos hle
  have hNgeR : 1 / (δ : ℝ) ≤ N := by rw [← hinv]; exact_mod_cast hNge
  have hNltR : (N : ℝ) < 1 / (δ : ℝ) + 1 := by rw [← hinv]; exact_mod_cast hNlt
  have hltR : (N : ℝ) < 2 ^ N.size := by exact_mod_cast hlt
  have hleR : (2 : ℝ) ^ (N.size - 1) ≤ N := by exact_mod_cast hle
  refine ⟨hNgeR.trans_lt hltR, ?_⟩
  have hs : (2 : ℝ) ^ N.size = 2 * 2 ^ (N.size - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1d : 1 < 1 / (δ : ℝ) := by rw [lt_div_iff₀ hD0]; linarith
  have : 4 / (δ : ℝ) = 2 * (1 / δ) + 2 * (1 / δ) := by ring
  rw [hs, this]
  linarith

/-- The integer form of `k_δ`: the bit length of `(den + num - 1)/num = ⌈den/num⌉`. -/
theorem kDel_eq {δ : ℚ} (h0 : 0 < δ) : kDel δ = ((δ.den + δ.num.toNat - 1) / δ.num.toNat).size := by
  have hnum : 0 < δ.num := Rat.num_pos.2 h0
  set b := δ.num.toNat with hb
  set a := δ.den with ha
  have hb0 : 0 < b := by omega
  have hbq : ((b : ℕ) : ℚ) = (δ.num : ℚ) := by
    rw [hb]; exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hinv : δ⁻¹ = (a : ℚ) / (b : ℚ) := by
    rw [hbq, ha]
    conv_lhs => rw [← Rat.num_div_den δ]
    rw [inv_div]
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb0
  unfold kDel
  congr 1
  rw [hinv]
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hbQ]
    have h := Nat.div_add_mod (a + b - 1) b
    have hr := Nat.mod_lt (a + b - 1) hb0
    have : a ≤ (a + b - 1) / b * b := by
      have := Nat.mul_comm b ((a + b - 1) / b)
      omega
    exact_mod_cast this
  · have hc : (a : ℚ) / b ≤ ⌈(a : ℚ) / b⌉₊ := Nat.le_ceil _
    have hca : a ≤ b * ⌈(a : ℚ) / b⌉₊ := by
      have : (a : ℚ) ≤ b * ⌈(a : ℚ) / b⌉₊ := by
        rw [div_le_iff₀ hbQ] at hc; linarith
      exact_mod_cast this
    have h := Nat.div_add_mod (a + b - 1) b
    have hr := Nat.mod_lt (a + b - 1) hb0
    by_contra hlt
    push Not at hlt
    have : b * (⌈(a : ℚ) / b⌉₊ + 1) ≤ b * ((a + b - 1) / b) := Nat.mul_le_mul_left b hlt
    rw [mul_add, mul_one] at this
    omega

theorem deltaO_pos (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < deltaO d n k := by
  unfold deltaO
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- **UNI-DELTA.** -/
theorem deltaO_holds : DeltaO := by
  intro d n δ hd hn h0 h1
  obtain ⟨hk1, hk4⟩ := kDel_bounds h0 h1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD0 : (0 : ℝ) < δ := by exact_mod_cast h0
  have hD1 : (δ : ℝ) < 1 := by exact_mod_cast h1
  have hx : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have hx0 : (0 : ℝ) < (d : ℝ) * n := by linarith
  set k := kDel δ with hkdef
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hinvk : (2 : ℝ)⁻¹ ^ k = 1 / 2 ^ k := by rw [inv_pow, one_div]
  refine ⟨hk1, hk4, ?_, ?_, ?_, kDel_eq h0⟩
  · -- `δ_BL ≤ 2^{-19} δ/(dn)³`
    unfold deltaO
    rw [pow_add, hinvk]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 1 / (2 : ℝ) ^ k ≤ δ := by
      rw [div_le_iff₀ h2k]
      rw [div_lt_iff₀ hD0] at hk1
      linarith
    have h19 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 19 := by positivity
    exact mul_le_mul_of_nonneg_left this h19
  · -- `N_e δ_BL = 15 n/4`
    unfold NeO deltaO
    push_cast
    rw [pow_add, pow_add, hinvk]
    field_simp
    ring
  · -- `log(2dn/δ_BL) ≤ 22 log(2dn/δ)`
    have e : 2 * (d : ℝ) * n / deltaO d n k = 2 ^ 20 * 2 ^ k * ((d : ℝ) * n) ^ 4 := by
      unfold deltaO
      rw [pow_add, hinvk]
      field_simp
    have hlp := Real.log_pow (2 * (d : ℝ) * n / δ) 22
    push_cast at hlp
    rw [e, ← hlp]
    apply Real.log_le_log (by positivity)
    have hδ22 : (δ : ℝ) ^ 22 ≤ δ := pow_le_of_le_one hD0.le hD1.le (by norm_num)
    have hx22 : ((d : ℝ) * n) ^ 4 ≤ ((d : ℝ) * n) ^ 22 := pow_le_pow_right₀ hx (by norm_num)
    calc (2 : ℝ) ^ 20 * 2 ^ k * ((d : ℝ) * n) ^ 4 ≤ 2 ^ 20 * (4 / δ) * ((d : ℝ) * n) ^ 4 := by gcongr
      _ = 2 ^ 22 * ((d : ℝ) * n) ^ 4 / δ := by ring
      _ ≤ 2 ^ 22 * ((d : ℝ) * n) ^ 22 / δ ^ 22 :=
          div_le_div₀ (by positivity) (by gcongr) (by positivity) hδ22
      _ = (2 * d * n / δ) ^ 22 := by ring

/-! ## The schedule -/

theorem parN_B_pos (ne d n : ℕ) : 0 < (parN ne d n).B := by
  unfold parN; dsimp only; omega

theorem parO_B_pos (d n : ℕ) (δ : ℚ) : 0 < (parO d n δ).B := parN_B_pos _ _ _

/-- **The schedule**: `0 < B`, `K0O = 2 B P0O`, the windows `winL`, `winN`. -/
theorem schedOKO : SchedOKO := fun d n δ r0 R0 _ =>
  ⟨parO_B_pos d n δ, ⟨P0O d n δ r0 R0, rfl⟩, rfl, rfl⟩

/-- The prologue blocks hold the coins of the position: `m_st L' ≤ K0O`. -/
theorem LposO_le_K0O (d n : ℕ) (δ r0 R0 : ℚ) : LposO d n δ r0 R0 ≤ K0O d n δ r0 R0 := by
  unfold K0O P0O
  have hB := parO_B_pos d n δ
  generalize LposO d n δ r0 R0 = L
  generalize (parO d n δ).B = B at hB ⊢
  have hm : 0 < 2 * B := by omega
  have h := Nat.div_add_mod (L + 2 * B - 1) (2 * B)
  have hr := Nat.mod_lt (L + 2 * B - 1) hm
  have := Nat.mul_comm (2 * B) ((L + 2 * B - 1) / (2 * B))
  omega

/-! ## UNI-OBS -/

theorem sqrt_le_isqrt_succ (m : ℕ) : Real.sqrt m ≤ Nat.sqrt m + 1 := by
  rw [Real.sqrt_le_left (by positivity)]
  have h : m < (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
  have : (m : ℝ) < ((Nat.sqrt m : ℕ) + 1 : ℝ) ^ 2 := by exact_mod_cast h
  linarith

theorem log_le_size (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ N.size := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : (N : ℝ) < 2 ^ N.size := by exact_mod_cast Nat.lt_size_self N
  have h1 : Real.log N ≤ Real.log (2 ^ N.size) := Real.log_le_log hN0 hlt.le
  rw [Real.log_pow] at h1
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h3 : (0 : ℝ) ≤ N.size := by positivity
  nlinarith

/-- **UNI-OBS**: the range `qO` covers the bound of the route's Sec. 3.10, so the clip does not act on such a
feedback. -/
theorem obsClipO : ObsClipO := by
  intro d c o hn hNe ho
  apply uni_clip_readO
  set N := 14 * c.n * c.par.Ne with hNdef
  have hN1 : 1 ≤ N := by
    have : 1 ≤ 14 * c.n := by omega
    exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  have hlogN : Real.log (14 * (c.n : ℝ) * c.par.Ne) = Real.log (N : ℝ) := by rw [hNdef]; push_cast; ring_nf
  have hl : Real.log (N : ℝ) ≤ N.size := log_le_size N hN1
  have hs1 : Real.sqrt (Real.log (N : ℝ)) ≤ Nat.sqrt N.size + 1 :=
    (Real.sqrt_le_sqrt hl).trans (sqrt_le_isqrt_succ _)
  have hs2 : Real.sqrt (2 * (c.par.B : ℝ)) ≤ Nat.sqrt (2 * c.par.B) + 1 := by
    have := sqrt_le_isqrt_succ (2 * c.par.B); push_cast at this; exact this
  set M := 9 + 4 * Nat.sqrt N.size + Nat.sqrt (2 * c.par.B) with hM
  have hoM : |o| ≤ M := by
    rw [hlogN] at ho
    rw [hM]; push_cast
    linarith
  have hMp : (M : ℝ) ≤ 2 ^ Nat.clog 2 M := by exact_mod_cast Nat.le_pow_clog (by norm_num) M
  have hq : c.qO = c.par.p + Nat.clog 2 M := rfl
  rw [hq, pow_add]
  have : (0 : ℝ) < 2 ^ c.par.p := by positivity
  exact mul_le_mul_of_nonneg_left (hoM.trans hMp) this.le

/-! ## UNI-PLAY -/

/-- E17's form: for the shift `m = (r - 1) ε + μ` with `r ≥ 1/2`, `τ(m, r) = (|r - 1| + |m|)/min(r, 1)` is at most
`2(|r - 1| + |μ|) + 2|r - 1||ε|`, so `τ_1 = 2 sup|r - 1|` (the route's `4 sup|r - 1|` is a majorant). -/
theorem tau_shift (r ε μ : ℝ) (hr : 1 / 2 ≤ r) :
    (|r - 1| + |(r - 1) * ε + μ|) / min r 1 ≤ 2 * (|r - 1| + |μ|) + 2 * |r - 1| * |ε| := by
  have hm : 1 / 2 ≤ min r 1 := le_min hr (by norm_num)
  have hm0 : 0 < min r 1 := by linarith
  have hnum : |r - 1| + |(r - 1) * ε + μ| ≤ |r - 1| + |μ| + |r - 1| * |ε| := by
    have := abs_add_le ((r - 1) * ε) μ
    rw [abs_mul] at this; linarith
  rw [div_le_iff₀ hm0]
  have h0 : 0 ≤ |r - 1| + |μ| + |r - 1| * |ε| := by positivity
  nlinarith

end AdversarialBco.Unified.BLO
