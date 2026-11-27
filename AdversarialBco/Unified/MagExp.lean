/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.MagField
public import AdversarialBco.Unified.ProgOMag

@[expose] public section

/-!
# The exponent of BL-O's calls: `expBLO : ExpBLO`

The exponent of ELL-O's integer call `clearO D` is that of the rowless problem
`(clearO D).base` (`ellExpO_eq`), whose `θ` is the `θ` of `clearQ D` (`base_theta`: the same objective, accuracy and
radius `R̄ = R_int`) and whose radius is `r/2`, so `1/(θ min(r/2, 1)) ≤ T^16` at the unit `T = 2^{K + E₀}`,
`K = pF + 8` (`fld_unit`), the three pairs (radius, accuracy) bounded by `pair_bndP` (over any PARAM whose `ε'` and
`s_b` are on the grid `2^{-pF}`). The exponent is at most `52 K + 48 E₀ + 8 ≤ 30000 (W + E₀ + 1)`.
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK AdversarialBco.Uni
open AdversarialBco.Bit.BLP (Par CallQ frob2 eBL)
open AdversarialBco.Bit.RQ (EllI clearQ ellExp lgQ)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (InU wU ExpBLO)
open Matrix

variable {d : ℕ}

theorem ellExpO_eq (I : EllOI d) : ellExpO I = ellExp I.base := rfl

theorem base_theta (D : CallQ d) : (clearO D).base.θ = (clearQ D).θ := rfl

theorem base_r (D : CallQ d) : (clearO D).base.r = D.r / 2 := rfl

theorem base_Rb (D : CallQ d) : (clearO D).base.Rb = (clearQ D).Rb := rfl

/-- **`1/e` and `1/r` for BL's three calls**, over a PARAM whose `ε'` and `s_b` are on the grid `2^{-pF}`. -/
theorem pair_bndP (P : Par) (d n : ℕ) {T : ℚ} (hT : 128 ≤ T) (hNe : (P.Ne : ℚ) ≤ T) (hdT : (d : ℚ) ≤ T)
    (hnT : (n : ℚ) ≤ T) (hR : |P.R| ≤ T) (hpF : 2 * (2 : ℚ) ^ P.pF ≤ T) (heps : OnG P.pF P.eps)
    (hsbg : OnG P.pF P.sb) {r e : ℚ} (h : (r, e) ∈ callRE P d n) : 0 ≤ e ∧ |1 / e| ≤ T ^ 7 ∧ |r⁻¹| ≤ T ^ 2 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hp1 : (2 : ℚ) ^ P.pF ≤ T := by
    have : (0 : ℚ) < 2 ^ P.pF := by positivity
    linarith
  have he1 : |(1 - P.eps)⁻¹| ≤ T := (inv_one_sub_grid heps).trans hp1
  have hsb : |P.sb⁻¹| ≤ T := (inv_grid hsbg).trans hp1
  have hNe0 : (0 : ℚ) ≤ P.Ne := Nat.cast_nonneg _
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg _
  have habs : ∀ {x : ℚ}, 0 ≤ x → x ≤ T → |x| ≤ T ^ 1 := fun h0 h1 => by rw [abs_of_nonneg h0, pow_one]; exact h1
  have h8 : |(8 : ℚ)| ≤ T ^ 1 := habs (by norm_num) (by linarith)
  have hNd8 : |(P.Ne : ℚ) * d * 8| ≤ T ^ 3 := bnd_mul (bnd_mul (habs hNe0 hNe) (habs hd0 hdT)) h8
  have hrB : |(Bit.BLP.rB P)⁻¹| ≤ T ^ 2 := by
    unfold Bit.BLP.rB; rw [mul_inv, abs_mul, sq]
    exact mul_le_mul hsb he1 (abs_nonneg _) (by linarith)
  have hsb2 := inv_grid hsbg
  have hrB2 : |(Bit.BLP.rB P / 2)⁻¹| ≤ T ^ 2 := by
    unfold Bit.BLP.rB
    rw [inv_div, div_eq_mul_inv, mul_inv, abs_mul, abs_mul, abs_two, sq]
    calc 2 * (|P.sb⁻¹| * |(1 - P.eps)⁻¹|) = (2 * |P.sb⁻¹|) * |(1 - P.eps)⁻¹| := by ring
      _ ≤ T * T := mul_le_mul (by linarith) he1 (abs_nonneg _) (by linarith)
  simp only [callRE, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by positivity, ?_, bnd_up hT1 (pw1 he1) (by norm_num)⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul (pw1 he1) (pw1 he1))) (by norm_num)
  · refine ⟨by positivity, ?_, hrB2⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul hrB hrB)) (by norm_num)
  · refine ⟨by unfold eBL; positivity, ?_, hrB2⟩
    unfold eBL
    rw [one_div_one_div]
    have h128 : |(128 : ℚ)| ≤ T ^ 1 := habs (by norm_num) hT
    have hn2 : |(n : ℚ) ^ 2| ≤ T ^ 2 := by
      rw [sq]; exact bnd_mul (habs (Nat.cast_nonneg _) hnT) (habs (Nat.cast_nonneg _) hnT)
    have hR2 : |P.R ^ 2| ≤ T ^ 2 := by rw [sq]; exact bnd_mul (pw1 hR) (pw1 hR)
    have h3 : |128 * (n : ℚ) ^ 2| ≤ T ^ 3 := bnd_mul (a := 1) (b := 2) h128 hn2
    have h5 : |128 * (n : ℚ) ^ 2 * P.R ^ 2| ≤ T ^ 5 := bnd_mul (a := 3) (b := 2) h3 hR2
    have h6 : |128 * (n : ℚ) ^ 2 * P.R ^ 2 * d| ≤ T ^ 6 := bnd_mul (a := 5) (b := 1) h5 (habs hd0 hdT)
    exact bnd_mul (a := 1) (b := 6) (habs hNe0 hNe) h6

/-- The exponent from the bounds: `3 j + lg R̄ + lg(d²(d + 1)) + 7 ≤ 30000 (W + E₀ + 1)`. -/
theorem exp_arith (j c1 c2 K E0 W : ℕ) (hj : j ≤ 16 * (K + E0)) (h1 : c1 ≤ K) (h2 : c2 ≤ 3 * K + 1)
    (hK : K ≤ 528 * W) : 3 * j + c1 + c2 + 7 ≤ 30000 * (W + E0 + 1) ^ 1 := by
  rw [pow_one]; omega

/-- **`expBLO`: the exponent of BL-O's calls.** -/
theorem expBLO : ExpBLO := by
  refine ⟨30000, 1, ?_⟩
  intro d n E0 δ r0 R0 a c H g ℓq Bp f r e hI hc _ hfr hf hre
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨hT4, hdT, hnT, hNeT, -, -, -, -, -, hLam, -, -, hRint, hR, -, -, h2pF⟩ := fld_unit d n (kDel δ) hd hn
  have hKW := Ku_le d n δ r0 R0 a hI.hδ0
  have hp := pF_ge d n (kDel δ)
  have hK168 : 168 ≤ Ku d n (kDel δ) := by unfold Ku; omega
  have hheps : OnG (parO d n δ).pF (parO d n δ).eps := by
    show OnG (parK d n (kDel δ)).pF (parK d n (kDel δ)).eps
    rw [parK_eps]; exact onG_up _ _
  have hhsb : OnG (parO d n δ).pF (parO d n δ).sb := by
    show OnG (parK d n (kDel δ)).pF (parK d n (kDel δ)).sb
    rw [parK_sb]; exact onG_dn _ _
  have hNe' : ((parO d n δ).Ne : ℚ) ≤ 2 ^ Ku d n (kDel δ) := hNeT
  have hRint' : ((parO d n δ).Rint : ℚ) ≤ 2 ^ Ku d n (kDel δ) := hRint
  have hR' : |(parO d n δ).R| ≤ 2 ^ Ku d n (kDel δ) := hR
  have h2pF' : 2 * (2 : ℚ) ^ (parO d n δ).pF ≤ 2 ^ Ku d n (kDel δ) := h2pF
  have hLam' : ((parO d n δ).Lam : ℚ) ≤ 2 ^ Ku d n (kDel δ) := hLam
  have hDR : (callO c H g ℓq r (Bp * Bpᵀ) f e).R = ((parO d n δ).Rint : ℚ) := by rw [← hc]; rfl
  have hDP : (callO c H g ℓq r (Bp * Bpᵀ) f e).P = Bp * Bpᵀ := rfl
  have hDf : (callO c H g ℓq r (Bp * Bpᵀ) f e).f = f := rfl
  have hDe : (callO c H g ℓq r (Bp * Bpᵀ) f e).e = e := rfl
  have hDr : (callO c H g ℓq r (Bp * Bpᵀ) f e).r = r := rfl
  clear hNeT hRint hR h2pF hLam hp hc
  generalize callO c H g ℓq r (Bp * Bpᵀ) f e = D at *
  generalize parO d n δ = P at *
  generalize Ku d n (kDel δ) = K at *
  obtain ⟨T, hTdef⟩ : ∃ T : ℚ, T = 2 ^ (K + E0) := ⟨_, rfl⟩
  have hKT : (2 : ℚ) ^ K ≤ T := hTdef ▸ pow_le_pow_right₀ (by norm_num) (by omega)
  have hE0T : (2 : ℚ) ^ E0 ≤ T := hTdef ▸ pow_le_pow_right₀ (by norm_num) (by omega)
  have hT : (128 : ℚ) ≤ T := by
    have : (2 : ℚ) ^ 7 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  obtain ⟨he0, he, hr⟩ := pair_bndP P d n hT (hNe'.trans hKT) (hdT.trans hKT) (hnT.trans hKT)
    (hR'.trans hKT) (h2pF'.trans hKT) hheps hhsb hre
  -- `R̄ = R_int`
  have hRb : (clearQ D).Rb = P.Rint := by
    show ⌈D.R⌉₊ = _
    rw [hDR, Nat.ceil_natCast]
  have hRbT : ((clearQ D).Rb : ℚ) ≤ T := by rw [hRb]; exact hRint'.trans hKT
  have hRb0 : (0 : ℚ) ≤ (clearQ D).Rb := Nat.cast_nonneg _
  -- `tr(P) R̄ + |f|₁ ≤ T^4`
  have hL : abs (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) ≤ T ^ 4 := by
    have htr : D.P.trace = frob2 Bp := by rw [hDP]; exact trace_mul_tr Bp
    have h0 := frob2_nonneg Bp
    have hLam2 : (2 : ℚ) * P.Lam ≤ T ^ 2 := by
      have h1 : (P.Lam : ℚ) ≤ T := hLam'.trans hKT
      calc (2 : ℚ) * P.Lam ≤ T * T := mul_le_mul hT2 h1 (Nat.cast_nonneg _) (by linarith)
        _ = T ^ 2 := by ring
    have hf1 : abs (∑ i, |D.f i|) ≤ T ^ 3 := by
      rw [hDf]
      have hs : ∑ i, |f i| ≤ d * 2 ^ E0 := by
        calc ∑ i, |f i| ≤ ∑ _i : Fin d, (2 : ℚ) ^ E0 := Finset.sum_le_sum fun i _ => hf i
          _ = d * 2 ^ E0 := by simp
      rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      calc ∑ i, |f i| ≤ d * 2 ^ E0 := hs
        _ ≤ T * T := mul_le_mul (hdT.trans hKT) hE0T (by positivity) (by linarith)
        _ ≤ T * T * T := le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hT1
        _ = T ^ 3 := by ring
    have hP : |D.P.trace * (clearQ D).Rb| ≤ T ^ 3 := by
      rw [htr, abs_of_nonneg (mul_nonneg h0 hRb0), pow_succ]
      exact mul_le_mul (hfr.trans hLam2) hRbT hRb0 (pow_nonneg (by linarith) _)
    exact bnd_add hT2 hP hf1
  have hθ := invθ_le D (by linarith) hL hRbT (by rw [hDe]; exact he)
  rw [← base_theta] at hθ
  have hr2 : |(clearO D).base.r⁻¹| ≤ T ^ 3 := by
    rw [base_r, hDr, inv_div, div_eq_mul_inv, abs_mul, abs_two, pow_succ]
    have h2 : (0 : ℚ) ≤ T ^ 2 := by positivity
    nlinarith [abs_nonneg r⁻¹]
  have hX := X_le (clearO D).base hT1 hθ hr2
  have hj : (clearO D).base.j ≤ 16 * (K + E0) := by
    apply lgQ_le
    rw [pow_mul', ← hTdef]
    exact hX.trans (pow_le_pow_right₀ hT1 (by norm_num))
  have hc1 : Nat.clog 2 (clearO D).base.Rb ≤ K := by
    rw [base_Rb, hRb]
    apply Nat.clog_le_of_le_pow
    exact_mod_cast hRint'
  have hc2 : Nat.clog 2 (d ^ 2 * (d + 1)) ≤ 3 * K + 1 := by
    apply Nat.clog_le_of_le_pow
    have h1 : d ≤ 2 ^ K := by exact_mod_cast hdT
    have h2 : d + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := K); omega
    calc d ^ 2 * (d + 1) ≤ (2 ^ K) ^ 2 * 2 ^ (K + 1) := Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) h2
      _ = 2 ^ (3 * K + 1) := by rw [← pow_mul, ← pow_add]; ring_nf
  rw [ellExpO_eq]
  exact (ellExp_le _).trans (exp_arith _ _ _ K E0 _ hj hc1 hc2 hKW)

end AdversarialBco.Unified.MagO
