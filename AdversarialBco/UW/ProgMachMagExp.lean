/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachMagDefs
public import AdversarialBco.Unified.MagExp

@[expose] public section

/-!
# The exponent of BL-OW's calls: `expBLW : ExpBLW`

The exponent of BL-O (Unified/MagExp.lean) at BL-OW: the parameters are `parOW d n δ` in place of `parO d n δ`. The two
agree on every field the proof reads (`p`, `pF`, `Ne`, `R`, `sb`, `Rint`, `Lam`, `B`, by `rfl`: `parOW_p`, `parOW_pF`,
`parOW_Ne`, `parOW_R`, `parOW_sb`, `parOW_Lam`). Only `eps` differs: `parOW_eps` writes it as an upward rounding at
precision `pF`, which lies on the grid of precision `pF` (`onG_up`), the hypothesis `pair_bndP` needs. The grid fact for
`sb` is `parO`'s (`parK_sb`, `onG_dn`). The unit `K = Ku d n (kDel δ)` and the constants `30000` and `1` are those of
BL-O's exponent.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK AdversarialBco.Uni
open AdversarialBco.Bit.BLP (Par CallQ frob2 eBL)
open AdversarialBco.Bit.RQ (EllI clearQ ellExp lgQ)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (InU wU)
open AdversarialBco.UW.BLOW (parOW parOW_eps parOW_pF parOW_sb)
open Matrix

/-- **`expBLW`: the exponent of BL-OW's calls.** The exponent of BL-O with the parameters `parOW`. -/
theorem expBLW : ExpBLW := by
  refine ⟨30000, 1, ?_⟩
  intro d n E0 δ r0 R0 a c H g ℓq Bp f r e hI hc _ hfr hf hre
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨hT4, hdT, hnT, hNeT, -, -, -, -, -, hLam, -, -, hRint, hR, -, -, h2pF⟩ :=
    Unified.MagO.fld_unit d n (kDel δ) hd hn
  have hKW := Unified.MagO.Ku_le d n δ r0 R0 a hI.hδ0
  have hp := Unified.MagO.pF_ge d n (kDel δ)
  have hK168 : 168 ≤ Unified.MagO.Ku d n (kDel δ) := by unfold Unified.MagO.Ku; omega
  have hheps : OnG (parOW d n δ).pF (parOW d n δ).eps := by
    rw [parOW_eps, parOW_pF]; exact onG_up _ _
  have hhsb : OnG (parOW d n δ).pF (parOW d n δ).sb := by
    rw [parOW_pF, parOW_sb]
    show OnG (parK d n (kDel δ)).pF (parK d n (kDel δ)).sb
    rw [parK_sb]; exact onG_dn _ _
  have hNe' : ((parOW d n δ).Ne : ℚ) ≤ 2 ^ Unified.MagO.Ku d n (kDel δ) := hNeT
  have hRint' : ((parOW d n δ).Rint : ℚ) ≤ 2 ^ Unified.MagO.Ku d n (kDel δ) := hRint
  have hR' : |(parOW d n δ).R| ≤ 2 ^ Unified.MagO.Ku d n (kDel δ) := hR
  have h2pF' : 2 * (2 : ℚ) ^ (parOW d n δ).pF ≤ 2 ^ Unified.MagO.Ku d n (kDel δ) := h2pF
  have hLam' : ((parOW d n δ).Lam : ℚ) ≤ 2 ^ Unified.MagO.Ku d n (kDel δ) := hLam
  have hDR : (callO c H g ℓq r (Bp * Bpᵀ) f e).R = ((parOW d n δ).Rint : ℚ) := by rw [← hc]; rfl
  have hDP : (callO c H g ℓq r (Bp * Bpᵀ) f e).P = Bp * Bpᵀ := rfl
  have hDf : (callO c H g ℓq r (Bp * Bpᵀ) f e).f = f := rfl
  have hDe : (callO c H g ℓq r (Bp * Bpᵀ) f e).e = e := rfl
  have hDr : (callO c H g ℓq r (Bp * Bpᵀ) f e).r = r := rfl
  clear hNeT hRint hR h2pF hLam hp hc
  generalize callO c H g ℓq r (Bp * Bpᵀ) f e = D at *
  generalize parOW d n δ = P at *
  generalize Unified.MagO.Ku d n (kDel δ) = K at *
  obtain ⟨T, hTdef⟩ : ∃ T : ℚ, T = 2 ^ (K + E0) := ⟨_, rfl⟩
  have hKT : (2 : ℚ) ^ K ≤ T := hTdef ▸ pow_le_pow_right₀ (by norm_num) (by omega)
  have hE0T : (2 : ℚ) ^ E0 ≤ T := hTdef ▸ pow_le_pow_right₀ (by norm_num) (by omega)
  have hT : (128 : ℚ) ≤ T := by
    have : (2 : ℚ) ^ 7 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  obtain ⟨he0, he, hr⟩ := Unified.MagO.pair_bndP P d n hT (hNe'.trans hKT) (hdT.trans hKT) (hnT.trans hKT)
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
  rw [← Unified.MagO.base_theta] at hθ
  have hr2 : |(clearO D).base.r⁻¹| ≤ T ^ 3 := by
    rw [Unified.MagO.base_r, hDr, inv_div, div_eq_mul_inv, abs_mul, abs_two, pow_succ]
    have h2 : (0 : ℚ) ≤ T ^ 2 := by positivity
    nlinarith [abs_nonneg r⁻¹]
  have hX := X_le (clearO D).base hT1 hθ hr2
  have hj : (clearO D).base.j ≤ 16 * (K + E0) := by
    apply lgQ_le
    rw [pow_mul', ← hTdef]
    exact hX.trans (pow_le_pow_right₀ hT1 (by norm_num))
  have hc1 : Nat.clog 2 (clearO D).base.Rb ≤ K := by
    rw [Unified.MagO.base_Rb, hRb]
    apply Nat.clog_le_of_le_pow
    exact_mod_cast hRint'
  have hc2 : Nat.clog 2 (d ^ 2 * (d + 1)) ≤ 3 * K + 1 := by
    apply Nat.clog_le_of_le_pow
    have h1 : d ≤ 2 ^ K := by exact_mod_cast hdT
    have h2 : d + 1 ≤ 2 ^ (K + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := K); omega
    calc d ^ 2 * (d + 1) ≤ (2 ^ K) ^ 2 * 2 ^ (K + 1) := Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) h2
      _ = 2 ^ (3 * K + 1) := by rw [← pow_mul, ← pow_add]; ring_nf
  rw [Unified.MagO.ellExpO_eq]
  exact (ellExp_le _).trans (Unified.MagO.exp_arith _ _ _ K E0 _ hj hc1 hc2 hKW)

end AdversarialBco.UW.ProgW
