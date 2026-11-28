/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.BudEncW
public import AdversarialBco.UW.BudEncU
public import AdversarialBco.UW.ProgRec

@[expose] public section

/-!
# Lemma ENC-W

PARAM-W's values `parOW d n δ` against the reference of Theorem UW at PARAM-W's
own scaling and thresholds (`refW d n δ`, so `u = u'`) and against the level constants of `regW d n k_δ (refW d n δ)`,
with the bounds of Theorem U's Lemma ENC (`EncOK`, Unified/BudDefs.lean). The floor fields (`L`, `λ`, `σ²`, `ρ`, `ν`,
`A_0`, `B_0`) come from `encF` (UW/BudEncW.lean) and Theorem U's enclosures over `EncR`; `ε`, `η`, `κ_c`, which read
the root `r_u` of `u'`, from UW/BudEncU.lean; the level fields (`R`, `s_b`, `W`, `Λ`, `N_e`) from `encR_okW`.
-/

namespace AdversarialBco.UW.BudW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (lnQ lnErr sqrtDn sqrtUp rnd up dn)
open AdversarialBco.Bit.PieceA (sqrtDn_le_sqrt sqrt_le_sqrtDn_add one_le_sqrtDn rnd_errR le_upR upR_le)
open AdversarialBco.Unified.BudR (EncR)
open AdversarialBco.UW
open AdversarialBco.UW.BLOW (n0O lf0 lf1 parOW uOW ruOW refW poW)

/-- **Lemma ENC-W** at `(d, n, δ)`, `k = k_δ`, `ρ = refW d n δ`: the bounds of `EncOK` for `parOW d n δ` against
`regW d n k ρ` (the parameters of T4U at `u'`, the level caps) and `poW d n δ = parW d n u'`. -/
structure EncOKW (d n : ℕ) (δ : ℚ) : Prop where
  Lf_le : ((parOW d n δ).Le : ℝ) ≤ (regW d n (kDel δ) (refW d n δ)).Lf
  Lf_rel : |((parOW d n δ).Le : ℝ) / (regW d n (kDel δ) (refW d n δ)).Lf - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  eps_le : (regW d n (kDel δ) (refW d n δ)).eps ≤ (parOW d n δ).eps
  eps_rel : ((parOW d n δ).eps : ℝ) ≤
    (regW d n (kDel δ) (refW d n δ)).eps * (1 + (regW d n (kDel δ) (refW d n δ)).tp / 16)
  lam_rel : |((parOW d n δ).lam : ℝ) / (regW d n (kDel δ) (refW d n δ)).lam - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  eta_rel : |((parOW d n δ).eta : ℝ) / (regW d n (kDel δ) (refW d n δ)).eta - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  sig2_rel : |((parOW d n δ).sig2 : ℝ) / (poW d n δ).sig2 - 1| ≤ (regW d n (kDel δ) (refW d n δ)).tp / 16
  rho_le : ((parOW d n δ).rho : ℝ) ≤ (regW d n (kDel δ) (refW d n δ)).rho
  rho_rel : |((parOW d n δ).rho : ℝ) / (regW d n (kDel δ) (refW d n δ)).rho - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  kapc_rel : |((parOW d n δ).kapc : ℝ) / (regW d n (kDel δ) (refW d n δ)).kc - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  nu_rel : |((parOW d n δ).nu : ℝ) * (1 - (regW d n (kDel δ) (refW d n δ)).lam) - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  R_le : (regW d n (kDel δ) (refW d n δ)).R ≤ (parOW d n δ).R
  R_rel : |((parOW d n δ).R : ℝ) / (regW d n (kDel δ) (refW d n δ)).R - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  sb_le : ((parOW d n δ).sb : ℝ) ≤ (regW d n (kDel δ) (refW d n δ)).de ^ 2 /
    ((regW d n (kDel δ) (refW d n δ)).R * ((regW d n (kDel δ) (refW d n δ)).R + 1))
  sb_rel : |((parOW d n δ).sb : ℝ) / ((regW d n (kDel δ) (refW d n δ)).de ^ 2 /
    ((regW d n (kDel δ) (refW d n δ)).R * ((regW d n (kDel δ) (refW d n δ)).R + 1))) - 1| ≤
      (regW d n (kDel δ) (refW d n δ)).tp / 16
  W_le : (regW d n (kDel δ) (refW d n δ)).W0 ≤ (parOW d n δ).W
  W_rel : |((parOW d n δ).W : ℝ) / (regW d n (kDel δ) (refW d n δ)).W0 - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp / 16
  A0 : |((parOW d n δ).A0 : ℝ) / Real.sqrt (poW d n δ).sig2 - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp * Real.sqrt (8 * (regW d n (kDel δ) (refW d n δ)).Lf) +
      (regW d n (kDel δ) (refW d n δ)).tp / 16
  B0 : |((parOW d n δ).B0 : ℝ) * Real.sqrt (poW d n δ).sig2 - 1| ≤
    (regW d n (kDel δ) (refW d n δ)).tp + (regW d n (kDel δ) (refW d n δ)).tp / 16
  Lam_eq : ((parOW d n δ).Lam : ℝ) = (regW d n (kDel δ) (refW d n δ)).Lam
  Ne_eq : ((parOW d n δ).Ne : ℝ) = (regW d n (kDel δ) (refW d n δ)).Ne

/-- `u' ≤ n` in the regime: `ε(u') ≤ 1/4` gives `58000² d³ L_f^10 u' ≤ n`. -/
theorem u_le_n {d n : ℕ} {ρ : RefW} (hρ : RegimeW d n ρ) : ρ.u ≤ n := by
  have hu := hρ.hu
  have hLf := regW_Le hρ.hd hρ.hn hu hρ.heps
  have h := hρ.heps
  rw [parW_eps, Bit.PieceA.eps] at h
  have h' : 14500 * (d : ℝ) * Real.sqrt d * Bit.PieceA.Le d n ^ 5 * Real.sqrt ρ.u / Real.sqrt n ≤ 1 / 4 := by
    have e : 14500 * (d : ℝ) * Real.sqrt d * Bit.PieceA.Le d n ^ 5 * Real.sqrt ρ.u / Real.sqrt n =
        14500 * d * Real.sqrt d * Bit.PieceA.Le d n ^ 5 / Real.sqrt n * Real.sqrt ρ.u := by ring
    rw [e]; exact h
  have hn := n_ge_of_epsW d n (Bit.PieceA.Le d n) ρ.u hρ.hn (by linarith) h' (by linarith)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hρ.hd
  have h1 : (1 : ℝ) ≤ (58000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Bit.PieceA.Le d n ^ 10 := by
    have a : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd'
    have b : (1 : ℝ) ≤ Bit.PieceA.Le d n ^ 10 := one_le_pow₀ (by linarith)
    have c : (1 : ℝ) ≤ (58000 : ℝ) ^ 2 := by norm_num
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul c a zero_le_one (by positivity)) b zero_le_one (by positivity)
  have : ρ.u ≤ (58000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Bit.PieceA.Le d n ^ 10 * ρ.u :=
    le_mul_of_one_le_left (by linarith) h1
  linarith

/-- **Lemma ENC-W**: in the regime of PARAM-W's reference. -/
theorem encOKW (d n : ℕ) (δ : ℚ) (hρ : RegimeW d n (refW d n δ)) : EncOKW d n δ := by
  set k := kDel δ with hk
  set ρ := refW d n δ with hρdef
  have hd := hρ.hd
  have hn := hρ.hn
  have hF := encF_ok d n δ ρ hρ
  have hG := encR_okW d n k ρ hρ
  set r := regW d n k ρ with hr
  have htp : r.tp = Unified.BudK.tp d n k := rfl
  have hu0 : 0 < r.tp := by rw [htp, tp_eq]; positivity
  have w16 : r.tp / 2 ^ 16 ≤ r.tp / 16 := div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num)
  have hu1 : (1 : ℝ) ≤ ρ.u := hρ.hu
  have huR : ρ.u = (uOW d n δ : ℝ) := rfl
  have hsu0 : 0 < Real.sqrt ρ.u := Real.sqrt_pos.mpr (by linarith)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- the root of `u'`
  have huQ : (1 : ℚ) ≤ uOW d n δ := by
    have h := hu1
    rw [huR] at h
    exact_mod_cast h
  have hru1 : (1 : ℝ) ≤ (ruOW d n δ : ℝ) := one_le_sqrtDn _ huQ
  have hru : (ruOW d n δ : ℝ) ≤ Real.sqrt ρ.u := by
    rw [huR]; exact sqrtDn_le_sqrt _ (by linarith)
  have hru2 : Real.sqrt ρ.u ≤ (ruOW d n δ : ℝ) + (encF d n δ).eq := by
    rw [huR]; exact sqrt_le_sqrtDn_add _ _
  -- the rounding of the floor fields at `u'`
  have hEu : (encF d n δ).eF * (encF d n δ).Ne * Real.sqrt ρ.u ≤ (encF d n δ).tp / 2 ^ 40 := by
    obtain ⟨-, -, hNe0, -, -, -, hnN, -, -, -, -, heFb⟩ := hF.base
    have hsu : Real.sqrt ρ.u ≤ (encF d n δ).Ne := by
      have a : Real.sqrt ρ.u ≤ ρ.u := by
        rw [Real.sqrt_le_left (by linarith)]; exact le_self_pow₀ hu1 (by norm_num)
      have b : ρ.u ≤ (encF d n δ).n := u_le_n hρ
      linarith
    have heF0 : 0 < (encF d n δ).eF := hF.heF0
    have : (encF d n δ).eF * (encF d n δ).Ne * Real.sqrt ρ.u ≤ (encF d n δ).eF * (encF d n δ).Ne * (encF d n δ).Ne :=
      mul_le_mul_of_nonneg_left hsu (by positivity)
    have e : (encF d n δ).eF * (encF d n δ).Ne * (encF d n δ).Ne = (encF d n δ).eF * (encF d n δ).Ne ^ 2 := by ring
    linarith
  -- the identifications
  have hLf : r.Lf = (encF d n δ).Le := rfl
  have hlam : r.lam = (encF d n δ).lam := by
    show (parW d n ρ.u).lam = 1 / (725 * (d : ℝ) * Bit.PieceA.Le d n ^ 2)
    rw [parW_lam]
  have hsig : (poW d n δ).sig2 = (encF d n δ).sig2 := by
    show 1 / (8 * (parW d n ρ.u).Le) = 1 / (8 * Bit.PieceA.Le d n)
    rw [parW_Le]
  have hrho : r.rho = (encF d n δ).rho := by
    show 2 * Poly.df2oClam * (d : ℝ) ^ 2 * (parW d n ρ.u).Le ^ 3 = 1450 * (d : ℝ) ^ 2 * Bit.PieceA.Le d n ^ 3
    rw [parW_Le, Poly.df2oClam]; ring
  have heps : r.eps = (encF d n δ).eps * Real.sqrt ρ.u := by
    show (parW d n ρ.u).eps = 14500 * (d : ℝ) * Real.sqrt d * Bit.PieceA.Le d n ^ 5 / Real.sqrt n * Real.sqrt ρ.u
    rw [parW_eps, Bit.PieceA.eps]
  have heta : r.eta = (encF d n δ).eta / Real.sqrt ρ.u := by
    show (parW d n ρ.u).eta = Real.sqrt d / (Bit.PieceA.Le d n * Real.sqrt n) / Real.sqrt ρ.u
    have hsn0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hLe0 : 0 < Bit.PieceA.Le d n := by linarith [regW_Le hd hn hu1 hρ.heps]
    rw [parW_eta, Real.sqrt_mul hnR.le]
    field_simp
  have hkc : r.kc = (encF d n δ).eta / Real.sqrt ρ.u * (encF d n δ).lam / (4 * (1 - (encF d n δ).lam) ^ 2) := by
    have e1 : r.kc = r.eta * (1 / 4) * r.lam * ((1 - r.lam) ^ 2)⁻¹ := rfl
    rw [e1, heta, hlam]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hR : r.R = (encR d n k).R := rfl
  have hW : r.W0 = (encR d n k).W0 := rfl
  have hsb : r.de ^ 2 / (r.R * (r.R + 1)) = (encR d n k).sbR := rfl
  -- the fields of `ε'`, `η'`, `κ_c'`
  have hX : 14500 * (encF d n δ).d * ((encF d n δ).rd + (encF d n δ).eq) * (encF d n δ).Lh ^ 5 *
      ((ruOW d n δ : ℝ) + (encF d n δ).eq) / (encF d n δ).rn =
      (((14500 * d * (sqrtDn (parO d n δ).q d + 1 / 2 ^ (parO d n δ).q) * (36 * lf1 d n δ) ^ 5 *
        (ruOW d n δ + 1 / 2 ^ (parO d n δ).q) / sqrtDn (parO d n δ).q n) : ℚ) : ℝ) := by
    simp only [encF]; push_cast; ring
  have hepsF : (encF d n δ).eps * Real.sqrt ρ.u ≤ (parOW d n δ).eps := by
    refine EncU.epsW_le hF hru2 ?_
    rw [hX]
    exact le_upR _ _
  have hepsF2 : ((parOW d n δ).eps : ℝ) ≤ (encF d n δ).eps * Real.sqrt ρ.u * (1 + (encF d n δ).tp / 16) := by
    refine EncU.epsW_rel hF hu1 hru1 hru ?_
    rw [hX]
    exact upR_le _ _
  have het : |((parOW d n δ).eta : ℝ) - (encF d n δ).rd / ((encF d n δ).Lp * (encF d n δ).rn * (ruOW d n δ : ℝ))| ≤
      (encF d n δ).eF / 2 := by
    have := rnd_errR (parO d n δ).pF (sqrtDn (parO d n δ).q d /
      ((parOW d n δ).Le * sqrtDn (parO d n δ).q n * ruOW d n δ))
    push_cast at this ⊢; exact this
  have hetaF := EncU.etaW_rel hF hru1 hru hru2 hEu het
  have hkp : |((parOW d n δ).kapc : ℝ) - ((parOW d n δ).eta : ℝ) * (encF d n δ).lm / (4 * (1 - (encF d n δ).lm) ^ 2)| ≤
      (encF d n δ).eF / 2 := by
    have := rnd_errR (parO d n δ).pF ((parOW d n δ).eta * (parOW d n δ).lam / (4 * (1 - (parOW d n δ).lam) ^ 2))
    push_cast at this ⊢; exact this
  have hkcF := EncU.kapcW_rel hF hu1 hEu hetaF hkp
  exact
    { Lf_le := hF.hLp2
      Lf_rel := hF.Le_rel
      eps_le := by rw [heps]; exact hepsF
      eps_rel := by rw [heps]; exact hepsF2
      lam_rel := by rw [hlam]; exact hF.lam_rel.trans w16
      eta_rel := by rw [heta]; exact hetaF.trans w16
      sig2_rel := by rw [hsig]; exact hF.sig2_rel.trans w16
      rho_le := by rw [hrho]; exact hF.rho_le
      rho_rel := by rw [hrho]; exact hF.rho_rel
      kapc_rel := by rw [hkc]; exact hkcF
      nu_rel := by rw [hlam]; exact hF.nu_rel
      R_le := by rw [hR]; exact hG.R_le
      R_rel := by rw [hR]; exact hG.R_rel.trans (div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num))
      sb_le := by rw [hsb]; exact hG.sb_le
      sb_rel := by rw [hsb]; exact hG.sb_rel
      W_le := by rw [hW]; exact hG.W_le
      W_rel := by rw [hW]; exact hG.W_rel
      A0 := by rw [hsig, hLf]; exact hF.A0_rel
      B0 := by rw [hsig]; exact hF.B0_rel
      Lam_eq := by
        show (((d * NeO d n k : ℕ) : ℚ) : ℝ) = (d : ℝ) * ((NeO d n k : ℕ) : ℝ)
        push_cast; ring
      Ne_eq := by show (((NeO d n k : ℕ) : ℚ) : ℝ) = ((NeO d n k : ℕ) : ℝ); push_cast; rfl }

end AdversarialBco.UW.BudW
