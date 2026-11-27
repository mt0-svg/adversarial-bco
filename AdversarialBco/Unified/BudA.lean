/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BudEnc
public import AdversarialBco.Unified.BudEncMaj
public import AdversarialBco.Unified.BudMajO
public import AdversarialBco.Bit.TriSamp

@[expose] public section

/-!
# Theorem BUD of BL-O at `k`

Lemma ENC and Theorem BUD at every `(d, n, k)` of the case `RunCaseK`, after Bit/PieceA/BudA.lean: `encOKK` reads the
fields of `EncOK` off `EncR.OK (encR d n k)` (Unified/BudEnc.lean, BudEncMaj.lean), `budAK` the fields of `BudOK` off
`Reg.OK (regK d n k)` (Unified/BudInst.lean, BudMaj.lean, BudMajO.lean), with `log(14n/δe) ≤ Lgb` and the coin bound
proved here. The budgets in `δ` use `2^k ≤ N_e(k)`.

At the input `δ`: `budO` gives `BudOK d n (kDel δ)` under `RunCaseO`-form hypotheses, and `R(po) ≤ R'` (`EncOK.R_le`)
with `36.4 d λ(ρ_h) ≤ R(po)` (`triRad_le_R`, from Bit/TriSamp.lean) for the position.
-/

namespace AdversarialBco.Unified.BudK

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.BLO
open AdversarialBco.Unified.BudR (Reg EncR)

theorem encOKK (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCaseK d n k) : EncOK d n k := by
  have hE := encR_ok d n k hd hn h
  have hLe : Le d n k = (encR d n k).Le := rfl
  have hde := de_eq d n k hd hn
  have hu0 : 0 < tp d n k := by rw [tp_eq]; positivity
  have hsig : (poK d n k).sig2 = (encR d n k).sig2 := rfl
  have hlam : lam d n k = (encR d n k).lam := lam_eq d n k
  have hW : W0 d n k = (encR d n k).W0 := by
    show R d n k + 4 * d * Real.sqrt (Ne d n k / Le d n k) = _
    rfl
  have hsb : (poK d n k).sb = (encR d n k).sbR := by
    show (poK d n k).δe ^ 2 / ((poK d n k).R * ((poK d n k).R + 1)) = _
    rw [poK_de d n k hd hn]; rfl
  have w16 : tp d n k / 2 ^ 16 ≤ tp d n k / 16 := by
    apply div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num)
  refine
    { de_eq := hde
      Le_eq := Le_eq d n k hd hn
      Le_le := hE.hLp2
      Le_rel := hE.Le_rel
      eps_le := by rw [eps_eq]; exact hE.eps_le
      eps_rel := by rw [eps_eq]; exact hE.eps_rel
      lam_rel := by rw [hlam]; exact hE.lam_rel.trans w16
      eta_rel := by rw [eta_eq]; exact hE.eta_rel.trans w16
      sig2_rel := by rw [hsig]; exact hE.sig2_rel.trans w16
      rho_le := by rw [rho_eq]; exact hE.rho_le
      rho_rel := by rw [rho_eq]; exact hE.rho_rel
      kapc_rel := by rw [kc_eq, eta_eq, lam_eq]; exact hE.kapc_rel
      nu_rel := by rw [hlam]; exact hE.nu_rel
      R_le := hE.R_le
      R_rel := hE.R_rel.trans (div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num))
      sb_le := by rw [hsb]; exact hE.sb_le
      sb_rel := by rw [hsb]; exact hE.sb_rel
      W_le := by rw [hW]; exact hE.W_le
      W_rel := by rw [hW]; exact hE.W_rel
      A0 := by rw [hsig]; exact hE.A0_rel
      B0 := by rw [hsig]; exact hE.B0_rel
      Lam_eq := by
        show (((d * NeO d n k : ℕ) : ℚ) : ℝ) = (d : ℝ) * ((NeO d n k : ℕ) : ℝ)
        push_cast; ring
      Ne_eq := by show (((NeO d n k : ℕ) : ℚ) : ℝ) = ((NeO d n k : ℕ) : ℝ); push_cast; rfl
      kap := rfl
      k0 := by show ((1 - (poK d n k).lam) ^ 2)⁻¹ = 1 / (1 - lam d n k) ^ 2; rw [one_div]; rfl
      theta := rfl
      alpha := rfl
      c1 := rfl
      gam := rfl }

theorem Lg_leK (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    AdversarialBco.Poly.df2Lg (poK d n k) n ≤ Lgb d n k := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < Ne d n k := by
    have : (1 : ℝ) ≤ Ne d n k := by unfold Ne; exact_mod_cast NeO_pos d n k hd hn
    linarith
  have hn4 : (n : ℝ) ^ 4 ≤ Ne d n k := by
    have h0 := Ne_ge0 d n k hd hn
    have : (n : ℝ) ^ 4 ≤ Bit.PieceA.Ne d n := by
      unfold Bit.PieceA.Ne Bit.PieceA.NeN; push_cast
      have : (1 : ℝ) ≤ d ^ 3 := one_le_pow₀ hd'
      nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
    linarith
  have hlog : 4 * Real.log n ≤ Real.log (Ne d n k) := by
    have e := Real.log_pow (n : ℝ) 4; push_cast at e
    rw [← e]; exact Real.log_le_log (by positivity) hn4
  show Real.log (14 * n / (poK d n k).δe) ≤ Real.log 14 + 5 * Le d n k / 144
  rw [Le_eq d n k hd hn, poK_de d n k hd hn, show (14 : ℝ) * n / (1 / Ne d n k) = 14 * n * Ne d n k by field_simp,
    Real.log_mul (by positivity) hN0.ne', Real.log_mul (by norm_num) (by positivity)]
  linarith

theorem coins_leK (d n k : ℕ) :
    (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / 2 ^ ((parK d n k).B / 2) : ℝ) ≤ dbits d n k := by
  have ht := t2_tpK d n k
  have hc : (((d + 1) / 2 + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 2 := by
    have : (d + 1) / 2 + 1 ≤ d + 2 := by omega
    exact_mod_cast this
  have hB : (0 : ℝ) < 2 ^ ((parK d n k).B / 2) := by positivity
  show _ ≤ tp d n k / 4
  rw [mul_one_div, div_le_div_iff₀ hB (by norm_num)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc hn0]

/-- `2^k ≤ N_e(k)`. -/
theorem two_pow_le_Ne (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : (2 : ℝ) ^ k ≤ Ne d n k := by
  show (2 : ℝ) ^ k ≤ ((NeO d n k : ℕ) : ℝ)
  have : 2 ^ k ≤ NeO d n k := by
    unfold NeO
    have h1 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    calc 2 ^ k ≤ 2 ^ (17 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1 * 2 ^ (17 + k) * 1 * 1 := by ring
      _ ≤ 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := by gcongr; norm_num
  exact_mod_cast this

/-- **Theorem BUD of BL-O at `k`**: Lemma ENC and Theorem BUD with BL-O's fields at every `(d, n, k)` of the case. -/
theorem budAK : BudAK := by
  intro d n k hd hn h
  have hR := reg_okK d n k hd hn h
  have hL1 : 17467 ≤ Le d n k := hR.hL1
  obtain ⟨hx, hV, hb⟩ := hR.p1
  obtain ⟨hXb, hreg⟩ := hR.p4
  obtain ⟨hgT, hgW, hgA⟩ := hR.guard
  obtain ⟨hbud, hk0⟩ := hR.budget
  have hK0 : (0 : ℝ) < 2 ^ k := by positivity
  have hK := two_pow_le_Ne d n k hd hn
  have e2 : (2 : ℝ)⁻¹ ^ k / 8 = 1 / 2 ^ k / 8 := by rw [inv_pow, one_div]
  exact
    { enc := encOKK d n k hd hn h
      Le_ge := hL1
      Lg_le := Lg_leK d n k hd hn
      cb_le := hR.cb_dom
      x_le := hx
      V_le := hV
      hb_le := hb
      hTr_le := fun j hj => hR.hTr_le j (by show (j : ℝ) ≤ (n : ℝ); exact_mod_cast hj)
      sel_le := hR.sel_le
      h_le := hR.h_le_rmin
      val_le := hR.val_le
      Xb_le := hXb
      reg_le := hreg
      ePhi_le := hR.ePhi_le_eh
      eX_le := hR.eX_le_eh
      gT := hgT
      gW := hgW
      gA := hgA
      coins := coins_leK d n k
      budget := hbud
      kap0_nonneg := hk0
      regO_le := hR.regO_le
      S_le := hR.S_le
      bits_k := by rw [e2]; exact hR.bits_k hK0 hK
      kap_k := by rw [e2]; exact hR.kap_k hK0 hK
      kapO_nonneg := hR.kapO_bd.1 }

/-- At the input `δ`: Theorem BUD at `kDel δ` in the case `ε ≤ 1/4` of `df2oPar d n δ_BL`. -/
theorem budO (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : (df2oPar d n (deltaO d n (kDel δ))).eps ≤ 1 / 4) :
    BudOK d n (kDel δ) :=
  budAK d n (kDel δ) hd hn h

/-- The radius of TRI-OGD-O's good position is at most P°'s `R` (Bit/TriSamp.lean), hence at most `R'`. -/
theorem triRad_le_R (d n k : ℕ) (hd : 1 ≤ d) :
    36.4 * d * AdversarialBco.Poly.pgLam (Bit.triRh d) ≤ R d n k := by
  exact (Bit.tri_par_stage d hd).2.2

end AdversarialBco.Unified.BudK
