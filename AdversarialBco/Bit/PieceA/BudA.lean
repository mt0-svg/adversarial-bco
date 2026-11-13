/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Enc
public import AdversarialBco.Bit.PieceA.EncMaj
public import AdversarialBco.Bit.PieceA.Maj

@[expose] public section

/-!
# Piece A: `BudA`

The enclosure lemma and the precision theorem at every `(d, n)` of `RunCase`: `encOK` reads the fields of
`Bud.EncOK` off `EncR.OK (encR d n)` (Bit/PieceA/Enc.lean, EncMaj.lean), and `budA` the fields of `Bud.BudOK` off
`Reg.OK (reg d n)` (Bit/PieceA/Inst.lean, Maj.lean), with the two regime facts `Lg_le` and `coins` proved here.
-/

namespace AdversarialBco.Bit.PieceA

open AdversarialBco.Bit.BLP (po par)

open AdversarialBco.Bit.Asm (RunCase)

theorem encOK (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCase d n) : BLP.Bud.EncOK d n := by
  have hE := encR_ok d n hd hn h
  have hLe : BLP.Bud.Le d n = Le d n := bud_Le d n hd hn
  have hde := po_de d n hd hn
  have hu : BLP.Bud.tp d n = u d n := rfl
  have hu0 : 0 < u d n := by unfold u; positivity
  have hsig : (po d n).sig2 = (encR d n).sig2 := by
    show 1 / (8 * (po d n).Le) = 1 / (8 * Le d n)
    rw [← hLe]; rfl
  have hlam : BLP.Bud.lam d n = (encR d n).lam := bud_lam d n hd hn
  have hW : BLP.Bud.W0 d n = (encR d n).W0 := by
    show BLP.Bud.R d n + 4 * d * Real.sqrt (BLP.Bud.Ne d n / BLP.Bud.Le d n) = _
    rw [hLe]; rfl
  have hsb : (po d n).sb = (encR d n).sbR := by
    show (po d n).δe ^ 2 / ((po d n).R * ((po d n).R + 1)) = _
    rw [hde]; rfl
  have w16 : u d n / 2 ^ 16 ≤ u d n / 16 := by
    apply div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num)
  refine
    { de_eq := hde
      Le_eq := hLe
      Le_le := by rw [hLe]; exact hE.hLp2
      Le_rel := by rw [hLe, hu]; exact hE.Le_rel
      eps_le := by rw [bud_eps d n hd hn]; exact hE.eps_le
      eps_rel := by rw [bud_eps d n hd hn, hu]; exact hE.eps_rel
      lam_rel := by rw [hlam, hu]; exact hE.lam_rel.trans w16
      eta_rel := by rw [bud_eta d n hd hn, hu]; exact hE.eta_rel.trans w16
      sig2_rel := by rw [hsig, hu]; exact hE.sig2_rel.trans w16
      rho_le := by rw [bud_rho d n hd hn]; exact hE.rho_le
      rho_rel := by rw [bud_rho d n hd hn, hu]; exact hE.rho_rel
      kapc_rel := by rw [bud_kc d n hd hn, hu]; exact hE.kapc_rel
      nu_rel := by rw [hlam, hu]; exact hE.nu_rel
      R_le := hE.R_le
      R_rel := by
        rw [hu]
        exact hE.R_rel.trans (div_le_div_of_nonneg_left hu0.le (by norm_num) (by norm_num))
      sb_le := by rw [hsb]; exact hE.sb_le
      sb_rel := by rw [hsb, hu]; exact hE.sb_rel
      W_le := by rw [hW]; exact hE.W_le
      W_rel := by rw [hW, hu]; exact hE.W_rel
      A0 := by rw [hsig, hu, hLe]; exact hE.A0_rel
      B0 := by rw [hsig, hu]; exact hE.B0_rel
      Lam_eq := by
        show (((d * BLP.Ne d n : ℕ) : ℚ) : ℝ) = (d : ℝ) * ((BLP.Ne d n : ℕ) : ℝ)
        push_cast; ring
      Ne_eq := by show (((BLP.Ne d n : ℕ) : ℚ) : ℝ) = ((BLP.Ne d n : ℕ) : ℝ); push_cast; rfl
      kap := rfl
      k0 := by show ((1 - (po d n).lam) ^ 2)⁻¹ = 1 / (1 - BLP.Bud.lam d n) ^ 2; rw [one_div]; rfl
      theta := rfl
      alpha := rfl
      c1 := rfl
      gam := rfl }

theorem Lg_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    AdversarialBco.Poly.df2Lg (po d n) n ≤ BLP.Bud.Lgb d n := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < Ne d n := by unfold Ne NeN; push_cast; positivity
  have hn4 : (n : ℝ) ^ 4 ≤ Ne d n := by
    unfold Ne NeN; push_cast
    have : (1 : ℝ) ≤ d ^ 3 := one_le_pow₀ hd'
    nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
  have hlog : 4 * Real.log n ≤ Real.log (Ne d n) := by
    have e := Real.log_pow (n : ℝ) 4; push_cast at e
    rw [← e]; exact Real.log_le_log (by positivity) hn4
  rw [bud_Lgb d n hd hn]
  show Real.log (14 * n / (po d n).δe) ≤ Real.log 14 + 5 * (36 * Real.log (Ne d n)) / 144
  rw [po_de d n hd hn, show (14 : ℝ) * n / (1 / Ne d n) = 14 * n * Ne d n by field_simp, Real.log_mul (by positivity) hN0.ne', Real.log_mul (by norm_num) (by positivity)]
  linarith

theorem coins_le (d n : ℕ) :
    (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / 2 ^ ((par d n).B / 2) : ℝ) ≤ BLP.Bud.dbits d n := by
  have ht := t2_tp d n
  have hc : (((d + 1) / 2 + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 2 := by
    have : (d + 1) / 2 + 1 ≤ d + 2 := by omega
    exact_mod_cast this
  have hB : (0 : ℝ) < 2 ^ ((par d n).B / 2) := by positivity
  show _ ≤ BLP.Bud.tp d n / 4
  rw [mul_one_div, div_le_div_iff₀ hB (by norm_num)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc hn0]

/-- Piece A: the enclosure lemma and the precision theorem at every `(d, n)` of `RunCase`. -/
theorem budA : BLP.BudA := by
  intro d n hd hn h
  have hR := reg_ok d n hd hn h
  have hL1 : 17467 ≤ BLP.Bud.Le d n := hR.hL1
  obtain ⟨hx, hV, hb⟩ := hR.p1
  obtain ⟨hXb, hreg⟩ := hR.p4
  obtain ⟨hgT, hgW, hgA⟩ := hR.guard
  obtain ⟨hbud, hk0⟩ := hR.budget
  exact
    { enc := encOK d n hd hn h
      Le_ge := hL1
      Lg_le := Lg_le d n hd hn
      cb_le := hR.cb_dom
      x_le := hx
      V_le := hV
      hb_le := hb
      hTr_le := fun k hk => hR.hTr_le k (by show (k : ℝ) ≤ (n : ℝ); exact_mod_cast hk)
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
      coins := coins_le d n
      budget := hbud
      kap0_nonneg := hk0 }

end AdversarialBco.Bit.PieceA
