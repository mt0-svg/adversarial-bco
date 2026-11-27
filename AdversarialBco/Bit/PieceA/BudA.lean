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

end AdversarialBco.Bit.PieceA
