/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngCSet
public import AdversarialBco.Unified.EngPlay

@[expose] public section

/-!
# Piece C for BL-OW, the play: `PlayCOW`

Unified/EngPlay.lean at BUD-W (Lemma TRACK-2 and E6): with `μ' = μ°` and `A' = (I + H) A°`,
`X' - X° = (1 - λ)(H A°ξ' + A°(ξ' - ξ)) + (λ - λ')(I + H) A°ξ'`, so `|X' - X°| ≤ X̄`. The play does not read the
observation, so the weighting does not enter: `X̄` is Theorem U's, with `Ξ₁` from event (a) at the level.
-/

namespace AdversarialBco.UW.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open AdversarialBco.Unified.BLO
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng
open AdversarialBco.Bit.BLP (Par St cV cM opN)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

/-- `|λ' - λ| ≤ 2^{-p-4} λ` (ENC-W). -/
theorem lam_errW {n : ℕ} {δ : ℚ} (h : EncOKW d n δ) (hl : 0 < (poW d n δ).lam) :
    |((parOW d n δ).lam : ℝ) - (poW d n δ).lam| ≤ (rW d n δ).tp / 16 * (poW d n δ).lam := by
  have := h.lam_rel
  have e : ((parOW d n δ).lam : ℝ) - (poW d n δ).lam =
      (poW d n δ).lam * (((parOW d n δ).lam : ℝ) / (poW d n δ).lam - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hl]
  have h2 : |((parOW d n δ).lam : ℝ) / (poW d n δ).lam - 1| ≤ (rW d n δ).tp / 16 := this
  nlinarith [abs_nonneg (((parOW d n δ).lam : ℝ) / (poW d n δ).lam - 1)]

/-- **Piece C for BL-OW, the play.** -/
theorem playCOW : PlayCOW := by
  intro d K c δ ap π s st ξ' hd hn hpar hc hreg hbud henc hpg hs hdet htau hevG htr hxi
  set cx := ctxOW K c δ ap with hcdef
  set πw := pwOW K c δ ap π with hπw
  have hxi' : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ ((parOW d c.n δ).B / 2) := by rw [← hpar]; exact hxi
  have S : SettW d c.n δ cx π πw s st ξ' :=
    ⟨hd, hn, hc, hreg, hbud, henc, hs, hdet, htau, hevG, rfl, rfl, rfl, htr, hxi'⟩
  have R := S.R
  obtain ⟨H, hAH, hHn⟩ := htr.hA
  have hmu := htr.mu
  have hA : opN (cx.st πw s).A ≤ Real.sqrt (rW d c.n δ).Lam := S.opN_A0
  have hdξ : oNorm (cV ξ' - π.xi s) ≤ (rW d c.n δ).exi := S.dxi_le
  have hξ' : oNorm (cV ξ') ≤ (rW d c.n δ).Xi1 := S.xi'_le
  have hH : opN H ≤ (rW d c.n δ).hb :=
    hHn.trans (R.hTr_le s (by show (s : ℝ) ≤ (c.n : ℝ); exact_mod_cast hs.le))
  have hb0 := (R.hb_bd).1
  have hl0 : 0 < cx.p.lam := hdet.rows.pos_lam
  have hl1 : cx.p.lam ≤ 1 / 2 := hdet.rows.lam_le
  have hll : |cx.p.lam - ((parOW d c.n δ).lam : ℝ)| ≤ (rW d c.n δ).tp / 16 * cx.p.lam := by
    rw [abs_sub_comm]; exact lam_errW henc hl0
  have hL0 : 0 ≤ Real.sqrt (rW d c.n δ).Lam := Real.sqrt_nonneg _
  have hX1 : 0 ≤ (rW d c.n δ).Xi1 := (oNorm_nonneg _).trans hξ'
  have e : cV (XO c st ξ') - cx.X πw s =
      (1 - cx.p.lam) • (H *ᵥ ((cx.st πw s).A *ᵥ cV ξ') + (cx.st πw s).A *ᵥ (cV ξ' - π.xi s)) +
        (cx.p.lam - ((parOW d c.n δ).lam : ℝ)) • ((cx.st πw s).A *ᵥ cV ξ' + H *ᵥ ((cx.st πw s).A *ᵥ cV ξ')) := by
    rw [Unified.EngC.cV_XO, hAH, hmu]
    have : ((1 - c.par.lam : ℚ) : ℝ) = 1 - ((parOW d c.n δ).lam : ℝ) := by rw [hpar]; push_cast; rfl
    rw [this]
    exact play_diff _ _ _ _ _ _ _
  rw [e]
  have ha : oNorm ((cx.st πw s).A *ᵥ cV ξ') ≤ Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xi1 :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hξ' (oNorm_nonneg _) hL0)
  have hha : oNorm (H *ᵥ ((cx.st πw s).A *ᵥ cV ξ')) ≤
      (rW d c.n δ).hb * (Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xi1) :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hH ha (oNorm_nonneg _) hb0)
  have hbb : oNorm ((cx.st πw s).A *ᵥ (cV ξ' - π.xi s)) ≤ Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).exi :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hdξ (oNorm_nonneg _) hL0)
  have := play_bound _ _ _ cx.p.lam ((parOW d c.n δ).lam : ℝ) (Real.sqrt (rW d c.n δ).Lam) (rW d c.n δ).Xi1
    (rW d c.n δ).exi (rW d c.n δ).hb (rW d c.n δ).tp hl0.le (by linarith) hll hL0 ha hha hbb hb0 hX1
    R.htp0.le
  unfold RegW.Xb
  have hlam : (rW d c.n δ).lam = cx.p.lam := rfl
  rw [hlam]
  linarith

end AdversarialBco.UW.EngC
