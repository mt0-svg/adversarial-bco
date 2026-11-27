/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngCSet
public import AdversarialBco.Bit.BLRoundPlay

@[expose] public section

/-!
# Piece C for BL-O, the play: `PlayCO`

Bit/BLRoundPlay.lean at `k` (Lemma TRACK-2 and the error E6 of one round): with `μ' = μ°` and `A' = (I + H) A°`,
`X' - X° = (1 - λ)(H A°ξ' + A°(ξ' - ξ)) + (λ - λ')(I + H) A°ξ'`, so `|X' - X°| ≤ X̄`. BL-O's point
`X' = μ' + (1 - λ') A'ξ'` (`XO`) is BL's; it reads neither the gauge nor the oracle.
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St cV cM opN)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

theorem cV_XO (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) :
    cV (XO c st ξ) = cV st.mu + ((1 - c.par.lam : ℚ) : ℝ) • (cM st.A *ᵥ cV ξ) := by
  unfold XO; rw [cV_add, cV_smul, cM_mulVec]

/-- **Piece C for BL-O, the play.** -/
theorem playCO : PlayCO := by
  intro d K c k ap π s st ξ' hd hn hpar hc hbud hpg hs hdet htau htr hxi
  set cx := ctxO K c k ap with hcdef
  have hs' : s ≤ cx.tau π (s + 1) := tau_le htau
  have hp : cx.p = poK d c.n k := rfl
  have hcn : cx.n = c.n := rfl
  obtain ⟨H, hAH, hHn⟩ := htr.hA
  have hmu := htr.mu
  have hA : opN (cx.st π s).A ≤ Real.sqrt (BudK.Lam d c.n k) :=
    (opN_A_sq hdet hs').trans (Real.sqrt_le_sqrt (by rw [hp]; exact NK.inv_de_le_Lam hd hbud))
  have hξ : oNorm (π.xi s) ≤ BudK.Xi d c.n k := NK.xi_norm hdet hs' hp hcn hbud
  have hxi' : ∀ i, |(ξ' i : ℝ) - π.xi s i| ≤ 4 / 2 ^ ((parK d c.n k).B / 2) := by rw [← hpar]; exact hxi
  have hdξ : oNorm (cV ξ' - π.xi s) ≤ BudK.exi d c.n k := NK.dxi_norm ξ' (π.xi s) hxi'
  have hexi : BudK.exi d c.n k ≤ 1 := (NK.exi_le hd hn hbud).trans (NK.tp_le_one d c.n k)
  have hξ' : oNorm (cV ξ') ≤ BudK.Xi1 d c.n k := by
    have := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
    rw [add_sub_cancel] at this
    unfold BudK.Xi1; linarith
  have hH : opN H ≤ BudK.hb d c.n k := hHn.trans (hbud.hTr_le s hs.le)
  have hb0 := NK.hb_nonneg hbud
  have hl0 : 0 < cx.p.lam := hdet.rows.pos_lam
  have hl1 : cx.p.lam ≤ 1 / 2 := hdet.rows.lam_le
  have hll : |cx.p.lam - ((parK d c.n k).lam : ℝ)| ≤ BudK.tp d c.n k / 16 * cx.p.lam := by
    rw [abs_sub_comm, hp]; rw [hp] at hl0; exact NK.lam_err hbud hl0
  have hL0 : 0 ≤ Real.sqrt (BudK.Lam d c.n k) := Real.sqrt_nonneg _
  have hX1 : 0 ≤ BudK.Xi1 d c.n k := (oNorm_nonneg _).trans hξ'
  have e : cV (XO c st ξ') - cx.X π s =
      (1 - cx.p.lam) • (H *ᵥ ((cx.st π s).A *ᵥ cV ξ') + (cx.st π s).A *ᵥ (cV ξ' - π.xi s)) +
        (cx.p.lam - ((parK d c.n k).lam : ℝ)) • ((cx.st π s).A *ᵥ cV ξ' + H *ᵥ ((cx.st π s).A *ᵥ cV ξ')) := by
    rw [cV_XO, hAH, hmu]
    have : ((1 - c.par.lam : ℚ) : ℝ) = 1 - ((parK d c.n k).lam : ℝ) := by rw [hpar]; push_cast; rfl
    rw [this]
    exact play_diff _ _ _ _ _ _ _
  rw [e]
  have ha : oNorm ((cx.st π s).A *ᵥ cV ξ') ≤ Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hξ' (oNorm_nonneg _) hL0)
  have hha : oNorm (H *ᵥ ((cx.st π s).A *ᵥ cV ξ')) ≤
      BudK.hb d c.n k * (Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k) :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hH ha (oNorm_nonneg _) hb0)
  have hbb : oNorm ((cx.st π s).A *ᵥ (cV ξ' - π.xi s)) ≤ Real.sqrt (BudK.Lam d c.n k) * BudK.exi d c.n k :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hdξ (oNorm_nonneg _) hL0)
  have := play_bound _ _ _ cx.p.lam ((parK d c.n k).lam : ℝ) (Real.sqrt (BudK.Lam d c.n k)) (BudK.Xi1 d c.n k)
    (BudK.exi d c.n k) (BudK.hb d c.n k) (BudK.tp d c.n k) hl0.le (by linarith) hll hL0 ha hha hbb hb0 hX1
    (NK.tp_pos d c.n k).le
  unfold BudK.Xb
  have hlam : BudK.lam d c.n k = cx.p.lam := rfl
  rw [hlam]
  linarith

end AdversarialBco.Unified.EngC
