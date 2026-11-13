/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRoundCtx

@[expose] public section

/-!
# Piece C, the play: `PlayC`

The tracking lemma and E6: with `μ' = μ°` and `A' = (I + H) A°`,

    X' - X° = (1 - λ)(H A°ξ' + A°(ξ' - ξ)) + (λ - λ')(I + H) A°ξ',

so `|X' - X°| ≤ Λ^{1/2}(ℏ Ξ₁ + e_ξ) + 2^{-p-4} λ (1 + ℏ) Λ^{1/2} Ξ₁ = X̄`, from `|A°| ≤ Λ^{1/2}`, `|ξ| ≤ Ξ`,
`|ξ' - ξ| ≤ e_ξ ≤ 1`, `|H| ≤ hTr s ≤ ℏ`, `|λ' - λ| ≤ 2^{-p-4} λ`.
-/

namespace AdversarialBco.Bit.BLP.RC

open AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg)
open Matrix
open AdversarialBco.Bit.Asm (deltaBL)
open AdversarialBco.Poly.Layer2 (kTh)
open AdversarialBco.RealRAM (polytope)

variable {d : ℕ}

theorem cV_XQ (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) :
    cV (XQ cfg st ξ) = cV st.mu + ((1 - cfg.par.lam : ℚ) : ℝ) • (cM st.A *ᵥ cV ξ) := by
  unfold XQ; rw [cV_add, cV_smul, cM_mulVec]

/-- The algebra of E6. -/
theorem play_diff (μ ξ' ξ : Fin d → ℝ) (A H : Matrix (Fin d) (Fin d) ℝ) (l l' : ℝ) :
    μ + (1 - l') • (((1 + H) * A) *ᵥ ξ') - (μ + (1 - l) • (A *ᵥ ξ)) =
      (1 - l) • (H *ᵥ (A *ᵥ ξ') + A *ᵥ (ξ' - ξ)) + (l - l') • (A *ᵥ ξ' + H *ᵥ (A *ᵥ ξ')) := by
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- E6 in norms. -/
theorem play_bound (a Ha b : Fin d → ℝ) (l l' L X1 ex h tq : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hll : |l - l'| ≤ tq / 16 * l) (hL : 0 ≤ L) (hav : oNorm a ≤ L * X1) (hHa : oNorm Ha ≤ h * (L * X1))
    (hb : oNorm b ≤ L * ex) (hh : 0 ≤ h) (hX : 0 ≤ X1) (htq : 0 ≤ tq) :
    oNorm ((1 - l) • (Ha + b) + (l - l') • (a + Ha)) ≤ L * (h * X1 + ex) + tq / 16 * l * (1 + h) * L * X1 := by
  have h1 := oNorm_add_le ((1 - l) • (Ha + b)) ((l - l') • (a + Ha))
  rw [oNorm_smul, oNorm_smul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - l)] at h1
  have h2 := oNorm_add_le Ha b
  have h3 := oNorm_add_le a Ha
  have hn1 := oNorm_nonneg (Ha + b)
  have hn2 := oNorm_nonneg (a + Ha)
  have hab : oNorm (Ha + b) ≤ L * (h * X1 + ex) := by nlinarith
  have hah : oNorm (a + Ha) ≤ (1 + h) * (L * X1) := by nlinarith
  have t1 : (1 - l) * oNorm (Ha + b) ≤ L * (h * X1 + ex) := by
    have : (1 - l) * oNorm (Ha + b) ≤ 1 * oNorm (Ha + b) := mul_le_mul_of_nonneg_right (by linarith) hn1
    linarith
  have t2 : |l - l'| * oNorm (a + Ha) ≤ tq / 16 * l * ((1 + h) * (L * X1)) :=
    mul_le_mul hll hah hn2 (by positivity)
  nlinarith

open AdversarialBco.Bit.BLP.RC.Bud in
/-- Piece C, the play. -/
theorem playC : PlayC := by
  intro R d n m A b cs ap π s st ξ' hd hn hc hbud hpg hs hdet htau htr hxi
  set c := df2CtxAtF d n (deltaBL d n) (kTh n (deltaBL d n) (polytope A b) (posR R d n m A b cs)) ap with hcdef
  have hs' : s ≤ c.tau π (s + 1) := tau_le htau
  have hp : c.p = po d n := rfl
  have hcn : c.n = n := rfl
  obtain ⟨H, hAH, hHn⟩ := htr.hA
  have hmu := htr.mu
  -- the facts
  have hA : opN (c.st π s).A ≤ Real.sqrt (Bud.Lam d n) :=
    (opN_A_sq hdet hs').trans (Real.sqrt_le_sqrt (inv_de_le_Lam hd hbud))
  have hξ : oNorm (π.xi s) ≤ Bud.Xi d n := xi_norm hdet hs' hp hcn hbud
  have hdξ : oNorm (cV ξ' - π.xi s) ≤ Bud.exi d n := dxi_norm ξ' (π.xi s) hxi
  have hexi : Bud.exi d n ≤ 1 := (exi_le hd hn hbud).trans (tp_le_one d n)
  have hξ' : oNorm (cV ξ') ≤ Bud.Xi1 d n := by
    have := oNorm_add_le (π.xi s) (cV ξ' - π.xi s)
    rw [add_sub_cancel] at this
    unfold Bud.Xi1; linarith
  have hH : opN H ≤ Bud.hb d n := hHn.trans (hbud.hTr_le s hs.le)
  have hb0 := hb_nonneg hbud
  have hl0 : 0 < c.p.lam := hdet.rows.pos_lam
  have hl1 : c.p.lam ≤ 1 / 2 := hdet.rows.lam_le
  have hll : |c.p.lam - ((par d n).lam : ℝ)| ≤ Bud.tp d n / 16 * c.p.lam := by
    rw [abs_sub_comm]; exact lam_err hbud hl0
  have hL0 : 0 ≤ Real.sqrt (Bud.Lam d n) := Real.sqrt_nonneg _
  have hX1 : 0 ≤ Bud.Xi1 d n := (oNorm_nonneg _).trans hξ'
  -- the algebra
  have e : cV (XQ (cfgOf R d n m A b cs) st ξ') - c.X π s =
      (1 - c.p.lam) • (H *ᵥ ((c.st π s).A *ᵥ cV ξ') + (c.st π s).A *ᵥ (cV ξ' - π.xi s)) +
        (c.p.lam - ((par d n).lam : ℝ)) • ((c.st π s).A *ᵥ cV ξ' + H *ᵥ ((c.st π s).A *ᵥ cV ξ')) := by
    rw [cV_XQ, hAH, hmu]
    have : ((1 - (cfgOf R d n m A b cs).par.lam : ℚ) : ℝ) = 1 - ((par d n).lam : ℝ) := by
      push_cast; rfl
    rw [this]
    exact play_diff _ _ _ _ _ _ _
  rw [e]
  have ha : oNorm ((c.st π s).A *ᵥ cV ξ') ≤ Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hξ' (oNorm_nonneg _) hL0)
  have hha : oNorm (H *ᵥ ((c.st π s).A *ᵥ cV ξ')) ≤ Bud.hb d n * (Real.sqrt (Bud.Lam d n) * Bud.Xi1 d n) :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hH ha (oNorm_nonneg _) hb0)
  have hbb : oNorm ((c.st π s).A *ᵥ (cV ξ' - π.xi s)) ≤ Real.sqrt (Bud.Lam d n) * Bud.exi d n :=
    (oNorm_mulVec_le _ _).trans (mul_le_mul hA hdξ (oNorm_nonneg _) hL0)
  have := play_bound _ _ _ c.p.lam ((par d n).lam : ℝ) (Real.sqrt (Bud.Lam d n)) (Bud.Xi1 d n) (Bud.exi d n)
    (Bud.hb d n) (Bud.tp d n) hl0.le (by linarith) hll hL0 ha hha hbb hb0 hX1 (tp_pos d n).le
  unfold Bud.Xb
  have hlam : Bud.lam d n = c.p.lam := rfl
  rw [hlam]
  linarith

end AdversarialBco.Bit.BLP.RC
