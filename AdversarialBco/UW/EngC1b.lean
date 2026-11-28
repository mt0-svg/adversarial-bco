/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngC1a
public import AdversarialBco.UW.DetRegion
public import AdversarialBco.Unified.EngC1b

@[expose] public section

/-!
# Piece C for BL-OW, part C1 (b): Lemma TRACK at `s + 1` and the fields

Unified/EngC1b.lean for BL-OW at BUD-W: E4 and Lemma TRACK for `A'` and `B'` at `s + 1`, the guard R10, E7w and E8
(`u`, `w`, `P`), E9w and E11w (the fields `b, k, G, l`), and `c1OW : C1OW`. The increments of `b, k, G, l` read the
weighted observation: on a weighted round (Lemma WR) they are bounded with `Ξ_{w1}`, `c̄_w`, `Δ^w_c`, `Δ^w_u`, `e^w_Y`,
`y0`; on an unweighted round `c' = c° = 0` and `Y' = Y° = 0`, so the increments are BL's roundings only.
-/

namespace AdversarialBco.UW.Eng.RCHypOW

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Eng (xO obsO rvO)
open AdversarialBco.Unified.Eng.RCHypO (phi psi frob2_cast)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW AdversarialBco.UW.Eng AdversarialBco.UW.EngC
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {δ : ℚ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-- The weighted rounds (Lemma WR): `Y' ≠ 0` or `Y° ≠ 0`. -/
abbrev Wt (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : Prop :=
  (((rvHW orc c δ st ξ' ζ' ε f).Y : ℚ) : ℝ) ≠ 0 ∨ (ctxOW K c δ ap).Y (pwOW K c δ ap π) s ≠ 0

/-! ## Lemma TRACK at `s + 1` -/

theorem hT (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (j : ℕ) (hj : j ≤ c.n) : (rW d c.n δ).hTr j ≤ 1 / 100 :=
  (H.R.hTr_le j (by show (j : ℝ) ≤ (c.n : ℝ); exact_mod_cast hj)).trans (H.R.p1).2.2

theorem hb0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).hb := (H.R.hb_bd).1

theorem hb_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).hb ≤ 1 / 100 := (H.R.p1).2.2

theorem hTs (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : (rW d c.n δ).hTr s ≤ (rW d c.n δ).hb :=
  H.R.hTr_le s (by show (s : ℝ) ≤ (c.n : ℝ); exact_mod_cast H.hs.le)

/-- E4 and TRACK for `A`: `A'_+ = (I + H') A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackA (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvHW orc c δ st ξ' ζ' ε f).A =
      (1 + H') * (ctxOW K c δ ap).An (pwOW K c δ ap π) s ∧ opN H' ≤ (rW d c.n δ).hTr (s + 1) := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  set M := r.s1 • st.A - r.s2 • vecMulVec (st.A *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-((r.s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := (Real.sqrt (cx.aa πw s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-phi cx πw s) • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.A * N' := by
    rw [cM_sub, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, sub_eq_add_neg, ← neg_smul, fac_mul]
  have hr : cM r.A = (1 + H0) * (cx.st πw s).A * N' + (cM r.A - cM M) := by
    rw [← hA0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm (cx.st πw s).A (cx.An πw s) ((cx.An πw s)ᵀ * cx.Pn πw s) N0 N' (cM r.A - cM M)
    H0 S.An_fac S.An_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.A - cM M) ≤ (rW d c.n δ).nu := by
    rw [← H.nu_eqH]; exact rndM_err _ M
  exact track_numW s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_A0 (opN_nonneg _) S.opN_AnPn
    (opN_nonneg _) H.e3A (opN_nonneg _) hρ S.Lam_pos.le

/-- E4 and TRACK for `B`: `B'_+ = (I + H') P°_{s+1} A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackB (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvHW orc c δ st ξ' ζ' ε f).B =
      (1 + H') * ((ctxOW K c δ ap).Pn (pwOW K c δ ap π) s * (ctxOW K c δ ap).An (pwOW K c δ ap π) s) ∧
      opN H' ≤ (rW d c.n δ).hTr (s + 1) := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  set M := r.s3 • st.B + r.s4 • vecMulVec (st.B *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    ((r.s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := Real.sqrt (cx.aa πw s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    psi cx πw s • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.B * N' := by
    rw [cM_add, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, fac_mul]
  have hr : cM r.B = (1 + H0) * ((cx.st πw s).P * (cx.st πw s).A) * N' + (cM r.B - cM M) := by
    rw [← hB0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm ((cx.st πw s).P * (cx.st πw s).A) (cx.Pn πw s * cx.An πw s) (cx.An πw s)ᵀ N0
    N' (cM r.B - cM M) H0 S.PnAn_fac S.PnAn_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.B - cM M) ≤ (rW d c.n δ).nu := by
    rw [← H.nu_eqH]; exact rndM_err _ M
  exact track_numW s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_PA0 (opN_nonneg _)
    (by rw [opN_transpose]; exact S.opN_An) (opN_nonneg _) H.e3B (opN_nonneg _) hρ S.Lam_pos.le

/-- GUARD (E18), R10: the traces of `A'_+ A'_+ᵀ` and `B'_+ B'_+ᵀ` are at most `(1 + ℏ)² Λ ≤ 2Λ`. -/
theorem gt (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvHW orc c δ st ξ' ζ' ε f).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvHW orc c δ st ξ' ζ' ε f).A) := by
  have S := H.sett
  have hL : ((c.par.Lam : ℕ) : ℝ) = (rW d c.n δ).Lam := by rw [H.par]; exact H.enc.Lam_eq
  have hb := H.hT (s + 1) H.hs
  have hLp := S.Lam_pos
  have key : ∀ X : Matrix (Fin d) (Fin d) ℚ, ∀ Y : Matrix (Fin d) (Fin d) ℝ,
      (∃ H' : Matrix (Fin d) (Fin d) ℝ, cM X = (1 + H') * Y ∧ opN H' ≤ (rW d c.n δ).hTr (s + 1)) →
      (Y * Yᵀ).trace ≤ (rW d c.n δ).Lam → ¬ (2 * (c.par.Lam : ℚ) < frob2 X) := by
    intro X Y ⟨H', e, hH'⟩ hY
    rw [not_lt]
    have h := frob_le_of H' Y _ _ (hH'.trans hb) hY
    rw [← e] at h
    have : ((frob2 X : ℚ) : ℝ) ≤ ((2 * (c.par.Lam : ℚ) : ℚ) : ℝ) := by
      rw [frob2_cast]; push_cast; rw [hL]; nlinarith
    exact_mod_cast this
  rw [not_or]
  refine ⟨key _ _ H.trackB ?_, key _ _ H.trackA ?_⟩
  · rw [S.PnAn_sq]; exact S.trn.1
  · rw [S.R1.2.2.1]; exact S.trn.2

/-! ## E7w, E8 -/

/-- E7w: on a weighted round, `|w' - w°| ≤ Δ^w_u`. -/
theorem ew (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : H.Wt) :
    oNorm (cV (st.A *ᵥ ξ') - (ctxOW K c δ ap).w (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Duw := by
  have S := H.sett
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  rw [cM_mulVec, hA0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_A0 (hH0.trans H.hTs) (H.wr hw).2 S.dxi_le

/-- `u' = B'ξ'` as a real vector. -/
theorem u'_eq (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : cV (st.B *ᵥ ξ') = cM st.B *ᵥ cV ξ' :=
  cM_mulVec _ _

theorem u0_eq (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (ctxOW K c δ ap).u (pwOW K c δ ap π) s =
      (((ctxOW K c δ ap).st (pwOW K c δ ap π) s).P * ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).A) *ᵥ π.xi s := by
  rw [← Matrix.mulVec_mulVec]; rfl

/-- E7w: on a weighted round, `|u' - u°| ≤ Δ^w_u`. -/
theorem du (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : H.Wt) :
    oNorm (cV (st.B *ᵥ ξ') - (ctxOW K c δ ap).u (pwOW K c δ ap π) s) ≤ (rW d c.n δ).Duw := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  rw [H.u'_eq, H.u0_eq, hB0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_PA0 (hH0.trans H.hTs) (H.wr hw).2 S.dxi_le

/-- On a weighted round, `|u°| ≤ Λ^{1/2} Ξ_w`. -/
theorem u0_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : H.Wt) :
    oNorm ((ctxOW K c δ ap).u (pwOW K c δ ap π) s) ≤ Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw := by
  have S := H.sett
  rw [H.u0_eq]
  exact (oNorm_mulVec_le _ _).trans (mul_le_mul S.opN_PA0 (H.wr hw).1 (oNorm_nonneg _) (Real.sqrt_nonneg _))

theorem u0_le1 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : H.Wt) :
    oNorm ((ctxOW K c δ ap).u (pwOW K c δ ap π) s) ≤ Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 :=
  (H.u0_le hw).trans (mul_le_mul_of_nonneg_left (H.R.Xw_bd).2.2.1 (Real.sqrt_nonneg _))

theorem Duw_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    (rW d c.n δ).Duw ≤ 1 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 +
      Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).exi := by
  unfold RegW.Duw
  have := H.hb_le
  have hX := (Xw_nonneg H.R).2
  have hs := Real.sqrt_nonneg (rW d c.n δ).Lam
  nlinarith [mul_le_mul_of_nonneg_right H.hb_le (mul_nonneg hs hX)]

/-- On a weighted round, `|u'| ≤ 1.01 Λ^{1/2} Ξ_{w1}`. -/
theorem u'_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : H.Wt) :
    oNorm (cV (st.B *ᵥ ξ')) ≤ 101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 := by
  have S := H.sett
  have h1 := H.du hw
  have h2 := H.u0_le hw
  have h3 := oNorm_add_le ((ctxOW K c δ ap).u (pwOW K c δ ap π) s)
    (cV (st.B *ᵥ ξ') - (ctxOW K c δ ap).u (pwOW K c δ ap π) s)
  rw [add_sub_cancel] at h3
  have h4 := H.Duw_le
  have hs := Real.sqrt_nonneg (rW d c.n δ).Lam
  have h5 : Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw + Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).exi ≤
      Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 := by
    rw [← mul_add]; unfold RegW.Xw1; exact mul_le_mul_of_nonneg_left (by linarith [S.exi_le_one]) hs
  linarith

/-- BL's `P' = B'B'ᵀ` of round `s`. -/
theorem P'_err (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    opN (cM st.B * (cM st.B)ᵀ - ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).P) ≤ (rW d c.n δ).DP ∧
      opN (cM st.B * (cM st.B)ᵀ) ≤ 10201 / 10000 * (rW d c.n δ).Lam := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  have e : cM st.B * (cM st.B)ᵀ = (1 + H0) * (cx.st πw s).P * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * ((cx.st πw s).P * (cx.st πw s).A) * (((cx.st πw s).P * (cx.st πw s).A)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * (((cx.st πw s).P * (cx.st πw s).A) * ((cx.st πw s).P * (cx.st πw s).A)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PA_sq]
  rw [e]
  have hb := H.hb_le
  have hb0 := H.hb0
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans H.hTs) S.opN_P0
  refine ⟨h1.trans (le_of_eq (by unfold RegW.DP; ring)), h2.trans ?_⟩
  have : (1 + (rW d c.n δ).hb) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

theorem P'_mulVec (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    cV (st.B *ᵥ (st.Bᵀ *ᵥ st.mu)) = (cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu := by
  rw [cM_mulVec, cM_mulVec, cM_transpose, Matrix.mulVec_mulVec]

theorem vv_eq (_H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    ((((st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu) : ℚ)) : ℝ) = cV st.mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu) := by
  rw [cV_dot, cM_mulVec, cM_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (cV st.mu),
    ← Matrix.mulVec_transpose]

theorem mu_le (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : oNorm (cV st.mu) ≤ (rW d c.n δ).R := by
  have S := H.sett
  rw [S.track.mu]
  exact S.det.norm_le_of_keps S.inv.mu

theorem R0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).R := (oNorm_nonneg _).trans H.mu_le

theorem Duw0 (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) : 0 ≤ (rW d c.n δ).Duw := (H.R.Duw_le).1

theorem sLam (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    Real.sqrt (rW d c.n δ).Lam * Real.sqrt (rW d c.n δ).Lam = (rW d c.n δ).Lam :=
  Real.mul_self_sqrt H.sett.Lam_pos.le

theorem c0' (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) (hw : ¬ H.Wt) :
    (((rvHW orc c δ st ξ' ζ' ε f).c : ℚ) : ℝ) = 0 ∧ (ctxOW K c δ ap).cc (pwOW K c δ ap π) s = 0 := by
  obtain ⟨h1, h2⟩ := H.c_zero hw
  exact ⟨by rw [h1]; simp, h2⟩

/-- E9w for `b`. -/
theorem errb (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvHW orc c δ st ξ' ζ' ε f).b - (ctxOW K c δ ap).bn (pwOW K c δ ap π) s) ≤
      (s + 1) * (rW d c.n δ).eb := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  set v : Fin d → ℚ := r.c • (((st.B *ᵥ ξ') ⬝ᵥ st.mu) • (st.B *ᵥ ξ') - st.B *ᵥ (st.Bᵀ *ᵥ st.mu))
  have hv : cV v = ((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu) := by
    simp only [v]; rw [cV_smul, cV_sub, cV_smul, cV_dot, H.P'_mulVec, S.track.mu]
  have e : cV r.b - cx.bn πw s = (cV st.b - (cx.st πw s).b) + (cV (rndV c.par.p v) - cV v) +
      (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) • cV (st.B *ᵥ ξ') -
        (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu) -
        cx.cc πw s • ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) • cx.u πw s - (cx.st πw s).P *ᵥ (cx.st πw s).mu)) := by
    have hb : r.b = st.b + rndV c.par.p v := rfl
    rw [hb, cV_add, ← hv]; unfold Df2Ctx.bn; abel
  rw [e]
  have h1 := S.track.errb
  have h2 : oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * (rW d c.n δ).tp / 2 := H.rndV_errH v
  have hP := H.P'_err
  have hX := (Xw_nonneg H.R).2
  have hD := H.Dcw0
  have hcb := H.cbw0
  have hR := H.R0
  have hs := Real.sqrt_nonneg (rW d c.n δ).Lam
  have hDP := (H.R.DP_le).1
  have hDu := H.Duw0
  have h3 : oNorm (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) • cV (st.B *ᵥ ξ') -
        (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu) -
        cx.cc πw s • ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) • cx.u πw s - (cx.st πw s).P *ᵥ (cx.st πw s).mu)) ≤
      (rW d c.n δ).Dcw * (rW d c.n δ).R * ((101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) ^ 2 +
        10201 / 10000 * (rW d c.n δ).Lam) +
      (rW d c.n δ).cbw * (rW d c.n δ).R * ((101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 +
        Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) * (rW d c.n δ).Duw + (rW d c.n δ).DP) := by
    by_cases hw : H.Wt
    · exact inc_b (cV (st.B *ᵥ ξ')) (cx.u πw s) (cx.st πw s).mu (cM st.B * (cM st.B)ᵀ) (cx.st πw s).P
        ((r.c : ℚ) : ℝ) (cx.cc πw s) (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1)
        (Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) (rW d c.n δ).Duw (10201 / 10000 * (rW d c.n δ).Lam)
        (rW d c.n δ).DP (rW d c.n δ).R (rW d c.n δ).Dcw (rW d c.n δ).cbw (H.u'_le hw) (H.u0_le1 hw) (H.du hw)
        hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
    · have hc0 : ((r.c : ℚ) : ℝ) = 0 := (H.c0' hw).1
      have hcc0 : cx.cc πw s = 0 := (H.c0' hw).2
      rw [hc0, hcc0, zero_smul, zero_smul, sub_zero, oNorm_eq]
      simp only [WithLp.toLp_zero, norm_zero]
      have hL0 := S.Lam_pos.le
      have a1 : 0 ≤ (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) ^ 2 +
          10201 / 10000 * (rW d c.n δ).Lam := add_nonneg (sq_nonneg _) (by linarith)
      have a2 : 0 ≤ (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 +
          Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) * (rW d c.n δ).Duw + (rW d c.n δ).DP :=
        add_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hX) (mul_nonneg hs hX)) hDu) hDP
      exact add_nonneg (mul_nonneg (mul_nonneg hD hR) a1) (mul_nonneg (mul_nonneg hcb hR) a2)
  have h4 := eb_geW (r := rW d c.n δ) _ _ _ _ H.sLam hs hX hDu rfl rfl rfl rfl hD hR hcb
  have t1 := oNorm_add_le (cV st.b - (cx.st πw s).b + (cV (rndV c.par.p v) - cV v))
    (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu) -
      cx.cc πw s • ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) • cx.u πw s - (cx.st πw s).P *ᵥ (cx.st πw s).mu))
  have t2 := oNorm_add_le (cV st.b - (cx.st πw s).b) (cV (rndV c.par.p v) - cV v)
  have hsd : Real.sqrt (rW d c.n δ).d = Real.sqrt d := rfl
  rw [hsd] at h4
  nlinarith

/-- E9w for `k`. -/
theorem errk (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).k : ℚ) : ℝ) - (ctxOW K c δ ap).kn (pwOW K c δ ap π) s| ≤
      (s + 1) * (rW d c.n δ).ek := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  set x : ℚ := r.c / 2 * (((st.B *ᵥ ξ') ⬝ᵥ st.mu) ^ 2 - (st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu))
  have hx : ((x : ℚ) : ℝ) = ((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) ^ 2 -
      (cx.st πw s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu)) := by
    simp only [x]; push_cast; rw [cV_dot, H.vv_eq, S.track.mu]
  have e : ((r.k : ℚ) : ℝ) - cx.kn πw s = ((st.k : ℝ) - (cx.st πw s).k) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)) +
      (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) ^ 2 -
        (cx.st πw s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu)) - cx.cc πw s / 2 *
          ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) ^ 2 - (cx.st πw s).mu ⬝ᵥ ((cx.st πw s).P *ᵥ (cx.st πw s).mu))) := by
    have hk : r.k = st.k + rnd c.par.p x := rfl
    rw [hk, ← hx]; push_cast; unfold Df2Ctx.kn; ring
  rw [e]
  have h1 := S.track.errk
  have h2 := H.rnd_errH x
  have hP := H.P'_err
  have hX := (Xw_nonneg H.R).2
  have hD := H.Dcw0
  have hcb := H.cbw0
  have hR := H.R0
  have hs := Real.sqrt_nonneg (rW d c.n δ).Lam
  have hDP := (H.R.DP_le).1
  have hDu := H.Duw0
  have h3 : |((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) ^ 2 -
        (cx.st πw s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu)) - cx.cc πw s / 2 *
          ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) ^ 2 - (cx.st πw s).mu ⬝ᵥ ((cx.st πw s).P *ᵥ (cx.st πw s).mu))| ≤
      (rW d c.n δ).Dcw / 2 * (rW d c.n δ).R ^ 2 *
        ((101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) ^ 2 + 10201 / 10000 * (rW d c.n δ).Lam) +
      (rW d c.n δ).cbw / 2 * (rW d c.n δ).R ^ 2 * ((101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 +
        Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) * (rW d c.n δ).Duw + (rW d c.n δ).DP) := by
    by_cases hw : H.Wt
    · exact inc_k (cV (st.B *ᵥ ξ')) (cx.u πw s) (cx.st πw s).mu (cM st.B * (cM st.B)ᵀ) (cx.st πw s).P
        ((r.c : ℚ) : ℝ) (cx.cc πw s) (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1)
        (Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) (rW d c.n δ).Duw (10201 / 10000 * (rW d c.n δ).Lam)
        (rW d c.n δ).DP (rW d c.n δ).R (rW d c.n δ).Dcw (rW d c.n δ).cbw (H.u'_le hw) (H.u0_le1 hw) (H.du hw)
        hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
    · have hc0 : ((r.c : ℚ) : ℝ) = 0 := (H.c0' hw).1
      have hcc0 : cx.cc πw s = 0 := (H.c0' hw).2
      rw [hc0, hcc0, zero_div, zero_mul, zero_mul, sub_zero, abs_zero]
      have hL0 := S.Lam_pos.le
      have hR2 := sq_nonneg (rW d c.n δ).R
      have a1 : 0 ≤ (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) ^ 2 +
          10201 / 10000 * (rW d c.n δ).Lam := add_nonneg (sq_nonneg _) (by linarith)
      have a2 : 0 ≤ (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 +
          Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) * (rW d c.n δ).Duw + (rW d c.n δ).DP :=
        add_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hX) (mul_nonneg hs hX)) hDu) hDP
      exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) hR2) a1) (mul_nonneg (mul_nonneg (by linarith) hR2) a2)
  have h4 := ek_geW (r := rW d c.n δ) _ _ _ _ H.sLam hs hX hDu rfl rfl rfl rfl hD hR hcb
  have t1 := abs_add_le (((st.k : ℝ) - (cx.st πw s).k) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)))
    (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st πw s).mu) ^ 2 -
      (cx.st πw s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st πw s).mu)) -
      cx.cc πw s / 2 * ((cx.u πw s ⬝ᵥ (cx.st πw s).mu) ^ 2 - (cx.st πw s).mu ⬝ᵥ ((cx.st πw s).P *ᵥ (cx.st πw s).mu)))
  have t2 := abs_add_le ((st.k : ℝ) - (cx.st πw s).k) (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ))
  nlinarith

theorem lam_facts (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    0 < 1 - (poW d c.n δ).lam ∧ (1 + (rW d c.n δ).tp / 16) / (1 - (poW d c.n δ).lam) ≤ 101 / 100 ∧
      1 / (1 - (poW d c.n δ).lam) ≤ 101 / 100 := by
  have hl : (poW d c.n δ).lam ≤ 1 / 1000 := by
    have h := (H.R.lam_bd).2
    have : (1 : ℝ) / (725 * 17467 ^ 2) ≤ 1 / 1000 := by norm_num
    exact h.trans this
  have ht := H.tp_small
  have ht0 := H.tp0
  have h1 : 0 < 1 - (poW d c.n δ).lam := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_iff₀ h1]; nlinarith

/-- E11w: BL's increment `g'` of `G` against `ĝ°`. -/
theorem g_err (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvHW orc c δ st ξ' ζ' ε f).g - (ctxOW K c δ ap).ghat (pwOW K c δ ap π) s) ≤ (rW d c.n δ).eg := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  set v : Fin d → ℚ := (r.Y * c.par.nu) • (st.B *ᵥ ξ')
  have hg : r.g = rndV c.par.p v := rfl
  have hv : cV v = ((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') := by
    simp only [v]; rw [cV_smul]; push_cast; rfl
  have e : cV r.g - cx.ghat πw s = (cV (rndV c.par.p v) - cV v) +
      (((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') - (cx.Y πw s / (1 - cx.p.lam)) • cx.u πw s) := by
    rw [hg, ← hv]; unfold Df2Ctx.ghat; abel
  rw [e]
  have h2 : oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * (rW d c.n δ).tp / 2 := H.rndV_errH v
  have hX := (Xw_nonneg H.R).2
  have hy00 := H.y00
  have hDu := H.Duw0
  have hs := Real.sqrt_nonneg (rW d c.n δ).Lam
  have heY := (H.R.eYw_le).1
  have htp := H.tp0
  have h3 : oNorm (((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') - (cx.Y πw s / (1 - cx.p.lam)) • cx.u πw s) ≤
      101 / 100 * ((rW d c.n δ).eYw + (rW d c.n δ).y0 * (rW d c.n δ).tp / 16) *
        (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) +
      101 / 100 * (rW d c.n δ).y0 * (rW d c.n δ).Duw := by
    by_cases hw : H.Wt
    · obtain ⟨hl, hl1, hl2⟩ := H.lam_facts
      have hcp : (poW d c.n δ).lam = cx.p.lam := rfl
      rw [hcp] at hl hl1 hl2
      have hnu : |((c.par.nu : ℚ) : ℝ) * (1 - (rW d c.n δ).lam) - 1| ≤ (rW d c.n δ).tp / 16 := by
        rw [H.par]; exact H.enc.nu_rel
      have hy := ynu (r.Y : ℝ) (cx.Y πw s) (c.par.nu : ℝ) cx.p.lam (rW d c.n δ).eYw (rW d c.n δ).y0
        (rW d c.n δ).tp H.eY S.Y_le hnu hl hl1 hl2 htp
      have hy0 : |cx.Y πw s / (1 - cx.p.lam)| ≤ 101 / 100 * (rW d c.n δ).y0 := by
        rw [abs_div, abs_of_pos hl, div_eq_mul_one_div]
        calc |cx.Y πw s| * (1 / (1 - cx.p.lam)) ≤ (rW d c.n δ).y0 * (101 / 100) :=
              mul_le_mul S.Y_le hl2 (by positivity) hy00
          _ = _ := by ring
      have h3 := inc_g ((r.Y : ℝ) * (c.par.nu : ℝ)) (cx.Y πw s / (1 - cx.p.lam))
        (101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1) (rW d c.n δ).Duw _ _ (H.u'_le hw) (H.du hw)
      have hU : 0 ≤ 101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 :=
        mul_nonneg (mul_nonneg (by norm_num) hs) hX
      have h4 := mul_le_mul_of_nonneg_right hy hU
      have h5 := mul_le_mul_of_nonneg_right hy0 hDu
      linarith
    · rw [not_or, not_not, not_not] at hw
      have hY0 : ((r.Y : ℚ) : ℝ) = 0 := hw.1
      have hY1 : cx.Y πw s = 0 := hw.2
      rw [hY0, hY1, zero_mul, zero_div, zero_smul, zero_smul, sub_zero, oNorm_eq]
      simp only [WithLp.toLp_zero, norm_zero]
      have hU : 0 ≤ 101 / 100 * Real.sqrt (rW d c.n δ).Lam * (rW d c.n δ).Xw1 :=
        mul_nonneg (mul_nonneg (by norm_num) hs) hX
      have a1 : 0 ≤ (rW d c.n δ).eYw + (rW d c.n δ).y0 * (rW d c.n δ).tp / 16 := by
        have := mul_nonneg hy00 htp; linarith
      exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) a1) hU) (mul_nonneg (mul_nonneg (by norm_num) hy00) hDu)
  have t := oNorm_add_le (cV (rndV c.par.p v) - cV v)
    (((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') - (cx.Y πw s / (1 - cx.p.lam)) • cx.u πw s)
  unfold RegW.eg
  have hsd : Real.sqrt (rW d c.n δ).d = Real.sqrt d := rfl
  rw [hsd]
  nlinarith

/-- E11w for `G`. -/
theorem errG (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvHW orc c δ st ξ' ζ' ε f).G - (ctxOW K c δ ap).Gn (pwOW K c δ ap π) s) ≤
      (s + 1) * (rW d c.n δ).eg := by
  have S := H.sett
  have e : cV (rvHW orc c δ st ξ' ζ' ε f).G - (ctxOW K c δ ap).Gn (pwOW K c δ ap π) s =
      (cV st.G - ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).G) +
        (cV (rvHW orc c δ st ξ' ζ' ε f).g - (ctxOW K c δ ap).ghat (pwOW K c δ ap π) s) := by
    rw [rvOW_G, cV_add]; unfold Df2Ctx.Gn; abel
  rw [e]
  have := oNorm_add_le (cV st.G - ((ctxOW K c δ ap).st (pwOW K c δ ap π) s).G)
    (cV (rvHW orc c δ st ξ' ζ' ε f).g - (ctxOW K c δ ap).ghat (pwOW K c δ ap π) s)
  have h1 := S.track.errG
  have h2 := H.g_err
  nlinarith

/-- E11w for `l`. -/
theorem errl (H : RCHypOW K orc c δ ap π s st ξ' ζ' Z ε f) :
    |(((rvHW orc c δ st ξ' ζ' ε f).l : ℚ) : ℝ) - (ctxOW K c δ ap).ln (pwOW K c δ ap π) s| ≤
      (s + 1) * (rW d c.n δ).el := by
  have S := H.sett
  set cx := ctxOW K c δ ap
  set πw := pwOW K c δ ap π
  set r := rvHW orc c δ st ξ' ζ' ε f
  set x : ℚ := r.g ⬝ᵥ st.mu
  have hl : r.l = st.l + rnd c.par.p x := rfl
  have e : ((r.l : ℚ) : ℝ) - cx.ln πw s = ((st.l : ℝ) - (cx.st πw s).l) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)) +
      (cV r.g - cx.ghat πw s) ⬝ᵥ (cx.st πw s).mu := by
    rw [hl]; push_cast; simp only [x]; rw [cV_dot, S.track.mu, sub_dotProduct]; unfold Df2Ctx.ln; ring
  rw [e]
  have h1 := S.track.errl
  have h2 := H.rnd_errH x
  have h3 : |(cV r.g - cx.ghat πw s) ⬝ᵥ (cx.st πw s).mu| ≤ (rW d c.n δ).eg * (rW d c.n δ).R :=
    (abs_dot_le _ _).trans (mul_le_mul H.g_err (by rw [← S.track.mu]; exact H.mu_le) (oNorm_nonneg _)
      ((oNorm_nonneg _).trans H.g_err))
  have t1 := abs_add_le (((st.l : ℝ) - (cx.st πw s).l) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)))
    ((cV r.g - cx.ghat πw s) ⬝ᵥ (cx.st πw s).mu)
  have t2 := abs_add_le ((st.l : ℝ) - (cx.st πw s).l) (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ))
  have hel : (rW d c.n δ).el = (rW d c.n δ).tp / 2 + (rW d c.n δ).R * (rW d c.n δ).eg := rfl
  rw [hel] at h1 ⊢
  nlinarith

end AdversarialBco.UW.Eng.RCHypOW

namespace AdversarialBco.UW.Eng

open AdversarialBco.UW.Eng.RCHypOW in
/-- **C1 for BL-OW.** -/
theorem c1OW : C1OW := by
  intro d K orc c δ ap π s st ξ' ζ' Z ε f H
  exact ⟨H.ga, H.gt, H.trackA, H.trackB, H.errb, H.errk, H.errG, H.errl, H.eY, H.dq, H.ew⟩

end AdversarialBco.UW.Eng
