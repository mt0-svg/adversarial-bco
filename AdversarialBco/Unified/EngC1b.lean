/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngC1a

@[expose] public section

/-!
# Piece C for BL-O, part C1 (b): Lemma TRACK at `s + 1` and the fields

Bit/BLRoundC1.lean (second half) for BL-O at `k`: E4 and Lemma TRACK for `A'` and `B'` at `s + 1`, the guard R10,
E7 and E8 (`u`, `w`, `P`), E9 and E11 (the fields `b, k, G, l`), and `c1O : C1O`. Nothing here reads the gauge, the
oracle or the reading beyond `eY` of part (a).
-/

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-! ## Lemma TRACK at `s + 1` -/

theorem hT (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (j : ℕ) (hj : j ≤ c.n) : BudK.hTr d c.n k j ≤ 1 / 100 :=
  (H.bud.hTr_le j hj).trans H.bud.hb_le

/-- E4 and TRACK for `A`: `A'_+ = (I + H') A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackA (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvH orc c st ξ' ζ' ε f).A = (1 + H') * (ctxO K c k ap).An π s ∧
      opN H' ≤ BudK.hTr d c.n k (s + 1) := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  set M := r.s1 • st.A - r.s2 • vecMulVec (st.A *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s1 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-((r.s2 : ℚ) : ℝ)) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := (Real.sqrt (cx.aa π s))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) +
    (-phi cx π s) • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.A * N' := by
    rw [cM_sub, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, sub_eq_add_neg, ← neg_smul, fac_mul]
  have hr : cM r.A = (1 + H0) * (cx.st π s).A * N' + (cM r.A - cM M) := by
    rw [← hA0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm (cx.st π s).A (cx.An π s) ((cx.An π s)ᵀ * cx.Pn π s) N0 N' (cM r.A - cM M) H0
    S.An_fac S.An_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.A - cM M) ≤ BudK.nu d c.n k := by
    rw [← H.nu_eqH]; exact rndM_err _ M
  exact track_numK s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_A0 (opN_nonneg _) S.opN_AnPn
    (opN_nonneg _) H.e3A (opN_nonneg _) hρ S.Lam_pos.le

/-- E4 and TRACK for `B`: `B'_+ = (I + H') P°_{s+1} A°_{s+1}` with `|H'| ≤ hTr (s + 1)`. -/
theorem trackB (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ∃ H' : Matrix (Fin d) (Fin d) ℝ, cM (rvH orc c st ξ' ζ' ε f).B =
      (1 + H') * ((ctxO K c k ap).Pn π s * (ctxO K c k ap).An π s) ∧
      opN H' ≤ BudK.hTr d c.n k (s + 1) := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  set M := r.s3 • st.B + r.s4 • vecMulVec (st.B *ᵥ ξ') ξ'
  set N' : Matrix (Fin d) (Fin d) ℝ := ((r.s3 : ℚ) : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    ((r.s4 : ℚ) : ℝ) • vecMulVec (cV ξ') (cV ξ')
  set N0 : Matrix (Fin d) (Fin d) ℝ := Real.sqrt (cx.aa π s) • (1 : Matrix (Fin d) (Fin d) ℝ) +
    psi cx π s • vecMulVec (π.xi s) (π.xi s)
  have hM : cM M = cM st.B * N' := by
    rw [cM_add, cM_smul, cM_smul, cM_vecMulVec, cM_mulVec, fac_mul]
  have hr : cM r.B = (1 + H0) * ((cx.st π s).P * (cx.st π s).A) * N' + (cM r.B - cM M) := by
    rw [← hB0, ← hM]; abel
  obtain ⟨H', e, hH'⟩ := track_norm ((cx.st π s).P * (cx.st π s).A) (cx.Pn π s * cx.An π s) (cx.An π s)ᵀ N0 N'
    (cM r.B - cM M) H0 S.PnAn_fac S.PnAn_inv
  refine ⟨H', hr.trans e, hH'.trans ?_⟩
  have hρ : opN (cM r.B - cM M) ≤ BudK.nu d c.n k := by
    rw [← H.nu_eqH]; exact rndM_err _ M
  exact track_numK s _ _ _ _ _ (opN_nonneg _) hH0 (opN_nonneg _) S.opN_PA0 (opN_nonneg _)
    (by rw [opN_transpose]; exact S.opN_An) (opN_nonneg _) H.e3B (opN_nonneg _) hρ S.Lam_pos.le

theorem frob2_cast (M : Matrix (Fin d) (Fin d) ℚ) : ((frob2 M : ℚ) : ℝ) = ∑ i, ∑ j, (cM M i j) ^ 2 := by
  simp [frob2, cM]

/-- GUARD (E18), R10: the traces of `A'_+ A'_+ᵀ` and `B'_+ B'_+ᵀ` are at most `(1 + ℏ)² Λ ≤ 2Λ`. -/
theorem gt (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvH orc c st ξ' ζ' ε f).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvH orc c st ξ' ζ' ε f).A) := by
  have S := H.sett
  have hL : ((c.par.Lam : ℕ) : ℝ) = BudK.Lam d c.n k := by rw [H.par]; exact H.bud.enc.Lam_eq
  have hb := H.hT (s + 1) H.hs
  have hLp := S.Lam_pos
  have key : ∀ X : Matrix (Fin d) (Fin d) ℚ, ∀ Y : Matrix (Fin d) (Fin d) ℝ,
      (∃ H' : Matrix (Fin d) (Fin d) ℝ, cM X = (1 + H') * Y ∧ opN H' ≤ BudK.hTr d c.n k (s + 1)) →
      (Y * Yᵀ).trace ≤ BudK.Lam d c.n k → ¬ (2 * (c.par.Lam : ℚ) < frob2 X) := by
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


theorem hb0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.hb d c.n k := NK.hb_nonneg H.bud

theorem hTs (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : BudK.hTr d c.n k s ≤ BudK.hb d c.n k := H.bud.hTr_le s H.hs.le

/-- E7: `|w' - w°| ≤ Δ_u`. -/
theorem ew (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (st.A *ᵥ ξ') - (ctxO K c k ap).w π s) ≤ BudK.Du d c.n k := by
  have S := H.sett
  obtain ⟨H0, hA0, hH0⟩ := S.track.hA
  rw [cM_mulVec, hA0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_A0 (hH0.trans H.hTs) S.xi'_le S.dxi_le

/-- `u' = B'ξ'` as a real vector. -/
theorem u'_eq (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : cV (st.B *ᵥ ξ') = cM st.B *ᵥ cV ξ' := cM_mulVec _ _

theorem u0_eq (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (ctxO K c k ap).u π s =
      (((ctxO K c k ap).st π s).P * ((ctxO K c k ap).st π s).A) *ᵥ π.xi s := by
  rw [← Matrix.mulVec_mulVec]; rfl

/-- E7: `|u' - u°| ≤ Δ_u`. -/
theorem du (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (st.B *ᵥ ξ') - (ctxO K c k ap).u π s) ≤ BudK.Du d c.n k := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  rw [H.u'_eq, H.u0_eq, hB0]
  exact fac_vec_err _ _ _ _ _ _ _ _ S.opN_PA0 (hH0.trans H.hTs) S.xi'_le S.dxi_le

theorem u0_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm ((ctxO K c k ap).u π s) ≤ Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k := by
  have S := H.sett
  rw [H.u0_eq]
  exact (oNorm_mulVec_le _ _).trans (mul_le_mul S.opN_PA0 S.xi_le1 (oNorm_nonneg _) (Real.sqrt_nonneg _))

theorem Du_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.Du d c.n k ≤ 1 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k + Real.sqrt (BudK.Lam d c.n k) * BudK.exi d c.n k := by
  unfold BudK.Du
  have := H.bud.hb_le; have := (NK.Xi1_pos d c.n k).le; have := Real.sqrt_nonneg (BudK.Lam d c.n k)
  nlinarith [mul_le_mul_of_nonneg_right H.bud.hb_le (mul_nonneg (Real.sqrt_nonneg (BudK.Lam d c.n k)) (NK.Xi1_pos d c.n k).le)]

theorem u'_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (st.B *ᵥ ξ')) ≤ 101 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k := by
  have S := H.sett
  have h1 := H.du
  have h2 : oNorm ((ctxO K c k ap).u π s) ≤ Real.sqrt (BudK.Lam d c.n k) * BudK.Xi d c.n k := by
    rw [H.u0_eq]
    exact (oNorm_mulVec_le _ _).trans (mul_le_mul S.opN_PA0 S.xi_le (oNorm_nonneg _) (Real.sqrt_nonneg _))
  have h3 := oNorm_add_le ((ctxO K c k ap).u π s) (cV (st.B *ᵥ ξ') - (ctxO K c k ap).u π s)
  rw [add_sub_cancel] at h3
  have h4 := H.Du_le
  have hs := Real.sqrt_nonneg (BudK.Lam d c.n k)
  have h5 : Real.sqrt (BudK.Lam d c.n k) * BudK.Xi d c.n k + Real.sqrt (BudK.Lam d c.n k) * BudK.exi d c.n k ≤
      Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k := by
    rw [← mul_add]; unfold BudK.Xi1; exact mul_le_mul_of_nonneg_left (by linarith [S.exi_le_one]) hs
  linarith

/-- BL's `P' = B'B'ᵀ` of round `s`. -/
theorem P'_err (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    opN (cM st.B * (cM st.B)ᵀ - ((ctxO K c k ap).st π s).P) ≤ BudK.DP d c.n k ∧
      opN (cM st.B * (cM st.B)ᵀ) ≤ 10201 / 10000 * BudK.Lam d c.n k := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := S.track.hB
  have e : cM st.B * (cM st.B)ᵀ = (1 + H0) * ((ctxO K c k ap).st π s).P * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * (((ctxO K c k ap).st π s).P * ((ctxO K c k ap).st π s).A) *
          ((((ctxO K c k ap).st π s).P * ((ctxO K c k ap).st π s).A)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * ((((ctxO K c k ap).st π s).P * ((ctxO K c k ap).st π s).A) *
          (((ctxO K c k ap).st π s).P * ((ctxO K c k ap).st π s).A)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PA_sq]
  rw [e]
  have hb := H.bud.hb_le
  have hb0 := H.hb0
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans H.hTs) S.opN_P0
  refine ⟨h1.trans (le_of_eq (by unfold BudK.DP; ring)), h2.trans ?_⟩
  have : (1 + BudK.hb d c.n k) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

theorem P'_mulVec (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    cV (st.B *ᵥ (st.Bᵀ *ᵥ st.mu)) = (cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu := by
  rw [cM_mulVec, cM_mulVec, cM_transpose, Matrix.mulVec_mulVec]

theorem vv_eq (_H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ((((st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu) : ℚ)) : ℝ) = cV st.mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ cV st.mu) := by
  rw [cV_dot, cM_mulVec, cM_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (cV st.mu),
    ← Matrix.mulVec_transpose]

theorem mu_le (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : oNorm (cV st.mu) ≤ BudK.R d c.n k := by
  have S := H.sett
  rw [S.track.mu]
  exact S.det.norm_le_of_keps S.inv.mu

theorem R0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.R d c.n k := (oNorm_nonneg _).trans H.mu_le


theorem Du0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.Du d c.n k := (oNorm_nonneg _).trans H.du

theorem sLam (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    Real.sqrt (BudK.Lam d c.n k) * Real.sqrt (BudK.Lam d c.n k) = BudK.Lam d c.n k := Real.mul_self_sqrt H.sett.Lam_pos.le

/-- E9 for `b`. -/
theorem errb (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvH orc c st ξ' ζ' ε f).b - (ctxO K c k ap).bn π s) ≤ (s + 1) * BudK.eb d c.n k := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  set v : Fin d → ℚ := r.c • (((st.B *ᵥ ξ') ⬝ᵥ st.mu) • (st.B *ᵥ ξ') - st.B *ᵥ (st.Bᵀ *ᵥ st.mu))
  have hv : cV v = ((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu) := by
    simp only [v]; rw [cV_smul, cV_sub, cV_smul, cV_dot, H.P'_mulVec, S.track.mu]
  have e : cV r.b - cx.bn π s = (cV st.b - (cx.st π s).b) + (cV (rndV c.par.p v) - cV v) +
      (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) • cV (st.B *ᵥ ξ') -
        (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu) -
        cx.cc π s • ((cx.u π s ⬝ᵥ (cx.st π s).mu) • cx.u π s - (cx.st π s).P *ᵥ (cx.st π s).mu)) := by
    have hb : r.b = st.b + rndV c.par.p v := rfl
    rw [hb, cV_add, ← hv]; unfold Df2Ctx.bn; abel
  rw [e]
  have h1 := S.track.errb
  have h2 : oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * BudK.tp d c.n k / 2 := by
    exact H.rndV_errH v
  have hP := H.P'_err
  have h3 := inc_b (cV (st.B *ᵥ ξ')) (cx.u π s) (cx.st π s).mu (cM st.B * (cM st.B)ᵀ) (cx.st π s).P
    ((r.c : ℚ) : ℝ) (cx.cc π s) (101 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k)
    (Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k) (BudK.Du d c.n k) (10201 / 10000 * BudK.Lam d c.n k) (BudK.DP d c.n k) (BudK.R d c.n k)
    (BudK.Dc d c.n k) (BudK.cb d c.n k) H.u'_le H.u0_le H.du hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
  have h4 := eb_geK (d := d) (n := c.n) (k := k) _ _ _ _ H.sLam (Real.sqrt_nonneg _) (NK.Xi1_pos d c.n k).le H.Du0 rfl rfl rfl rfl
    H.Dc0 H.R0 H.cb0
  have t1 := oNorm_add_le (cV st.b - (cx.st π s).b + (cV (rndV c.par.p v) - cV v))
    (((r.c : ℚ) : ℝ) • ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) • cV (st.B *ᵥ ξ') -
      (cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu) -
      cx.cc π s • ((cx.u π s ⬝ᵥ (cx.st π s).mu) • cx.u π s - (cx.st π s).P *ᵥ (cx.st π s).mu))
  have t2 := oNorm_add_le (cV st.b - (cx.st π s).b) (cV (rndV c.par.p v) - cV v)
  nlinarith

/-- E9 for `k`. -/
theorem errk (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).k : ℚ) : ℝ) - (ctxO K c k ap).kn π s| ≤ (s + 1) * BudK.ek d c.n k := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  set x : ℚ := r.c / 2 * (((st.B *ᵥ ξ') ⬝ᵥ st.mu) ^ 2 - (st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu))
  have hx : ((x : ℚ) : ℝ) = ((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) ^ 2 -
      (cx.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu)) := by
    simp only [x]; push_cast; rw [cV_dot, H.vv_eq, S.track.mu]
  have e : ((r.k : ℚ) : ℝ) - cx.kn π s = ((st.k : ℝ) - (cx.st π s).k) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)) +
      (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) ^ 2 -
        (cx.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu)) - cx.cc π s / 2 * ((cx.u π s ⬝ᵥ (cx.st π s).mu) ^ 2 -
        (cx.st π s).mu ⬝ᵥ ((cx.st π s).P *ᵥ (cx.st π s).mu))) := by
    have hk : r.k = st.k + rnd c.par.p x := rfl
    rw [hk, ← hx]; push_cast; unfold Df2Ctx.kn; ring
  rw [e]
  have h1 := S.track.errk
  have h2 := H.rnd_errH x
  have hP := H.P'_err
  have h3 := inc_k (cV (st.B *ᵥ ξ')) (cx.u π s) (cx.st π s).mu (cM st.B * (cM st.B)ᵀ) (cx.st π s).P
    ((r.c : ℚ) : ℝ) (cx.cc π s) (101 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k)
    (Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k) (BudK.Du d c.n k) (10201 / 10000 * BudK.Lam d c.n k) (BudK.DP d c.n k) (BudK.R d c.n k)
    (BudK.Dc d c.n k) (BudK.cb d c.n k) H.u'_le H.u0_le H.du hP.2 hP.1 (by rw [← S.track.mu]; exact H.mu_le) H.dc S.cc_le
  have h4 := ek_geK (d := d) (n := c.n) (k := k) _ _ _ _ H.sLam (Real.sqrt_nonneg _) (NK.Xi1_pos d c.n k).le H.Du0 rfl rfl rfl rfl
    H.Dc0 H.R0 H.cb0
  have t1 := abs_add_le (((st.k : ℝ) - (cx.st π s).k) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)))
    (((r.c : ℚ) : ℝ) / 2 * ((cV (st.B *ᵥ ξ') ⬝ᵥ (cx.st π s).mu) ^ 2 -
      (cx.st π s).mu ⬝ᵥ ((cM st.B * (cM st.B)ᵀ) *ᵥ (cx.st π s).mu)) -
      cx.cc π s / 2 * ((cx.u π s ⬝ᵥ (cx.st π s).mu) ^ 2 - (cx.st π s).mu ⬝ᵥ ((cx.st π s).P *ᵥ (cx.st π s).mu)))
  have t2 := abs_add_le ((st.k : ℝ) - (cx.st π s).k) (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ))
  nlinarith


theorem lam_facts (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 < 1 - (poK d c.n k).lam ∧ (1 + BudK.tp d c.n k / 16) / (1 - (poK d c.n k).lam) ≤ 101 / 100 ∧
      1 / (1 - (poK d c.n k).lam) ≤ 101 / 100 := by
  have hl := H.sett.lam_small
  have hl0 := H.sett.lam_pos
  have ht := NK.tp_small d c.n k
  have h1 : 0 < 1 - (poK d c.n k).lam := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_iff₀ h1]; nlinarith

/-- E11: BL's increment `g'` of `G` against `ĝ°`. -/
theorem g_err (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvH orc c st ξ' ζ' ε f).g - (ctxO K c k ap).ghat π s) ≤ BudK.eg d c.n k := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  set v : Fin d → ℚ := (r.Y * c.par.nu) • (st.B *ᵥ ξ')
  have hg : r.g = rndV c.par.p v := rfl
  have hv : cV v = ((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') := by
    simp only [v]; rw [cV_smul]; push_cast; rfl
  have e : cV r.g - cx.ghat π s = (cV (rndV c.par.p v) - cV v) +
      (((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') - (cx.Y π s / (1 - cx.p.lam)) • cx.u π s) := by
    rw [hg, ← hv]; unfold Df2Ctx.ghat; abel
  rw [e]
  have h2 : oNorm (cV (rndV c.par.p v) - cV v) ≤ Real.sqrt d * BudK.tp d c.n k / 2 := by
    exact H.rndV_errH v
  obtain ⟨hl, hl1, hl2⟩ := H.lam_facts
  have hcp : (poK d c.n k).lam = cx.p.lam := rfl
  rw [hcp] at hl hl1 hl2
  have hnu : |((c.par.nu : ℚ) : ℝ) * (1 - BudK.lam d c.n k) - 1| ≤ BudK.tp d c.n k / 16 := by
    rw [H.par]; exact H.bud.enc.nu_rel
  have hy := ynu (r.Y : ℝ) (cx.Y π s) (c.par.nu : ℝ) cx.p.lam (BudK.eY d c.n k) (BudK.Yb d c.n k) (BudK.tp d c.n k) H.eY
    S.Y_le hnu hl hl1 hl2 (NK.tp_pos d c.n k).le
  have hy0 : |cx.Y π s / (1 - cx.p.lam)| ≤ 101 / 100 * BudK.Yb d c.n k := by
    rw [abs_div, abs_of_pos hl, div_eq_mul_one_div]
    have hYb0 : 0 ≤ BudK.Yb d c.n k := (abs_nonneg _).trans S.Y_le
    calc |cx.Y π s| * (1 / (1 - cx.p.lam)) ≤ BudK.Yb d c.n k * (101 / 100) :=
          mul_le_mul S.Y_le hl2 (by positivity) hYb0
      _ = _ := by ring
  have h3 := inc_g ((r.Y : ℝ) * (c.par.nu : ℝ)) (cx.Y π s / (1 - cx.p.lam))
    (101 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k) (BudK.Du d c.n k) _ _ H.u'_le H.du
  have hU : 0 ≤ 101 / 100 * Real.sqrt (BudK.Lam d c.n k) * BudK.Xi1 d c.n k := by
    have := (NK.Xi1_pos d c.n k).le; positivity
  have h4 := mul_le_mul_of_nonneg_right hy hU
  have h5 := mul_le_mul_of_nonneg_right hy0 H.Du0
  have t := oNorm_add_le (cV (rndV c.par.p v) - cV v)
    (((r.Y : ℝ) * (c.par.nu : ℝ)) • cV (st.B *ᵥ ξ') - (cx.Y π s / (1 - cx.p.lam)) • cx.u π s)
  unfold BudK.eg
  nlinarith

/-- E11 for `G`. -/
theorem errG (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    oNorm (cV (rvH orc c st ξ' ζ' ε f).G - (ctxO K c k ap).Gn π s) ≤ (s + 1) * BudK.eg d c.n k := by
  have S := H.sett
  have e : cV (rvH orc c st ξ' ζ' ε f).G - (ctxO K c k ap).Gn π s =
      (cV st.G - ((ctxO K c k ap).st π s).G) +
        (cV (rvH orc c st ξ' ζ' ε f).g - (ctxO K c k ap).ghat π s) := by
    rw [rvO_G, cV_add]; unfold Df2Ctx.Gn; abel
  rw [e]
  have := oNorm_add_le (cV st.G - ((ctxO K c k ap).st π s).G)
    (cV (rvH orc c st ξ' ζ' ε f).g - (ctxO K c k ap).ghat π s)
  have h1 := S.track.errG
  have h2 := H.g_err
  nlinarith

/-- E11 for `l`. -/
theorem errl (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(((rvH orc c st ξ' ζ' ε f).l : ℚ) : ℝ) - (ctxO K c k ap).ln π s| ≤ (s + 1) * BudK.el d c.n k := by
  have S := H.sett
  set cx := ctxO K c k ap
  set r := rvH orc c st ξ' ζ' ε f
  set x : ℚ := r.g ⬝ᵥ st.mu
  have hl : r.l = st.l + rnd c.par.p x := rfl
  have e : ((r.l : ℚ) : ℝ) - cx.ln π s = ((st.l : ℝ) - (cx.st π s).l) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)) +
      (cV r.g - cx.ghat π s) ⬝ᵥ (cx.st π s).mu := by
    rw [hl]; push_cast; simp only [x]; rw [cV_dot, S.track.mu, sub_dotProduct]; unfold Df2Ctx.ln; ring
  rw [e]
  have h1 := S.track.errl
  have h2 := H.rnd_errH x
  have h3 : |(cV r.g - cx.ghat π s) ⬝ᵥ (cx.st π s).mu| ≤ BudK.eg d c.n k * BudK.R d c.n k :=
    (abs_dot_le _ _).trans (mul_le_mul H.g_err (by rw [← S.track.mu]; exact H.mu_le) (oNorm_nonneg _)
      ((oNorm_nonneg _).trans H.g_err))
  have t1 := abs_add_le (((st.l : ℝ) - (cx.st π s).l) + (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ)))
    ((cV r.g - cx.ghat π s) ⬝ᵥ (cx.st π s).mu)
  have t2 := abs_add_le ((st.l : ℝ) - (cx.st π s).l) (((rnd c.par.p x : ℚ) : ℝ) - (x : ℝ))
  have hel : BudK.el d c.n k = BudK.tp d c.n k / 2 + BudK.R d c.n k * BudK.eg d c.n k := rfl
  rw [hel] at h1 ⊢
  nlinarith


end AdversarialBco.Unified.Eng.RCHypO

namespace AdversarialBco.Unified.Eng

open AdversarialBco.Unified.Eng.RCHypO in
/-- **C1 for BL-O.** -/
theorem c1O : C1O := by
  intro d K orc c k ap π s st ξ' ζ' Z ε f H
  exact ⟨H.ga, H.gt, H.trackA, H.trackB, H.errb, H.errk, H.errG, H.errl, H.eY, H.dq, H.ew⟩

end AdversarialBco.Unified.Eng
