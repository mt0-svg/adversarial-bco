/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Run
public import AdversarialBco.Poly.Df2R1Proof
public import AdversarialBco.Poly.Df2ParBounds

@[expose] public section

/-!
# The state of DF2-O in run mode

`df2oMode_run_r`: in run mode, `ε ≤ 1/2` and the radius `st.r` of the state (the radius of the first call of AP in
the round) is `1 - ε` or `s_b (1 - ε)`. `df2oMode_run_R1`: the state satisfies the hypotheses of Lemma D.2 (`P`
positive definite, `A Aᵀ = Σ = P⁻¹`), so that past the test on `a` and `q` the matrix `P'` of the calls of AP is
positive definite. The caps of the calls of AP read both.
-/

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM Matrix

variable {d : ℕ}

/-- `df2Next` in run mode starts an epoch (radius `1 - ε`) or commits the radius `s_b (1 - ε)`. -/
theorem df2Next_run_r {p : Df2OPar} {n : ℕ} {Keps : Set (Fin d → ℝ)} {st : Df2St d} {ξ w : Fin d → ℝ} {Y : ℝ}
    {st' : Df2St d} (h : df2Next p n Keps st ξ w Y = .run st') :
    st'.r = 1 - p.eps ∨ st'.r = p.sb * (1 - p.eps) := by
  unfold df2Next at h
  simp only at h
  split_ifs at h
  all_goals (try (split at h))
  all_goals (try (split_ifs at h))
  all_goals (try (split at h))
  all_goals (try cases h)
  all_goals first | (left; rfl) | (right; rfl)

/-- A round ends in run mode only from run mode, with the radius of `df2Next_run_r`. -/
theorem df2Round_run_r {p : Df2OPar} {n : ℕ} {K : Set (E d)} {Ps : PgSp d} {ft : E d → ℝ} {nt : ℝ}
    {ξ : Fin d → ℝ} {ζ : ℝ} {m : Df2Mode d} {st' : Df2St d} (h : (df2Round p n K Ps ft nt ξ ζ m).2 = .run st') :
    (∃ st, m = .run st) ∧ (st'.r = 1 - p.eps ∨ st'.r = p.sb * (1 - p.eps)) := by
  cases m with
  | off => cases h
  | guard =>
    unfold df2Round at h
    split_ifs at h
  | run st =>
    unfold df2Round at h
    simp only at h
    split_ifs at h
    · exact ⟨⟨st, rfl⟩, df2Next_run_r h⟩

/-- In run mode, `ε ≤ 1/2` and the radius of the state is `1 - ε` (the start of an epoch) or `s_b (1 - ε)`. -/
theorem df2oMode_run_r (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (st : Df2St d)
    (h : df2oMode d n r0 R0 δ w t = .run st) :
    (df2oPar d n δ).eps ≤ 1 / 2 ∧
      (st.r = 1 - (df2oPar d n δ).eps ∨ st.r = (df2oPar d n δ).sb * (1 - (df2oPar d n δ).eps)) := by
  induction t generalizing st with
  | zero =>
    change df2oMode0 d n r0 R0 δ w = .run st at h
    unfold df2oMode0 at h
    split at h
    · cases h
    · split_ifs at h with he
      cases h; exact ⟨le_of_not_gt he, Or.inl rfl⟩
  | succ t ih =>
    have e : df2oMode d n r0 R0 δ w (t + 1) = (df2oRoundAt d n r0 R0 δ w t (df2oMode d n r0 R0 δ w t)).2 := by
      simp only [df2oMode, df2oFrom, Nat.zero_add]
    rw [e] at h
    obtain ⟨⟨st0, h0⟩, hr⟩ := df2Round_run_r h
    exact ⟨(ih st0 h0).1, hr⟩

/-- The two ends of `df2Next` in run mode: the start of an epoch, or the update of Lemma D.2 past the test on `a`
and `q`. -/
theorem df2Next_run_shape {p : Df2OPar} {n : ℕ} {Keps : Set (Fin d → ℝ)} {st : Df2St d} {ξ : Fin d → ℝ} {Y : ℝ}
    {st' : Df2St d} (h : df2Next p n Keps st ξ (st.A *ᵥ ξ) Y = .run st') :
    st' = df2Init p d ∨
      (0 < 1 - p.eta * p.kap * p.lam * p.k0 * Y ∧ 0 < r1Q (p.eta * p.kap * p.lam * p.k0 * Y) ξ ∧
        st'.P = r1P' st.P st.A ξ (p.eta * p.kap * p.lam * p.k0 * Y) ∧
        st'.S = r1S' st.S st.A ξ (p.eta * p.kap * p.lam * p.k0 * Y) ∧
        st'.A = r1A' st.A ξ (p.eta * p.kap * p.lam * p.k0 * Y)) := by
  unfold df2Next at h
  simp only at h
  split_ifs at h with h1
  all_goals (try (split at h))
  all_goals (try (split_ifs at h))
  all_goals (try (split at h))
  all_goals (try cases h)
  all_goals first
    | (left; rfl)
    | (right
       simp only [not_or, not_le] at h1
       exact ⟨h1.1, h1.2, rfl, rfl, rfl⟩)

/-- The start of an epoch satisfies the hypotheses of Lemma D.2 when `σ² > 0`. -/
theorem df2Init_R1 (p : Df2OPar) (hs : 0 < p.sig2) :
    R1Hyp (df2Init p d).P (df2Init p d).S (df2Init p d).A := by
  refine ⟨Matrix.PosDef.one.smul (inv_pos.2 hs), ?_, ?_⟩
  · show (Real.sqrt p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (Real.sqrt p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ =
      p.sig2 • 1
    rw [transpose_smul, transpose_one, smul_mul_smul_comm, one_mul, Real.mul_self_sqrt hs.le]
  · show (p.sig2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * (p.sig2⁻¹ • 1) = 1
    rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hs.ne', one_smul]

/-- `df2Next` keeps the hypotheses of Lemma D.2 on the state. -/
theorem df2Next_R1 {p : Df2OPar} {n : ℕ} {Keps : Set (Fin d → ℝ)} {st : Df2St d} {ξ : Fin d → ℝ} {Y : ℝ}
    {st' : Df2St d} (hs : 0 < p.sig2) (hR : R1Hyp st.P st.S st.A)
    (h : df2Next p n Keps st ξ (st.A *ᵥ ξ) Y = .run st') : R1Hyp st'.P st'.S st'.A := by
  rcases df2Next_run_shape h with e | ⟨ha, hq, hP, hS, hA⟩
  · rw [e]; exact df2Init_R1 p hs
  · rw [hP, hS, hA]
    exact ⟨(lemmaR1i d _ _ _ ξ _ hR).2.2.2.2.1 ha hq, (lemmaR1iii d _ _ _ ξ _ hR ha hq).2.1,
      (lemmaR1ii d _ _ _ ξ _ hR ha hq).1⟩

/-- In run mode the state satisfies the hypotheses of Lemma D.2: `P` positive definite and `A Aᵀ = Σ = P⁻¹`. -/
theorem df2oMode_run_R1 (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (r0 R0 δ : ℝ) (hδ : 0 < δ) (w : World d) (t : ℕ)
    (st : Df2St d) (h : df2oMode d n r0 R0 δ w t = .run st) : R1Hyp st.P st.S st.A := by
  have hs : 0 < (df2oPar d n δ).sig2 := by
    have := df2oPar_Le_ge d n hd hn δ hδ
    show 0 < 1 / (8 * (df2oPar d n δ).Le)
    positivity
  induction t generalizing st with
  | zero =>
    change df2oMode0 d n r0 R0 δ w = .run st at h
    unfold df2oMode0 at h
    split at h
    · cases h
    · split_ifs at h
      cases h; exact df2Init_R1 _ hs
  | succ t ih =>
    have e : df2oMode d n r0 R0 δ w (t + 1) = (df2oRoundAt d n r0 R0 δ w t (df2oMode d n r0 R0 δ w t)).2 := by
      simp only [df2oMode, df2oFrom, Nat.zero_add]
    rw [e] at h
    unfold df2oRoundAt at h
    generalize df2oMode d n r0 R0 δ w t = m at h ih
    cases m with
    | off => cases h
    | guard => unfold df2Round at h; split_ifs at h
    | run st0 =>
      unfold df2Round at h
      simp only at h
      split_ifs at h
      exact df2Next_R1 hs (ih st0 rfl) h

end AdversarialBco.Poly
