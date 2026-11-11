/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachDf2B
public import AdversarialBco.Poly.MachAP
public import AdversarialBco.Poly.Df2ModeInv

@[expose] public section

/-!
# The calls of AP in a round of DF2-O: layout and read sets

The layouts of the two calls of AP in `df2Next` (`apV1_ok`, `apV2_ok`) and the facts their membership codes read,
kept by AP (`iq1_rule`, `iq2_rule`): the inputs of the rule of the code of AP, from which `ApRules` follows.
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly Matrix

variable {d : ℕ} {w : World d}

/-- The layout of the first call of AP. -/
theorem apV1_ok : apV1.Ok df2L [3, 4, 5] memS [12, 13, 95] := by
  constructor <;> decide

/-- The layout of the second call of AP. -/
theorem apV2_ok : apV2.Ok df2L [3, 4, 5] memS [12, 13, 95] := by
  constructor <;> decide

/-- What the membership code of the first call reads is kept by AP. -/
theorem iq1_rule (p : Df2OPar) (Ps : PgSp d) (st : Df2St d) : AP.IqRule apV1 (Iq1 p Ps st) :=
  fun _ _ h hF => h.frame hF (by decide) (by decide)

/-- What the membership code of the second call reads is kept by AP. -/
theorem iq2_rule (p : Df2OPar) (Ps : PgSp d) (F : NxF d) : AP.IqRule apV2 (Iq2 p Ps F) :=
  fun _ _ h hF => h.frame hF (by decide) (by decide)


/-- The rule of the first call of AP within `K` steps, when `K` bounds the steps `kAP` of AP on its inputs. -/
theorem apSpec1 (p : Df2OPar) (Ps : PgSp d) (st : Df2St d) (F : NxF d) (hd : 1 ≤ d) (K : ℕ)
    (hK : ∀ σ, nxI1 p Ps st F σ → AP.kAP d (kMemR d) (σ.sc 26) (σ.sc 17) (σ.mat 80) (σ.vec 86) (σ.sc 91) ≤ K) :
    ApSpec w memRm apV1 (nxRm p (df2Keps w.K Ps p.R p.eps) st) (nxI1 p Ps st F) K :=
  fun σ hI hd' h1 => runs_mono (AP.runs_apCode apV1_ok (runs_memRm p Ps st) (iq1_rule p Ps st) σ hd' h1 hI.1
    (by omega)) (hK σ hI) (fun _ h => ⟨h.1, h.2.2⟩)

/-- The rule of the second call of AP within `K` steps, when `K` bounds the steps `kAP` of AP on its inputs. -/
theorem apSpec2 (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (F : NxF d) (pt wmu : Fin d → ℝ) (hd : 1 ≤ d) (K : ℕ)
    (hK : ∀ σ, nxI2 p n Ps F pt wmu σ →
      AP.kAP d (kMemR d) (σ.sc 100) (σ.sc 17) (σ.mat 80) (σ.vec 91) (σ.sc 106) ≤ K) :
    ApSpec w memRp apV2 {y | y ∈ df2Keps w.K Ps p.R p.eps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho}
      (nxI2 p n Ps F pt wmu) K :=
  fun σ hI hd' h1 => runs_mono (AP.runs_apCode apV2_ok (runs_memRp p Ps F) (iq2_rule p Ps F) σ hd' h1 hI.1
    (by omega)) (hK σ hI) (fun _ h => ⟨h.1, h.2.2⟩)

/-- The cap of the first call of AP: radii `s_b/2 ≤ r ≤ R`, trace at most `d/δ_e`, `‖z‖ ≤ R/δ_e³`, accuracy `1`. -/
noncomputable def apCap1 (d : ℕ) (p : Df2OPar) : ℕ :=
  AP.kAPcap d (kMemR d) (p.sb / 2) p.R ((d : ℝ) / p.δe) (p.R / p.δe ^ 3) 1

/-- The cap of the second call of AP: radii `s_b/2 ≤ r ≤ R`, trace at most `d/δ_e`, the bound of the test on
`w_μ`, and the accuracy at the largest trace. -/
noncomputable def apCap2 (d n : ℕ) (p : Df2OPar) : ℕ :=
  AP.kAPcap d (kMemR d) (p.sb / 2) p.R ((d : ℝ) / p.δe) (p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe))
    (1 / (16 * (n : ℝ) ^ 2 * max 1 (4 * p.R ^ 2 * ((d : ℝ) / p.δe))))

/-- The two calls of AP in `df2Next` run within `apCap1` and `apCap2` steps when the state satisfies the hypotheses
of Lemma D.2, its radius is `1 - ε` or `s_b (1 - ε)` with `0 ≤ ε ≤ 1/2`, `0 < s_b ≤ 1 ≤ R`, and the accuracy of the
first call is `1`. -/
theorem apRules_of (p : Df2OPar) (n : ℕ) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) (Y : ℝ) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hR1 : R1Hyp st.P st.S st.A) (hsb0 : 0 < p.sb) (hsb1 : p.sb ≤ 1) (heps0 : 0 ≤ p.eps)
    (heps : p.eps ≤ 1 / 2) (hR : 1 ≤ p.R) (hr : st.r = 1 - p.eps ∨ st.r = p.sb * (1 - p.eps))
    (he1 : min 1 (p.alpha * p.rho / 2) = 1) :
    ApRules w p n Ps st ξ Y (apCap1 d p) (apCap2 d n p) := by
  have hPD : NxG0 p ξ Y → (nxFields p st ξ (st.A *ᵥ ξ) Y).P.PosDef := fun h0 =>
    (lemmaR1i d _ _ _ ξ (nxC p Y) hR1).2.2.2.2.1 h0.1 h0.2
  have hrb : 0 < p.sb / 2 := by linarith
  refine ⟨fun h0 h1 => apSpec1 p Ps st _ hd _ (fun σ hI => ?_),
    fun h0 h1 pt h2 => apSpec2 p n Ps _ pt _ hd _ (fun σ hI => ?_)⟩
  · obtain ⟨hI1, -, h26, h80, h86, h91⟩ := hI
    rw [h26, hI1.2.1, h80, h86, h91, he1]
    have hr1 : p.sb / 2 ≤ st.r := by
      rcases hr with e | e <;> rw [e] <;> nlinarith
    have hr2 : st.r ≤ p.R := by
      rcases hr with e | e <;> rw [e] <;> nlinarith
    exact AP.kAP_le hrb hr1 hr2 le_rfl one_pos le_rfl (hPD h0).posSemidef.trace_nonneg (not_lt.1 h1.1)
      (not_lt.1 h1.2.2)
  · obtain ⟨hI2, -, h100, h91, h106⟩ := hI
    rw [h100, hI2.2.1, hI2.2.2.2.2.1, h91, h106]
    have hT0 := (hPD h0).posSemidef.trace_nonneg
    have hT := not_lt.1 h1.1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hm : ∀ x : ℝ, 0 < 16 * (n : ℝ) ^ 2 * max 1 x := fun x =>
      mul_pos (by positivity) (lt_of_lt_of_le one_pos (le_max_left _ _))
    refine AP.kAP_le hrb (by nlinarith) (by nlinarith) le_rfl (one_div_pos.2 (hm _)) ?_ hT0 hT (not_lt.1 h2)
    refine one_div_le_one_div_of_le (hm _) (mul_le_mul_of_nonneg_left (max_le_max le_rfl ?_) (by positivity))
    exact mul_le_mul_of_nonneg_left hT (by positivity)

/-- The cap of the first call of AP in DF2-O with `d`, `n`, `δ`. -/
noncomputable def df2Cap1 (d n : ℕ) (δ : ℝ) : ℕ := apCap1 d (df2oPar d n δ)

/-- The cap of the second call of AP in DF2-O with `d`, `n`, `δ`. -/
noncomputable def df2Cap2 (d n : ℕ) (δ : ℝ) : ℕ := apCap2 d n (df2oPar d n δ)

/-- In every round of DF2-O in run mode, the two calls of AP run within `df2Cap1` and `df2Cap2` steps. -/
theorem df2oMode_apRules (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (r0 R0 δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (w : World d) (t : ℕ) (st : Df2St d) (h : df2oMode d n r0 R0 δ w t = .run st) (Ps : PgSp d) (ξ : Fin d → ℝ)
    (Y : ℝ) : ApRules w (df2oPar d n δ) n Ps st ξ Y (df2Cap1 d n δ) (df2Cap2 d n δ) := by
  obtain ⟨heps, hr⟩ := df2oMode_run_r d n r0 R0 δ w t st h
  obtain ⟨hsb0, hsb1, -⟩ := df2oPar_sb_bounds d n hd hn δ hδ hδ1
  have heps0 : 0 ≤ (df2oPar d n δ).eps :=
    le_trans (by positivity) (df2oPar_eps_ge d n hd hn δ hδ)
  exact apRules_of _ n Ps st ξ Y hd hn (df2oMode_run_R1 d n hd hn r0 R0 δ hδ w t st h) hsb0 hsb1 heps0 heps
    (df2oPar_R_ge_one d n hd δ) hr (df2oPar_e1 d n hd hn δ hδ)

end AdversarialBco.Poly.Mach.VL
