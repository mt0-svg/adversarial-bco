/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.MagField
public import AdversarialBco.Unified.EllOProof
public import AdversarialBco.Unified.SepGauge
public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# The magnitudes of BL-O's run, part B: one round

The bounds of Bit/Transfer/XBLMagC.lean for BL-O's round `stepO`. The lines R5 to R15 are BL's, so the bounds of the
increments and of the commit (`commit_bnd`, `init_bnd`) apply to the rowless configuration `cfgV c`; what changes:

* the play `pt' = max(1, π̃(X')/(1 - ε'))` with the gauge `π̃(X') ∈ [0, 2|X'|₁]` (`gaugeP_bnd`, the bisection's
  counter is at most `2^{jG}`), so `pt' ≤ T^9` for `|X'| ≤ T^6`;
* the reading is clipped, `|o| ≤ 2^{q_O} ≤ 2^p T` (`clip_abs`, the field `clip` of `CfgBO`), on every world;
* the answers of ELL-O are in the box of radius `R_int`: a returned point lies in the exact part of the region
  (`ellOCert`), so its norm is at most the radius `R_int` of the call (`apO_abs`).
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Uni
open AdversarialBco.Bit.BLP (Par St Mode init rnd CallQ)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (cfgV)
open Matrix

variable {d : ℕ}

/-- BL-O's configuration at the unit `T`: BL's `CfgB` of the rowless configuration, and the range of the clipped
reading. -/
structure CfgBO (T : ℚ) (c : CfgO d) : Prop where
  cb : CfgB T (cfgV c)
  clip : (2 : ℚ) ^ c.qO ≤ 2 ^ c.par.p * T

/-! ## The gauge play and the reading -/

theorem gaugeQ_bnd (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) {H : ℚ} (hH : 0 ≤ H) (j : ℕ) :
    0 ≤ gaugeQ T a0 x H j ∧ gaugeQ T a0 x H j ≤ H := by
  have h := (gaugeIt_le T a0 x H j j le_rfl).2
  have h' : ((gaugeIt T a0 x H j j).2 : ℚ) ≤ 2 ^ j := by exact_mod_cast h
  unfold gaugeQ
  have hj : (0 : ℚ) < 2 ^ j := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hj]
  exact mul_le_mul_of_nonneg_left h' hH

theorem l1_nonneg (x : Fin d → ℚ) : 0 ≤ l1 x := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The gauge of the play is in `[0, 2|X'|₁]`.** -/
theorem gaugeP_bnd (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (X : Fin d → ℚ) :
    0 ≤ gaugeP orc c X ∧ gaugeP orc c X ≤ 2 * l1 X := by
  unfold gaugeP
  split_ifs
  · exact ⟨le_rfl, by have := l1_nonneg X; linarith⟩
  · exact gaugeQ_bnd _ _ _ (by have := l1_nonneg X; linarith) _

theorem clip_abs (q : ℕ) (z : ℤ) : |BitRAMO.clip q z| ≤ 2 ^ q := by
  unfold BitRAMO.clip
  have h0 : (0 : ℤ) ≤ 2 ^ q := by positivity
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- **`|Y'| ≤ T^14`** for BL-O's reading. -/
theorem Y_bndO (orc : (Fin d → ℚ) → ℕ → Bool) {c : CfgO d} {T : ℚ} (hc : CfgBO T c) {st : St d} {t : ℕ}
    (hs : StI T c.par.Rint t st) (ξ : Fin d → ℚ) (ζ : ℚ) (o : ℤ) (hξ : ∀ i, |ξ i| ≤ T) (hζ : |ζ| ≤ T)
    (ho : |(o : ℚ)| ≤ 2 ^ c.qO) :
    |rnd c.par.p (ptO orc c (XO c st ξ) * ((o : ℚ) / 2 ^ c.par.p + ζ) / 2 +
      2 * (ptO orc c (XO c st ξ) - 1) / c.par.eps)| ≤ T ^ 14 := by
  have hcb := hc.cb
  have hT2 : (2 : ℚ) ≤ T := by linarith [hcb.T4]
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hw : ∀ i, |(st.A *ᵥ ξ) i| ≤ T ^ 3 := bnd_mulVec (a := 1) (b := 1) hT1 hcb.d
    (fun i j => pw1 (hs.A i j)) (fun j => pw1 (hξ j))
  have hlam : |1 - c.par.lam| ≤ T ^ 2 :=
    bnd_sub (a := 1) hT2 (pw1 (by rw [abs_one]; exact hT1)) (pw1 hcb.lam)
  have hX : ∀ i, |XO c st ξ i| ≤ T ^ 6 := fun i => by
    show |st.mu i + (1 - c.par.lam) * (st.A *ᵥ ξ) i| ≤ T ^ 6
    exact bnd_add (a := 5) hT2 (bnd_up hT1 (pw1 ((hs.mu i).trans hcb.R)) (by norm_num)) (bnd_mul hlam (hw i))
  have hl1 : l1 (XO c st ξ) ≤ T ^ 7 := by
    have h6 : (0 : ℚ) ≤ T ^ 6 := by positivity
    calc l1 (XO c st ξ) ≤ ∑ _i : Fin d, T ^ 6 := Finset.sum_le_sum fun i _ => hX i
      _ = d * T ^ 6 := by simp
      _ ≤ T * T ^ 6 := mul_le_mul_of_nonneg_right hcb.d h6
      _ = T ^ 7 := by ring
  obtain ⟨hg0, hg1⟩ := gaugeP_bnd orc c (XO c st ξ)
  have heps1 : c.par.eps ≤ 1 / 2 := hcb.eps1
  have hpt1 : 1 ≤ ptO orc c (XO c st ξ) := le_max_left _ _
  have hpt2 : ptO orc c (XO c st ξ) ≤ T ^ 10 := by
    unfold ptO
    have hT9 : (1 : ℚ) ≤ T ^ 10 := one_le_pow₀ hT1
    refine max_le hT9 ?_
    rw [div_le_iff₀ (by linarith)]
    have h7 : (0 : ℚ) ≤ T ^ 7 := by positivity
    have h10 : 4 * T ^ 7 ≤ T ^ 10 := by
      have : T ^ 10 = T ^ 3 * T ^ 7 := by ring
      rw [this]
      have : (4 : ℚ) ≤ T ^ 3 := by nlinarith [hcb.T4]
      nlinarith
    have hpos : (0 : ℚ) ≤ T ^ 10 := by positivity
    nlinarith [hcb.eps0]
  set pt := ptO orc c (XO c st ξ)
  have hpt : |pt| ≤ T ^ 10 := by rw [abs_of_nonneg (by linarith)]; exact hpt2
  have hpt' : |pt - 1| ≤ T ^ 10 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hp : (0 : ℚ) < 2 ^ c.par.p := by positivity
  have ho' : |(o : ℚ) / 2 ^ c.par.p| ≤ T ^ 1 := by
    rw [abs_div, abs_of_pos hp, pow_one, div_le_iff₀ hp]
    linarith [hc.clip]
  have h1 : |pt * ((o : ℚ) / 2 ^ c.par.p + ζ) / 2| ≤ T ^ 12 :=
    bnd_up hT1 (bnd_div2 (bnd_mul hpt (bnd_add hT2 ho' (pw1 hζ)))) (by norm_num)
  have h2 : |2 * (pt - 1) / c.par.eps| ≤ T ^ 12 := by
    rw [div_eq_mul_inv]
    exact bnd_mul (a := 11) (b := 1) (bnd_mul (a := 1) (pw1 (by rw [abs_two]; exact hT2)) hpt') (pw1 hcb.epsI)
  exact bnd_rnd hT2 _ (bnd_up hT1 (bnd_add hT2 h1 h2) (by norm_num))

/-! ## The answers of ELL-O -/

/-- **An answer of ELL-O/BIS-O is in the box of the call's radius**: it lies in the exact part of the region
(`ellOCert`), whose norm bound is the call's `R`. -/
theorem apO_abs (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (D : CallQ d) (y : Fin d → ℚ)
    (h : apO orc c D = some y) (j : Fin d) : |y j| ≤ D.R := by
  unfold apO at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, hreg⟩ := EllO.ellOCert d (clearO D) _ x hx
  have hn := hreg.2
  have hj := Poly.LeanAp.abs_apply_le_oNorm (fun j => (x j : ℝ) / 2 ^ ellExpO (clearO D)) j
  have hR : (((clearO D).R : ℚ) : ℝ) = (D.R : ℝ) := rfl
  have : |((x j : ℝ) / 2 ^ ellExpO (clearO D))| ≤ (D.R : ℝ) := by
    rw [← hR]; exact hj.trans hn
  exact_mod_cast this

end AdversarialBco.Unified.MagO
