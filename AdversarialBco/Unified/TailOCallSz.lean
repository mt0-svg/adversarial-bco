/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOCallP
public import AdversarialBco.Unified.TailOSpec
public import AdversarialBco.Bit.Transfer.XCallSz
public import AdversarialBco.Bit.Transfer.XBLPrepP

@[expose] public section

/-!
# The data of BL-O's ELL-O calls

The facts that link the cells written by `xprep; xpreC` to ELL-O's call `clearO (callO c H g ℓ r P f e)` and its test
`tstO`: the reduced form of `r/2` (`half_num`, `half_den`), the scale `PF'/D'' = (1 - ε')⁻¹` (`scale_eq`), the test of
the block at the position's cells is BL-O's test (`pmapC_T`), the fields of `clearO` are those of v2.1's `clearQ` on
the rowless call (`clearO_fields`), and the bit length of the call is at most `2 (d + 1)² (s + 1) + 2`
(`ellOSz_callO`), the data given as pairs below `2^s` (`PrepIn`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Bit.Transfer.CallSz
open AdversarialBco.Bit.RQ (clr quadDen objDen linDen clearQ)
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ callOf)
open Matrix

variable {d : ℕ}

/-! ## `r/2` reduced -/

theorem half_numden (r : ℚ) :
    (r / 2).num = r.num / (Int.gcd r.num ((r.den : ℤ) + r.den) : ℤ) ∧
      (((r / 2).den : ℕ) : ℤ) = ((r.den : ℤ) + r.den) / (Int.gcd r.num ((r.den : ℤ) + r.den) : ℤ) := by
  have hv : (0 : ℤ) < (r.den : ℤ) + r.den := by have := r.den_pos; omega
  have he : ((r.num : ℤ) : ℚ) / (((r.den : ℤ) + r.den : ℤ) : ℚ) = r / 2 := by
    have hd : (r.den : ℚ) ≠ 0 := by have := r.den_pos; positivity
    push_cast
    rw [show (r.den : ℚ) + r.den = r.den * 2 by ring, ← div_div, Rat.num_div_den]
  have h := AdversarialBco.Bit.Transfer.RowP.e_numden 1 one_pos (r / 2) r.num ((r.den : ℤ) + r.den) hv he
  simpa using h

/-! ## The scale of the test -/

theorem scale_eq {pF : ℕ} {eps : ℚ} (hOn : OnG pF eps) :
    ((pfp ((2 : ℤ) ^ pF - BLM.qn pF eps) (2 ^ pF) : ℤ) : ℚ) / (dpp ((2 : ℤ) ^ pF - BLM.qn pF eps) : ℤ) =
      (1 - eps)⁻¹ := by
  rw [pfp_div_dpp]
  unfold OnG at hOn
  have hp : (2 : ℚ) ^ pF ≠ 0 := by positivity
  push_cast
  rw [hOn, show (1 - eps)⁻¹ = (2 : ℚ) ^ pF / ((1 - eps) * 2 ^ pF) by
    rw [div_mul_eq_div_div_swap, div_self hp, one_div]]
  congr 1; ring

/-! ## The test -/

/-- The CM test at the scaled position map of the cells is BL-O's test `c.T orc k (1 - ε')⁻¹`. -/
theorem pmapC_T (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) {DS Dp PF : ℤ} {muS : Fin d → ℤ}
    {aS : Matrix (Fin d) (Fin d) ℤ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} (hDS : 0 < DS)
    (hmu : ∀ j, (muS j : ℚ) / DS = c.μS j) (haS : ∀ i j, (aS i j : ℚ) / DS = c.AS i j)
    (ha : ptDN Da Na = c.a) (hr : (rn : ℚ) / rd = c.r0) (hs : (PF : ℚ) / Dp = (1 - c.par.eps)⁻¹) (k : ℕ)
    (y : Fin d → ℚ) :
    cmQ orc (ptDN Da Na) ((rn : ℚ) / rd) k (pmapC DS Dp PF muS aS y) = c.T orc k (1 - c.par.eps)⁻¹ y := by
  have hDS' : (DS : ℚ) ≠ 0 := by exact_mod_cast hDS.ne'
  have e : pmapC DS Dp PF muS aS y = c.μS + c.AS *ᵥ ((1 - c.par.eps)⁻¹ • y) := by
    funext i
    simp only [pmapC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, ← hmu, ← haS, ← hs]
    rw [add_div, Finset.mul_sum, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, ha, hr]
  rfl

/-! ## The fields of the call -/

/-- The fields of `clearO` on BL-O's call are those of v2.1's `clearQ` on the rowless call of `cfgV c`. -/
theorem clearO_fields (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) :
    (clearO (callO c H g ℓq r P f e)).H = (clearQ (callOf (cfgV c) H g ℓq r P f e)).H ∧
    (clearO (callO c H g ℓq r P f e)).g = (clearQ (callOf (cfgV c) H g ℓq r P f e)).g ∧
    (clearO (callO c H g ℓq r P f e)).ℓ = (clearQ (callOf (cfgV c) H g ℓq r P f e)).ℓ ∧
    (clearO (callO c H g ℓq r P f e)).P = (clearQ (callOf (cfgV c) H g ℓq r P f e)).P ∧
    (clearO (callO c H g ℓq r P f e)).f = (clearQ (callOf (cfgV c) H g ℓq r P f e)).f ∧
    (clearO (callO c H g ℓq r P f e)).Df = (clearQ (callOf (cfgV c) H g ℓq r P f e)).Df ∧
    (clearO (callO c H g ℓq r P f e)).R = (clearQ (callOf (cfgV c) H g ℓq r P f e)).R ∧
    (clearO (callO c H g ℓq r P f e)).r = (clearQ (callOf (cfgV c) H g ℓq r P f e)).r / 2 ∧
    (clearO (callO c H g ℓq r P f e)).e = (clearQ (callOf (cfgV c) H g ℓq r P f e)).e ∧
    (clearO (callO c H g ℓq r P f e)).Dc = 1 ∧ (clearO (callO c H g ℓq r P f e)).Nc = 0 ∧
    (clearO (callO c H g ℓq r P f e)).erK = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The bit length of the call -/

theorem ellOMx_le_of {I : EllOI d} {M : ℕ} (hH : ∀ i j, (I.H i j).natAbs ≤ M) (hP : ∀ i j, (I.P i j).natAbs ≤ M)
    (hg : ∀ j, (I.g j).natAbs ≤ M) (hf : ∀ j, (I.f j).natAbs ≤ M) (hNc : ∀ j, (I.Nc j).natAbs ≤ M)
    (hl : I.ℓ.natAbs ≤ M) (hDf : I.Df ≤ M) (hDc : I.Dc.natAbs ≤ M) (hR : I.R.num.natAbs ≤ M ∧ I.R.den ≤ M)
    (hr : I.r.num.natAbs ≤ M ∧ I.r.den ≤ M) (he : I.e.num.natAbs ≤ M ∧ I.e.den ≤ M) : ellOMx I ≤ M := by
  unfold ellOMx
  simp only [max_le_iff, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
  exact ⟨fun i j => ⟨hH i j, hP i j⟩, fun j => ⟨⟨hg j, hf j⟩, hNc j⟩, hl, hDf, hDc, hR, hr, he⟩

set_option maxHeartbeats 2000000 in
/-- **The bit length of BL-O's call** from its data as pairs below `2^s`. -/
theorem ellOSz_callO {L : Layout} {s : ℕ} {c : CfgO d} {H : Matrix (Fin d) (Fin d) ℚ} {g : Fin d → ℚ} {ℓq r : ℚ}
    {P : Matrix (Fin d) (Fin d) ℚ} {f : Fin d → ℚ} {e : ℚ} {σ : Env d}
    (hI : PrepIn σ (cfgV c) s H g ℓq r P f e) :
    ellOSz (clearO (callO c H g ℓq r P f e)) ≤ 2 * (d + 1) ^ 2 * (s + 1) + 2 := by
  obtain ⟨-, -, -, -, -, hRs, pH0, pg0, pP0, pf0, pl0, pr0, pe0⟩ := hI
  have pH : ∀ i j, (H i j).den ≤ 2 ^ s ∧ (H i j).num.natAbs ≤ 2 ^ s ∧ |H i j| ≤ 2 ^ s := fun i j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pH0 i j
    exact pair_bound u v _ hv hu hvs huv
  have pP : ∀ i j, (P i j).den ≤ 2 ^ s ∧ (P i j).num.natAbs ≤ 2 ^ s ∧ |P i j| ≤ 2 ^ s := fun i j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pP0 i j
    exact pair_bound u v _ hv hu hvs huv
  have pg : ∀ j, (g j).den ≤ 2 ^ s ∧ (g j).num.natAbs ≤ 2 ^ s ∧ |g j| ≤ 2 ^ s := fun j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pg0 j
    exact pair_bound u v _ hv hu hvs huv
  have pf : ∀ j, (f j).den ≤ 2 ^ s ∧ (f j).num.natAbs ≤ 2 ^ s ∧ |f j| ≤ 2 ^ s := fun j => by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pf0 j
    exact pair_bound u v _ hv hu hvs huv
  have pl : ℓq.den ≤ 2 ^ s ∧ ℓq.num.natAbs ≤ 2 ^ s ∧ |ℓq| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pl0
    exact pair_bound u v _ hv hu hvs huv
  have pr : r.den ≤ 2 ^ s ∧ r.num.natAbs ≤ 2 ^ s ∧ |r| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pr0
    exact pair_bound u v _ hv hu hvs huv
  have pe : e.den ≤ 2 ^ s ∧ e.num.natAbs ≤ 2 ^ s ∧ |e| ≤ 2 ^ s := by
    obtain ⟨u, v, hv, hu, hvs, -, -, huv⟩ := pe0
    exact pair_bound u v _ hv hu hvs huv
  have hgd : ∏ j, (g j).den ≤ 2 ^ (s * d) := by
    simpa [Fintype.card_fin] using prod_den_le_pow g (fun j => (pg j).1)
  have hfd : ∏ j, (f j).den ≤ 2 ^ (s * d) := by
    simpa [Fintype.card_fin] using prod_den_le_pow f (fun j => (pf j).1)
  have hPd : ∏ i, ∏ j, (P i j).den ≤ 2 ^ (s * (d * d)) := prod_den_mat P fun i j => (pP i j).1
  have hQ : (∏ i, ∏ j, (H i j).den) * (∏ j, (g j).den) * ℓq.den ≤ 2 ^ (s * (d * d + d + 1)) := by
    calc _ ≤ 2 ^ (s * (d * d)) * 2 ^ (s * d) * 2 ^ s :=
          Nat.mul_le_mul (Nat.mul_le_mul (prod_den_mat H fun i j => (pH i j).1) hgd) pl.1
      _ = _ := by rw [← pow_add, ← pow_add]; ring_nf
  set T := 2 * (d + 1) ^ 2 * (s + 1) with hT
  have pw : ∀ {a : ℕ}, a ≤ T → 2 ^ a ≤ 2 ^ T := fun h => Nat.pow_le_pow_right (by norm_num) h
  have hdd : s * (d * d + d + 1) + s ≤ T := by rw [hT]; nlinarith
  have hdP : s * (d * d) + s ≤ T := by rw [hT]; nlinarith
  have hdf : s * d + s + s * (d * d) ≤ T := by rw [hT]; nlinarith
  have hMx : ellOMx (clearO (callO c H g ℓq r P f e)) ≤ 2 ^ T := by
    refine ellOMx_le_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- `H`
      intro i j
      refine (clr_bound (H i j) ?_ hQ (pH i j).2.2).trans (pw (by omega))
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((Finset.dvd_prod_of_mem (fun j => (H i j).den)
        (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem (fun i => ∏ j, (H i j).den) (Finset.mem_univ i))) _) _
    · -- `P`
      intro i j
      refine (clr_bound (P i j) ?_ hPd (pP i j).2.2).trans (pw (by omega))
      exact (Finset.dvd_prod_of_mem (fun j => (P i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (P i j).den) (Finset.mem_univ i))
    · -- `g`
      intro j
      refine (clr_bound (g j) ?_ hQ (pg j).2.2).trans (pw (by omega))
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun j => (g j).den) (Finset.mem_univ j)) _) _
    · -- `f`
      intro j
      have h1 := clr_bound (f j) (Finset.dvd_prod_of_mem (fun j => (f j).den) (Finset.mem_univ j)) hfd (pf j).2.2
      show (clr (linDen (callO c H g ℓq r P f e)) (f j) * (objDen (callO c H g ℓq r P f e) : ℤ)).natAbs ≤ _
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      refine (Nat.mul_le_mul h1 hPd).trans ?_
      rw [← pow_add]; exact pw (by omega)
    · intro j; simp [clearO]
    · -- `ℓ`
      exact (clr_bound ℓq (dvd_mul_left _ _) hQ pl.2.2).trans (pw (by omega))
    · -- `D_f`
      exact hfd.trans (pw (by omega))
    · simp only [clearO]; exact Nat.one_le_two_pow
    · -- `R`
      show (((c.par.Rint : ℕ) : ℚ)).num.natAbs ≤ _ ∧ (((c.par.Rint : ℕ) : ℚ)).den ≤ _
      rw [Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
      have : c.par.Rint ≤ 2 ^ s := by exact_mod_cast hRs
      exact ⟨this.trans (pw (by omega)), Nat.one_le_two_pow⟩
    · -- `r/2`
      show (r / 2).num.natAbs ≤ _ ∧ (r / 2).den ≤ _
      have h2 : (r / 2).num.natAbs ≤ r.num.natAbs ∧ (r / 2).den ≤ 2 * r.den := by
        obtain ⟨hn, hd⟩ := half_numden r
        have hg : (0 : ℤ) < (Int.gcd r.num ((r.den : ℤ) + r.den) : ℤ) := by
          have : 0 < Int.gcd r.num ((r.den : ℤ) + r.den) :=
            Int.gcd_pos_of_ne_zero_right _ (by have := r.den_pos; omega)
          exact_mod_cast this
        constructor
        · rw [hn]; exact Int.natAbs_ediv_le_natAbs _ _
        · have : (((r / 2).den : ℕ) : ℤ) ≤ (r.den : ℤ) + r.den := by
            rw [hd]; exact Int.ediv_le_self _ (by have := r.den_pos; omega)
          omega
      refine ⟨h2.1.trans (pr.2.1.trans (pw (by omega))), h2.2.trans ?_⟩
      calc 2 * r.den ≤ 2 * 2 ^ s := Nat.mul_le_mul_left _ pr.1
        _ = 2 ^ (s + 1) := by ring
        _ ≤ 2 ^ T := pw (by rw [hT]; nlinarith)
    · -- `e`
      obtain ⟨h1, h2⟩ := natmul_bound _ e hPd pe.1 pe.2.1
      exact ⟨h1.trans (pw (by omega)), h2.trans (pw (by omega))⟩
  unfold ellOSz
  have hsz : (ellOMx (clearO (callO c H g ℓq r P f e))).size ≤ T + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt hMx (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have : (clearO (callO c H g ℓq r P f e)).erK = 1 := rfl
  omega

end AdversarialBco.Unified.ProgO
