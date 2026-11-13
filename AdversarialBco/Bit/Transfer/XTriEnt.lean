/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XExpr

@[expose] public section

/-!
# TRI-M, the clip of one entry of the box step

One entry of the step `x_{t+1} = clip(x_t - s Ṽ(x_t; y_t))` of TRI-OGD's core in integers at the grid `2^{-G}` is
clipped to `[lo, hi]`.

* `clipZ lo hi v = max lo (min hi v)`, `xclip`: the clip of a slot, by two tests.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `max lo (min hi v)`, the clip of `triClipQ` on one coordinate. -/
def clipZ (lo hi v : ℤ) : ℤ := max lo (min hi v)

/-- `v := max lo (min hi v)`: `if hi < v then v := hi`, then `if v < lo then v := lo` (`z` holds `0`). -/
def xclip (L : Layout) (v lo hi z : ℕ) : XCmd :=
  .seq (xifS L hi v (toX (VL.sop2 L .add v hi z)) .skip) (xifS L v lo (toX (VL.sop2 L .add v lo z)) .skip)

theorem XV.clip {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {v lo hi z : ℕ}
    (hv : v < L.NS) (hlo : lo < L.NS) (hhi : hi < L.NS) (hz : z < L.NS) (hvl : v ≠ lo) (hvz : v ≠ z)
    {x a b : ℤ} (ex : σ.sc v = x) (ea : σ.sc lo = a) (eb : σ.sc hi = b) (ez : σ.sc z = 0) (bx : |x| < 2 ^ ℓ)
    (ba : |a| < 2 ^ ℓ) (bb : |b| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xclip L v lo hi z) σ 4 (fun σ' => σ'.sc v = clipZ a b x ∧ |clipZ a b x| < 2 ^ ℓ ∧
      σ'.draws = σ.draws ∧ FrameP (fun y => y = v) (fun _ => False) σ σ') := by
  have hcopy : ∀ (σ1 : Env d) (w : ℕ) (c : ℤ), w < L.NS → σ1.sc w = c → σ1.sc z = 0 → |c| < 2 ^ ℓ →
      XRunsB L X ℓa ℓ (toX (VL.sop2 L .add v w z)) σ1 1 (· = σ1.setSc v (c : ℝ)) := fun σ1 w c hw ec e0 bc =>
    XV.mono (XV.addI hL hv hw hz (v := 0) ec (by rw [e0]; simp) bc (by simp) (by simpa using bc)) le_rfl
      fun σ' h => by rw [h]; simp
  have hm : |min b x| < 2 ^ ℓ := by
    rcases min_choice b x with h | h <;> rw [h] <;> assumption
  -- the first test
  have step1 : XRunsB L X ℓa ℓ (xifS L hi v (toX (VL.sop2 L .add v hi z)) .skip) σ 2 (fun σ1 =>
      σ1.sc v = min b x ∧ σ1.draws = σ.draws ∧ FrameP (fun y => y = v) (fun _ => False) σ σ1) := by
    by_cases hc : b < x
    · refine XV.mono (XV.ifS_t hL hhi hv (by rw [eb]; exact XV.abs_int_lt bb) (by rw [ex]; exact XV.abs_int_lt bx)
        (by rw [eb, ex]; exact_mod_cast hc) (hcopy σ hi b hhi eb ez bb)) (by omega) fun σ1 e => ?_
      subst e
      exact ⟨by simp [min_eq_left hc.le], rfl, (FrameP.refl (fun y => y = v) (fun _ => False) σ).setSc rfl _⟩
    · refine XV.mono (XV.ifS_f hL hhi hv (by rw [eb]; exact XV.abs_int_lt bb) (by rw [ex]; exact XV.abs_int_lt bx)
        (by rw [eb, ex]; exact_mod_cast hc) (XV.skip σ)) le_rfl fun σ1 e => ?_
      subst e
      exact ⟨by rw [ex, min_eq_right (not_lt.1 hc)], rfl, FrameP.refl _ _ σ1⟩
  refine XV.mono (K := 2 + 2) (XV.seq step1 fun σ1 ⟨e1, d1, F1⟩ => ?_) le_rfl fun _ h => h
  have ea1 : σ1.sc lo = a := by rw [F1.2.1 lo hvl.symm, ea]
  have ez1 : σ1.sc z = 0 := by rw [F1.2.1 z hvz.symm, ez]
  by_cases hc : min b x < a
  · refine XV.mono (XV.ifS_t hL hv hlo (by rw [e1]; exact_mod_cast hm) (by rw [ea1]; exact XV.abs_int_lt ba)
      (by rw [e1, ea1]; exact_mod_cast hc) (hcopy σ1 lo a hlo ea1 ez1 ba)) (by omega) fun σ2 e => ?_
    subst e
    refine ⟨by simp [clipZ, max_eq_left hc.le], by rw [clipZ, max_eq_left hc.le]; exact ba, d1, F1.setSc rfl _⟩
  · refine XV.mono (XV.ifS_f hL hv hlo (by rw [e1]; exact_mod_cast hm) (by rw [ea1]; exact XV.abs_int_lt ba)
      (by rw [e1, ea1]; exact_mod_cast hc) (XV.skip σ1)) le_rfl fun σ2 e => ?_
    subst e
    refine ⟨by rw [e1, clipZ, max_eq_right (not_lt.1 hc)], by rw [clipZ, max_eq_right (not_lt.1 hc)]; exact hm, d1,
      F1⟩

end AdversarialBco.Bit.Transfer
