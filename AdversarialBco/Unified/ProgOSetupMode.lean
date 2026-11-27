/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetup

@[expose] public section

/-!
# BL-O's setup: the mode

`xmodeO`: v2.1's `xmode` (Bit/Transfer/XBLSetupEpoch.lean) with the third mode: the mode slot is `0` (off) if
`2^pF < 2 ε'_num`, else `1` (guard) if the cross check's flag is set, else `2` (run). `modeSpecO`: `ModeSpecO` for it,
within `6` units, with room `172` slots.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni

variable {d : ℕ}

/-- P5 of BL-O: `sMode := 0` if `2^pF < 2 ε̂` (`ε' > 1/2`), else `1` if the flag `sBadS` is positive, else `2`. -/
def xmodeO (L : Layout) : XCmdO :=
  .base (.seq (toX (VL.sop2 L .add 124 sEps sEps))
    (xifS L s2pF 124 .skip (xifS L sZ sBadS (toX (VL.sconst L sMode 1)) (toX (VL.sconst L sMode 2)))))

set_option maxHeartbeats 1000000 in
/-- **The mode on the machine.** -/
theorem modeSpecO : ModeSpecO xmodeO 6 172 0 0 := by
  intro d L XO ℓa ℓ σ fl PF ep hL hR hz hfl hPF hep hm bfl bPF bep h2
  have hNS : 172 ≤ L.NS := hR.1
  refine XVO.ofX ?_
  have bep1 : |(ep : ℝ)| < 2 ^ ℓ := by
    have h1 : |ep| ≤ |2 * ep| := by rw [abs_mul]; norm_num; linarith [abs_nonneg ep]
    exact_mod_cast h1.trans_lt bep
  have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2l : |((2 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [abs_of_pos (by norm_num)]; norm_num
    exact lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ ℓ))
  refine XV.mono (K := 1 + 5) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.sop2 hL (x := 124) (a := sEps) (b := sEps) (by omega) (by bomega) (by bomega) .add
    (by intro h; cases h) (by rw [hep]; exact bep1) (by rw [hep]; exact bep1)
    (by simp only [RealRAM.Op2.eval, hep]; exact_mod_cast (show |ep + ep| < 2 ^ ℓ by rw [← two_mul]; exact bep)))
    fun σ1 e1 => ?_
  subst e1
  set σ1 := σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps)) with hσ1
  have z1 : σ1.sc sZ = 0 := by rw [hσ1, Env.setSc_sc, if_neg (by bomega), hz]
  have f1 : σ1.sc sBadS = fl := by rw [hσ1, Env.setSc_sc, if_neg (by decide), hfl]
  have p1 : σ1.sc s2pF = PF := by rw [hσ1, Env.setSc_sc, if_neg (by bomega), hPF]
  have e1 : σ1.sc 124 = ((2 * ep : ℤ) : ℝ) := by
    rw [hσ1, Env.setSc_sc, if_pos rfl]; simp only [RealRAM.Op2.eval, hep]; push_cast; ring
  have m1 : σ1.sc sMode = 0 := by rw [hσ1, Env.setSc_sc, if_neg (by bomega), hm]
  have F1 : FrameA (fun y => y = sMode ∨ y = 124) (fun _ => False) (fun _ _ => False) σ σ1 :=
    (FrameA.refl _ _ _ σ).setSc (Or.inr rfl) _
  have h0l : |σ1.sc sZ| < 2 ^ ℓ := by rw [z1]; simp
  have hfll : |σ1.sc sBadS| < 2 ^ ℓ := by rw [f1]; exact_mod_cast bfl
  have hpl : |σ1.sc s2pF| < 2 ^ ℓ := by rw [p1]; exact_mod_cast bPF
  have hel : |σ1.sc 124| < 2 ^ ℓ := by rw [e1]; exact_mod_cast bep
  by_cases hp : PF < 2 * ep
  · refine XV.mono (XV.ifS_t hL (by bomega) (by omega) hpl hel (by rw [p1, e1]; exact_mod_cast hp)
      (XV.skip _)) (by omega) fun σ' e => ?_
    subst e
    exact ⟨by rw [m1, if_pos hp]; simp, rfl, F1⟩
  · refine XV.mono (XV.ifS_f (K := 3) hL (by bomega) (by omega) hpl hel (by rw [p1, e1]; exact_mod_cast hp) ?_)
      le_rfl fun _ h => h
    by_cases hf : 0 < fl
    · refine XV.mono (XV.ifS_t hL (by bomega) (by simp only [sBadS]; omega) h0l hfll
        (by rw [z1, f1]; exact_mod_cast hf) (XV.sconst hL (x := sMode) (by bomega) 1 rfl h1l)) (by omega)
        fun σ' e => ?_
      subst e
      exact ⟨by rw [Env.setSc_sc, if_pos rfl, if_neg hp, if_pos hf]; simp, rfl, F1.setSc (Or.inl rfl) _⟩
    · refine XV.mono (XV.ifS_f hL (by bomega) (by simp only [sBadS]; omega) h0l hfll
        (by rw [z1, f1]; exact_mod_cast hf) (XV.sconst hL (x := sMode) (by bomega) 2 rfl h2l)) le_rfl
        fun σ' e => ?_
      subst e
      exact ⟨by rw [Env.setSc_sc, if_pos rfl, if_neg hp, if_neg hf]; simp, rfl, F1.setSc (Or.inl rfl) _⟩

end AdversarialBco.Unified.ProgO
