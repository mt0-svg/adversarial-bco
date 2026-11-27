/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOHead
public import AdversarialBco.Unified.ProgOMag
public import AdversarialBco.Bit.Transfer.XBLRoundP

@[expose] public section

/-!
# The bounds of BL-O's new state for the tail

`run_factsO`: a round of BL-O in mode `run` that ends in a state after the epoch's first round passed R10's test on
`B'` and R13's test on `w_μ`. `tl_newO`: the hypothesis `hnew` of `XVO.runTO`, from the
magnitudes of BL-O's state at the next round (the body of `MagBLO`) and the exponent of R14's point (the body of
`ExpBLO` with the linear term `(B'B'ᵀ) w_μ` below `2^{5a+5}`, `a = 2K + 10`, `K = Ku d n k_δ`), when the invariant's
exponent `E` is above both.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- **R10's and R13's tests** on a round of BL-O in mode `run` that ends in a state after the epoch's first round. -/
theorem run_factsO {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {n : ℕ} {st st' : St d} {ξ : Fin d → ℚ} {ζ : ℚ}
    {obs : ℤ} (h : BLO.stepO orc c n (.run st) ξ ζ obs = .run st') (hf : st'.first = false) :
    frob2 (rB' (cfgH orc c st ξ) st ξ ζ obs) ≤ 2 * (c.par.Lam : ℚ) ∧
      ¬ (2 * c.par.W) ^ 2 < rwmu (cfgH orc c st ξ) st ξ ζ obs ⬝ᵥ rwmu (cfgH orc c st ξ) st ξ ζ obs := by
  rw [stepO_run] at h
  by_cases h7 : ra (cfgH orc c st ξ) st ξ ζ obs < 1 / 2 ∨ rq (cfgH orc c st ξ) st ξ ζ obs < 1 / 2
  · rw [if_pos h7] at h; cases h
  rw [if_neg h7] at h
  unfold tailModeO at h
  by_cases h10 : 2 * (c.par.Lam : ℚ) < frob2 (rB' (cfgH orc c st ξ) st ξ ζ obs) ∨
      2 * (c.par.Lam : ℚ) < frob2 (rA' (cfgH orc c st ξ) st ξ ζ obs)
  · rw [if_pos h10] at h; cases h
  rw [if_neg h10] at h
  refine ⟨le_of_not_gt fun h' => h10 (Or.inl h'), fun h13 => ?_⟩
  unfold m11O at h
  split at h
  · cases h
  · unfold m12O at h
    split_ifs at h with h12
    · cases h; simp [init] at hf
    · unfold m13O at h
      rw [if_pos h13] at h
      cases h

/-- The second coordinate of BL-O's draw at round `t` (the dither). -/
def zetaO (R : RdO d) : ℚ := (drawO d R.n R.δ R.r0 R.R0 R.w.cs R.t).2

set_option maxHeartbeats 4000000 in
/-- **The bounds of the new state and of R14's point** for `XVO.runTO`. -/
theorem tl_newO {Cm km Cx kx : ℕ}
    (hM : ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 → ∀ w : WorldO d,
      PosBnd (cfgV (cfgW d n δ r0 R0 a w)) E0 → ∀ (t : ℕ) (st : St d), t ≤ n →
        modeO d n δ r0 R0 a w t = .run st →
          StBnd (parO d n δ).p (Cm * (wU d n δ r0 R0 a + E0 + 1) ^ km) (parO d n δ).Rint st)
    (hX : ∀ (d n E0 : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ)
      (g : Fin d → ℚ) (ℓq : ℚ) (Bp : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (r e : ℚ),
      InU d n δ r0 R0 → c.par = parO d n δ → (∀ i j, OnG (parO d n δ).p (Bp i j)) →
      frob2 Bp ≤ 2 * (parO d n δ).Lam → (∀ j, |f j| ≤ 2 ^ E0) → (r, e) ∈ callRE (parO d n δ) d n →
        ellExpO (clearO (callO c H g ℓq r (Bp * Bpᵀ) f e)) ≤ Cx * (wU d n δ r0 R0 a + E0 + 1) ^ kx)
    {R : RdO d} {st : St d} (hIn : InU d R.n R.δ R.r0 R.R0) (hpos : PosBnd (cfgV R.c) R.E0) (ht : R.t < R.n)
    (hmo : R.mo = .run st) (hE1 : Cm * (R.W + R.E0 + 1) ^ km ≤ R.E)
    (hE2 : Cx * (R.W + (5 * (2 * MagO.Ku d R.n (kDel R.δ) + 10) + 5) + 1) ^ kx + MagO.Ku d R.n (kDel R.δ) ≤ R.E) :
    ∀ mu' : Fin d → ℚ, BLO.stepO R.w.orc R.c R.n (.run st) R.ξ (zetaO R) R.obs =
        .run ⟨false, mu', rA' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs, rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs, rG' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rl' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs⟩ →
      StBnd R.c.par.p R.E R.c.par.Rint ⟨false, mu', rA' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs, rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs, rG' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs,
          rl' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs⟩ ∧
      ∀ x, apI R.w.orc R.c (callLO R.c R.n (rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs)
          (rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs) (rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs)
          (rwmu (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs)) = some x →
        (∀ j, |x j| ≤ 2 ^ R.E) ∧ ellExpO (clearO (callLO R.c R.n
          (rB' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs) (rb' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs)
          (rk' (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs)
          (rwmu (cfgH R.w.orc R.c st R.ξ) st R.ξ (zetaO R) R.obs))) ≤ R.E := by
  intro mu' hs
  have hd := hIn.hd
  have hn := hIn.hn
  have e : modeO d R.n R.δ R.r0 R.R0 R.a R.w (R.t + 1) =
      BLO.stepO R.w.orc R.c R.n (.run st) R.ξ (zetaO R) R.obs := by
    rw [modeO_succ, show modeO d R.n R.δ R.r0 R.R0 R.a R.w R.t = .run st from hmo]
    rfl
  refine ⟨StBnd_mono (hM d R.n R.E0 R.δ R.r0 R.R0 R.a hIn R.w hpos (R.t + 1) _ ht (e.trans hs)) hE1, ?_⟩
  intro x hx
  set H := cfgH R.w.orc R.c st R.ξ with hH
  obtain ⟨hF, hWm⟩ := run_factsO hs rfl
  obtain ⟨-, hdT, -, -, -, -, -, -, -, hLam, -, -, hRint, -⟩ := MagO.fld_unit d R.n (kDel R.δ) hd hn
  obtain ⟨hW0, hW1⟩ := W_bndK d R.n (kDel R.δ) hd hn
  set K := MagO.Ku d R.n (kDel R.δ) with hK
  have pK : (2 : ℚ) ^ K ≤ 2 ^ (2 * K + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hf : ∀ j, |((rB' H st R.ξ (zetaO R) R.obs * (rB' H st R.ξ (zetaO R) R.obs)ᵀ) *ᵥ
      rwmu H st R.ξ (zetaO R) R.obs) j| ≤ 2 ^ (5 * (2 * K + 10) + 5) :=
    f_abs _ _ R.c.par.Lam R.c.par.W (2 * K + 10) hF (hLam.trans pK) (fun j => hb_wmu _ _ hWm j)
      ((le_of_eq (abs_of_nonneg hW0)).trans hW1) (hdT.trans pK)
  have hexp : ellExpO (clearO (callLO R.c R.n (rB' H st R.ξ (zetaO R) R.obs) (rb' H st R.ξ (zetaO R) R.obs)
      (rk' H st R.ξ (zetaO R) R.obs) (rwmu H st R.ξ (zetaO R) R.obs))) ≤
      Cx * (R.W + (5 * (2 * K + 10) + 5) + 1) ^ kx :=
    hX d R.n (5 * (2 * K + 10) + 5) R.δ R.r0 R.R0 R.a R.c _ _ _ (rB' H st R.ξ (zetaO R) R.obs) _ _ _ hIn rfl
      (fun i j => onG_rnd_s _ _) hF hf
      (by unfold callRE; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))
  have hle : ellExpO (clearO (callLO R.c R.n (rB' H st R.ξ (zetaO R) R.obs) (rb' H st R.ξ (zetaO R) R.obs)
      (rk' H st R.ξ (zetaO R) R.obs) (rwmu H st R.ξ (zetaO R) R.obs))) + K ≤ R.E := by omega
  refine ⟨fun j => (apI_abs hx (E := K) (by show ((R.c.par.Rint : ℕ) : ℚ) ≤ 2 ^ K; exact hRint) j).trans
    (pow_le_pow_right₀ (by norm_num) hle), by omega⟩

end AdversarialBco.Unified.ProgO
