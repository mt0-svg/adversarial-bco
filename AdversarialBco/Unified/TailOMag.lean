/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOHead
public import AdversarialBco.Unified.ProgOSplit
public import AdversarialBco.Bit.Transfer.XBLRoundP

@[expose] public section

/-!
# The round of BL-O that reaches the tail

`run_factsO`: a round of BL-O in mode `run` that ends in a state after the epoch's first round passed R10's test on
`B'` and R13's test on `w_μ`.
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

end AdversarialBco.Unified.ProgO
