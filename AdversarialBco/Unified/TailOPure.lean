/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit
public import AdversarialBco.Unified.MagStep
public import AdversarialBco.Bit.Transfer.XBLTailRe

@[expose] public section

/-!
# The tail of BL-O's round in BL-O's terms

`stepO` in mode `run` (BLOSpec.lean) is v2.1's head (R5 to R9, the values `rY`, ..., `rwmu` of
Bit/Transfer/XBLStep.lean) at a configuration `cfgPt c X g` of BL whose gauge at `X' = X` is BL-O's gauge `g`, then a
tail (`tailModeO`: R10's test, R11's call `callTO`, R12's test, R13's test, R14's call `callLO`, R15) on BL-O's calls
`apO` (`stepO_run`). `apO` splits into the integer answer of ELL-O and its exponent (`apO_none`, `apO_some`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2 XQ)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The head at a configuration with BL-O's gauge -/

/-- A configuration of BL with BL-O's parameters and position and one row `α = (g/|X|²) X`, `β = 1`: BL's gauge at
`X` is `max(0, g)`. -/
def cfgPt (c : CfgO d) (X : Fin d → ℚ) (g : ℚ) : Cfg d :=
  ⟨c.par, 1, fun _ => (g / (X ⬝ᵥ X)) • X, fun _ => 1, c.μS, c.AS, c.a⟩

theorem gaugeQ_cfgPt (c : CfgO d) (X : Fin d → ℚ) {g : ℚ} (hg : 0 ≤ g) (h0 : X = 0 → g = 0) :
    Bit.BLP.gaugeQ (cfgPt c X g) X = g := by
  unfold Bit.BLP.gaugeQ cfgPt
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, div_one, smul_dotProduct,
    smul_eq_mul]
  by_cases hX : X = 0
  · subst hX
    rw [h0 rfl]
    simp
  · have hXX : X ⬝ᵥ X ≠ 0 := fun h => hX (dotProduct_self_eq_zero.1 h)
    rw [div_mul_cancel₀ _ hXX, max_eq_right hg]

/-- BL-O's configuration of the head at the draw `ξ`. -/
def cfgH (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) : Cfg d :=
  cfgPt c (XO c st ξ) (gaugeP orc c (XO c st ξ))

/-- `pt'` of BL-O is BL's at `cfgH`. -/
theorem ptO_eq (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) :
    ptO orc c (XO c st ξ) = Bit.BLP.ptQ (cfgH orc c st ξ) (XQ (cfgH orc c st ξ) st ξ) := by
  have hX : XQ (cfgH orc c st ξ) st ξ = XO c st ξ := rfl
  rw [hX]
  unfold Bit.BLP.ptQ ptO
  rw [show (cfgH orc c st ξ).par = c.par from rfl, cfgH,
    gaugeQ_cfgPt _ _ (MagO.gaugeP_bnd orc c _).1 (fun h => by unfold gaugeP; rw [if_pos h])]

/-! ## The tail on BL-O's calls -/

/-- R11's call of BL-O. -/
def callTO (c : CfgO d) (st : St d) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) : CallQ d :=
  if st.first then
    callO c 0 0 0 (1 - c.par.eps) (Bp * Bpᵀ) (bp - (c.par.eta / 2) • Gp) ((1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8))
  else
    callO c (st.B * st.Bᵀ) st.b (LT c.par - st.k) (Bit.BLP.rB c.par / 2) (Bp * Bpᵀ) (bp - (c.par.eta / 2) • Gp)
      (Bit.BLP.rB c.par ^ 2 / (c.par.Ne * d * 8))

/-- R14's call of BL-O. -/
def callLO (c : CfgO d) (n : ℕ) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wmu : Fin d → ℚ) :
    CallQ d :=
  callO c (Bp * Bpᵀ) bp (Lmu c.par - kp) (Bit.BLP.rB c.par / 2) (Bp * Bpᵀ) ((Bp * Bpᵀ) *ᵥ wmu) (eBL c.par d n)

section Modes

variable (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ)

/-- R14 LINE and R15 COMMIT. -/
def m14O (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) : Mode d :=
  match apO orc c (callLO c n Bp bp kp wmu) with
  | none => .guard
  | some mu' => .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩

/-- R13's guard, then R14 and R15. -/
def m13O (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) : Mode d :=
  if (2 * c.par.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else m14O orc c n Ap Bp bp Gp kp lp wmu

/-- R12 FIRE at the test point `p'`, then R13 to R15. -/
def m12O (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu p' : Fin d → ℚ) : Mode d :=
  if c.par.eta * (lp - Gp ⬝ᵥ p') - 2 * (p' ⬝ᵥ ((Bp * Bpᵀ) *ᵥ p') / 2 - bp ⬝ᵥ p' + kp) ≤
      -c.par.rho + c.par.eHat then .run (init c.par d) else m13O orc c n Ap Bp bp Gp kp lp wmu

/-- R11 TEST, then R12 to R15. -/
def m11O (st : St d) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) :
    Mode d :=
  match apO orc c (callTO c st Bp bp Gp) with
  | none => .guard
  | some p' => m12O orc c n Ap Bp bp Gp kp lp wmu p'

/-- **R10 to R15** on BL-O's calls. -/
def tailModeO (st : St d) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) :
    Mode d :=
  if 2 * (c.par.Lam : ℚ) < frob2 Bp ∨ 2 * (c.par.Lam : ℚ) < frob2 Ap then .guard else
    m11O orc c n st Ap Bp bp Gp kp lp wmu

end Modes

set_option maxHeartbeats 1000000 in
/-- **`stepO` in mode `run`**: v2.1's head at `cfgH`, R7's tests, then the tail on BL-O's calls. -/
theorem stepO_run (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) :
    BLO.stepO orc c n (.run st) ξ ζ obs =
      if ra (cfgH orc c st ξ) st ξ ζ obs < 1 / 2 ∨ rq (cfgH orc c st ξ) st ξ ζ obs < 1 / 2 then .guard else
      tailModeO orc c n st (rA' (cfgH orc c st ξ) st ξ ζ obs) (rB' (cfgH orc c st ξ) st ξ ζ obs)
        (rb' (cfgH orc c st ξ) st ξ ζ obs) (rG' (cfgH orc c st ξ) st ξ ζ obs) (rk' (cfgH orc c st ξ) st ξ ζ obs)
        (rl' (cfgH orc c st ξ) st ξ ζ obs) (rwmu (cfgH orc c st ξ) st ξ ζ obs) := by
  have hpt := ptO_eq orc c st ξ
  unfold BLO.stepO
  dsimp only
  rw [hpt]
  rfl

/-! ## The calls -/

theorem callTO_eq (c : CfgO d) (st : St d) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) :
    callTO c st Bp bp Gp =
      callO c (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
        (if st.first then 0 else LT c.par - st.k) (if st.first then 1 - c.par.eps else Bit.BLP.rB c.par / 2)
        (Bp * Bpᵀ) (bp - (c.par.eta / 2) • Gp)
        (if st.first then (1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8)
          else Bit.BLP.rB c.par ^ 2 / (c.par.Ne * d * 8)) := by
  unfold callTO; cases st.first <;> rfl

/-- ELL-O's test of a call: the CM test at the scale `(1 - ε')⁻¹` and the precision `eK + kK`. -/
def tstO (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (D : CallQ d) : (Fin d → ℚ) → Bool :=
  c.T orc ((clearO D).eK + c.kK) (1 - c.par.eps)⁻¹

/-- ELL-O's integer answer on a call. -/
def apI (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (D : CallQ d) : Option (Fin d → ℤ) :=
  ellOI (clearO D) (tstO orc c D)

theorem apO_none {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {D : CallQ d} (h : apI orc c D = none) :
    apO orc c D = none := by
  unfold apO; unfold apI tstO at h; rw [h]; rfl

theorem apO_some {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {D : CallQ d} {x : Fin d → ℤ}
    (h : apI orc c D = some x) : apO orc c D = some fun i => (x i : ℚ) / 2 ^ ellExpO (clearO D) := by
  unfold apO; unfold apI tstO at h; rw [h]; rfl

/-- The integer answer of a call lies in the box of radius `R_int` at the scale `2^{ellExpO}`. -/
theorem apI_abs {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {D : CallQ d} {x : Fin d → ℤ}
    (h : apI orc c D = some x) {E : ℕ} (hR : D.R ≤ 2 ^ E) (j : Fin d) :
    |x j| ≤ 2 ^ (ellExpO (clearO D) + E) := by
  have hy := MagO.apO_abs orc c D _ (apO_some h) j
  have hp : (0 : ℚ) < 2 ^ ellExpO (clearO D) := by positivity
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp] at hy
  have h1 : ((|x j| : ℤ) : ℚ) ≤ 2 ^ E * 2 ^ ellExpO (clearO D) := by
    rw [Int.cast_abs]; exact hy.trans (mul_le_mul_of_nonneg_right hR hp.le)
  rw [pow_add, mul_comm]
  exact_mod_cast h1

end AdversarialBco.Unified.ProgO
