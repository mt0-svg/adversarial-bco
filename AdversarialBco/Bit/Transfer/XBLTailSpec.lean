/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTail
public import AdversarialBco.Bit.Transfer.XBLStep

@[expose] public section

/-!
# The tail of BL's round in mode `run`: R10 to R15 (frozen statement)

`step` in mode `run` (Bit/BLPure.lean) is R7's test, then a tail (`tailMode`, `step_run_tail`) that reads only the
state `st`, the round's values `A'`, `B'`, `b'`, `G'`, `k'`, `l'` and `w_μ`: R10's test, R11's call (`callTOf`), R12's
test, R13's test, R14's call (`callLOf`), R15's new state.

`TailBL`: one command `xtail L` runs this tail on the machine from the cells that R2 to R9 leave, at the round `t` of
`BLInv` (after R1 and the play, so `t` is the next round in the driver's count):

* `A'`, `B'` (matrices, the cells `d i + j`), `b'`, `G'` as numerators on the grid `2^{-p}` in the arrays `26`, `27`,
  `28`, `29`; `k'`, `l'` as numerators in the slots `59`, `63`;
* `ŝ5` in the slot `72` (`s5 = ŝ5 / 2^p`), `Â Γ` in the array `aWv = 25` (`Â` the numerators of `st.A`, `Γ` the
  draw's numerators over `G = 2^(2 p_B)`), so `w_μ = μ' - s5 A' (Γ / G)` (`wmuOf`);
* the constants `1, 2, 4` in the slots `41, 42, 43`.

Every one of them at most `2^E₁`, `E ≤ E₁` (`E` the bound of `BLInv`). When the tail ends in a new state (mode `run`
with `first = false`), the caller supplies its bounds at `E` (`StBnd`) and those of the routine's point of R14 (`x`
at most `2^E`, its exponent at most `E`), which `BLInv` at `E` and `CommitBL` need. Work term
`W = d + m + size M + size n + E₁ + 1`: within `C W^k` units, under `C W^k ≤ ℓ` and `C W^k < 2^ℓa`, with the
block's room `nS, nN, nA` in the layout. The tail ends in `BLInv` with the mode `tailMode`, at the same round, with
the same points. The theorem to prove: `tailBL_of : CallBL → DataT → DataL → CommitBL → FireBL → ExpBL → TailBL`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- R11's call from the state `st` and the round's `B'`, `b'`, `G'`. -/
def callTOf (cfg : Cfg d) (st : St d) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) : CallQ d :=
  if st.first then
    callOf cfg 0 0 0 (1 - cfg.par.eps) (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
      ((1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8))
  else
    callOf cfg (st.B * st.Bᵀ) st.b (LT cfg.par - st.k) (BLP.rB cfg.par / 2) (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
      (BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8))

/-- R14's call from the round's `B'`, `b'`, `k'`, `w_μ`. -/
def callLOf (cfg : Cfg d) (n : ℕ) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wmu : Fin d → ℚ) :
    CallQ d :=
  callOf cfg (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (BLP.rB cfg.par / 2) (Bp * Bpᵀ) ((Bp * Bpᵀ) *ᵥ wmu) (eBL cfg.par d n)

/-- **R10 to R15**: the mode after the round from the state `st` and the round's values. -/
def tailMode (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (st : St d)
    (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (wmu : Fin d → ℚ) : Mode d :=
  if 2 * (cfg.par.Lam : ℚ) < frob2 Bp ∨ 2 * (cfg.par.Lam : ℚ) < frob2 Ap then .guard else
  match ap (callTOf cfg st Bp bp Gp) with
  | none => .guard
  | some p' =>
    if cfg.par.eta * (lp - Gp ⬝ᵥ p') - 2 * (p' ⬝ᵥ ((Bp * Bpᵀ) *ᵥ p') / 2 - bp ⬝ᵥ p' + kp) ≤
        -cfg.par.rho + cfg.par.eHat then .run (init cfg.par d) else
    if (2 * cfg.par.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else
    match ap (callLOf cfg n Bp bp kp wmu) with
    | none => .guard
    | some mu' => .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩

/-- `step` in mode `run`: R7's test, then the tail. -/
theorem step_run_tail (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ)
    (ζ : ℚ) (obs : ℤ) :
    step ap cfg n (.run st) ξ ζ obs =
      if ra cfg st ξ ζ obs < 1 / 2 ∨ rq cfg st ξ ζ obs < 1 / 2 then .guard else
      tailMode ap cfg n st (rA' cfg st ξ ζ obs) (rB' cfg st ξ ζ obs) (rb' cfg st ξ ζ obs) (rG' cfg st ξ ζ obs)
        (rk' cfg st ξ ζ obs) (rl' cfg st ξ ζ obs) (rwmu cfg st ξ ζ obs) := rfl

/-- `w_μ = μ' - (ŝ5 / 2^p) A' (Γ / G)`, `G = 2^(2 p_B)`. -/
def wmuOf (P : Par) (st : St d) (s5 : ℤ) (Γ : Fin d → ℤ) : Fin d → ℚ :=
  st.mu - ((s5 : ℚ) / 2 ^ P.p) • (st.A *ᵥ fun k => (Γ k : ℚ) / 2 ^ (2 * gsm_prec P.B))

/-- **The tail of BL's round (frozen).** -/
def TailBL : Prop :=
  ∃ (xtail : Layout → XCmd) (C k nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M K0 E E1 ℓa ℓ t : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
      (b : Fin m → ℚ) (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d)
      (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (s5 : ℤ) (Γ : Fin d → ℤ)
      (P0 : ℕ → EuclideanSpace ℝ (Fin d)) (σ : Env d),
      1 ≤ d → 1 ≤ n → LayOK L d ℓa → BLLay L → blkBL.OK L nS nN nA → RealRAM.HeightLE A b M →
      OnG (par d n).pF (par d n).eps → 0 ≤ (par d n).eps → (par d n).eps ≤ 1 → E ≤ E1 →
      BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ → σ.pts = P0 →
      σ.sc 41 = 1 → σ.sc 42 = 2 → σ.sc 43 = 4 →
      (∀ i j : Fin d, σ.arr 26 (d * i + j) = qn (par d n).p (Ap i j) ∧ OnG (par d n).p (Ap i j) ∧
        |qn (par d n).p (Ap i j)| ≤ 2 ^ E1) →
      (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn (par d n).p (Bp i j) ∧ OnG (par d n).p (Bp i j) ∧
        |qn (par d n).p (Bp i j)| ≤ 2 ^ E1) →
      (∀ j : Fin d, σ.arr 28 j = qn (par d n).p (bp j) ∧ OnG (par d n).p (bp j) ∧
        |qn (par d n).p (bp j)| ≤ 2 ^ E1) →
      (∀ j : Fin d, σ.arr 29 j = qn (par d n).p (Gp j) ∧ OnG (par d n).p (Gp j) ∧
        |qn (par d n).p (Gp j)| ≤ 2 ^ E1) →
      σ.sc 59 = qn (par d n).p kp → OnG (par d n).p kp → |qn (par d n).p kp| ≤ 2 ^ E1 →
      σ.sc 63 = qn (par d n).p lp → OnG (par d n).p lp → |qn (par d n).p lp| ≤ 2 ^ E1 →
      σ.sc 72 = s5 → |s5| ≤ 2 ^ E1 →
      (∀ i : Fin d, σ.arr aWv i = ((fun i j => qn (par d n).p (st.A i j) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Γ) i) →
      (∀ j, |Γ j| ≤ 2 ^ E1) →
      (∀ mu' : Fin d → ℚ,
        tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) =
          .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ →
        StBnd (par d n).p E (par d n).Rint ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ ∧
        ∀ x, ellRI (clearQ (callLOf (mkCfg d n m A b c S) n Bp bp kp (wmuOf (par d n) st s5 Γ))) = some x →
          (∀ j, |x j| ≤ 2 ^ E) ∧
          ellExp (clearQ (callLOf (mkCfg d n m A b c S) n Bp bp kp (wmuOf (par d n) st s5 Γ))) ≤ E) →
      C * (d + m + M.size + n.size + E1 + 1) ^ k ≤ ℓ → C * (d + m + M.size + n.size + E1 + 1) ^ k < 2 ^ ℓa →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xtail L) σ (C * (d + m + M.size + n.size + E1 + 1) ^ k)
        (RPost L n m K0 E (mkCfg d n m A b c S)
          (tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)) t P0)

end AdversarialBco.Bit.Transfer.BLM
