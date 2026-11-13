/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# Two pieces of BL's program split off (frozen statements)

The rounds of BL's program take these three statements as hypotheses; each is a `Prop` with no proof
here, to be proved in its own file:

* `CallBL`: one call of BL's projection routine (R11 TEST, R14 LINE) as one command, from the call data as integer
  pairs (`PrepIn`, Bit/Transfer/XBLCall.lean) and BL's context (`RowCtx`): the preparation (`CallPrepBL`), then the
  routine (`EllRule`) with the row command (`RowBL`). The theorem to prove:
  `callBL_of : EllRule → CallPrepBL → RowBL → CallBL`.
* `MagBL`: the magnitudes of BL's state on the pure run (Bit/BLPure.lean): on every input, against every admissible
  strategy, in every round `t ≤ n` in mode `run`, the numerators of `A', B', b', k', G', l'` on the grid `2^{-p}` are
  at most `2^E` with `E` polynomial in `d, m, size M, size n` and the bound `E₀` of the position, and `μ'` lies in the
  box of radius `R_int`. The theorem to prove: `magBL : MagBL`.
* `ExpBL`: the exponent `ellExp` of the point that a call of BL returns (its denominator `2^ellExp`) is polynomial in
  `d`, `size n` and the bound `2^E₀` of the linear term, for the objective `P = B'B'ᵀ` with `B'` on the grid `2^{-p}`
  and `frob2 B' ≤ 2Λ`, and the three pairs (radius, accuracy) of BL's calls. The theorem to prove: `expBL : ExpBL`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## One call of the projection routine -/

/-- **The call contract (frozen).** One command `xcall L` runs one call of BL's projection routine: from the call data
`H, g, ℓ, r, P, f, e` as integer pairs below `2^s` (`PrepIn`) and BL's context (`RowCtx`), it leaves the routine's
output for `clearQ (callOf cfg H g ℓ r P f e)` in the block `blkBL` (`EllOut`), for every input `(A, b)` of height `M`,
frame centre `c`, position `S`. Work term `W = d + m + size M + E + s + 1`: within `C W^k` units, under `C W^k ≤ ℓ`
and `C W^k < 2^ℓa`, with the block's room `nS, nN, nA` in the layout. It reads no coin and changes only the block, the
cells of the preparation (`SPrep`, `NPrep`, `APrep`). -/
def CallBL : Prop :=
  ∃ (xcall : Layout → XCmd) (C k nS nN nA : ℕ),
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M E ℓa ℓ s : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
      (b : Fin m → ℚ) (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (H : Matrix (Fin d) (Fin d) ℚ)
      (g : Fin d → ℚ) (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (σ : Env d),
      1 ≤ d → LayOK L d ℓa → blkBL.OK L nS nN nA → RealRAM.HeightLE A b M →
      OnG (par d n).pF (par d n).eps → 0 ≤ (par d n).eps → (par d n).eps ≤ 1 →
      RowCtx L m E (mkCfg d n m A b c S) σ → PrepIn σ (mkCfg d n m A b c S) s H g ℓq r P f e →
      C * (d + m + M.size + E + s + 1) ^ k ≤ ℓ → C * (d + m + M.size + E + s + 1) ^ k < 2 ^ ℓa →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xcall L) σ (C * (d + m + M.size + E + s + 1) ^ k) (fun σ' =>
        EllOut blkBL (ellRI (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)))
          (ellExp (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e))) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => oE ≤ y ∨ SPrep y) (fun j => rEE ≤ j ∨ NPrep j) (fun a _ => aWE ≤ a ∨ APrep a) σ σ')

/-! ## The magnitudes of the state -/

/-- The position `(μ_S, A_S)` over one positive denominator `D_S ≤ 2^E₀`, numerators at most `2^E₀`. -/
def PosBnd (cfg : Cfg d) (E0 : ℕ) : Prop :=
  ∃ DS : ℤ, 0 < DS ∧ DS ≤ 2 ^ E0 ∧ (∀ j, ∃ x : ℤ, |x| ≤ 2 ^ E0 ∧ (x : ℚ) / DS = cfg.μS j) ∧
    ∀ i j, ∃ x : ℤ, |x| ≤ 2 ^ E0 ∧ (x : ℚ) / DS = cfg.AS i j

/-- BL's state in mode `run`: the numerators of `A', B', b', k', G', l'` on the grid `2^{-p}` at most `2^E`, every
coordinate of `μ'` at most `R` in absolute value. -/
def StBnd (p E R : ℕ) (st : St d) : Prop :=
  (∀ i j, |qn p (st.A i j)| ≤ 2 ^ E) ∧ (∀ i j, |qn p (st.B i j)| ≤ 2 ^ E) ∧ (∀ j, |qn p (st.b j)| ≤ 2 ^ E) ∧
    |qn p st.k| ≤ 2 ^ E ∧ (∀ j, |qn p (st.G j)| ≤ 2 ^ E) ∧ |qn p st.l| ≤ 2 ^ E ∧ ∀ j, |st.mu j| ≤ R

/-- **The magnitude contract (frozen).** On every input of the frozen statement, against every
admissible strategy, on every coin sequence whose position is bounded by `2^E₀` (`PosBnd`), BL's state in every round
`t ≤ n` in mode `run` has numerators at most `2^E`, `E = C (d + m + size M + size n + E₀ + 1)^k`, and `μ'` in the box of
radius `R_int`. -/
def MagBL : Prop :=
  ∃ C k : ℕ, ∀ (d n m M E0 : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b →
    ∀ σ : Strategy d, AdmStrat (polytope A b) n σ → ∀ cs : ℕ → Bool,
      PosBnd (cfgOf RoutinesQ d n m A b cs) E0 →
      ∀ (t : ℕ) (st : St d), t ≤ n → modeAt RoutinesQ d n m A b σ cs t = .run st →
        StBnd (par d n).p (C * (d + m + M.size + n.size + E0 + 1) ^ k) (par d n).Rint st

/-- The pairs (radius, accuracy) of BL's three calls: R11 in the first round of an epoch, R11 after it, R14. -/
def callRE (P : Par) (d n : ℕ) : List (ℚ × ℚ) :=
  [(1 - P.eps, (1 - P.eps) ^ 2 / (P.Ne * d * 8)),
   (BLP.rB P / 2, BLP.rB P ^ 2 / (P.Ne * d * 8)), (BLP.rB P / 2, eBL P d n)]

/-- **The exponent contract (frozen).** For every call of BL with the objective `P = B'B'ᵀ`, `B'` on the grid `2^{-p}`
with `frob2 B' ≤ 2Λ`, a linear term `f` with coordinates at most `2^E₀` and one of the three pairs (radius, accuracy)
of BL, the exponent of the routine's point is at most `C (d + size n + E₀ + 1)^k`, whatever the rows and the quadratic
constraint. -/
def ExpBL : Prop :=
  ∃ C k : ℕ, ∀ (d n m E0 : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq : ℚ)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (r e : ℚ),
    1 ≤ d → 1 ≤ n → (∀ i j, OnG (par d n).p (Bp i j)) → frob2 Bp ≤ 2 * (par d n).Lam →
    (∀ j, |f j| ≤ 2 ^ E0) → (r, e) ∈ callRE (par d n) d n →
      ellExp (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r (Bp * Bpᵀ) f e)) ≤ C * (d + n.size + E0 + 1) ^ k

end AdversarialBco.Bit.Transfer.BLM
