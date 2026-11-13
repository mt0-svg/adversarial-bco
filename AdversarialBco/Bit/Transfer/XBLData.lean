/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# The call data of BL's round (frozen statements)

Two commands of BL's round write the data of a call of the projection routine as integer pairs (`PrepIn`,
Bit/Transfer/XBLCall.lean), from BL's invariant and the round's cells; `CallBL` then runs the call.

* `DataT` (R11 TEST): the call `callT` of `BLPure.step`. In the first round of an epoch (`st.first`): `H = 0`, `g = 0`,
  `ℓ = 0`, `r = 1 - ε'`, `e = (1 - ε')²/(N_e d 8)`; after it: `H = B Bᵀ`, `g = b`, `ℓ = LT - k`, `r = r'/2`,
  `e = r'²/(N_e d 8)`, `r' = s'_b (1 - ε')`; in both, `P = B' B'ᵀ` and `f = b' - (η'/2) G'`.
* `DataL` (R14 LINE): `H = P = B' B'ᵀ`, `g = b'`, `ℓ = L_μ - k'`, `r = r'/2`, `f = P w_μ`, `e = e_BL`.

The round's cells read: `B'`, `b'`, `G'` as numerators on the grid `2^{-p}` in the arrays `27`, `28`, `29` (`B'` in the
cells `d i + j`), `k'` as its numerator in the slot `59`, `w_μ` as the numerators `ŵ` in the array `31` over the
positive denominator `D_w` in the slot `91`; `B`, `b`, `k`, `first` and the parameters from `BLInv` in mode `run`.
Every one of them at most `2^E` in absolute value. Work term `W = d + E + 1`: within `C W^k` units, under `C W^k ≤ ℓ`
and `C W^k < 2^ℓa`, the pairs below `2^(C W^k)`. The commands read no coin and change only the slots `64..69` and from
`256` on, the registers `19..31`, the arrays `16..23` and `30`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

/-- **The data of R11 TEST (frozen).** -/
def DataT : Prop :=
  ∃ (xdt : Layout → XCmd) (C k : ℕ),
    ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d)
      (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (σ : Env d),
      1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
      (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
        |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
      (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
      (∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E) →
      C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
      XRunsB L X ℓa ℓ (xdt L) σ (C * (d + E + 1) ^ k) (fun σ' =>
        PrepIn σ' cfg (C * (d + E + 1) ^ k) (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
          (if st.first then 0 else LT cfg.par - st.k) (if st.first then 1 - cfg.par.eps else BLP.rB cfg.par / 2)
          (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
          (if st.first then (1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8)
            else BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8)) ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
          (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ')

/-- **The data of R14 LINE (frozen).** -/
def DataL : Prop :=
  ∃ (xdl : Layout → XCmd) (C k : ℕ),
    ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t : ℕ) (cfg : Cfg d) (st : St d)
      (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wh : Fin d → ℤ) (Dw : ℤ) (σ : Env d),
      1 ≤ d → 1 ≤ n → cfg.par = par d n → LayOK L d ℓa → BLLay L → BLInv L n m K0 E cfg (.run st) t σ →
      (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
        |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
      (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
      σ.sc 59 = qn cfg.par.p kp → OnG cfg.par.p kp → |qn cfg.par.p kp| ≤ 2 ^ E →
      0 < Dw → Dw ≤ 2 ^ E → σ.sc 91 = Dw → (∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ E) →
      C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
      XRunsB L X ℓa ℓ (xdl L) σ (C * (d + E + 1) ^ k) (fun σ' =>
        PrepIn σ' cfg (C * (d + E + 1) ^ k) (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (BLP.rB cfg.par / 2) (Bp * Bpᵀ)
          ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL cfg.par d n) ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
          (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ')

end AdversarialBco.Bit.Transfer.BLM
