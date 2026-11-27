/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRa

@[expose] public section

/-!
# The tail of BL's round, part b: the frames of the data and of a call

`TIn.data`, `TIn.call`: the frame of the two data commands and the frame of a call keep `TIn`, the cells that the
tail reads.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The frame of the two data commands keeps `TIn`. -/
theorem TIn.data {L : Layout} {n m K0 E E1 : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {σ σ' : Env d}
    (h : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hF : FrameA (fun y => (sPl ≤ y ∧ y < sPl + 6) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j < 32)
      (fun a _ => (aPHn ≤ a ∧ a ≤ aPfd) ∨ a = 30) σ σ') (hd : σ'.draws = σ.draws) :
    TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ' :=
  h.frame hF (fun y hy => by simp only [sPl, nSP] at hy ⊢; omega) (fun j hj => by omega)
    (fun a k hk => by simp only [aPHn, aPfd, nAP] at hk ⊢; omega) hd

/-- The frame of a call keeps `TIn`. -/
theorem TIn.call {L : Layout} {n m K0 E E1 : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {σ σ' : Env d}
    (h : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hF : FrameA (fun y => oE ≤ y ∨ SPrep y) (fun j => rEE ≤ j ∨ NPrep j) (fun a _ => aWE ≤ a ∨ APrep a) σ σ')
    (hd : σ'.draws = σ.draws) : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ' :=
  h.frame hF (fun y hy => by simp only [oE, SPrep, SRow, sEl, nSP] at hy ⊢; omega)
    (fun j hj => by simp only [rEE, NPrep, NRow] at hj; omega)
    (fun a k hk => by simp only [aWE, APrep, ARow, aEH, aEf, nAP] at hk ⊢; omega) hd

end AdversarialBco.Bit.Transfer.BLM
