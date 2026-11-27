/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRb
public import AdversarialBco.Bit.Transfer.XBLTailRf

@[expose] public section

/-!
# The tail of BL's round, part c: the state's numerators

`tl_runVals`: the state's numerators of `μ'` and `A'` from `BLInv` in mode `run`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The state's numerators of `μ'` and `A'` from `BLInv` in mode `run`. -/
theorem tl_runVals {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg (.run st) t σ) :
    ∃ (Dm : ℤ) (mu : Fin d → ℤ), 0 < Dm ∧ σ.sc sDmu = Dm ∧ |Dm| ≤ 2 ^ E ∧
      (∀ j : Fin d, σ.arr aMu j = mu j ∧ |mu j| ≤ 2 ^ E ∧ (mu j : ℚ) / Dm = st.mu j) ∧
      (∀ i j : Fin d, OnG cfg.par.p (st.A i j) ∧ |qn cfg.par.p (st.A i j)| ≤ 2 ^ E) := by
  obtain ⟨-, -, ⟨Dm, hDm, hDm', hmu⟩, hAst, -⟩ := h.mode
  choose mu hmu1 hmu2 using hmu
  have hdi : ∀ i j : Fin d, d * i + j < asz d := fun i j => by
    unfold asz
    have := i.2; have := j.2
    nlinarith
  refine ⟨Dm, mu, hDm, hDm', h.slot_abs (by decide) hDm', fun j => ⟨hmu1 j, h.arr_abs (by decide) ?_ (hmu1 j),
    hmu2 j⟩, fun i j => ⟨(hAst i j).2, h.arr_abs (by decide) (hdi i j) (hAst i j).1⟩⟩
  unfold asz; have := j.2; nlinarith

end AdversarialBco.Bit.Transfer.BLM
