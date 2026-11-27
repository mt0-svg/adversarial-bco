/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR3

@[expose] public section

/-!
# BL's round on the machine, R2 to R4 in mode `run`: the pieces

BL's point `X'` from the machine's integers (`XQ_mach`), the slot `sObs` of the reading `⌊2^p f_t(x_t)⌋`, the frames
of a round (`FrameC`, `FrameC.ofA`, `FrameC.mono`), and the bounds `abs_mul_pow`, `abs_add_pow`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.BitRAM (toE inputMem entry)

variable {d : ℕ}

/-! ## Bounds -/

theorem abs_mul_pow {x y : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ b) : |x * y| ≤ 2 ^ (a + b) := by
  rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

theorem abs_add_pow {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x + y| ≤ 2 ^ (a + 1) := by
  rw [pow_succ]; exact (abs_add_le _ _).trans (by linarith)

/-! ## The play of mode `run` from the machine's integers -/

/-- BL's point `X'` from the machine's integers. -/
theorem XQ_mach (cfg : Cfg d) (st : St d) (Dm : ℤ) (mh Γ : Fin d → ℤ) (g : ℕ) (hDm : 0 < Dm)
    (hmh : ∀ j, (mh j : ℚ) / Dm = st.mu j) (hA : ∀ i k, OnG cfg.par.p (st.A i k))
    (hlam : OnG cfg.par.pF cfg.par.lam) (j : Fin d) :
    XQ cfg st (fun i => (Γ i : ℚ) / 2 ^ g) j =
      (xhI mh (fun i k => qn cfg.par.p (st.A i k)) Γ Dm (2 ^ cfg.par.pF) (2 ^ cfg.par.p) (2 ^ g)
        (qn cfg.par.pF cfg.par.lam) j : ℚ) / ((Dm * 2 ^ cfg.par.pF * 2 ^ cfg.par.p * 2 ^ g : ℤ) : ℚ) := by
  have hmuq : st.mu = fun j => (mh j : ℚ) / Dm := funext fun j => (hmh j).symm
  have hAq : st.A = Matrix.of fun i k => ((qn cfg.par.p (st.A i k) : ℤ) : ℚ) / ((2 ^ cfg.par.p : ℤ) : ℚ) := by
    ext i k; rw [Matrix.of_apply]; push_cast; exact eq_qn_div _ (hA i k)
  have hlq : cfg.par.lam = ((qn cfg.par.pF cfg.par.lam : ℤ) : ℚ) / ((2 ^ cfg.par.pF : ℤ) : ℚ) := by
    push_cast; exact eq_qn_div _ hlam
  have hg : (2 : ℚ) ^ g = ((2 ^ g : ℤ) : ℚ) := by push_cast; rfl
  unfold XQ
  rw [hg]
  conv_lhs => rw [hmuq, hAq, hlq]
  rw [XQ_int Dm (2 ^ cfg.par.pF) (2 ^ cfg.par.p) (2 ^ g) (qn cfg.par.pF cfg.par.lam) mh
    (fun i k => qn cfg.par.p (st.A i k)) Γ hDm (by positivity) (by positivity) (by positivity) j]
  rfl

/-! ## R2 to R4 in mode `run` -/

/-- The slot of the reading `obs`. -/
abbrev sObs : ℕ := 44

/-- `romega` with the slot of the reading unfolded. -/
macro "r24omega" : tactic => `(tactic| ((try simp only [sObs] at *) <;> romega))


/-- `σ'` agrees with `σ` outside the cells `S`, `N`, `Ar` (rounds and points free). -/
def FrameC (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) (σ σ' : Env d) : Prop :=
  (∀ j, ¬ N j → σ'.nat j = σ.nat j) ∧ (∀ y, ¬ S y → σ'.sc y = σ.sc y) ∧ (∀ b k, ¬ Ar b k → σ'.arr b k = σ.arr b k)

theorem FrameC.ofA {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameA S N Ar σ σ') :
    FrameC S N Ar σ σ' := ⟨h.1, h.2.1, h.2.2.1⟩

theorem FrameC.mono {S N S' N' : ℕ → Prop} {Ar Ar' : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameC S N Ar σ σ')
    (hS : ∀ y, S y → S' y) (hN : ∀ j, N j → N' j) (hA : ∀ b k, Ar b k → Ar' b k) : FrameC S' N' Ar' σ σ' :=
  ⟨fun j hj => h.1 j fun h' => hj (hN j h'), fun y hy => h.2.1 y fun h' => hy (hS y h'),
    fun b k hb => h.2.2 b k fun h' => hb (hA b k h')⟩

end AdversarialBco.Bit.Transfer.BLM
