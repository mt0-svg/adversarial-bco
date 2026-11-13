/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# DET, the run of one epoch

The round map `df2NextAP` of an epoch, read off the context `Df2Ctx` and a path: the quantities that the round
computes after the update (`Σ'`, `A'`, `Ĝ`, `l`, the centre `z` of the test, the two regions, the two calls, the
statistic `Ξ` of the test), the unfolding of a round (`nextAP_unfold`, by `rfl`), and the three outcomes of a round
that reaches the test: a fire (`fire_iff`), a continuation (`cont_iff`, `st_succ_of_cont`), else the guard.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- `Σ' = (Σ - (c/q) w wᵀ)/a`. -/
noncomputable def Sn (s : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (c.aa π s)⁻¹ • ((c.st π s).S - (c.cc π s / c.qq π s) • vecMulVec (c.w π s) (c.w π s))

/-- `c' = (c/q)/(1 + (a/q)^{1/2})`. -/
noncomputable def cp (s : ℕ) : ℝ := c.cc π s / c.qq π s / (1 + Real.sqrt (c.aa π s / c.qq π s))

/-- `A' = a^{-1/2} (A - c' w ξᵀ)`. -/
noncomputable def An (s : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (Real.sqrt (c.aa π s))⁻¹ • ((c.st π s).A - c.cp π s • vecMulVec (c.w π s) (π.xi s))

/-- `Ĝ' = Ĝ + ĝ`. -/
noncomputable def Gn (s : ℕ) : Fin d → ℝ := (c.st π s).G + c.ghat π s

/-- `l' = l + ⟨ĝ, μ⟩`. -/
noncomputable def ln (s : ℕ) : ℝ := (c.st π s).l + c.ghat π s ⬝ᵥ (c.st π s).mu

/-- The centre of the test, `z = Σ' (b' - (η/2) Ĝ')`. -/
noncomputable def zz (s : ℕ) : Fin d → ℝ := c.Sn π s *ᵥ (c.bn π s - (c.p.eta / 2) • c.Gn π s)

/-- The region of the test call, `R⁻` (all of `K_ε` in the first round of an epoch). -/
def Rm (s : ℕ) : Set (Fin d → ℝ) :=
  if (c.st π s).first then c.Keps
  else {y | y ∈ c.Keps ∧ df2Phi (c.st π s).P (c.st π s).b (c.st π s).k y ≤ (c.p.c1 - c.p.gam) * c.p.rho}

/-- The accuracy of the test call, `min (1, α ρ/2)`. -/
noncomputable def eT : ℝ := min 1 (c.p.alpha * c.p.rho / 2)

/-- The test call. -/
noncomputable def tcall (s : ℕ) : Option (Fin d → ℝ) :=
  c.ap s (c.Rm π s) (c.st π s).ctr (c.st π s).r c.p.R (c.Pn π s) (c.zz π s) c.eT

/-- The statistic of the test, `Ξ(y) = η (l' - ⟨Ĝ', y⟩) - 2 Φ'(y)`. -/
noncomputable def Xi (s : ℕ) (y : Fin d → ℝ) : ℝ := c.p.eta * (c.ln π s - c.Gn π s ⬝ᵥ y) - 2 * c.PhiN π s y

/-- The Newton point of line μ, `w_μ = μ - (η Y/((1 - λ) q)) w`. -/
noncomputable def wmu (s : ℕ) : Fin d → ℝ :=
  (c.st π s).mu - (c.p.eta * c.Y π s / ((1 - c.p.lam) * c.qq π s)) • c.w π s

/-- The region of line μ, `R⁺ = {y ∈ K_ε : Φ'(y) ≤ c₁ ρ}`. -/
def Rp (s : ℕ) : Set (Fin d → ℝ) := {y | y ∈ c.Keps ∧ c.PhiN π s y ≤ c.p.c1 * c.p.rho}

/-- The accuracy of line μ. -/
noncomputable def eM (s : ℕ) : ℝ := 1 / (16 * c.n ^ 2 * max 1 (4 * c.p.R ^ 2 * (c.Pn π s).trace))

/-- The call of line μ, on the ball `(ctr', r')`. -/
noncomputable def mcall (s : ℕ) (ctr' : Fin d → ℝ) (r' : ℝ) : Option (Fin d → ℝ) :=
  c.ap s (c.Rp π s) ctr' r' c.p.R (c.Pn π s) (c.wmu π s) (c.eM π s)

/-- The first guard: the two scalars. -/
def GdA (s : ℕ) : Prop := c.aa π s ≤ 0 ∨ c.qq π s ≤ 0

/-- The second guard: the two traces. -/
def GdT (s : ℕ) : Prop := d / c.p.δe < (c.Pn π s).trace ∨ d / c.p.δe < (c.Sn π s).trace

/-- The third guard: the centre of the test. -/
def GdZ (s : ℕ) : Prop := c.p.R / c.p.δe ^ 3 < oNorm (c.zz π s)

/-- The fourth guard: the Newton point of line μ. -/
def GdW (s : ℕ) : Prop :=
  c.p.R + c.p.eta * Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) < oNorm (c.wmu π s)

/-- The state after a round that continues the epoch, from the two points returned. -/
noncomputable def stNext (s : ℕ) (pt mu' : Fin d → ℝ) : Df2St d :=
  ⟨false, mu', c.Pn π s, c.Sn π s, c.An π s, c.bn π s, c.kn π s, c.Gn π s, c.ln π s, (1 - c.p.sb) • pt,
    c.p.sb * (1 - c.p.eps)⟩

open Classical in
/-- One round from the state of round `s`, unfolded. -/
theorem nextAP_unfold (s : ℕ) :
    df2NextAP (c.ap s) c.p c.n c.Keps (c.st π s) (π.xi s) (c.w π s) (c.Y π s) =
      if c.aa π s ≤ 0 ∨ c.qq π s ≤ 0 then .guard else
      if d / c.p.δe < (c.Pn π s).trace ∨ d / c.p.δe < (c.Sn π s).trace then .guard else
      if c.p.R / c.p.δe ^ 3 < oNorm (c.zz π s) then .guard else
      match c.tcall π s with
      | none => .guard
      | some pt =>
        if c.Xi π s pt ≤ -(c.p.theta * c.p.rho) then .run (df2Init c.p d) else
        if c.p.R + c.p.eta * Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) < oNorm (c.wmu π s) then .guard else
        match c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) with
        | none => .guard
        | some mu' => .run (c.stNext π s pt mu') := rfl

/-- The mode after a round from a running mode. -/
theorem mode_succ_of_run (s : ℕ) (h : c.mode π s = .run (c.st π s)) :
    c.mode π (s + 1) = df2NextAP (c.ap s) c.p c.n c.Keps (c.st π s) (π.xi s) (c.w π s) (c.Y π s) := by
  show (df2RoundE c (c.ap s) (π.g s) (π.e s) (π.xi s) (c.mode π s)).2 = _
  rw [h]
  rfl

theorem df2Init_first (p : Df2OPar) : (df2Init p d).first = true := rfl

theorem stNext_first (s : ℕ) (pt mu' : Fin d → ℝ) : (c.stNext π s pt mu').first = false := rfl

theorem ite_of_neg {α : Sort*} {q : Prop} [Decidable q] (h : ¬ q) (a b : α) : (if q then a else b) = b := by
  simp [h]

theorem ite_of_pos {α : Sort*} {q : Prop} [Decidable q] (h : q) (a b : α) : (if q then a else b) = a := by
  simp [h]

/-- A round from a running mode fires exactly when it passes the three guards before the test, the test call
returns a point and the statistic is at most `-θ ρ` there. -/
theorem fire_iff (s : ℕ) (h : c.mode π s = .run (c.st π s)) :
    c.fire π s ↔ ¬ c.GdA π s ∧ ¬ c.GdT π s ∧ ¬ c.GdZ π s ∧
      ∃ pt, c.tcall π s = some pt ∧ c.Xi π s pt ≤ -(c.p.theta * c.p.rho) := by
  unfold fire GdA GdT GdZ
  rw [c.mode_succ_of_run π s h, nextAP_unfold]
  constructor
  · intro hf
    by_cases h1 : c.aa π s ≤ 0 ∨ c.qq π s ≤ 0
    · rw [ite_of_pos h1] at hf; cases hf
    rw [ite_of_neg h1] at hf
    by_cases h2 : d / c.p.δe < (c.Pn π s).trace ∨ d / c.p.δe < (c.Sn π s).trace
    · rw [ite_of_pos h2] at hf; cases hf
    rw [ite_of_neg h2] at hf
    by_cases h3 : c.p.R / c.p.δe ^ 3 < oNorm (c.zz π s)
    · rw [ite_of_pos h3] at hf; cases hf
    rw [ite_of_neg h3] at hf
    rcases htc : c.tcall π s with _ | pt
    · rw [htc] at hf; cases hf
    rw [htc] at hf
    simp only at hf
    by_cases h4 : c.Xi π s pt ≤ -(c.p.theta * c.p.rho)
    · exact ⟨h1, h2, h3, pt, rfl, h4⟩
    rw [ite_of_neg h4] at hf
    by_cases h5 : c.p.R + c.p.eta * Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) < oNorm (c.wmu π s)
    · rw [ite_of_pos h5] at hf; cases hf
    rw [ite_of_neg h5] at hf
    rcases hmc : c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) with _ | mu'
    · rw [hmc] at hf; cases hf
    rw [hmc] at hf
    simp only [Df2Mode.run.injEq] at hf
    have := congrArg Df2St.first hf
    simp [stNext_first, df2Init_first] at this
  · rintro ⟨h1, h2, h3, pt, htc, h4⟩
    rw [ite_of_neg h1, ite_of_neg h2, ite_of_neg h3, htc]
    simp only
    rw [ite_of_pos h4]

/-- A round from a running mode continues the epoch exactly when it passes the four guards, the test call returns
a point where the statistic is above `-θ ρ`, and the call of line μ returns a point. -/
theorem cont_iff (s : ℕ) (h : c.mode π s = .run (c.st π s)) :
    c.cont π s ↔ ¬ c.GdA π s ∧ ¬ c.GdT π s ∧ ¬ c.GdZ π s ∧
      ∃ pt, c.tcall π s = some pt ∧ ¬ c.Xi π s pt ≤ -(c.p.theta * c.p.rho) ∧ ¬ c.GdW π s ∧
        ∃ mu', c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) = some mu' ∧
          c.mode π (s + 1) = .run (c.stNext π s pt mu') := by
  have hm := c.mode_succ_of_run π s h
  rw [nextAP_unfold] at hm
  unfold cont GdA GdT GdZ GdW
  constructor
  · rintro ⟨st, hst, hfst⟩
    rw [hm] at hst
    by_cases h1 : c.aa π s ≤ 0 ∨ c.qq π s ≤ 0
    · rw [ite_of_pos h1] at hst; cases hst
    rw [ite_of_neg h1] at hst hm
    by_cases h2 : d / c.p.δe < (c.Pn π s).trace ∨ d / c.p.δe < (c.Sn π s).trace
    · rw [ite_of_pos h2] at hst; cases hst
    rw [ite_of_neg h2] at hst hm
    by_cases h3 : c.p.R / c.p.δe ^ 3 < oNorm (c.zz π s)
    · rw [ite_of_pos h3] at hst; cases hst
    rw [ite_of_neg h3] at hst hm
    rcases htc : c.tcall π s with _ | pt
    · rw [htc] at hst; cases hst
    rw [htc] at hst hm
    simp only at hst hm
    by_cases h4 : c.Xi π s pt ≤ -(c.p.theta * c.p.rho)
    · rw [ite_of_pos h4] at hst
      simp only [Df2Mode.run.injEq] at hst
      rw [← hst, df2Init_first] at hfst; cases hfst
    rw [ite_of_neg h4] at hst hm
    by_cases h5 : c.p.R + c.p.eta * Real.sqrt (16 * d * c.n * c.p.Le / c.p.δe) < oNorm (c.wmu π s)
    · rw [ite_of_pos h5] at hst; cases hst
    rw [ite_of_neg h5] at hst hm
    rcases hmc : c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) with _ | mu'
    · rw [hmc] at hst; cases hst
    rw [hmc] at hm
    exact ⟨h1, h2, h3, pt, rfl, h4, h5, mu', hmc, hm⟩
  · rintro ⟨-, -, -, pt, -, -, -, mu', -, hm'⟩
    exact ⟨c.stNext π s pt mu', hm', rfl⟩

/-- After a round that continues the epoch, the next state. -/
theorem st_succ_of_cont (s : ℕ) (h : c.mode π s = .run (c.st π s)) (hc : c.cont π s) :
    ∃ pt mu', c.tcall π s = some pt ∧ ¬ c.Xi π s pt ≤ -(c.p.theta * c.p.rho) ∧
      c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) = some mu' ∧
      c.mode π (s + 1) = .run (c.st π (s + 1)) ∧ c.st π (s + 1) = c.stNext π s pt mu' := by
  obtain ⟨-, -, -, pt, htc, h4, -, mu', hmc, hm⟩ := (c.cont_iff π s h).1 hc
  have hst : c.st π (s + 1) = c.stNext π s pt mu' := by
    show (c.mode π (s + 1)).stOr (df2Init c.p d) = _
    rw [hm]; rfl
  exact ⟨pt, mu', htc, h4, hmc, by rw [hm, hst], hst⟩

/-- The modes of the rounds up to `τ` run, when the rounds before `τ` continue. -/
theorem mode_run_of_cont (τ : ℕ) (hc : ∀ s < τ, c.cont π s) : ∀ s ≤ τ, c.mode π s = .run (c.st π s) := by
  intro s hs
  induction s with
  | zero => rfl
  | succ s ih =>
    obtain ⟨st, hst, -⟩ := hc s (by omega)
    have : c.st π (s + 1) = st := by
      show (c.mode π (s + 1)).stOr (df2Init c.p d) = _
      rw [hst]; rfl
    rw [hst, this]

end Df2Ctx

end AdversarialBco.Poly
