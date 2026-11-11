/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetRun
public import AdversarialBco.Poly.Df2DetProof
public import AdversarialBco.Poly.Df2DetTools

@[expose] public section

/-!
# DET, the proof

`df2DetOf_holds : Df2DetOf`. The hypotheses of DET are bundled in `DetHyp`, which extends `DetBase` (the same
without the five events, all that the state invariants up to `τ` read); `τ = c.tau π m`. The proof is the induction on
the rounds:

* the states up to `τ` (`StInv`): the conditions before `τ`, Lemma D.2, the bonus, the sums `Ĝ` and `l`;
* the closure at `τ` (`closure_tau`): conditions 2 and 3 at `τ` from the events Gauss and S-DF and from X8;
* the region (`inc2_at`, `mon_at`): Proposition D.8 and Lemma D.7 on the run;
* the three calls (`acc_all`): the test call is accurate (its ball is that of the round before), the online Newton
  inequality with the defects of line μ holds, and a round without a fire has its ball in the next lower region
  (Lemma D.17, with Lemma D.18 for the centre), so line μ is accurate;
* Lemma D.14 at `τ` (`epoch_ok`), with Lemma D.10 for (W4s), (W4c) and Lemma D.12 for (W1).

Sums over the rounds: `OmH t`, `Lin t`, ... sum over `u < t`, so the quantities of round `t` (DF2's index `t + 1`)
carry `t + 1`.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- The estimated bonus `Ω̂_t(y) = (η κ/2) ∑_{u < t} |y - μ_u|²_{ŝ''_u}`. -/
noncomputable def OmH (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  c.p.eta * c.p.kap / 2 * ∑ u ∈ Finset.range t, df2Sq (c.shh π u) (y - (c.st π u).mu)

/-- The true bonus `Ω_t(y) = (η κ/2) ∑_{u < t} |y - μ_u|²_{s''_u(μ_u)}`. -/
noncomputable def OmT (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  c.p.eta * c.p.kap / 2 * ∑ u ∈ Finset.range t, df2Sq (c.sHess π u) (y - (c.st π u).mu)

/-- `W_t(y) = ∑_{u < t} |y - μ_u|²_{s''_u(μ_u)}`. -/
noncomputable def Wt (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range t, df2Sq (c.sHess π u) (y - (c.st π u).mu)

/-- `Lin_t(y) = ∑_{u < t} ⟨s'_u(μ_u), μ_u - y⟩`. -/
noncomputable def Lin (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range t, c.sGrad π u ⬝ᵥ ((c.st π u).mu - y)

/-- `ĥLin_t(y) = ∑_{u < t} ⟨ĝ_u, μ_u - y⟩`. -/
noncomputable def hLin (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range t, c.ghat π u ⬝ᵥ ((c.st π u).mu - y)

/-- `sReg_t(y) = ∑_{u < t} (s_u(μ_u) - s_u(y))`. -/
noncomputable def sReg (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range t, (c.surr π u (WithLp.toLp 2 (c.st π u).mu) - c.surr π u (WithLp.toLp 2 y))

/-- `T_t = Lin_t - W_t/4`. -/
noncomputable def TT (t : ℕ) (y : Fin d → ℝ) : ℝ := c.Lin π t y - 1 / 4 * c.Wt π t y

/-- `T̂_t = ĥLin_t - (1/4) ∑_{u < t} |y - μ_u|²_{ŝ''_u}`. -/
noncomputable def ThT (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  c.hLin π t y - 1 / 4 * ∑ u ∈ Finset.range t, df2Sq (c.shh π u) (y - (c.st π u).mu)

/-- `ĥqReg^κ_t(y) = ∑_{u < t} (⟨ĝ_u, μ_u - y⟩ - (κ/2) |y - μ_u|²_{ŝ''_u})`. -/
noncomputable def hqReg (t : ℕ) (y : Fin d → ℝ) : ℝ :=
  ∑ u ∈ Finset.range t, (c.ghat π u ⬝ᵥ ((c.st π u).mu - y) - c.p.kap / 2 * df2Sq (c.shh π u) (y - (c.st π u).mu))

/-- The lower region after round `t`, `R⁻_{t+1} = {y ∈ K_ε : Φ_{t+1}(y) ≤ (c₁ - γ) ρ}`. -/
def RmN (t : ℕ) : Set (Fin d → ℝ) := {y | y ∈ c.Keps ∧ c.PhiN π t y ≤ (c.p.c1 - c.p.gam) * c.p.rho}

/-- (A5) at the state of round `s`. -/
def StOK (s : ℕ) : Prop := Df2StateOK c.p c.Kt (c.st π s).mu (c.st π s).A

end Df2Ctx

/-! ## The hypotheses of DET -/

/-- The hypotheses of DET for the context `c` (at the parameters `df2oPar d c.n δ`), the path `π` and the horizon
`m`, without the five events: what the state invariants up to the stopping time read. -/
structure DetBase {d : ℕ} (c : Df2Ctx d) (δ : ℝ) (π : Df2Path d) (m : ℕ) : Prop where
  L1 : Df2LayerOne
  W : LemmaW
  SI : Df2SIFacts
  hd : 1 ≤ d
  hn : 1 ≤ c.n
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hp : c.p = df2oPar d c.n δ
  heps : c.p.eps ≤ 1 / 2
  rows : Df2Rows c.p d c.n
  hm1 : 1 ≤ m
  hmn : m ≤ c.n
  body : Df2Body d c.p.R c.Kt
  hap : ApSpec c.ap
  adm : ∀ s < m, AdmLoss c.Kt (π.g s)

/-- The hypotheses of DET: `DetBase` and the five events on the path. -/
structure DetHyp {d : ℕ} (c : Df2Ctx d) (δ : ℝ) (π : Df2Path d) (m : ℕ) : Prop extends DetBase c δ π m where
  evG : c.EvG π m
  evY : c.EvY π m
  evLQ : c.EvLQ π m
  evSDF : c.EvSDF π m
  evDQ : c.EvDQ π m

namespace DetBase

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-! ### The stopping time -/

open Classical in
theorem tau_lt (H : DetBase c δ π m) : c.tau π m < m := by
  unfold Df2Ctx.tau
  split_ifs with h
  · exact (Nat.find_spec h).1
  · have := H.hm1; omega

open Classical in
theorem cond_lt_tau (_H : DetBase c δ π m) : ∀ s < c.tau π m, c.Cond π s := by
  intro s hs
  unfold Df2Ctx.tau at hs
  split_ifs at hs with h
  · by_contra hc
    exact Nat.find_min h hs ⟨by have := (Nat.find_spec h).1; omega, hc⟩
  · by_contra hc
    exact h ⟨s, by omega, hc⟩

open Classical in
theorem tau_cases (_H : DetBase c δ π m) :
    (∀ s < m, c.Cond π s) ∧ c.tau π m = m - 1 ∨ ¬ c.Cond π (c.tau π m) := by
  unfold Df2Ctx.tau
  split_ifs with h
  · exact Or.inr (Nat.find_spec h).2
  · refine Or.inl ⟨fun s hs => ?_, rfl⟩
    by_contra hc
    exact h ⟨s, hs, hc⟩

/-! ### The parameters -/

theorem kap (H : DetBase c δ π m) : c.p.kap = 1 / 4 := by rw [H.hp]; rfl
theorem theta (H : DetBase c δ π m) : c.p.theta = 1 := by rw [H.hp]; rfl
theorem alpha (H : DetBase c δ π m) : c.p.alpha = 1 / 4 := by rw [H.hp]; rfl
theorem c1 (H : DetBase c δ π m) : c.p.c1 = 8 := by rw [H.hp]; rfl
theorem gam (H : DetBase c δ π m) : c.p.gam = 1 / 100 := by rw [H.hp]; rfl
theorem k0 (H : DetBase c δ π m) : c.p.k0 = ((1 - c.p.lam) ^ 2)⁻¹ := by rw [H.hp]; rfl
theorem sb (H : DetBase c δ π m) : c.p.sb = c.p.δe ^ 2 / (c.p.R * (c.p.R + 1)) := by rw [H.hp]; rfl
theorem Le (H : DetBase c δ π m) : c.p.Le = df2C0 * Real.log (1 / c.p.δe) := by rw [H.hp]; rfl
theorem sig2 (H : DetBase c δ π m) : c.p.sig2 = 1 / (8 * c.p.Le) := by rw [H.hp]; rfl

/-! ### The layer-1 statements -/

theorem dfi (H : DetBase c δ π m) : LemmaDFI := H.L1.1
theorem mon (H : DetBase c δ π m) : LemmaMON := H.L1.2.1
theorem inc2 (H : DetBase c δ π m) : PropINC2 := H.L1.2.2.1
theorem d2 (H : DetBase c δ π m) : LemmaD2 := H.L1.2.2.2.1
theorem ons2 (H : DetBase c δ π m) : LemmaONS2Core := H.L1.2.2.2.2.1
theorem zcore (H : DetBase c δ π m) : LemmaZCore := H.L1.2.2.2.2.2.1
theorem rowz (H : DetBase c δ π m) : Df2RowZ := H.L1.2.2.2.2.2.2.1
theorem shift (H : DetBase c δ π m) : PlayShift := H.L1.2.2.2.2.2.2.2.1
theorem carriers (H : DetBase c δ π m) : Df2Carriers := H.L1.2.2.2.2.2.2.2.2.2.2.2.1
theorem r1i (H : DetBase c δ π m) : LemmaR1i := H.L1.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem r1ii (H : DetBase c δ π m) : LemmaR1ii := H.L1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem r1iii (H : DetBase c δ π m) : LemmaR1iii := H.L1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem r1iv (H : DetBase c δ π m) : LemmaR1iv := H.L1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem r1v (H : DetBase c δ π m) : LemmaR1v := H.L1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end DetBase

end AdversarialBco.Poly
