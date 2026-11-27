/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementPoly
public import AdversarialBco.Poly.PgProc
public import AdversarialBco.Poly.Df2Oracle
public import AdversarialBco.Poly.Df2
public import AdversarialBco.Poly.MachVL
public import AdversarialBco.Poly.PgProcProof
public import AdversarialBco.Conj1Arith.Proc
public import AdversarialBco.Conj1Arith.ClampNS

@[expose] public section

/-!
# DF2-O: the parameters and the state of an epoch

The parameters of the learner DF2-O at `(d, n, δ)` (`df2oPar`), the state of an epoch (`Df2St`), the mode of the
learner before a round (`Df2Mode`), the start of an epoch (`df2Init`), the quadratic `df2Phi`, and the positioned
body cut by `B_R`, `K' = K~ ∩ B_R` (`df2Kp`), with `K_ε = (1 - ε) K'` (`df2Keps`). DF2-O runs DF2 on `K'`,
`K~ = posBody K μ_S A_S` the body in the position returned by Procedure PG, `R = 134 d (log (2d + 2))^{1/2}`, in the
positioned coordinates (`Fin d → ℝ` and matrices, as `Df2R1.lean`).

The state of an epoch (`Df2St`): `μ_t`, `P_t`, `Σ_t`, the factor `A_t`, the quadratic
`Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`, `Ĝ_{t-1}`, `l_{t-1}`, the ball `(ctr_t, r_t)`, and whether `t` is
the first round of its epoch (then `R⁻_t = K_ε`). `Df2Mode`: off (`o` played), guard (`μ_S` played), or a state.

## Parameters

`δ₁ = min (δ/3, e^{-14} (d n)^{-3})` (the confidence of the learner: Theorem POLY32-DF2 asks `δ ≤ e^{-14} (dn)^{-3}`,
and part A of Theorem POLY32-DF2-O spends `3 δ₁`), `δ_e = 4 δ₁/(5n)`, `L_e = C₀ log (1/δ_e)` (`C₀ = df2C0 = 36`),
`C_λ = 725`, `C_σ = 8`, `C_ε = 20 C_λ`, `λ = 1/(C_λ d L_e²)`, `η = d^{1/2}/(L_e n^{1/2})`, `σ² = 1/(C_σ L_e)`,
`ρ = 2 C_λ d² L_e³`, `ε = C_ε d^{3/2} L_e⁵/n^{1/2}`, `κ = 1/4`, `θ = 1`, `α = 1/4`, `c₁ = 8`, `γ = 1/100`,
`κ₀ = (1 - λ)^{-2}`, `R = 134 d (log (2d + 2))^{1/2}`, `j = ⌈log₂ (n R (R + 7)/(δ₁ ε))⌉`, `s_b = δ_e²/(R (R + 1))`.

## Junk values

`x / 0 = 0`, `Real.sqrt` of a negative number is `0`, `Real.log` and `Real.logb` read `|x|`, `⌈x⌉₊ = 0` for `x ≤ 0`.
For `d, n ≥ 1` and `0 < δ`: `δ₁, δ_e > 0`, `δ_e < 1`, so `L_e > 0` and `λ, η, σ², ρ, ε, R > 0`; `λ < 1`. `K_ε`
divides by `1 - ε`, read only when `ε ≤ 1/2`.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open AdversarialBco.RealRAM
open AdversarialBco.Conj1Arith (pgN clampNSRoutine)

variable {d : ℕ}

/-! ## Parameters -/

/-- The parameters of the learner at `(d, n, δ)`. -/
structure Df2OPar where
  δ1 : ℝ
  δe : ℝ
  Le : ℝ
  lam : ℝ
  eta : ℝ
  sig2 : ℝ
  rho : ℝ
  eps : ℝ
  kap : ℝ
  theta : ℝ
  alpha : ℝ
  c1 : ℝ
  gam : ℝ
  k0 : ℝ
  R : ℝ
  sb : ℝ
  j : ℕ

/-- `C_λ = 725`. -/
noncomputable def df2oClam : ℝ := 725

/-- The parameters of the module docstring. -/
noncomputable def df2oPar (d n : ℕ) (δ : ℝ) : Df2OPar :=
  let δ1 := min (δ / 3) (Real.exp (-14) / ((d : ℝ) * n) ^ 3)
  let δe := 4 * δ1 / (5 * n)
  let Le := df2C0 * Real.log (1 / δe)
  let lam := 1 / (df2oClam * d * Le ^ 2)
  let eps := 20 * df2oClam * (d * Real.sqrt d) * Le ^ 5 / Real.sqrt n
  let R := 134 * d * Real.sqrt (Real.log (2 * d + 2))
  { δ1 := δ1, δe := δe, Le := Le, lam := lam, eta := Real.sqrt d / (Le * Real.sqrt n), sig2 := 1 / (8 * Le),
    rho := 2 * df2oClam * d ^ 2 * Le ^ 3, eps := eps, kap := 1 / 4, theta := 1, alpha := 1 / 4, c1 := 8,
    gam := 1 / 100, k0 := ((1 - lam) ^ 2)⁻¹, R := R, sb := δe ^ 2 / (R * (R + 1)),
    j := ⌈Real.logb 2 (n * R * (R + 7) / (δ1 * eps))⌉₊ }

/-! ## The block of the positioning -/

/-- The confidence of each stage of PG, `δ₁/m`. -/
noncomputable def df2oPgDelta (r0 R0 δ1 : ℝ) : ℝ := δ1 / pgStages r0 R0

/-- The vectors of one repeat of stage `i`: `N_i + m_T n_{T,i}`. -/
noncomputable def df2oPgW (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ :=
  pgNs d (pgRhoStage d i) + pgMT δ' * pgNT d (pgRhoStage d i)

/-- The terms of stage `i`: `J (N_i + m_T n_{T,i}) d`. -/
noncomputable def df2oPgBlock (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ := pgJr δ' * df2oPgW d δ' i * d

/-- The first term of stage `i`. -/
noncomputable def df2oPgOff (d : ℕ) (δ' : ℝ) (i : ℕ) : ℕ := ∑ i' ∈ Finset.range i, df2oPgBlock d δ' i'

/-- `N₀`, the terms of the block of PG. -/
noncomputable def df2oN0 (d : ℕ) (r0 R0 δ1 : ℝ) : ℕ := df2oPgOff d (df2oPgDelta r0 R0 δ1) (pgStages r0 R0)

/-- The first term not read by the rounds `t < n`: `N₀ + n (d + 1)`. The spare entries of `ω` live from there on, and a
round `t ≥ n` reads them: a lemma on the positioning and the rounds holds below round `n` only. -/
noncomputable def df2oSpare (d n : ℕ) (r0 R0 δ1 : ℝ) : ℕ := df2oN0 d r0 R0 δ1 + n * (d + 1)

open Classical in
/-- The term of the stream that holds coordinate `c` of descent vector `k` of repeat `r` of stage `i`. -/
noncomputable def df2oIdxA (d n : ℕ) (r0 R0 δ1 : ℝ) (i r k : ℕ) (c : Fin d) : ℕ :=
  let δ' := df2oPgDelta r0 R0 δ1
  if i < pgStages r0 R0 ∧ r < pgJr δ' ∧ k < pgNs d (pgRhoStage d i) then
    df2oPgOff d δ' i + (r * df2oPgW d δ' i + k) * d + c
  else df2oSpare d n r0 R0 δ1 + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c)

open Classical in
/-- The term of the stream that holds coordinate `c` of test vector `k` of verdict `v` of repeat `r` of stage `i`. -/
noncomputable def df2oIdxT (d n : ℕ) (r0 R0 δ1 : ℝ) (i r v k : ℕ) (c : Fin d) : ℕ :=
  let δ' := df2oPgDelta r0 R0 δ1
  if i < pgStages r0 R0 ∧ r < pgJr δ' ∧ v < pgMT δ' ∧ k < pgNT d (pgRhoStage d i) then
    df2oPgOff d δ' i + (r * df2oPgW d δ' i + pgNs d (pgRhoStage d i) + v * pgNT d (pgRhoStage d i) + k) * d + c
  else df2oSpare d n r0 R0 δ1 + Nat.pair (Nat.pair i r) (Nat.pair (2 * Nat.pair v k + 1) c)

/-- The stream of PG read off the Gaussian stream. -/
noncomputable def df2oOmega (d n : ℕ) (r0 R0 δ1 : ℝ) (gs : ℕ → ℝ) : ℕ → ℕ → PgRound d :=
  fun i r => (fun k => WithLp.toLp 2 fun c => gs (df2oIdxA d n r0 R0 δ1 i r k c),
    fun v k => WithLp.toLp 2 fun c => gs (df2oIdxT d n r0 R0 δ1 i r v k c))

/-- The position `(μ_S, A_S)` returned by PG, else `none`. -/
noncomputable def df2oPos (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Option (PgSp d) :=
  pgN clampNSRoutine d w.K r0 R0 (df2oPar d n δ).δ1 (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 w.gs)

/-- `ξ_t`, the `d` terms of round `t`. -/
def df2oXi (N0 : ℕ) (gs : ℕ → ℝ) (t : ℕ) : Fin d → ℝ := fun c => gs (N0 + t * (d + 1) + c)

/-- The dither `ζ_t = g/2`, `g` the last term of round `t`. -/
noncomputable def df2oZeta (d N0 : ℕ) (gs : ℕ → ℝ) (t : ℕ) : ℝ := gs (N0 + t * (d + 1) + d) / 2

/-! ## One round -/

/-- The state of an epoch before round `t`. -/
structure Df2St (d : ℕ) where
  /-- `t` is the first round of its epoch. -/
  first : Bool
  mu : Fin d → ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  S : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  b : Fin d → ℝ
  k : ℝ
  G : Fin d → ℝ
  l : ℝ
  ctr : Fin d → ℝ
  r : ℝ

/-- The mode of the learner before a round. -/
inductive Df2Mode (d : ℕ)
  /-- `o = 0` is played: no position, the regime `ε > 1/2`, or a failed play test. -/
  | off
  /-- The guard has acted: `S⁻¹(0) = μ_S` is played after the play test. -/
  | guard
  /-- A round of DF2 from this state. -/
  | run (st : Df2St d)

/-- The start of an epoch: `μ₁ = 0`, `P₁ = I/σ²`, `Σ₁ = σ² I`, `A₁ = σ I`, `Φ₀ = |·|²/(2σ²)`, `Ĝ₀ = 0`, `l₀ = 0`,
the ball `(0, 1 - ε)`. -/
noncomputable def df2Init (p : Df2OPar) (d : ℕ) : Df2St d :=
  ⟨true, 0, p.sig2⁻¹ • 1, p.sig2 • 1, Real.sqrt p.sig2 • 1, 0, 0, 0, 0, 0, 1 - p.eps⟩

/-- `Φ_{t-1}(y) = ½ yᵀ P_t y - b_{t-1}ᵀ y + k_{t-1}`. -/
noncomputable def df2Phi (P : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (k : ℝ) (y : Fin d → ℝ) : ℝ :=
  1 / 2 * (y ⬝ᵥ (P *ᵥ y)) - b ⬝ᵥ y + k

/-- The positioned body cut by `B_R`, `K' = K~ ∩ B_R`, in `E d`. -/
def df2Kp (K : Set (E d)) (Ps : PgSp d) (R : ℝ) : Set (E d) := {y | pgMu Ps + pgOp Ps y ∈ K ∧ ‖y‖ ≤ R}

/-- `K_ε = (1 - ε) K'`, in the coordinates `Fin d → ℝ`: `y/(1 - ε) ∈ K'`. -/
noncomputable def df2Keps (K : Set (E d)) (Ps : PgSp d) (R eps : ℝ) : Set (Fin d → ℝ) :=
  {y | WithLp.toLp 2 ((1 - eps)⁻¹ • y) ∈ df2Kp K Ps R}

open Classical in
/-- The rest of a round of DF2 after the observation `Y_t`, from the state `st`, the draw `ξ_t` and `w_t = A_t ξ_t`:
the scalars and (T1'); the updates and (T1') on the traces; `z_t` and (T2z); the test call and (T4); the restart test;
the ball, (T2), line `μ` and (T4). -/
noncomputable def df2Next (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) :
    Df2Mode d :=
  let u := st.P *ᵥ w
  let g := (Y / (1 - p.lam)) • u
  let c := p.eta * p.kap * p.lam * p.k0 * Y
  let a := 1 - c
  let q := a + c * (ξ ⬝ᵥ ξ)
  if a ≤ 0 ∨ q ≤ 0 then .guard else
  let P' := a • st.P + c • vecMulVec u u
  let S' := a⁻¹ • (st.S - (c / q) • vecMulVec w w)
  let c' := c / q / (1 + Real.sqrt (a / q))
  let A' := (Real.sqrt a)⁻¹ • (st.A - c' • vecMulVec w ξ)
  let b' := st.b + c • ((u ⬝ᵥ st.mu) • u - st.P *ᵥ st.mu)
  let k' := st.k + c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - st.mu ⬝ᵥ (st.P *ᵥ st.mu))
  let G' := st.G + g
  let l' := st.l + g ⬝ᵥ st.mu
  if d / p.δe < P'.trace ∨ d / p.δe < S'.trace then .guard else
  let z := S' *ᵥ (b' - (p.eta / 2) • G')
  if p.R / p.δe ^ 3 < oNorm z then .guard else
  let Rm : Set (Fin d → ℝ) :=
    if st.first then Keps else {y | y ∈ Keps ∧ df2Phi st.P st.b st.k y ≤ (p.c1 - p.gam) * p.rho}
  match apCall Rm st.ctr st.r p.R P' z (min 1 (p.alpha * p.rho / 2)) with
  | none => .guard
  | some pt =>
    if p.eta * (l' - G' ⬝ᵥ pt) - 2 * df2Phi P' b' k' pt ≤ -(p.theta * p.rho) then .run (df2Init p d) else
    let ctr' := (1 - p.sb) • pt
    let r' := p.sb * (1 - p.eps)
    let wmu := st.mu - (p.eta * Y / ((1 - p.lam) * q)) • w
    if p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm wmu then .guard else
    let Rp : Set (Fin d → ℝ) := {y | y ∈ Keps ∧ df2Phi P' b' k' y ≤ p.c1 * p.rho}
    match apCall Rp ctr' r' p.R P' wmu (1 / (16 * n ^ 2 * max 1 (4 * p.R ^ 2 * P'.trace))) with
    | none => .guard
    | some mu' => .run ⟨false, mu', P', S', A', b', k', G', l', ctr', r'⟩

open Classical in
/-- One round: the point played and the mode after it, from the position `Ps`, the loss `ft`, the noise `nt`, the
draws `ξ_t`, `ζ_t`, and the mode before it. In a round of DF2: the sample `X_t = μ_t + (1 - λ) A_t ξ_t`, the gauge
`pt(X_t) = max (1, π̃(X_t)/(1 - ε))`, the point `S⁻¹(X_t/pt(X_t)) = μ_S + A_S (X_t/pt(X_t))`, the play test, the
observation `O_t = f_t(x) + ε_t` and `Y_t = pt(X_t) (O_t + ζ_t)/2 + 2 (pt(X_t) - 1)/ε`, then `df2Next`. -/
noncomputable def df2Round (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) : Df2Mode d → E d × Df2Mode d
  | .off => (0, .off)
  | .guard => if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, .guard) else (0, .off)
  | .run st =>
    let w := st.A *ᵥ ξ
    let X := st.mu + (1 - p.lam) • w
    let pt := max 1 (piTilde (df2Kp K Ps p.R) p.R p.j (WithLp.toLp 2 X) / (1 - p.eps))
    let x := pgMu Ps + pgOp Ps (WithLp.toLp 2 (pt⁻¹ • X))
    if x ∈ K then
      (x, df2Next p n (df2Keps K Ps p.R p.eps) st ξ w (pt * (ft x + nt + ζ) / 2 + 2 * (pt - 1) / p.eps))
    else (0, .off)

/-! ## The run -/

open Classical in
/-- The mode before round `0`: off if PG returns no position or `ε > 1/2`, else the start of an epoch. -/
noncomputable def df2oMode0 (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) : Df2Mode d :=
  match df2oPos d n r0 R0 δ w with
  | none => .off
  | some _ => if 1 / 2 < (df2oPar d n δ).eps then .off else .run (df2Init (df2oPar d n δ) d)

/-- Round `t` of the learner from the mode `m`. -/
noncomputable def df2oRoundAt (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2Round (df2oPar d n δ) n w.K ((df2oPos d n r0 R0 δ w).getD 0) (w.f t) (w.noise t)
    (df2oXi (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) (df2oZeta d (df2oN0 d r0 R0 (df2oPar d n δ).δ1) w.gs t) m

/-- The mode before round `a + s` of the run started in the mode `m` before round `a`. -/
noncomputable def df2oFrom (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (a : ℕ) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (df2oRoundAt d n r0 R0 δ w (a + s) (df2oFrom d n r0 R0 δ w a m s)).2

/-- The mode of the learner before round `t`. -/
noncomputable def df2oMode (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : Df2Mode d :=
  df2oFrom d n r0 R0 δ w 0 (df2oMode0 d n r0 R0 δ w) t

/-- The point played by the learner in round `t`. -/
noncomputable def df2oPlay (d n : ℕ) (r0 R0 δ : ℝ) (w : World d) (t : ℕ) : E d :=
  (df2oRoundAt d n r0 R0 δ w t (df2oMode d n r0 R0 δ w t)).1

/-- One round plays `0` or a point that passed the membership test of `K`. -/
theorem df2Round_mem (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (m : Df2Mode d) :
    (df2Round p n K Ps ft nt ξ ζ m).1 = 0 ∨ (df2Round p n K Ps ft nt ξ ζ m).1 ∈ K := by
  cases m with
  | off => exact Or.inl rfl
  | guard =>
    unfold df2Round
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl
  | run st =>
    unfold df2Round
    simp only
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl

/-- Every point played is in `K`, on every world whose body contains the ball `B(0, r₀)`, `r₀ > 0`. -/
theorem df2oPlay_mem (d n : ℕ) (r0 R0 δ : ℝ) (hr0 : 0 < r0) (K : Set (E d)) (hball : Metric.closedBall 0 r0 ⊆ K)
    (f : ℕ → E d → ℝ) (gs noise : ℕ → ℝ) (t : ℕ) : df2oPlay d n r0 R0 δ ⟨K, f, noise, gs⟩ t ∈ K := by
  have h0 : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self hr0.le)
  unfold df2oPlay df2oRoundAt
  rcases df2Round_mem (df2oPar d n δ) n K _ (f t) (noise t) _ _ _ with h | h
  · simp only at h ⊢; rw [h]; exact h0
  · exact h

end AdversarialBco.Poly
