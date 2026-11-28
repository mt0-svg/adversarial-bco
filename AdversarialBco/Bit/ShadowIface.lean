/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.WorldAzAd
public import AdversarialBco.Poly.Df2WorldVE
public import AdversarialBco.StatementBitRAM

@[expose] public section

/-!
# The coupling layer: the coupled world, the checked advice routine, the clauses of the coupling

The paper's section on the coupling: the world layer (O1) of the reference, the pair layout of (W0d).

The bit learner BL is coupled to an exact reference P°: the epochs of D0 with the checked advice routine `apAdv` on
BL's position, run on the coupled world `WΩ = (gs, noise)` under `μ* = gaussStream ⊗ ν`.

This file holds the definitions the layer shares: the indices of the coupled world (`cIdx`, `idxC`, the draws `ξc`,
`ξg` and the coupling coordinates `zc`), the checked advice routine (`advPick`, `advOK`, `apAdv`), the two clauses of
the coupling, (O2-L) `CoupLaw` and (O2-C) `CoupTV` with the bound `tvB` of the coupling lemma, the round `cRoundA` of
P°, the regime `Regime`, the regret bound `bReg` of D0 and the failure budget `deltaRef` of P°.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2
open AdversarialBco.Poly.Conj1 (fL lamAt)

variable {d : ℕ}

/-! ## The coupled world -/

/-- The index of role `c` in the block of round `t` on the Gaussian stream: blocks of `d + 5` even indices. Roles:
`c < d` the draw `ξ_t c`; `d` the padding of the draws (BL's sampler reads the draws in pairs, (W0d)); `d + 1` the
dither source `Z̃_t`; `d + 2` its padding; `d + 3`, `d + 4` the coupling coordinates `G^U_t`, `G^W_t`, read by the
coupling only. The odd indices are BL's other coins (its position under (POS-P)). -/
def cIdx (d t c : ℕ) : ℕ := 2 * (t * (d + 5) + c)

/-- The indices known before round `t`: the odd ones and the blocks of the rounds `< t`. -/
def idxC (d t : ℕ) : Set ℕ := {i | i % 2 = 1} ∪ {i | i < 2 * (t * (d + 5))}

/-- The sigma-field before round `t`: the terms of the Gaussian stream in `idxC d t` and the noise before `t`. -/
abbrev cSeq (d t : ℕ) : MeasurableSpace WΩ :=
  (⨆ i ∈ idxC d t, gσ i) ⊔ MeasurableSpace.comap Prod.snd (pastNoise t)

theorem idxC_mono (d : ℕ) {s t : ℕ} (h : s ≤ t) : idxC d s ⊆ idxC d t := by
  rintro i (hi | hi)
  · exact Or.inl hi
  · exact Or.inr (lt_of_lt_of_le hi (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (d + 5) h)))

theorem cSeq_mono (d : ℕ) {s t : ℕ} (h : s ≤ t) : cSeq d s ≤ cSeq d t := by
  apply sup_le_sup
  · exact iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ idxC d t) => gσ i) i (idxC_mono d h hi)
  · exact MeasurableSpace.comap_mono (pastNoise_mono h)

theorem cSeq_le (d t : ℕ) : cSeq d t ≤ (inferInstance : MeasurableSpace WΩ) := by
  apply sup_le
  · exact iSup₂_le fun i _ => gσ_le i
  · exact (MeasurableSpace.comap_mono (pastNoise_le t)).trans measurable_snd.comap_le

/-- The filtration of the coupled world. -/
def cσ (d : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace WΩ) where
  seq := cSeq d
  mono' _ _ h := cSeq_mono d h
  le' := cSeq_le d

/-- The draw of round `t`. -/
def ξc (d t : ℕ) (ω : WΩ) : Fin d → ℝ := fun c => ω.1 (cIdx d t c)

/-- The draw group of round `t`: the draws and their padding (roles `c ≤ d`). -/
def ξg (d t : ℕ) (ω : WΩ) : Fin (d + 1) → ℝ := fun c => ω.1 (cIdx d t c)

/-- The coordinates of the coupling in round `t`: `(Z̃_t, G^U_t, G^W_t)` (roles `d + 1`, `d + 3`, `d + 4`). -/
def zc (d t : ℕ) (ω : WΩ) : Fin 3 → ℝ :=
  ![ω.1 (cIdx d t (d + 1)), ω.1 (cIdx d t (d + 3)), ω.1 (cIdx d t (d + 4))]

/-- The standard Gaussian law on `Fin k → ℝ`. -/
noncomputable abbrev gaussK (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1

/-! ## The losses on the coupled layout -/

/-- A loss process for the filtration `𝒢`: the loss of round `t` on the world `ω` is `L t (lam t ω)`, its parameter
known before round `t`. For the bit statement at a fixed seed, `lam t ω` is BL's history before round `t`. -/
structure Df2LossProcF (d n : ℕ) (K : Set (E d)) (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace WΩ)) where
  /-- The parameter space of the losses. -/
  Λ : Type
  /-- Its sigma-field. -/
  [mΛ : MeasurableSpace Λ]
  /-- The loss of round `t` at the parameter `l`. -/
  L : ℕ → Λ → E d → ℝ
  /-- The parameter of round `t` on the world `ω`. -/
  lam : ℕ → WΩ → Λ
  /-- Every loss of the rounds `t < n` is admissible. -/
  adm : ∀ t < n, ∀ l, AdmLoss K (L t l)
  /-- At each point of the interior of `K`, the loss of a round `t < n` is measurable in the parameter. -/
  meas : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y
  /-- The parameter of a round `t < n` is known before round `t`. -/
  lam_meas : ∀ t < n, Measurable[𝒢 t] (lam t)

attribute [instance] Df2LossProcF.mΛ

/-! ## The checked advice routine -/

/-- An advice: a candidate for the test call and one for line μ. -/
abbrev Adv (d : ℕ) : Type := (Fin d → ℝ) × (Fin d → ℝ)

/-- The candidate of a call at accuracy `e`: the test call has `e ≥ 1/2`, line μ has `e ≤ 1/16` in the regime. -/
noncomputable def advPick (v : Adv d) (e : ℝ) : Fin d → ℝ := if 1 / 2 ≤ e then v.1 else v.2

/-- The test of a candidate `x`: in `Q`, of norm at most `R`, within `e` of `ellF P w` at every rational point of
`Q`. -/
def advOK (Q : Set (Fin d → ℝ)) (R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (e : ℝ) (x : Fin d → ℝ) :
    Prop :=
  x ∈ Q ∧ oNorm x ≤ R ∧ ∀ q : Fin d → ℚ, (fun i => (q i : ℝ)) ∈ Q → ellF P w x ≤ ellF P w (fun i => (q i : ℝ)) + e

open Classical in
/-- The checked advice routine: the candidate if it passes the test, else the proved routine `apCall`. -/
noncomputable def apAdv (v : Adv d) : ApFun d := fun Q a0 r R P w e =>
  if advOK Q R P w e (advPick v e) then some (advPick v e) else apCall Q a0 r R P w e

/-! ## The coupling (O2) -/

/-- (O2-L), the law clause of the coupling: `Coup m r z` is the coupled dither at the
shift `(m, r)` from the three coordinates `z = (Z̃, G^U, G^W)`; it is jointly Borel, and for every fixed `(m, r)` its
law under three standard Gaussians is `N(0, 1/4)`, the law of `Z/2`. -/
structure CoupLaw (Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ) : Prop where
  meas : Measurable fun x : ℝ × ℝ × (Fin 3 → ℝ) => Coup x.1 x.2.1 x.2.2
  law : ∀ m r, (gaussK 3).map (Coup m r) = (gaussianReal 0 1).map (· / 2)

/-- The bound of the coupling lemma: `TV(N(m, r²/4), N(0, 1/4)) ≤ (|r - 1| + |m|)/min(r, 1)`. -/
noncomputable def tvB (m r : ℝ) : ℝ := (|r - 1| + |m|) / min r 1

/-- (O2-C), the coupling clause: at `r > 0` the coupled dither differs from `m + r Z̃/2` with probability at most the
bound of the coupling lemma. -/
def CoupTV (Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ m r, 0 < r → gaussK 3 {z | Coup m r z ≠ m + r * z 0 / 2} ≤ ENNReal.ofReal (tvB m r)

/-! ## BL's run as the coupling layer reads it, and the reference P° -/

/-- The data of the coupling layer at the horizon `n` on the body `K`. -/
structure Run (d n : ℕ) (K : Set (E d)) where
  /-- The losses, chosen against BL. -/
  F : Df2LossProcF d n K (cσ d)
  /-- BL's position `S'` (POS). -/
  pos : WΩ → PgSp d
  /-- The shift `(m_t, r_t)` of round `t` at P°'s mode before round `t` (the section on the coupling:
  `r = pt'/pt°`, `m = (r - 1) ε_t + 2 (ext'(X'_t) - ext(X°_t))/pt°` when the mode is `.run`). -/
  sh : ℕ → WΩ → Df2Mode d → ℝ × ℝ
  /-- The advice of round `t` at P°'s mode before round `t` (BL's state after round `t` and the selection; P°'s
  dither of round `t` is a function of the world and of that mode). -/
  adv : ℕ → WΩ → Df2Mode d → Adv d
  /-- BL's play of round `t`, in the coordinates of `K`. -/
  play : ℕ → WΩ → E d
  /-- BL's soundness event (the lemma of the draws): `E_bits ∩ Z_n`, the worlds at
  which BL's draws of the rounds `< n` are within their error bounds (`E_bits`, an event of the Gaussian coordinates)
  and the noise of the rounds `< n` is `0` (`Z_n`, the noiseless worlds). -/
  bits : Set WΩ
  /-- The coupling. -/
  Coup : ℝ → ℝ → (Fin 3 → ℝ) → ℝ

/-- The round of P° at the position `q` with the routine `ap`: D0's round at the exact gauge of `kTh`. -/
noncomputable def cRoundA (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa (df2oPar d n δ) n K q (gauge (kTh n δ K q)) ap ft nt ξ ζ m

namespace Run

variable {n : ℕ} {K : Set (E d)}

/-- The losses on the world `ω`. -/
def loss (B : Run d n K) (ω : WΩ) : ℕ → E d → ℝ := fun t => B.F.L t (B.F.lam t ω)

open Classical in
/-- The loss that P°'s round `t` reads: the loss of the round on the interior of `K` (`fL`) for `t < n`, `0` past the
horizon (the run past `n` is read only by the setting (E) of the noise, which needs it measurable). -/
noncomputable def lossR (B : Run d n K) (t : ℕ) (ω : WΩ) : E d → ℝ := if t < n then fL K B.F.L t (B.F.lam t ω) else 0

/-- The coupled dither of round `t` at P°'s mode `m` before round `t`. -/
noncomputable def zeta (B : Run d n K) (t : ℕ) (ω : WΩ) (m : Df2Mode d) : ℝ :=
  B.Coup (B.sh t ω m).1 (B.sh t ω m).2 (zc d t ω)

/-- The mode of P° before round `t` ((O1-RUN)). -/
noncomputable def mode (B : Run d n K) (δ : ℝ) : ℕ → WΩ → Df2Mode d
  | 0, _ => .run (df2Init (df2oPar d n δ) d)
  | t + 1, ω => (cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (mode B δ t ω))) (B.lossR t ω) (ω.2 t)
      (ξc d t ω) (B.zeta t ω (mode B δ t ω)) (mode B δ t ω)).2

/-- The play of P° in round `t`. -/
noncomputable def refPlay (B : Run d n K) (δ : ℝ) (t : ℕ) (ω : WΩ) : E d :=
  (cRoundA n δ K (B.pos ω) (apAdv (B.adv t ω (B.mode δ t ω))) (B.lossR t ω) (ω.2 t) (ξc d t ω)
    (B.zeta t ω (B.mode δ t ω)) (B.mode δ t ω)).1

/-- The noise of P°'s path in round `t`: `(ε_t + ζ*_t)/2`. -/
noncomputable def eRef (B : Run d n K) (δ : ℝ) (t : ℕ) (ω : WΩ) : ℝ := (ω.2 t + B.zeta t ω (B.mode δ t ω)) / 2

/-- The context of P°'s virtual epoch started before round `a`: the body at BL's position, the routine of round `s`
the checked advice of round `a + s`. -/
noncomputable def ctx (B : Run d n K) (δ : ℝ) (a : ℕ) (ω : WΩ) : Df2Ctx d :=
  df2CtxAtF d n δ (kTh n δ K (B.pos ω)) fun s => apAdv (B.adv (a + s) ω (B.mode δ (a + s) ω))

/-- The path of P°'s virtual epoch started before round `a`. -/
noncomputable def path (B : Run d n K) (δ : ℝ) (a : ℕ) (ω : WΩ) : Df2Path d :=
  ⟨fun s => gTh n δ K (fun t => B.F.L t (lamAt n B.F.lam a s ω)) a s (B.pos ω), fun s => B.eRef δ (a + s) ω,
    fun s => ξc d (a + s) ω⟩

/-- The case of the analysis: BL's position is good. -/
def Case (B : Run d n K) (δ : ℝ) (ω : WΩ) : Prop := PgGood d K (df2oPar d n δ).R (some (B.pos ω))

/-- The mean loss of round `t` of P° given the past (the play does not read the routine, the noise or the dither). -/
noncomputable def mean (B : Run d n K) (δ : ℝ) (t : ℕ) (ω : WΩ) : ℝ :=
  ∫ z, B.loss ω t ((cRoundA n δ K (B.pos ω) apCall (B.lossR t ω) 0 z 0 (B.mode δ t ω)).1) ∂gaussK d

/-- The Azuma event of P°. -/
def Az (B : Run d n K) (δ : ℝ) (ω : WΩ) : Prop :=
  ∑ t ∈ Finset.range n, B.loss ω t (B.refPlay δ t ω) ≤
    ∑ t ∈ Finset.range n, B.mean δ t ω + Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe))

/-- `Ω_ref`: every virtual epoch of P° meets the five events of DET at its horizon `n - a`, and the Azuma event
holds. -/
def Good (B : Run d n K) (δ : ℝ) (ω : WΩ) : Prop :=
  (∀ a < n, (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) ∧ B.Az δ ω

/-- The shift of round `t` on P°'s run. -/
noncomputable def shR (B : Run d n K) (δ : ℝ) (t : ℕ) (ω : WΩ) : ℝ × ℝ := B.sh t ω (B.mode δ t ω)

end Run

/-- The regime: `d, n ≥ 1`, `δ ∈ (0, 1)`, `ε ≤ 1/2` at `df2oPar`. -/
def Regime (d n : ℕ) (δ : ℝ) : Prop := 1 ≤ d ∧ 1 ≤ n ∧ 0 < δ ∧ δ < 1 ∧ (df2oPar d n δ).eps ≤ 1 / 2

/-- The regret bound of D0, `B_n = 2 ρ/η + n ε + (2 n log(7/δe))^{1/2}`. -/
noncomputable def bReg (d n : ℕ) (δ : ℝ) : ℝ :=
  2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) + n * (df2oPar d n δ).eps +
    Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe))

/-- `δ_ref = n (149/168) δe + δe/7`. -/
noncomputable def deltaRef (d n : ℕ) (δ : ℝ) : ℝ :=
  n * (149 / 168 * (df2oPar d n δ).δe) + (df2oPar d n δ).δe / 7

/-! ## The hypotheses, one per open item -/

/-- (W0), the law clause: the digit map carries the Gaussian stream to the fair coins. -/
def W0Law (β : (ℕ → ℝ) → ℕ → Bool) : Prop := Measurable β ∧ gaussStream.map β = BitRAM.coinStream

end AdversarialBco.Bit.Cpl
