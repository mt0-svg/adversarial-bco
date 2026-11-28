/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmRec
public import AdversarialBco.Unified.ProgOBL
public import AdversarialBco.Unified.BLOGeom
public import AdversarialBco.Conj1Exp.Bound

@[expose] public section

/-!
# The named hypotheses of BL-O's assembly

The hypotheses that the assembly of BL-O (Unified/BLOSpec.lean) leaves named, one `Prop` each, and the arithmetic of
their budgets:

* the W-hypotheses of SHADOW on BL-O's record `recO` (Unified/AsmRec.lean) on the extension `extO` of every
  environment with BL-O's windows, in the case `RunCaseO`, with their budgets in `δ`: `PosRecO` (`PosHypW` with
  `δpos ≤ δ/4`), `MeasRecO` (`BLMeasW`), `BitsRecO` (`BitsHypW` with `δbits ≤ δ/8`);
* the measurability of the regret on the environment's space (UNI-MEAS, `RegMeasU`);
* the arithmetic of the threshold at BL-O's confidence (`ThrO`).

The budget of the bad event is `δpos + δ_ref + δbits + n (κ0 + κ1) ≤ δ/4 + δ/2 + δ/8 + δ/8` (`budget_le_delta`), and
`B_n + 1 ≤ 10^29 d^{3/2} √n log(2dn/δ)^5` (`ThrO`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (toE State)
open AdversarialBco.BitRAMO (InstrO WorldO playedO)
open AdversarialBco.RealRAM (regretPts)

/-! ## The named hypotheses -/

/-- **(POS) for BL-O's record**: on every input in the run case and every environment with BL-O's windows, the
position of the record is known before round `0` and good off an event of probability at most `δpos ≤ δ/4`. -/
def PosRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δpos : ℝ, 0 ≤ δpos ∧ δpos ≤ (δ : ℝ) / 4 ∧
        PosHypW (recO n δ r0 R0 a orc h hI.convex) (dBL d n δ) δpos

/-- **(O4-M) for BL-O's record**: the shift of round `t` is measurable at `F*_t` jointly with P°'s mode, the advice
at `𝓕 (t + 1)`. -/
def MeasRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      BLMeasW (recO n δ r0 R0 a orc h hI.convex)

/-- **(O4), the bit clause for BL-O's record**: the soundness event `E_bits ∩ NoClip` fails with probability at most
`δbits ≤ δ/8`. -/
def BitsRecO : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseO d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise),
      ∃ δbits : ℝ, 0 ≤ δbits ∧ δbits ≤ (δ : ℝ) / 8 ∧ BitsHypW (recO n δ r0 R0 a orc h hI.convex) δbits

/-- **UNI-MEAS**: on the environment's own space, the regret of a program whose plays of the rounds `t < n` lie in `K`
is measurable. -/
def RegMeasU : Prop :=
  ∀ (P : List InstrO) {d n : ℕ} (K : Set (E d)), (interior K).Nonempty → ∀ (s0 : State d), s0.rounds = 0 →
    ∀ (orc : (Fin d → ℚ) → ℕ → Bool) {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool}
      {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {D D' : ℕ → ℕ}, NoisyAdv K n D D' μ coin loss noise →
      (∀ ω, ∀ t < n, playedO P (envWorld orc coin loss noise ω) s0 t ∈ K) →
      Measurable fun ω => regretU P K n s0 (envWorld orc coin loss noise ω)

/-- The threshold of the theorem, `10^29 d^{3/2} √n log(2dn/δ)^5`. -/
noncomputable def thrU (d n : ℕ) (δ : ℚ) : ℝ :=
  10 ^ 29 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / (δ : ℝ)) ^ 5

/-- **The arithmetic at BL-O's confidence** (UNI-DELTA, Lemma thr at `δ`): `0 < δ_BL < 1`, `δ_ref ≤ δ/2`, in the
run case `B_n + 1 ≤ thrU`, off it `n ≤ thrU`. -/
def ThrO : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 →
    0 < dBL d n δ ∧ dBL d n δ < 1 ∧ deltaRef d n (dBL d n δ) ≤ (δ : ℝ) / 2 ∧
      (RunCaseO d n δ → bReg d n (dBL d n δ) + 1 ≤ thrU d n δ) ∧ (¬ RunCaseO d n δ → (n : ℝ) ≤ thrU d n δ)

/-! ## The regret clauses -/

/-- The interior of `K` holds the centre `a`. -/
theorem interior_nonempty {d n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) : (interior K).Nonempty := by
  have hr : (0 : ℝ) < r0 := by exact_mod_cast hI.hr0
  exact ⟨toE a, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr)
    (Metric.ball_subset_closedBall.trans hI.ball_in))⟩

/-- The budget of the bad event: `δpos + δ_ref + δbits + n (κ0 + κ1) ≤ δ`. -/
theorem budget_le_delta {δ δpos δr δbits nk : ℝ} (hp : δpos ≤ δ / 4) (hr : δr ≤ δ / 2) (hb : δbits ≤ δ / 8)
    (hk : nk ≤ δ / 8) : δpos + δr + δbits + nk ≤ δ := by linarith

end AdversarialBco.Unified.Asm
