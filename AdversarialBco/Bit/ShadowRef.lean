/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowAz
public import AdversarialBco.Bit.ShadowWDet
public import AdversarialBco.Bit.ShadowStep2

@[expose] public section

/-!
# (O1) and SHADOW from W-EV

* `WEvProp` (W-EV): the five budgets G, Y, LQ, S-DF, DQ of the virtual epoch of P° started before each round `a < n`,
  on `Case`, at `3/7, 1/7, 1/21, 1/7, 1/8` of `δe`;
* `Run.five_bound`: on `Case`, the epoch started at `a` misses one of its five events with probability at most
  `(149/168) δe` (`union5`);
* `Run.refProb`: `Case` off `Ω_ref` has probability at most `δ_ref = n (149/168) δe + δe/7` (W-AZ for the Azuma
  event);
* `refProp_of_wev : WEvProp → RefProp`, with W-DET (`Run.wdet`) on the checked advice routine (`apAdv_spec`);
* `shadowProp_of_wev : WEvProp → ShadowProp`, with Step 2 (`coupStepProp_holds`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-- The five events of the virtual epoch of P° started before round `a`, at its horizon `n - a`. -/
def Run.Five {n : ℕ} {K : Set (E d)} (B : Run d n K) (δ : ℝ) (a : ℕ) (ω : WΩ) : Prop :=
  (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a) ∧ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a) ∧
    (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)

/-- (W-EV): on the coupled world and on `Case`, the virtual epoch of P° started before
round `a < n` misses G with probability at most `3 δe/7`, and on G misses Y, LQ, S-DF, DQ with probabilities at most
`δe/7`, `δe/21`, `δe/7`, `δe/8`. -/
def WEvProp : Prop :=
  ∀ (d n : ℕ) (δ : ℝ) (K : Set (E d)) (ν : Measure (ℕ → ℝ)) (B : Run d n K),
    Regime d n δ → IsClosed K → Convex ℝ K → NoiseOK ν → Measurable[cσ d 0] B.pos → CoupLaw B.Coup → BLMeas B →
    ∀ a < n,
      μs ν {ω | B.Case δ ω ∧ ¬ (B.ctx δ a ω).EvG (B.path δ a ω) (n - a)} ≤
          ENNReal.ofReal (3 / 7 * (df2oPar d n δ).δe) ∧
        μs ν {ω | B.Case δ ω ∧ (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧
          ¬ (B.ctx δ a ω).EvY (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) ∧
        μs ν {ω | B.Case δ ω ∧ (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧
          ¬ (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (1 / 21 * (df2oPar d n δ).δe) ∧
        μs ν {ω | B.Case δ ω ∧ (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧
          ¬ (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) ∧
        μs ν {ω | B.Case δ ω ∧ (B.ctx δ a ω).EvG (B.path δ a ω) (n - a) ∧
          ¬ (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)} ≤ ENNReal.ofReal (1 / 8 * (df2oPar d n δ).δe)

namespace Run

variable {n : ℕ} {K : Set (E d)} {B : Run d n K} {δ : ℝ} {ν : Measure (ℕ → ℝ)}

section

variable (hW : WEvProp) (hreg : Regime d n δ) (hKc : IsClosed K) (hKconv : Convex ℝ K) (hν : NoiseOK ν)
  (hpos : Measurable[cσ d 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeas B)
include hW hreg hKc hKconv hν hpos hC hB

/-- On `Case`, the epoch started before round `a < n` misses one of its five events with probability at most
`(149/168) δe`. -/
theorem five_bound {a : ℕ} (ha : a < n) :
    μs ν {ω | B.Case δ ω ∧ ¬ B.Five δ a ω} ≤ ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) := by
  obtain ⟨hG, hY, hLQ, hSDF, hDQ⟩ := hW d n δ K ν B hreg hKc hKconv hν hpos hC hB a ha
  obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
  have hde : 0 ≤ (df2oPar d n δ).δe := (rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  refine le_trans (measure_mono fun ω hω => ?_) (union5 (μs ν)
    (fun ω => B.Case δ ω → (B.ctx δ a ω).EvG (B.path δ a ω) (n - a))
    (fun ω => B.Case δ ω → (B.ctx δ a ω).EvY (B.path δ a ω) (n - a))
    (fun ω => B.Case δ ω → (B.ctx δ a ω).EvLQ (B.path δ a ω) (n - a))
    (fun ω => B.Case δ ω → (B.ctx δ a ω).EvSDF (B.path δ a ω) (n - a))
    (fun ω => B.Case δ ω → (B.ctx δ a ω).EvDQ (B.path δ a ω) (n - a)) _ hde
    ((measure_mono fun ω hω => ?_).trans hG) ((measure_mono fun ω hω => ?_).trans hY)
    ((measure_mono fun ω hω => ?_).trans hLQ) ((measure_mono fun ω hω => ?_).trans hSDF)
    ((measure_mono fun ω hω => ?_).trans hDQ))
  · obtain ⟨hc, hnot⟩ := hω
    exact fun h => hnot ⟨h.1 hc, h.2.1 hc, h.2.2.1 hc, h.2.2.2.1 hc, h.2.2.2.2 hc⟩
  · exact not_imp.mp hω
  all_goals
    obtain ⟨hg, hnot⟩ := hω
    obtain ⟨hc, hn'⟩ := not_imp.mp hnot
    exact ⟨hc, hg hc, hn'⟩

/-- `Case` off `Ω_ref` has probability at most `δ_ref`. -/
theorem refProb : μs ν {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ≤ ENNReal.ofReal (deltaRef d n δ) := by
  have hde : 0 ≤ (df2oPar d n δ).δe := by
    obtain ⟨hd, hn, hδ0, hδ1, heps⟩ := hreg
    exact (rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  have hsub : {ω | B.Case δ ω ∧ ¬ B.Good δ ω} ⊆
      (⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) ∪ {ω | B.Case δ ω ∧ ¬ B.Az δ ω} := by
    rintro ω ⟨hc, hg⟩
    by_cases hall : ∀ a < n, B.Five δ a ω
    · exact Or.inr ⟨hc, fun haz => hg ⟨hall, haz⟩⟩
    · obtain ⟨a, ha, hna⟩ : ∃ a < n, ¬ B.Five δ a ω :=
        by_contra fun hcon => hall fun a ha => by_contra fun hn => hcon ⟨a, ha, hn⟩
      exact Or.inl (Set.mem_biUnion (Finset.mem_range.mpr ha) ⟨hc, hna⟩)
  calc μs ν {ω | B.Case δ ω ∧ ¬ B.Good δ ω}
      ≤ μs ν ((⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) ∪ {ω | B.Case δ ω ∧ ¬ B.Az δ ω}) :=
        measure_mono hsub
    _ ≤ μs ν (⋃ a ∈ Finset.range n, {ω | B.Case δ ω ∧ ¬ B.Five δ a ω}) + μs ν {ω | B.Case δ ω ∧ ¬ B.Az δ ω} :=
        measure_union_le _ _
    _ ≤ ∑ a ∈ Finset.range n, μs ν {ω | B.Case δ ω ∧ ¬ B.Five δ a ω} + μs ν {ω | B.Case δ ω ∧ ¬ B.Az δ ω} :=
        add_le_add (measure_biUnion_finset_le _ _) le_rfl
    _ ≤ ∑ _a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
          ENNReal.ofReal ((df2oPar d n δ).δe / 7) :=
        add_le_add (Finset.sum_le_sum fun a ha =>
          five_bound hW hreg hKc hKconv hν hpos hC hB (Finset.mem_range.mp ha))
          (waz hreg hKc hKconv hν hpos hB hC)
    _ = ENNReal.ofReal (deltaRef d n δ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, deltaRef,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast]

end

end Run

/-- (O1) from W-EV: the probability part from the five budgets and W-AZ, the regret part from W-DET on the checked
advice routine. -/
theorem refProp_of_wev (hW : WEvProp) : RefProp := by
  intro d n δ K ν B hreg hKc hKconv hν hpos hC hB
  exact ⟨Run.refProb hW hreg hKc hKconv hν hpos hC hB,
    fun ω hq hg => Run.wdet (fun v => apAdv_spec hreg.1 v) hreg hKc hKconv hq hg⟩

/-- The proposition of the coupling of a run from W-EV. -/
theorem shadowProp_of_wev (hW : WEvProp) : ShadowProp :=
  shadowProp_of (refProp_of_wev hW) coupStepProp_holds

end AdversarialBco.Bit.Cpl
