/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvAz

@[expose] public section

/-!
# W-EV for P° of Theorem UW: the failure budget

`evProbUW_of : EvGPropUW → EvYPropUW → EvLQPropUW → EvSDFPropUW → EvDQPropUW → EvProbUW`, the port of Theorem U's
`RunW.five_bound` and `RunW.refProb` (Unified/WorldShadowRef.lean) to the level `δc`:

* `five_boundU`: the virtual epoch started before round `a < n` misses one of its five events with probability at
  most `(149/168) δc`. Each Prop of UW/EvIface.lean bounds its event on the world (`epoch_boundU`, UW/EvSetE.lean);
  no event is conditioned on event (a), so the bounds of (b) to (e) enter `union5` through the inclusion
  `{G ∧ ¬Y} ⊆ {¬Y}`.
* `refProbU`: off `Ω_ref` (`GoodU`), the case has probability at most `n (149/168) δc + δc/7 = δ_ref(δc)`: the
  union over the `n` epochs and Azuma (`wazU`, UW/EvAz.lean).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World

variable {d : ℕ}

namespace RunU

section Ref

variable {n : ℕ} {K : Set (E d)} {Ω : Type} [m0 : MeasurableSpace Ω] {W : CWorld d Ω} {B : RunW d n K W}
  {ρ : RefW}

/-- The epoch started before round `a < n` misses one of its five events with probability at most
`(149/168) δc`. -/
theorem five_boundU (hG : EvGPropUW) (hY : EvYPropUW) (hLQ : EvLQPropUW) (hSDF : EvSDFPropUW)
    (hDQ : EvDQPropUW) (hW : WorldLawOK W) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeasW B) {a : ℕ} (ha : a < n) :
    W.μ {ω | B.Case ρ.δc ω ∧ ¬ FiveU B ρ a ω} ≤ ENNReal.ofReal (149 / 168 * ρ.δc) := by
  have eG := epoch_boundU hG hW hreg hKc hKconv hpos hC hB ha
  have eY := epoch_boundU hY hW hreg hKc hKconv hpos hC hB ha
  have eLQ := epoch_boundU hLQ hW hreg hKc hKconv hpos hC hB ha
  have eSDF := epoch_boundU hSDF hW hreg hKc hKconv hpos hC hB ha
  have eDQ := epoch_boundU hDQ hW hreg hKc hKconv hpos hC hB ha
  refine le_trans (measure_mono fun ω hω => hω.2) (union5 W.μ
    (fun ω => EvGW (ctxU B ρ a ω) (pathU B ρ a ω) (epU B ρ a ω) (lgW n ρ.δc) (leW ρ.δc) (n - a))
    (fun ω => EvYW (ctxU B ρ a ω) (epU B ρ a ω) (sYW n ρ.y0 ρ.δc) (n - a))
    (fun ω => EvLQW (ctxU B ρ a ω) (epU B ρ a ω) (b1W (parW d n ρ.u) d n ρ.u) (n - a))
    (fun ω => EvSDFW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a))
    (fun ω => EvDQW (ctxU B ρ a ω) (epU B ρ a ω) (bnW (parW d n ρ.u) d n ρ.u) (n - a)) _ hreg.dc_pos.le eG
    (le_trans (measure_mono fun ω hω => hω.2) eY) (le_trans (measure_mono fun ω hω => hω.2) eLQ)
    (le_trans (measure_mono fun ω hω => hω.2) eSDF) (le_trans (measure_mono fun ω hω => hω.2) eDQ))

/-- Off `Ω_ref` of Theorem UW the case has probability at most `δ_ref(δc)`. -/
theorem refProbU (hG : EvGPropUW) (hY : EvYPropUW) (hLQ : EvLQPropUW) (hSDF : EvSDFPropUW)
    (hDQ : EvDQPropUW) (hW : WorldLawOK W) (hreg : RegimeW d n ρ) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hpos : Measurable[W.𝓕 0] B.pos) (hC : CoupLaw B.Coup) (hB : BLMeasW B) :
    W.μ {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω} ≤ ENNReal.ofReal (deltaRefW n ρ.δc) := by
  have hdc := hreg.dc_pos
  have hsub : {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω} ⊆
      (⋃ a ∈ Finset.range n, {ω | B.Case ρ.δc ω ∧ ¬ FiveU B ρ a ω}) ∪ {ω | B.Case ρ.δc ω ∧ ¬ AzU B ρ ω} := by
    rintro ω ⟨hc, hg⟩
    by_cases hall : ∀ a < n, FiveU B ρ a ω
    · exact Or.inr ⟨hc, fun haz => hg ⟨hall, haz⟩⟩
    · obtain ⟨a, ha, hna⟩ : ∃ a < n, ¬ FiveU B ρ a ω :=
        by_contra fun hcon => hall fun a ha => by_contra fun hn => hcon ⟨a, ha, hn⟩
      exact Or.inl (Set.mem_biUnion (Finset.mem_range.mpr ha) ⟨hc, hna⟩)
  calc W.μ {ω | B.Case ρ.δc ω ∧ ¬ GoodU B ρ ω}
      ≤ W.μ ((⋃ a ∈ Finset.range n, {ω | B.Case ρ.δc ω ∧ ¬ FiveU B ρ a ω}) ∪
          {ω | B.Case ρ.δc ω ∧ ¬ AzU B ρ ω}) := measure_mono hsub
    _ ≤ W.μ (⋃ a ∈ Finset.range n, {ω | B.Case ρ.δc ω ∧ ¬ FiveU B ρ a ω}) +
          W.μ {ω | B.Case ρ.δc ω ∧ ¬ AzU B ρ ω} := measure_union_le _ _
    _ ≤ ∑ a ∈ Finset.range n, W.μ {ω | B.Case ρ.δc ω ∧ ¬ FiveU B ρ a ω} +
          W.μ {ω | B.Case ρ.δc ω ∧ ¬ AzU B ρ ω} := add_le_add (measure_biUnion_finset_le _ _) le_rfl
    _ ≤ ∑ _a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * ρ.δc) + ENNReal.ofReal (ρ.δc / 7) :=
        add_le_add (Finset.sum_le_sum fun a ha =>
          five_boundU hG hY hLQ hSDF hDQ hW hreg hKc hKconv hpos hC hB (Finset.mem_range.mp ha))
          (wazU hW hreg hKc hKconv hpos hB hC)
    _ = ENNReal.ofReal (deltaRefW n ρ.δc) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, deltaRefW,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ENNReal.ofReal_natCast]

end Ref

end RunU

/-- **W-EV at the level `δc`** from the five bounds of setting (E). -/
theorem evProbUW_of (hG : EvGPropUW) (hY : EvYPropUW) (hLQ : EvLQPropUW) (hSDF : EvSDFPropUW)
    (hDQ : EvDQPropUW) : EvProbUW := by
  intro d n ρ K Ω _ W B hreg hKc hKconv hW hpos hC hB
  exact RunU.refProbU hG hY hLQ hSDF hDQ hW hreg hKc hKconv hpos hC hB

end AdversarialBco.UW
