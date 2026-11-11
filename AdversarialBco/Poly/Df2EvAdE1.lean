/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2EvAdMeas

@[expose] public section

/-!
# E1-loc with an adapted parameter

`df2E1LocAdOf_holds : Df2E1LocAdOf`, the union bound of `df2E1LocOf_holds` (Df2Layer2Proof.lean) on
`Df2OnSetEAd`: off the union of the five bad events the epoch is good by DET, applied at each `ω` to the context at
`θ 0 ω` and the path of the losses `gθ s (θ s ω)`, admissible on that body (`EvAd.admAd`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly

/-- E1-loc with an adapted parameter from DET and the five adapted budgets: the budgets add up to
`(3/7 + 1/7 + 1/21 + 1/7 + 1/8) δ_e = (149/168) δ_e`. -/
theorem df2E1LocAdOf_holds : Df2E1LocAdOf := by
  intro hDet hG hY hLQ hSDF hDQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ _ Kθ gθ ap hbody hadm hap hmeas Ω _ μ hμ
    𝒢 θ ξ e hθ hK hE
  have hde : 0 ≤ (df2oPar d n δ).δe := (Layer2.rowHyp_of d n δ hd hn hδ0 hδ1 heps).de_pos.le
  let c : Ω → Df2Ctx d := fun ω => df2CtxAt d n δ (Kθ (θ 0 ω)) ap
  let π : Ω → Df2Path d := fun ω => ⟨fun s => gθ s (θ s ω), fun s => e s ω, fun s => ξ s ω⟩
  have key : {ω | ¬ (c ω).EpochOK (π ω) m} ⊆
      {ω | ¬ (c ω).EvG (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} ∪
        {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m} := by
    intro ω hω
    by_contra hn'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hn'
    obtain ⟨⟨⟨⟨hg, hy⟩, hlq⟩, hsdf⟩, hdq⟩ := hn'
    exact hω (hDet d n δ (Kθ (θ 0 ω)) ap (π ω) m hd hn hδ0 hδ1 heps hm1 hmn (hbody _) hap
      (EvAd.admAd Kθ gθ hadm θ hK ω) hg (hy hg) (hlq hg) (hsdf hg) (hdq hg))
  have h1 := hG d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hK hE
  have h2 := hY d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hK hE
  have h3 := hLQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hK hE
  have h4 := hSDF d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hK hE
  have h5 := hDQ d n m δ hd hn hm1 hmn hδ0 hδ1 heps Θ Kθ gθ ap hbody hadm hap hmeas Ω μ hμ 𝒢 θ ξ e hθ hK hE
  calc μ {ω | ¬ (c ω).EpochOK (π ω) m}
      ≤ μ ({ω | ¬ (c ω).EvG (π ω) m} ∪ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} ∪
          {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m}) := measure_mono key
    _ ≤ μ {ω | ¬ (c ω).EvG (π ω) m} + μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvY (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvLQ (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvSDF (π ω) m} +
          μ {ω | (c ω).EvG (π ω) m ∧ ¬ (c ω).EvDQ (π ω) m} := by
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (3 / 7 * (df2oPar d n δ).δe) + ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) +
          ENNReal.ofReal (1 / 21 * (df2oPar d n δ).δe) + ENNReal.ofReal (1 / 7 * (df2oPar d n δ).δe) +
          ENNReal.ofReal (1 / 8 * (df2oPar d n δ).δe) := by gcongr
    _ = ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

end AdversarialBco.Poly
