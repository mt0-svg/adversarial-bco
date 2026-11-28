/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.LowerDeltaQ.Main
public import AdversarialBco.StatementMinimaxQ
public import AdversarialBco.UnifiedLower.Small
public import AdversarialBco.UnifiedLower.Prog

@[expose] public section

/-!
# `TheoremLowerUDQ` and `TheoremLowerUDProgQ`

The two lower statements with a failure probability `δ` stopped on the bowl of AdversarialBco/StatementMinimaxQ.lean,
from LowerDeltaQ/Main.lean and Lemma SMALL (UnifiedLower/Small.lean).

* `theoremLowerUDQ`: clause (a) is `lowerU_probDeltaQ` (`LowerProbNN`), clause (b) is `lowerU_meanDeltaQ`, clause (c)
  is Lemma SMALL (`Small.lowerU_small_mean`, `Small.lowerU_small_prob`);
* `progUDQ_of_lowerUDQ : TheoremLowerUDQ → TheoremLowerUDProgQ`: the learner of a program that
  meets `MachineOK` (Lemma BRIDGE, `progLearner_isLearner`) meets a strategy of `StratsLowU`, whose closed loop with the
  program (Lemma REAL, `clLoss`, `closedLoop_cl`, `noisyAdv_cl`) is an environment of `TheoremUnified` with the
  program's windows and the noise `0`, and the regrets agree coin sequence by coin sequence (`regretU_cl`);
* `theoremLowerUDProgQ`.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.LowerDeltaQ

open BitRAM BitRAMO Unified UnifiedLower UnifiedLower.Prog UnifiedLower.LowerSanity Minimax
open RealRAM (Strategy Strats)
open Lower (Learner IsLearnerAd regretAd)

/-- **Theorem LU-DQ** (`TheoremLowerUDQ`). -/
theorem theoremLowerUDQ : TheoremLowerUDQ := by
  intro d hd n hn a r0 R0 K hb Ω _ μ hμ pol hpol
  exact ⟨fun δ hδ0 hδ1 h1 h2 hD1 hD3 => lowerU_probDeltaQ h1 h2 hδ0 hδ1 hD1 hD3 hb μ hpol,
    fun h1 h2 => lowerU_meanDeltaQ h1 h2 hb μ hpol, Small.lowerU_small_mean μ hd hn hb hpol,
    Small.lowerU_small_prob μ hd hn hb hpol⟩

/-- `TheoremLowerUDProgQ` from `TheoremLowerUDQ`, as `TheoremLowerUDProg` from `TheoremLowerUD`. -/
theorem progUDQ_of_lowerUDQ (hL : TheoremLowerUDQ) : TheoremLowerUDProgQ := by
  intro P d hd n hn δ r0 R0 hδ0 hδ1 hr0 hr0R a K hKc hKv hK1 hK2 orc _ B D D' hM
  have hs0 : (initU d n δ r0 R0 a).rounds = 0 := rfl
  have hb := bodyU_of_unified hr0 hr0R a hKc hKv hK1 hK2
  have hpol := progLearner_isLearner hKv hM hs0
  obtain ⟨hpa, hmb, hcm, hcp⟩ := hL d hd n hn (toE a) r0 R0 K hb (ℕ → Bool) _ coinStream inferInstance
    (progLearner P (initU d n δ r0 R0 a) orc) hpol
  have mean : ∀ c, LowerMean K n r0 coinStream (progLearner P (initU d n δ r0 R0 a) orc) c →
      ProgMean P K orc (initU d n δ r0 R0 a) n r0 D D' c := by
    rintro c ⟨σ, hσ, hint, hge⟩
    refine ⟨σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_⟩
    · simpa only [regretU_cl] using hint
    · simpa only [regretU_cl] using hge
  have prob : ∀ c p, LowerProb K n r0 coinStream (progLearner P (initU d n δ r0 R0 a) orc) c p →
      ProgProb P K orc (initU d n δ r0 R0 a) n r0 D D' c p := by
    rintro c p ⟨σ, hσ, hm, hge⟩
    refine ⟨σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_⟩
    · simpa only [regretU_cl] using hm
    · simpa only [regretU_cl] using hge
  have probNN : ∀ c p, LowerProbNN K n r0 coinStream (progLearner P (initU d n δ r0 R0 a) orc) c p →
      ProgProbNN P K orc (initU d n δ r0 R0 a) n r0 D D' c p := by
    rintro c p ⟨σ, hσ, hm, hnn, hge⟩
    refine ⟨σ, clLoss P (initU d n δ r0 R0 a) orc σ, hσ, closedLoop_cl _ _ _ _ hσ, noisyAdv_cl hσ hM, ?_, ?_, ?_⟩
    · simpa only [regretU_cl] using hm
    · simpa only [regretU_cl] using hnn
    · simpa only [regretU_cl] using hge
  exact ⟨fun δ' h0 h1 h2 h3 hD1 hD3 => probNN _ _ (hpa δ' h0 h1 h2 h3 hD1 hD3), fun h1 h2 => mean _ (hmb h1 h2),
    mean _ hcm, prob _ _ hcp⟩

/-- **Theorem LU-DQ for the programs of the oracle machine, in the objects of `TheoremUnified`**
(`TheoremLowerUDProgQ`). -/
theorem theoremLowerUDProgQ : TheoremLowerUDProgQ :=
  progUDQ_of_lowerUDQ theoremLowerUDQ

end AdversarialBco.LowerDeltaQ
