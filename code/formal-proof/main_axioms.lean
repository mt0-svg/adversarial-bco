import AdversarialBco.UW.TheoremU
import AdversarialBco.LowerDeltaQ.Minimax
import AdversarialBco.Matched.Main
import AdversarialBco.Conj1BitHP.Main
import AdversarialBco.Conj1.Main
-- The axioms of the delivered theorems and of the non-vacuity witnesses, those of the configurations config-*.json
-- (the imports are their solution modules).
-- Run from the package root: lake env lean code/formal-proof/main_axioms.lean
#print axioms AdversarialBco.theoremConj1UpperBitHP
#print axioms AdversarialBco.theoremConj1UpperBit_of_hp
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.hyps_satisfiable_exists
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.randAdv_unit
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.nil_not_costOKBit
#print axioms AdversarialBco.UW.theoremUW
#print axioms AdversarialBco.Grow.theoremGrowG
#print axioms AdversarialBco.Grow.theoremGrowGProg
#print axioms AdversarialBco.Matched.theoremMinimaxMatched
#print axioms AdversarialBco.Matched.theoremMinimaxMatched_of
#print axioms AdversarialBco.Matched.MatchedSanity.growG_hyps_satisfiable
#print axioms AdversarialBco.Matched.MatchedSanity.matched_hyps_satisfiable
#print axioms AdversarialBco.Matched.MatchedSanity.matched_exceeds_flat
#print axioms AdversarialBco.Matched.MatchedSanity.growGProg_matched_hyps_satisfiable
#print axioms AdversarialBco.LowerDeltaQ.Sanity.minimaxQ_high_hyps_satisfiable
#print axioms AdversarialBco.UnifiedLower.LowerSanity.lowerU_hyps_satisfiable
#print axioms AdversarialBco.UnifiedLower.LowerSanity.progU_hyps_satisfiable
#print axioms AdversarialBco.LowerDeltaQ.theoremLowerUDQ
#print axioms AdversarialBco.LowerDeltaQ.theoremLowerUDProgQ
#print axioms AdversarialBco.LowerDeltaQ.theoremMinimaxQ
#print axioms AdversarialBco.theoremConj1LowerPolyDQ_holds
#print axioms AdversarialBco.LowerDeltaQ.lowerU_b_of_UDQ
#print axioms AdversarialBco.LowerDeltaQ.lowerUProg_b_of_UDProgQ
#print axioms AdversarialBco.LowerDeltaQ.Sanity.lowerUDQ_a_hyps_satisfiable
#print axioms AdversarialBco.LowerDeltaQ.Sanity.lowerUDQ_a_small_hyps_satisfiable
#print axioms AdversarialBco.LowerDeltaQ.Sanity.boundDQ_facts
#print axioms AdversarialBco.LowerDeltaQ.Sanity.zeroStrat_fails_of_nonemptyDQ
#print axioms AdversarialBco.Lower.PolyDSanity.constLearner_mem_of_mem
#print axioms AdversarialBco.Minimax.MinimaxSanity.payoffs_bounded
#print axioms AdversarialBco.Minimax.MinimaxSanity.meanPosOf_tail_eq_integral
#print axioms AdversarialBco.theoremUnified
#print axioms AdversarialBco.Unified.UnifiedSanity.weakMemOracle_exact
#print axioms AdversarialBco.Unified.UnifiedSanity.histσ_le
#print axioms AdversarialBco.Unified.UnifiedSanity.hyps_satisfiable
#print axioms AdversarialBco.Unified.UnifiedSanity.noisyAdv_signNoise
#print axioms AdversarialBco.Unified.UnifiedSanity.nil_not_costOKO
#print axioms AdversarialBco.UW.theoremUnified_of_UW
#print axioms AdversarialBco.theoremConj1Upper
#print axioms AdversarialBco.RealRAM.Conj1Sanity.hyps_satisfiable_exists
#print axioms AdversarialBco.RealRAM.Conj1Sanity.isProbabilityMeasure_runs
#print axioms AdversarialBco.RealRAM.Conj1Sanity.nil_not_costOKAd
