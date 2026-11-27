import AdversarialBco.UnifiedMatch.Main
import AdversarialBco.Conj1BitHP.Main
import AdversarialBco.Conj1.Main
import AdversarialBco.Conj1LowerPoly.Main
-- The axioms of the delivered theorems and of the non-vacuity witnesses, those of the six configurations
-- config-*.json (UnifiedMatch.Main imports the solution modules of config-unified.json and config-unified-lower.json).
-- Run from the package root: lake env lean code/formal-proof/main_axioms.lean
#print axioms AdversarialBco.theoremUnified
#print axioms AdversarialBco.Unified.UnifiedSanity.weakMemOracle_exact
#print axioms AdversarialBco.Unified.UnifiedSanity.histσ_le
#print axioms AdversarialBco.Unified.UnifiedSanity.hyps_satisfiable
#print axioms AdversarialBco.Unified.UnifiedSanity.noisyAdv_signNoise
#print axioms AdversarialBco.Unified.UnifiedSanity.nil_not_costOKO
#print axioms AdversarialBco.theoremLowerU
#print axioms AdversarialBco.theoremLowerUProg
#print axioms AdversarialBco.theoremLowerU_cube
#print axioms AdversarialBco.UnifiedLower.LowerSanity.lowerU_hyps_satisfiable
#print axioms AdversarialBco.UnifiedLower.LowerSanity.lowerU_zero
#print axioms AdversarialBco.UnifiedLower.LowerSanity.progU_hyps_satisfiable
#print axioms AdversarialBco.UnifiedLower.LowerSanity.nil_not_machineOK
#print axioms AdversarialBco.UnifiedLower.LowerSanity.progU_zero
#print axioms AdversarialBco.UnifiedLower.LowerSanity.bodyU_of_unified
#print axioms AdversarialBco.UnifiedLower.LowerSanity.theoremConj1Lower_of_lowerU
#print axioms AdversarialBco.UnifiedLower.LowerSanity.corollaryMatch_of_unified_lower
#print axioms AdversarialBco.UnifiedLower.LowerSanity.theoremUnified_of_corollaryMatch
#print axioms AdversarialBco.corollaryMatch
#print axioms AdversarialBco.theoremConj1UpperBitHP
#print axioms AdversarialBco.theoremConj1UpperBit_of_hp
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.hyps_satisfiable_exists
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.randAdv_unit
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.nil_not_costOKBit
#print axioms AdversarialBco.theoremConj1Upper
#print axioms AdversarialBco.RealRAM.Conj1Sanity.hyps_satisfiable_exists
#print axioms AdversarialBco.RealRAM.Conj1Sanity.isProbabilityMeasure_runs
#print axioms AdversarialBco.RealRAM.Conj1Sanity.nil_not_costOKAd
#print axioms AdversarialBco.theoremConj1LowerPoly_holds
#print axioms AdversarialBco.Lower.Sanity.constLearner_mem_of_mem
#print axioms AdversarialBco.Lower.Sanity.zeroStrat_fails_of_nonempty
