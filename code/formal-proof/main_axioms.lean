import AdversarialBco.Conj1Bit.Main
import AdversarialBco.Conj1BitExp.Main
import AdversarialBco.Conj1LowerPoly.Main
-- The axioms of the delivered theorems and of the non-vacuity witnesses, those of the three configurations
-- config-*.json. Run from the package root: lake env lean code/formal-proof/main_axioms.lean
#print axioms AdversarialBco.theoremConj1UpperBit
#print axioms AdversarialBco.theoremConj1UpperBitExp
#print axioms AdversarialBco.theoremConj1UpperBitExp_of_bit
#print axioms AdversarialBco.theoremConj1LowerPoly_holds
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.hyps_satisfiable_exists
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.randAdv_unit
#print axioms AdversarialBco.BitRAM.Conj1BitSanity.nil_not_costOKBit
#print axioms AdversarialBco.Lower.Sanity.constLearner_mem_of_mem
#print axioms AdversarialBco.Lower.Sanity.zeroStrat_fails_of_nonempty
