import AdversarialBco.Main
import AdversarialBco.Explicit
import AdversarialBco.Body2.Main
import AdversarialBco.Poly.Poly32OFinal
import AdversarialBco.Conj1.Main
import AdversarialBco.Conj1Exp.Main
import AdversarialBco.Conj1Lower.Main
import AdversarialBco.Conj1Poly.Main
import AdversarialBco.Conj1PolyExp.Main

-- The axioms of the delivered theorems (those of the nine configurations config*.json, and the Gaussian
-- concentration). Run from the package root: lake env lean code/formal-proof/main_axioms.lean

#print axioms AdversarialBco.theoremConj1UpperExp
#print axioms AdversarialBco.theoremConj1UpperExp_of_conj1
#print axioms AdversarialBco.theoremConj1Upper
#print axioms AdversarialBco.theoremPoly32O_holds
#print axioms AdversarialBco.theoremPoly32O_of_conj1
#print axioms AdversarialBco.theoremConj1UpperPoly
#print axioms AdversarialBco.theoremConj1UpperPoly_of_conj1
#print axioms AdversarialBco.theoremConj1UpperPolyExp
#print axioms AdversarialBco.theoremConj1UpperPolyExp_of_poly
#print axioms AdversarialBco.theoremConj1Lower
#print axioms AdversarialBco.corollaryADV
#print axioms AdversarialBco.Explicit.theoremExplicit
#print axioms AdversarialBco.Explicit.lemmaMarg
#print axioms AdversarialBco.Explicit.corollaryExplicit
#print axioms AdversarialBco.BodySpec.dilTheorem
#print axioms AdversarialBco.BodySpec.bodyExplicit
#print axioms AdversarialBco.BodySpec.bodyHExplicit
#print axioms AdversarialBco.body_H
#print axioms AdversarialBco.Gauss.gaussConcAt
