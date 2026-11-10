import AdversarialBco.Main
import AdversarialBco.Explicit
import AdversarialBco.Body2.Main

-- The axioms of the delivered theorems (those of config.json, config-explicit.json and config-body.json, and the
-- Gaussian concentration). Run from the package root: lake env lean code/formal-proof/main_axioms.lean

#print axioms AdversarialBco.corollaryADV
#print axioms AdversarialBco.Explicit.theoremExplicit
#print axioms AdversarialBco.Explicit.lemmaMarg
#print axioms AdversarialBco.Explicit.corollaryExplicit
#print axioms AdversarialBco.BodySpec.dilTheorem
#print axioms AdversarialBco.BodySpec.bodyExplicit
#print axioms AdversarialBco.BodySpec.bodyHExplicit
#print axioms AdversarialBco.body_H
#print axioms AdversarialBco.Gauss.gaussConcAt
