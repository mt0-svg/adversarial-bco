/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body2.Dil2
public import AdversarialBco.Body2.PropBody
public import AdversarialBco.Explicit.DilAll

@[expose] public section

/-!
# Theorem 3.1 for every family and Proposition 2.2, with their explicit constants

The solution module of the challenge `AdversarialBco.ChallengeBody` (`config-body.json`):

* `dilTheorem`: Theorem 3.1 with `K_S = 2 (32/κ)^2 (13/4 + 2 κ_2)` and `K_D = 1.6·10^6`, from its regular case
  (`AdversarialBco.Body2.dilRegExplicit`, `AdversarialBco.Body2.ecReg`) through Appendix D
  (`AdversarialBco.DilAll.dilTheorem_of_reg`);
* `bodyExplicit`: Proposition 2.2 with `C_0 = 1.2·10^9` (`AdversarialBco.Body2.bodyExplicit_of_dil`);
* `bodyHExplicit`: Proposition 2.2 on the inner body of a convex body containing a unit ball
  (`AdversarialBco.Body2.bodyHExplicit_of_body`).
-/

namespace AdversarialBco.BodySpec

/-- **Theorem 3.1** for every family. -/
theorem dilTheorem : DilTheorem :=
  AdversarialBco.DilAll.dilTheorem_of_reg AdversarialBco.Body2.dilRegExplicit AdversarialBco.Body2.ecReg

/-- **Proposition 2.2** with `C_0 = 1.2·10^9`. -/
theorem bodyExplicit : BodyExplicit := AdversarialBco.Body2.bodyExplicit_of_dil dilTheorem

/-- Proposition 2.2 on the inner body `{y | closedBall y (1/n) ⊆ K}`, for every `D ≥ diam K`. -/
theorem bodyHExplicit : BodyHExplicit := AdversarialBco.Body2.bodyHExplicit_of_body bodyExplicit

end AdversarialBco.BodySpec
