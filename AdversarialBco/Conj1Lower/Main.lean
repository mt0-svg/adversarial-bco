/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Lower.Top

@[expose] public section

/-!
# Theorem 1.4 of the paper: the lower bound

The solution module of config-conj1-lower.json: `TheoremConj1Lower` (StatementConj1Lower.lean) from
`Lower.Top.theoremConj1Lower_of_inputs`, its hypotheses `Lower.Top.Inputs` filled with the theorems of Moments.lean,
Ledger.lean and Info.lean.
-/

open MeasureTheory

namespace AdversarialBco

/-- The statements of Moments.lean, Ledger.lean and Info.lean that Top.lean uses. -/
theorem lowerTopInputs : Lower.Top.Inputs where
  secMom_posSemidef := fun π _ h2 m => Lower.secMom_posSemidef π h2 m
  cellPay_empty := fun π w => Lower.cellPay_empty π w
  pay_tail := fun π _ h2 _ _ hw hk x _ hc ht => Lower.pay_tail π h2 hw hk x hc ht
  pay_inner := fun π _ h2 _ hw hd hlive _ hc hin => Lower.pay_inner π h2 hw hd hlive hc hin
  pay_outer := fun π _ h2 _ hw hd _ hc hout => Lower.pay_outer π h2 hw hd hc hout
  ledger_game := fun hd _ hr μ _ R hR _ hsc _ _ hpol _ hw => Lower.ledger_game hd hr μ R hR hsc hpol hw
  infoJ_chain := fun π _ _ hc _ hs _ hsb _ hsc ĉ => Lower.infoJ_chain π hc hs hsb hsc ĉ
  infoJ_const := fun π _ a₀ b _ hsc => Lower.infoJ_const π a₀ b hsc
  integrable_infoRound := fun π0 _ μ _ R hR _ hsc _ _ hpol _ hsb _ ht =>
    Lower.integrable_infoRound π0 μ R hR hsc hpol hsb ht
  count_game := fun hd μ _ R hR _ hsc _ _ hpol _ hsb _ hw hX => Lower.count_game hd μ R hR hsc hpol hsb hw hX

theorem theoremConj1Lower : TheoremConj1Lower :=
  Lower.Top.theoremConj1Lower_of_inputs lowerTopInputs

end AdversarialBco
