/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupCopy
public import AdversarialBco.Bit.Transfer.XSetup

@[expose] public section

/-!
# BL's setup on the machine: the copies of PARAM's values

`prmCopies`: the copies of PARAM's values into BL's slots, `(dst, 30 + k)` for the value `pv d n k`; `prmCopies_ok`:
the destinations are distinct slots below `30`, apart from the sources. `XV.rtoNat`: `rtoN` on a slot holding a
natural number.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- `omega` after unfolding the names of BL's cells. -/
macro "bomega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst,
  sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu,
  sK, sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0]) <;> omega))

/-- The copies of PARAM's values into BL's slots, `(dst, 30 + k)` for the value `pv d n k`. -/
def prmCopies : List (ℕ × ℕ) :=
  [(s2p, 65), (s2pF, 66), (s2g, 64), (sNe, 48), (sLam, 70), (sRint, 121), (s2eh, 69), (sEps, 99), (sLamb, 100),
    (sEta, 101), (sRho, 103), (sKapc, 104), (sNu, 105), (sR, 110), (sSb, 111), (sW, 115), (sA0, 119), (sB0, 120)]

theorem prmCopies_ok : (∀ p ∈ prmCopies, p.1 < 30 ∧ p.1 ≠ sMode ∧ 30 ≤ p.2 ∧ p.2 - 30 < 93) ∧
    (prmCopies.map Prod.fst).Nodup ∧ (∀ p ∈ prmCopies, ∀ q ∈ prmCopies, p.1 ≠ q.2) ∧
    (∀ p ∈ prmCopies, 4 ≤ p.1 ∧ p.1 ≤ 21) := by decide

/-- `rtoN` on a slot holding a natural number. -/
theorem XV.rtoNat {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {i x v : ℕ}
    (hi : i < L.NN) (hx : x < L.NS) (hv : σ.sc x = ((v : ℤ) : ℝ)) (ha : v < 2 ^ ℓa) (hl : v < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrtoN L i x) σ 1 (· = σ.setNat i v) :=
  XV.mono (XV.rtoN hL hi hx (by rw [hv]; positivity) (by rw [hv]; exact_mod_cast ha)
    (by rw [hv, abs_of_nonneg (by positivity)]; exact_mod_cast hl)) le_rfl fun σ' e => by
    rw [e, hv, Int.floor_intCast, Int.toNat_natCast]

end AdversarialBco.Bit.Transfer.BLM
