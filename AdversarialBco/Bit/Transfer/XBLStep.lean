/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv

@[expose] public section

/-!
# BL's round in mode `run` as named values

The values of `BLPure.step` in mode `run` as definitions (`rY`, `rc`, `ra`, `rq`, the roots, `A'`, `B'`, `b'`, `k'`,
`g`, `G'`, `l'`, `P'`, `w'`, the call of R11, `s5`, `w_μ`, the call of R14).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit.BLP Matrix
open AdversarialBco.BitRAM (toE)
open AdversarialBco.RealRAM (Strategy lossAd)

variable {d : ℕ}

section Vals

variable (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)

/-- R5: `Y`. -/
def rY : ℚ :=
  rnd cfg.par.p (ptQ cfg (XQ cfg st ξ) * ((obs : ℚ) / 2 ^ cfg.par.p + ζ) / 2 +
    2 * (ptQ cfg (XQ cfg st ξ) - 1) / cfg.par.eps)

/-- R7: `c`, `a`, `q`. -/
def rc : ℚ := cfg.par.kapc * rY cfg st ξ ζ obs
def ra : ℚ := 1 - rc cfg st ξ ζ obs
def rq : ℚ := ra cfg st ξ ζ obs + rc cfg st ξ ζ obs * (ξ ⬝ᵥ ξ)

/-- R7: the roots. -/
def rs1 : ℚ := sqrtDn cfg.par.p (1 / ra cfg st ξ ζ obs)
def rs3 : ℚ := sqrtDn cfg.par.p (ra cfg st ξ ζ obs)
def rrq : ℚ := sqrtDn cfg.par.p (rq cfg st ξ ζ obs)
def rs2 : ℚ :=
  rnd cfg.par.p (rc cfg st ξ ζ obs /
    (rs3 cfg st ξ ζ obs * rrq cfg st ξ ζ obs * (rs3 cfg st ξ ζ obs + rrq cfg st ξ ζ obs)))
def rs4 : ℚ := rnd cfg.par.p (rc cfg st ξ ζ obs / (rs3 cfg st ξ ζ obs + rrq cfg st ξ ζ obs))

/-- R8: `A'`, `B'`. -/
def rA' : Matrix (Fin d) (Fin d) ℚ :=
  rndM cfg.par.p (rs1 cfg st ξ ζ obs • st.A - rs2 cfg st ξ ζ obs • vecMulVec (st.A *ᵥ ξ) ξ)
def rB' : Matrix (Fin d) (Fin d) ℚ :=
  rndM cfg.par.p (rs3 cfg st ξ ζ obs • st.B + rs4 cfg st ξ ζ obs • vecMulVec (st.B *ᵥ ξ) ξ)

/-- R9: `b'`, `k'`, `g`, `G'`, `l'`. -/
def rb' : Fin d → ℚ :=
  st.b + rndV cfg.par.p (rc cfg st ξ ζ obs • (((st.B *ᵥ ξ) ⬝ᵥ st.mu) • (st.B *ᵥ ξ) - st.B *ᵥ (st.Bᵀ *ᵥ st.mu)))
def rk' : ℚ :=
  st.k + rnd cfg.par.p (rc cfg st ξ ζ obs / 2 * (((st.B *ᵥ ξ) ⬝ᵥ st.mu) ^ 2 - (st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu)))
def rg : Fin d → ℚ := rndV cfg.par.p ((rY cfg st ξ ζ obs * cfg.par.nu) • (st.B *ᵥ ξ))
def rG' : Fin d → ℚ := st.G + rg cfg st ξ ζ obs
def rl' : ℚ := st.l + rnd cfg.par.p (rg cfg st ξ ζ obs ⬝ᵥ st.mu)

/-- R13: `s5`, `w_μ`. -/
def rs5 : ℚ := rnd cfg.par.p (cfg.par.eta * rY cfg st ξ ζ obs * cfg.par.nu / rq cfg st ξ ζ obs)
def rwmu : Fin d → ℚ := st.mu - rs5 cfg st ξ ζ obs • (st.A *ᵥ ξ)

end Vals

end AdversarialBco.Bit.Transfer.BLM
