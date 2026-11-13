/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2CompProof
public import AdversarialBco.Poly.Df2ParBounds
public import AdversarialBco.Poly.Df2WorldAz
public import AdversarialBco.Poly.Df2WorldDetProof
public import AdversarialBco.Poly.MachAPBase
public import AdversarialBco.Poly.Df2PlayProof
public import AdversarialBco.Poly.Df2R1Proof
public import AdversarialBco.Poly.WrapperProof
public import AdversarialBco.Poly.PgProcProof
public import AdversarialBco.Poly.PgMeasProof
public import AdversarialBco.Poly.Df2AzumaProof
public import AdversarialBco.Poly.Df2OracleProof
public import AdversarialBco.Poly.Df2PropGProof
public import AdversarialBco.Poly.Df2ApMeasProof

@[expose] public section

/-!
# The layer-1 Props of DF2, all proved

`df2LayerOne_holds : Df2LayerOne`, the layer-1 Props of `Df2.lean` and `Df2R1.lean` gathered from their proofs, the
input that the coupling of the bit-model learner (`Bit/BLEngine.lean`, `Bit/ShadowDet.lean`) takes from the analysis of
DF2.
-/

namespace AdversarialBco.Poly

open Mach.VL

/-- The layer-1 Props of `Df2.lean` and `Df2R1.lean`, all proved. -/
theorem df2LayerOne_holds : Df2LayerOne :=
  ⟨lemmaDFI_holds, lemmaMON_holds, propINC2_holds, lemmaD2_holds, lemmaONS2Core_holds, lemmaZCore_holds,
    df2RowZ_holds, playShift_holds, lemmaUBPrime_holds, playHess_holds, df2Trivial_holds, df2Carriers_holds,
    lemmaR1i, lemmaR1ii, lemmaR1iii, lemmaR1iv, lemmaR1v⟩

end AdversarialBco.Poly
