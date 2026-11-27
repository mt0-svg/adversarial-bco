/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngDefs
public import AdversarialBco.Unified.EngVE

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the record's identities

The identities of BL-O's record `recO` (Unified/AsmRec.lean). With `B = recO ..`, `w` the environment's world at `ω`
and `c = cfgW .. w` BL-O's configuration: the record's losses and noises of the rounds `t < n` are the environment's
(`loss_eq`, `nz_eq`), BL-O's reading in mode `run` is `obsO` (`readO_eq`), and its next mode is `stepO` at that
reading (`modeO_succ`, `modeO_succ_run`). The loss of a round and P°'s observation on `Case` are in
Unified/EngVE.lean (`path_g`, `ctx_Y`); P°'s observation as the record's `refYO` and BL-O's coupled observation in
Unified/EngInd.lean (`refYO_eq`, `cY_coupledO`).
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Bit.BLP (Par St Mode init refX refPt)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (clip WorldO)
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

theorem loss_eq (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (ω : Ω × (ℕ → ℝ)) {t : ℕ} (ht : t < n) :
    (recO n δ r0 R0 a orc h hK).loss ω t = (envWorld orc coin loss noise ω.1).f t :=
  recO_loss n δ r0 R0 a orc h hK ω t ht

theorem nz_eq (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (ω : Ω × (ℕ → ℝ))
    {t : ℕ} (ht : t < n) : (extO n δ r0 R0 a h).nz t ω = (envWorld orc coin loss noise ω.1).noise t := by
  show (extW (P0O d n δ r0 R0) (parO d n δ).B (winO h)).nz t ω = _
  rw [extW_nz, if_pos ht]
  rfl

/-- BL-O's mode after round `t`. -/
theorem modeO_succ (w : WorldO d) (t : ℕ) :
    modeO d n δ r0 R0 a w (t + 1) = stepO w.orc (cfgW d n δ r0 R0 a w) n (modeO d n δ r0 R0 a w t)
      (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2
      (clip (cfgW d n δ r0 R0 a w).qO ⌊(2 : ℝ) ^ (cfgW d n δ r0 R0 a w).par.p *
        (w.f t (toE (playPtO w.orc (cfgW d n δ r0 R0 a w) (modeO d n δ r0 R0 a w t) (drawO d n δ r0 R0 w.cs t).1)) +
          w.noise t)⌋) := rfl

/-- BL-O's reading in mode `run st` is `obsO`. -/
theorem readO_eq (w : WorldO d) {t : ℕ} {st : St d} (hW : modeO d n δ r0 R0 a w t = .run st) :
    readO d n δ r0 R0 a w t =
      obsO w.orc (cfgW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1 (w.f t) (w.noise t) := by
  unfold readO obsO playO
  rw [hW]
  rfl

/-- BL-O's next mode in mode `run st` is `stepO` at the reading `obsO`. -/
theorem modeO_succ_run (w : WorldO d) {t : ℕ} {st : St d} (hW : modeO d n δ r0 R0 a w t = .run st) :
    modeO d n δ r0 R0 a w (t + 1) = stepO w.orc (cfgW d n δ r0 R0 a w) n (.run st)
      (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2
      (obsO w.orc (cfgW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1 (w.f t) (w.noise t)) := by
  rw [modeO_succ, hW]
  rfl

end Rec

end AdversarialBco.Unified.Eng
