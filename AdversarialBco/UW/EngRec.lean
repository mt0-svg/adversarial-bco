/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngRecDefs
public import AdversarialBco.UW.EngVE
public import AdversarialBco.Unified.EngInd

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the record's identities

Unified/EngRec.lean for BL-OW's record `recOW` (UW/EngRecDefs.lean) and P° of Theorem UW at PARAM-W's reference
`ρ = refW d n δ`. With `w` the environment's world at `ω` and `c = cfgWW .. w` BL-OW's configuration:

* the losses and noises of the rounds `t < n` are the environment's (`loss_eqW`, `nz_eqW`); BL-OW's reading in mode
  `run` is `obsO` (`readOW_eq`, `modeOW_succ_run`);
* P°'s unweighted observation of round `t` at its mode `.run so` is the record's `refYOW` (`refYOW_eqU`); when the
  round does not decouple, it is BL-OW's exact observation `YcO` (`refYOW_coupled`, the algebra `y_alg'`).
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.Unified.Eng (xO obsO y_alg')
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW
open AdversarialBco.Bit.BLP (St)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)

variable {d : ℕ}

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

theorem loss_eqW (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (ω : Ω × (ℕ → ℝ)) {t : ℕ} (ht : t < n) :
    (recOW n δ r0 R0 a orc h hK).loss ω t = (envWorld orc coin loss noise ω.1).f t := by
  show (lossProcE (winO h) (extO_ok n δ r0 R0 a h) hK).L t
    ((lossProcE (winO h) (extO_ok n δ r0 R0 a h) hK).lam t ω) = _
  simp only [lossProcE, ht, ↓reduceDIte]
  try rfl

theorem nz_eqW (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (ω : Ω × (ℕ → ℝ))
    {t : ℕ} (ht : t < n) : (extO n δ r0 R0 a h).nz t ω = (envWorld orc coin loss noise ω.1).noise t :=
  Unified.Eng.nz_eq (orc := orc) h ω ht

/-- BL-OW's reading in mode `run st` is `obsO`. -/
theorem readOW_eq (w : BitRAMO.WorldO d) {t : ℕ} {st : St d} (hW : modeOW d n δ r0 R0 a w t = .run st) :
    readOW d n δ r0 R0 a w t =
      obsO w.orc (cfgWW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1 (w.f t) (w.noise t) := by
  unfold readOW obsO playOW
  rw [hW]
  rfl

/-- BL-OW's next mode in mode `run st` is `stepOW` at the reading `obsO`. -/
theorem modeOW_succ_run (w : BitRAMO.WorldO d) {t : ℕ} {st : St d} (hW : modeOW d n δ r0 R0 a w t = .run st) :
    modeOW d n δ r0 R0 a w (t + 1) = stepOW (b0OW d n δ) (y0OW d n δ) w.orc (cfgWW d n δ r0 R0 a w) n (.run st)
      (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2
      (obsO w.orc (cfgWW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1 (w.f t) (w.noise t)) := by
  rw [modeOW_succ, hW, readOW_eq w hW]

set_option hygiene false in
local notation "BB" => recOW n δ r0 R0 a orc h hK
set_option hygiene false in
local notation "WE" => extO n δ r0 R0 a h
set_option hygiene false in
local notation "WW" => envWorld orc coin loss noise ω.1
set_option hygiene false in
local notation "CC" => cfgWW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)
set_option hygiene false in
local notation "RF" => refW d n δ

/-- `refPlayU_run` at P°'s parameters `poW d n δ`. -/
theorem refPlayU_runW (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
    (hK : Convex ℝ K) (hreg : RegimeW d n RF) {ω : Ω × (ℕ → ℝ)} (hq : (BB).Case (RF).δc ω) {t : ℕ} {so : Df2St d}
    (hmo : modeU BB RF t ω = .run so) :
    refPlayU BB RF t ω = pgMu ((BB).pos ω) + pgOp ((BB).pos ω)
      ((Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))))⁻¹ •
        WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))) ∧
    refPlayU BB RF t ω ∈ interior K :=
  refPlayU_run hK hq (EvP.eps_pos hreg) (EvP.eps_lt_one hreg) hmo

/-- P°'s unweighted observation of round `t < n` at its mode `.run so`, on `Case`: the record's `refYOW`. -/
theorem refYOW_eqU (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (hreg : RegimeW d n RF) {ω : Ω × (ℕ → ℝ)} (hq : (BB).Case (RF).δc ω) {t : ℕ} (ht : t < n) {so : Df2St d}
    (hmo : modeU BB RF t ω = .run so) :
    refYOW n δ r0 R0 a orc h hK t ω so =
      Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))) *
        ((BB).loss ω t (pgMu ((BB).pos ω) + pgOp ((BB).pos ω)
            ((Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
              (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))))⁻¹ •
              WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω)))) / 2 +
          ((WE).nz t ω + (BB).zeta t ω (modeU BB RF t ω)) / 2) +
      2 * (Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))) - 1) / (poW d n δ).eps := by
  obtain ⟨hrp, hint⟩ := refPlayU_runW h hK hreg hq hmo
  rw [hrp] at hint
  rw [hmo]
  have e : refYOW n δ r0 R0 a orc h hK t ω so =
      Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))) *
        ((if t < n then fL K (BB).F.L t ((BB).F.lam t ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2
              ((Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
                (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))))⁻¹ •
                (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))))) +
          (WE).nz t ω + (BB).zeta t ω (.run so)) / 2 +
      2 * (Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps
          (WithLp.toLp 2 (so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω))) - 1) /
        (poW d n δ).eps := rfl
  rw [e, if_pos ht, WithLp.toLp_smul, fL_interior hint]
  have hl : (BB).F.L t ((BB).F.lam t ω) = (BB).loss ω t := rfl
  rw [hl]
  ring

/-- When round `t < n` does not decouple, P°'s unweighted observation at its mode `.run so` is BL-OW's exact
observation `YcO` with the noise. -/
theorem refYOW_coupled (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
    (hK : Convex ℝ K) (hreg : RegimeW d n RF) {ω : Ω × (ℕ → ℝ)} (hq : (BB).Case (RF).δc ω) {t : ℕ} (ht : t < n)
    {so : Df2St d} {st : St d} (hmo : modeU BB RF t ω = .run so) (hW : modeOW d n δ r0 R0 a WW t = .run st)
    (hD : ¬ DU BB RF t ω) :
    refYOW n δ r0 R0 a orc h hK t ω so =
      YcO orc CC st (drawO d n δ r0 R0 (coin ω.1) t).1 ((WE).zz t ω 0) ((WE).nz t ω) ((BB).loss ω t) := by
  have hD' : (BB).zeta t ω (modeU BB RF t ω) =
      (shRU BB RF t ω).1 + (shRU BB RF t ω).2 * (WE).zz t ω 0 / 2 := not_not.mp hD
  rw [refYOW_eqU h hK hreg hq ht hmo, hD']
  obtain ⟨hrp, hint⟩ := refPlayU_runW h hK hreg hq hmo
  rw [hrp] at hint
  set X : Fin d → ℝ := so.mu + (1 - (poW d n δ).lam) • (so.A *ᵥ (WE).xi t ω) with hX
  set PTO := Bit.BLP.EngL.ptE (kTh n (RF).δc K ((BB).pos ω)) (poW d n δ).eps (WithLp.toLp 2 X) with hPTO
  set PT1 : ℝ := (ptO orc CC (XO CC st (drawO d n δ r0 R0 (coin ω.1) t).1) : ℝ) with hPT1
  have hp0 : 0 < PTO := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hpl : playOW d n δ r0 R0 a WW t = playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) t).1 := by
    unfold playOW
    rw [hW]
    rfl
  unfold YcO
  refine y_alg' hp0.ne' ?_ ?_
  · show (shOW n δ r0 R0 a orc h hK t ω (modeU BB RF t ω)).2 = _
    rw [hmo]
    unfold shOW
    rw [if_pos ht, hW]
    all_goals rfl
  · have e1 : (shRU BB RF t ω).1 = (PT1 / PTO - 1) * (WE).nz t ω +
        (PT1 * (BB).F.L t ((BB).F.lam t ω) (toE (playOW d n δ r0 R0 a WW t)) -
          PTO * (if t < n then fL K (BB).F.L t ((BB).F.lam t ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2 (PTO⁻¹ • X))) +
          4 * (PT1 - 1) / ((CC).par.eps : ℝ) - 4 * (PTO - 1) / (poW d n δ).eps) / PTO := by
      show (shOW n δ r0 R0 a orc h hK t ω (modeU BB RF t ω)).1 = _
      rw [hmo]
      unfold shOW
      rw [if_pos ht, hW]
      all_goals rfl
    rw [e1, if_pos ht, WithLp.toLp_smul, fL_interior hint, hpl]
    rfl

end Rec

end AdversarialBco.UW.Eng
