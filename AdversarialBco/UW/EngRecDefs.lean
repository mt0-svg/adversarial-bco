/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngDefs
public import AdversarialBco.UW.ProgRec

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the induction and the round bounds

The section `Rec` of Unified/EngDefs.lean for BL-OW's record and P° of Theorem UW at PARAM-W's reference
`ρ = refW d n δ` (UW/ProgRec.lean):

* `recOW`: BL-OW's run record, `recUW` at BL-OW's data; it reads neither the program text nor its cost constants, so
  `recUW (implW P C' k) = recOW`, by definition;
* `EngInvOW` (`IND(t)`): before round `t` both learners are in mode `run` on one virtual
  epoch of P° started before a round `a0` at a fresh mode, continued on its weighted path through its rounds
  `< t - a0`, with `TrackW` between BL-OW's state and P°'s;
* `IndOW`: `IND(t)` before the first decoupling on `Case ∩ Ω_ref ∩ E_bits`, at every round `t ≤ n`;
* `RoundBndOW`: the shift and the regret of a round in `IND(t)`, with `κ = kapO` and the loss gap `regO/n` of
  Theorem BUD-W at `rW d n δ`.
-/

open MeasureTheory

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW
open AdversarialBco.Bit.BLP (St)

variable {d : ℕ}

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- BL-OW's run record on the extension. -/
noncomputable abbrev recOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) :
    RunW d n K (extO n δ r0 R0 a h) :=
  recUW (implW [] 0 0) n δ r0 R0 a orc h hK

/-- **`IND(t)`** on BL-OW's record: before round `t` both learners are in mode `run` on one virtual epoch of P°
started before a round `a0` at a fresh mode and continued on its weighted path through its rounds `< t - a0`, with
`TrackW` between BL-OW's state and P°'s. -/
def EngInvOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    (ω : Ω × (ℕ → ℝ)) (t : ℕ) : Prop :=
  ∃ a0 s : ℕ, ∃ st : St d, a0 + s = t ∧
    modeU (recOW n δ r0 R0 a orc h hK) (refW d n δ) a0 ω = .run (df2Init (poW d n δ) d) ∧
    (∀ u < s, (ctxU (recOW n δ r0 R0 a orc h hK) (refW d n δ) a0 ω).cont
      (epU (recOW n δ r0 R0 a orc h hK) (refW d n δ) a0 ω) u) ∧
    modeOW d n δ r0 R0 a (envWorld orc coin loss noise ω.1) t = .run st ∧
    TrackW d n δ st ((ctxU (recOW n δ r0 R0 a orc h hK) (refW d n δ) a0 ω).st
      (epU (recOW n δ r0 R0 a orc h hK) (refW d n δ) a0 ω) s) s

end Rec

/-- **The regime of PARAM-W's reference in the case** (the first clause of `SchedUW`). -/
def RegRefW : Prop :=
  ∀ (d n : ℕ) (δ : ℚ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < 1 → RunCaseUW d n δ → RegimeW d n (refW d n δ)

theorem regRefW_of_sched {P : List BitRAMO.InstrO} {C' : ℝ} {k : ℕ} (h : SchedUW (implW P C' k)) : RegRefW :=
  fun d n δ hd hn h0 h1 hc => (h d n δ hd hn h0 h1 hc).1

/-- **`IND(t)` before the first decoupling** on `Case ∩ Ω_ref ∩ E_bits`, at every round `t ≤ n`. -/
def IndOW : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
      (ω : Ω × (ℕ → ℝ)),
      (recOW n δ r0 R0 a orc h hI.convex).Case (refW d n δ).δc ω →
      GoodU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) ω →
      ω ∈ (recOW n δ r0 R0 a orc h hI.convex).bits →
      ∀ t ≤ n, (∀ u < t, ¬ DU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) u ω) →
        EngInvOW n δ r0 R0 a orc h hI.convex ω t

/-- **The shift and the regret of a round** in `IND(t)` on `Case ∩ Ω_ref ∩ E_bits`: `r > 0` and
`tvB(m, r) ≤ κ + κ |ε_t|` with `κ = kapO` of Theorem BUD-W, and BL-OW's loss exceeds P°'s by at most `regO/n`. -/
def RoundBndOW : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (orc : (Fin d → ℚ) → ℕ → Bool)
    (hI : InpU n δ r0 R0 a K orc), RunCaseUW d n δ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (coin : Ω → ℕ → Bool) (loss : ℕ → Ω → E d → ℝ)
      (noise : ℕ → Ω → ℝ) (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise)
      (ω : Ω × (ℕ → ℝ)),
      (recOW n δ r0 R0 a orc h hI.convex).Case (refW d n δ).δc ω →
      GoodU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) ω →
      ω ∈ (recOW n δ r0 R0 a orc h hI.convex).bits →
      ∀ t < n, EngInvOW n δ r0 R0 a orc h hI.convex ω t →
        (0 < (shRU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) t ω).2 ∧
          tvB (shRU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) t ω).1
              (shRU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) t ω).2 ≤
            (rW d n δ).kapO + (rW d n δ).kapO * |(extO n δ r0 R0 a h).nz t ω|) ∧
        (recOW n δ r0 R0 a orc h hI.convex).loss ω t ((recOW n δ r0 R0 a orc h hI.convex).play t ω) ≤
          (recOW n δ r0 R0 a orc h hI.convex).loss ω t
              (refPlayU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) t ω) +
            (rW d n δ).regO / n

end AdversarialBco.UW.Eng
