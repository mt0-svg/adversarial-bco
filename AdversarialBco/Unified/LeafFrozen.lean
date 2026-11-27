/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAMO
public import AdversarialBco.Unified.LeafReal
public import AdversarialBco.Unified.LeafCM
public import AdversarialBco.Unified.LeafLift

@[expose] public section

/-!
# Leaves of the unified route on the frozen oracle machine

The leaves of LeafReal.lean, LeafCM.lean and LeafLift.lean restated on the definitions of StatementBitRAMO.lean
(namespace `AdversarialBco.BitRAMO`), where they differ from an earlier draft of the machine:

* `uni_liftO`: `LiftOK` for the frozen machine, from `uni_lift_gen` (the frozen `stepO` reads `clip q (reading ...)`
  and costs the clipped reading differently from the draft, which the lift does not see).
* `uni_clip_readO`, `uni_clip_lenO`: the clipped reading `clip q ⌊2^p o⌋` of instruction `obsR`, with the range `q`
  read from its own cell (the draft clipped to `2^(p+r)`).
* `uni_cm_weakMem`: UNI-CM (a) and (b) for an oracle with `WeakMemOracle K orc`, queried at a rational point `q` with
  `toE q = a + (1 + 2·2^{-k}/r₀)(y - a)`: an accept puts `y` in the interior of `K`, a reject puts the gauge of `y`
  above `1 - 3·2^{-k}/r₀`.
-/

open Metric

namespace AdversarialBco.Uni

open BitRAM BitRAMO

/-- UNI-MACH on the frozen machine: a run of the oracle machine whose lowered run ends inside the code made no query
and no clipped reading; it is the run of the bit machine on the lowered program. -/
theorem uni_liftO {d : ℕ} (P : List BitRAMO.InstrO) (w : BitRAMO.WorldO d) (s : State d) (k : ℕ)
    (hpc : (run (BitRAMO.lowerP P) w.toW s k).pc < P.length) :
    BitRAMO.runO P w s k = run (BitRAMO.lowerP P) w.toW s k := by
  refine uni_lift_gen P (BitRAMO.lowerI P.length) w.toW (BitRAMO.stepO P w) (fun s h => ?_)
    (fun s i h => ?_) s k hpc
  · unfold BitRAMO.stepO
    rw [h]
  · cases i with
    | base i =>
      left
      unfold BitRAMO.stepO
      rw [h]
      rfl
    | orc dst src prec => exact Or.inr rfl
    | obsR dst prec rng => exact Or.inr rfl

/-- UNI-OBS on the frozen machine: when `2^p |o| ≤ 2^q` the clip does not act on the reading `⌊2^p o⌋`, which is within
`2^{-p}` of `o`. -/
theorem uni_clip_readO (o : ℝ) (p q : ℕ) (ho : (2 : ℝ) ^ p * |o| ≤ 2 ^ q) :
    BitRAMO.clip q ⌊(2 : ℝ) ^ p * o⌋ = ⌊(2 : ℝ) ^ p * o⌋ ∧
      |(⌊(2 : ℝ) ^ p * o⌋ : ℝ) / 2 ^ p - o| ≤ (2 : ℝ)⁻¹ ^ p :=
  uni_clip_read_q o p q ho

/-- UNI-OBS on the frozen machine: the clipped reading has at most `q + 1` bits. -/
theorem uni_clip_lenO (v : ℤ) (q : ℕ) : len (BitRAMO.clip q v) ≤ q + 1 :=
  uni_clip_len_q v q

/-- UNI-CM (a) and (b) for a weak membership oracle of the frozen statement, queried once at the rational point `q`
with `toE q = a + (1 + 2·2^{-k}/r₀)(y - a)`. -/
theorem uni_cm_weakMem {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (a y : E d) (r0 : ℝ) (hr0 : 0 < r0)
    (hball : closedBall a r0 ⊆ K) (orc : (Fin d → ℚ) → ℕ → Bool) (horc : WeakMemOracle K orc)
    (q : Fin d → ℚ) (k : ℕ) (hq : toE q = a + (1 + 2 * (2 : ℝ)⁻¹ ^ k / r0) • (y - a)) :
    (orc q k = true → y ∈ interior K) ∧
      (orc q k = false → 1 - 3 * (2 : ℝ)⁻¹ ^ k / r0 < sInf {t : ℝ | 0 < t ∧ a + t⁻¹ • (y - a) ∈ K}) := by
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨z, hzK, hz⟩ := (horc q k).1 h
    refine uni_worc_accept K hK a y r0 _ hr0 hε hball ?_
    rw [← hq]
    exact (infDist_le_dist_of_mem hzK).trans hz
  · have hrej := (horc q k).2 h
    rw [hq] at hrej
    exact uni_cm_reject K hK a y r0 _ hr0 hε hball hrej

end AdversarialBco.Uni
