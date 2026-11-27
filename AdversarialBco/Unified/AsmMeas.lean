/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmMain
public import AdversarialBco.Unified.RunFacts
public import AdversarialBco.Bit.RegMeas

@[expose] public section

/-!
# UNI-MEAS: the regret is measurable on the environment's space (`RegMeasU`)

`regMeasU : RegMeasU`, the port of Bit/RegMeas.lean's `measurable_regret` to the oracle machine and to a noisy
adversary on any probability space (route Sec. 3.14). The feedback at a state reached with at most `n` rounds is the
loss of the last round at its point, which lies in `K`, plus its noise: measurable in `ω` (`FbMeasO`). So the points of
the rounds `t < n` are measurable with countably many values (M2, `playedO_meas` of Unified/RunFacts.lean), and so is
the tuple of them (`tuple_fibers`). At a fixed tuple `Q` of points of `K` the regret is measurable in `ω`
(`measurable_regQU`): the losses at the points of `K` are, and the infimum over `K` of the sum of the losses, convex
with values in `[0, n]`, is the infimum over the rational points of the interior (`sInf_image_eq_iInf_rat`). The
regret is the regret at the tuple of the run (`measurable_of_countable_fibers`).
-/

open MeasureTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco.BitRAM (toE State)
open AdversarialBco.BitRAMO (InstrO WorldO playedO runO)
open AdversarialBco.RealRAM (regretPts)
open AdversarialBco.Unified.RunFacts (FbMeasO fbO fbO_eq playedO_eq_pts playedO_meas)
open AdversarialBco.Bit.RegMeas (extQ tuple_fibers)

/-- The regret at a fixed tuple of points of `K` is measurable in `ω` when the losses are admissible and measurable at
the points of `K`. -/
theorem measurable_regQU {d n : ℕ} (K : Set (E d)) (hK : (interior K).Nonempty) {Ω : Type} [MeasurableSpace Ω]
    {loss : ℕ → Ω → E d → ℝ} (hadm : ∀ t < n, ∀ ω, AdmLoss K (loss t ω))
    (hm : ∀ t < n, ∀ y ∈ K, Measurable fun ω => loss t ω y) (Q : Fin n → E d) (hQK : ∀ t, Q t ∈ K) :
    Measurable fun ω => regretPts K (fun t => loss t ω) (extQ Q) n := by
  classical
  unfold regretPts
  refine Measurable.sub ?_ ?_
  · refine Finset.measurable_sum _ fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    have hQ : extQ Q t = Q ⟨t, ht'⟩ := by simp [extQ, ht']
    show Measurable fun ω => loss t ω (extQ Q t)
    rw [hQ]
    exact hm t ht' _ (hQK _)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact measurable_const
    have key : ∀ ω, sInf ((fun y => ∑ t ∈ Finset.range n, loss t ω y) '' K) =
        ⨅ q : Fin d → ℚ, if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ interior K then
          ∑ t ∈ Finset.range n, loss t ω (WithLp.toLp 2 (fun i => (q i : ℝ))) else (n : ℝ) := by
      intro ω
      have hKc : Convex ℝ K := (hadm 0 hn ω).1.1
      have hcv := Poly.PropGAd.convexOn_sum_range K hKc n (fun t => loss t ω) (fun t ht => (hadm t ht ω).1)
        (fun t ht => (hadm t ht ω).2)
      exact Poly.PropGAd.sInf_image_eq_iInf_rat K hK _ hcv.1 n hcv.2
    simp only [key]
    refine Measurable.iInf fun q => ?_
    split_ifs with hq
    · exact Finset.measurable_sum _ fun t ht => hm t (Finset.mem_range.mp ht) _ (interior_subset hq)
    · exact measurable_const

/-- **UNI-MEAS.** -/
theorem regMeasU : RegMeasU := by
  intro P d n K hK s0 hs0 orc Ω _ μ coin loss noise D D' hA hplay
  set g : Ω → WorldO d := fun ω => envWorld orc coin loss noise ω with hg
  have hcs : ∀ j, Measurable fun ω => (g ω).cs j := fun j => (measurable_pi_apply j).comp hA.coin_meas
  have hfb : FbMeasO P g s0 n := by
    intro k ω0 hk
    set s := runO P (g ω0) s0 k with hs
    by_cases h0 : s.rounds = 0
    · have : (fun ω => fbO (g ω) s) = fun _ => 0 := funext fun ω => by simp only [fbO_eq, h0, ↓reduceIte]
      rw [this]
      exact measurable_const
    · have hr : s.rounds - 1 < n := by omega
      have hpt : toE (s.pts (s.rounds - 1)) ∈ K := by
        rw [← playedO_eq_pts P (g ω0) s0 (by omega : s.rounds - 1 < s.rounds)]
        exact hplay ω0 _ hr
      have : (fun ω => fbO (g ω) s) =
          fun ω => loss (s.rounds - 1) ω (toE (s.pts (s.rounds - 1))) + noise (s.rounds - 1) ω :=
        funext fun ω => by simp only [fbO_eq, h0, ↓reduceIte]; rfl
      rw [this]
      exact (hA.loss_meas _ hr _ hpt).add (hA.noise_meas _ hr)
  have hX := tuple_fibers (X := fun (t : Fin n) (ω : Ω) => playedO P (g ω) s0 t)
    (fun t => (playedO_meas orc (fun _ => rfl) hcs hfb hs0 t.2).1)
    (fun t v => (playedO_meas orc (fun _ => rfl) hcs hfb hs0 t.2).2 v)
  have key : (fun ω => regretU P K n s0 (envWorld orc coin loss noise ω)) =
      fun ω => (fun (Q : Fin n → E d) (ω : Ω) => regretPts K (fun t => loss t ω) (extQ Q) n)
        ((fun ω (t : Fin n) => playedO P (g ω) s0 t) ω) ω := by
    funext ω
    exact Bit.Asm.regretPts_congr (fun t _ => rfl) (fun t ht => by simp [extQ, ht, g])
  rw [key]
  refine RunFacts.measurable_of_countable_fibers (Y := ℝ)
    (G := fun (Q : Fin n → E d) (ω : Ω) => regretPts K (fun t => loss t ω) (extQ Q) n) hX.1 (fun q _ => hX.2 q) ?_
  rintro Q ⟨ω0, rfl⟩
  exact measurable_regQU K hK hA.adm hA.loss_meas _ (fun t => hplay ω0 t t.2)

end AdversarialBco.Unified.Asm
