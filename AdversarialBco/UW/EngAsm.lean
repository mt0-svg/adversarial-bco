/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EngRecDefs
public import AdversarialBco.Unified.EngAsm

@[expose] public section

/-!
# Step 1 of SHADOW for BL-OW's record: the assembly

Unified/EngAsm.lean for BL-OW: from `IndOW` and `RoundBndOW` (UW/EngRecDefs.lean) and Theorem BUD-W at `k_δ` and
PARAM-W's reference (`budW`, in the regime `RegRefW` of the reference), `EngineRecUW (implW P C' k)` holds with
`κ0 = κ1 = kapO` of `rW d n δ`: the shift clause is `RoundBndOW` in `IND(t)`, the regret clause sums its loss gap
over the rounds (`n · regO/n = regO ≤ 1`), and `n (κ0 + κ1) ≤ 2^{-k_δ}/8 < δ/8`.
-/

open MeasureTheory

namespace AdversarialBco.UW.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Asm
open AdversarialBco.UW AdversarialBco.UW.BudW AdversarialBco.UW.BLOW

/-- **Step 1 of SHADOW for BL-OW's record** from the induction and the round bounds. -/
theorem engineRecOW_of (hReg : RegRefW) (hInd : IndOW) (hRB : RoundBndOW) (P : List BitRAMO.InstrO) (C' : ℝ)
    (k : ℕ) : EngineRecUW (implW P C' k) := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h
  have hreg := hReg d n δ hI.hd hI.hn hI.hδ0 hI.hδ1 hc
  have hbud : BudOKW d n (kDel δ) (refW d n δ) := budW d n (kDel δ) (refW d n δ) hreg
  have hk := Unified.Eng.two_inv_pow_lt hI.hδ0 hI.hδ1
  refine ⟨(rW d n δ).kapO, (rW d n δ).kapO, hbud.kapO_nonneg, hbud.kapO_nonneg, ?_, ⟨?_, ?_⟩⟩
  · have := hbud.kap_k
    linarith
  · intro ω hq hG hb t ht hD
    exact (hRB d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht
      (hInd d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht.le hD)).1
  · intro ω hq hG hb hD
    show ∑ t ∈ Finset.range n, (recOW n δ r0 R0 a orc h hI.convex).loss ω t
        ((recOW n δ r0 R0 a orc h hI.convex).play t ω) ≤
      ∑ t ∈ Finset.range n, (recOW n δ r0 R0 a orc h hI.convex).loss ω t
        (refPlayU (recOW n δ r0 R0 a orc h hI.convex) (refW d n δ) t ω) + 1
    set B := recOW n δ r0 R0 a orc h hI.convex with hB
    have hround : ∀ t ∈ Finset.range n, B.loss ω t (B.play t ω) ≤
        B.loss ω t (refPlayU B (refW d n δ) t ω) + (rW d n δ).regO / n := by
      intro t ht
      rw [Finset.mem_range] at ht
      exact (hRB d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht
        (hInd d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht.le
          fun u hu => hD u (hu.trans ht))).2
    have hn0 : (n : ℝ) ≠ 0 := by have := hI.hn; positivity
    calc ∑ t ∈ Finset.range n, B.loss ω t (B.play t ω)
        ≤ ∑ t ∈ Finset.range n, (B.loss ω t (refPlayU B (refW d n δ) t ω) + (rW d n δ).regO / n) :=
          Finset.sum_le_sum hround
      _ = ∑ t ∈ Finset.range n, B.loss ω t (refPlayU B (refW d n δ) t ω) + (rW d n δ).regO := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hn0]
      _ ≤ _ := by linarith [hbud.regO_le]

end AdversarialBco.UW.Eng
