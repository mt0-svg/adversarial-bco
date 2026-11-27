/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngDefs

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the assembly

The engine hypothesis for BL-O: from `IndO` and `RoundBndO` (Unified/EngDefs.lean) and Theorem BUD at
`k_δ` (`budAK`), `EngineRecO` holds with `κ0 = κ1 = kapO d n k_δ`: the shift clause is `RoundBndO` in `IND(t)`, the
regret clause sums its loss gap over the rounds (`n · regO/n = regO ≤ 1`), and `n (κ0 + κ1) ≤ 2^{-k_δ}/8 < δ/8`
(`kap_k` of BUD, `1/δ < 2^{k_δ}` by `kDel_bounds`).
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK)

/-- `2^{-k_δ} < δ`. -/
theorem two_inv_pow_lt {δ : ℚ} (h0 : 0 < δ) (h1 : δ < 1) : (2 : ℝ)⁻¹ ^ kDel δ < δ := by
  have hk := (kDel_bounds h0 h1).1
  have hδ : (0 : ℝ) < δ := by exact_mod_cast h0
  rw [one_div] at hk
  rw [inv_pow]
  exact (inv_lt_comm₀ hδ (by positivity)).1 hk

/-- **Step 1 of SHADOW for BL-O's record** from the induction and the round bounds. -/
theorem engineRecO_of (hInd : IndO) (hRB : RoundBndO) : EngineRecO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h
  have hbud : BudOK d n (kDel δ) := BudK.budAK d n (kDel δ) hI.hd hI.hn hc
  have hk := two_inv_pow_lt hI.hδ0 hI.hδ1
  refine ⟨BudK.kapO d n (kDel δ), BudK.kapO d n (kDel δ), hbud.kapO_nonneg, hbud.kapO_nonneg, ?_, ⟨?_, ?_⟩⟩
  · have := hbud.kap_k
    linarith
  · intro ω hq hG hb t ht hD
    exact (hRB d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht
      (hInd d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht.le hD)).1
  · intro ω hq hG hb hD
    set B := recO n δ r0 R0 a orc h hI.convex with hB
    have hround : ∀ t ∈ Finset.range n, B.loss ω t (B.play t ω) ≤
        B.loss ω t (B.refPlay (dBL d n δ) t ω) + BudK.regO d n (kDel δ) / n := by
      intro t ht
      rw [Finset.mem_range] at ht
      exact (hRB d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht
        (hInd d n δ r0 R0 a K orc hI hc Ω μ coin loss noise h ω hq hG hb t ht.le
          fun u hu => hD u (hu.trans ht))).2
    have hn0 : (n : ℝ) ≠ 0 := by have := hI.hn; positivity
    calc ∑ t ∈ Finset.range n, B.loss ω t (B.play t ω)
        ≤ ∑ t ∈ Finset.range n, (B.loss ω t (B.refPlay (dBL d n δ) t ω) + BudK.regO d n (kDel δ) / n) :=
          Finset.sum_le_sum hround
      _ = ∑ t ∈ Finset.range n, B.loss ω t (B.refPlay (dBL d n δ) t ω) + BudK.regO d n (kDel δ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hn0]
      _ ≤ _ := by linarith [hbud.regO_le]

end AdversarialBco.Unified.Eng
