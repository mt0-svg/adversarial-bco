/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk

@[expose] public section

/-!
# UNI-POLY, part 5: `PLAYB`, the play of `P`

* `ptAt_nrm`: the normalised buffer holds the same point as `P`'s cells.
* `rs_PLAYB`: `play src` of `P`: the memory unchanged, one round more, the point of `P` played.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

/-- The normalised buffer holds the point of `P`. -/
theorem ptAt_nrm (Pm m : ℤ → ℤ) (a YB : ℤ)
    (hm : ∀ c, YB ≤ c → c ≤ YB + d → m c = nrm (Pm a) (Pm (a + (c - YB))) (c - YB)) :
    ptAt d m YB = ptAt d Pm a := by
  funext i
  have hid := i.2
  simp only [ptAt]
  rw [hm YB le_rfl (by omega), hm (YB + 1 + (i : ℕ)) (by omega) (by omega)]
  have e1 : YB + 1 + ((i : ℕ) : ℤ) - YB = 1 + (i : ℕ) := by ring
  have e2 : a + (1 + ((i : ℕ) : ℤ)) = a + 1 + (i : ℕ) := by ring
  simp only [sub_self, add_zero, e1, e2, nrm]
  by_cases h0 : Pm a = 0
  · simp only [h0, ↓reduceIte, show ¬ (1 + ((i : ℕ) : ℤ) = 0) by omega, Int.cast_zero, Int.cast_one, div_zero,
      zero_div]
  · by_cases hn : Pm a < 0
    · simp only [h0, hn, ↓reduceIte, Int.cast_neg, neg_div_neg_eq]
    · simp only [h0, hn, ↓reduceIte]

/-- The value of the normalised buffer is no longer than `1` and the entry. -/
theorem len_nrm_le (y0 yj j : ℤ) {L : ℕ} (h1 : 1 ≤ L) (hy : len yj ≤ L) : len (nrm y0 yj j) ≤ L := by
  unfold nrm
  split_ifs
  · rw [len_one]; exact h1
  · rw [len_zero]; omega
  · unfold len; rw [Int.natAbs_neg]; exact hy
  · exact hy

/-- `PLAYB src`: `play src` of `P`, with the buffer and the scratch cells back at `0`. -/
theorem rs_PLAYB {src a YB : ℤ} (ha : t.mem (φ src) = a) (hYB1 : 1 ≤ YB) (hYB : t.mem cYB = YB)
    (hd : t.mem 0 = d) (hz : t.mem cZ = 0) (hAa : t.mem cAa = 0) (hOne : t.mem cOne = 0) (hD1 : t.mem cD1 = 0)
    (hA : t.mem cA = 0) (hC : t.mem cC = 0) (hY0 : t.mem cY0 = 0) (hSg : t.mem cSg = 0) (hI : t.mem cI = 0)
    (hX : t.mem cX = 0) (hV : t.mem cV = 0) (hB : t.mem cB = 0)
    (hYz : ∀ c, YB ≤ c → c ≤ YB + d → t.mem c = 0)
    (hLs : len src + 11 ≤ L) (hLa : ∀ j : ℕ, j ≤ d → len (a + j) + 11 ≤ L)
    (hLy : ∀ j : ℕ, j ≤ d → len (t.mem (φ (a + j))) ≤ L)
    (hLY : len (YB + d) ≤ L) (hLd : len ((d : ℤ) + 1) ≤ L) (h10 : 10 ≤ L) :
    RS w L (PLAYB src) t (fun n t' => n ≤ (d + 1) * 25 + 60 ∧ t'.mem = t.mem ∧ t'.coins = t.coins ∧
      t'.rounds = t.rounds + 1 ∧
      t'.pts = Function.update t.pts t.rounds (ptAt d (fun x => t.mem (φ x)) a)) := by
  have hYB0 : 0 ≤ YB := by omega
  unfold PLAYB; simp only [seqL]
  refine RS.seq (rs_COPYN ha hYB0 hYB hd hz hAa hOne hD1 hA hC hY0 hSg hI hX hV hB hYz hLs hLa hLy hLY hLd h10) ?_
  rintro n₁ t₁ ⟨hn₁, m₁, s₁⟩
  have hout : ∀ c, ¬ (YB ≤ c ∧ c ≤ YB + d) → t₁.mem c = t.mem c := fun c hc => by
    rw [m₁]; simp only [hc, ↓reduceIte]
  have e (c : ℤ) (hc : c < 0) : t₁.mem c = t.mem c := hout c (by omega)
  have hY0L : len YB ≤ L := (len_mono hYB0 (by omega)).trans hLY
  refine RS.seq (RS.ins (Q := fun n t₂ => n = 1 ∧ t₂ = stepI w (.play cYB) t₁)
    ⟨len_scr (by decide) (by decide) h10, by rw [e cYB (by decide), hYB]; exact hY0L, fun i hi => ⟨?_, ?_⟩⟩
    ⟨rfl, rfl⟩) ?_
  · rw [e cYB (by decide), hYB]; exact (len_mono (by omega) (by omega)).trans hLY
  · rw [e cYB (by decide), hYB, m₁]
    simp only [show YB ≤ YB + (i : ℤ) ∧ YB + (i : ℤ) ≤ YB + d by omega, ↓reduceIte]
    exact len_nrm_le _ _ _ (by omega) (by rw [show YB + (i : ℤ) - YB = i by ring]; exact hLy i hi)
  rintro n₂ t₂ ⟨rfl, rfl⟩
  refine (rs_CLEARY (YB := YB) (by simp [e _ (by decide : cZ < 0), hz]) (by rw [stepI_play_mem, hout 0 (by omega), hd])
    (by simp [e _ (by decide : cYB < 0), hYB]) hYB0 (by simp [e _ (by decide : cOne < 0), hOne])
    (by simp [e _ (by decide : cD1 < 0), hD1]) (by simp [e _ (by decide : cI < 0), hI])
    (by simp [e _ (by decide : cB < 0), hB]) hLY hLd h10).mono ?_
  rintro n₃ t₃ ⟨hn₃, m₃, s₃⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [m₃, stepI_play_mem]
    funext c
    by_cases hc : YB ≤ c ∧ c ≤ YB + d
    · simp only [hc, and_self, ↓reduceIte]; exact (hYz c hc.1 hc.2).symm
    · simp only [hc, ↓reduceIte]; exact hout c hc
  · rw [s₃.1, stepI_play_coins, s₁.1]
  · rw [s₃.2.1, stepI_play_rounds, s₁.2.1]
  · rw [s₃.2.2, stepI_play_pts, s₁.2.2, s₁.2.1, e cYB (by decide), hYB]
    congr 1
    refine ptAt_nrm _ _ a YB fun c h1 h2 => ?_
    rw [m₁]; simp only [h1, h2, and_self, ↓reduceIte]

end AdversarialBco.UniPoly
