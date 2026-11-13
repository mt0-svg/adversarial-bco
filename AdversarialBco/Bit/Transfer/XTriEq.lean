/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriM

@[expose] public section

/-!
# TRI-M, the integer model against the rational position

The scan of the rows at `ẑ` is `triUQ` at `z`, the update at the grid is `triClipQ` of the rounded step, the stage rows
read in the stage position, and the iterates, stages and the position of `tzPos` against `triPosQ`.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.tzKeep_triU {d M : ℕ} (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ)
    (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (z : Fin d → ℤ) :
    0 < (tzKeep T mu ra rb M z).bb ∧
    triUQ (fun k : Fin M => (T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (ra k i : ℚ))
        (fun k : Fin M => ((rb k - ra k ⬝ᵥ mu : ℤ) : ℚ)) (fun i => (z i : ℚ)) =
      fun i => (((Tᵀ *ᵥ (tzKeep T mu ra rb M z).row) i : ℤ) : ℚ) / (tzKeep T mu ra rb M z).bb := by
  have hK : tzKeep T mu ra rb M z =
      scan (fun k => ra k ⬝ᵥ (T *ᵥ z)) (fun k => rb k - ra k ⬝ᵥ mu) ra M := rfl
  generalize hN : (fun k => ra k ⬝ᵥ (T *ᵥ z)) = N at hK
  generalize hB : (fun k => rb k - ra k ⬝ᵥ mu) = B at hK
  obtain ⟨hpos, hsum⟩ := scan_spec N B ra M
  rw [hK]
  refine ⟨hpos, ?_⟩
  set Tq := T.map (Int.cast : ℤ → ℚ) with hTq
  have hq : ∀ k : Fin M, triQQ (fun k : Fin M => Tqᵀ *ᵥ fun i => (ra k i : ℚ))
      (fun k : Fin M => ((rb k - ra k ⬝ᵥ mu : ℤ) : ℚ)) k (fun i => (z i : ℚ)) = (N k : ℚ) / B k := by
    intro k
    unfold triQQ
    rw [← hN, ← hB]
    congr 1
    show (Tqᵀ *ᵥ fun i => (ra k i : ℚ)) ⬝ᵥ (fun i => (z i : ℚ)) = ((ra k ⬝ᵥ (T *ᵥ z) : ℤ) : ℚ)
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    have h1 := RingHom.map_dotProduct (Int.castRingHom ℚ) (ra k) (T *ᵥ z)
    simp only [eq_intCast] at h1
    rw [h1]
    congr 1
    ext i
    have h2 := RingHom.map_mulVec (Int.castRingHom ℚ) T z i
    simp only [eq_intCast] at h2
    rw [Function.comp_apply, eq_intCast, h2]
    rfl
  have hR : (fun i => (((Tᵀ *ᵥ (scan N B ra M).row) i : ℤ) : ℚ) / (scan N B ra M).bb) =
      Tqᵀ *ᵥ fun i => ((scan N B ra M).row i : ℚ) / (scan N B ra M).bb := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hTq, Matrix.map_apply]
    push_cast
    rw [Finset.sum_div]
    congr 1
    ext l
    ring
  rw [hR, hsum, Matrix.mulVec_sum, Finset.sum_range]
  unfold triUQ
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hq]
  have hc : (0 < (N k : ℚ) / B k ∧ (∀ k' : Fin M, (N k' : ℚ) / B k' ≤ (N k : ℚ) / B k) ∧
      (∀ k' : Fin M, k' < k → (N k' : ℚ) / B k' < (N k : ℚ) / B k)) ↔
      (0 < (N k : ℚ) / B k ∧ (∀ j < M, (N j : ℚ) / B j ≤ (N k : ℚ) / B k) ∧
        (∀ j < (k : ℕ), (N j : ℚ) / B j < (N k : ℚ) / B k)) := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, fun j hj => h1 ⟨j, hj⟩, fun j hj => h2 ⟨j, lt_trans hj k.2⟩ (Fin.mk_lt_mk.2 hj)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, fun k' => h1 k' k'.2, fun k' hk' => h2 k' (Fin.lt_def.1 hk')⟩
  have hBk : (((rb k - ra k ⬝ᵥ mu : ℤ)) : ℚ) = B k := by rw [← hB]
  split_ifs with h1 h2 h2
  · rw [Matrix.mulVec_smul, hBk]
  · exact absurd (hc.1 h1) h2
  · exact absurd (hc.2 h2) h1
  · rw [Matrix.mulVec_zero]
