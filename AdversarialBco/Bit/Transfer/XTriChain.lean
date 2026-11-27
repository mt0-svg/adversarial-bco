/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriUpdEq
public import AdversarialBco.Bit.Transfer.XTriAux

@[expose] public section

/-!
# TRI-M, the integer model of a draw against the rational one

* `triDrawQ_eq`: a draw of BM-INT as `tzY` over `2^{2 p}`;
* `tzUpd_step`: one clipped step of the rational stage as the integer update `tzUpd` at the grid `2^{-G}`.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.triDrawQ_eq (d B : ℕ) (x : ℕ → Bool) (t : ℕ) :
    triDrawQ d B x t = fun i => (tzY d B x t i : ℚ) / 2 ^ (2 * gsm_prec B) := by
  funext i
  simp [triDrawQ, tzY]

theorem AdversarialBco.Bit.TriM.tzUpd_step {d : ℕ} (hd : 1 ≤ d) (Bv Js ja p La G : ℕ) (hG : G = Bv + Js + ja)
    (hLa : 10 ≤ La) (X : PosZ d) (hdiag : ∀ i, 0 < X.2 i i) (A Y : Fin d → ℤ) (Bb : ℤ) (hBb : 0 < Bb)
    (x : PosQ d) (hx : x = (fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G))
    (y : Fin d → ℚ) (hy : y = fun i => (Y i : ℚ) / 2 ^ (2 * p))
    (u : (Fin d → ℚ) → Fin d → ℚ) (hu : u (x.1 + x.2 *ᵥ y) = fun i => (A i : ℚ) / Bb)
    (c : DC) (hc : c = ⟨2 ^ Bv, 2 ^ (2 * p), 2 ^ G, 2 ^ ja, 2 ^ (La - 3 + G), 2 ^ (Bv + Js),
      161 * 2 ^ (La - 10 + G), d⟩) :
    triClipQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (x - (1 / 2 ^ Js : ℚ) • triRoundQ Bv (triVQ u x y)) =
      (fun i => ((tzUpd c X A Y Bb).1 i : ℚ) / 2 ^ G, fun i l => ((tzUpd c X A Y Bb).2 i l : ℚ) / 2 ^ G) := by
  unfold triVQ
  rw [hu]
  subst hx hy hc hG
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun l => ?_)
  · have e1 : ∀ (z w : PosQ d) (s : ℚ), (z - s • w).1 i = z.1 i - s * w.1 i := fun _ _ _ => rfl
    simp only [triClipQ]
    refine (congrArg₂ max rfl (congrArg₂ min rfl (e1 _ _ _))).trans ?_
    simp only [triLoQ, triHiQ, triRoundQ, tzUpd, tzRMu]
    exact upd_mu Bv Js ja La hLa (X.1 i) (A i) Bb hBb
  · have e2 : ∀ (z w : PosQ d) (s : ℚ), (z - s • w).2 i l = z.2 i l - s * w.2 i l := fun _ _ _ => rfl
    simp only [triClipQ]
    refine (congrArg₂ max rfl (congrArg₂ min rfl (e2 _ _ _))).trans ?_
    simp only [triLoQ, triHiQ, triRoundQ, tzUpd, tzRLow, tzRDiag]
    rcases lt_trichotomy l i with hl | rfl | hl
    · simp only [hl, hl.le, ne_of_gt hl, ↓reduceIte, sub_zero]
      exact upd_low Bv Js ja La p hLa (X.2 i l) (A i) (Y l) Bb hBb
    · simp only [lt_irrefl, le_refl, ↓reduceIte]
      exact upd_diag d hd Bv Js ja La p hLa (X.2 l l) (A l) (Y l) Bb hBb (hdiag l)
    · have h1 : ¬ l < i := not_lt.mpr hl.le
      have h2 : ¬ l ≤ i := not_le.mpr hl
      have h3 : i ≠ l := ne_of_lt hl
      have h4 : l ≠ i := (ne_of_lt hl).symm
      simp only [h1, h2, h3, h4, ↓reduceIte, Int.cast_zero, zero_div]
      exact max_eq_left (min_le_left _ _)

