/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.BLRun

@[expose] public section

/-!
# Positions in rationals: the cast into `PgSp d`

`castP`, a rational position `(μ, T)` (`PosQ` of Bit/RoutQ.lean) as a point of `PgSp d` (the packing
`pgPack (toE μ) (cM T)` of `posR`), and its algebra (`castP_injective`, `castP_add`, `castP_sum`, `castP_smul`,
`castP_sub`, `castP_clip`); with it the round, the iterates, the average and the composition of TRI-OGD in rationals
cast to the real ones (`triV_cast`, `triRound_cast`, `triIter_cast`, `triAvg_cast`, `pgComp_cast`).
-/

namespace AdversarialBco.Bit.RQ

open AdversarialBco.Poly
open AdversarialBco.BitRAM (toE readCoins)
open AdversarialBco.Bit.BLP (cM posR Routines blRun betaR)
open AdversarialBco.RealRAM (polytope)
open AdversarialBco.Bit.Asm (InputOK)
open Matrix

variable {d : ℕ}

/-! ## The cast of a rational position -/

/-- A rational position as a point of `PgSp d`. -/
noncomputable def castP (P : PosQ d) : PgSp d := pgPack (toE P.1) (cM P.2)

theorem castP_apply_inl (P : PosQ d) (i : Fin d) : castP P (Sum.inl i) = (P.1 i : ℝ) := rfl

theorem castP_apply_inr (P : PosQ d) (i j : Fin d) : castP P (Sum.inr (i, j)) = (P.2 i j : ℝ) := rfl

theorem castP_injective : Function.Injective (castP (d := d)) := by
  intro P P' h
  have h1 : ∀ i, (P.1 i : ℝ) = P'.1 i := fun i => by
    rw [← castP_apply_inl, ← castP_apply_inl, h]
  have h2 : ∀ i j, (P.2 i j : ℝ) = P'.2 i j := fun i j => by
    rw [← castP_apply_inr, ← castP_apply_inr, h]
  refine Prod.ext (funext fun i => by exact_mod_cast h1 i) (Matrix.ext fun i j => by exact_mod_cast h2 i j)

/-! ## The leaves: each operation of the core commutes with the cast -/

theorem triV_cast (u : (Fin d → ℚ) → Fin d → ℚ) (U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hU : ∀ z, U (toE z) = toE (u z)) (x : PosQ d) (y : Fin d → ℚ) :
    triV U (castP x) (toE y) = castP (triVQ u x y) := by
  have h_center : pgMu (castP x) + pgOp (castP x) (toE y) = toE (x.1 + x.2 *ᵥ y) := by
    calc
      pgMu (castP x) + pgOp (castP x) (toE y) = toE x.1 + pgOp (castP x) (toE y) := by
        rw [castP, pgMu_pgPack]
      _ = toE x.1 + (WithLp.toLp 2 (pgMat (castP x) *ᵥ WithLp.ofLp (toE y))) := by
        rw [pgOp_apply]
      _ = toE x.1 + (WithLp.toLp 2 (cM x.2 *ᵥ WithLp.ofLp (toE y))) := by
        rw [castP, pgMat_pgPack]
      _ = toE x.1 + toE (x.2 *ᵥ y) := by
        have h_mulVec : (WithLp.toLp 2 (cM x.2 *ᵥ WithLp.ofLp (toE y))) = toE (x.2 *ᵥ y) := by
          ext i
          simp [toE, cM, mulVec, dotProduct]
        rw [h_mulVec]
      _ = toE (x.1 + x.2 *ᵥ y) := by
        ext i
        simp [toE, Pi.add_apply]
  have hUcenter : U (pgMu (castP x) + pgOp (castP x) (toE y)) = toE (u (x.1 + x.2 *ᵥ y)) := by
    rw [h_center, hU]
  have hU_i (i : Fin d) : U (pgMu (castP x) + pgOp (castP x) (toE y)) i = toE (u (x.1 + x.2 *ᵥ y)) i := by
    simpa using congrArg (fun f : EuclideanSpace ℝ (Fin d) => f i) hUcenter
  ext k
  rcases k with (i | ⟨i, j⟩)
  · -- Sum.inl i
    calc
      (triV U (castP x) (toE y)).ofLp (Sum.inl i) = U (pgMu (castP x) + pgOp (castP x) (toE y)) i := by
        simp [triV, PiLp.toLp_apply]
      _ = toE (u (x.1 + x.2 *ᵥ y)) i := by rw [hU_i i]
      _ = (castP (triVQ u x y)).ofLp (Sum.inl i) := by
        simp [castP, triVQ, pgPack, PiLp.toLp_apply, toE]
  · -- Sum.inr (i, j)
    calc
      (triV U (castP x) (toE y)).ofLp (Sum.inr (i, j)) =
          (if j ≤ i then U (pgMu (castP x) + pgOp (castP x) (toE y)) i * (toE y) j else 0) -
          (if i = j then pgKappa / d / pgMat (castP x) i i else 0) := by
        simp [triV, PiLp.toLp_apply]
      _ = (if j ≤ i then toE (u (x.1 + x.2 *ᵥ y)) i * (toE y) j else 0) -
          (if i = j then pgKappa / d / pgMat (castP x) i i else 0) := by rw [hU_i i]
      _ = (if j ≤ i then ((u (x.1 + x.2 *ᵥ y) i : ℝ) * (y j : ℝ)) else 0) -
          (if i = j then (1/8) / (d : ℝ) / ((x.2 i i : ℚ) : ℝ) else 0) := by
        simp [toE, cM, pgMat_pgPack, castP, pgKappa]
      _ = (((if j ≤ i then u (x.1 + x.2 *ᵥ y) i * y j else 0) -
          (if i = j then 1 / 8 / (d : ℚ) / x.2 i i else 0) : ℚ) : ℝ) := by
        split_ifs with hji hij
        · simp [Rat.cast_mul, Rat.cast_div]
        · simp [Rat.cast_mul]
        · simp [Rat.cast_div]
        · simp
      _ = (castP (triVQ u x y)).ofLp (Sum.inr (i, j)) := by
        simp [castP, triVQ, pgPack, PiLp.toLp_apply, toE, cM, Matrix.map]

theorem triRound_cast (Bv : ℕ) (x : PosQ d) : triRound Bv (castP x) = castP (triRoundQ Bv x) := by
  ext k
  rcases k with i | ⟨i, j⟩
  · simp [triRound, triRoundQ, castP_apply_inl]
    norm_cast
  · simp [triRound, triRoundQ, castP_apply_inr]
    norm_cast

theorem castP_add (x y : PosQ d) : castP (x + y) = castP x + castP y := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · simp [castP, pgPack, toE, cM, Pi.add_apply]
  · simp [castP, pgPack, toE, cM, Matrix.add_apply]

theorem castP_zero : castP (0 : PosQ d) = (0 : PgSp d) := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · simp [castP, pgPack, toE]
  · simp [castP, pgPack, toE, cM]

theorem castP_sum (f : ℕ → PosQ d) (N : ℕ) : castP (∑ t ∈ Finset.range N, f t) = ∑ t ∈ Finset.range N, castP (f t) := by
  induction' N with m ih
  · simp [castP_zero]
  · simp [Finset.sum_range_succ, castP_add, ih]

theorem castP_smul (c : ℚ) (x : PosQ d) : castP (c • x) = (c : ℝ) • castP x := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · simp [castP, pgPack, toE, cM, Pi.smul_apply]
  · simp [castP, pgPack, toE, cM, Matrix.smul_apply]

theorem castP_sub (x z : PosQ d) (s : ℚ) : castP (x - s • z) = castP x - (s : ℝ) • castP z := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · simp [castP, pgPack, toE, cM, Pi.sub_apply, Pi.smul_apply]
  · simp [castP, pgPack, toE, cM, Matrix.sub_apply, Matrix.smul_apply]

theorem castP_clip (r a b : ℚ) (x : PosQ d) : triClip (r : ℝ) (a : ℝ) (b : ℝ) (castP x) = castP (triClipQ r a b x) := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · simp [triClip, triClipQ, triLo, triHi, triLoQ, triHiQ, castP, pgPack, toE, cM]
  · simp [triClip, triClipQ, triLo, triHi, triLoQ, triHiQ, castP, pgPack, toE, cM]
    simp [Matrix.map, Rat.cast_max, Rat.cast_min]
    split_ifs <;> simp

theorem triIter_cast (r a b s : ℚ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (VtQ : PosQ d → (Fin d → ℚ) → PosQ d) (hV : ∀ x w, Vt (castP x) (toE w) = castP (VtQ x w))
    (y : ℕ → Fin d → ℚ) : ∀ t : ℕ, triIter (r : ℝ) (a : ℝ) (b : ℝ) (s : ℝ) Vt (fun t => toE (y t)) t = castP (triIterQ r a b s VtQ y t) := by
  intro t
  induction' t with m ih
  · simp [triIter, triIterQ, castP, toE, cM, pgPack, Matrix.one_apply]
    ext k
    rcases k with (i | ⟨i, j⟩)
    · simp
    · simp
      split_ifs <;> simp
  · rw [triIter, triIterQ]
    rw [ih]
    rw [hV (triIterQ r a b s VtQ y m) (y m)]
    rw [← castP_sub (triIterQ r a b s VtQ y m) (VtQ (triIterQ r a b s VtQ y m) (y m)) s]
    rw [castP_clip r a b (triIterQ r a b s VtQ y m - s • VtQ (triIterQ r a b s VtQ y m) (y m))]

theorem triAvg_cast (r a b s : ℚ) (Vt : PgSp d → EuclideanSpace ℝ (Fin d) → PgSp d)
    (VtQ : PosQ d → (Fin d → ℚ) → PosQ d) (hV : ∀ x w, Vt (castP x) (toE w) = castP (VtQ x w))
    (y : ℕ → Fin d → ℚ) (N : ℕ) :
    triAvg (r : ℝ) a b s Vt (fun t => toE (y t)) N = castP (triAvgQ r a b s VtQ y N) := by
  calc
    triAvg (r : ℝ) a b s Vt (fun t => toE (y t)) N
        = (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, triIter (r : ℝ) (a : ℝ) (b : ℝ) (s : ℝ) Vt (fun t => toE (y t)) t := rfl
    _ = (N : ℝ)⁻¹ • ∑ t ∈ Finset.range N, castP (triIterQ r a b s VtQ y t) := by
      simp [triIter_cast r a b s Vt VtQ hV y]
    _ = (N : ℝ)⁻¹ • castP (∑ t ∈ Finset.range N, triIterQ r a b s VtQ y t) := by
      rw [castP_sum]
    _ = castP ((N : ℚ)⁻¹ • ∑ t ∈ Finset.range N, triIterQ r a b s VtQ y t) := by
      simpa [push_cast] using (castP_smul (N : ℚ)⁻¹ (∑ t ∈ Finset.range N, triIterQ r a b s VtQ y t)).symm
    _ = castP (triAvgQ r a b s VtQ y N) := rfl

open WithLp in
theorem pgComp_cast (P P' : PosQ d) : pgComp (castP P) (castP P') = castP (pgCompQ P P') := by
  ext k
  rcases k with (i | ⟨i, j⟩)
  · -- vector part (Sum.inl i)
    simp [pgComp, pgPack, castP, pgOp_apply, pgCompQ, cM, toE, pgMu, pgMat, mulVec, dotProduct]
  · -- matrix part (Sum.inr (i, j))
    simp [pgComp, pgPack, castP, pgOp_apply, pgCompQ, cM, toE, pgMat, Matrix.mul_apply]

/-! ## The constants -/

theorem natCeil_ratCast (q : ℚ) : ⌈(q : ℝ)⌉₊ = ⌈q⌉₊ := by
  rw [← Int.ceil_toNat, Rat.ceil_cast, Int.ceil_toNat]

theorem triSQ_eq (d : ℕ) : triSQ d = triS d := rfl

theorem triR_cast (d : ℕ) : (triRQ d : ℝ) = triR d := by
  unfold triRQ triR; push_cast; rfl

theorem triA_cast (d : ℕ) : (triAQ d : ℝ) = triA d := by
  unfold triAQ triA triJaQ triJa; push_cast; rfl

theorem triB_cast (d : ℕ) : (triBQ d : ℝ) = triB d := by
  unfold triBQ triB; push_cast; rfl

theorem triRh_cast (d : ℕ) : (triRhQ d : ℝ) = triRh d := by
  unfold triRhQ triRh; push_cast; rfl

theorem triD2_cast (d : ℕ) : (triD2Q d : ℝ) = triD2 d := by
  unfold triD2Q triD2; push_cast; rw [triR_cast, triB_cast, triA_cast]

theorem triElo_cast (d : ℕ) : (triEloQ d : ℝ) = triElo d := by
  unfold triEloQ triElo pgKappa; push_cast; rw [triRh_cast]; rfl

theorem triKg_eq (d : ℕ) : triKgQ d = triKg d := by
  unfold triKgQ triKg
  rw [← natCeil_ratCast]; push_cast; rw [triB_cast, triElo_cast]

theorem triGu_cast (d : ℕ) : (triGuQ d : ℝ) = triGu d := by
  unfold triGuQ triGu triJaQ triJa; push_cast; rw [triKg_eq]; rfl

theorem triBv_eq (d : ℕ) : triBvQ d = triBv d := by
  unfold triBvQ triBv
  rw [← natCeil_ratCast]; push_cast; rw [triD2_cast, triElo_cast]

theorem triBu_cast (d : ℕ) : (triBuQ d : ℝ) = triBu d := by
  unfold triBuQ triBu; push_cast; rw [triBv_eq]

theorem triNe_eq (d ℓ : ℕ) : triNeQ d ℓ = triNe d ℓ := by
  unfold triNeQ triNe
  rw [← natCeil_ratCast]; push_cast; rw [triD2_cast, triGu_cast, triBu_cast, triElo_cast]

theorem triBg_eq (d : ℕ) : triBgQ d = triBg d := by
  unfold triBgQ triBg; rw [triKg_eq]

theorem triMst_eq (r0 R0 : ℚ) : triMstQ r0 R0 = triMst (r0 : ℝ) (R0 : ℝ) := by
  unfold triMstQ triMst
  rw [← natCeil_ratCast]; push_cast; rfl

/-! ## The core, the stages, the position -/

theorem triDraw_cast (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : triDraw d B x t = toE (triDrawQ d B x t) := by
  unfold triDraw triDrawQ gsVec toE
  congr 1; funext i; push_cast; rfl

end AdversarialBco.Bit.RQ

