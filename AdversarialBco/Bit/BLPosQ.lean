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
# Piece (C) of the program cut: `triPosQ` is `triPos` in rationals

`triPosQ` (Bit/RoutQ.lean, Interface I) is TRI-OGD staged written line by line in `ℚ`. Its cast into `PgSp d`
(`castP`, the packing `pgPack (toE μ) (cM T)` of `posR`) is `triPos` of Bit/TriStage.lean on the cast rows
(`triPosQ_cast`). Consequences for BL's routines `RoutinesQ`:

* `posLocalQ`: `PosLocal RoutinesQ` (the prologue reads the coins `< K0Q d n`), from `triPos_local`;
* `posTriQ`: `PosTri RoutinesQ`, given the frame inclusion `B̄(frameQ, 1/2) ⊆ K` (`FrameQBall`, piece (B) of the cut);
* `posInst_of_posTri`: `PosTri R → PosInst (blInst P R)`.
-/

namespace AdversarialBco.Bit.RQ

open AdversarialBco.Poly
open AdversarialBco.BitRAM (toE readCoins)
open AdversarialBco.Bit.BLP (cM posR Routines PosTri PosLocal blInst blRun betaR)
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

theorem posR_eq (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool) :
    posR R d n m A b cs = castP (R.pos d n m A b cs) := rfl

/-! ## The leaves: each operation of the core commutes with the cast -/

theorem triU_cast {m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (z : Fin d → ℚ) :
    triU (fun k => toE (α k)) (fun k => (β k : ℝ)) (toE z) = toE (triUQ α β z) := by
  have hQ : ∀ k, triQ (fun k => toE (α k)) (fun k => (β k : ℝ)) k (toE z) = (triQQ α β k z : ℝ) := by
    intro k
    simp only [triQ, triQQ, Rat.cast_div]
    congr 1
    simp [toE, dotProduct, inner, Rat.cast_sum, Rat.cast_mul, mul_comm]
  ext i
  simp only [triU, triUQ, hQ, Rat.cast_pos, Rat.cast_le, Rat.cast_lt]
  simp only [toE, WithLp.ofLp_sum, Finset.sum_apply, Rat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

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

theorem triStA_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (P : PosQ d) (k : Fin (m + (d + d))) :
    triStA (fun i => toE (A i)) (castP P) k = toE (triStAQ A P k) := by
  unfold triStA triStAQ castP pgOp triRowsA triRowsAQ toE cM
  simp [pgMat_pgPack]
  -- Now we have: ContinuousLinearMap.adjoint (toEuclideanCLM (P.2.map Rat.cast)) (Fin.append ... k) = ...
  -- Use the adjoint lemma
  have h_adj : ContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P.2.map Rat.cast)) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) ((P.2.map Rat.cast).transpose) := by
    calc
      ContinuousLinearMap.adjoint ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P.2.map Rat.cast)) =
          star ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (P.2.map Rat.cast)) := by
        rw [ContinuousLinearMap.star_eq_adjoint]
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) (star (P.2.map Rat.cast)) := by
        exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)).map_star' (P.2.map Rat.cast)).symm
      _ = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) ((P.2.map Rat.cast).transpose) := rfl
  rw [h_adj]
  -- Now we need: (Matrix.toEuclideanCLM (P.2.map Rat.cast).transpose) (Fin.append ... k) = toE (P.2ᵀ *ᵥ ...)
  -- Use Fin.addCases to split k into three cases
  refine Fin.addCases (m := m) (n := d + d) ?left ?right k
  · -- k is in the first block (from A)
    intro i
    simp [toE, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, PiLp.single_apply]
    ext j
    simp [Matrix.mulVec, dotProduct, PiLp.single_apply]
  · -- k is in the second block (e_i and -e_i)
    intro i
    refine Fin.addCases (m := d) (n := d) ?left' ?right' i
    · -- k is in the e_i block
      intro j
      simp [toE, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, PiLp.single_apply]
      ext x
      simp [Matrix.mulVec, dotProduct, PiLp.single_apply]
    · -- k is in the -e_i block
      intro j
      simp [toE, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, PiLp.single_apply]
      ext x
      have h_addNat : j.addNat d = Fin.natAdd d j := by ext i; simp
      rw [h_addNat, Fin.append_right, Fin.append_right]
      simp [PiLp.single_apply, Matrix.mulVec, dotProduct]
      -- Goal: ↑(P.2 j x) = ∑ x_1, ↑(P.2 x_1 x) * ↑(Pi.single j 1 x_1)
      have hsum : (∑ x_1 : Fin d, ((P.2.map Rat.cast) x_1 x) * (↑(if x_1 = j then (1 : ℚ) else 0) : ℝ)) = ((P.2.map Rat.cast) j x : ℝ) := by
        calc
          (∑ x_1 : Fin d, ((P.2.map Rat.cast) x_1 x) * (↑(if x_1 = j then (1 : ℚ) else 0) : ℝ)) =
            (∑ x_1 : Fin d, (if x_1 = j then ((P.2.map Rat.cast) j x) * ((1 : ℚ) : ℝ) else 0)) := by
              refine Finset.sum_congr rfl (fun x_1 hx => ?_)
              by_cases h : x_1 = j
              · simp [h]
              · simp [h]
          _ = ((P.2.map Rat.cast) j x : ℝ) := by simp
      simpa [Pi.single_apply] using hsum.symm

theorem triRowsA_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (k : Fin (m + (d + d))) :
    triRowsA (fun i => toE (A i)) k = toE (triRowsAQ A k) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [triRowsA, triRowsAQ, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [triRowsA, triRowsAQ, Fin.append_right, Fin.append_left]
      ext x
      simp only [toE, PiLp.single_apply, Pi.single_apply]
      split_ifs <;> simp
    · simp only [triRowsA, triRowsAQ, Fin.append_right]
      ext x
      simp only [toE, PiLp.neg_apply, Pi.neg_apply, PiLp.single_apply, Pi.single_apply]
      split_ifs <;> simp

theorem triRowsB_cast {m : ℕ} (b : Fin m → ℚ) (c : Fin d → ℚ) (s : ℚ) (k : Fin (m + (d + d))) :
    triRowsB (fun i => (b i : ℝ)) (toE c) (s : ℝ) k = (triRowsBQ b c s k : ℝ) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [triRowsB, triRowsBQ, Fin.append_left]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [triRowsB, triRowsBQ, Fin.append_right, Fin.append_left, toE]
      push_cast; rfl
    · simp only [triRowsB, triRowsBQ, Fin.append_right, toE]
      push_cast; rfl

theorem triStB_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (s : ℚ) (P : PosQ d)
    (k : Fin (m + (d + d))) :
    triStB (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (s : ℝ) (castP P) k = (triStBQ A b c s P k : ℝ) := by
  unfold triStB triStBQ
  rw [triRowsB_cast, triRowsA_cast]
  have hmu : pgMu (castP P) = toE P.1 := rfl
  rw [hmu]
  push_cast
  congr 1
  simp [toE, PiLp.inner_apply, dotProduct, mul_comm]

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

theorem triJs_eq (d ℓ : ℕ) : triJsQ d ℓ = triJs d ℓ := by
  unfold triJsQ triJs
  rw [← natCeil_ratCast]; push_cast; rw [triGu_cast, triBu_cast, triNe_eq, triD2_cast]

theorem triBg_eq (d : ℕ) : triBgQ d = triBg d := by
  unfold triBgQ triBg; rw [triKg_eq]

theorem triL_eq (d ℓ : ℕ) : triLQ d ℓ = triL d ℓ := by
  unfold triLQ triL; rw [triNe_eq, triBg_eq]

theorem triMst_eq (r0 R0 : ℚ) : triMstQ r0 R0 = triMst (r0 : ℝ) (R0 : ℝ) := by
  unfold triMstQ triMst
  rw [← natCeil_ratCast]; push_cast; rfl

/-! ## The core, the stages, the position -/

theorem triDraw_cast (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : triDraw d B x t = toE (triDrawQ d B x t) := by
  unfold triDraw triDrawQ gsVec toE
  congr 1; funext i; push_cast; rfl

theorem triCoreOut_cast (d : ℕ) {m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (ℓ : ℕ) (y : ℕ → Fin d → ℚ) :
    triCoreOut d (fun k => toE (α k)) (fun k => (β k : ℝ)) ℓ (fun t => toE (y t)) =
      castP (triCoreOutQ d α β ℓ y) := by
  unfold triCoreOut triCoreOutQ
  have hV : ∀ x w, (fun x w => triRound (triBvQ d) (triV (triU (fun k => toE (α k)) (fun k => (β k : ℝ))) x w))
      (castP x) (toE w) = castP ((fun x w => triRoundQ (triBvQ d) (triVQ (triUQ α β) x w)) x w) := by
    intro x w
    simp only
    rw [triV_cast (triUQ α β) _ (fun z => triU_cast α β z) x w, triRound_cast]
  rw [← triR_cast, ← triA_cast, ← triB_cast, ← triNe_eq, ← triJs_eq, ← triBv_eq]
  have hs : ((1 : ℝ) / 2 ^ triJsQ d ℓ) = ((1 / 2 ^ triJsQ d ℓ : ℚ) : ℝ) := by push_cast; ring
  rw [hs]
  exact triAvg_cast _ _ _ _ _ _ hV y _

theorem triStep_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ j : ℕ)
    (P : PosQ d) (x : ℕ → Bool) :
    triStep (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (r0 : ℝ) ℓ j (castP P) x =
      castP (triStepQ A b c r0 ℓ j P x) := by
  unfold triStep triStepQ
  have hA : triStA (fun i => toE (A i)) (castP P) = fun k => toE (triStAQ A P k) :=
    funext fun k => triStA_cast A P k
  have hB : triStB (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (2 ^ (j + 1) * (r0 : ℝ)) (castP P) =
      fun k => (triStBQ A b c (2 ^ (j + 1) * r0) P k : ℝ) := by
    funext k
    rw [← triStB_cast A b c (2 ^ (j + 1) * r0) P k]
    push_cast
    rfl
  have hD : (fun t => triDraw d (triBg d) x t) = fun t => toE (triDrawQ d (triBgQ d) x t) := by
    funext t
    rw [triDraw_cast, triBg_eq]
  rw [hA, hB, hD, triCoreOut_cast, pgComp_cast]

theorem triStageN_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ : ℕ)
    (ω : ℕ → ℕ → Bool) (J : ℕ) :
    triStageN (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (r0 : ℝ) ℓ ω J =
      castP (triStageNQ A b c r0 ℓ ω J) := by
  induction J with
  | zero =>
    show pgPack (toE c) ((r0 : ℝ) • 1) = pgPack (toE c) (cM (r0 • 1))
    congr 1
    ext i j
    simp only [cM, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  | succ J ih =>
    show triStep (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (r0 : ℝ) ℓ J
        (triStageN (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (r0 : ℝ) ℓ ω J) (ω J) =
      castP (triStepQ A b c r0 ℓ J (triStageNQ A b c r0 ℓ ω J) (ω J))
    rw [ih, triStep_cast]

/-- **`triPosQ` is `triPos` on the cast rows.** -/
theorem triPosQ_cast {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ)
    (cs : ℕ → Bool) :
    triPos (fun i => toE (A i)) (fun i => (b i : ℝ)) (toE c) (r0 : ℝ) (R0 : ℝ) ℓ cs =
      castP (triPosQ A b c r0 R0 ℓ cs) := by
  unfold triPos triPosQ
  rw [← triMst_eq, ← triL_eq, triStageN_cast]

theorem triMst_half (n : ℕ) : triMstQ (1 / 2) n = triMst (1 / 2) (n : ℝ) := by
  rw [triMst_eq]; norm_num

/-- BL's position is `triPos` on the rows of `K` at the frame centre. -/
theorem posQ_cast (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool) :
    castP (posQ d n m A b cs) = triPos (fun k => toE (A k)) (fun k => (b k : ℝ)) (toE (frameQ d n m A b)) (1 / 2) n
      (ellPos d n) cs := by
  unfold posQ
  rw [← triPosQ_cast]
  have h1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have h2 : (((n : ℚ)) : ℝ) = n := Rat.cast_natCast n
  rw [h1, h2]

/-- `PosLocal RoutinesQ`: BL's position reads the coins `< K0Q d n` only. -/
theorem posLocalQ : PosLocal RoutinesQ := by
  intro d n m A b cs cs' h
  apply castP_injective
  show castP (posQ d n m A b cs) = castP (posQ d n m A b cs')
  rw [posQ_cast, posQ_cast]
  refine triPos_local _ _ _ _ _ _ cs cs' fun i hi => h i ?_
  show i < K0Q d n
  unfold K0Q
  rw [triMst_half, triL_eq]
  exact hi

/-- The frame inclusion of Procedure FRAME, `B̄(c, 1/2) ⊆ K` at `c = frameQ` (piece (B) of the program cut). -/
def FrameQBall : Prop :=
  ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b →
    Metric.closedBall (toE (frameQ d n m A b)) (1 / 2) ⊆ polytope A b

theorem polytope_rows {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    polytope A b = {y | ∀ k, inner ℝ (toE (A k)) y ≤ (b k : ℝ)} := by
  ext y
  simp only [polytope, Set.mem_ofPred_eq, PiLp.inner_apply, toE, RCLike.inner_apply, conj_trivial]
  refine forall_congr' fun k => ?_
  simp [mul_comm]

/-- `PosTri RoutinesQ`, given the frame inclusion. -/
theorem posTriQ (hF : FrameQBall) : PosTri RoutinesQ := by
  intro d n m M A b hI hc
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast hI.hd
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hI.hn
  have hD : (1 : ℝ) ≤ (d : ℝ) * n := by nlinarith
  have hD3 : (n : ℝ) ≤ ((d : ℝ) * n) ^ 3 := by nlinarith [pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1) hD 2]
  refine ⟨m, fun k => toE (A k), fun k => (b k : ℝ), toE (frameQ d n m A b), ellPos d n,
    1 / (3 * 2 ^ 19 * ((d : ℝ) * n) ^ 3), polytope_rows A b, hF d n m M A b hI, by positivity, ?_, ?_, ?_,
    fun cs => ?_⟩
  · rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  · have hN1 : 1 ≤ 3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n := by
      have h1 : 1 ≤ triMstQ (1 / 2) n := le_max_left _ _
      have h2 : 1 ≤ d * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hI.hd; omega)
        (by have := hI.hn; omega))
      have h3 : 1 ≤ (d * n) ^ 3 := Nat.one_le_pow _ _ h2
      nlinarith
    have hdiv : (triMst (1 / 2) (n : ℝ) : ℝ) / (1 / (3 * 2 ^ 19 * ((d : ℝ) * n) ^ 3)) =
        ((3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n : ℕ) : ℝ) := by
      rw [triMst_half]; push_cast; field_simp; ring
    rw [hdiv]
    have hpos : (0 : ℝ) < ((3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n : ℕ) : ℝ) := by
      exact_mod_cast hN1
    have hle : ((3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n : ℕ) : ℝ) ≤ 2 ^ ellPos d n := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    calc Real.log ((3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n : ℕ) : ℝ)
        ≤ Real.log (2 ^ ellPos d n) := Real.log_le_log hpos hle
      _ = ellPos d n * Real.log 2 := by rw [Real.log_pow]
      _ ≤ ellPos d n := mul_le_of_le_one_right (Nat.cast_nonneg _)
          ((Real.log_le_sub_one_of_pos two_pos).trans (by norm_num))
  · show triMst (1 / 2) (n : ℝ) * triL d (ellPos d n) ≤ K0Q d n
    unfold K0Q
    rw [triMst_half, triL_eq]
  · rw [posR_eq]
    exact posQ_cast d n m A b cs

end AdversarialBco.Bit.RQ

namespace AdversarialBco.Bit.BLP

/-- `PosTri R` gives `PosInst (blInst P R)`: the position of the record is the position on the coins `β ω`. -/
theorem posInst_of_posTri {P : List AdversarialBco.BitRAM.Instr} {R : Routines} (h : PosTri R) :
    AdversarialBco.Bit.Asm.PosInst (blInst P R) := by
  intro d n m M A b hI hc σ _
  obtain ⟨m', α, β', c, ℓ, δpos, h1, h2, h3, h4, h5, h6, h7⟩ := h d n m M A b hI hc
  exact ⟨m', α, β', c, ℓ, δpos, h1, h2, h3, h4, h5, h6, fun ω => h7 _⟩

end AdversarialBco.Bit.BLP
