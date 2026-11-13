/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriSem

@[expose] public section

/-!
# TRI-M, the update step on integers

The rational step `triClipQ (x - 2^{-Js} round(V))` of `triIterQ` against the integer step `tzUpd`, entry by entry
(`upd_mu`, `upd_low`, `upd_diag`), and the rows of a stage (`stage_rows_*`).
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.clip_div (lo hi v : ℤ) (t : ℚ) (ht : 0 < t) :
    max ((lo : ℚ) / t) (min ((hi : ℚ) / t) ((v : ℚ) / t)) = ((clipZ lo hi v : ℤ) : ℚ) / t := by
  have ht' : 0 ≤ (t : ℚ) := by linarith
  calc
    max ((lo : ℚ) / t) (min ((hi : ℚ) / t) ((v : ℚ) / t))
        = max ((lo : ℚ) / t) ((min (hi : ℚ) (v : ℚ)) / t) := by
      rw [min_div_div_right ht' (hi : ℚ) (v : ℚ)]
    _ = (max (lo : ℚ) (min (hi : ℚ) (v : ℚ))) / t := by
      rw [max_div_div_right ht' (lo : ℚ) (min (hi : ℚ) (v : ℚ))]
    _ = ((clipZ lo hi v : ℤ) : ℚ) / t := by
      simp [clipZ]


theorem AdversarialBco.Bit.TriM.floor_div_int (a b : ℤ) (hb : 0 < b) : ⌊(a : ℚ) / b⌋ = a / b := by
  have hb_nonneg : 0 ≤ b := by linarith
  have h := Rat.floor_intCast_div_natCast a (Int.toNat b)
  have h_ℤ : ((Int.toNat b : ℕ) : ℤ) = b := by
    simpa using Int.toNat_of_nonneg hb_nonneg
  have h_ℚ : ((Int.toNat b : ℕ) : ℚ) = (b : ℚ) := by
    exact_mod_cast h_ℤ
  simpa [h_ℚ, h_ℤ] using h


theorem AdversarialBco.Bit.TriM.step_sub (X k : ℤ) (Bv Js ja : ℕ) :
    (X : ℚ) / 2 ^ (Bv + Js + ja) - (1 / 2 ^ Js : ℚ) * ((k : ℚ) / 2 ^ Bv) =
      ((X - k * 2 ^ ja : ℤ) : ℚ) / 2 ^ (Bv + Js + ja) := by
  push_cast
  have h : (2 : ℚ) ^ (Bv + Js + ja) = (2 : ℚ) ^ Bv * (2 : ℚ) ^ Js * (2 : ℚ) ^ ja := by
    simp [pow_add]
  field_simp [h]
  ring



theorem AdversarialBco.Bit.TriM.round_low (A Y Bb : ℤ) (Bv p : ℕ) (hBb : 0 < Bb) :
    ⌊(A : ℚ) / Bb * ((Y : ℚ) / 2 ^ (2 * p)) * 2 ^ Bv⌋ = A * Y * 2 ^ Bv / (Bb * 2 ^ (2 * p)) := by
  have h_denom_pos : 0 < Bb * (2 : ℤ) ^ (2 * p) := by
    have h2 : 0 < (2 : ℤ) ^ (2 * p) := pow_pos (by norm_num) _
    exact mul_pos hBb h2
  have h_eq : (A : ℚ) / Bb * ((Y : ℚ) / (2 : ℚ) ^ (2 * p)) * (2 : ℚ) ^ Bv =
      ((A * Y * (2 : ℤ) ^ Bv : ℤ) : ℚ) / ((Bb * (2 : ℤ) ^ (2 * p) : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [h_eq]
  exact AdversarialBco.Bit.TriM.floor_div_int (A * Y * (2 : ℤ) ^ Bv) (Bb * (2 : ℤ) ^ (2 * p)) h_denom_pos


theorem AdversarialBco.Bit.TriM.upd_mu (Bv Js ja La : ℕ) (hLa : 10 ≤ La) (X A Bb : ℤ) (hBb : 0 < Bb) :
    max (-(2 : ℚ) ^ (La - 3)) (min ((2 : ℚ) ^ (La - 3))
        ((X : ℚ) / 2 ^ (Bv + Js + ja) - (1 / 2 ^ Js : ℚ) * ((⌊(A : ℚ) / Bb * 2 ^ Bv⌋ : ℚ) / 2 ^ Bv))) =
      ((clipZ (-2 ^ (La - 3 + (Bv + Js + ja))) (2 ^ (La - 3 + (Bv + Js + ja))) (X - A * 2 ^ Bv / Bb * 2 ^ ja) : ℤ) :
        ℚ) / 2 ^ (Bv + Js + ja) := by
  set G := Bv + Js + ja
  set t := (2 : ℚ) ^ G
  have htpos : 0 < t := by
    dsimp [t]
    exact pow_pos (by norm_num) _
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  -- Step 1: rewrite the floor ⌊(A : ℚ) / Bb * 2 ^ Bv⌋ = A * 2 ^ Bv / Bb
  have hfloor : ⌊(A : ℚ) / (Bb : ℚ) * (2 : ℚ) ^ Bv⌋ = A * (2 : ℤ) ^ Bv / Bb := by
    have hBb_nonneg : 0 ≤ Bb := Int.le_of_lt hBb
    let Bb' : ℕ := Int.toNat Bb
    have hBb'_eq : (Bb' : ℤ) = Bb := Int.toNat_of_nonneg hBb_nonneg
    have h := Rat.floor_intCast_div_natCast (A * (2 : ℤ) ^ Bv) Bb'
    have hq : ((Bb' : ℕ) : ℚ) = (Bb : ℚ) := by
      rw [show ((Bb' : ℕ) : ℚ) = ((Bb' : ℤ) : ℚ) by simp, hBb'_eq]
    have hz : ((Bb' : ℕ) : ℤ) = Bb := by
      rw [show ((Bb' : ℕ) : ℤ) = (Bb' : ℤ) by simp, hBb'_eq]
    have h' : ⌊(A * (2 : ℤ) ^ Bv : ℚ) / (Bb : ℚ)⌋ = (A * (2 : ℤ) ^ Bv) / Bb := by
      simpa [hq, hz] using h
    have h_eq : (A : ℚ) / (Bb : ℚ) * (2 : ℚ) ^ Bv = (A * (2 : ℤ) ^ Bv : ℚ) / (Bb : ℚ) := by
      push_cast
      ring
    simpa [h_eq] using h'
  -- Step 2: rewrite the min argument using algebraic manipulation
  have hstep : (X : ℚ) / (2 : ℚ) ^ G - (1 / (2 : ℚ) ^ Js) * (((A * (2 : ℤ) ^ Bv / Bb : ℤ) : ℚ) / (2 : ℚ) ^ Bv) = ((X - (A * (2 : ℤ) ^ Bv / Bb) * (2 : ℤ) ^ ja : ℤ) : ℚ) / (2 : ℚ) ^ G := by
    push_cast
    field_simp
    ring
  -- Step 3: rewrite the bounds
  have hbound_pos : (2 : ℚ) ^ (La - 3) = (((2 : ℤ) ^ (La - 3 + G) : ℤ) : ℚ) / t := by
    dsimp [t]
    push_cast
    rw [pow_add]
    field_simp
  have hbound_neg : -(2 : ℚ) ^ (La - 3) = (((-(2 : ℤ) ^ (La - 3 + G) : ℤ) : ℚ) / t) := by
    dsimp [t]
    push_cast
    rw [pow_add]
    field_simp
  -- Step 4: rewrite the LHS
  rw [hbound_neg, hbound_pos]
  have hinner : ((X : ℚ) / (2 : ℚ) ^ G - (1 / (2 : ℚ) ^ Js) * ((⌊(A : ℚ) / (Bb : ℚ) * (2 : ℚ) ^ Bv⌋ : ℚ) / (2 : ℚ) ^ Bv)) = ((X - (A * (2 : ℤ) ^ Bv / Bb) * (2 : ℤ) ^ ja : ℤ) : ℚ) / (2 : ℚ) ^ G := by
    rw [hfloor]
    exact hstep
  rw [hinner]
  -- Step 5: apply clip_div
  have hclip_div (lo hi v : ℤ) : max ((lo : ℚ) / t) (min ((hi : ℚ) / t) ((v : ℚ) / t)) = ((max lo (min hi v) : ℤ) : ℚ) / t := by
    calc
      max ((lo : ℚ) / t) (min ((hi : ℚ) / t) ((v : ℚ) / t))
          = max ((lo : ℚ) / t) ((min (hi : ℚ) (v : ℚ)) / t) := by rw [min_div_div_right ht_nonneg]
      _ = (max (lo : ℚ) (min (hi : ℚ) (v : ℚ))) / t := by rw [max_div_div_right ht_nonneg]
      _ = ((max lo (min hi v) : ℤ) : ℚ) / t := by push_cast; rfl
  rw [hclip_div (-2 ^ (La - 3 + G)) (2 ^ (La - 3 + G)) (X - A * (2 : ℤ) ^ Bv / Bb * (2 : ℤ) ^ ja)]
  rfl

theorem AdversarialBco.Bit.TriM.upd_low (Bv Js ja La p : ℕ) (hLa : 10 ≤ La) (X A Y Bb : ℤ) (hBb : 0 < Bb) :
    max (-(161 * 2 ^ (La - 10) : ℚ)) (min (161 * 2 ^ (La - 10) : ℚ)
        ((X : ℚ) / 2 ^ (Bv + Js + ja) -
          (1 / 2 ^ Js : ℚ) * ((⌊(A : ℚ) / Bb * ((Y : ℚ) / 2 ^ (2 * p)) * 2 ^ Bv⌋ : ℚ) / 2 ^ Bv))) =
      ((clipZ (-(161 * 2 ^ (La - 10 + (Bv + Js + ja)))) (161 * 2 ^ (La - 10 + (Bv + Js + ja)))
          (X - A * Y * 2 ^ Bv / (Bb * 2 ^ (2 * p)) * 2 ^ ja) : ℤ) : ℚ) / 2 ^ (Bv + Js + ja) := by
  set G := Bv + Js + ja
  set k := A * Y * 2 ^ Bv / (Bb * 2 ^ (2 * p)) with hk
  have hpos_t : 0 < (2 : ℚ) ^ G := pow_pos (by norm_num) G
  have hfloor_eq : (⌊(A : ℚ) / (Bb : ℚ) * ((Y : ℚ) / (2 : ℚ) ^ (2 * p)) * (2 : ℚ) ^ Bv⌋ : ℚ) = ((k : ℤ) : ℚ) := by
    have h := round_low A Y Bb Bv p hBb
    simpa [hk] using congrArg (fun (x : ℤ) => (x : ℚ)) h
  have hstep_eq : (X : ℚ) / (2 : ℚ) ^ G - (1 / (2 : ℚ) ^ Js : ℚ) * (((k : ℤ) : ℚ) / (2 : ℚ) ^ Bv) =
      (((X : ℤ) - k * (2 : ℤ) ^ ja : ℤ) : ℚ) / (2 : ℚ) ^ G := by
    simpa [G] using step_sub X k Bv Js ja
  have hbound_pos : (161 * 2 ^ (La - 10) : ℚ) = (((161 * 2 ^ (La - 10 + G) : ℤ) : ℚ) / (2 : ℚ) ^ G) := by
    push_cast
    rw [pow_add]
    field_simp [hpos_t.ne']
  have hbound_neg : (-(161 * 2 ^ (La - 10) : ℚ)) = (((-(161 * 2 ^ (La - 10 + G) : ℤ) : ℚ) / (2 : ℚ) ^ G)) := by
    push_cast
    rw [pow_add]
    field_simp [hpos_t.ne']
  calc
    max (-(161 * 2 ^ (La - 10) : ℚ)) (min (161 * 2 ^ (La - 10) : ℚ)
        ((X : ℚ) / (2 : ℚ) ^ G - (1 / (2 : ℚ) ^ Js : ℚ) * ((⌊(A : ℚ) / (Bb : ℚ) * ((Y : ℚ) / (2 : ℚ) ^ (2 * p)) * (2 : ℚ) ^ Bv⌋ : ℚ) / (2 : ℚ) ^ Bv)))
    = max (-(161 * 2 ^ (La - 10) : ℚ)) (min (161 * 2 ^ (La - 10) : ℚ)
        ((X : ℚ) / (2 : ℚ) ^ G - (1 / (2 : ℚ) ^ Js : ℚ) * (((k : ℤ) : ℚ) / (2 : ℚ) ^ Bv))) := by
      rw [hfloor_eq]
    _ = max (-(161 * 2 ^ (La - 10) : ℚ)) (min (161 * 2 ^ (La - 10) : ℚ)
        (((X - k * (2 : ℤ) ^ ja : ℤ) : ℚ) / (2 : ℚ) ^ G)) := by
      rw [hstep_eq]
    _ = max (((-(161 * 2 ^ (La - 10 + G) : ℤ) : ℚ) / (2 : ℚ) ^ G))
        (min (((161 * 2 ^ (La - 10 + G) : ℤ) : ℚ) / (2 : ℚ) ^ G) (((X - k * (2 : ℤ) ^ ja : ℤ) : ℚ) / (2 : ℚ) ^ G)) := by
      rw [hbound_neg, hbound_pos]
    _ = ((clipZ (-(161 * 2 ^ (La - 10 + G))) (161 * 2 ^ (La - 10 + G)) (X - k * (2 : ℤ) ^ ja) : ℤ) : ℚ) / (2 : ℚ) ^ G := by
      simpa [push_cast] using clip_div (-(161 * 2 ^ (La - 10 + G))) (161 * 2 ^ (La - 10 + G)) (X - k * (2 : ℤ) ^ ja) ((2 : ℚ) ^ G) hpos_t
    _ = ((clipZ (-(161 * 2 ^ (La - 10 + (Bv + Js + ja)))) (161 * 2 ^ (La - 10 + (Bv + Js + ja)))
          (X - A * Y * 2 ^ Bv / (Bb * 2 ^ (2 * p)) * 2 ^ ja) : ℤ) : ℚ) / 2 ^ (Bv + Js + ja) := by
      simp [G, hk]

theorem AdversarialBco.Bit.TriM.upd_diag (d : ℕ) (hd : 1 ≤ d) (Bv Js ja La p : ℕ) (hLa : 10 ≤ La) (X A Y Bb : ℤ)
    (hBb : 0 < Bb) (hX : 0 < X) :
    max (1 / 2 ^ ja : ℚ) (min (161 * 2 ^ (La - 10) : ℚ)
        ((X : ℚ) / 2 ^ (Bv + Js + ja) - (1 / 2 ^ Js : ℚ) *
          ((⌊((A : ℚ) / Bb * ((Y : ℚ) / 2 ^ (2 * p)) - 1 / 8 / (d : ℚ) / ((X : ℚ) / 2 ^ (Bv + Js + ja))) *
            2 ^ Bv⌋ : ℚ) / 2 ^ Bv))) =
      ((clipZ (2 ^ (Bv + Js)) (161 * 2 ^ (La - 10 + (Bv + Js + ja)))
          (X - (A * Y * (8 * d * X) - 2 ^ (Bv + Js + ja) * Bb * 2 ^ (2 * p)) * 2 ^ Bv /
            (Bb * 2 ^ (2 * p) * (8 * d * X)) * 2 ^ ja) : ℤ) : ℚ) / 2 ^ (Bv + Js + ja) := by
  set G := Bv + Js + ja with hG
  have ht_pos : 0 < (2 : ℚ) ^ G := pow_pos (by norm_num) G
  have hP2_pos : 0 < (2 : ℤ) ^ (2 * p) := pow_pos (by norm_num) (2 * p)
  have hPG_pos : 0 < (2 : ℤ) ^ G := pow_pos (by norm_num) G
  have hPB_pos : 0 < (2 : ℤ) ^ Bv := pow_pos (by norm_num) Bv
  have hX_pos_int : 0 < X := hX
  -- Step 1: rewrite the floor using rdiag_eq
  have hfloor_eq := rdiag_eq A Y Bb ((2 : ℤ) ^ (2 * p)) ((2 : ℤ) ^ G) ((2 : ℤ) ^ Bv) X d hd hBb hP2_pos hPG_pos hPB_pos hX_pos_int
  have hfloor_eq_rat : (⌊((A : ℚ) / Bb * ((Y : ℚ) / 2 ^ (2 * p)) - 1 / 8 / (d : ℚ) / ((X : ℚ) / 2 ^ G)) * 2 ^ Bv⌋ : ℚ) =
      (((A * Y * (8 * d * X) - (2 : ℤ) ^ G * Bb * 2 ^ (2 * p)) * (2 : ℤ) ^ Bv / (Bb * 2 ^ (2 * p) * (8 * d * X)) : ℤ) : ℚ) := by
    simpa using congrArg (fun (x : ℤ) => (x : ℚ)) hfloor_eq
  -- Step 2: rewrite the min argument using step_sub
  set k : ℤ := (A * Y * (8 * d * X) - (2 : ℤ) ^ G * Bb * 2 ^ (2 * p)) * (2 : ℤ) ^ Bv / (Bb * 2 ^ (2 * p) * (8 * d * X)) with hk
  have hmin_inner : ((X : ℚ) / 2 ^ G - (1 / 2 ^ Js : ℚ) * ((⌊((A : ℚ) / Bb * ((Y : ℚ) / 2 ^ (2 * p)) - 1 / 8 / (d : ℚ) / ((X : ℚ) / 2 ^ G)) * 2 ^ Bv⌋ : ℚ) / 2 ^ Bv)) =
      (((X : ℤ) - k * (2 : ℤ) ^ ja : ℤ) : ℚ) / 2 ^ G := by
    rw [hfloor_eq_rat]
    rw [hk]
    rw [hG]
    rw [step_sub X k Bv Js ja]
  -- Step 3: rewrite the bounds
  have hbound1 : (1 / 2 ^ ja : ℚ) = (((2 : ℤ) ^ (Bv + Js) : ℤ) : ℚ) / (2 : ℚ) ^ G := by
    push_cast
    have h_pow : (2 : ℚ) ^ G = (2 : ℚ) ^ (Bv + Js) * (2 : ℚ) ^ ja := by
      rw [hG, pow_add]
    field_simp [pow_ne_zero ja (by norm_num : (2 : ℚ) ≠ 0), pow_ne_zero G (by norm_num : (2 : ℚ) ≠ 0)]
    rw [h_pow, mul_comm]
  have hbound2 : (161 * 2 ^ (La - 10) : ℚ) = (((161 : ℤ) * (2 : ℤ) ^ (La - 10 + G) : ℤ) : ℚ) / (2 : ℚ) ^ G := by
    push_cast
    have h_pow : (2 : ℚ) ^ (La - 10 + G) = (2 : ℚ) ^ (La - 10) * (2 : ℚ) ^ G := by rw [pow_add]
    field_simp [pow_ne_zero G (by norm_num : (2 : ℚ) ≠ 0), h_pow]
    ring
  rw [hbound1, hbound2, hmin_inner]
  -- Step 4: close with clip_div
  rw [clip_div ((2 : ℤ) ^ (Bv + Js)) ((161 : ℤ) * (2 : ℤ) ^ (La - 10 + G))
    ((X : ℤ) - k * (2 : ℤ) ^ ja) ((2 : ℚ) ^ G) ht_pos]

theorem AdversarialBco.Bit.TriM.stage_rows_in {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (D : ℤ) (hD : 0 < D) (mu : Fin d → ℤ) (T : Matrix (Fin d) (Fin d) ℤ) (k : Fin m) :
    ((T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (frAl A b k i : ℚ)) =
        ((frDen A b k : ℚ) * D) • ((fun i l => (T i l : ℚ) / D : Matrix (Fin d) (Fin d) ℚ)ᵀ *ᵥ A k) ∧
      ((frBe A b k * D - frAl A b k ⬝ᵥ mu : ℤ) : ℚ) =
        ((frDen A b k : ℚ) * D) * (b k - A k ⬝ᵥ fun i => (mu i : ℚ) / D) := by
  have hcast := frAl_cast A b k
  rcases hcast with ⟨hfpos, hal_cast, hbe_cast⟩
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne.symm
  constructor
  · ext l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.map_apply]
    have hsum : (∑ x, ((fun i l => (T i l : ℚ) / D : Matrix (Fin d) (Fin d) ℚ)ᵀ) l x * A k x) =
               (∑ x, ((T x l : ℚ) / (D : ℚ)) * A k x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rfl
    rw [hsum]
    simp only [hal_cast]
    have hLHS : (∑ x, (T x l : ℚ) * ((frDen A b k : ℚ) * A k x)) = (frDen A b k : ℚ) * (∑ x, (T x l : ℚ) * A k x) := by
      simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    have hRHS : (↑(frDen A b k) * ↑D * ∑ x, ((T x l : ℚ) / (D : ℚ)) * A k x) = (frDen A b k : ℚ) * (∑ x, (T x l : ℚ) * A k x) := by
      simp [Finset.mul_sum]
      field_simp [hDq]
    rw [hLHS, hRHS]
  · push_cast
    simp only [dotProduct, Int.cast_sum, Int.cast_mul]
    simp only [hal_cast, hbe_cast]
    rw [mul_sub]
    simp only [Finset.mul_sum]
    field_simp [hDq]


theorem AdversarialBco.Bit.TriM.stage_rows_bp {d : ℕ} (Dc : ℤ) (hDc : 0 < Dc) (e j : ℕ) (ch : Fin d → ℤ)
    (mu : Fin d → ℤ) (T : Matrix (Fin d) (Fin d) ℤ) (i : Fin d) :
    ((T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun l => ((Pi.single i 1 : Fin d → ℤ) l : ℚ)) =
        ((Dc : ℚ) * 2 ^ e) •
          ((fun i l => (T i l : ℚ) / (Dc * 2 ^ e) : Matrix (Fin d) (Fin d) ℚ)ᵀ *ᵥ (Pi.single i 1 : Fin d → ℚ)) ∧
      ((ch i * 2 ^ e + 2 ^ j * (Dc * 2 ^ e) - (Pi.single i 1 : Fin d → ℤ) ⬝ᵥ mu : ℤ) : ℚ) =
        ((Dc : ℚ) * 2 ^ e) * (((ch i : ℚ) / Dc + 2 ^ j) -
          (Pi.single i 1 : Fin d → ℚ) ⬝ᵥ fun l => (mu l : ℚ) / (Dc * 2 ^ e)) := by
  have hDc_ne : (Dc : ℚ) ≠ 0 := by exact_mod_cast hDc.ne.symm
  have hDpos : (0 : ℚ) < (Dc : ℚ) * (2 : ℚ) ^ e := by
    have hDc' : (0 : ℚ) < (Dc : ℚ) := by exact_mod_cast hDc
    have h2e : (0 : ℚ) < (2 : ℚ) ^ e := pow_pos (by norm_num) e
    exact mul_pos hDc' h2e
  have hDne : (Dc : ℚ) * (2 : ℚ) ^ e ≠ 0 := by linarith
  constructor
  · ext l
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, smul_eq_mul, Matrix.map_apply]
    dsimp only [Matrix.transpose]
    simp only [Matrix.of_apply]
    field_simp [hDne]
  · push_cast
    simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    field_simp [hDpos.ne.symm, hDc_ne]


theorem AdversarialBco.Bit.TriM.stage_rows_bm {d : ℕ} (Dc : ℤ) (hDc : 0 < Dc) (e j : ℕ) (ch : Fin d → ℤ)
    (mu : Fin d → ℤ) (T : Matrix (Fin d) (Fin d) ℤ) (i : Fin d) :
    ((T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun l => ((-Pi.single i 1 : Fin d → ℤ) l : ℚ)) =
        ((Dc : ℚ) * 2 ^ e) •
          ((fun i l => (T i l : ℚ) / (Dc * 2 ^ e) : Matrix (Fin d) (Fin d) ℚ)ᵀ *ᵥ (-Pi.single i 1 : Fin d → ℚ)) ∧
      ((2 ^ j * (Dc * 2 ^ e) - ch i * 2 ^ e - (-Pi.single i 1 : Fin d → ℤ) ⬝ᵥ mu : ℤ) : ℚ) =
        ((Dc : ℚ) * 2 ^ e) * ((2 ^ j - (ch i : ℚ) / Dc) -
          (-Pi.single i 1 : Fin d → ℚ) ⬝ᵥ fun l => (mu l : ℚ) / (Dc * 2 ^ e)) := by
  have hDc' : (Dc : ℚ) ≠ 0 := by exact_mod_cast hDc.ne.symm
  have h2e : (2 ^ e : ℚ) ≠ 0 := pow_ne_zero e (by norm_num : (2 : ℚ) ≠ 0)
  have hDc2e : (Dc : ℚ) * (2 ^ e : ℚ) ≠ 0 := mul_ne_zero hDc' h2e
  constructor
  · ext l
    simp only [Matrix.mulVec, dotProduct]
    simp only [Matrix.transpose]
    simp only [Pi.neg_apply, Pi.single_apply]
    simp [mul_ite, Finset.mem_univ]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    field_simp [hDc2e]
  · simp [Pi.single_apply, dotProduct]
    field_simp [hDc']


theorem AdversarialBco.Bit.TriM.stage_rows_scale {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (ch : Fin d → ℤ) (Dc : ℤ) (hDc : 0 < Dc) (e j : ℕ) (mu : Fin d → ℤ) (T : Matrix (Fin d) (Fin d) ℤ)
    (k : Fin (m + (d + d))) :
    ∃ sk : ℚ, 0 < sk ∧
      ((T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (tzRowA A b k i : ℚ)) =
        sk • triStAQ (fun k => A k) (fun i => (mu i : ℚ) / (Dc * 2 ^ e), fun i l => (T i l : ℚ) / (Dc * 2 ^ e)) k ∧
      ((tzRowB A b ch e j (Dc * 2 ^ e) k - tzRowA A b k ⬝ᵥ mu : ℤ) : ℚ) =
        sk * triStBQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (2 ^ j)
          (fun i => (mu i : ℚ) / (Dc * 2 ^ e), fun i l => (T i l : ℚ) / (Dc * 2 ^ e)) k := by
  set D := (Dc : ℚ) * ((2 : ℚ) ^ e) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (by exact_mod_cast hDc) (pow_pos (by norm_num) e)
  have hDpos_int : 0 < Dc * (2 ^ e : ℤ) := by
    have h2e : 0 < (2 ^ e : ℤ) := by exact_mod_cast pow_pos (by norm_num) e
    exact mul_pos hDc h2e
  refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
  · -- k' : Fin m, input row
    have hfr := (frAl_cast A b k').1
    have hfrpos : 0 < (frDen A b k' : ℚ) := by exact_mod_cast hfr
    have hpos : 0 < (frDen A b k' : ℚ) * D := mul_pos hfrpos hDpos
    refine ⟨(frDen A b k' : ℚ) * D, hpos, ?_, ?_⟩
    · simp only [tzRowA, triStAQ, triRowsAQ, Fin.append_left]
      have h_in := stage_rows_in A b (Dc * 2 ^ e) hDpos_int mu T k'
      simpa [hDdef] using h_in.1
    · simp only [tzRowA, tzRowB, triStBQ, triRowsBQ, triRowsAQ, Fin.append_left]
      have h_in := stage_rows_in A b (Dc * 2 ^ e) hDpos_int mu T k'
      simpa [hDdef] using h_in.2
  · -- k' : Fin (d + d), box row
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
    · -- i : Fin d, e_i row
      have hpos : 0 < (Dc : ℚ) * ((2 : ℚ) ^ e) := hDpos
      refine ⟨(Dc : ℚ) * ((2 : ℚ) ^ e), hpos, ?_, ?_⟩
      · simp only [tzRowA, triStAQ, triRowsAQ, Fin.append_right, Fin.append_left]
        have h_bp := stage_rows_bp Dc hDc e j ch mu T i
        simpa [hDdef] using h_bp.1
      · simp only [tzRowA, tzRowB, triStBQ, triRowsBQ, triRowsAQ, Fin.append_right, Fin.append_left]
        have h_bp := stage_rows_bp Dc hDc e j ch mu T i
        simpa [hDdef] using h_bp.2
    · -- i : Fin d, -e_i row
      have hpos : 0 < (Dc : ℚ) * ((2 : ℚ) ^ e) := hDpos
      refine ⟨(Dc : ℚ) * ((2 : ℚ) ^ e), hpos, ?_, ?_⟩
      · simp only [tzRowA, triStAQ, triRowsAQ, Fin.append_right]
        have h_bm := stage_rows_bm Dc hDc e j ch mu T i
        simpa [hDdef] using h_bm.1
      · simp only [tzRowA, tzRowB, triStBQ, triRowsBQ, triRowsAQ, Fin.append_right]
        have h_bm := stage_rows_bm Dc hDc e j ch mu T i
        simpa [hDdef] using h_bm.2
