/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyEnv
public import AdversarialBco.Unified.PolyBound

@[expose] public section

/-!
# UNI-POLY: the constants and Corollary P (`conj1BitHP_of_unified`)

* `Kc_le`, `Cpro_le`: the block constant and the prologue cost are polynomial in the size of the instance.
* `bound_mach`: the bound of the machine clauses in the frozen form (`bound_mach_gen`, PolyBound.lean).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UniPoly

open BitRAM BitRAMO Unified
open RealRAM (Strategy lossAd regretPts polytope HeightLE)
open Bit.Asm (InputOK)
open Bit.Transfer (B.run_add)
open AdversarialBco.Poly.Mach (Layout asz)
open AdversarialBco.Bit.Transfer (offOf)

variable {d : ℕ}

/-! ## The constants -/

theorem U_mono2 {d d' L L' : ℕ} (hd : d ≤ d') (hL : L ≤ L') : U d L ≤ U d' L' := by
  unfold U; gcongr

theorem offOf_mono {d m d' m' : ℕ} (hd : d ≤ d') (hm : m ≤ m') : offOf d m ≤ offOf d' m' := by
  unfold offOf; gcongr

theorem base_mono {d d' : ℕ} (a : ℕ) (hd : d ≤ d') : LPL.base d a ≤ LPL.base d' a := by
  unfold Layout.base asz; gcongr

theorem LYv_mono {d m d' m' : ℕ} (hd : d ≤ d') (hm : m ≤ m') : LYv d m ≤ LYv d' m' := by
  unfold LYv YBv
  have := offOf_mono hd hm
  have := base_mono aY hd
  omega

theorem Kc0_mono {d m Ms LY d' m' Ms' LY' : ℕ} (hd : d ≤ d') (hm : m ≤ m') (hM : Ms ≤ Ms') (hL : LY ≤ LY') :
    Kc0 d m Ms LY ≤ Kc0 d' m' Ms' LY' := by
  unfold Kc0 N1 Kd U; gcongr

/-- The block constant is polynomial: `Kc d m M ≤ 10^28 (d + m + size M + 1)^35`. -/
theorem Kc_le (d m M : ℕ) : Kc d m M ≤ 10 ^ 28 * (d + m + M.size + 1) ^ 35 := by
  set X := d + m + M.size + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have h1 : Kc d m M ≤ Kc0 X X X (LYv X X) :=
    Kc0_mono (by omega) (by omega) (by omega) (LYv_mono (by omega) (by omega))
  have p : ∀ k ≤ 35, X ^ k ≤ X ^ 35 := fun k hk => Nat.pow_le_pow_right hX1 hk
  have h2 : Kc0 X X X (LYv X X) ≤ 10 ^ 28 * X ^ 35 := by
    simp only [Kc0, N1, Kd, U, LYv, YBv, offOf, Layout.base, LPL, aY, asz]
    linarith [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p 3 (by norm_num), p 4 (by norm_num),
      p 5 (by norm_num), p 6 (by norm_num)]
  exact h1.trans h2

/-- The cost of `SETUP` is polynomial. -/
theorem Cset_le (d n m M : ℕ) : Cset d n m M ≤ 10 ^ 26 * (d + m + n.size + M.size + 1) ^ 34 := by
  set Y := d + m + n.size + M.size + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hdY : d ≤ Y := by omega
  have hS : Spl d m M ≤ 10 ^ 8 * Y ^ 11 := by
    unfold Spl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 11)
  have hL : Lset d n m M ≤ 10 ^ 8 * Y ^ 11 + Y + 2 + (offOf Y Y + LPL.base Y 16 + Y * Y + 4 * Y + 2000) := by
    unfold Lset
    have := offOf_mono (d := d) (m := m) (d' := Y) (m' := Y) hdY (by omega)
    have := base_mono 16 hdY
    have : d * d ≤ Y * Y := Nat.mul_le_mul hdY hdY
    have : n.size ≤ Y := by omega
    omega
  have h1 : Cset d n m M ≤ (50 + Y * (8 * (2 * (10 ^ 8 * Y ^ 11) + 1) + 22)) *
      U Y (10 ^ 8 * Y ^ 11 + Y + 2 + (offOf Y Y + LPL.base Y 16 + Y * Y + 4 * Y + 2000)) := by
    unfold Cset
    refine Nat.mul_le_mul ?_ (U_mono2 hdY hL)
    gcongr
  have p : ∀ k ≤ 34, Y ^ k ≤ Y ^ 34 := fun k hk => Nat.pow_le_pow_right hY1 hk
  refine h1.trans ?_
  simp only [U, offOf, Layout.base, LPL, asz]
  linarith [p 0 (by norm_num), p 1 (by norm_num), p 2 (by norm_num), p 3 (by norm_num), p 4 (by norm_num),
    p 5 (by norm_num), p 6 (by norm_num), p 7 (by norm_num), p 8 (by norm_num), p 9 (by norm_num),
    p 10 (by norm_num), p 11 (by norm_num), p 12 (by norm_num), p 13 (by norm_num), p 14 (by norm_num),
    p 15 (by norm_num), p 16 (by norm_num), p 17 (by norm_num), p 18 (by norm_num), p 19 (by norm_num),
    p 20 (by norm_num), p 21 (by norm_num), p 22 (by norm_num), p 23 (by norm_num), p 24 (by norm_num),
    p 25 (by norm_num), p 26 (by norm_num), p 27 (by norm_num), p 28 (by norm_num), p 29 (by norm_num),
    p 30 (by norm_num), p 31 (by norm_num), p 32 (by norm_num), p 33 (by norm_num)]

/-- The prologue cost is polynomial: `Cpro d n m M ≤ 10^28 (d + m + size n + size M + 1)^35`. -/
theorem Cpro_le (d n m M : ℕ) : Cpro d n m M ≤ 10 ^ 28 * (d + m + n.size + M.size + 1) ^ 35 := by
  have h1 := CpL_le d n m M
  have h2 := Cset_le d n m M
  set Y := d + m + n.size + M.size + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have a1 : Y ^ 33 ≤ Y ^ 35 := Nat.pow_le_pow_right hY1 (by norm_num)
  have a2 : Y ^ 34 ≤ Y ^ 35 := Nat.pow_le_pow_right hY1 (by norm_num)
  unfold Cpro
  linarith

/-- The bound of the machine clauses in the frozen form. -/
theorem bound_mach (CU' : ℝ) (kU : ℕ) : ∃ (C' : ℝ) (k' : ℕ), ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ), InputOK d n m M A b →
    0 ≤ CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
      sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU →
    Bmach d n m M (CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
      sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU) ≤
      C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k' :=
  bound_mach_gen Kc Cpro (10 ^ 28) 35 Kc_le Cpro_le CU' kU

/-- The regret bound of Theorem U at `δ = 1/(n+1)` against the bound of the corollary. -/
theorem bound_reg (CU : ℝ) {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    CU * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) ^ 5 + 1 ≤
      (32 * |CU| + 7) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n) ^ 5 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : 2 * (d : ℝ) * n / ((δK n : ℚ) : ℝ) = 2 * d * n * (n + 1) := by
    unfold δK; push_cast; field_simp
  rw [e]
  set L := Real.log (2 * d * n) with hL
  set L' := Real.log (2 * d * n * (n + 1)) with hL'
  set X := (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n with hX
  have hX1 : 1 ≤ X := by
    have h1 : 1 ≤ (d : ℝ) ^ (3 / 2 : ℝ) := Real.one_le_rpow hd' (by norm_num)
    have h2 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn'
    nlinarith
  have hdn : (2 : ℝ) ≤ 2 * d * n := by nlinarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hdn
  have hlog2 := Real.log_two_gt_d9
  have hL0 : 0 ≤ L := by linarith
  have hL'0 : 0 ≤ L' := Real.log_nonneg (by nlinarith)
  have hL'le : L' ≤ 2 * L := by
    rw [hL', hL, ← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [show ((2 : ℝ) * d * n) ^ (2 : ℝ) = (2 * d * n) * (2 * d * n) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
    have : (n : ℝ) + 1 ≤ 2 * d * n := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h5 : L' ^ 5 ≤ 32 * L ^ 5 := by
    have := pow_le_pow_left₀ hL'0 hL'le 5
    calc L' ^ 5 ≤ (2 * L) ^ 5 := this
      _ = 32 * L ^ 5 := by ring
  have hL5 : 1 / 7 ≤ L ^ 5 := by
    have : (0.6931471803 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    have h' : (1 / 7 : ℝ) ≤ (0.6931471803 : ℝ) ^ 5 := by norm_num
    linarith
  have hC : CU * X * L' ^ 5 ≤ 32 * |CU| * X * L ^ 5 := by
    have h1 : CU * X * L' ^ 5 ≤ |CU| * X * L' ^ 5 := by
      have := le_abs_self CU
      have : 0 ≤ X * L' ^ 5 := by positivity
      nlinarith
    have h2 : |CU| * X * L' ^ 5 ≤ |CU| * X * (32 * L ^ 5) := by
      have : 0 ≤ |CU| * X := by positivity
      exact mul_le_mul_of_nonneg_left h5 this
    linarith
  have h7 : 1 ≤ 7 * X * L ^ 5 := by nlinarith
  have e1 : CU * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L' ^ 5 = CU * X * L' ^ 5 := by rw [hX]; ring
  have e2 : (32 * |CU| + 7) * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * L ^ 5 =
      32 * |CU| * X * L ^ 5 + 7 * X * L ^ 5 := by rw [hX]; ring
  rw [e1, e2]
  linarith

end AdversarialBco.UniPoly

open MeasureTheory ProbabilityTheory

namespace AdversarialBco

open BitRAM BitRAMO Unified UniPoly
open RealRAM (Strategy lossAd regretPts polytope HeightLE)

/-- **Corollary P**: Theorem U gives Conjecture 1 of Bubeck, Eldan and Lee in the bit-cost model, in expectation and
with high probability. -/
theorem conj1BitHP_of_unified : TheoremUnified → TheoremConj1UpperBitHP := by
  rintro ⟨P, CU, CU', kU, D, D', hU⟩
  obtain ⟨C', k', hB⟩ := bound_mach CU' kU
  refine ⟨progP P, 32 * |CU| + 7, C', k', ?_⟩
  intro d hd n hn m M A b hH hball hdiam Θ _ ρ hρ σ hσ
  have hI : Bit.Asm.InputOK d n m M A b := ⟨hd, hn, hH, hball, hdiam⟩
  have hδ0 : (0 : ℚ) < δK n := by unfold δK; positivity
  have hδ1 : δK n < 1 := by
    unfold δK
    rw [div_lt_one (by positivity)]
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : (0 : ℚ) < 1 / 2 := by norm_num
  have hr0R : (1 / 2 : ℚ) ≤ n := by
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hb1, hb2⟩ := Bit.ApQ.frameQ_ball hI
  have hb1' : Metric.closedBall (toE (Bit.RQ.frameQ d n m A b)) (((1 / 2 : ℚ)) : ℝ) ⊆ polytope A b := by
    push_cast; exact hb1
  have hb2' : polytope A b ⊆ Metric.closedBall (toE (Bit.RQ.frameQ d n m A b)) (((n : ℚ)) : ℝ) := by
    push_cast; exact hb2
  have hU' := hU d hd n hn (δK n) (1 / 2) n hδ0 hδ1 hr0 hr0R (Bit.RQ.frameQ d n m A b) (polytope A b)
    (Conj1Poly.isCompact_polytope A b n hdiam) (Conj1Poly.convex_polytope A b) hb1' hb2' (orcK A b)
    (@UnifiedSanity.weakMemOracle_exact d (polytope A b) (fun _ => Classical.dec _))
  set BU : ℝ := CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
      sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU with hBU
  have hm1 : ∀ θ cs, CostOKO P (worldO A b (gw P ⟨σ θ, cs⟩ n m A b)) (s0U d n m A b) n BU ∧
      SpaceOKO P (worldO A b (gw P ⟨σ θ, cs⟩ n m A b)) (s0U d n m A b) n BU ∧
      (∀ t < n, playedO P (worldO A b (gw P ⟨σ θ, cs⟩ n m A b)) (s0U d n m A b) t ∈ polytope A b) := by
    intro θ cs
    obtain ⟨h1, h2, h3, -⟩ := hU'.1 (gw P ⟨σ θ, cs⟩ n m A b).f (fun _ => 0) cs (adm_gw P hσ θ cs)
    exact ⟨h1, h2, h3⟩
  refine ⟨fun θ cs => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hm1 θ cs
    have hBU0 : 0 ≤ BU := by
      have := h2 0 (by show 0 < n; omega) ∅ (by simp)
      simpa using this
    obtain ⟨hc, hs⟩ := mach P hI ⟨σ θ, cs⟩ h1 h2 h3 (adm_gw P hσ θ cs)
    have hb := hB d n m M A b hI hBU0
    refine ⟨fun k hk => ?_, fun k hk => Bit.Transfer.spaceLE_mono (hs k hk) hb, fun t ht => ?_⟩
    · obtain ⟨j, hj1, hj2⟩ := hc k hk
      exact ⟨j, hj1, hj2.trans (by linarith)⟩
    · rw [plays_eq P hI ⟨σ θ, cs⟩ h1 t ht]; exact h3 t ht
  -- the regret
  have hNA := env_noisy P hI ρ σ hσ (D d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b))
    (D' d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b)) (BU := BU)
    (fun f cs hf => by obtain ⟨h1, -, h3, h4⟩ := hU'.1 f (fun _ => 0) cs hf; exact ⟨h1, h3, h4⟩)
  obtain ⟨hmeas, hint, hprob, hexp⟩ := hU'.2 (Θ × (ℕ → Bool)) (ρ.prod coinStream) Prod.snd (lossE P σ n m A b)
    (fun _ _ => 0) hNA
  have hfeq : ∀ ω : Θ × (ℕ → Bool),
      regretPts (polytope A b) (lossAd (σ ω.1) 0 (playedBit (progP P) ⟨σ ω.1, ω.2⟩ (initBit d n m A b)))
        (playedBit (progP P) ⟨σ ω.1, ω.2⟩ (initBit d n m A b)) n =
      regretU P (polytope A b) n (initU d n (δK n) (1 / 2) n (Bit.RQ.frameQ d n m A b))
        (envWorld (orcK A b) Prod.snd (lossE P σ n m A b) (fun _ _ => 0) ω) := by
    intro ω
    unfold regretU
    exact regretPts_congr _ _ n (plays_eq P hI ⟨σ ω.1, ω.2⟩ (hm1 ω.1 ω.2).1)
  simp only [hfeq]
  have hreg := bound_reg CU hd hn
  have hδn : (((δK n : ℚ) : ℝ)) ≤ 1 / n := by
    unfold δK; push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hnδ : (n : ℝ) * ((δK n : ℚ) : ℝ) ≤ 1 := by
    unfold δK; push_cast
    rw [mul_one_div, div_le_one (by positivity)]; linarith
  refine ⟨hmeas, hint, ?_, ?_⟩
  · refine hexp.trans ?_
    linarith
  · refine le_trans (measure_mono fun ω hω => ?_) (hprob.trans (ENNReal.ofReal_le_ofReal hδn))
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith

end AdversarialBco
