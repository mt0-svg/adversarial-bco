/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLRun
public import AdversarialBco.Bit.BLBasic
public import AdversarialBco.Bit.CoinSchedLaw
public import AdversarialBco.Bit.BoxMuller

@[expose] public section

/-!
# Piece B of the cut of `RunOK`: BL's draws

* `bitsB : BitsB` (the lemma of the draws (b)): under the Gaussian stream, BL's draws of the rounds `t < n`
  are unsound (`(Ebits R d n)ᶜ`) with probability at most `2^{-p-2}`.
* `measDrawB : MeasDrawB`: BL's draw `ξ'_t` is measurable for the sigma-field of the draw group
  `ξg d t`.

The draws: block `q` of round `t` reads the cells `U = ⌈2^B u⌉ - 1`, `W = ⌈2^B w⌉ - 1` of the exact pair
`(u, w) = bmInv (x, y)` of its two terms `(x, y)` of the stream (`readCoins_blk_u`, `readCoins_blk_w`), and BM-INT's
outputs are within `2^{-B}` of Box-Muller at `((U + 1)/2^B, (W + 1)/2^B)` (`gsSpec_err`), which is within
`K = 2^{1 - B/2} + 2π B^{1/2} 2^{-B}` of Box-Muller at `(u, w)`, that is of `(x, y)` (`bm_bmInv`), off the event
`badBM B` of `boxMuller_pair` (`gOut_err`). So the draws of round `t` are within `K + 2^{-B} ≤ 4/2^{B/2}` of the
terms of the draw group and the dither (`errB_le`). Each block's pair `(u, w)` is uniform on `(0, 1]²` (`uw_pair_law`,
from `map_bmInv`), so the event `badBM B` has probability at most `2^{-B/2}` (`boxMuller_pair`), and the union over
the `n (⌈d/2⌉ + 1)` blocks is at most `2^{-p-2}` (`coins_le`, `B/2 = p + size (n (d + 2)) + 2`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AdversarialBco.Bit.PieceB

open AdversarialBco.BitRAM AdversarialBco.RealRAM AdversarialBco.Bit.Cpl AdversarialBco.Bit.Sched
open AdversarialBco.Bit.BLP
open AdversarialBco.Poly.Layer2 (WΩ)

/-! ## The exact pair of a block -/

theorem bm_bmInv (p : ℝ × ℝ) : bm (bmInv p) = p := by
  rcases p with ⟨x, y⟩
  let z : ℂ := Complex.mk x y
  have hz_re : z.re = x := rfl
  have hz_im : z.im = y := rfl
  set r := Real.sqrt (x ^ 2 + y ^ 2) with hr
  set a := Complex.arg z with ha
  have hlog : Real.log (Real.exp (-(x ^ 2 + y ^ 2) / 2)) = -(x ^ 2 + y ^ 2) / 2 :=
    Real.log_exp (-(x ^ 2 + y ^ 2) / 2)
  have hsqrt : Real.sqrt (-2 * Real.log (Real.exp (-(x ^ 2 + y ^ 2) / 2))) = r := by
    rw [hlog, hr]
    ring_nf
  have hnorm : ‖z‖ = r := by
    rw [Complex.norm_def, Complex.normSq_apply, hz_re, hz_im, hr]
    simp [sq]
  have hcos_arg : 2 * Real.pi * (if 0 < a then a / (2 * Real.pi) else a / (2 * Real.pi) + 1) =
      if 0 < a then a else a + 2 * Real.pi := by
    by_cases h : 0 < a
    · rw [ite_eq_left h, ite_eq_left h]
      field_simp
    · rw [ite_eq_right h, ite_eq_right h]
      field_simp
  have hcos : Real.cos (if 0 < a then a else a + 2 * Real.pi) = Real.cos a := by
    by_cases h : 0 < a
    · simp [h]
    · simp [h, Real.cos_add_two_pi]
  have hsin : Real.sin (if 0 < a then a else a + 2 * Real.pi) = Real.sin a := by
    by_cases h : 0 < a
    · simp [h]
    · simp [h, Real.sin_add_two_pi]
  have hcos_eq : r * Real.cos a = x := by
    calc
      r * Real.cos a = ‖z‖ * Real.cos (Complex.arg z) := by rw [hnorm, ha]
      _ = z.re := by rw [Complex.norm_mul_cos_arg]
      _ = x := hz_re
  have hsin_eq : r * Real.sin a = y := by
    calc
      r * Real.sin a = ‖z‖ * Real.sin (Complex.arg z) := by rw [hnorm, ha]
      _ = z.im := by rw [Complex.norm_mul_sin_arg]
      _ = y := hz_im
  dsimp [bm, bmInv, bmW]
  rw [hsqrt]
  rw [hcos_arg]
  rw [hcos, hsin]
  exact Prod.ext hcos_eq hsin_eq

theorem pair_law {a b : ℕ} (hab : a ≠ b) :
    gaussStream.map (fun x : ℕ → ℝ => (x a, x b)) = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let e : Fin 2 → ℕ := ![a, b]
  have he : Function.Injective e := by
    intro i j h
    have h0 : e 0 = a := rfl
    have h1 : e 1 = b := rfl
    fin_cases i <;> fin_cases j <;> simp [e, h0, h1] at h ⊢ <;> first | rfl | exact (hab h).elim | exact (hab h.symm).elim
  let f : (ℕ → ℝ) → (Fin 2 → ℝ) := fun x i => x (e i)
  have h_map := infinitePi_map_comp_injective (gaussianReal 0 1) he
  have h_finTwoArrow_map : (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map
      MeasurableEquiv.finTwoArrow = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    rw [Measure.infinitePi_eq_pi (fun _ => gaussianReal 0 1)]
    exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  have h_meas_f : Measurable f := by
    rw [measurable_pi_iff]
    intro i
    simpa [f] using measurable_pi_apply (e i)
  calc
    gaussStream.map (fun x : ℕ → ℝ => (x a, x b))
        = gaussStream.map (MeasurableEquiv.finTwoArrow ∘ f) := by
      have h_eq : (fun x : ℕ → ℝ => (x a, x b)) = MeasurableEquiv.finTwoArrow ∘ f := by
        funext x
        calc
          (x a, x b) = (x (e 0), x (e 1)) := by simp [e]
          _ = (f x 0, f x 1) := rfl
          _ = MeasurableEquiv.finTwoArrow (f x) := by rw [MeasurableEquiv.finTwoArrow_apply]
          _ = (MeasurableEquiv.finTwoArrow ∘ f) x := rfl
      rw [h_eq]
    _ = (gaussStream.map f).map MeasurableEquiv.finTwoArrow := by
      rw [(Measure.map_map (MeasurableEquiv.measurable _) h_meas_f).symm]
    _ = ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map f).map MeasurableEquiv.finTwoArrow := rfl
    _ = (Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map MeasurableEquiv.finTwoArrow := by
      rw [h_map]
    _ = (gaussianReal 0 1).prod (gaussianReal 0 1) := by rw [h_finTwoArrow_map]

theorem uw_pair_law {a b : ℕ} (hab : a ≠ b) :
    gaussStream.map (fun x : ℕ → ℝ => bmInv (x a, x b)) =
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hpair_meas : Measurable (fun x : ℕ → ℝ => (x a, x b)) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  calc
    gaussStream.map (fun x : ℕ → ℝ => bmInv (x a, x b))
        = (gaussStream.map (fun x : ℕ → ℝ => (x a, x b))).map bmInv := by
      rw [Measure.map_map measurable_bmInv hpair_meas, ← Function.comp_def]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map bmInv := by rw [pair_law hab]
    _ = (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by rw [map_bmInv]

/-- The coupling bound of `boxMuller_path`: `2^{1 - B/2} + 2π B^{1/2} 2^{-B}`. -/
noncomputable def KB (B : ℕ) : ℝ := (2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ))

/-- The event of `boxMuller_pair`: Box-Muller at `(u, w)` and at the rounded pair differ by more than `KB B`. -/
def badBM (B : ℕ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | KB B < |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
      Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
        Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| ∨
    KB B < |Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2) -
      Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
        Real.sin (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|}

theorem gauss_bad_le {a b : ℕ} (hab : a ≠ b) (B : ℕ) :
    gaussStream {x : ℕ → ℝ | bmInv (x a, x b) ∈ badBM B} ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
  have h_meas : AEMeasurable (fun x : ℕ → ℝ => bmInv (x a, x b)) gaussStream :=
    (Sched.measurable_bmInv.comp ((measurable_pi_apply a).prodMk (measurable_pi_apply b))).aemeasurable
  calc
    gaussStream {x : ℕ → ℝ | bmInv (x a, x b) ∈ badBM B}
        = gaussStream ((fun x : ℕ → ℝ => bmInv (x a, x b)) ⁻¹' (badBM B)) := rfl
    _ ≤ (gaussStream.map (fun x : ℕ → ℝ => bmInv (x a, x b))) (badBM B) :=
      MeasureTheory.Measure.le_map_apply h_meas (badBM B)
    _ = ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) (badBM B) := by
      rw [uw_pair_law hab]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
      have h_badBM : badBM B = {p : ℝ × ℝ | KB B < |Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2) -
          Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
            Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))| ∨
          KB B < |Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2) -
          Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * p.1⌉ : ℝ) / 2 ^ B)) *
            Real.sin (2 * Real.pi * ((⌈(2 : ℝ) ^ B * p.2⌉ : ℝ) / 2 ^ B))|} := by
        ext p; simp [badBM, KB]
      rw [h_badBM]
      exact Bit.boxMuller_pair B

/-! ## One block -/

/-- The error of a draw on a good block: `KB B + 2^{-B}`. -/
noncomputable def errB (B : ℕ) : ℝ := KB B + 1 / 2 ^ B

theorem sqrt_le_half_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ (x + 1) / 2 := by
  have hsq : (Real.sqrt x)^2 ≤ ((x + 1) / 2)^2 := by
    calc
      (Real.sqrt x)^2 = x := Real.sq_sqrt hx
      _ ≤ ((x + 1) / 2)^2 := by
        have h : ((x + 1) / 2)^2 - x = (x - 1)^2 / 4 := by ring
        have hnonneg : 0 ≤ (x - 1)^2 / 4 := by positivity
        linarith
  have h_nonneg_sqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h_nonneg_frac : 0 ≤ (x + 1) / 2 := by linarith
  have h_sq_eq : ((Real.sqrt x) - ((x + 1) / 2)) * ((Real.sqrt x) + ((x + 1) / 2)) = (Real.sqrt x)^2 - ((x + 1) / 2)^2 := by ring
  have h_nonpos : (Real.sqrt x) - ((x + 1) / 2) ≤ 0 := by
    by_contra! hpos
    have hsum_pos : 0 < (Real.sqrt x) + ((x + 1) / 2) := by linarith
    have hprod_pos : 0 < ((Real.sqrt x) - ((x + 1) / 2)) * ((Real.sqrt x) + ((x + 1) / 2)) := by
      exact mul_pos hpos hsum_pos
    rw [h_sq_eq] at hprod_pos
    linarith
  linarith

-- Helper lemma: the key inequality 2π√(2k) + 1 ≤ 2^(k+1) for k ≥ 4
theorem errB_aux {k : ℕ} (hk : 4 ≤ k) : (2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1 ≤ (2 : ℝ) ^ ((k : ℝ) + 1) := by
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hsqrt : Real.sqrt (2 * (k : ℝ)) ≤ ((2 * (k : ℝ)) + 1) / 2 := by
    apply sqrt_le_half_add_one
    positivity
  have hbound : (2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1 ≤ (2 : ℝ) * (3.15 : ℝ) * (((2 * (k : ℝ)) + 1) / 2) + 1 := by
    have h_mul : (2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) ≤ (2 : ℝ) * (3.15 : ℝ) * (((2 * (k : ℝ)) + 1) / 2) := by
      have ha : 0 ≤ (2 : ℝ) * Real.pi := by nlinarith [Real.pi_pos.le]
      have hb : 0 ≤ (2 : ℝ) * (3.15 : ℝ) := by norm_num
      have hc : 0 ≤ Real.sqrt (2 * (k : ℝ)) := Real.sqrt_nonneg _
      have hd : 0 ≤ ((2 * (k : ℝ)) + 1) / 2 := by
        refine div_nonneg ?_ (by norm_num)
        have : 0 ≤ (2 : ℝ) * (k : ℝ) := by
          positivity
        positivity
      have h1 : (2 : ℝ) * Real.pi ≤ (2 : ℝ) * (3.15 : ℝ) := by linarith
      have h2 : Real.sqrt (2 * (k : ℝ)) ≤ ((2 * (k : ℝ)) + 1) / 2 := hsqrt
      exact mul_le_mul h1 h2 hc hb
    linarith
  have hsimpl : (2 : ℝ) * (3.15 : ℝ) * (((2 * (k : ℝ)) + 1) / 2) + 1 = (6.3 : ℝ) * (k : ℝ) + 4.15 := by
    ring
  rw [hsimpl] at hbound
  have h_induction : ∀ (m : ℕ), 4 ≤ m → (6.3 : ℝ) * (m : ℝ) + 4.15 ≤ (2 : ℝ) ^ ((m : ℝ) + 1) := by
    intro m hm
    refine Nat.le_induction ?base ?step m hm
    · norm_num
    · intro n hn ih
      have h_pow_ge : (6.3 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := by
        have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h_exp : (5 : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h_pow_le : (2 : ℝ) ^ (5 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) h_exp
        have h_32 : (2 : ℝ) ^ (5 : ℝ) = (32 : ℝ) := by norm_num
        rw [h_32] at h_pow_le
        linarith
      have h_ih_cast : (6.3 : ℝ) * (n : ℝ) + 4.15 ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := ih
      have h_left : (6.3 : ℝ) * ((n : ℕ).succ : ℝ) + 4.15 = ((6.3 : ℝ) * (n : ℝ) + 4.15) + 6.3 := by
        push_cast
        ring
      rw [h_left]
      calc
        ((6.3 : ℝ) * (n : ℝ) + 4.15) + 6.3 ≤ (2 : ℝ) ^ ((n : ℝ) + 1) + 6.3 := by linarith
        _ ≤ (2 : ℝ) ^ ((n : ℝ) + 1) + (2 : ℝ) ^ ((n : ℝ) + 1) := by linarith
        _ = 2 * (2 : ℝ) ^ ((n : ℝ) + 1) := by ring
        _ = (2 : ℝ) ^ (((n : ℝ) + 1) + 1) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < (2 : ℝ)) ((n : ℝ) + 1) (1 : ℝ)]
          ring
        _ = (2 : ℝ) ^ (((n : ℕ).succ : ℝ) + 1) := by
          push_cast
          ring
  exact le_trans hbound (h_induction k hk)

theorem errB_le {B : ℕ} (hB : 8 ≤ B) (hev : Even B) : errB B ≤ 4 / 2 ^ (B / 2) := by
  rcases hev with ⟨k, hk⟩
  -- hk : B = k + k
  have hk4 : 4 ≤ k := by
    omega
  have hdiv : B / 2 = k := by
    rw [hk]
    omega
  rw [hdiv, hk]
  -- goal: errB (k + k) ≤ 4 / 2 ^ k
  unfold errB KB
  -- simplify the casts from ℕ to ℝ
  simp only [Nat.cast_add]
  -- simplify: ↑k + ↑k = 2 * ↑k
  have hkcast : (k : ℝ) + (k : ℝ) = 2 * (k : ℝ) := by ring
  rw [hkcast]
  -- simplify exponents
  have h_exp1 : (1 : ℝ) - (2 * (k : ℝ)) / 2 = (1 : ℝ) - (k : ℝ) := by ring
  rw [h_exp1]
  have h_exp2 : (-(2 * (k : ℝ))) = -2 * (k : ℝ) := by ring
  rw [h_exp2]
  -- Now the goal is: (2 : ℝ) ^ (1 - (k : ℝ)) + 2 * Real.pi * Real.sqrt (2 * (k : ℝ)) * (2 : ℝ) ^ (-2 * (k : ℝ)) + 1 / ((2 : ℕ) ^ (k + k) : ℝ) ≤ 4 / ((2 : ℕ) ^ k : ℝ)
  -- Let c = 2^(-k)
  set c := (2 : ℝ) ^ (-(k : ℝ)) with hc_def
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _
  have hc_nonneg : 0 ≤ c := hc_pos.le
  -- identities relating powers of 2 to c
  have h_pow1 : (2 : ℝ) ^ (1 - (k : ℝ)) = 2 * c := by
    rw [hc_def]
    calc
      (2 : ℝ) ^ (1 - (k : ℝ)) = (2 : ℝ) ^ ((1 : ℝ) + (-(k : ℝ))) := by ring_nf
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (1 : ℝ) (-(k : ℝ))]
      _ = 2 * (2 : ℝ) ^ (-(k : ℝ)) := by norm_num
  have h_pow2 : (2 : ℝ) ^ (-2 * (k : ℝ)) = c ^ 2 := by
    rw [hc_def]
    calc
      (2 : ℝ) ^ (-2 * (k : ℝ)) = (2 : ℝ) ^ ((-(k : ℝ)) * 2) := by ring_nf
      _ = ((2 : ℝ) ^ (-(k : ℝ))) ^ 2 := by
        simpa using (Real.rpow_mul (show 0 ≤ (2 : ℝ) from by norm_num) (-(k : ℝ)) 2)
      _ = c ^ 2 := rfl
  have h_denom1 : (2 ^ (k + k) : ℝ) = ((2 ^ k : ℕ) : ℝ) ^ 2 := by
    simp [pow_add, pow_two]
  have h_denom2 : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by simp
  have h_c_inv : (2 : ℝ) ^ (k : ℝ) = c⁻¹ := by
    rw [hc_def]
    -- c = 2^(-k) = (2^k)⁻¹, so c⁻¹ = 2^k
    rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) from by norm_num) (k : ℝ)]
    -- now c = (2^k)⁻¹, so c⁻¹ = ((2^k)⁻¹)⁻¹ = 2^k
    field_simp
  -- Also convert (2 : ℝ) ^ (k : ℕ) to (2 : ℝ) ^ (k : ℝ) on the RHS
  have h_denom3 : (2 : ℝ) ^ (k : ℕ) = (2 : ℝ) ^ (k : ℝ) := by simp
  -- Now rewrite the goal using these identities
  rw [h_pow1, h_pow2, h_denom1, h_denom2, h_denom3, h_c_inv]
  -- Goal: 2 * c + 2 * Real.pi * Real.sqrt (2 * (k : ℝ)) * c ^ 2 + 1 / (c⁻¹ ^ 2) ≤ 4 / c⁻¹
  -- Simplify: 1 / (c⁻¹ ^ 2) = c^2, 4 / c⁻¹ = 4 * c
  have h_simp1 : 1 / (c⁻¹ ^ 2) = c ^ 2 := by
    field_simp [hc_pos.ne']
  have h_simp2 : 4 / c⁻¹ = 4 * c := by
    field_simp [hc_pos.ne']
  rw [h_simp1, h_simp2]
  -- Goal: 2 * c + 2 * Real.pi * Real.sqrt (2 * (k : ℝ)) * c ^ 2 + c ^ 2 ≤ 4 * c
  -- Rearrange: (2*π*√(2k) + 1) * c^2 ≤ 2*c
  -- Since c > 0, divide by c: (2*π*√(2k) + 1) * c ≤ 2
  -- Since c > 0, divide by c again: 2*π*√(2k) + 1 ≤ 2/c = 2^(k+1)
  -- This is exactly errB_aux
  have h_aux := errB_aux hk4
  -- h_aux : (2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1 ≤ (2 : ℝ) ^ ((k : ℝ) + 1)
  -- We need to relate (2 : ℝ) ^ ((k : ℝ) + 1) to 2 / c
  have h_rhs : (2 : ℝ) ^ ((k : ℝ) + 1) = 2 / c := by
    rw [hc_def]
    calc
      (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) (k : ℝ) (1 : ℝ)]
      _ = (2 : ℝ) ^ (k : ℝ) * 2 := by norm_num
      _ = 2 * (2 : ℝ) ^ (k : ℝ) := by ring
      _ = 2 * ((2 : ℝ) ^ (-(k : ℝ)))⁻¹ := by
        rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) from by norm_num) (k : ℝ)]
        field_simp
      _ = 2 / c := by
        rw [hc_def]
        ring
  rw [h_rhs] at h_aux
  -- h_aux : (2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1 ≤ 2 / c
  -- Now we have: 2*c + (2*π*√(2k))*c^2 + c^2 ≤ 4*c
  -- i.e. c * (2 + (2*π*√(2k))*c + c) ≤ 4*c
  -- Since c > 0, divide both sides by c:
  -- 2 + (2*π*√(2k))*c + c ≤ 4
  -- i.e. (2*π*√(2k) + 1)*c ≤ 2
  -- This is exactly h_aux multiplied by c
  have h_main : 2 * c + (2 * Real.pi * Real.sqrt (2 * (k : ℝ))) * c ^ 2 + c ^ 2 ≤ 4 * c := by
    have h := mul_le_mul_of_nonneg_right h_aux hc_nonneg
    -- h : ((2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1) * c ≤ (2 / c) * c
    -- (2 / c) * c = 2 (since c ≠ 0)
    have h_right : (2 / c) * c = 2 := by field_simp [hc_pos.ne']
    rw [h_right] at h
    -- h : ((2 : ℝ) * Real.pi * Real.sqrt (2 * (k : ℝ)) + 1) * c ≤ 2
    -- Expand LHS: (2*π*√(2k))*c + c ≤ 2
    -- Add 2*c to both sides: 2*c + (2*π*√(2k))*c + c ≤ 2*c + 2
    -- Wait, that's not right. Let me redo.
    -- h: (2*π*√(2k) + 1)*c ≤ 2
    -- Expand: (2*π*√(2k))*c + c ≤ 2
    -- Multiply both sides by c (c > 0): (2*π*√(2k))*c^2 + c^2 ≤ 2*c
    -- Add 2*c to both sides: 2*c + (2*π*√(2k))*c^2 + c^2 ≤ 4*c
    have h_mul : (2 * Real.pi * Real.sqrt (2 * (k : ℝ))) * c ^ 2 + c ^ 2 ≤ 2 * c := by
      -- From h: (2*π*√(2k) + 1)*c ≤ 2
      -- Multiply both sides by c (> 0)
      nlinarith
    nlinarith
  exact h_main

/-- The two terms of a draw block: roles `2q`, `2q + 1` of round `t`. -/
theorem blkPair_draw (d : ℕ) (x : ℕ → ℝ) (t q : ℕ) (hq : q < (d + 1) / 2) :
    blkPair d x (t * nBlk d + q) = (x (cIdx d t (2 * q)), x (cIdx d t (2 * q + 1))) := by
  have hnBlk_pos : 0 < nBlk d := by
    unfold nBlk
    omega
  have hq_lt_nBlk : q < nBlk d := by
    unfold nBlk
    omega
  have hmod : (t * nBlk d + q) % nBlk d = q := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq_lt_nBlk]
  have hdiv : (t * nBlk d + q) / nBlk d = t := by
    rw [add_comm, Nat.add_mul_div_right _ _ hnBlk_pos, Nat.div_eq_of_lt hq_lt_nBlk, zero_add]
  have h_not_last' : q + 1 ≠ nBlk d := by
    have : q + 1 < nBlk d := by
      unfold nBlk
      omega
    omega
  unfold blkPair
  simp [pairOf, hdiv, hmod, h_not_last']

/-- The two terms of the dither block: roles `d + 1`, `d + 2` of round `t`. -/
theorem blkPair_dither (d : ℕ) (x : ℕ → ℝ) (t : ℕ) :
    blkPair d x (t * nBlk d + (d + 1) / 2) = (x (cIdx d t (d + 1)), x (cIdx d t (d + 2))) := by
  have h_lt : (d + 1) / 2 < nBlk d := by
    unfold nBlk
    omega
  have hmod : (t * nBlk d + (d + 1) / 2) % nBlk d = (d + 1) / 2 := by
    rw [Nat.add_mod]
    have h1 : t * nBlk d % nBlk d = 0 := by
      rw [mul_comm, Nat.mul_mod_right]
    rw [h1, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt h_lt
  have hcond : (t * nBlk d + (d + 1) / 2) % nBlk d + 1 = nBlk d := by
    rw [hmod]
    unfold nBlk
    omega
  have hdiv : (t * nBlk d + (d + 1) / 2) / nBlk d = t := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul]
      exact Nat.add_lt_add_left h_lt (t * nBlk d)
  have hmod_small : (d + 1) / 2 % nBlk d = (d + 1) / 2 :=
    Nat.mod_eq_of_lt h_lt
  have hcond' : (d + 1) / 2 % nBlk d + 1 = nBlk d := by
    rw [hmod_small]
    unfold nBlk
    omega
  unfold blkPair
  simp [pairOf, hdiv, hcond']

theorem coins_arith (n d p : ℕ) :
    (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((2 * (p + (n * (d + 2)).size + 2) : ℕ) : ℝ) / 2) ≤
      1 / 2 ^ p / 4 := by
  set N := n * (d + 2) with hN
  set s := N.size with hs
  have hpos2 : 0 ≤ (2 : ℝ) := by norm_num
  have hpos2' : 0 < (2 : ℝ) := by norm_num
  have hN_lt_nat : N < 2 ^ s := by
    rw [hs]
    exact Nat.lt_size_self N
  have hN_lt : (N : ℝ) < (2 : ℝ) ^ s := by
    exact_mod_cast hN_lt_nat
  have h_div_le_nat : ((d + 1) / 2 + 1 : ℕ) ≤ (d + 2 : ℕ) := by
    have h : (d + 1) / 2 ≤ d + 1 := Nat.div_le_self (d + 1) 2
    omega
  have h_div_le : (((d + 1) / 2 + 1 : ℕ) : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by
    exact_mod_cast h_div_le_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h_mul_le : (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    simpa [N, Nat.cast_mul] using mul_le_mul_of_nonneg_left h_div_le hn_nonneg
  have h_power_eq : (2 : ℝ) ^ (-((2 * (p + s + 2) : ℕ) : ℝ) / 2) = 1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4) := by
    calc
      (2 : ℝ) ^ (-((2 * (p + s + 2) : ℕ) : ℝ) / 2) = (2 : ℝ) ^ (-(((p + s + 2 : ℕ) : ℝ))) := by
        push_cast
        have h : -(2 * ((p : ℝ) + (s : ℝ) + 2)) / 2 = -(((p : ℝ) + (s : ℝ) + 2)) := by
          field_simp
        rw [h]
      _ = ((2 : ℝ) ^ (((p + s + 2 : ℕ) : ℝ)))⁻¹ := by rw [Real.rpow_neg hpos2]
      _ = ((2 : ℝ) ^ ((p : ℝ) + (s : ℝ) + 2))⁻¹ := by
        push_cast
        rfl
      _ = ((2 : ℝ) ^ ((p : ℝ) + ((s : ℝ) + 2)))⁻¹ := by
        simp [add_assoc]
      _ = (((2 : ℝ) ^ (p : ℝ)) * ((2 : ℝ) ^ ((s : ℝ) + 2)))⁻¹ := by
        rw [Real.rpow_add hpos2' (p : ℝ) ((s : ℝ) + 2)]
      _ = (((2 : ℝ) ^ (p : ℝ)) * (((2 : ℝ) ^ (s : ℝ)) * ((2 : ℝ) ^ (2 : ℝ))))⁻¹ := by
        rw [Real.rpow_add hpos2' (s : ℝ) 2]
      _ = (((2 : ℝ) ^ (p : ℝ)) * ((2 : ℝ) ^ (s : ℝ)) * ((2 : ℝ) ^ (2 : ℝ)))⁻¹ := by ring
      _ = (((2 : ℝ) ^ p) * ((2 : ℝ) ^ s) * ((2 : ℝ) ^ 2))⁻¹ := by
        simp [Real.rpow_natCast]
      _ = (((2 : ℝ) ^ p) * ((2 : ℝ) ^ s) * 4)⁻¹ := by norm_num
      _ = 1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4) := by ring
  rw [h_power_eq]
  have h_denom_nonneg : 0 ≤ (2 : ℝ) ^ p * (2 : ℝ) ^ s * 4 := by
    positivity
  have h_left : (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) ≤
      (N : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) := by
    have h := mul_le_mul_of_nonneg_right h_mul_le (by
      have : 0 ≤ 1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4) := by
        refine div_nonneg ?_ h_denom_nonneg
        norm_num
      exact this)
    -- h : (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / ...) ≤ (N : ℝ) * (1 / ...)
    -- but we have three factors: a * b * c, which is (a * b) * c
    -- h_mul_le is a * b ≤ N, so we need (a * b) * c ≤ N * c
    calc
      (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) =
          ((n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ)) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) := by ring
      _ ≤ (N : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) := h
  have hN_div : (N : ℝ) / ((2 : ℝ) ^ s) ≤ 1 := by
    refine (div_le_one ?_).mpr hN_lt.le
    positivity
  have h_right : (N : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) ≤ 1 / ((2 : ℝ) ^ p * 4) := by
    calc
      (N : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) = ((N : ℝ) / ((2 : ℝ) ^ s)) / ((2 : ℝ) ^ p * 4) := by
        ring
      _ ≤ 1 / ((2 : ℝ) ^ p * 4) := by
        have hpos : 0 ≤ (2 : ℝ) ^ p * 4 := by positivity
        exact div_le_div_of_nonneg_right hN_div hpos
  have h_right' : 1 / ((2 : ℝ) ^ p * 4) = 1 / 2 ^ p / 4 := by
    ring
  calc
    (n : ℝ) * (((d + 1) / 2 + 1 : ℕ) : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) ≤
        (N : ℝ) * (1 / ((2 : ℝ) ^ p * (2 : ℝ) ^ s * 4)) := h_left
    _ ≤ 1 / ((2 : ℝ) ^ p * 4) := h_right
    _ = 1 / 2 ^ p / 4 := by ring

/-! ## The draw group determines the draw -/

/-- The stream with the draw group `y` of round `t` (roles `c ≤ d`) and `0` elsewhere. -/
noncomputable def extG (d t : ℕ) (y : Fin (d + 1) → ℝ) : ℕ → ℝ :=
  Function.extend (fun c : Fin (d + 1) => cIdx d t c) y 0

theorem extG_cIdx (d t : ℕ) (y : Fin (d + 1) → ℝ) (c : Fin (d + 1)) : extG d t y (cIdx d t c) = y c := by
  unfold extG
  have hinj : Function.Injective (fun c : Fin (d + 1) => cIdx d t c) := by
    intro a b h
    apply Fin.ext
    unfold cIdx at h
    have h' : t * (d + 5) + a.val = t * (d + 5) + b.val :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h
    omega
  exact Function.Injective.extend_apply hinj y 0 c

theorem measurable_extG (d t : ℕ) : Measurable (extG d t) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : ∃ c : Fin (d + 1), cIdx d t c = i
  · rcases h with ⟨c, hc⟩
    subst hc
    have h_eq : (fun (y : Fin (d + 1) → ℝ) => extG d t y (cIdx d t c)) = fun y => y c := by
      ext y
      exact extG_cIdx d t y c
    rw [h_eq]
    exact measurable_pi_apply c
  · have h_ne : ¬∃ (a : Fin (d + 1)), (fun c : Fin (d + 1) => cIdx d t c) a = i := by
      simpa using h
    have h_val : ∀ y : Fin (d + 1) → ℝ, extG d t y i = (0 : ℝ) := by
      intro y
      dsimp [extG]
      rw [Function.extend_apply' y (0 : ℕ → ℝ) i h_ne]
      rfl
    have h_const : (fun (y : Fin (d + 1) → ℝ) => extG d t y i) = fun _ => (0 : ℝ) := by
      ext y; exact h_val y
    rw [h_const]
    exact measurable_const

/-- A draw block of round `t` reads the draw group of round `t` only. -/
theorem blkUW_congr_grp {d K0 B : ℕ} (t q : ℕ) (hq : q < (d + 1) / 2) {x x' : ℕ → ℝ}
    (h : ∀ c ≤ d, x (cIdx d t c) = x' (cIdx d t c)) :
    blkUW (beta d K0 B x) K0 B d t q = blkUW (beta d K0 B x') K0 B d t q := by
  have h2q_le_d : 2 * q ≤ d := by
    have h' : 2 * q < d + 1 := by omega
    omega
  have h2q1_le_d : 2 * q + 1 ≤ d := by
    have h' : 2 * q + 1 < d + 1 := by omega
    omega
  have h_beta_eq : ∀ j, blkStart d K0 B t q ≤ j → j < blkStart d K0 B t q + (2 * B) → beta d K0 B x j = beta d K0 B x' j := by
    intro j hj_le hj_lt
    set s := j - blkStart d K0 B t q with hs_def
    have hs_lt : s < 2 * B := by
      rw [hs_def]
      omega
    have hj_eq : j = blkStart d K0 B t q + s := by
      rw [hs_def]
      omega
    have h_blkOf : blkOf K0 B j = .inr (t * nBlk d + q) := by
      rw [hj_eq]
      exact (blkOf_posOf_blkStart hs_lt).1
    have hq_lt_nBlk : q < nBlk d := by
      unfold nBlk
      omega
    have hmod : (t * nBlk d + q) % nBlk d = q := by
      rw [Nat.add_mod]
      have h0 : (t * nBlk d) % nBlk d = 0 := by simp
      rw [h0, zero_add]
      have hq_mod : q % nBlk d = q := Nat.mod_eq_of_lt hq_lt_nBlk
      rw [hq_mod]
      exact Nat.mod_eq_of_lt hq_lt_nBlk
    have h_ineq : t * nBlk d + q < nBlk d * (t + 1) := by
      have h1 : t * nBlk d + q < t * nBlk d + nBlk d := Nat.add_lt_add_left hq_lt_nBlk _
      have h2 : t * nBlk d + nBlk d = nBlk d * (t + 1) := by
        rw [mul_comm t (nBlk d), ← Nat.mul_succ]
      exact h1.trans_eq h2
    have hdiv : (t * nBlk d + q) / nBlk d = t :=
      Nat.div_eq_of_lt_le
        (Nat.le_add_right _ _)
        (by simpa [mul_comm] using h_ineq)
    have hpair : pairOf d (.inr (t * nBlk d + q)) = (cIdx d t (2 * q), cIdx d t (2 * q + 1)) := by
      unfold pairOf
      simp
      rw [Nat.mod_eq_of_lt hq_lt_nBlk, hdiv]
      have h_not_eq : q + 1 ≠ nBlk d := by
        unfold nBlk
        omega
      simp [h_not_eq]
    have h_grp : grp d K0 B j = {cIdx d t (2 * q), cIdx d t (2 * q + 1)} := by
      rw [grp, h_blkOf, hpair]
    apply beta_local d K0 B j x x'
    rw [h_grp]
    intro i hi
    simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with (rfl | rfl)
    · exact h (2 * q) h2q_le_d
    · exact h (2 * q + 1) h2q1_le_d
  unfold blkUW
  have h_first : readCoins (beta d K0 B x) (blkStart d K0 B t q) B = readCoins (beta d K0 B x') (blkStart d K0 B t q) B :=
    BLP.readCoins_congr (beta d K0 B x) (beta d K0 B x') (blkStart d K0 B t q) B (by
      intro j hj_le hj_lt
      apply h_beta_eq j hj_le
      omega)
  have h_second : readCoins (beta d K0 B x) (blkStart d K0 B t q + B) B = readCoins (beta d K0 B x') (blkStart d K0 B t q + B) B :=
    BLP.readCoins_congr (beta d K0 B x) (beta d K0 B x') (blkStart d K0 B t q + B) B (by
      intro j hj_le' hj_lt'
      have hj_le : blkStart d K0 B t q ≤ j := by omega
      apply h_beta_eq j hj_le
      omega)
  simp [h_first, h_second]

theorem measurable_blkUW (d K0 B t q : ℕ) : Measurable fun x : ℕ → ℝ => blkUW (beta d K0 B x) K0 B d t q := by
  have hbeta : Measurable (beta d K0 B) := measurable_beta d K0 B
  have h_readCoins (c k : ℕ) : Measurable (fun (cs : ℕ → Bool) => readCoins cs c k) := by
    induction' k with k ih
    · simp [readCoins]
    · simp [readCoins]
      refine Measurable.add ?_ ?_
      · refine (measurable_const_mul 2).comp ih
      · refine Measurable.ite ?_ measurable_const measurable_const
        -- prove that {cs | cs (c + k) = true} is measurable
        have h_set : MeasurableSet {cs : ℕ → Bool | cs (c + k)} := by
          -- this set is the preimage of {true} under the projection cs ↦ cs (c + k)
          -- which is measurable because projections are measurable
          have h_proj : Measurable (fun (cs : ℕ → Bool) => cs (c + k)) :=
            measurable_pi_apply (c + k)
          have : {cs : ℕ → Bool | cs (c + k)} = (fun (cs : ℕ → Bool) => cs (c + k)) ⁻¹' {true} := by
            ext cs; simp
          rw [this]
          exact measurableSet_preimage h_proj (MeasurableSet.singleton true)
        exact h_set
  have h_toNat : Measurable (Int.toNat : ℤ → ℕ) := Measurable.of_discrete
  have h1 : Measurable (fun (x : ℕ → ℝ) => (readCoins (beta d K0 B x) (Sched.blkStart d K0 B t q) B).toNat) :=
    h_toNat.comp ((h_readCoins (Sched.blkStart d K0 B t q) B).comp hbeta)
  have h2 : Measurable (fun (x : ℕ → ℝ) => (readCoins (beta d K0 B x) (Sched.blkStart d K0 B t q + B) B).toNat) :=
    h_toNat.comp ((h_readCoins (Sched.blkStart d K0 B t q + B) B).comp hbeta)
  simpa [blkUW] using Measurable.prodMk h1 h2
/-! ## The draws of one block -/

/-- BM-INT's outputs on block `q` of round `t` are within `errB B` of the block's two terms of the stream, when the
exact pair of the block is off `badBM B`. -/
theorem gOut_err {d K0 B : ℕ} (t q : ℕ) (hB : 8 ≤ B) (x : ℕ → ℝ)
    (hgood : bmInv (blkPair d x (t * nBlk d + q)) ∉ badBM B) :
    |((gOut B (blkUW (beta d K0 B x) K0 B d t q)).1 : ℝ) - (blkPair d x (t * nBlk d + q)).1| ≤ errB B ∧
      |((gOut B (blkUW (beta d K0 B x) K0 B d t q)).2 : ℝ) - (blkPair d x (t * nBlk d + q)).2| ≤ errB B := by
  set p := blkPair d x (t * nBlk d + q) with hp
  have hu := bmInv_fst_mem p
  have hw := bmInv_snd_mem p
  have hUW : blkUW (beta d K0 B x) K0 B d t q = (cellIdx B (bmInv p).1, cellIdx B (bmInv p).2) := by
    simp only [blkUW, readCoins_blk_u, readCoins_blk_w, Int.toNat_natCast, hp]
  have cell1 : ∀ v : ℝ, 0 < v → v ≤ 1 → ((cellIdx B v : ℕ) : ℝ) + 1 = (⌈(2 : ℝ) ^ B * v⌉ : ℝ) := by
    intro v h0 h1
    have h := cellIdx_eq (B := B) h0 h1
    have h2 : ((cellIdx B v : ℕ) : ℝ) = (((cellIdx B v : ℕ) : ℤ) : ℝ) := by norm_cast
    rw [h2, h]; push_cast; ring
  obtain ⟨h1, h2, -, -⟩ := gsSpec_err B (cellIdx B (bmInv p).1) (cellIdx B (bmInv p).2) hB
    (cellIdx_lt hu.1 hu.2) (cellIdx_lt hw.1 hw.2)
  rw [cell1 _ hu.1 hu.2, cell1 _ hw.1 hw.2] at h1 h2
  have hbm := bm_bmInv p
  simp only [badBM, Set.mem_ofPred_eq, not_or, not_lt] at hgood
  obtain ⟨g1, g2⟩ := hgood
  have e1 : (bm (bmInv p)).1 = p.1 := by rw [hbm]
  have e2 : (bm (bmInv p)).2 = p.2 := by rw [hbm]
  simp only [bm] at e1 e2
  rw [e1] at g1
  rw [e2] at g2
  rw [hUW]
  simp only [gOut]
  push_cast
  unfold errB
  constructor
  · calc _ ≤ _ := abs_sub_le _ (Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * (bmInv p).1⌉ : ℝ) / 2 ^ B)) *
            Real.cos (2 * Real.pi * ((⌈(2 : ℝ) ^ B * (bmInv p).2⌉ : ℝ) / 2 ^ B))) _
      _ ≤ 1 / 2 ^ B + KB B := add_le_add h1 (by rw [abs_sub_comm]; exact g1)
      _ = KB B + 1 / 2 ^ B := add_comm _ _
  · calc _ ≤ _ := abs_sub_le _ (Real.sqrt (-2 * Real.log ((⌈(2 : ℝ) ^ B * (bmInv p).1⌉ : ℝ) / 2 ^ B)) *
            Real.sin (2 * Real.pi * ((⌈(2 : ℝ) ^ B * (bmInv p).2⌉ : ℝ) / 2 ^ B))) _
      _ ≤ 1 / 2 ^ B + KB B := add_le_add h2 (by rw [abs_sub_comm]; exact g2)
      _ = KB B + 1 / 2 ^ B := add_comm _ _

/-! ## BL's parameters -/

theorem par_B (d n : ℕ) : 8 ≤ (par d n).B ∧ Even (par d n).B := by
  refine ⟨?_, ?_⟩
  · show 8 ≤ 2 * (10 * (BLP.Ne d n).size + 16 * d.size + 160 + (n * (d + 2)).size + 2)
    omega
  · exact ⟨_, (two_mul _)⟩

theorem coins_le (d n : ℕ) :
    (n : ℝ) * (nBlk d : ℝ) * (2 : ℝ) ^ (-((par d n).B : ℝ) / 2) ≤ Bud.dbits d n := by
  have h := coins_arith n d (par d n).p
  have hB : (par d n).B = 2 * ((par d n).p + (n * (d + 2)).size + 2) := rfl
  rw [hB]
  simpa [Bud.dbits, Bud.tp, nBlk] using h


/-! ## Piece B -/

/-- Off the bad events of the blocks of the rounds `t < n`, BL's draws are sound. -/
theorem ebits_compl_subset (R : Routines) (d n : ℕ) :
    (Ebits R d n)ᶜ ⊆ ⋃ t ∈ Finset.range n, ⋃ q ∈ Finset.range (nBlk d),
      {ω : WΩ | bmInv (blkPair d ω.1 (t * nBlk d + q)) ∈ badBM (par d n).B} := by
  intro ω hω
  by_contra hno
  apply hω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, not_exists] at hno
  obtain ⟨hB8, hBev⟩ := par_B d n
  have herr := errB_le hB8 hBev
  intro t ht
  have hd : drawW R d n t ω = draw (beta d (R.K0 d n) (par d n).B ω.1) (R.K0 d n) (par d n).B d t := rfl
  rw [hd]
  refine ⟨fun i => ?_, ?_⟩
  · have hq : (i : ℕ) / 2 < (d + 1) / 2 := by have := i.2; omega
    have hgood := hno t ht ((i : ℕ) / 2) (by unfold nBlk; omega)
    obtain ⟨e1, e2⟩ := gOut_err (K0 := R.K0 d n) t ((i : ℕ) / 2) hB8 ω.1 hgood
    rw [blkPair_draw d ω.1 t _ hq] at e1 e2
    simp only [draw, ξc]
    unfold eXi0
    split_ifs with hi
    · have : 2 * ((i : ℕ) / 2) = (i : ℕ) := by omega
      rw [this] at e1
      exact e1.trans herr
    · have : 2 * ((i : ℕ) / 2) + 1 = (i : ℕ) := by omega
      rw [this] at e2
      exact e2.trans herr
  · have hgood := hno t ht ((d + 1) / 2) (by unfold nBlk; omega)
    obtain ⟨e1, -⟩ := gOut_err (K0 := R.K0 d n) t ((d + 1) / 2) hB8 ω.1 hgood
    rw [blkPair_dither d ω.1 t] at e1
    simp only [draw, zc, Matrix.cons_val_zero]
    unfold eZt0
    push_cast
    have h2 : (2 : ℝ) / 2 ^ ((par d n).B / 2) = (4 / 2 ^ ((par d n).B / 2)) / 2 := by ring
    rw [h2, ← sub_div, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (e1.trans herr) (by norm_num)

theorem pairOf_ne (d : ℕ) (s : ℕ ⊕ ℕ) : (pairOf d s).1 ≠ (pairOf d s).2 := by
  intro h
  have := pairIdx_injective d (a₁ := (s, 0)) (a₂ := (s, 1)) (by simpa [pairIdx] using h)
  simp at this

theorem bitsB : BitsB := by
  intro R d n _ _ _
  have hfst : ∀ S : Set (ℕ → ℝ), μs (Measure.dirac 0) {ω : WΩ | ω.1 ∈ S} = gaussStream S := by
    intro S
    have : {ω : WΩ | ω.1 ∈ S} = S ×ˢ Set.univ := by ext ω; simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
  calc μs (Measure.dirac 0) (Ebits R d n)ᶜ
      ≤ μs (Measure.dirac 0) (⋃ t ∈ Finset.range n, ⋃ q ∈ Finset.range (nBlk d),
          {ω : WΩ | bmInv (blkPair d ω.1 (t * nBlk d + q)) ∈ badBM (par d n).B}) :=
        measure_mono (ebits_compl_subset R d n)
    _ ≤ ∑ t ∈ Finset.range n, ∑ q ∈ Finset.range (nBlk d),
          μs (Measure.dirac 0) {ω : WΩ | bmInv (blkPair d ω.1 (t * nBlk d + q)) ∈ badBM (par d n).B} := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.range n, ∑ q ∈ Finset.range (nBlk d),
          ENNReal.ofReal ((2 : ℝ) ^ (-((par d n).B : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun q _ => ?_
        exact (hfst {x | bmInv (blkPair d x (t * nBlk d + q)) ∈ badBM (par d n).B}).trans_le
          (gauss_bad_le (pairOf_ne d (.inr (t * nBlk d + q))) _)
    _ = ENNReal.ofReal ((n : ℝ) * (nBlk d : ℝ) * (2 : ℝ) ^ (-((par d n).B : ℝ) / 2)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (Bud.dbits d n) := ENNReal.ofReal_le_ofReal (coins_le d n)

theorem measDrawB : MeasDrawB := by
  intro R d n t
  set K0 := R.K0 d n
  set B := (par d n).B
  have hcongr : ∀ ω : WΩ, (drawW R d n t ω).1 =
      (draw (beta d K0 B (extG d t (ξg d t ω))) K0 B d t).1 := by
    intro ω
    funext i
    have hq : (i : ℕ) / 2 < (d + 1) / 2 := by have := i.2; omega
    have h := blkUW_congr_grp (K0 := K0) (B := B) t ((i : ℕ) / 2) hq (x := ω.1)
      (x' := extG d t (ξg d t ω)) (fun c hc => by
        rw [show cIdx d t c = cIdx d t ((⟨c, by omega⟩ : Fin (d + 1)) : ℕ) from rfl, extG_cIdx]
        rfl)
    show (draw (beta d K0 B ω.1) K0 B d t).1 i = _
    simp only [draw, h]
  have hF : Measurable fun y : Fin (d + 1) → ℝ => (draw (beta d K0 B (extG d t y)) K0 B d t).1 := by
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [draw]
    split_ifs
    · exact (measurable_of_countable (fun UW : ℕ × ℕ => (gOut B UW).1)).comp
        ((measurable_blkUW d K0 B t _).comp (measurable_extG d t))
    · exact (measurable_of_countable (fun UW : ℕ × ℕ => (gOut B UW).2)).comp
        ((measurable_blkUW d K0 B t _).comp (measurable_extG d t))
  simp only [hcongr]
  exact hF.comp (comap_measurable (ξg d t))

end AdversarialBco.Bit.PieceB
