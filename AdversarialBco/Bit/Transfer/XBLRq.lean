/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib

@[expose] public section

/-! # BL's round over the integers: R7 to R14 as fractions of integers

Each value of R7 to R14 that the program computes, written over the denominators of its inputs (`2^pF`, `2^p`, the
denominator `G` of the draw, the denominator of `μ'`), with each test as one comparison of integers.
-/

open Matrix

/-- R7 of BL's round over the integers: with `κ = κ̂/F`, `Y = Ŷ/Q`, `ξ = Γ/G`, `c = κ Y`, the values `a = 1 - c` and
`q = a + c (ξ·ξ)` as fractions, and the tests `a < 1/2`, `q < 1/2` as integer comparisons. -/
theorem AdversarialBco.Bit.Transfer.BLM.r7_aq {d : ℕ} (F Q G kh yh : ℤ) (Γ : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q)
    (hG : 0 < G) :
    (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) = ((F * Q - kh * yh : ℤ) : ℚ) / ((F * Q : ℤ) : ℚ)) ∧
      (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) + (kh : ℚ) / F * ((yh : ℚ) / Q) *
          ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) =
        (((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / ((F * Q * G ^ 2 : ℤ) : ℚ)) ∧
      (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) < 1 / 2 ↔ 2 * (F * Q - kh * yh) < F * Q) ∧
      (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) + (kh : ℚ) / F * ((yh : ℚ) / Q) *
          ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) < 1 / 2 ↔
        2 * ((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ)) < F * Q * G ^ 2) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne.symm
  have hFQ' : (F * Q : ℚ) ≠ 0 := mul_ne_zero hF' hQ'
  -- dot product identity
  have hdot : ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) = ((Γ ⬝ᵥ Γ : ℤ) : ℚ) / ((G : ℚ)^2) := by
    calc
      ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) = ∑ i : Fin d, ((Γ i : ℚ) / G) * ((Γ i : ℚ) / G) := rfl
      _ = ∑ i : Fin d, ((Γ i : ℚ)^2 / (G : ℚ)^2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      _ = (∑ i : Fin d, (Γ i : ℚ)^2) / (G : ℚ)^2 := by rw [Finset.sum_div]
      _ = ((∑ i : Fin d, (Γ i)^2 : ℤ) : ℚ) / (G : ℚ)^2 := by simp
      _ = ((Γ ⬝ᵥ Γ : ℤ) : ℚ) / ((G : ℚ)^2) := by
        simp [dotProduct, sq]
  have h1 : (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) = ((F * Q - kh * yh : ℤ) : ℚ) / ((F * Q : ℤ) : ℚ)) := by
    field_simp [hF', hQ']
    push_cast
    ring
  have h2 : (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) + (kh : ℚ) / F * ((yh : ℚ) / Q) *
      ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) =
      (((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / ((F * Q * G ^ 2 : ℤ) : ℚ)) := by
    rw [hdot]
    field_simp [hF', hQ', hG']
    push_cast
    ring
  have h3 : (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) < 1 / 2 ↔ 2 * (F * Q - kh * yh) < F * Q) := by
    rw [h1]
    have hpos : (0 : ℚ) < ((F * Q : ℤ) : ℚ) := by exact_mod_cast mul_pos hF hQ
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℚ) < 2)]
    push_cast
    constructor
    · intro h
      have h' : (2 * (F * Q - kh * yh) : ℚ) < (F * Q : ℚ) := by
        simpa [mul_comm, one_mul] using h
      exact_mod_cast h'
    · intro h
      have h' : (2 * (F * Q - kh * yh) : ℚ) < (F * Q : ℚ) := by exact_mod_cast h
      simpa [mul_comm, one_mul] using h'
  have h4 : (1 - (kh : ℚ) / F * ((yh : ℚ) / Q) + (kh : ℚ) / F * ((yh : ℚ) / Q) *
      ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) < 1 / 2 ↔
      2 * ((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ)) < F * Q * G ^ 2) := by
    rw [h2]
    have hpos : (0 : ℚ) < ((F * Q * G ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast mul_pos (mul_pos hF hQ) (pow_pos hG 2)
    rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℚ) < 2)]
    push_cast
    constructor
    · intro h
      have h' : (2 * ((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ)) : ℚ) < (F * Q * G ^ 2 : ℚ) := by
        simpa [mul_comm, one_mul] using h
      exact_mod_cast h'
    · intro h
      have h' : (2 * ((F * Q - kh * yh) * G ^ 2 + kh * yh * (Γ ⬝ᵥ Γ)) : ℚ) < (F * Q * G ^ 2 : ℚ) := by
        exact_mod_cast h
      simpa [mul_comm, one_mul] using h'
  exact ⟨h1, h2, h3, h4⟩

/-- R7 of BL's round over the integers: with `c = (κ̂/F)(Ŷ/Q)`, `s3 = ŝ3/Q`, `rq = r̂q/Q` (positive), the quotients
`c/(s3 rq (s3 + rq))` and `c/(s3 + rq)` as fractions of integers. -/
theorem AdversarialBco.Bit.Transfer.BLM.r7_s2s4 (F Q kh yh s3 rq : ℤ) (hF : 0 < F) (hQ : 0 < Q) (h3 : 0 < s3)
    (hr : 0 < rq) :
    (kh : ℚ) / F * ((yh : ℚ) / Q) / ((s3 : ℚ) / Q * ((rq : ℚ) / Q) * ((s3 : ℚ) / Q + (rq : ℚ) / Q)) =
        ((kh * yh * Q ^ 2 : ℤ) : ℚ) / ((F * s3 * rq * (s3 + rq) : ℤ) : ℚ) ∧
      (kh : ℚ) / F * ((yh : ℚ) / Q) / ((s3 : ℚ) / Q + (rq : ℚ) / Q) =
        ((kh * yh : ℤ) : ℚ) / ((F * (s3 + rq) : ℤ) : ℚ) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have h3' : (s3 : ℚ) ≠ 0 := by exact_mod_cast h3.ne.symm
  have hr' : (rq : ℚ) ≠ 0 := by exact_mod_cast hr.ne.symm
  have hsum' : ((s3 + rq : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (by linarith : s3 + rq ≠ 0)
  constructor
  · push_cast
    field_simp [hF', hQ', h3', hr', hsum']
  · push_cast
    field_simp [hF', hQ', hsum']

/-- R8 of BL's round over the integers: with `A = Â/Q`, `ξ = Γ/G`, `s1 = ŝ1/Q`, `s2 = ŝ2/Q`, the entry `(i, j)` of
`s1 A - s2 (A ξ) ξᵀ` as one fraction. -/
theorem AdversarialBco.Bit.Transfer.BLM.r8_A {d : ℕ} (Q G s1 s2 : ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (hQ : 0 < Q) (hG : 0 < G) (i j : Fin d) :
    (((s1 : ℚ) / Q) • (Matrix.of fun a b => (Ah a b : ℚ) / Q) -
        ((s2 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j =
      ((s1 * Ah i j * G ^ 2 - s2 * (Ah *ᵥ Γ) i * Γ j : ℤ) : ℚ) / ((Q ^ 2 * G ^ 2 : ℤ) : ℚ) := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne.symm
  have h_mulVec (i : Fin d) : ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) i =
      ((Ah *ᵥ Γ) i : ℚ) / ((Q : ℚ) * (G : ℚ)) := by
    simp [Matrix.mulVec_apply, dotProduct, Finset.sum_div, div_mul_div_comm]
  calc
    (((s1 : ℚ) / Q) • (Matrix.of fun a b => (Ah a b : ℚ) / Q) -
        ((s2 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j
        = (((s1 : ℚ) / Q) • (Matrix.of fun a b => (Ah a b : ℚ) / Q)) i j -
          (((s2 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
            (fun k => (Γ k : ℚ) / G)) i j := by
      rw [Matrix.sub_apply]
    _ = ((s1 : ℚ) / Q) * ((Matrix.of fun a b => (Ah a b : ℚ) / Q) i j) -
        ((s2 : ℚ) / Q) * (vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j := by
      simp [Matrix.smul_apply]
    _ = ((s1 : ℚ) / Q) * ((Ah i j : ℚ) / Q) -
        ((s2 : ℚ) / Q) * (vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j := by
      simp [Matrix.of_apply]
    _ = ((s1 : ℚ) / Q) * ((Ah i j : ℚ) / Q) -
        ((s2 : ℚ) / Q) * (((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) i *
          ((fun k => (Γ k : ℚ) / G) j)) := by
      simp [Matrix.vecMulVec_apply]
    _ = ((s1 : ℚ) / Q) * ((Ah i j : ℚ) / Q) -
        ((s2 : ℚ) / Q) * ((((Ah *ᵥ Γ) i : ℚ) / ((Q : ℚ) * (G : ℚ))) * ((Γ j : ℚ) / (G : ℚ))) := by
      simp [h_mulVec]
    _ = ((s1 * Ah i j * G ^ 2 - s2 * (Ah *ᵥ Γ) i * Γ j : ℤ) : ℚ) / ((Q ^ 2 * G ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp [hQ', hG']

/-- R9 of BL's round over the integers: with `B = B̂/Q`, `ξ = Γ/G`, `Y = Ŷ/Q`, `ν = ν̂/F`, the entry `i` of `(Y ν) B ξ`
as one fraction; and the dot product of `g = ĝ/Q` with `μ = μ̂/D`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_gl {d : ℕ} (F Q G D yh nh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ gh mu : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D) (i : Fin d) :
    ((((yh : ℚ) / Q) * ((nh : ℚ) / F)) • ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)) i =
        ((yh * nh * (Bh *ᵥ Γ) i : ℤ) : ℚ) / ((F * Q ^ 2 * G : ℤ) : ℚ) ∧
      ((fun k => (gh k : ℚ) / Q) ⬝ᵥ fun k => (mu k : ℚ) / D) = ((gh ⬝ᵥ mu : ℤ) : ℚ) / ((Q * D : ℤ) : ℚ) := by
  refine ⟨?_, ?_⟩
  · -- first equality
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply]
    simp only [push_cast]
    simp only [Finset.mul_sum]
    simp only [Finset.sum_div]
    simp only [mul_assoc, div_mul_div_comm]
    field_simp [show (Q : ℚ) ≠ 0 from by exact_mod_cast hQ.ne.symm,
      show (F : ℚ) ≠ 0 from by exact_mod_cast hF.ne.symm,
      show (G : ℚ) ≠ 0 from by exact_mod_cast hG.ne.symm]
  · -- second equality
    simp only [dotProduct]
    simp only [push_cast]
    simp only [Finset.sum_div]
    field_simp [show (Q : ℚ) ≠ 0 from by exact_mod_cast hQ.ne.symm,
      show (D : ℚ) ≠ 0 from by exact_mod_cast hD.ne.symm]

/-- R9 of BL's round over the integers: with `B = B̂/Q`, `ξ = Γ/G`, `μ = μ̂/D`, `c = (κ̂/F)(Ŷ/Q)`, `u = B ξ`,
`v = Bᵀ μ`, the increment `c/2 ((u·μ)² - v·v)` of `k'` as one fraction. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_k {d : ℕ} (F Q G D kh yh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D) :
    (kh : ℚ) / F * ((yh : ℚ) / Q) / 2 *
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) ^ 2 -
          ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D) ⬝ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)) =
      ((kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) ^ 2 - G ^ 2 * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu))) : ℤ) : ℚ) /
        ((2 * F * Q ^ 3 * G ^ 2 * D ^ 2 : ℤ) : ℚ) := by
  have hposF : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hposQ : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have hposG : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne.symm
  have hposD : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne.symm
  set B := Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ) with hB
  set ξ := fun k => (Γ k : ℚ) / (G : ℚ) with hξ
  set μ' := fun k => (mu k : ℚ) / (D : ℚ) with hμ'
  have h_u_dot : (B *ᵥ ξ) ⬝ᵥ μ' = (↑((Bh *ᵥ Γ) ⬝ᵥ mu : ℤ) : ℚ) / ((Q : ℚ) * (G : ℚ) * (D : ℚ)) := by
    dsimp [B, ξ, μ']
    simp only [Matrix.mulVec_apply, dotProduct, div_eq_mul_inv]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have h_v_dot : (Bᵀ *ᵥ μ') ⬝ᵥ (Bᵀ *ᵥ μ') = (↑((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu) : ℤ) : ℚ) / ((Q : ℚ)^2 * (D : ℚ)^2) := by
    dsimp [B, μ']
    simp only [Matrix.mulVec_apply, dotProduct, div_eq_mul_inv]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc, sq]
  rw [h_u_dot, h_v_dot]
  push_cast
  field_simp [hposF, hposQ, hposG, hposD]

/-- R10 of BL's round over the integers: the sum of the squares of the entries of `B̂/Q` is `∑ B̂²/Q²`, and the test
`2Λ < ∑ (B̂/Q)²` is `2 Λ Q² < ∑ B̂²`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r10_frob {d : ℕ} (Q : ℤ) (Lam : ℕ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (hQ : 0 < Q) :
    (∑ i, ∑ j, (Matrix.of fun a b => (Bh a b : ℚ) / Q) i j ^ 2) =
        ((∑ i, ∑ j, Bh i j ^ 2 : ℤ) : ℚ) / ((Q ^ 2 : ℤ) : ℚ) ∧
      (2 * (Lam : ℚ) < ∑ i, ∑ j, (Matrix.of fun a b => (Bh a b : ℚ) / Q) i j ^ 2 ↔
        2 * (Lam : ℤ) * Q ^ 2 < ∑ i, ∑ j, Bh i j ^ 2) := by
  have hQpos : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hQsq_pos : (0 : ℚ) < (Q : ℚ) ^ 2 := pow_pos hQpos 2
  have h_eq : (∑ i, ∑ j, (Matrix.of fun a b => (Bh a b : ℚ) / Q) i j ^ 2) =
      ((∑ i, ∑ j, Bh i j ^ 2 : ℤ) : ℚ) / ((Q ^ 2 : ℤ) : ℚ) := by
    simp [Matrix.of_apply, div_pow, Finset.sum_div]
  constructor
  · exact h_eq
  · rw [h_eq]
    have hpos' : (0 : ℚ) < (Q : ℚ) ^ 2 := hQsq_pos
    have h_denom : ((Q ^ 2 : ℤ) : ℚ) = (Q : ℚ) ^ 2 := by push_cast; simp
    rw [h_denom]
    rw [lt_div_iff₀ hpos']
    push_cast
    have hsum : (∑ i, ∑ j, ((Bh i j : ℤ) : ℚ) ^ 2) = ((∑ i, ∑ j, Bh i j ^ 2 : ℤ) : ℚ) := by
      simp
    have hprod : (2 * (Lam : ℚ)) * ((Q : ℚ) ^ 2) = ((2 * (Lam : ℤ) * Q ^ 2 : ℤ) : ℚ) := by
      push_cast
      ring
    rw [hsum, hprod]
    rw [Int.cast_lt]

/-- R13 WMU of BL's round over the integers: with `η = η̂/F`, `Y = Ŷ/Q`, `ν = ν̂/F` and `q = N/(F Q G²)` (`N > 0`),
`η Y ν / q = η̂ Ŷ ν̂ G²/(F N)`; with `μ = μ̂/D`, `s5 = ŝ5/Q`, `A = Â/Q`, `ξ = Γ/G`, `w_μ = μ - s5 A ξ` has entries
`(μ̂ Q² G - ŝ5 (Â Γ) D)/(D Q² G)`; and with `W = Ŵ/F`, the test `(2W)² < w_μ·w_μ` is one comparison of integers. -/
theorem AdversarialBco.Bit.Transfer.BLM.r13_s5w {d : ℕ} (F Q G D N eh yh nh s5 Wh : ℤ)
    (Ah : Matrix (Fin d) (Fin d) ℤ) (Γ mu : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D)
    (hN : 0 < N) :
    (eh : ℚ) / F * ((yh : ℚ) / Q) * ((nh : ℚ) / F) / ((N : ℚ) / ((F * Q * G ^ 2 : ℤ) : ℚ)) =
        ((eh * yh * nh * G ^ 2 : ℤ) : ℚ) / ((F * N : ℤ) : ℚ) ∧
      (∀ j, ((fun k => (mu k : ℚ) / D) - ((s5 : ℚ) / Q) • ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ
          fun k => (Γ k : ℚ) / G)) j =
        ((mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * D : ℤ) : ℚ) / ((D * Q ^ 2 * G : ℤ) : ℚ)) ∧
      ((2 * ((Wh : ℚ) / F)) ^ 2 <
          ((fun k => (mu k : ℚ) / D) - ((s5 : ℚ) / Q) • ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ
            fun k => (Γ k : ℚ) / G)) ⬝ᵥ
          ((fun k => (mu k : ℚ) / D) - ((s5 : ℚ) / Q) • ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ
            fun k => (Γ k : ℚ) / G)) ↔
        4 * Wh ^ 2 * (D * Q ^ 2 * G) ^ 2 <
          (fun j => mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * D) ⬝ᵥ (fun j => mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * D) *
            F ^ 2) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne'
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpos_F : 0 < (F : ℚ) := by exact_mod_cast hF
  have hpos_Q : 0 < (Q : ℚ) := by exact_mod_cast hQ
  have hpos_G : 0 < (G : ℚ) := by exact_mod_cast hG
  have hpos_D : 0 < (D : ℚ) := by exact_mod_cast hD
  have hpos_N : 0 < (N : ℚ) := by exact_mod_cast hN
  have hpos_M_int : 0 < D * Q ^ 2 * G := by positivity
  have hpos_M : 0 < ((D * Q ^ 2 * G : ℤ) : ℚ) := by exact_mod_cast hpos_M_int
  have hpos_F_sq : 0 < (F : ℚ) ^ 2 := pow_pos hpos_F 2
  have hpos_M_sq : 0 < (((D * Q ^ 2 * G : ℤ) : ℚ) ^ 2) := pow_pos hpos_M 2
  have hsum : ∀ j : Fin d, (∑ x : Fin d, ((Ah j x : ℚ) / Q) * ((Γ x : ℚ) / G)) = ((Ah *ᵥ Γ) j : ℚ) / (Q * G) := by
    intro j
    calc
      (∑ x : Fin d, ((Ah j x : ℚ) / Q) * ((Γ x : ℚ) / G)) = (∑ x : Fin d, ((Ah j x : ℚ) * (Γ x : ℚ)) / (Q * G)) := by
        simp [div_mul_div_comm]
      _ = ((∑ x : Fin d, (Ah j x : ℚ) * (Γ x : ℚ)) / (Q * G)) := by rw [Finset.sum_div]
      _ = ((Ah *ᵥ Γ) j : ℚ) / (Q * G) := by
        simp [Matrix.mulVec_apply, dotProduct]
  let w : Fin d → ℚ := fun k => (mu k : ℚ) / D - ((s5 : ℚ) / Q) • (((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) k)
  let wn : Fin d → ℤ := fun j => mu j * Q ^ 2 * G - s5 * (Ah *ᵥ Γ) j * D
  have hw_eq : ∀ j, w j = (wn j : ℚ) / ((D * Q ^ 2 * G : ℤ) : ℚ) := by
    intro j
    dsimp [w, wn]
    simp [mulVec, dotProduct, Matrix.of_apply, hsum j]
    push_cast
    field_simp [hD', hQ', hG']
    try ring
  have h_dot : w ⬝ᵥ w = ((wn ⬝ᵥ wn : ℤ) : ℚ) / (((D * Q ^ 2 * G : ℤ) : ℚ) ^ 2) := by
    calc
      w ⬝ᵥ w = ∑ j : Fin d, w j * w j := by rw [dotProduct]
      _ = ∑ j : Fin d, ((wn j : ℚ) / ((D * Q ^ 2 * G : ℤ) : ℚ)) * ((wn j : ℚ) / ((D * Q ^ 2 * G : ℤ) : ℚ)) := by simp [hw_eq]
      _ = ∑ j : Fin d, ((wn j : ℚ) * (wn j : ℚ)) / (((D * Q ^ 2 * G : ℤ) : ℚ) * ((D * Q ^ 2 * G : ℤ) : ℚ)) := by
        simp [div_mul_div_comm]
      _ = (∑ j : Fin d, (wn j : ℚ) * (wn j : ℚ)) / (((D * Q ^ 2 * G : ℤ) : ℚ) * ((D * Q ^ 2 * G : ℤ) : ℚ)) := by
        rw [Finset.sum_div]
      _ = ((wn ⬝ᵥ wn : ℤ) : ℚ) / (((D * Q ^ 2 * G : ℤ) : ℚ) * ((D * Q ^ 2 * G : ℤ) : ℚ)) := by simp [dotProduct, push_cast]
      _ = ((wn ⬝ᵥ wn : ℤ) : ℚ) / (((D * Q ^ 2 * G : ℤ) : ℚ) ^ 2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · -- first conjunct
    field_simp [hF', hQ', hG', hN']
    push_cast
    try ring
  · -- second conjunct
    intro j
    dsimp [w, wn]
    simp [mulVec, dotProduct, Matrix.of_apply, hsum j]
    push_cast
    field_simp [hD', hQ', hG']
    try ring
  · -- third conjunct: equivalence
    have h_left_sq : ((2 * ((Wh : ℚ) / F)) ^ 2) = (4 * (Wh : ℚ) ^ 2) / ((F : ℚ) ^ 2) := by ring
    rw [h_left_sq]
    -- goal: 4*Wh^2/F^2 < (f - s•(M*ᵥv)) ⬝ᵥ (f - s•(M*ᵥv)) ↔ ...
    -- w is definitionally equal to (f - s•(M*ᵥv)), so change works
    change 4 * (Wh : ℚ) ^ 2 / (F : ℚ) ^ 2 < w ⬝ᵥ w ↔
      4 * Wh ^ 2 * (D * Q ^ 2 * G) ^ 2 < wn ⬝ᵥ wn * F ^ 2
    rw [h_dot]
    rw [div_lt_div_iff₀ hpos_F_sq hpos_M_sq]
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h

/-- R8 of BL's round over the integers: with `B = B̂/Q`, `ξ = Γ/G`, `s3 = ŝ3/Q`, `s4 = ŝ4/Q`, the entry `(i, j)` of
`s3 B + s4 (B ξ) ξᵀ` as one fraction. -/
theorem AdversarialBco.Bit.Transfer.BLM.r8_B {d : ℕ} (Q G s3 s4 : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (hQ : 0 < Q) (hG : 0 < G) (i j : Fin d) :
    (((s3 : ℚ) / Q) • (Matrix.of fun a b => (Bh a b : ℚ) / Q) +
        ((s4 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j =
      ((s3 * Bh i j * G ^ 2 + s4 * (Bh *ᵥ Γ) i * Γ j : ℤ) : ℚ) / ((Q ^ 2 * G ^ 2 : ℤ) : ℚ) := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne.symm
  simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.of_apply, Matrix.mulVec_apply, Matrix.row_apply, dotProduct]
  push_cast
  rw [smul_eq_mul, smul_eq_mul]
  have hleft : ((s3 : ℚ) / (Q : ℚ)) * ((Bh i j : ℚ) / (Q : ℚ)) + ((s4 : ℚ) / (Q : ℚ)) * (((∑ k, (Bh i k : ℚ) / (Q : ℚ) * ((Γ k : ℚ) / (G : ℚ))) * ((Γ j : ℚ) / (G : ℚ)))) = ((s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) ^ 2 + (s4 : ℚ) * (∑ k, (Bh i k : ℚ) * (Γ k : ℚ)) * (Γ j : ℚ)) / ((Q : ℚ) ^ 2 * (G : ℚ) ^ 2) := by
    field_simp [hQ', hG']
    simp [Finset.mul_sum, Finset.sum_mul]
    calc
      (G : ℚ) * ((s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) + ∑ i_1, (Q : ℚ) * (s4 : ℚ) * ((Bh i i_1 : ℚ) * (Γ i_1 : ℚ) / ((Q : ℚ) * (G : ℚ))) * (Γ j : ℚ))
          = (G : ℚ) * (s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) + (G : ℚ) * ∑ i_1, (Q : ℚ) * (s4 : ℚ) * ((Bh i i_1 : ℚ) * (Γ i_1 : ℚ) / ((Q : ℚ) * (G : ℚ))) * (Γ j : ℚ) := by ring
      _ = (s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) ^ 2 + (G : ℚ) * ∑ i_1, (Q : ℚ) * (s4 : ℚ) * ((Bh i i_1 : ℚ) * (Γ i_1 : ℚ) / ((Q : ℚ) * (G : ℚ))) * (Γ j : ℚ) := by ring
      _ = (s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) ^ 2 + ∑ i_1, (G : ℚ) * (Q : ℚ) * (s4 : ℚ) * ((Bh i i_1 : ℚ) * (Γ i_1 : ℚ) / ((Q : ℚ) * (G : ℚ))) * (Γ j : ℚ) := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [mul_assoc]
      _ = (s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) ^ 2 + ∑ i_1, (s4 : ℚ) * (Γ j : ℚ) * (Bh i i_1 : ℚ) * (Γ i_1 : ℚ) := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        field_simp [hQ', hG']
      _ = (s3 : ℚ) * (Bh i j : ℚ) * (G : ℚ) ^ 2 + ∑ i_1, (s4 : ℚ) * (Γ j : ℚ) * ((Bh i i_1 : ℚ) * (Γ i_1 : ℚ)) := by
        simp [mul_assoc]
  rw [hleft]

/-- R12 FIRE of BL's round over the integers: with `η = η̂/F`, `l = l̂/Q`, `G = Ĝ/Q`, `p = x/D`, `P = B Bᵀ` for
`B = B̂/Q`, `b = b̂/Q`, `k = k̂/Q`, `ρ = ρ̂/F`, `ê = 1/H` (all denominators positive), the test
`η (l - G·p) - 2 (p·(P p)/2 - b·p + k) ≤ -ρ + ê` is one comparison of integers. -/
theorem AdversarialBco.Bit.Transfer.BLM.r12_fire {d : ℕ} (F Q D H eh lh kh rh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Gh bh x : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hD : 0 < D) (hH : 0 < H) :
    ((eh : ℚ) / F * ((lh : ℚ) / Q - (fun k => (Gh k : ℚ) / Q) ⬝ᵥ fun k => (x k : ℚ) / D) -
          2 * ((fun k => (x k : ℚ) / D) ⬝ᵥ (((Matrix.of fun a b => (Bh a b : ℚ) / Q) *
              (Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ) *ᵥ fun k => (x k : ℚ) / D) / 2 -
            (fun k => (bh k : ℚ) / Q) ⬝ᵥ (fun k => (x k : ℚ) / D) + (kh : ℚ) / Q) ≤
        -((rh : ℚ) / F) + 1 / (H : ℚ)) ↔
      eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
          F * H * (x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) - 2 * Q * D * (bh ⬝ᵥ x) + 2 * Q * D ^ 2 * kh) ≤
        (F - rh * H) * Q ^ 2 * D ^ 2 := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne.symm
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne.symm
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne.symm
  have hH' : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne.symm
  have hMpos : 0 < (F : ℚ) * (Q : ℚ) ^ 2 * (D : ℚ) ^ 2 * (H : ℚ) := by positivity
  -- auxiliary identities for dot products with division
  have h_dot_Gh : (fun k => (Gh k : ℚ) / (Q : ℚ)) ⬝ᵥ (fun k => (x k : ℚ) / (D : ℚ)) = ((Gh ⬝ᵥ x : ℤ) : ℚ) / ((Q : ℚ) * (D : ℚ)) := by
    simp [dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp [hQ', hD']
  have h_dot_bh : (fun k => (bh k : ℚ) / (Q : ℚ)) ⬝ᵥ (fun k => (x k : ℚ) / (D : ℚ)) = ((bh ⬝ᵥ x : ℤ) : ℚ) / ((Q : ℚ) * (D : ℚ)) := by
    simp [dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp [hQ', hD']
  have h_dot_B : (fun k => (x k : ℚ) / (D : ℚ)) ⬝ᵥ (((Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ)) *
      (Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ))ᵀ) *ᵥ (fun k => (x k : ℚ) / (D : ℚ))) = ((x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) : ℤ) : ℚ) / (((Q : ℚ) ^ 2) * ((D : ℚ) ^ 2)) := by
    have hB_eq : (Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ)) * (Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ))ᵀ =
        (Matrix.of fun a b => ((Bh * Bhᵀ) a b : ℤ) / ((Q : ℚ) ^ 2)) := by
      ext a b
      have h1 : ((Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ)) * (Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ))ᵀ) a b =
        ∑ j, ((Bh a j : ℚ) / (Q : ℚ)) * ((Bh b j : ℚ) / (Q : ℚ)) := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Matrix.transpose_apply, Matrix.of_apply]
      have h2 : (Matrix.of fun a b => ((Bh * Bhᵀ) a b : ℤ) / ((Q : ℚ) ^ 2)) a b = ((Bh * Bhᵀ) a b : ℤ) / ((Q : ℚ) ^ 2) := by
        simp [Matrix.of_apply]
      rw [h1, h2]
      have hRHS : ((Bh * Bhᵀ) a b : ℤ) / ((Q : ℚ) ^ 2) = (∑ j, (Bh a j : ℚ) * (Bh b j : ℚ)) / ((Q : ℚ) ^ 2) := by
        push_cast
        simp [Matrix.mul_apply, Matrix.of_apply]
      rw [hRHS]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [hQ']
    calc
      (fun k => (x k : ℚ) / (D : ℚ)) ⬝ᵥ (((Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ)) *
          (Matrix.of fun a b => (Bh a b : ℚ) / (Q : ℚ))ᵀ) *ᵥ (fun k => (x k : ℚ) / (D : ℚ))) =
          (fun k => (x k : ℚ) / (D : ℚ)) ⬝ᵥ ((Matrix.of fun a b => ((Bh * Bhᵀ) a b : ℤ) / ((Q : ℚ) ^ 2)) *ᵥ (fun k => (x k : ℚ) / (D : ℚ))) := by rw [hB_eq]
      _ = ((x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) : ℤ) : ℚ) / (((Q : ℚ) ^ 2) * ((D : ℚ) ^ 2)) := by
        have hterm (i j : Fin d) : (x i : ℚ) / (D : ℚ) * (((Bh * Bhᵀ) i j : ℤ) / ((Q : ℚ) ^ 2) * ((x j : ℚ) / (D : ℚ))) =
            ((x i : ℚ) * (((Bh * Bhᵀ) i j : ℤ) : ℚ) * (x j : ℚ)) / (((Q : ℚ) ^ 2) * ((D : ℚ) ^ 2)) := by
          push_cast
          field_simp [hQ', hD']
        simp [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.sum_div, Finset.mul_sum, hterm]
        simp [mul_assoc]
  -- rewrite LHS and RHS using the identities
  rw [h_dot_Gh, h_dot_bh, h_dot_B]
  -- Multiply both sides by M = F*Q^2*D^2*H > 0
  have hLHS_mul_M : (((eh : ℚ) / (F : ℚ)) * (((lh : ℚ) / (Q : ℚ)) - ((Gh ⬝ᵥ x : ℤ) : ℚ) / ((Q : ℚ) * (D : ℚ))) -
      2 * ((((x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) : ℤ) : ℚ) / (((Q : ℚ) ^ 2) * ((D : ℚ) ^ 2)) / 2 - ((bh ⬝ᵥ x : ℤ) : ℚ) / ((Q : ℚ) * (D : ℚ)) + (kh : ℚ) / (Q : ℚ)))) * ((F : ℚ) * (Q : ℚ) ^ 2 * (D : ℚ) ^ 2 * (H : ℚ)) =
      ((eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
      F * H * (x ⬝ᵥ ((Bh * Bhᵀ) *ᵥ x) - 2 * Q * D * (bh ⬝ᵥ x) + 2 * Q * D ^ 2 * kh) : ℤ) : ℚ) := by
    field_simp [hF', hQ', hD', hH']
    push_cast
    ring
  have hRHS_mul_M : (-((rh : ℚ) / (F : ℚ)) + 1 / (H : ℚ)) * ((F : ℚ) * (Q : ℚ) ^ 2 * (D : ℚ) ^ 2 * (H : ℚ)) = (((F - rh * H) * Q ^ 2 * D ^ 2 : ℤ) : ℚ) := by
    field_simp [hF', hH']
    push_cast
    ring
  refine Iff.trans ((mul_le_mul_iff_of_pos_right hMpos).symm) ?_
  rw [hLHS_mul_M, hRHS_mul_M]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- R9 of BL's round over the integers: with `B = B̂/Q`, `ξ = Γ/G`, `μ = μ̂/D`, `c = (κ̂/F)(Ŷ/Q)`, `u = B ξ`,
`v = Bᵀ μ`, the entry `i` of `c ((u·μ) u - B v)` as one fraction. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_b {d : ℕ} (F Q G D kh yh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hG : 0 < G) (hD : 0 < D) (i : Fin d) :
    (((kh : ℚ) / F * ((yh : ℚ) / Q)) •
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) •
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) -
          (Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D))) i =
      ((kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) i - G ^ 2 * (Bh *ᵥ (Bhᵀ *ᵥ mu)) i) : ℤ) : ℚ) /
        ((F * Q ^ 3 * G ^ 2 * D : ℤ) : ℚ) := by
  have hF' : (F : ℚ) ≠ 0 := by exact_mod_cast hF.ne'
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hu : ∀ a, ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) a =
      ((Bh *ᵥ Γ) a : ℚ) / (Q * G) := fun a => by
    simp only [mulVec, dotProduct, of_apply]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  have huμ : (((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) =
      (((Bh *ᵥ Γ) ⬝ᵥ mu : ℤ) : ℚ) / (Q * G * D) := by
    simp only [dotProduct, hu]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  have hv : ∀ j, ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D) j =
      ((Bhᵀ *ᵥ mu) j : ℚ) / (Q * D) := fun j => by
    simp only [mulVec, dotProduct, transpose_apply, of_apply]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by field_simp
  have hBv : ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ
      ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)) i =
      ((Bh *ᵥ (Bhᵀ *ᵥ mu)) i : ℚ) / (Q ^ 2 * D) := by
    rw [mulVec, dotProduct]
    simp only [hv, of_apply]
    rw [mulVec, dotProduct]
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by field_simp
  rw [Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, hBv, hu, huμ, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
