/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRq
public import AdversarialBco.Bit.Transfer.XBLRr
public import AdversarialBco.Bit.Transfer.XBLSetupPar
public import AdversarialBco.Bit.Transfer.XBLSetupFacts

@[expose] public section

/-! # BL's round on the grid: R8 to R10 and R12 as numerators

A vector or a matrix of the grid `2^{-p}` as its numerators over `2^p`; R10's Frobenius test on the numerators; the
quadratic form of R12; R8's `A'`, `B'` and R9's `b'`, `k'`, `l'` as numerators `(U Q + U Q + V)/(V + V)`, the form the
machine computes.
-/

open AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer.BLM Matrix

/-- R10's test on a matrix of the grid `2^{-p}`: `2Λ < frob2 M` iff `2Λ 4^p < Σ qn(M_ij)²`. -/
theorem AdversarialBco.Bit.Transfer.BLM.frob2_grid {d : ℕ} (p Lam : ℕ) (M : Matrix (Fin d) (Fin d) ℚ)
    (h : ∀ i j, OnG p (M i j)) :
    (2 * (Lam : ℚ) < frob2 M ↔ 2 * (Lam : ℤ) * (2 ^ p) ^ 2 < ∑ i, ∑ j, qn p (M i j) ^ 2) := by
  set Bh := Matrix.of fun (a b : Fin d) => qn p (M a b) with hBh
  set Q := (2 ^ p : ℤ) with hQ
  have hQpos : 0 < Q := by
    rw [hQ]
    exact pow_pos (by norm_num : 0 < (2 : ℤ)) p
  have hM : M = Matrix.of fun a b => ((Bh a b : ℤ) : ℚ) / (Q : ℚ) := by
    ext i j
    dsimp [Bh, Q]
    field_simp [show ((2 ^ p : ℤ) : ℚ) ≠ 0 from by norm_num]
    have h_on := h i j
    unfold OnG at h_on
    simpa [push_cast] using h_on.symm
  have h_frob2 : frob2 M = ∑ i, ∑ j, (((Bh i j : ℤ) : ℚ) / (Q : ℚ)) ^ 2 := by
    dsimp [frob2]
    rw [hM]
    simp
  rw [h_frob2]
  rcases r10_frob Q Lam Bh hQpos with ⟨_, h_equiv⟩
  simpa [hBh, hQ] using h_equiv

/-- `x·(B Bᵀ x) = (Bᵀ x)·(Bᵀ x)` over a commutative ring. -/
theorem AdversarialBco.Bit.Transfer.BLM.dot_mulVec_mul_transpose {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) (x : Fin d → R) : x ⬝ᵥ ((B * Bᵀ) *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
  calc
    x ⬝ᵥ ((B * Bᵀ) *ᵥ x) = x ⬝ᵥ (B *ᵥ (Bᵀ *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec]
    _ = (Matrix.vecMul x B) ⬝ᵥ (Bᵀ *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    _ = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
      rw [← Matrix.mulVec_transpose B x]

/-- The sum of two points of the grid `2^{-k}` is on the grid, with the sum of the numerators. -/
theorem AdversarialBco.Bit.Transfer.BLM.qn_add_onG (k : ℕ) (x y : ℚ) (hx : OnG k x) (hy : OnG k y) :
    OnG k (x + y) ∧ qn k (x + y) = qn k x + qn k y := by
  have hx' : ((qn k x : ℤ) : ℚ) = x * (2 : ℚ) ^ k := hx
  have hy' : ((qn k y : ℤ) : ℚ) = y * (2 : ℚ) ^ k := hy
  have hsum : (x + y) * (2 : ℚ) ^ k = ((qn k x + qn k y : ℤ) : ℚ) := by
    calc
      (x + y) * (2 : ℚ) ^ k = x * (2 : ℚ) ^ k + y * (2 : ℚ) ^ k := by rw [add_mul]
      _ = ((qn k x : ℤ) : ℚ) + ((qn k y : ℤ) : ℚ) := by rw [hx', hy']
      _ = ((qn k x + qn k y : ℤ) : ℚ) := by simp
  have hqn : qn k (x + y) = qn k x + qn k y := by
    dsimp [qn]
    rw [hsum]
    simp [qn, Int.floor_intCast]
  have hon : OnG k (x + y) := by
    dsimp [OnG]
    rw [hqn, hsum]
  exact And.intro hon hqn

/-- R9's `b'` on the integers: with `b = b̂/Q`, `B = B̂/Q`, `ξ = Γ/G`, `μ = μ̂/D`, `c = (κ̂/F)(Ŷ/Q)`, `Q = 2^p`, the
coordinate `j` of `b + rnd_p (c ((u·μ) u - B (Bᵀ μ)))`, `u = B ξ`, lies on the grid and its numerator is
`b̂_j + (U Q + U Q + V)/(V + V)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_bq {d : ℕ} (p : ℕ) (F Q G D kh yh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu bh : Fin d → ℤ) (hQ : Q = 2 ^ p) (hF : 0 < F) (hG : 0 < G) (hD : 0 < D) (j : Fin d) :
    OnG p (((fun k => (bh k : ℚ) / Q) + rndV p (((kh : ℚ) / F * ((yh : ℚ) / Q)) •
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) •
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) -
          (Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)))) j) ∧
    qn p (((fun k => (bh k : ℚ) / Q) + rndV p (((kh : ℚ) / F * ((yh : ℚ) / Q)) •
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) •
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) -
          (Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)))) j) =
      bh j + ((kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j)) * Q +
          (kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j)) * Q +
          F * Q * Q * Q * (G * G) * D) / (F * Q * Q * Q * (G * G) * D + F * Q * Q * Q * (G * G) * D) := by
  -- Define x and y for readability
  set x := fun k => (bh k : ℚ) / Q with hx_def
  set y := ((kh : ℚ) / F * ((yh : ℚ) / Q)) •
    ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) •
        ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) -
      (Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ
        ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)) with hy_def
  -- Show that x j lies on the grid
  have hx_onG : OnG p (x j) := by
    unfold OnG qn
    simp [hx_def, hQ]
  have hx_qn : qn p (x j) = bh j := by
    unfold qn
    simp [hx_def, hQ]
  -- Now compute (x + rndV p y) j
  have h_add : (x + rndV p y) j = x j + rnd p (y j) := by
    rw [Pi.add_apply, rndV]
  -- Apply qn_rnd_add
  have h_result := qn_rnd_add p (x j) (y j) hx_onG
  rcases h_result with ⟨h_onG, h_qn⟩
  -- h_onG : OnG p (x j + rnd p (y j))
  -- h_qn : qn p (x j + rnd p (y j)) = qn p (x j) + ⌊y j * 2 ^ p + 1 / 2⌋
  -- Rewrite the goal using h_add
  rw [h_add]
  -- Goal: OnG p (x j + rnd p (y j)) ∧ qn p (x j + rnd p (y j)) = ...
  -- Now h_onG gives the first conjunct
  -- And we need to compute qn p (x j + rnd p (y j))
  rw [hx_qn] at h_qn
  -- Now h_qn : qn p (x j + rnd p (y j)) = bh j + ⌊y j * 2 ^ p + 1 / 2⌋
  -- We need to compute ⌊y j * 2 ^ p + 1 / 2⌋
  -- First, compute y j explicitly
  -- y j = (kh/F * (yh/Q)) * ((u ⬝ᵥ v) * u j - (B *ᵥ v) j)
  -- where B = Matrix.of fun a b => (Bh a b : ℚ) / Q
  --       u = B *ᵥ (Γ / G)
  --       v = Bᵀ *ᵥ (mu / D)
  -- Let U = kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G ^ 2 * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j)
  -- Let V = F * Q ^ 3 * G ^ 2 * D
  -- Then y j = U / V (by r9_b, which we inline)

  -- Use r9_b from Work.Deps (it has sorry but we can reference it)
  have hQpos : 0 < Q := by
    rw [hQ]
    exact pow_pos (by norm_num) p
  have hyj_eq : y j = ((kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G ^ 2 * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j) : ℤ) : ℚ) /
    ((F * Q ^ 3 * G ^ 2 * D : ℤ) : ℚ) := by
    -- y j = ... by r9_b
    -- But we need to match the exact form
    -- r9_b gives an equality of vectors at index i, we need at index j
    have h := AdversarialBco.Bit.Transfer.BLM.r9_b F Q G D kh yh Bh Γ mu hF hQpos hG hD j
    -- h : (((kh : ℚ) / F * ((yh : ℚ) / Q)) • ...) j = ...
    -- This is exactly y j = ...
    simpa [y] using h

  rw [hyj_eq] at h_qn

  -- Now h_qn : qn p ((x + rndV p y) j) = bh j + ⌊(((U : ℚ) / V) * 2 ^ p + 1 / 2)⌋
  -- where U = kh * yh * ... and V = F * Q^3 * G^2 * D

  -- Set U and V for clarity
  set U := kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G ^ 2 * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j) with hU_def
  set V := F * Q ^ 3 * G ^ 2 * D with hV_def

  have hVpos : 0 < V := by
    -- V = F * Q^3 * G^2 * D, all factors are positive
    rw [hV_def]
    have hQpos : 0 < Q := by
      rw [hQ]
      exact pow_pos (by norm_num) p
    have hQ3pos : 0 < Q ^ 3 := pow_pos hQpos 3
    have hG2pos : 0 < G ^ 2 := pow_pos hG 2
    positivity

  -- Now compute ⌊(U/V) * 2^p + 1/2⌋
  -- This equals qn p (rnd p (U/V))
  have h_floor_eq : ⌊(((U : ℚ) / V) * (2 ^ p : ℚ) + 1 / 2)⌋ = qn p (rnd p ((U : ℚ) / V)) := by
    unfold qn rnd
    -- qn p (rnd p ((U : ℚ) / V)) = ⌊(rnd p ((U : ℚ) / V)) * 2 ^ p⌋
    -- = ⌊(((⌊((U : ℚ) / V) * 2 ^ p + 1 / 2⌋ : ℚ) / 2 ^ p)) * 2 ^ p⌋
    -- = ⌊(⌊((U : ℚ) / V) * 2 ^ p + 1 / 2⌋ : ℚ)⌋
    -- = ⌊((U : ℚ) / V) * 2 ^ p + 1 / 2⌋
    have h2p : (2 ^ p : ℚ) ≠ 0 := by norm_num
    field_simp [h2p]
    simp

  rw [h_floor_eq] at h_qn

  -- Now use qn_rnd_div
  rw [qn_rnd_div p U V hVpos] at h_qn

  -- Now h_qn : qn p (x j + rnd p (y j)) = bh j + (2 * U * 2 ^ p + V) / (2 * V)
  -- The goal is: OnG p (x j + rnd p (y j)) ∧ qn p (x j + rnd p (y j)) = target RHS
  -- We have h_onG for the first conjunct
  -- For the second, rewrite using h_qn and then simplify

  -- Provide the OnG part
  refine And.intro h_onG ?_
  -- Goal: qn p (x j + rnd p (y j)) = target RHS
  -- First rewrite y j using hyj_eq
  rw [hyj_eq]
  -- Goal: qn p (x j + rnd p (↑U / ↑V)) = target RHS
  rw [h_qn]
  -- Goal: bh j + (2 * U * 2 ^ p + V) / (2 * V) = target RHS
  -- Expand U and V
  unfold U V
  rw [hQ]
  -- Both sides are equal by ring
  congr 1
  -- Simplify RHS numerator and denominator to match LHS
  have hnum : (kh * yh * (Bh *ᵥ Γ ⬝ᵥ mu * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ Bhᵀ *ᵥ mu) j)) * 2 ^ p +
      (kh * yh * (Bh *ᵥ Γ ⬝ᵥ mu * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ Bhᵀ *ᵥ mu) j)) * 2 ^ p +
      F * 2 ^ p * 2 ^ p * 2 ^ p * (G * G) * D =
      2 * (kh * yh * (Bh *ᵥ Γ ⬝ᵥ mu * (Bh *ᵥ Γ) j - G ^ 2 * (Bh *ᵥ Bhᵀ *ᵥ mu) j)) * 2 ^ p +
      F * (2 ^ p) ^ 3 * G ^ 2 * D := by
    ring
  have hden : F * 2 ^ p * 2 ^ p * 2 ^ p * (G * G) * D + F * 2 ^ p * 2 ^ p * 2 ^ p * (G * G) * D =
      2 * (F * (2 ^ p) ^ 3 * G ^ 2 * D) := by
    ring
  rw [hnum, hden]

/-- R9's `k'` on the integers: with `k = k̂/Q`, `B = B̂/Q`, `ξ = Γ/G`, `μ = μ̂/D`, `c = (κ̂/F)(Ŷ/Q)`, `Q = 2^p`,
`k + rnd_p (c/2 ((u·μ)² - v·v))`, `u = B ξ`, `v = Bᵀ μ`, lies on the grid and its numerator is
`k̂ + (U Q + U Q + V)/(V + V)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_kq {d : ℕ} (p : ℕ) (F Q G D kh yh k0 : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ mu : Fin d → ℤ) (hQ : Q = 2 ^ p) (hF : 0 < F) (hG : 0 < G) (hD : 0 < D) :
    OnG p ((k0 : ℚ) / Q + rnd p ((kh : ℚ) / F * ((yh : ℚ) / Q) / 2 *
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) ^ 2 -
          ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D) ⬝ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)))) ∧
    qn p ((k0 : ℚ) / Q + rnd p ((kh : ℚ) / F * ((yh : ℚ) / Q) / 2 *
        ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) ^ 2 -
          ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D) ⬝ᵥ
            ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)))) =
      k0 + ((kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) - G * G * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)))) * Q +
          (kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) - G * G * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)))) * Q +
          2 * F * Q * Q * Q * (G * G) * (D * D)) /
        (2 * F * Q * Q * Q * (G * G) * (D * D) + 2 * F * Q * Q * Q * (G * G) * (D * D)) := by
  set Y := (kh : ℚ) / F * ((yh : ℚ) / Q) / 2 *
    ((((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G) ⬝ᵥ fun k => (mu k : ℚ) / D) ^ 2 -
      ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D) ⬝ᵥ
        ((Matrix.of fun a b => (Bh a b : ℚ) / Q)ᵀ *ᵥ fun k => (mu k : ℚ) / D)) with hY
  have hQpos : 0 < Q := by
    rw [hQ]
    exact pow_pos (by norm_num) p
  have h_onG : OnG p ((k0 : ℚ) / Q) := by
    rw [OnG, qn]
    simp [hQ]
  rcases qn_rnd_add p ((k0 : ℚ) / Q) Y h_onG with ⟨h_onG2, h_qn⟩
  refine ⟨h_onG2, ?_⟩
  rw [h_qn]
  have h_qn_k0 : qn p ((k0 : ℚ) / Q) = k0 := by
    rw [OnG] at h_onG
    simpa [qn, hQ] using h_onG
  rw [h_qn_k0]
  have h_floor : Int.floor (Y * (2 : ℚ) ^ p + 1 / 2) = qn p (rnd p Y) := by
    simp [qn, rnd]
  rw [h_floor]
  dsimp [Y]
  have h_r9 := r9_k F Q G D kh yh Bh Γ mu hF hQpos hG hD
  rw [h_r9]
  have hVpos : 0 < (2 * F * Q ^ 3 * G ^ 2 * D ^ 2 : ℤ) := by
    positivity
  rw [qn_rnd_div p (kh * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) ^ 2 - G ^ 2 * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu))))
    (2 * F * Q ^ 3 * G ^ 2 * D ^ 2) hVpos]
  rw [← hQ]
  ring_nf

/-- R9's `l'` on the integers: with `l = l̂/Q`, `g = ĝ/Q`, `μ = μ̂/D`, `Q = 2^p`, `l + rnd_p (g·μ)` lies on the grid and
its numerator is `l̂ + (U Q + U Q + V)/(V + V)`, `U = ĝ·μ̂`, `V = Q D`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_lq {d : ℕ} (p : ℕ) (Q D lh : ℤ) (gh mu : Fin d → ℤ) (hQ : Q = 2 ^ p)
    (hD : 0 < D) :
    OnG p ((lh : ℚ) / Q + rnd p ((fun k => (gh k : ℚ) / Q) ⬝ᵥ fun k => (mu k : ℚ) / D)) ∧
    qn p ((lh : ℚ) / Q + rnd p ((fun k => (gh k : ℚ) / Q) ⬝ᵥ fun k => (mu k : ℚ) / D)) =
      lh + ((gh ⬝ᵥ mu) * Q + (gh ⬝ᵥ mu) * Q + Q * D) / (Q * D + Q * D) := by
  have hQpos : 0 < Q := by
    rw [hQ]
    exact pow_pos (by norm_num : 0 < (2 : ℤ)) p
  have hx : OnG p ((lh : ℚ) / Q) := by
    rw [OnG, hQ]
    unfold qn
    simp
  let y := (fun k => (gh k : ℚ) / Q) ⬝ᵥ fun k => (mu k : ℚ) / D
  have hy : y = ((gh ⬝ᵥ mu : ℤ) : ℚ) / ((Q * D : ℤ) : ℚ) := by
    dsimp [y, dotProduct]
    calc
      (∑ k, ((gh k : ℚ) / Q) * ((mu k : ℚ) / D)) = (∑ k, ((gh k : ℚ) * (mu k : ℚ)) / ((Q : ℚ) * (D : ℚ))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      _ = (∑ k, ((gh k : ℚ) * (mu k : ℚ))) / ((Q : ℚ) * (D : ℚ)) := by rw [Finset.sum_div]
      _ = ((gh ⬝ᵥ mu : ℤ) : ℚ) / ((Q * D : ℤ) : ℚ) := by simp [dotProduct]
  have h_add := qn_rnd_add p ((lh : ℚ) / Q) y hx
  have h_onG := h_add.1
  have h_qn := h_add.2
  refine ⟨h_onG, ?_⟩
  rw [h_qn, hy]
  have h_qn_lh : qn p ((lh : ℚ) / Q) = lh := by
    rw [hQ]
    unfold qn
    simp
  rw [h_qn_lh]
  have h_floor_eq : ⌊(((gh ⬝ᵥ mu : ℤ) : ℚ) / ((Q * D : ℤ) : ℚ)) * (2 : ℚ) ^ p + 1 / 2⌋ =
      qn p (rnd p (((gh ⬝ᵥ mu : ℤ) : ℚ) / ((Q * D : ℤ) : ℚ))) := by
    unfold rnd qn
    simp
  rw [h_floor_eq]
  have h_qn_div := qn_rnd_div p (gh ⬝ᵥ mu) (Q * D) (mul_pos hQpos hD)
  rw [h_qn_div]
  rw [hQ]
  have h_num : 2 * (gh ⬝ᵥ mu) * (2 ^ p) + (2 ^ p) * D =
      (gh ⬝ᵥ mu) * (2 ^ p) + (gh ⬝ᵥ mu) * (2 ^ p) + (2 ^ p) * D := by ring
  have h_den : 2 * ((2 ^ p) * D) = (2 ^ p) * D + (2 ^ p) * D := by ring
  rw [h_num, h_den]

/-- R8's `A'` on the integers: with `A = Â/Q`, `ξ = Γ/G`, `s1 = ŝ1/Q`, `s2 = ŝ2/Q`, `Q = 2^p`, the entry `(i, j)` of
`rnd_p (s1 A - s2 (A ξ) ξᵀ)` lies on the grid and its numerator is `(U Q + U Q + V)/(V + V)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r8_Aq {d : ℕ} (p : ℕ) (Q G s1 s2 : ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (hQ : Q = 2 ^ p) (hG : 0 < G) (i j : Fin d) :
    OnG p (rndM p (((s1 : ℚ) / Q) • (Matrix.of fun a b => (Ah a b : ℚ) / Q) -
        ((s2 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j) ∧
    qn p (rndM p (((s1 : ℚ) / Q) • (Matrix.of fun a b => (Ah a b : ℚ) / Q) -
        ((s2 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Ah a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j) =
      ((s1 * Ah i j * (G * G) - s2 * (Ah *ᵥ Γ) i * Γ j) * Q +
          (s1 * Ah i j * (G * G) - s2 * (Ah *ᵥ Γ) i * Γ j) * Q + Q * Q * (G * G)) /
        (Q * Q * (G * G) + Q * Q * (G * G)) := by
  have hQpos : 0 < Q := by rw [hQ]; positivity
  refine ⟨onG_rnd_s p _, ?_⟩
  simp only [rndM]
  rw [r8_A Q G s1 s2 Ah Γ hQpos hG i j, qn_rnd_div p _ _ (by positivity)]
  subst hQ
  congr 1 <;> ring

/-- R8's `B'` on the integers: with `B = B̂/Q`, `ξ = Γ/G`, `s3 = ŝ3/Q`, `s4 = ŝ4/Q`, `Q = 2^p`, the entry `(i, j)` of
`rnd_p (s3 B + s4 (B ξ) ξᵀ)` lies on the grid and its numerator is `(U Q + U Q + V)/(V + V)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r8_Bq {d : ℕ} (p : ℕ) (Q G s3 s4 : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (hQ : Q = 2 ^ p) (hG : 0 < G) (i j : Fin d) :
    OnG p (rndM p (((s3 : ℚ) / Q) • (Matrix.of fun a b => (Bh a b : ℚ) / Q) +
        ((s4 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j) ∧
    qn p (rndM p (((s3 : ℚ) / Q) • (Matrix.of fun a b => (Bh a b : ℚ) / Q) +
        ((s4 : ℚ) / Q) • vecMulVec ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)
          (fun k => (Γ k : ℚ) / G)) i j) =
      ((s3 * Bh i j * (G * G) + s4 * (Bh *ᵥ Γ) i * Γ j) * Q +
          (s3 * Bh i j * (G * G) + s4 * (Bh *ᵥ Γ) i * Γ j) * Q + Q * Q * (G * G)) /
        (Q * Q * (G * G) + Q * Q * (G * G)) := by
  have hQpos : 0 < Q := by rw [hQ]; positivity
  refine ⟨onG_rnd_s p _, ?_⟩
  simp only [rndM]
  rw [r8_B Q G s3 s4 Bh Γ hQpos hG i j, qn_rnd_div p _ _ (by positivity)]
  subst hQ
  congr 1 <;> ring

/-- R9's `g` on the integers: with `B = B̂/Q`, `ξ = Γ/G`, `Y = Ŷ/Q`, `ν = ν̂/F`, `Q = 2^p`, the coordinate `i` of
`rnd_p ((Y ν) B ξ)` lies on the grid and its numerator is `(U Q + U Q + V)/(V + V)`. -/
theorem AdversarialBco.Bit.Transfer.BLM.r9_gq {d : ℕ} (p : ℕ) (F Q G yh nh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (Γ : Fin d → ℤ) (hQ : Q = 2 ^ p) (hF : 0 < F) (hG : 0 < G) (i : Fin d) :
    OnG p (rndV p ((((yh : ℚ) / Q) * ((nh : ℚ) / F)) •
        ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)) i) ∧
    qn p (rndV p ((((yh : ℚ) / Q) * ((nh : ℚ) / F)) •
        ((Matrix.of fun a b => (Bh a b : ℚ) / Q) *ᵥ fun k => (Γ k : ℚ) / G)) i) =
      (yh * nh * (Bh *ᵥ Γ) i * Q + yh * nh * (Bh *ᵥ Γ) i * Q + F * Q * Q * G) / (F * Q * Q * G + F * Q * Q * G) := by
  have hQpos : 0 < Q := by rw [hQ]; positivity
  refine ⟨onG_rnd_s p _, ?_⟩
  simp only [rndV]
  rw [(r9_gl F Q G 1 yh nh Bh Γ 0 0 hF hQpos hG one_pos i).1, qn_rnd_div p _ _ (by positivity)]
  subst hQ
  congr 1 <;> ring
