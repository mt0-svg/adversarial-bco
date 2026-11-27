/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllOut

@[expose] public section

/-!
# ELL-R and BIS-R on the machine: the bounds of the projection routine

The register needs (`ell_regs`), the products of ELL-R's constants below powers of `2` (`ell_pows`), the exponent
bounds of ELL-R's matrix and point (`ellE`, `ellF`), and the inputs of the block under a change above its bases
(`EllIn.frame`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Arithmetic -/

/-- The register needs from `1000 W^3 < A`, `W = d + m + s + 1`. -/
theorem ell_regs {d m s lam A : ℕ} (hlam : lam ≤ 7 * s + d + 3) (h : 1000 * (d + m + s + 1) ^ 3 < A) :
    2 * d * (d + 1) * lam + 1 < A ∧ 1000 * (d + m + s + 1) < A ∧ d * d + d < A ∧
      (d * (d + 1) + d * (d + 1)) * lam + 1 < A ∧ d * (d + 1) + d * (d + 1) < A := by
  have hW : 1 ≤ d + m + s + 1 := by omega
  have h2 : (d + m + s + 1) ^ 2 ≤ (d + m + s + 1) ^ 3 := Nat.pow_le_pow_right hW (by norm_num)
  have h1 : d + m + s + 1 ≤ (d + m + s + 1) ^ 2 := by
    calc d + m + s + 1 = (d + m + s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (d + m + s + 1) ^ 2 := Nat.pow_le_pow_right hW (by norm_num)
  have hdd : d * (d + 1) ≤ (d + m + s + 1) ^ 2 := by nlinarith
  have hdd' : d * d + d ≤ (d + m + s + 1) ^ 2 := by nlinarith
  have hl : lam ≤ 7 * (d + m + s + 1) := by omega
  have hN : 2 * d * (d + 1) * lam ≤ 14 * (d + m + s + 1) ^ 3 := by
    calc 2 * d * (d + 1) * lam = 2 * (d * (d + 1)) * lam := by ring
      _ ≤ 2 * (d + m + s + 1) ^ 2 * (7 * (d + m + s + 1)) := by gcongr
      _ = 14 * (d + m + s + 1) ^ 3 := by ring
  have hN' : (d * (d + 1) + d * (d + 1)) * lam = 2 * d * (d + 1) * lam := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem abs_le_of_le {x : ℤ} {a E : ℕ} (h0 : 0 ≤ x) (h : x ≤ 2 ^ a) (ha : a ≤ E) : |x| ≤ 2 ^ E := by
  rw [abs_of_nonneg h0]; exact h.trans (pow_le_pow_right₀ (by norm_num) ha)

/-- The products of ELL-R's constants below powers of `2`, from `R̄ ≤ 2^s`. -/
theorem ell_pows {s lam p : ℕ} {Rb : ℤ} (hR0 : 0 ≤ Rb) (hR : Rb ≤ 2 ^ s) :
    Rb * Rb ≤ 2 ^ (2 * s) ∧ Rb * Rb * 2 ^ (6 * lam + 2) ≤ 2 ^ (2 * s + (6 * lam + 2)) ∧
      Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1)) ∧
      Rb + Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1) + 1) ∧
      (2 : ℤ) ^ p * (Rb * Rb) ≤ 2 ^ (p + 2 * s) ∧
      (2 : ℤ) ^ p * (Rb * Rb * 2 ^ (6 * lam + 2)) ≤ 2 ^ (p + (2 * s + (6 * lam + 2))) ∧
      (2 : ℤ) ^ p * (Rb + Rb * 2 ^ (3 * lam + 1)) ≤ 2 ^ (p + (s + (3 * lam + 1) + 1)) := by
  have hRR : Rb * Rb ≤ 2 ^ (2 * s) := by rw [two_mul, pow_add]; exact mul_le_mul hR hR hR0 (by positivity)
  have hL : Rb * Rb * 2 ^ (6 * lam + 2) ≤ 2 ^ (2 * s + (6 * lam + 2)) := by
    rw [pow_add (2 : ℤ) (2 * s) (6 * lam + 2)]; exact mul_le_mul_of_nonneg_right hRR (by positivity)
  have hLH : Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1)) := by
    rw [pow_add (2 : ℤ) s (3 * lam + 1)]; exact mul_le_mul_of_nonneg_right hR (by positivity)
  have hRL : Rb + Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1) + 1) := by
    have : Rb ≤ 2 ^ (s + (3 * lam + 1)) := hR.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    rw [pow_succ (2 : ℤ) (s + (3 * lam + 1))]; linarith
  refine ⟨hRR, hL, hLH, hRL, ?_, ?_, ?_⟩
  · rw [pow_add (2 : ℤ) p (2 * s)]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
  · rw [pow_add (2 : ℤ) p (2 * s + (6 * lam + 2))]; exact mul_le_mul_of_nonneg_left hL (by positivity)
  · rw [pow_add (2 : ℤ) p (s + (3 * lam + 1) + 1)]; exact mul_le_mul_of_nonneg_left hRL (by positivity)

/-- The inputs survive a change above the bases. -/
theorem EllIn.frame {B : EllBlk} {I : EllI d} {L : Layout} {nS nN nA : ℕ} {S N : ℕ → Prop}
    {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (hB : B.OK L nS nN nA) (h : EllIn B I σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → B.o ≤ y) (hN : ∀ j, N j → B.rE ≤ j) (hA : ∀ b k, Ar b k → B.aW ≤ b) : EllIn B I σ' := by
  obtain ⟨-, -, -, hrd, hrm, hsl, hsDf, hsRn, hsRd, hsrn, hsrd, hsen, hsed, haH, hag, haP, haf⟩ := hB
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := h
  have nS : ∀ y, y < B.o → σ'.sc y = σ.sc y := fun y hy => hF.2.1 y (fun h => by have := hS y h; omega)
  have nN : ∀ j, j < B.rE → σ'.nat j = σ.nat j := fun j hj => hF.1 j (fun h => by have := hN j h; omega)
  have nA : ∀ b k, b < B.aW → σ'.arr b k = σ.arr b k := fun b k hb =>
    hF.2.2.1 b k (fun h => by have := hA b k h; omega)
  exact ⟨by rw [nN _ hrd, e1], by rw [nN _ hrm, e2], by rw [nS _ hsl, e3], by rw [nS _ hsDf, e4],
    by rw [nS _ hsRn, e5], by rw [nS _ hsRd, e6], by rw [nS _ hsrn, e7], by rw [nS _ hsrd, e8],
    by rw [nS _ hsen, e9], by rw [nS _ hsed, e10], fun i j => by rw [nA _ _ haH, e11 i j],
    fun j => by rw [nA _ _ hag, e12 j], fun i j => by rw [nA _ _ haP, e13 i j], fun j => by rw [nA _ _ haf, e14 j]⟩

/-! ## ELL-R -/

/-- The exponent bound of ELL-R's matrix, `70 s + 30 d + 80`. -/
def ellE (d s : ℕ) : ℕ := 70 * s + 30 * d + 80

/-- The exponent bound of ELL-R's point, `40 s + 20 d + 60`. -/
def ellF (d s : ℕ) : ℕ := 40 * s + 20 * d + 60

end AdversarialBco.Bit.Transfer
