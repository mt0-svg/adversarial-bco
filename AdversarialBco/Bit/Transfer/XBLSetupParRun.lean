/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupParV

@[expose] public section

/-!
# BL's setup on the machine: the run of PARAM

The side conditions of the 22 steps of `parSt` that are not expressions (integer roots, powers, logarithms, Mercator
sums) hold at the magnitude `parG d n = q + pF + 2 gsm_prec B`; with them `XV.sl` runs PARAM from `d` (slot `0`) and
`n` (slot `3`), and slot `30 + k` ends holding `pv d n k`. The positivity of `Le'` (`LeN d n > 0`) comes from the
error bound of `LOGINT` (`PieceA.lnQ_err`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-! ## `LOGINT` on the integers -/

theorem lnQ_eq (q N : ℕ) (hN : 1 ≤ N) : lnQ q N = (loI q N : ℚ) / 2 ^ q := by
  have hgsm0 : ∀ i, gsm_powq q 0 i = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => unfold gsm_powq; rw [ih]; simp
  have hmercq0 : gsm_mercq q 0 q = 0 := by
    unfold gsm_mercq
    simp [hgsm0]
  have hlog1 : Nat.log 2 1 = 0 := by
    simp
  have hNpos : 0 < N := by omega
  have hpos_size : 0 < N.size := by
    rw [Nat.size_pos]
    exact hNpos
  have hsize_log_nat : N.size = Nat.log 2 N + 1 := by
    have hle : 2 ^ (N.size - 1) ≤ N := by
      have hlt : N.size - 1 < N.size := by omega
      rw [← Nat.lt_size]
      exact hlt
    have hlt : N < 2 ^ N.size := Nat.lt_size_self N
    have hsize_eq : N.size = (N.size - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ N.size)).symm
    rw [hsize_eq] at hlt
    have hlog := Nat.log_eq_of_pow_le_of_lt_pow hle hlt
    omega
  have hlog_eq : Nat.log 2 N = N.size - 1 := by omega
  unfold lnQ loI gsm_LLq
  push_cast
  have h2q : (2 ^ q : ℚ) ≠ 0 := by positivity
  field_simp [h2q]
  -- Simplify N - 1 + 1 = N
  have hNsub_nat : N - 1 + 1 = N := by omega
  rw [hNsub_nat]
  -- Simplify Nat.log 2 N = N.size - 1
  rw [hlog_eq]
  -- Now simplify using hlog1 and hmercq0
  simp [hlog1, hmercq0]
  have hsub : (N.size : ℚ) - ((N.size - 1 : ℕ) : ℚ) = 1 := by
    have h : 1 ≤ N.size := by omega
    push_cast [h]
    ring
  rw [hsub, mul_one]

theorem loI_nonneg (q N : ℕ) (hN : 1 ≤ N) : 0 ≤ loI q N := by
  have hs : (1 : ℤ) ≤ N.size := by exact_mod_cast Nat.size_pos.2 hN
  have hΛ := Int.natCast_nonneg (gsm_mercq q (2 ^ (q - 1)) q)
  have hS := Int.natCast_nonneg (gsm_mercq q ((N - 2 ^ (N.size - 1)) * 2 ^ q / N) q)
  have hm : max ((gsm_mercq q (2 ^ (q - 1)) q : ℤ) - gsm_mercq q ((N - 2 ^ (N.size - 1)) * 2 ^ q / N) q) 0 ≤
      (gsm_mercq q (2 ^ (q - 1)) q : ℤ) := max_le (by linarith) hΛ
  have h1 := mul_le_mul_of_nonneg_right hs hΛ
  unfold loI
  linarith

section Bounds

variable {d n : ℕ}

theorem xN_le (q N : ℕ) : xN q N ≤ 2 ^ q :=
  Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

end Bounds

/-! ## The side conditions -/

theorem nn_of_eq {v : ℤ} {a : ℕ} (h : v = a) : 0 ≤ v := h ▸ Int.natCast_nonneg a

theorem pw_of_eq {v : ℤ} {a G : ℕ} (h : v = a) (ha : a ≤ G) : 0 ≤ v ∧ v ≤ G := by
  subst h; exact ⟨Int.natCast_nonneg a, by exact_mod_cast ha⟩

theorem mc_of_eq {vq vQ vX : ℤ} {q G : ℕ} (hq : vq = q) (hQ : vQ = 2 ^ q) (hqG : q ≤ G) (hX0 : 0 ≤ vX)
    (hXq : vX ≤ 2 ^ q) : 0 ≤ vq ∧ vq ≤ G ∧ vQ = 2 ^ vq.toNat ∧ 0 ≤ vX ∧ vX ≤ vQ := by
  subst hq hQ
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hqG, by rw [Int.toNat_natCast], hX0, hXq⟩

end AdversarialBco.Bit.Transfer.BLM
