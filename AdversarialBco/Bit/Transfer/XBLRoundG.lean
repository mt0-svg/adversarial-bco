/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadG
public import AdversarialBco.Bit.Transfer.XBLHeadB
public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# The arithmetic glue of BL's round, second part

The units of the round as a power of its work term, the lower bound of `E` split into the magnitudes, the exponent
of R14's point, the sampler and the position's work term, `E + 4 ≤ ℓ`, R14's linear term from R10's and R13's tests,
the bounds of a state at a larger exponent, the sizes, a height bound at the next integer.
-/

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.Transfer.BLM Matrix

/-- R14's linear term `(B'B'ᵀ) w_μ` from R10's and R13's tests. -/
theorem AdversarialBco.Bit.Transfer.BLM.f_abs {d : ℕ} (Bp : Matrix (Fin d) (Fin d) ℚ) (w : Fin d → ℚ) (Lam : ℕ) (W : ℚ)
    (a : ℕ)
    (hF : frob2 Bp ≤ 2 * (Lam : ℚ)) (hL : (Lam : ℚ) ≤ 2 ^ a) (hw : ∀ j, |w j| ≤ 2 * |W|) (hW : |W| ≤ 2 ^ a)
    (hd : (d : ℚ) ≤ 2 ^ a) (i : Fin d) : |((Bp * Bpᵀ) *ᵥ w) i| ≤ 2 ^ (5 * a + 5) := by
  set T : ℚ := 2 * (Lam : ℚ) + 1 with hTdef
  set R : ℚ := 2 * |W| with hRdef
  have hLam_nonneg : 0 ≤ (Lam : ℚ) := by exact_mod_cast Nat.zero_le Lam
  have h_absW_nonneg : 0 ≤ |W| := abs_nonneg _
  have hT_one : 1 ≤ T := by
    rw [hTdef]
    nlinarith
  have hTpos : 0 ≤ T := by nlinarith
  have hRpos : 0 ≤ R := by
    rw [hRdef]
    nlinarith
  have h_frob_le_T : frob2 Bp ≤ T := by
    rw [hTdef]
    nlinarith
  have hT_le : T ≤ (2 : ℚ) ^ (a + 2) := by
    rw [hTdef]
    have h_pow_ge_one : 1 ≤ (2 : ℚ) ^ a :=
      Nat.rec (by norm_num) (fun k ih => by
        rw [pow_succ]
        nlinarith) a
    calc
      2 * (Lam : ℚ) + 1 ≤ 2 * ((2 : ℚ) ^ a) + 1 := by nlinarith
      _ ≤ 2 * ((2 : ℚ) ^ a) + (2 : ℚ) ^ a := by nlinarith
      _ = 3 * ((2 : ℚ) ^ a) := by ring
      _ ≤ 4 * ((2 : ℚ) ^ a) := by
        have h_nonneg : 0 ≤ (2 : ℚ) ^ a := pow_nonneg (by norm_num) a
        nlinarith
      _ = (2 : ℚ) ^ 2 * ((2 : ℚ) ^ a) := by norm_num
      _ = (2 : ℚ) ^ (a + 2) := by rw [← pow_add, add_comm 2 a]
  have hR_le : R ≤ (2 : ℚ) ^ (a + 1) := by
    rw [hRdef]
    calc
      2 * |W| ≤ 2 * ((2 : ℚ) ^ a) := by nlinarith
      _ = (2 : ℚ) ^ (a + 1) := by rw [mul_comm, ← pow_succ]
  have hB : ∀ i j, |Bp i j| ≤ T := by
    intro i j
    exact gl_frob Bp T h_frob_le_T hT_one i j
  have hw' : ∀ j, |w j| ≤ R := by
    intro j
    rw [hRdef]
    exact hw j
  have h_bound : |((Bp * Bpᵀ) *ᵥ w) i| ≤ (d : ℚ) * (d : ℚ) * T * T * R :=
    hb_Pw Bp w T R hTpos hRpos hB hw' i
  have h_final : (d : ℚ) * (d : ℚ) * T * T * R ≤ (2 : ℚ) ^ (5 * a + 5) := by
    have h_prod : (d : ℚ) * (d : ℚ) * T * T * R ≤
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) := by
      have h_nonneg_d : 0 ≤ (d : ℚ) := by exact_mod_cast Nat.zero_le d
      have h_nonneg_T : 0 ≤ T := hTpos
      have h_nonneg_2a : 0 ≤ (2 : ℚ) ^ a := pow_nonneg (by norm_num) a
      have h_nonneg_2a2 : 0 ≤ (2 : ℚ) ^ (a + 2) := pow_nonneg (by norm_num) (a + 2)
      have h1 : (d : ℚ) * (d : ℚ) ≤ (2 : ℚ) ^ a * (2 : ℚ) ^ a :=
        mul_le_mul hd hd h_nonneg_d h_nonneg_2a
      have h2 : T * T ≤ (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) :=
        mul_le_mul hT_le hT_le h_nonneg_T h_nonneg_2a2
      have h12 : ((d : ℚ) * (d : ℚ)) * (T * T) ≤
          ((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      have h_final : (((d : ℚ) * (d : ℚ)) * (T * T)) * R ≤
          (((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2))) * (2 : ℚ) ^ (a + 1) :=
        mul_le_mul h12 hR_le (by positivity) (by positivity)
      simpa [mul_assoc] using h_final
    have h_pow_eq : (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) =
        (2 : ℚ) ^ (5 * a + 5) := by
      calc
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1)
            = ((2 : ℚ) ^ a * (2 : ℚ) ^ a) * ((2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2)) * (2 : ℚ) ^ (a + 1) := by ring
        _ = (2 : ℚ) ^ (a + a) * (2 : ℚ) ^ ((a + 2) + (a + 2)) * (2 : ℚ) ^ (a + 1) := by rw [← pow_add, ← pow_add]
        _ = (2 : ℚ) ^ ((a + a) + ((a + 2) + (a + 2))) * (2 : ℚ) ^ (a + 1) := by rw [← pow_add]
        _ = (2 : ℚ) ^ (((a + a) + ((a + 2) + (a + 2))) + (a + 1)) := by rw [← pow_add]
        _ = (2 : ℚ) ^ (5 * a + 5) := by ring
    calc
      (d : ℚ) * (d : ℚ) * T * T * R ≤
        (2 : ℚ) ^ a * (2 : ℚ) ^ a * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 2) * (2 : ℚ) ^ (a + 1) := h_prod
      _ = (2 : ℚ) ^ (5 * a + 5) := h_pow_eq
  exact le_trans h_bound h_final

/-- The bounds of a state at a larger exponent. -/
theorem AdversarialBco.Bit.Transfer.BLM.StBnd_mono {d : ℕ} {p E E' R : ℕ} {st : St d}
    (h : StBnd p E R st) (hE : E ≤ E') : StBnd p E' R st := by
  rcases h with ⟨hA, hB, hb, hk, hG, hl, hmu⟩
  have hp : (2 : ℤ) ^ E ≤ (2 : ℤ) ^ E' :=
    pow_le_pow_right₀ (by norm_num) hE
  exact ⟨λ i j => (hA i j).trans hp, λ i j => (hB i j).trans hp, λ j => (hb j).trans hp,
    hk.trans hp, λ j => (hG j).trans hp, hl.trans hp, hmu⟩

