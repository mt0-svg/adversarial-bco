/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.ProjBit
public import AdversarialBco.Bit.Frame

@[expose] public section

/-!
# One step of the rounded ellipsoid method

`ellUpd_step`: the step `ellUpd` of Bit/RoutQ.lean (steps 6 to 8 of Procedure ELL-R, steps 3 to 5 of ELL-F) keeps the
invariant of the proof of the projection theorem (b), (i) to (iv): if the carried ball
`B' = B̄(z₀, ρ)`, `ρ = 2^{-j}`, lies in `E(A, a)` (`A = Â/2^p`, `a = â/2^p` positive definite) and on the side
`c·(x - a) ≤ 0` of the cut, the step passes (K1) and (K2), the new matrix is positive definite, `B' ⊆ E(A', a')`,
`λ_max` grows by at most `γ` and `det` falls by `e^{-ω}`, `ω = 95/(128(d + 1))`. The step is shared by ELL-R
(`O3SpecQ apQ`) and ELL-F (the frame). Lemmas CC, BALL, ABS, SQ come from Bit/ProjBit.lean, the margins from
Bit/Frame.lean.
-/

namespace AdversarialBco.Bit.ApQ

open AdversarialBco.Bit.RQ
open Matrix

variable {d : ℕ}

/-- `Â/2^p` over `ℝ`. -/
noncomputable def mR (p : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  ((1 : ℝ) / 2 ^ p) • A.map ((↑) : ℤ → ℝ)

/-- `â/2^p` over `ℝ`. -/
noncomputable def vR (p : ℕ) (a : Fin d → ℤ) : Fin d → ℝ := fun i => (a i : ℝ) / 2 ^ p

/-- An integer vector over `ℝ`. -/
def vZ (c : Fin d → ℤ) : Fin d → ℝ := fun i => (c i : ℝ)

/-- `x ∈ E(M, a)`. -/
def InE (M : Matrix (Fin d) (Fin d) ℝ) (a x : Fin d → ℝ) : Prop := (x - a) ⬝ᵥ (M⁻¹ *ᵥ (x - a)) ≤ 1

/-- `x ∈ B̄(z, ρ)`. -/
def InB (z : Fin d → ℝ) (ρ : ℝ) (x : Fin d → ℝ) : Prop := (x - z) ⬝ᵥ (x - z) ≤ ρ ^ 2

/-- `γ = κ + 1/(128 d (d + 1))`, the growth of `λ_max` in one step (Lemma CAP). -/
noncomputable def gam (d : ℕ) : ℝ :=
  (d : ℝ) * (2 * d + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) + 1 / (128 * d * ((d : ℝ) + 1))

/-- The blow-up `lam = ((2d + 1)²/(4d(d + 1)))^{1/2}`. -/
noncomputable def lamR (d : ℕ) : ℝ := Real.sqrt ((2 * (d : ℝ) + 1) ^ 2 / (4 * d * ((d : ℝ) + 1)))

/-- `t = isqrt(⌊ŝ 2^{2q}/2^p⌋)` of step 7. -/
def tQ (p q : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ) : ℤ :=
  (Nat.sqrt ((c ⬝ᵥ (A *ᵥ c)) * 2 ^ (2 * q) / 2 ^ p).toNat : ℤ)

/-- The new centre of step 7. -/
def newa (p q : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ) : Fin d → ℤ :=
  fun i => a i - rndI ((A *ᵥ c) i * 2 ^ q) ((d + 1) * tQ p q A c)

/-- The new matrix of step 7. -/
def newA (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i k => rndI (kapN d * ((d + 1) * (c ⬝ᵥ (A *ᵥ c)) * A i k - 2 * (A *ᵥ c) i * (A *ᵥ c) k))
    (kapD d * (d + 1) * (c ⬝ᵥ (A *ᵥ c)))

/-! ## Leaves -/

theorem ellUpd_eq (p q j : ℕ) (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ)
    (h1 : ¬ c ⬝ᵥ (A *ᵥ c) < 2 ^ (p - 2 * j) * (c ⬝ᵥ c)) (h2 : ∀ i k, |newA A c i k| ≤ capA)
    (h3 : ∀ i, |newa p q A a c i| ≤ capa) :
    ellUpd p q j capA capa A a c = some (newA A c, newa p q A a c) := by
  simp [ellUpd, h1]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [newA] using h2
  · simpa [newa, tQ] using h3
  · rfl

theorem vZ_one_le (c : Fin d → ℤ) (hc : c ≠ 0) : 1 ≤ vZ c ⬝ᵥ vZ c := by
  have hsum : vZ c ⬝ᵥ vZ c = ∑ i : Fin d, ((c i : ℝ) * (c i : ℝ)) := by
    simp [vZ, dotProduct]
  rw [hsum]
  have h_exists : ∃ i : Fin d, c i ≠ 0 := by
    have := (Function.ne_iff.mp hc)
    rcases this with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa using hi
  rcases h_exists with ⟨i, hi⟩
  have h_sq : 1 ≤ (c i : ℝ) ^ 2 := by
    have h_abs : (1 : ℤ) ≤ |c i| := Int.one_le_abs hi
    have h_abs' : (1 : ℝ) ≤ |(c i : ℝ)| := by
      exact_mod_cast h_abs
    have h_sq_abs : (1 : ℝ) ≤ |(c i : ℝ)| ^ 2 := by
      nlinarith
    have h_eq : (c i : ℝ) ^ 2 = |(c i : ℝ)| ^ 2 := by simp
    rw [h_eq]
    exact h_sq_abs
  have h_nonneg : ∀ i : Fin d, 0 ≤ (c i : ℝ) * (c i : ℝ) := by
    intro i
    have : 0 ≤ (c i : ℝ) ^ 2 := pow_two_nonneg _
    simpa [sq] using this
  have h_mem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
  calc
    1 ≤ (c i : ℝ) * (c i : ℝ) := by
      simpa [sq] using h_sq
    _ ≤ ∑ j : Fin d, ((c j : ℝ) * (c j : ℝ)) :=
      Finset.single_le_sum (fun j hj => h_nonneg j) h_mem

theorem vZ_ne (c : Fin d → ℤ) (hc : c ≠ 0) : vZ c ≠ 0 := by
  intro h
  apply hc
  ext i
  have hi : vZ c i = 0 := by rw [h, Pi.zero_apply]
  rw [vZ] at hi
  exact Int.cast_eq_zero.mp hi

theorem dot_cast (p : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ) :
    ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) = 2 ^ p * (vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) := by
  unfold vZ mR
  simp [dotProduct, Matrix.mulVec_apply, Matrix.smul_apply, Matrix.map_apply]
  simp only [Finset.mul_sum]
  have h : (2⁻¹ : ℝ) ^ p * (2 : ℝ) ^ p = 1 := by
    calc
      (2⁻¹ : ℝ) ^ p * (2 : ℝ) ^ p = ((2⁻¹ : ℝ) * (2 : ℝ)) ^ p := by rw [← mul_pow]
      _ = 1 ^ p := by norm_num
      _ = 1 := by simp
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  field_simp

theorem k1_pass (p j : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ) (hp : 2 * j ≤ p)
    (h : (1 / 2 ^ j : ℝ) ^ 2 * (vZ c ⬝ᵥ vZ c) ≤ vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) :
    ¬ c ⬝ᵥ (A *ᵥ c) < 2 ^ (p - 2 * j) * (c ⬝ᵥ c) := by
  have h_dot_eq : vZ c ⬝ᵥ vZ c = ((c ⬝ᵥ c : ℤ) : ℝ) := by
    simp [vZ, dotProduct]
  have hS : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hkey : (vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)) =
             (2 ^ p : ℝ) * (vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) := by
    calc
      (vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c))
          = (vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)) * 1 := by ring
      _ = (vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)) * (((2 : ℝ) ^ p)⁻¹ * ((2 : ℝ) ^ p)) := by
        field_simp [hS]
      _ = ((vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)) * ((2 : ℝ) ^ p)⁻¹) * ((2 : ℝ) ^ p) := by ring
      _ = (((2 : ℝ) ^ p)⁻¹ * ((vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)))) * ((2 : ℝ) ^ p) := by ring
      _ = ((2 : ℝ) ^ p) * (((2 : ℝ) ^ p)⁻¹ * ((vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)))) := by ring
      _ = ((2 : ℝ) ^ p) * ((vZ c) ⬝ᵥ (mR p A *ᵥ vZ c)) := by
        simp [mR, dotProduct_smul, Matrix.smul_mulVec]
  have h_mul_eq : ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) = (2 ^ p : ℝ) * (vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) := by
    calc
      ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) = (fun i => (c i : ℝ)) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (fun i => (c i : ℝ))) := by
        simp [dotProduct, mulVec]
      _ = (vZ c) ⬝ᵥ ((A.map (fun x => (x : ℝ))) *ᵥ (vZ c)) := rfl
      _ = (2 ^ p : ℝ) * (vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) := by rw [hkey]
  have h_pow_eq : (2 ^ p : ℝ) * ((1 : ℝ) / 2 ^ j) ^ 2 = (2 : ℝ) ^ (p - 2 * j) := by
    calc
      (2 ^ p : ℝ) * ((1 : ℝ) / 2 ^ j) ^ 2 = (2 ^ p : ℝ) * (1 / ((2 : ℝ) ^ j) ^ 2) := by ring
      _ = (2 ^ p : ℝ) / ((2 : ℝ) ^ j) ^ 2 := by ring
      _ = (2 ^ p : ℝ) / ((2 : ℝ) ^ (2 * j)) := by simp [pow_mul, mul_comm]
      _ = (2 : ℝ) ^ (p - 2 * j) := by
        rw [div_eq_mul_inv]
        simpa using (pow_sub₀ (a := (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 0) hp).symm
  have h_ineq_real : ((2 ^ (p - 2 * j) * (c ⬝ᵥ c) : ℤ) : ℝ) ≤ ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) := by
    calc
      ((2 ^ (p - 2 * j) * (c ⬝ᵥ c) : ℤ) : ℝ) = (2 : ℝ) ^ (p - 2 * j) * ((c ⬝ᵥ c : ℤ) : ℝ) := by simp
      _ = ((2 ^ p : ℝ) * ((1 : ℝ) / 2 ^ j) ^ 2) * ((c ⬝ᵥ c : ℤ) : ℝ) := by rw [h_pow_eq]
      _ = (2 ^ p : ℝ) * (((1 : ℝ) / 2 ^ j) ^ 2 * ((c ⬝ᵥ c : ℤ) : ℝ)) := by ring
      _ = (2 ^ p : ℝ) * (((1 : ℝ) / 2 ^ j) ^ 2 * (vZ c ⬝ᵥ vZ c)) := by rw [h_dot_eq]
      _ ≤ (2 ^ p : ℝ) * (vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) := by
        have h_nonneg : 0 ≤ (2 : ℝ) ^ p := by positivity
        exact mul_le_mul_of_nonneg_left h h_nonneg
      _ = ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) := by rw [h_mul_eq]
  have h_ineq_int : 2 ^ (p - 2 * j) * (c ⬝ᵥ c) ≤ c ⬝ᵥ (A *ᵥ c) := by
    exact_mod_cast h_ineq_real
  exact not_lt.mpr h_ineq_int

/-- Integer division is the floor of the real quotient, for `a ≥ 0`, `b > 0`. -/
theorem int_ediv_eq_floor_real {a b : ℤ} (hb_pos : 0 < b) (_ha_nonneg : 0 ≤ a) :
    (a / b : ℤ) = ⌊(a : ℝ) / (b : ℝ)⌋ := by
  have hb_ne_zero : b ≠ 0 := by linarith
  have h_div_add_mod := EuclideanDomain.div_add_mod (a := a) (b := b)
  have h_mod_lt : a % b < b := Int.emod_lt_of_pos a hb_pos
  have h_mod_nonneg : 0 ≤ a % b := Int.emod_nonneg a hb_ne_zero
  have hb_real_pos : 0 < (b : ℝ) := by exact_mod_cast hb_pos
  rw [eq_comm, Int.floor_eq_iff]
  have h_cast_div_add_mod : (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) = (a : ℝ) := by
    have h' := congrArg (fun x : ℤ => (x : ℝ)) h_div_add_mod
    push_cast at h'
    exact h'
  have h_cast_mod_lt : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast h_mod_lt
  have h_cast_mod_nonneg : 0 ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h_mod_nonneg
  constructor
  · rw [le_div_iff₀ hb_real_pos]
    have h_mul : (b : ℝ) * ((a / b : ℤ) : ℝ) ≤ (a : ℝ) := by
      linarith
    nlinarith
  · rw [div_lt_iff₀ hb_real_pos]
    nlinarith

theorem tQ_eq (p q : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ)
    (h : 0 ≤ vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) :
    ((tQ p q A c : ℤ) : ℝ) = (Nat.sqrt ⌊vZ c ⬝ᵥ (mR p A *ᵥ vZ c) * 2 ^ (2 * q)⌋₊ : ℝ) := by
  set s := c ⬝ᵥ (A *ᵥ c) with hs
  have hp_real_pos : 0 < (2 ^ p : ℝ) := pow_pos (by norm_num) p
  have hp_int_pos : 0 < (2 ^ p : ℤ) := pow_pos (by norm_num) p
  have hs_nonneg : 0 ≤ (s : ℝ) := by
    have h_eq : vZ c ⬝ᵥ (mR p A *ᵥ vZ c) = (s : ℝ) / (2 ^ p : ℝ) := by
      unfold vZ mR
      rw [Matrix.smul_mulVec, dotProduct_smul]
      have hdot : (fun i => (c i : ℝ)) ⬝ᵥ ((A.map (fun x => (x : ℝ))).mulVec (fun i => (c i : ℝ))) = (s : ℝ) := by
        simp [Matrix.map, Matrix.mulVec, dotProduct, hs]
      rw [hdot]
      ring
    rw [h_eq] at h
    rcases (div_nonneg_iff.mp h) with (⟨hnum, hden⟩ | ⟨hnum, hden⟩)
    · exact hnum
    · exfalso
      linarith [hp_real_pos, hden]
  have h_s_mul_nonneg : 0 ≤ s * (2 : ℤ) ^ (2 * q) := by
    have hs_int_nonneg : 0 ≤ s := by exact_mod_cast hs_nonneg
    have : 0 ≤ (2 : ℤ) ^ (2 * q) := pow_nonneg (by norm_num) _
    nlinarith
  set a := s * (2 : ℤ) ^ (2 * q) with ha
  set b := (2 ^ p : ℤ) with hb
  have ha_nonneg : 0 ≤ a := h_s_mul_nonneg
  have hb_pos : 0 < b := hp_int_pos
  -- Key equality: the integer division equals the real floor
  have h_floor_eq : ((a / b).toNat : ℤ) = ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋₊ := by
    -- Use the lemma int_ediv_eq_floor_real
    have h_int_eq : a / b = ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋ := by
      -- The lemma gives ⌊(a : ℝ) / (b : ℝ)⌋ = a / b
      -- But we need ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋
      -- These are equal because (a : ℝ) = (s : ℝ) * (2 : ℝ) ^ (2 * q) and (b : ℝ) = (2 ^ p : ℝ)
      have h_eq_floor : ⌊(a : ℝ) / (b : ℝ)⌋ = a / b := by
        rw [int_ediv_eq_floor_real hb_pos ha_nonneg]
      have h_cast_a : (a : ℝ) = (s : ℝ) * (2 : ℝ) ^ (2 * q) := by
        dsimp [a]
        push_cast
        ring
      have h_cast_b : (b : ℝ) = (2 ^ p : ℝ) := by simp [b]
      rw [h_cast_a, h_cast_b] at h_eq_floor
      rw [← h_eq_floor]
    -- Now convert Int.floor to Nat.floor
    have h_nonneg : 0 ≤ (s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ) := by
      positivity
    have h_nat_floor : (⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋₊ : ℤ) = ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋ := by
      rw [Int.natCast_floor_eq_floor h_nonneg]
    rw [h_nat_floor, ← h_int_eq]
    -- Now we have: (Int.toNat (a / b) : ℤ) = a / b
    have h_div_nonneg : 0 ≤ a / b :=
      Int.ediv_nonneg ha_nonneg (by exact_mod_cast hb_pos.le)
    rw [Int.toNat_of_nonneg h_div_nonneg]
  calc
    ((tQ p q A c : ℤ) : ℝ) = ((Nat.sqrt ((a / b).toNat) : ℤ) : ℝ) := by
      simp [tQ, hs, ha, hb]
    _ = ((Nat.sqrt ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋₊ : ℕ) : ℝ) := by
      have h_sqrt_eq : (Nat.sqrt ((a / b).toNat) : ℝ) = (Nat.sqrt ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋₊ : ℝ) := by
        have h_nat_eq : (a / b).toNat = ⌊(s : ℝ) * (2 : ℝ) ^ (2 * q) / (2 ^ p : ℝ)⌋₊ := by
          exact_mod_cast h_floor_eq
        simp [h_nat_eq]
      simp [h_sqrt_eq]
    _ = (Nat.sqrt ⌊vZ c ⬝ᵥ (mR p A *ᵥ vZ c) * (2 : ℝ) ^ (2 * q)⌋₊ : ℝ) := by
      have h_eq : vZ c ⬝ᵥ (mR p A *ᵥ vZ c) = (s : ℝ) / (2 ^ p : ℝ) := by
        unfold vZ mR
        rw [Matrix.smul_mulVec, dotProduct_smul]
        have hdot : (fun i => (c i : ℝ)) ⬝ᵥ ((A.map (fun x => (x : ℝ))).mulVec (fun i => (c i : ℝ))) = (s : ℝ) := by
          simp [Matrix.map, Matrix.mulVec, dotProduct, hs]
        rw [hdot]
        ring
      rw [h_eq]
      ring_nf

theorem newa_err (hd : 1 ≤ d) (p q : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ) (ρ eb : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hpr : (1 : ℝ) / 2 ^ p ≤ ρ ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)))
    (hs : 0 < vZ c ⬝ᵥ (mR p A *ᵥ vZ c)) (ht : 1 ≤ ((tQ p q A c : ℤ) : ℝ))
    (hb : (((2 : ℝ) ^ q / ((tQ p q A c : ℤ) : ℝ) - 1 / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) •
        (mR p A *ᵥ vZ c)) ⬝ᵥ
      (((2 : ℝ) ^ q / ((tQ p q A c : ℤ) : ℝ) - 1 / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) •
        (mR p A *ᵥ vZ c)) ≤ eb ^ 2)
    (heb0 : 0 ≤ eb) (heb : eb ≤ ρ / (64 * d)) :
    (vR p (newa p q A a c) -
        (vR p a - (1 / ((d : ℝ) + 1) / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • (mR p A *ᵥ vZ c))) ⬝ᵥ
      (vR p (newa p q A a c) -
        (vR p a - (1 / ((d : ℝ) + 1) / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • (mR p A *ᵥ vZ c))) ≤
      (3 * ρ / (128 * d * ((d : ℝ) + 1))) ^ 2 := by
  -- Abbreviations
  let u := mR p A *ᵥ vZ c
  let sr := vZ c ⬝ᵥ u
  have hsr_pos : 0 < sr := hs
  let T := (tQ p q A c : ℝ)
  have hT_pos : 0 < T := by linarith
  have hd_pos : 0 < (d : ℝ) := by
    have h : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := by linarith
  have hd1_pos : 0 < (d : ℝ) + 1 := by linarith
  have hT_pos_int : 0 < (tQ p q A c : ℤ) := by
    by_contra! hle
    have h_nonneg : (0 : ℤ) ≤ tQ p q A c := by
      unfold tQ
      exact Nat.cast_nonneg _
    have heq : tQ p q A c = (0 : ℤ) := by omega
    have hzero : ((tQ p q A c : ℤ) : ℝ) = (0 : ℝ) := by simpa [heq]
    linarith
  -- (A *ᵥ c) i = 2^p * u i (as ℝ)
  have h_A_mulVec_eq (i : Fin d) : ((A *ᵥ c) i : ℝ) = (2 : ℝ)^p * u i := by
    unfold u mR vZ
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply]
    simp [Finset.mul_sum, mul_comm, mul_left_comm, div_eq_inv_mul]
  -- Denominator in rndI is positive
  have h_denom_pos (i : Fin d) : 0 < ((d + 1 : ℤ) * tQ p q A c) := by
    have hdpos : (0 : ℤ) < d + 1 := by
      have : (1 : ℕ) ≤ d := hd
      omega
    exact mul_pos hdpos hT_pos_int
  -- rndI equals round in ℝ
  have h_rndI_eq (i : Fin d) : (rndI ((A *ᵥ c) i * (2 : ℤ)^q) ((d + 1 : ℤ) * tQ p q A c) : ℝ) =
      (round (((A *ᵥ c) i * (2 : ℤ)^q : ℝ) / (((d + 1 : ℤ) * tQ p q A c : ℤ) : ℝ)) : ℝ) := by
    have h := (fr_rnd_ediv ((A *ᵥ c) i * (2 : ℤ)^q) ((d + 1 : ℤ) * tQ p q A c) (h_denom_pos i)).1
    simpa [rndI] using congrArg (fun x : ℤ => (x : ℝ)) h
  -- Define y i = u i * 2^q / ((d+1) * T)
  let y := fun i : Fin d => u i * ((2 : ℝ) ^ q) / (((d : ℝ) + 1) * T)
  -- Key identity: vR p (newa ...) i = vR p a i - round(2^p * y i) / 2^p
  have h_vR_newa_i (i : Fin d) : vR p (newa p q A a c) i = vR p a i - ((round ((2 : ℝ)^p * y i) : ℝ) / (2 : ℝ)^p) := by
    unfold vR newa
    have h_rndI : (rndI ((A *ᵥ c) i * (2 : ℤ)^q) ((d + 1 : ℤ) * tQ p q A c) : ℝ) =
        (round ((2 : ℝ)^p * y i) : ℝ) := by
      rw [h_rndI_eq i]
      have h_arg_eq : (((A *ᵥ c) i * (2 : ℤ)^q : ℝ) / (((d + 1 : ℤ) * tQ p q A c : ℤ) : ℝ)) = (2 : ℝ)^p * y i := by
        push_cast
        rw [h_A_mulVec_eq i]
        dsimp [y]
        ring
      rw [h_arg_eq]
    push_cast
    rw [h_rndI]
    ring
  -- Define z i = y i - round(2^p * y i) / 2^p
  let z := fun i : Fin d => y i - ((round ((2 : ℝ)^p * y i) : ℝ) / (2 : ℝ)^p)
  -- Define w = (1/(d+1)) • ((1/√sr) • u - (2^q/T) • u)
  let w := (1 / ((d : ℝ) + 1)) • (((1 : ℝ) / Real.sqrt sr) • u - (((2 : ℝ)^q / T) • u))
  -- The difference is w + z
  have h_diff : vR p (newa p q A a c) - (vR p a - (1 / ((d : ℝ) + 1) / Real.sqrt sr) • u) = w + z := by
    ext i
    dsimp [w, z, y]
    rw [h_vR_newa_i i]
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    -- Goal: (vR p a i - round(2^p * y i)/2^p) - (vR p a i - (1/(d+1)/√sr) * u i) =
    --   ((1/(d+1)) * (u i/√sr - u i*2^q/T)) + (u i*2^q/((d+1)*T) - round(2^p * y i)/2^p)
    -- The round terms cancel; we need to show the rest is equal
    have h_round_arg : ((2 : ℝ)^p * (u i * ((2 : ℝ)^q) / (((d : ℝ) + 1) * T))) =
        (u i * (((d : ℝ) + 1) * T)⁻¹ * (2 : ℝ)^p * (2 : ℝ)^q) := by
      ring
    have h_round_eq : (round ((2 : ℝ)^p * (u i * ((2 : ℝ)^q) / (((d : ℝ) + 1) * T))) : ℝ) =
        (round (u i * (((d : ℝ) + 1) * T)⁻¹ * (2 : ℝ)^p * (2 : ℝ)^q) : ℝ) := by
      rw [h_round_arg]
    field_simp [hd1_pos.ne.symm, hT_pos.ne.symm, show Real.sqrt sr ≠ 0 from by positivity]
    rw [h_round_eq]
    ring
  -- Helper lemma: (-v) ⬝ᵥ (-v) = v ⬝ᵥ v
  have h_neg_sq (v : Fin d → ℝ) : (-v) ⬝ᵥ (-v) = v ⬝ᵥ v := by
    simp [dotProduct]
  -- Cauchy-Schwarz for dot product
  have h_cauchy_schwarz (f g : Fin d → ℝ) : f ⬝ᵥ g ≤ Real.sqrt (f ⬝ᵥ f) * Real.sqrt (g ⬝ᵥ g) := by
    calc
      f ⬝ᵥ g = ∑ i : Fin d, f i * g i := rfl
      _ ≤ Real.sqrt (∑ i : Fin d, f i ^ 2) * Real.sqrt (∑ i : Fin d, g i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
      _ = Real.sqrt (f ⬝ᵥ f) * Real.sqrt (g ⬝ᵥ g) := by
        simp [dotProduct, sq]
  -- (w + z) ⬝ᵥ (w + z) ≤ (√(w⬝ᵥw) + √(z⬝ᵥz))^2
  have h_cauchy_sum : (w + z) ⬝ᵥ (w + z) ≤ (Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z)) ^ 2 := by
    have h_expand : (w + z) ⬝ᵥ (w + z) = w ⬝ᵥ w + z ⬝ᵥ z + 2 * (w ⬝ᵥ z) := by
      simp [dotProduct, Pi.add_apply]
      calc
        ∑ i : Fin d, (w i + z i) * (w i + z i) = ∑ i : Fin d, (w i * w i + 2 * (w i * z i) + z i * z i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        _ = (∑ i : Fin d, w i * w i) + 2 * (∑ i : Fin d, w i * z i) + (∑ i : Fin d, z i * z i) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (∑ i : Fin d, w i * w i) + (∑ i : Fin d, z i * z i) + 2 * (∑ i : Fin d, w i * z i) := by ring
    rw [h_expand]
    have h_nonneg_ww : 0 ≤ w ⬝ᵥ w := by
      rw [dotProduct]
      refine Finset.sum_nonneg fun i _ => ?_
      nlinarith [sq_nonneg (w i)]
    have h_nonneg_zz : 0 ≤ z ⬝ᵥ z := by
      rw [dotProduct]
      refine Finset.sum_nonneg fun i _ => ?_
      nlinarith [sq_nonneg (z i)]
    have h_eq_sq : w ⬝ᵥ w + z ⬝ᵥ z + 2 * (Real.sqrt (w ⬝ᵥ w) * Real.sqrt (z ⬝ᵥ z)) =
        (Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z)) ^ 2 := by
      calc
        w ⬝ᵥ w + z ⬝ᵥ z + 2 * (Real.sqrt (w ⬝ᵥ w) * Real.sqrt (z ⬝ᵥ z))
            = (Real.sqrt (w ⬝ᵥ w)) ^ 2 + (Real.sqrt (z ⬝ᵥ z)) ^ 2 + 2 * (Real.sqrt (w ⬝ᵥ w) * Real.sqrt (z ⬝ᵥ z)) := by
          simp [Real.sq_sqrt h_nonneg_ww, Real.sq_sqrt h_nonneg_zz]
        _ = (Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z)) ^ 2 := by ring
    calc
      w ⬝ᵥ w + z ⬝ᵥ z + 2 * (w ⬝ᵥ z)
          ≤ w ⬝ᵥ w + z ⬝ᵥ z + 2 * (Real.sqrt (w ⬝ᵥ w) * Real.sqrt (z ⬝ᵥ z)) := by
        nlinarith [h_cauchy_schwarz w z]
      _ = (Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z)) ^ 2 := h_eq_sq
  -- w ⬝ᵥ w ≤ eb^2 / (d+1)^2
  have h_w_sq : w ⬝ᵥ w ≤ eb ^ 2 / (((d : ℝ) + 1) ^ 2) := by
    let s := ((1 : ℝ) / Real.sqrt sr) • u - (((2 : ℝ)^q / T) • u)
    have hs_eq : s = -(((2 : ℝ)^q / T - 1 / Real.sqrt sr) • u) := by
      ext i
      dsimp [s]
      ring
    have h_s_sq : s ⬝ᵥ s ≤ eb ^ 2 := by
      rw [hs_eq, h_neg_sq]
      simpa [sr, T] using hb
    have h_w_sq_eq : w ⬝ᵥ w = ((1 / ((d : ℝ) + 1)) ^ 2) * (s ⬝ᵥ s) := by
      calc
        w ⬝ᵥ w = ((1 / ((d : ℝ) + 1)) • s) ⬝ᵥ ((1 / ((d : ℝ) + 1)) • s) := by
          dsimp [w, s]
        _ = ((1 / ((d : ℝ) + 1)) ^ 2) * (s ⬝ᵥ s) := by
          simp [dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp [hd1_pos.ne.symm]
    rw [h_w_sq_eq]
    have h_pos : 0 ≤ ((1 / ((d : ℝ) + 1)) ^ 2) := by positivity
    calc
      ((1 / ((d : ℝ) + 1)) ^ 2) * (s ⬝ᵥ s) ≤ ((1 / ((d : ℝ) + 1)) ^ 2) * (eb ^ 2) := by
        nlinarith
      _ = eb ^ 2 / (((d : ℝ) + 1) ^ 2) := by
        field_simp [hd1_pos.ne.symm]
  -- z ⬝ᵥ z ≤ d * (1/2^(p+1))^2
  have h_z_sq : z ⬝ᵥ z ≤ (d : ℝ) * (1 / (2 : ℝ)^(p+1)) ^ 2 := by
    have hz_eq : z = -(((fun j => (round ((2 : ℝ)^p * y j) : ℝ) / (2 : ℝ)^p) - y)) := by
      ext i
      dsimp [z]
      ring
    rw [hz_eq, h_neg_sq]
    exact fr_rnd_vec y p
  -- √(w⬝ᵥw) ≤ eb/(d+1)
  have h_sqrt_w : Real.sqrt (w ⬝ᵥ w) ≤ eb / ((d : ℝ) + 1) := by
    have h_nonneg_ww : 0 ≤ w ⬝ᵥ w := by
      rw [dotProduct]
      refine Finset.sum_nonneg fun i _ => ?_
      nlinarith [sq_nonneg (w i)]
    have h_sqrt_le : Real.sqrt (w ⬝ᵥ w) ≤ Real.sqrt (eb ^ 2 / (((d : ℝ) + 1) ^ 2)) :=
      Real.sqrt_le_sqrt h_w_sq
    have h_sqrt_eb : Real.sqrt (eb ^ 2 / (((d : ℝ) + 1) ^ 2)) = eb / ((d : ℝ) + 1) := by
      rw [Real.sqrt_div (by positivity) _, Real.sqrt_sq heb0, Real.sqrt_sq (by linarith : 0 ≤ (d : ℝ) + 1)]
    rw [h_sqrt_eb] at h_sqrt_le
    exact h_sqrt_le
  -- √(z⬝ᵥz) ≤ √d / 2^(p+1)
  have h_sqrt_z : Real.sqrt (z ⬝ᵥ z) ≤ Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) := by
    have h_nonneg_zz : 0 ≤ z ⬝ᵥ z := by
      rw [dotProduct]
      refine Finset.sum_nonneg fun i _ => ?_
      nlinarith [sq_nonneg (z i)]
    have h_sqrt_le : Real.sqrt (z ⬝ᵥ z) ≤ Real.sqrt ((d : ℝ) * (1 / (2 : ℝ)^(p+1)) ^ 2) :=
      Real.sqrt_le_sqrt h_z_sq
    have h_sqrt_d : Real.sqrt ((d : ℝ) * (1 / (2 : ℝ)^(p+1)) ^ 2) = Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) := by
      rw [Real.sqrt_mul hd_nonneg, Real.sqrt_sq (by positivity : 0 ≤ 1 / (2 : ℝ)^(p+1))]
      ring
    rw [h_sqrt_d] at h_sqrt_le
    exact h_sqrt_le
  -- √d ≤ d for d ≥ 1
  have h_sqrt_d_le_d : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    have h_d_le_d_sq : (d : ℝ) ≤ (d : ℝ)^2 := by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
    calc
      Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ)^2) := Real.sqrt_le_sqrt h_d_le_d_sq
      _ = (d : ℝ) := Real.sqrt_sq hd_nonneg
  -- Combine the bounds
  have h_sum : eb / ((d : ℝ) + 1) + Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) ≤ 3 * ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
    have h_rho_sq_le_rho : ρ ^ 2 ≤ ρ := by
      nlinarith
    have h1 : eb / ((d : ℝ) + 1) ≤ ρ / (64 * (d : ℝ) * ((d : ℝ) + 1)) := by
      calc
        eb / ((d : ℝ) + 1) ≤ (ρ / (64 * (d : ℝ))) / ((d : ℝ) + 1) :=
          div_le_div_of_nonneg_right heb (by linarith)
        _ = ρ / (64 * (d : ℝ) * ((d : ℝ) + 1)) := by
          field_simp [hd_pos.ne.symm, show (d : ℝ) + 1 ≠ 0 from by linarith]
    have h2 : Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) ≤ ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
      have h_pow_pos : 0 < (2 : ℝ)^(p+1) := by positivity
      calc
        Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) ≤ (d : ℝ) / (2 : ℝ)^(p+1) :=
          div_le_div_of_nonneg_right h_sqrt_d_le_d (by positivity)
        _ = (d : ℝ) * (1 / (2 : ℝ)^(p+1)) := by ring
        _ = (d : ℝ) * ((1 / (2 : ℝ)) * (1 / (2 : ℝ)^p)) := by ring
        _ = (d : ℝ) * (1 / (2 : ℝ)) * (1 / (2 : ℝ)^p) := by ring
        _ ≤ (d : ℝ) * (1 / (2 : ℝ)) * (ρ ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1))) := by
          have h_nonneg : 0 ≤ (d : ℝ) * (1 / (2 : ℝ)) := by positivity
          have h_mul := mul_le_mul_of_nonneg_left hpr h_nonneg
          simpa [mul_assoc] using h_mul
        _ = ρ ^ 2 * (d : ℝ) / (128 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)) := by
          field_simp [hd_pos.ne.symm, show (d : ℝ) + 1 ≠ 0 from by linarith]
          ring
        _ = ρ ^ 2 / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
          field_simp [hd_pos.ne.symm, show (d : ℝ) + 1 ≠ 0 from by linarith]
        _ ≤ ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) :=
          div_le_div_of_nonneg_right h_rho_sq_le_rho (by positivity)
    have h_sum' : ρ / (64 * (d : ℝ) * ((d : ℝ) + 1)) + ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) = 3 * ρ / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
      field_simp [hd_pos.ne.symm, show (d : ℝ) + 1 ≠ 0 from by linarith]
      ring
    linarith
  -- Final assembly
  have h_nonneg_sqrt_w : 0 ≤ Real.sqrt (w ⬝ᵥ w) := Real.sqrt_nonneg _
  have h_nonneg_sqrt_z : 0 ≤ Real.sqrt (z ⬝ᵥ z) := Real.sqrt_nonneg _
  calc
    (vR p (newa p q A a c) - (vR p a - (1 / ((d : ℝ) + 1) / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • (mR p A *ᵥ vZ c))) ⬝ᵥ
      (vR p (newa p q A a c) - (vR p a - (1 / ((d : ℝ) + 1) / Real.sqrt (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • (mR p A *ᵥ vZ c)))
        = (w + z) ⬝ᵥ (w + z) := by rw [h_diff]
    _ ≤ (Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z)) ^ 2 := h_cauchy_sum
    _ ≤ (eb / ((d : ℝ) + 1) + Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1)) ^ 2 := by
      have h_sum_sqrt : Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z) ≤ eb / ((d : ℝ) + 1) + Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) :=
        add_le_add h_sqrt_w h_sqrt_z
      have h_nonneg : 0 ≤ Real.sqrt (w ⬝ᵥ w) + Real.sqrt (z ⬝ᵥ z) := by positivity
      have h_nonneg' : 0 ≤ eb / ((d : ℝ) + 1) + Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) := by positivity
      exact (sq_le_sq₀ h_nonneg h_nonneg').mpr h_sum_sqrt
    _ ≤ (3 * ρ / (128 * (d : ℝ) * ((d : ℝ) + 1))) ^ 2 := by
      have h_nonneg_sum : 0 ≤ eb / ((d : ℝ) + 1) + Real.sqrt (d : ℝ) / (2 : ℝ)^(p+1) := by positivity
      exact (sq_le_sq₀ h_nonneg_sum (by positivity)).mpr h_sum

theorem newA_entry (hd : 2 ≤ d) (p : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ)
    (hs : 0 < c ⬝ᵥ (A *ᵥ c)) (i k : Fin d) :
    |mR p (newA A c) i k - (lamR d ^ 2 • (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • (mR p A -
      (2 / ((d : ℝ) + 1) / (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • vecMulVec (mR p A *ᵥ vZ c) (mR p A *ᵥ vZ c)))) i k| ≤
      1 / 2 ^ (p + 1) := by
  -- define abbreviations (using `set` so they are hypotheses, unfolded by `simpa`)
  have hs_pos : 0 < c ⬝ᵥ (A *ᵥ c) := hs
  have hs_ne_zero : c ⬝ᵥ (A *ᵥ c) ≠ 0 := by linarith
  set s : ℤ := c ⬝ᵥ (A *ᵥ c) with hs_def
  set v : Fin d → ℤ := A *ᵥ c with hv_def
  set u_val : ℤ := kapN d * ((d + 1) * s * A i k - 2 * v i * v k) with hu_def
  set v_val : ℤ := kapD d * (d + 1) * s with hv_val_def
  have hv_val_pos : 0 < v_val := by
    have hd_int : 1 ≤ (d : ℤ) := by exact_mod_cast (show 1 ≤ d from by omega)
    have hkapD_pos : 0 < kapD d := by
      unfold kapD
      have hd1 : 1 ≤ (d : ℤ) - 1 := by
        have : 2 ≤ (d : ℤ) := by exact_mod_cast hd
        omega
      positivity
    have hd1_pos : 0 < (d : ℤ) + 1 := by omega
    exact mul_pos (mul_pos hkapD_pos hd1_pos) hs_pos
  have h_rnd := fr_rnd_ediv u_val v_val hv_val_pos
  rcases h_rnd with ⟨h_eq_int, h_bound⟩
  -- h_bound : |(((2 * u_val + v_val) / (2 * v_val) : ℤ) : ℝ) - (u_val : ℝ) / v_val| ≤ 1 / 2
  have h_bound' : |((newA A c i k : ℤ) : ℝ) - (u_val : ℝ) / v_val| ≤ 1 / 2 := by
    -- newA A c i k = rndI u_val v_val = (2*u_val + v_val) / (2*v_val)  (integer division in ℤ)
    simpa [newA, u_val, v_val, rndI, s, v] using h_bound
  have hmR_eq : mR p (newA A c) i k = (((newA A c i k : ℤ) : ℝ) / (2 ^ p : ℝ)) := by
    simp [mR, Matrix.map_apply]; field_simp
  let lam2 : ℝ := ((2 * (d : ℝ) + 1) ^ 2 / (4 * (d : ℝ) * ((d : ℝ) + 1)))
  have h_lamR_sq : lamR d ^ 2 = lam2 := by
    rw [AdversarialBco.Bit.ApQ.lamR]
    rw [Real.sq_sqrt]
    positivity
  -- compute mR p A *ᵥ vZ c = fun j => (v j : ℝ) / 2^p
  have h_mulVec_eq : mR p A *ᵥ vZ c = fun j => (v j : ℝ) / (2 ^ p : ℝ) := by
    ext j
    calc
      (mR p A *ᵥ vZ c) j = (mR p A).row j ⬝ᵥ vZ c := by rw [Matrix.mulVec_apply]
      _ = ∑ k, (mR p A) j k * (vZ c) k := rfl
      _ = ∑ k, ((A j k : ℝ) / (2 ^ p : ℝ)) * (c k : ℝ) := by
        simp [mR, Matrix.map_apply, vZ, div_eq_mul_inv, mul_comm]
      _ = ∑ k, ((A j k : ℝ) * (c k : ℝ)) / (2 ^ p : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      _ = (∑ k, (A j k : ℝ) * (c k : ℝ)) / (2 ^ p : ℝ) := by rw [Finset.sum_div]
      _ = (v j : ℝ) / (2 ^ p : ℝ) := by simp [v, Matrix.mulVec_apply, dotProduct]
  have h_sr_eq : vZ c ⬝ᵥ (mR p A *ᵥ vZ c) = (s : ℝ) / (2 ^ p : ℝ) := by
    rw [h_mulVec_eq]
    calc
      vZ c ⬝ᵥ (fun j => (v j : ℝ) / (2 ^ p : ℝ)) = ∑ j, (vZ c) j * ((v j : ℝ) / (2 ^ p : ℝ)) := rfl
      _ = ∑ j, (c j : ℝ) * ((v j : ℝ) / (2 ^ p : ℝ)) := by simp [vZ]
      _ = ∑ j, ((c j : ℝ) * (v j : ℝ)) / (2 ^ p : ℝ) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = (∑ j, (c j : ℝ) * (v j : ℝ)) / (2 ^ p : ℝ) := by rw [Finset.sum_div]
      _ = ((c ⬝ᵥ v : ℤ) : ℝ) / (2 ^ p : ℝ) := by simp [v, dotProduct]
      _ = (s : ℝ) / (2 ^ p : ℝ) := by simp [s, v]
  -- the main algebraic identity: target expression = ((u_val : ℝ) / v_val) / 2^p
  have h_target_eq : (lamR d ^ 2 • (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) • (mR p A -
      (2 / ((d : ℝ) + 1) / (vZ c ⬝ᵥ (mR p A *ᵥ vZ c))) • vecMulVec (mR p A *ᵥ vZ c) (mR p A *ᵥ vZ c)))) i k =
      ((u_val : ℝ) / v_val) / (2 ^ p : ℝ) := by
    rw [h_sr_eq, h_lamR_sq]
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    -- goal: lam2 * ((d^2/(d^2-1)) * (mR p A i k - (2/(d+1)/((s)/2^p)) * ((mR p A *ᵥ vZ c) i * (mR p A *ᵥ vZ c) k)))
    --       = ((u_val : ℝ) / v_val) / 2^p
    have h_mR_ik : mR p A i k = (A i k : ℝ) / (2 ^ p : ℝ) := by
      simp [mR, Matrix.map_apply, mul_comm, div_eq_mul_inv]
    have h_mulVec_i : (mR p A *ᵥ vZ c) i = (v i : ℝ) / (2 ^ p : ℝ) := by
      rw [h_mulVec_eq]
    have h_mulVec_k : (mR p A *ᵥ vZ c) k = (v k : ℝ) / (2 ^ p : ℝ) := by
      rw [h_mulVec_eq]
    have h_mat := fr_mat_step d p hd (A i k : ℝ) (v i : ℝ) (v k : ℝ) (s : ℝ) (by exact_mod_cast hs_ne_zero)
    -- h_mat: LHS = RHS where LHS = (u_val : ℝ) / v_val (after rewriting)
    have h_uval_div_vval_eq : (u_val : ℝ) / v_val =
        (d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 * (((d : ℝ) + 1) * (s : ℝ) * (A i k : ℝ) - 2 * (v i : ℝ) * (v k : ℝ)) /
          (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1) * (((d : ℝ) + 1) * (s : ℝ))) := by
      dsimp [u_val, v_val, kapN, kapD]
      push_cast
      ring
    -- (u_val)/v_val = RHS of h_mat
    have h_uval_eq_RHS : (u_val : ℝ) / v_val =
        (2 ^ p : ℝ) * lam2 * (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
          ((A i k : ℝ) / (2 ^ p : ℝ) - 2 / ((d : ℝ) + 1) * ((v i : ℝ) / (2 ^ p : ℝ) * ((v k : ℝ) / (2 ^ p : ℝ))) / ((s : ℝ) / (2 ^ p : ℝ)))) := by
      rw [h_uval_div_vval_eq, h_mat]
    -- Now compute ((u_val : ℝ) / v_val) / 2^p = target
    calc
      lam2 * (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
            ((mR p A i k) - (2 / ((d : ℝ) + 1) / ((s : ℝ) / (2 ^ p : ℝ))) * ((mR p A *ᵥ vZ c) i * (mR p A *ᵥ vZ c) k))) =
          lam2 * (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
            ((A i k : ℝ) / (2 ^ p : ℝ) - (2 / ((d : ℝ) + 1) / ((s : ℝ) / (2 ^ p : ℝ))) * ((v i : ℝ) / (2 ^ p : ℝ) * ((v k : ℝ) / (2 ^ p : ℝ))))) := by
        simp [h_mR_ik, h_mulVec_i, h_mulVec_k]
      _ = lam2 * (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
            ((A i k : ℝ) / (2 ^ p : ℝ) - 2 / ((d : ℝ) + 1) * ((v i : ℝ) / (2 ^ p : ℝ) * ((v k : ℝ) / (2 ^ p : ℝ))) / ((s : ℝ) / (2 ^ p : ℝ)))) := by ring
      _ = ((2 ^ p : ℝ) * lam2 * (((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
            ((A i k : ℝ) / (2 ^ p : ℝ) - 2 / ((d : ℝ) + 1) * ((v i : ℝ) / (2 ^ p : ℝ) * ((v k : ℝ) / (2 ^ p : ℝ))) / ((s : ℝ) / (2 ^ p : ℝ))))) / (2 ^ p : ℝ) := by
        field_simp [show (2 ^ p : ℝ) ≠ 0 from by positivity]
      _ = ((u_val : ℝ) / v_val) / (2 ^ p : ℝ) := by rw [← h_uval_eq_RHS]
  rw [hmR_eq, h_target_eq]
  -- goal: |((newA A c i k : ℝ) / 2^p) - ((u_val : ℝ) / v_val) / 2^p| ≤ 1 / 2^(p+1)
  rw [div_sub_div_same]
  -- goal: |((newA A c i k : ℝ) - (u_val : ℝ) / v_val) / 2^p| ≤ 1 / 2^(p+1)
  rw [abs_div, abs_of_pos (by positivity : 0 < (2 ^ p : ℝ))]
  -- goal: |(newA A c i k : ℝ) - (u_val : ℝ) / v_val| / 2^p ≤ 1 / 2^(p+1)
  have hpos : 0 ≤ (2 ^ p : ℝ) := by positivity
  calc
    |((newA A c i k : ℤ) : ℝ) - (u_val : ℝ) / v_val| / (2 ^ p : ℝ) ≤ (1 / 2) / (2 ^ p : ℝ) := by
      exact div_le_div_of_nonneg_right h_bound' hpos
    _ = 1 / (2 ^ (p + 1) : ℝ) := by ring

theorem quad_of_entry (E : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (h : ∀ i k, |E i k| ≤ η) (v : Fin d → ℝ) :
    |v ⬝ᵥ (E *ᵥ v)| ≤ d * η * (v ⬝ᵥ v) := by
  by_cases hd0 : d = 0
  · subst hd0
    simp
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have hη_nonneg : 0 ≤ η := by
    have hne : Nonempty (Fin d) := (Fin.pos_iff_nonempty.mp hd_pos)
    obtain ⟨i⟩ := hne
    have := h i i
    have hpos : 0 ≤ |E i i| := abs_nonneg _
    linarith
  have hsum : |v ⬝ᵥ (E *ᵥ v)| ≤ η * (∑ i : Fin d, |v i|) ^ 2 := by
    calc
      |v ⬝ᵥ (E *ᵥ v)|
          = |∑ i, v i * (E *ᵥ v) i| := by rfl
      _ ≤ ∑ i, |v i * (E *ᵥ v) i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |v i| * |(E *ᵥ v) i| := by
        simp_rw [abs_mul]
      _ ≤ ∑ i, |v i| * (∑ j, |E i j| * |v j|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hbound : |(E *ᵥ v) i| ≤ ∑ j, |E i j| * |v j| := by
          calc
            |(E *ᵥ v) i| = |∑ j, E i j * v j| := by simp [Matrix.mulVec_apply_eq_sum]
            _ ≤ ∑ j, |E i j * v j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j, |E i j| * |v j| := by simp_rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ ≤ ∑ i, |v i| * (∑ j, η * |v j|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (abs_nonneg _)
        have hE := h i j
        -- hE : |E i j| ≤ η, need |E i j| * |v j| ≤ η * |v j|
        exact mul_le_mul_of_nonneg_right hE (abs_nonneg _)
      _ = (∑ i, |v i|) * (∑ j, η * |v j|) := by
        simp [Finset.sum_mul]
      _ = (∑ i, |v i|) * (η * (∑ j, |v j|)) := by
        simp [Finset.mul_sum]
      _ = η * (∑ i, |v i|) * (∑ j, |v j|) := by
        rw [← mul_assoc, mul_comm (∑ i, |v i|) η]
      _ = η * (∑ i, |v i|) ^ 2 := by
        rw [sq, mul_assoc]
  have hcs : (∑ i : Fin d, |v i|) ^ 2 ≤ (d : ℝ) * (v ⬝ᵥ v) := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin d => |v i|)
    have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
    -- this gives (∑ i, |v i|)^2 ≤ (Finset.univ.card : ℝ) * ∑ i, |v i|^2
    -- Finset.univ.card = d
    have hsumsq : (v ⬝ᵥ v) = ∑ i : Fin d, (v i) ^ 2 := by
      simp [dotProduct, sq]
    simpa [hcard, hsumsq] using this
  calc
    |v ⬝ᵥ (E *ᵥ v)| ≤ η * (∑ i : Fin d, |v i|) ^ 2 := hsum
    _ ≤ η * ((d : ℝ) * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left hcs hη_nonneg
    _ = d * η * (v ⬝ᵥ v) := by ring

theorem newA_symm (A : Matrix (Fin d) (Fin d) ℤ) (c : Fin d → ℤ) (hA : Aᵀ = A) : (newA A c)ᵀ = newA A c := by
  ext i k
  simp only [Matrix.transpose_apply, newA]
  have hAik : A k i = A i k := by
    calc
      A k i = (Aᵀ) i k := by simp
      _ = A i k := by rw [hA]
  have hnum : kapN d * ((↑d + 1) * c ⬝ᵥ A *ᵥ c * A i k - 2 * (A *ᵥ c) k * (A *ᵥ c) i) =
             kapN d * ((↑d + 1) * c ⬝ᵥ A *ᵥ c * A i k - 2 * (A *ᵥ c) i * (A *ᵥ c) k) := by
    ring
  rw [hAik, hnum]

theorem mR_symm (p : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (hA : Aᵀ = A) : (mR p A)ᵀ = mR p A := by
  calc
    (mR p A)ᵀ = (((1 : ℝ) / 2 ^ p) • A.map ((↑) : ℤ → ℝ))ᵀ := rfl
    _ = ((1 : ℝ) / 2 ^ p) • (A.map ((↑) : ℤ → ℝ))ᵀ := by rw [Matrix.transpose_smul]
    _ = ((1 : ℝ) / 2 ^ p) • (Aᵀ.map ((↑) : ℤ → ℝ)) := by rw [Matrix.transpose_map]
    _ = ((1 : ℝ) / 2 ^ p) • (A.map ((↑) : ℤ → ℝ)) := by rw [hA]
    _ = mR p A := rfl

theorem DA_le (hd : 1 ≤ d) (p : ℕ) (ρ : ℝ) (hpr : (1 : ℝ) / 2 ^ p ≤ ρ ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1))) :
    (d : ℝ) * (1 / 2 ^ (p + 1)) ≤ ρ ^ 2 / (128 * d * ((d : ℝ) + 1)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have h : (0 : ℕ) < d := by omega
    exact_mod_cast h
  have hd_ne_zero : (d : ℝ) ≠ 0 := by linarith
  have h_nonneg_half_d : (0 : ℝ) ≤ (d : ℝ) / 2 := by
    have h : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    nlinarith
  calc
    (d : ℝ) * (1 / 2 ^ (p + 1)) = ((d : ℝ) / 2) * ((1 : ℝ) / 2 ^ p) := by
      field_simp
      ring
    _ ≤ ((d : ℝ) / 2) * (ρ ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpr h_nonneg_half_d
    _ = ρ ^ 2 / (128 * d * ((d : ℝ) + 1)) := by
      field_simp [hd_ne_zero]
      ring

theorem cap_mat (p : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (Λ : ℝ) (capA : ℤ) (h : ∀ i k, |mR p A i k| ≤ Λ)
    (hc : (2 : ℝ) ^ p * Λ ≤ capA) (i k : Fin d) : |A i k| ≤ capA := by
  have hmk : |mR p A i k| ≤ Λ := h i k
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (by norm_num) p
  have hmR_eq : mR p A i k = ((A i k : ℝ) / (2 : ℝ) ^ p) := by
    simp [mR, Matrix.smul_apply, Matrix.map_apply, div_eq_mul_inv, mul_comm]
  rw [hmR_eq] at hmk
  rw [abs_div, abs_of_pos hpos] at hmk
  have h_mul : |(A i k : ℝ)| ≤ (2 : ℝ) ^ p * Λ := by
    calc
      |(A i k : ℝ)| = (|(A i k : ℝ)| / (2 : ℝ) ^ p) * (2 : ℝ) ^ p := by field_simp [ne_of_gt hpos]
      _ ≤ Λ * (2 : ℝ) ^ p := mul_le_mul_of_nonneg_right hmk (by positivity)
      _ = (2 : ℝ) ^ p * Λ := mul_comm _ _
  have h_final : |(A i k : ℝ)| ≤ (capA : ℝ) := by linarith
  exact_mod_cast h_final

theorem cap_vec (p : ℕ) (a : Fin d → ℤ) (z : Fin d → ℝ) (Λ : ℝ) (capa : ℤ) (hΛ : 0 ≤ Λ)
    (h : (z - vR p a) ⬝ᵥ (z - vR p a) ≤ Λ) (hc : ∀ i, (2 : ℝ) ^ p * (|z i| + Real.sqrt Λ) ≤ capa) (i : Fin d) :
    |a i| ≤ capa := by
  have h_sq_term : ((z - vR p a) i) ^ 2 ≤ (z - vR p a) ⬝ᵥ (z - vR p a) := by
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ ((z - vR p a) j) ^ 2 := by
      intro j hj
      apply pow_two_nonneg
    calc
      ((z - vR p a) i) ^ 2 ≤ ∑ j ∈ (Finset.univ : Finset (Fin d)), ((z - vR p a) j) ^ 2 :=
        Finset.single_le_sum h_nonneg (Finset.mem_univ i)
      _ = (z - vR p a) ⬝ᵥ (z - vR p a) := by simp [dotProduct, sq]
  have h_sq_bound : ((z - vR p a) i) ^ 2 ≤ Λ :=
    le_trans h_sq_term h
  have h_abs_diff : |(z - vR p a) i| ≤ Real.sqrt Λ :=
    Real.abs_le_sqrt h_sq_bound
  have h_abs_vR : |vR p a i| ≤ |z i| + |(z - vR p a) i| := by
    calc
      |vR p a i| = |z i - (z i - vR p a i)| := by ring_nf
      _ ≤ |z i| + |z i - vR p a i| := abs_sub _ _
      _ = |z i| + |(z - vR p a) i| := rfl
  have h_abs_vR' : |vR p a i| ≤ |z i| + Real.sqrt Λ :=
    le_trans h_abs_vR (add_le_add_right h_abs_diff (|z i|))
  have hp_pos : 0 < (2 : ℝ) ^ p := by positivity
  have h_abs_a_real : |(a i : ℝ)| ≤ (2 : ℝ) ^ p * (|z i| + Real.sqrt Λ) := by
    have h_eq : (2 : ℝ) ^ p * |vR p a i| = |(a i : ℝ)| := by
      rw [vR]
      calc
        (2 : ℝ) ^ p * |(a i : ℝ) / ((2 : ℝ) ^ p)| = (2 : ℝ) ^ p * (|(a i : ℝ)| / |(2 : ℝ) ^ p|) := by rw [abs_div]
        _ = (2 : ℝ) ^ p * (|(a i : ℝ)| / ((2 : ℝ) ^ p)) := by rw [abs_of_pos hp_pos]
        _ = |(a i : ℝ)| := by field_simp [ne_of_gt hp_pos]
    calc
      |(a i : ℝ)| = (2 : ℝ) ^ p * |vR p a i| := by rw [h_eq]
      _ ≤ (2 : ℝ) ^ p * (|z i| + Real.sqrt Λ) := mul_le_mul_of_nonneg_left h_abs_vR' (by positivity)
  have h_abs_a_capa_real : |(a i : ℝ)| ≤ (capa : ℝ) :=
    le_trans h_abs_a_real (hc i)
  have h_cast_abs : ((|a i| : ℤ) : ℝ) = |(a i : ℝ)| := Int.cast_abs
  have h_goal_real : ((|a i| : ℤ) : ℝ) ≤ (capa : ℝ) := by
    rw [h_cast_abs]
    exact h_abs_a_capa_real
  exact (Int.cast_le (R := ℝ)).mp h_goal_real

theorem one_le_gam (hd : 2 ≤ d) : 1 ≤ gam d := by
  unfold gam
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden1 : 0 < 4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1) := by
    nlinarith
  have hfirst : 1 ≤ (d : ℝ) * (2 * (d : ℝ) + 1) ^ 2 / (4 * ((d : ℝ) + 1) ^ 2 * ((d : ℝ) - 1)) := by
    rw [one_le_div hden1]
    nlinarith
  have hsecond : 0 < 1 / (128 * (d : ℝ) * ((d : ℝ) + 1)) := by
    refine div_pos (by norm_num) ?_
    nlinarith
  nlinarith

/-! ## The step -/

/-- One step of ELL-R and ELL-F keeps the invariant (proof of (b), (i) to (iv)). -/
theorem ellUpd_step (hd : 2 ≤ d) (p q j : ℕ) (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ)
    (z0 : Fin d → ℝ) (L Λ : ℝ) (hAs : Aᵀ = A) (hA : (mR p A).PosDef)
    (hball : ∀ x, InB z0 (1 / 2 ^ j) x → InE (mR p A) (vR p a) x)
    (hL : ∀ v, v ⬝ᵥ (mR p A *ᵥ v) ≤ L * (v ⬝ᵥ v)) (hLΛ : gam d * L ≤ Λ)
    (hc : c ≠ 0) (hcut : ∀ x, InB z0 (1 / 2 ^ j) x → vZ c ⬝ᵥ (x - vR p a) ≤ 0)
    (hp : 2 * j ≤ p) (hpr : (1 : ℝ) / 2 ^ p ≤ (1 / 2 ^ j) ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)))
    (hq : 4 / (1 / 2 ^ j) ≤ (2 : ℝ) ^ q) (hq2 : 4 * Real.sqrt Λ / (1 / 2 ^ j * 2 ^ q) ≤ 1 / 2 ^ j / (64 * d))
    (hcapA : (2 : ℝ) ^ p * Λ ≤ capA) (hcapa : ∀ i, (2 : ℝ) ^ p * (|z0 i| + Real.sqrt Λ) ≤ capa) :
    ∃ A' a', ellUpd p q j capA capa A a c = some (A', a') ∧ A'ᵀ = A' ∧ (mR p A').PosDef ∧
      (∀ x, InB z0 (1 / 2 ^ j) x → InE (mR p A') (vR p a') x) ∧
      (∀ v, v ⬝ᵥ (mR p A' *ᵥ v) ≤ gam d * L * (v ⬝ᵥ v)) ∧
      (mR p A').det ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) * (mR p A).det := by
  set ρ : ℝ := 1 / 2 ^ j with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set Ar := mR p A with hArdef
  set ar := vR p a with hardef
  set cr := vZ c with hcrdef
  -- Lemma BALL on `E(A, a)`
  have hsym := pb_ball_sym Ar hA ar z0 ρ hball
  have hquad : ∀ v, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Ar *ᵥ v) := pb_ball_quad Ar hA ar ρ hρ hsym
  have hcr0 : cr ≠ 0 := vZ_ne c hc
  have hcc : 1 ≤ cr ⬝ᵥ cr := vZ_one_le c hc
  set u := Ar *ᵥ cr with hudef
  set sr := cr ⬝ᵥ u with hsrdef
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hsr : 0 < sr := by
    have := hquad cr
    have : ρ ^ 2 ≤ ρ ^ 2 * (cr ⬝ᵥ cr) := le_mul_of_one_le_right hρ2.le hcc
    linarith
  have hLρ : ρ ^ 2 ≤ L := by
    have h1 := hquad cr
    have h2 := hL cr
    have h3 : ρ ^ 2 * (cr ⬝ᵥ cr) ≤ L * (cr ⬝ᵥ cr) := le_trans h1 h2
    exact le_of_mul_le_mul_right h3 (by linarith)
  -- (K1) passes
  have hK1 := k1_pass p j A c hp (hquad cr)
  have hsZ : 0 < c ⬝ᵥ (A *ᵥ c) := by
    have h := dot_cast p A c
    have : (0 : ℝ) < ((c ⬝ᵥ (A *ᵥ c) : ℤ) : ℝ) := by rw [h]; positivity
    exact_mod_cast this
  -- Lemma SQ
  obtain ⟨ht1, hbt⟩ := pb_sq_main Ar hA ρ L hρ hquad hL c hc q hq
  have ht : ((tQ p q A c : ℤ) : ℝ) = ((Nat.sqrt ⌊sr * 2 ^ (2 * q)⌋₊ : ℕ) : ℝ) := tQ_eq p q A c hsr.le
  have hg1 : 1 ≤ gam d := one_le_gam hd
  have hLΛ0 : 0 ≤ Λ := le_trans (mul_nonneg (by linarith) (le_trans hρ2.le hLρ)) hLΛ
  -- the exact cut of Lemma CC
  set σ : ℝ := (d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1) with hσdef
  have hσ0 : 0 ≤ σ := by
    rw [hσdef]; apply div_nonneg (by positivity); nlinarith
  set As := σ • (Ar - (2 / ((d : ℝ) + 1) / sr) • vecMulVec u u) with hAsdef
  set as := ar - (1 / ((d : ℝ) + 1) / Real.sqrt sr) • u with hasdef
  have hAsPD : As.PosDef := pb_cc_posDef Ar hA cr hcr0 d hd
  have hinclS : ∀ x, InB z0 ρ x → InE As as x := fun x hx =>
    pb_cc_incl Ar hA cr ar x hcr0 d hd (hball x hx) (hcut x hx)
  have hsymS := pb_ball_sym As hAsPD as z0 ρ hinclS
  have hquadS : ∀ v, ρ ^ 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ (As *ᵥ v) := pb_ball_quad As hAsPD as ρ hρ hsymS
  -- the rounded step
  set A' := newA A c with hA'def
  set a' := newa p q A a c with ha'def
  set At := mR p A' with hAtdef
  set at' := vR p a' with hatdef
  set DA : ℝ := (d : ℝ) * (1 / 2 ^ (p + 1)) with hDAdef
  have hDA0 : 0 ≤ DA := by positivity
  have hDA : DA ≤ ρ ^ 2 / (128 * d * ((d : ℝ) + 1)) := DA_le (by omega) p ρ hpr
  have hD : ∀ v, |v ⬝ᵥ ((At - lamR d ^ 2 • As) *ᵥ v)| ≤ DA * (v ⬝ᵥ v) := by
    intro v
    have := quad_of_entry (At - lamR d ^ 2 • As) (1 / 2 ^ (p + 1))
      (fun i k => by rw [Matrix.sub_apply]; exact newA_entry hd p A c hsZ i k) v
    rw [hDAdef]; linarith
  set Dc : ℝ := 3 * ρ / (128 * d * ((d : ℝ) + 1)) with hDcdef
  have hc' : (at' - as) ⬝ᵥ (at' - as) ≤ Dc ^ 2 := by
    have hb : (((2 : ℝ) ^ q / ((Nat.sqrt ⌊sr * 2 ^ (2 * q)⌋₊ : ℕ) : ℝ) - 1 / Real.sqrt sr) • u) ⬝ᵥ
        (((2 : ℝ) ^ q / ((Nat.sqrt ⌊sr * 2 ^ (2 * q)⌋₊ : ℕ) : ℝ) - 1 / Real.sqrt sr) • u) ≤
        (4 * Real.sqrt L / (ρ * 2 ^ q)) ^ 2 := hbt
    rw [← ht] at hb
    exact newa_err (by omega) p q A a c ρ (4 * Real.sqrt L / (ρ * 2 ^ q)) hρ hρ1 hpr hsr
      (by rw [ht]; exact_mod_cast ht1) hb (by positivity) (by
        have hsL : Real.sqrt L ≤ Real.sqrt Λ := by
          apply Real.sqrt_le_sqrt
          nlinarith
        calc 4 * Real.sqrt L / (ρ * 2 ^ q) ≤ 4 * Real.sqrt Λ / (ρ * 2 ^ q) := by gcongr
          _ ≤ ρ / (64 * d) := hq2)
  obtain ⟨hm1, hm2⟩ := fr_abs_margin d hd ρ DA Dc hρ hρ1 hDA0 hDA le_rfl
  have hlam1 : 1 ≤ lamR d := by
    unfold lamR
    rw [Real.le_sqrt (by norm_num) (by positivity), one_pow, le_div_iff₀ (by positivity)]
    nlinarith
  have hAtSym : Atᵀ = At := mR_symm p A' (newA_symm A c hAs)
  have hAtPD : At.PosDef := pb_abs_posDef As At hAtSym (lamR d) ρ DA hquadS hD hm1
  have hincl : ∀ x, InB z0 ρ x → InE At at' x := fun x hx =>
    pb_abs_incl As At hAsPD hAtPD as at' (lamR d) ρ DA Dc hlam1 hρ hquadS hD hDA0 hm1 hc' (by positivity) hm2 x
      (hinclS x hx)
  -- `λ_max`
  have hAsL : ∀ v, v ⬝ᵥ (As *ᵥ v) ≤ σ * (v ⬝ᵥ (Ar *ᵥ v)) := fun v =>
    (pb_cc_loewner Ar hA cr hcr0 σ (2 / ((d : ℝ) + 1)) hσ0 (by positivity)
      (by rw [div_le_one (by positivity)]; linarith) v).2
  have hlmax : ∀ v, v ⬝ᵥ (At *ᵥ v) ≤ gam d * L * (v ⬝ᵥ v) := fun v =>
    fr_lmax_step d hd Ar As At L ρ DA hρ hLρ hAsL hL hD hDA v
  -- `det`
  have hdet1 : At.det ≤ (lamR d ^ 2 + DA / ρ ^ 2) ^ d * As.det :=
    pb_abs_det As At hAsPD hAtPD (lamR d) ρ DA hlam1 hρ hquadS hD hDA0
  have hArSym : Arᵀ = Ar := mR_symm p A hAs
  have hdet2 : As.det = σ ^ d * (1 - 2 / ((d : ℝ) + 1)) * Ar.det := by
    have := sc_det Ar (isUnit_iff_ne_zero.mpr hA.det_pos.ne') hArSym cr σ (2 / ((d : ℝ) + 1)) hsr.ne'
    exact this
  have hdet3 := (pb_cc_det_bound d hd).2
  have hlam2 := (fr_lam_sq d hd ρ DA hρ hDA).2.1
  have hdf := fr_det_factor d (by omega)
  have hdet : At.det ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) * Ar.det := by
    have hAr0 := hA.det_pos
    have hx0 : 0 ≤ lamR d ^ 2 + DA / ρ ^ 2 := by positivity
    have hy0 : 0 ≤ σ ^ d * (1 - 2 / ((d : ℝ) + 1)) := by
      apply mul_nonneg (by positivity)
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc At.det ≤ (lamR d ^ 2 + DA / ρ ^ 2) ^ d * As.det := hdet1
      _ = (lamR d ^ 2 + DA / ρ ^ 2) ^ d * (σ ^ d * (1 - 2 / ((d : ℝ) + 1))) * Ar.det := by rw [hdet2]; ring
      _ ≤ (1 + 33 / (128 * d * ((d : ℝ) + 1))) ^ d * Real.exp (-1 / ((d : ℝ) + 1)) * Ar.det := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ hx0 hlam2 d) hdet3 hy0 (by positivity)) hAr0.le
      _ ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) * Ar.det := by gcongr
  -- (K2) passes
  have hΛv : ∀ v, v ⬝ᵥ (At *ᵥ v) ≤ Λ * (v ⬝ᵥ v) := fun v =>
    le_trans (hlmax v) (mul_le_mul_of_nonneg_right hLΛ (by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)))
  have h2 : ∀ i k, |A' i k| ≤ capA := cap_mat p A' Λ capA (fun i k => fr_entry_cap At hAtPD Λ hΛv i k) hcapA
  have hz0 : InE At at' z0 := hincl z0 (by unfold InB; simp; positivity)
  have hcen := fr_center_cap At hAtPD Λ hLΛ0 hΛv at' z0 hz0
  have h3 : ∀ i, |a' i| ≤ capa := by
    intro i
    refine cap_vec p a' z0 Λ capa hLΛ0 hcen hcapa i
  exact ⟨A', a', ellUpd_eq p q j capA capa A a c hK1 h2 h3, newA_symm A c hAs, hAtPD, hincl, hlmax, hdet⟩

end AdversarialBco.Bit.ApQ
