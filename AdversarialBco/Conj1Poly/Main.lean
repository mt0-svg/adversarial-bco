/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Pre
public import AdversarialBco.Conj1.Main
public import AdversarialBco.Conj1Poly.Sanity

@[expose] public section

/-!
# Theorem 1.3, the composition

`theoremConj1UpperPoly_of_conj1 : TheoremConj1Upper → TheoremConj1UpperPoly` uses `TheoremConj1Upper` through its
statement alone: `P_pol = polyProg pre P` with `pre` from `exists_pre (regBound P)`. On an instance, PRE reaches in
`T` steps a state related to `init d n (1/2) n δ` at a centre `a₀`; `K - a₀` meets the hypotheses of
`TheoremConj1Upper` with `r₀ = 1/2`, `R₀ = n` (`transSet_*`), `transStrat σ a₀` is in its class; `lockstep` relates
the two runs; the cost clause transfers (`cost_transfer`, with `W = blockSteps d m`), the points played are
translated by `a₀` (`playedAd_transfer`), the regrets are equal (`regretPts_trans`, `lossAd_trans`), and the
constants are absorbed (`const_bounds`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- The cost clause transfers through a lockstep with blocks of at most `W` steps after a prefix of `T` steps
(`rP`, `rQ`: the rounds of the two runs). -/
theorem cost_transfer (rP rQ : ℕ → ℕ) (κ : ℕ → ℕ) (W T : ℕ) (hmono : Monotone rQ) (hκ0 : κ 0 = 0)
    (hκ : ∀ j, κ j < κ (j + 1) ∧ κ (j + 1) ≤ κ j + W) (hpre : ∀ k < T, rQ k = 0)
    (hin : ∀ j k, κ j ≤ k → k < κ (j + 1) → rQ (T + k) = rP j) (n b0 b : ℕ) (h1 : 1 ≤ rP b0)
    (h2 : ∀ k t, 1 ≤ t → t < n → rP k = t → t + 1 ≤ rP (k + b)) :
    1 ≤ rQ (T + W * b0) ∧ ∀ k t, 1 ≤ t → t < n → rQ k = t → t + 1 ≤ rQ (k + W * b) := by
  have hκ_lt : ∀ j, κ j < κ (j + 1) := fun j => (hκ j).1
  have hκ_add : ∀ j, κ (j + 1) ≤ κ j + W := fun j => (hκ j).2
  have hκ_ge_id : ∀ j, j ≤ κ j := by
    intro j
    induction' j with j ih
    · exact Nat.zero_le _
    · have := hκ_lt j
      have hle : κ j + 1 ≤ κ (j + 1) := by omega
      omega
  have hκ_add_mul : ∀ j b, κ (j + b) ≤ κ j + W * b := by
    intro j b
    induction' b with b ih
    · simp
    · have h := hκ_add (j + b)
      calc
        κ (j + (b + 1)) = κ ((j + b) + 1) := by rw [add_assoc]
        _ ≤ κ (j + b) + W := h
        _ ≤ (κ j + W * b) + W := Nat.add_le_add_right ih W
        _ = κ j + (W * b + W) := by omega
        _ = κ j + W * (b + 1) := by rw [Nat.mul_succ]
  have hpart1 : 1 ≤ rQ (T + W * b0) := by
    have hκb0_le : κ b0 ≤ W * b0 := by
      have h := hκ_add_mul 0 b0
      simpa [hκ0] using h
    have h_eq : rQ (T + κ b0) = rP b0 :=
      hin b0 (κ b0) (le_refl _) (hκ_lt b0)
    have h_one_le : 1 ≤ rQ (T + κ b0) := by
      rw [h_eq]
      exact h1
    have h_le : T + κ b0 ≤ T + W * b0 := by omega
    have h_mono := hmono h_le
    exact le_trans h_one_le h_mono
  have h_exists_j : ∀ k', ∃ j, κ j ≤ k' ∧ k' < κ (j + 1) := by
    intro k'
    have h_exists : ∃ j, k' < κ (j + 1) := by
      refine ⟨k' + 1, ?_⟩
      have hk : k' + 1 ≤ κ (k' + 1) := hκ_ge_id (k' + 1)
      have h_lt : κ (k' + 1) < κ (k' + 1 + 1) := hκ_lt (k' + 1)
      have h_trans : k' + 1 ≤ κ (k' + 1 + 1) := le_trans hk (le_of_lt h_lt)
      have : k' < k' + 1 := by omega
      have : k' < κ (k' + 1 + 1) := lt_of_lt_of_le this h_trans
      simpa [add_assoc] using this
    let j := Nat.find h_exists
    have hj_spec : k' < κ (j + 1) := Nat.find_spec h_exists
    have hj_min : ∀ i < j, κ (i + 1) ≤ k' := by
      intro i hi
      have h_not : ¬ (k' < κ (i + 1)) := Nat.find_min h_exists hi
      omega
    have hj_le : κ j ≤ k' := by
      by_cases hj0 : j = 0
      · rw [hj0, hκ0]
        exact Nat.zero_le _
      · have hpred : j - 1 < j := by
          have hpos : 0 < j := Nat.pos_of_ne_zero hj0
          omega
        have h := hj_min (j - 1) hpred
        have h_eq : (j - 1) + 1 = j := Nat.sub_add_cancel (by omega)
        rw [h_eq] at h
        exact h
    exact ⟨j, hj_le, hj_spec⟩
  have hpart2 : ∀ k t, 1 ≤ t → t < n → rQ k = t → t + 1 ≤ rQ (k + W * b) := by
    intro k t ht1 htn h_eq
    by_cases hk_lt_T : k < T
    · have hzero : rQ k = 0 := hpre k hk_lt_T
      rw [hzero] at h_eq
      omega
    · have hT_le_k : T ≤ k := by omega
      obtain ⟨k', hk_eq⟩ := Nat.exists_eq_add_of_le hT_le_k
      rw [hk_eq] at h_eq
      obtain ⟨j, hj_le, hj_lt⟩ := h_exists_j k'
      have h_rP_eq_t : rP j = t := by
        have := hin j k' hj_le hj_lt
        rw [this] at h_eq
        omega
      have h_rP_add : t + 1 ≤ rP (j + b) := by
        apply h2 j t ht1 htn h_rP_eq_t
      have h_κjb_le : κ (j + b) ≤ κ j + W * b := hκ_add_mul j b
      have h_T_κjb_le_kWb : T + κ (j + b) ≤ (T + k') + W * b := by omega
      have h_rQ_κjb_eq : rQ (T + κ (j + b)) = rP (j + b) :=
        hin (j + b) (κ (j + b)) (le_refl _) (hκ_lt (j + b))
      have h_rQ_κjb_ge : t + 1 ≤ rQ (T + κ (j + b)) := by
        rw [h_rQ_κjb_eq]
        exact h_rP_add
      have h_mono : rQ (T + κ (j + b)) ≤ rQ ((T + k') + W * b) := hmono h_T_κjb_le_kWb
      rw [hk_eq]
      exact le_trans h_rQ_κjb_ge h_mono
  exact And.intro hpart1 hpart2

/-- The cost clause is monotone in its two bounds. -/
theorem costOKAd_mono {P : List Instr} {g : GameAd d} {s0 : State d} {n : ℕ} {B0 B B0' B' : ℝ}
    (h : CostOKAd P g s0 n B0 B) (h0 : B0 ≤ B0') (h1 : B ≤ B') : CostOKAd P g s0 n B0' B' := by
  obtain ⟨hfirst, hsecond⟩ := h
  refine ⟨hfirst.trans (Poly.Conj1.runAd_rounds_mono P g s0 (Nat.ceil_mono h0)), fun k t ht1 htn hk => ?_⟩
  exact (hsecond k t ht1 htn hk).trans
    (Poly.Conj1.runAd_rounds_mono P g s0 (Nat.add_le_add_left (Nat.ceil_mono h1) k))

/-- The first clause of `const_bounds` on real variables: `l = log 2`, `l a = log (2 d n / δ)`, `l b = log (2 M)`,
`q = log (2 n)`. -/
theorem const_bounds_aux1 (C' cpre : ℝ) (k kpre : ℕ) {l a b q x y bs : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hq0 : 0 ≤ q) (hq : q ≤ l * a) (hx : 1 ≤ x) (hy : 1 ≤ y) (hbs : bs ≤ 38 * (x * y)) :
    cpre * (x * y * (l * b)) ^ kpre + bs * ((⌈C' * (x * (l * a) * (2 + q)) ^ k⌉₊ : ℝ) + 1) ≤
      (|cpre| + 38 * (|C'| * 3 ^ k + 2)) / l ^ (2 * max kpre (2 * k + 1)) *
        (x * y * (l * a) * (l * b)) ^ max kpre (2 * k + 1) := by
  set K := max kpre (2 * k + 1) with hK
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x * y * a * b := ⟨_, rfl⟩
  have hxy : 1 ≤ x * y := one_le_mul_of_one_le_of_one_le hx hy
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have hZ1 : 1 ≤ Z := by rw [hZ, mul_assoc]; exact one_le_mul_of_one_le_of_one_le hxy hab
  have hZ0 : 0 ≤ Z := by linarith
  have hrhs : (|cpre| + 38 * (|C'| * 3 ^ k + 2)) / l ^ (2 * K) * (x * y * (l * a) * (l * b)) ^ K =
      (|cpre| + 38 * (|C'| * 3 ^ k + 2)) * Z ^ K := by
    rw [show x * y * (l * a) * (l * b) = l ^ 2 * Z by rw [hZ]; ring, mul_pow, ← pow_mul]
    field_simp
  rw [hrhs, add_mul]
  have hZK : ∀ j ≤ K, Z ^ j ≤ Z ^ K := fun j hj => pow_le_pow_right₀ hZ1 hj
  have hla : l * a ≤ a := mul_le_of_le_one_left (by linarith) hl1.le
  have hlb : l * b ≤ b := mul_le_of_le_one_left (by linarith) hl1.le
  -- the prefix
  have t1 : cpre * (x * y * (l * b)) ^ kpre ≤ |cpre| * Z ^ K := by
    have e1 : 0 ≤ x * y * (l * b) := by have := hl0.le; positivity
    have e2 : x * y * (l * b) ≤ Z := by
      calc x * y * (l * b) ≤ x * y * b := by gcongr
        _ ≤ x * y * b * a := le_mul_of_one_le_right (by positivity) ha
        _ = Z := by rw [hZ]; ring
    calc cpre * (x * y * (l * b)) ^ kpre ≤ |cpre| * (x * y * (l * b)) ^ kpre :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg e1 _)
      _ ≤ |cpre| * Z ^ kpre := by gcongr
      _ ≤ |cpre| * Z ^ K := by gcongr; exact le_max_left _ _
  -- the blocks
  have hw0 : 0 ≤ x * (l * a) * (2 + q) := by have := hl0.le; positivity
  have hw : x * (l * a) * (2 + q) ≤ 3 * Z ^ 2 := by
    have e2 : 2 + q ≤ 3 * a := by linarith
    have e4 : x * a ≤ Z := by
      calc x * a ≤ x * a * (y * b) := le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hy hb)
        _ = Z := by rw [hZ]; ring
    have e5 : a ≤ Z := by
      calc a ≤ a * (x * y * b) := le_mul_of_one_le_right (by linarith)
            (one_le_mul_of_one_le_of_one_le hxy hb)
        _ = Z := by rw [hZ]; ring
    calc x * (l * a) * (2 + q) ≤ x * a * (3 * a) := by gcongr
      _ ≤ Z * (3 * Z) := by gcongr
      _ = 3 * Z ^ 2 := by ring
  have hceil : ∀ w : ℝ, (⌈w⌉₊ : ℝ) + 1 ≤ |w| + 2 := fun w => by
    have h1 : (⌈w⌉₊ : ℝ) ≤ ⌈|w|⌉₊ := by exact_mod_cast Nat.ceil_mono (le_abs_self w)
    have h2 := Nat.ceil_lt_add_one (abs_nonneg w)
    linarith
  have t2 : (⌈C' * (x * (l * a) * (2 + q)) ^ k⌉₊ : ℝ) + 1 ≤ (|C'| * 3 ^ k + 2) * Z ^ (2 * k) := by
    refine (hceil _).trans ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg hw0 k)]
    have e1 : (x * (l * a) * (2 + q)) ^ k ≤ 3 ^ k * Z ^ (2 * k) := by
      calc (x * (l * a) * (2 + q)) ^ k ≤ (3 * Z ^ 2) ^ k := by gcongr
        _ = 3 ^ k * Z ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    have e2 : 1 ≤ Z ^ (2 * k) := one_le_pow₀ hZ1
    have e3 : |C'| * (x * (l * a) * (2 + q)) ^ k ≤ |C'| * (3 ^ k * Z ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    have e4 : (|C'| * 3 ^ k + 2) * Z ^ (2 * k) = |C'| * (3 ^ k * Z ^ (2 * k)) + 2 * Z ^ (2 * k) := by ring
    rw [e4]
    linarith
  have hxyZ : x * y ≤ Z := by
    calc x * y ≤ x * y * (a * b) := le_mul_of_one_le_right (by positivity) hab
      _ = Z := by rw [hZ]; ring
  have t3 : bs * ((⌈C' * (x * (l * a) * (2 + q)) ^ k⌉₊ : ℝ) + 1) ≤ 38 * (|C'| * 3 ^ k + 2) * Z ^ K := by
    calc bs * ((⌈C' * (x * (l * a) * (2 + q)) ^ k⌉₊ : ℝ) + 1)
        ≤ (38 * Z) * ((|C'| * 3 ^ k + 2) * Z ^ (2 * k)) := by
          gcongr
          linarith
      _ = 38 * (|C'| * 3 ^ k + 2) * Z ^ (2 * k + 1) := by ring
      _ ≤ 38 * (|C'| * 3 ^ k + 2) * Z ^ K := by gcongr; exact le_max_right _ _
  linarith

/-- The second clause of `const_bounds` on real variables. -/
theorem const_bounds_aux2 (C' cpre : ℝ) (k kpre : ℕ) {l a x y bs : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (ha : 1 ≤ a)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hbs : bs ≤ 38 * (x * y)) :
    bs * ((⌈C' * (x * (l * a)) ^ k⌉₊ : ℝ) + 1) ≤
      (|cpre| + 38 * (|C'| * 3 ^ k + 2)) / l ^ (2 * max kpre (2 * k + 1)) *
        (x * y * (l * a)) ^ max kpre (2 * k + 1) := by
  set K := max kpre (2 * k + 1) with hK
  set A := |cpre| + 38 * (|C'| * 3 ^ k + 2) with hA
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x * y * a := ⟨_, rfl⟩
  have hxy : 1 ≤ x * y := one_le_mul_of_one_le_of_one_le hx hy
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact one_le_mul_of_one_le_of_one_le hxy ha
  have hZ0 : 0 ≤ Z := by linarith
  have hA0 : 0 ≤ A := by positivity
  have hrhs : A * Z ^ K ≤ A / l ^ (2 * K) * (x * y * (l * a)) ^ K := by
    rw [show x * y * (l * a) = l * Z by rw [hZ]; ring, mul_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have e1 : l ^ (2 * K) ≤ l ^ K := pow_le_pow_of_le_one hl0.le hl1.le (by omega)
    have e2 : 0 ≤ A * Z ^ K := by positivity
    calc A * Z ^ K * l ^ (2 * K) ≤ A * Z ^ K * l ^ K := by gcongr
      _ = A * (l ^ K * Z ^ K) := by ring
  refine le_trans ?_ hrhs
  have hZK : ∀ j ≤ K, Z ^ j ≤ Z ^ K := fun j hj => pow_le_pow_right₀ hZ1 hj
  have hw0 : 0 ≤ x * (l * a) := by have := hl0.le; positivity
  have hw : x * (l * a) ≤ Z := by
    have hla : l * a ≤ a := mul_le_of_le_one_left (by linarith) hl1.le
    calc x * (l * a) ≤ x * a := by gcongr
      _ ≤ x * a * y := le_mul_of_one_le_right (by positivity) hy
      _ = Z := by rw [hZ]; ring
  have hceil : ∀ w : ℝ, (⌈w⌉₊ : ℝ) + 1 ≤ |w| + 2 := fun w => by
    have h1 : (⌈w⌉₊ : ℝ) ≤ ⌈|w|⌉₊ := by exact_mod_cast Nat.ceil_mono (le_abs_self w)
    have h2 := Nat.ceil_lt_add_one (abs_nonneg w)
    linarith
  have t2 : (⌈C' * (x * (l * a)) ^ k⌉₊ : ℝ) + 1 ≤ (|C'| + 2) * Z ^ k := by
    refine (hceil _).trans ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg hw0 k)]
    have e1 : (x * (l * a)) ^ k ≤ Z ^ k := by gcongr
    have e2 : 1 ≤ Z ^ k := one_le_pow₀ hZ1
    have e3 : |C'| * (x * (l * a)) ^ k ≤ |C'| * Z ^ k := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    have e4 : (|C'| + 2) * Z ^ k = |C'| * Z ^ k + 2 * Z ^ k := by ring
    rw [e4]
    linarith
  have hxyZ : x * y ≤ Z := by
    calc x * y ≤ x * y * a := le_mul_of_one_le_right (by positivity) ha
      _ = Z := by rw [hZ]
  have h3k : |C'| ≤ |C'| * 3 ^ k := le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ (by norm_num))
  calc bs * ((⌈C' * (x * (l * a)) ^ k⌉₊ : ℝ) + 1)
      ≤ (38 * Z) * ((|C'| + 2) * Z ^ k) := by
        gcongr
        linarith
    _ = 38 * (|C'| + 2) * Z ^ (k + 1) := by ring
    _ ≤ 38 * (|C'| * 3 ^ k + 2) * Z ^ K := by
        gcongr
        exact le_trans (by omega) (le_max_right _ _)
    _ ≤ A * Z ^ K := by
        rw [hA, add_mul]
        have : 0 ≤ |cpre| * Z ^ K := by positivity
        linarith

/-- The constants: the prefix and the blocks are absorbed into one bound of the shape of `TheoremConj1UpperPoly`. -/
theorem const_bounds (C' cpre : ℝ) (k kpre : ℕ) :
    ∃ (C1 : ℝ) (k1 : ℕ), ∀ d m M n : ℕ, 1 ≤ d → 1 ≤ m → 1 ≤ M → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
      cpre * ((d : ℝ) * m * Real.log (2 * M)) ^ kpre +
          (blockSteps d m : ℝ) *
            (⌈C' * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log ((n : ℝ) / (1 / 2)))) ^ k⌉₊ + 1) ≤
        C1 * ((d : ℝ) * m * Real.log (2 * d * n / δ) * Real.log (2 * M)) ^ k1 ∧
      (blockSteps d m : ℝ) * (⌈C' * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k⌉₊ + 1) ≤
        C1 * ((d : ℝ) * m * Real.log (2 * d * n / δ)) ^ k1 := by
  refine ⟨(|cpre| + 38 * (|C'| * 3 ^ k + 2)) / Real.log 2 ^ (2 * max kpre (2 * k + 1)), max kpre (2 * k + 1),
    fun d m M n hd hm hM hn δ hδ0 hδ1 => ?_⟩
  have hℓ0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMm : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the logarithms
  have h2n : 2 * (n : ℝ) ≤ 2 * d * n / δ := by
    rw [le_div_iff₀ hδ0]
    have e1 : (2 : ℝ) * n ≤ 2 * d * n := by
      have := mul_le_mul_of_nonneg_right hD (by linarith : (0 : ℝ) ≤ 2 * n)
      linarith
    have e2 : 2 * (n : ℝ) * δ ≤ 2 * n := by
      have := mul_le_mul_of_nonneg_left hδ1.le (by linarith : (0 : ℝ) ≤ 2 * n)
      linarith
    linarith
  have hl2n : Real.log ((n : ℝ) / (1 / 2)) = Real.log (2 * n) := by congr 1; ring
  have hq0 : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hqL : Real.log (2 * (n : ℝ)) ≤ Real.log (2 * d * n / δ) := Real.log_le_log (by positivity) h2n
  have hLℓ : Real.log 2 ≤ Real.log (2 * d * n / δ) :=
    (Real.log_le_log (by norm_num) (by linarith)).trans hqL
  have hvℓ : Real.log 2 ≤ Real.log (2 * M) := Real.log_le_log (by norm_num) (by linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = Real.log (2 * d * n / δ) / Real.log 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.log (2 * M) / Real.log 2 := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by rw [ha]; exact (one_le_div hℓ0).2 hLℓ
  have hb1 : 1 ≤ b := by rw [hb]; exact (one_le_div hℓ0).2 hvℓ
  have hLa : Real.log (2 * d * n / δ) = Real.log 2 * a := by rw [ha]; field_simp
  have hMb : Real.log (2 * M) = Real.log 2 * b := by rw [hb]; field_simp
  have hbs : (blockSteps d m : ℝ) ≤ 38 * ((d : ℝ) * m) := by
    have e1 : (m : ℝ) ≤ d * m := le_mul_of_one_le_left (by linarith) hD
    have e2 : (d : ℝ) ≤ d * m := le_mul_of_one_le_right (by linarith) hMm
    have e3 : (1 : ℝ) ≤ d * m := one_le_mul_of_one_le_of_one_le hD hMm
    unfold blockSteps
    push_cast
    linarith
  rw [hl2n, hLa, hMb]
  rw [hLa] at hqL
  exact ⟨const_bounds_aux1 C' cpre k kpre hℓ0 hℓ1 ha1 hb1 hq0 hqL hD hMm hbs,
    const_bounds_aux2 C' cpre k kpre hℓ0 hℓ1 ha1 hD hMm hbs⟩

variable {m : ℕ}

/-- Under the cost clause, every round `t < n` is reached, from a state that has played no round. -/
theorem costOKAd_reach {P : List Instr} {g : GameAd d} {s0 : State d} {n : ℕ} {B0 B : ℝ} (hs0 : s0.rounds = 0)
    (h : CostOKAd P g s0 n B0 B) : ∀ t < n, ∃ k, t < (runAd P g s0 k).rounds := by
  intro t ht
  induction t with
  | zero => exact ⟨_, h.1⟩
  | succ t ih =>
    obtain ⟨k, hk⟩ := ih (by omega)
    obtain ⟨k', -, hk'⟩ := Conj1PolySanity.reachAd P g s0 k (t + 1) (by omega) hk
    exact ⟨k' + ⌈B⌉₊, h.2 k' (t + 1) (by omega) ht hk'⟩

theorem runAd_add (P : List Instr) (g : GameAd d) (s0 : State d) (T k : ℕ) :
    runAd P g s0 (T + k) = runAd P g (runAd P g s0 T) k := by
  simp only [runAd]
  rw [add_comm, Function.iterate_add_apply]

/-- The regret reads the losses and the points of the rounds `t < n` only. -/
theorem regretPts_congr (K : Set (E d)) {f f' : ℕ → E d → ℝ} {x x' : ℕ → E d} {n : ℕ}
    (hf : ∀ t < n, f t = f' t) (hx : ∀ t < n, x t = x' t) : regretPts K f x n = regretPts K f' x' n := by
  unfold regretPts
  have h1 : ∑ t ∈ Finset.range n, f t (x t) = ∑ t ∈ Finset.range n, f' t (x' t) :=
    Finset.sum_congr rfl fun t ht => by rw [hf t (Finset.mem_range.1 ht), hx t (Finset.mem_range.1 ht)]
  have h2 : (fun y => ∑ t ∈ Finset.range n, f t y) = fun y => ∑ t ∈ Finset.range n, f' t y :=
    funext fun y => Finset.sum_congr rfl fun t ht => by rw [hf t (Finset.mem_range.1 ht)]
  rw [h1, h2]

/-- The transfer through the lockstep: the cost clause of `P` against the translated strategy gives that of `Q`
with blocks of `blockSteps d m` steps after `T` steps of prefix, and the points of `Q` are those of `P` translated
by `a₀`. -/
theorem lockstep_transfer {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} (hregs : ∀ ins ∈ P, ∀ x ∈ Instr.regs ins, x < r)
    (hcode : ∀ p ins, P[p]? = some ins → CodeAt Q (τ p) (blockCode r (τ p) τ ins) ∧ τ (p + 1) = τ p + blockLen ins)
    (hhalt : ∀ p, P.length ≤ p → Q.length ≤ τ p) (σ : Strategy d) (ε gs : ℕ → ℝ) (K : Set (E d))
    {s0 s0' : State d} {T : ℕ} (hs0 : s0.rounds = 0)
    (hpre : ∀ k ≤ T, (runAd Q ⟨K, σ, ε, gs⟩ s0' k).rounds = 0)
    (h0 : SimRel r τ a0 Am bv s0 (runAd Q ⟨K, σ, ε, gs⟩ s0' T)) {n : ℕ} {B0 B : ℝ}
    (hc : CostOKAd P ⟨transSet (polytope Am bv) a0, transStrat σ a0, ε, gs⟩ s0 n B0 B) :
    CostOKAd Q ⟨K, σ, ε, gs⟩ s0' n ((T + blockSteps d m * ⌈B0⌉₊ : ℕ) : ℝ) ((blockSteps d m * ⌈B⌉₊ : ℕ) : ℝ) ∧
      ∀ t < n, playedAd Q ⟨K, σ, ε, gs⟩ s0' t =
        playedAd P ⟨transSet (polytope Am bv) a0, transStrat σ a0, ε, gs⟩ s0 t + a0 := by
  set g : GameAd d := ⟨K, σ, ε, gs⟩ with hg
  set g' : GameAd d := ⟨transSet (polytope Am bv) a0, transStrat σ a0, ε, gs⟩ with hg'
  obtain ⟨κ, hκ0, hκ, hrel, hrd⟩ := lockstep hregs hcode hhalt σ ε gs (transSet (polytope Am bv) a0) K
    (fun y => Iff.rfl) h0
  have hin : ∀ j k, κ j ≤ k → k < κ (j + 1) →
      (runAd Q g s0' (T + k)).rounds = (runAd P g' s0 j).rounds := by
    intro j k h1 h2
    rw [runAd_add]
    exact hrd j k h1 h2
  have hct := cost_transfer (fun j => (runAd P g' s0 j).rounds) (fun k => (runAd Q g s0' k).rounds) κ
    (blockSteps d m) T (fun _ _ h => Poly.Conj1.runAd_rounds_mono Q g s0' h) hκ0 hκ
    (fun k hk => hpre k hk.le) hin n ⌈B0⌉₊ ⌈B⌉₊ hc.1 hc.2
  refine ⟨⟨?_, fun k t h1 h2 h3 => ?_⟩, fun t ht => ?_⟩
  · rw [Nat.ceil_natCast]; exact hct.1
  · rw [Nat.ceil_natCast]; exact hct.2 k t h1 h2 h3
  · obtain ⟨j, hj⟩ := costOKAd_reach hs0 hc t ht
    have hjQ : (runAd Q g s0' (T + κ j)).rounds = (runAd P g' s0 j).rounds :=
      hin j (κ j) le_rfl (hκ j).1
    rw [Poly.Conj1.playedAd_eq P g' s0 j t hj, Poly.Conj1.playedAd_eq Q g s0' (T + κ j) t (by rw [hjQ]; exact hj),
      runAd_add]
    exact (hrel j).pts t hj


theorem codeAt_prefix (pre L : List Instr) : CodeAt (pre ++ L) 0 pre := fun i hi => by
  rw [Nat.zero_add, List.getElem?_append_left hi]

theorem blockStart_zero (o : ℕ) (P : List Instr) : blockStart o P 0 = o := by
  simp [blockStart]

/-- The composition: the polytope form from the frozen `TheoremConj1Upper`, through its statement alone. -/
theorem theoremConj1UpperPoly_of_conj1 : TheoremConj1Upper → TheoremConj1UpperPoly := by
  rintro ⟨P, C, C', k, hP⟩
  obtain ⟨pre, cpre, kpre, hpreQF, hpre⟩ := exists_pre (regBound P) (le_max_left _ _)
  obtain ⟨C1, k1, hC1⟩ := const_bounds C' cpre k kpre
  refine ⟨polyProg pre P, C, C1, k1, polyProg_queryFree hpreQF P, ?_⟩
  intro d hd n hn m M δ hδ0 hδ1 A b hH hball hdiam σ hσ ν hν
  obtain ⟨T, a0, hT, ha0, hrun⟩ :=
    hpre (polyProg pre P) (codeAt_prefix _ _) d hd n hn m M δ hδ0 hδ1 A b hH hball hdiam
  have ha0K : a0 ∈ polytope A b := ha0 (Metric.mem_closedBall_self (by norm_num))
  have hn' : (1 / 2 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hcost, hprob⟩ := hP d hd n hn (1 / 2) n δ (by norm_num) hn' hδ0 hδ1 (transSet (polytope A b) a0)
    (transSet_isCompact (isCompact_polytope A b n hdiam) a0) (transSet_convex (convex_polytope A b) a0)
    (ball_transSet ha0) (transSet_sub_ball ha0K hdiam) (transStrat σ a0) (transStrat_mem hσ a0) ν hν
  -- the lockstep, on every run
  have hτ0 : blockStart (pre.length) P 0 = pre.length := blockStart_zero _ _
  have key : ∀ gs noise : ℕ → ℝ,
      CostOKAd (polyProg pre P) ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m δ A b) n
          ((T + blockSteps d m * ⌈C' * ((d : ℝ) * Real.log (2 * d * n / δ) *
            (2 + Real.log ((n : ℝ) / (1 / 2)))) ^ k⌉₊ : ℕ) : ℝ)
          ((blockSteps d m * ⌈C' * ((d : ℝ) * Real.log (2 * d * n / δ)) ^ k⌉₊ : ℕ) : ℝ) ∧
        ∀ t < n, playedAd (polyProg pre P) ⟨polytope A b, σ, noise, gs⟩ (initPoly d n m δ A b) t =
          playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, noise, gs⟩ (init d n (1 / 2) n δ) t + a0 := by
    intro gs noise
    set g : GameAd d := ⟨polytope A b, σ, noise, gs⟩
    obtain ⟨hpts, hrel⟩ := hrun (g.world (initPoly d n m δ A b).pts)
    have heq : ∀ k ≤ T, runAd (polyProg pre P) g (initPoly d n m δ A b) k =
        run (polyProg pre P) (g.world (initPoly d n m δ A b).pts) (initPoly d n m δ A b) k :=
      fun k hk => runAd_eq_run_of_pts fun k' hk' => (hpts k' (by omega)).2
    refine lockstep_transfer (τ := blockStart pre.length P) (fun ins hins x hx => regs_lt_regBound hins hx)
      (fun p ins h => ⟨polyProg_codeAt pre P h, blockStart_succ _ P h⟩)
      (fun p hp => by rw [blockStart_ge _ P hp, polyProg_length]) σ noise gs (polytope A b) (by rfl)
      (fun k hk => by rw [heq k hk]; exact (hpts k hk).1) (by rw [heq T le_rfl]; exact hrel _ hτ0) ?_
    exact (hcost gs noise).1
  have hm := Conj1PolySanity.one_le_m hd A b hdiam
  have hM := Conj1PolySanity.one_le_M hm A b hH
  obtain ⟨h1, h2⟩ := hC1 d m M n hd hm hM hn δ hδ0 hδ1
  have hW : (0 : ℝ) ≤ blockSteps d m := Nat.cast_nonneg _
  refine ⟨fun gs noise => ⟨?_, fun t ht => ?_⟩, ?_⟩
  · refine costOKAd_mono (key gs noise).1 ?_ ?_
    · push_cast at h1 ⊢
      nlinarith
    · push_cast at h2 ⊢
      nlinarith
  · rw [(key gs noise).2 t ht]
    exact (hcost gs noise).2 t ht
  · have hreg : ∀ ω : (ℕ → ℝ) × (ℕ → ℝ),
        regretPts (polytope A b)
            (lossAd σ ω.2 (playedAd (polyProg pre P) ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)))
            (playedAd (polyProg pre P) ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)) n =
          regretPts (transSet (polytope A b) a0)
            (lossAd (transStrat σ a0) ω.2
              (playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, ω.2, ω.1⟩ (init d n (1 / 2) n δ)))
            (playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, ω.2, ω.1⟩ (init d n (1 / 2) n δ)) n := by
      intro ω
      have hx := (key ω.1 ω.2).2
      set xP := playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, ω.2, ω.1⟩ (init d n (1 / 2) n δ)
      calc _ = regretPts (polytope A b) (lossAd σ ω.2 (fun u => xP u + a0)) (fun u => xP u + a0) n :=
            regretPts_congr _ (fun t ht => Poly.Conj1.lossAd_congr σ ω.2 t fun i hi => hx i (by omega)) hx
        _ = regretPts (transSet (polytope A b) a0) (fun t y => lossAd σ ω.2 (fun u => xP u + a0) t (y + a0))
              xP n := (regretPts_trans _ a0 _ xP n).symm
        _ = _ := by
          congr 1
          funext t y
          rw [lossAd_trans]
    have hset : {ω : (ℕ → ℝ) × (ℕ → ℝ) |
          C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
            regretPts (polytope A b)
              (lossAd σ ω.2 (playedAd (polyProg pre P) ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)))
              (playedAd (polyProg pre P) ⟨polytope A b, σ, ω.2, ω.1⟩ (initPoly d n m δ A b)) n} =
        {ω : (ℕ → ℝ) × (ℕ → ℝ) |
          C * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 <
            regretPts (transSet (polytope A b) a0)
              (lossAd (transStrat σ a0) ω.2
                (playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, ω.2, ω.1⟩ (init d n (1 / 2) n δ)))
              (playedAd P ⟨transSet (polytope A b) a0, transStrat σ a0, ω.2, ω.1⟩ (init d n (1 / 2) n δ)) n} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hreg ω]
    rw [hset]
    exact hprob

end AdversarialBco.Conj1Poly

namespace AdversarialBco

/-- The upper half of Conjecture 1 on the polytopes of Bubeck, Eldan and Lee. -/
theorem theoremConj1UpperPoly_of_conj1 : TheoremConj1Upper → TheoremConj1UpperPoly :=
  Conj1Poly.theoremConj1UpperPoly_of_conj1

/-- The upper half of Conjecture 1 on the polytopes of Bubeck, Eldan and Lee, as frozen in StatementConj1Poly.lean. -/
theorem theoremConj1UpperPoly : TheoremConj1UpperPoly := theoremConj1UpperPoly_of_conj1 theoremConj1Upper

end AdversarialBco
