/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAM

@[expose] public section

/-!
# Bit-length arithmetic of the frozen machine and the frozen cost form

Self-contained facts on `BitRAM.len` and `BitRAM.readCoins`, the space of a step, and the comparison
of `(d m (size n + 1) (size M + 1))^k` with the frozen form `(d m log(2dn) log(2M))^k`.
-/

open AdversarialBco AdversarialBco.BitRAM

theorem AdversarialBco.Bit.Transfer.len_add_le (a b : ℤ) : len (a + b) ≤ max (len a) (len b) + 1 := by
  unfold len
  rw [Nat.size_le]
  have h_add : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have ha : a.natAbs < 2 ^ (a.natAbs.size) := Nat.lt_size_self _
  have hb : b.natAbs < 2 ^ (b.natAbs.size) := Nat.lt_size_self _
  have hmax_a : a.natAbs.size ≤ max (a.natAbs.size) (b.natAbs.size) := Nat.le_max_left _ _
  have hmax_b : b.natAbs.size ≤ max (a.natAbs.size) (b.natAbs.size) := Nat.le_max_right _ _
  have ha' : a.natAbs < 2 ^ (max (a.natAbs.size) (b.natAbs.size)) :=
    lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hmax_a)
  have hb' : b.natAbs < 2 ^ (max (a.natAbs.size) (b.natAbs.size)) :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hmax_b)
  have hsum : a.natAbs + b.natAbs < 2 ^ (max (a.natAbs.size) (b.natAbs.size)) + 2 ^ (max (a.natAbs.size) (b.natAbs.size)) :=
    Nat.add_lt_add ha' hb'
  have htemp : 2 ^ (max (a.natAbs.size) (b.natAbs.size)) + 2 ^ (max (a.natAbs.size) (b.natAbs.size))
      = 2 ^ (max (a.natAbs.size) (b.natAbs.size) + 1) := by
    calc
      2 ^ (max (a.natAbs.size) (b.natAbs.size)) + 2 ^ (max (a.natAbs.size) (b.natAbs.size))
          = 2 * 2 ^ (max (a.natAbs.size) (b.natAbs.size)) := by rw [Nat.two_mul]
      _ = 2 ^ (max (a.natAbs.size) (b.natAbs.size)) * 2 := by rw [mul_comm]
      _ = 2 ^ ((max (a.natAbs.size) (b.natAbs.size)).succ) := by rw [Nat.pow_succ]
      _ = 2 ^ (max (a.natAbs.size) (b.natAbs.size) + 1) := rfl
  have hgoal : a.natAbs + b.natAbs < 2 ^ (max (a.natAbs.size) (b.natAbs.size) + 1) :=
    lt_of_lt_of_eq hsum htemp
  exact lt_of_le_of_lt h_add hgoal

theorem AdversarialBco.Bit.Transfer.len_mul_le (a b : ℤ) : len (a * b) ≤ len a + len b := by
  unfold len
  rw [Int.natAbs_mul]
  rw [Nat.size_le]
  calc
    a.natAbs * b.natAbs < (2 ^ a.natAbs.size) * (2 ^ b.natAbs.size) :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self _) (Nat.lt_size_self _)
    _ = 2 ^ (a.natAbs.size + b.natAbs.size) := by rw [Nat.pow_add]

theorem AdversarialBco.Bit.Transfer.len_ediv_le (a b : ℤ) : len (a / b) ≤ len a := by
  unfold len
  apply Nat.size_le_size
  exact Int.natAbs_ediv_le_natAbs a b

theorem AdversarialBco.Bit.Transfer.len_readCoins_le (cs : ℕ → Bool) (c k : ℕ) : len (readCoins cs c k) ≤ k := by
  have h : 0 ≤ readCoins cs c k ∧ readCoins cs c k < 2 ^ k := by
    induction k with
    | zero => simp [readCoins]
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      simp only [readCoins, pow_succ]
      split_ifs <;> constructor <;> omega
  have h2 : ((readCoins cs c k).natAbs : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h.1]; push_cast; exact h.2
  unfold len
  rw [Nat.size_le]
  exact_mod_cast h2

theorem AdversarialBco.Bit.Transfer.frozen_form (d m n M k : ℕ) (c : ℝ) (hc : 0 ≤ c) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hM : 1 ≤ M) :
    c * ((d : ℝ) * m * (n.size + 1) * (M.size + 1)) ^ k ≤
      c * (4 / Real.log 2 ^ 2) ^ k * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k := by
  -- helper lemma: for x ≥ 1, (x.size : ℝ) * log 2 ≤ log(2*x)
  have hsize_log_bound (x : ℕ) (hx : 1 ≤ x) : (x.size : ℝ) * Real.log 2 ≤ Real.log (2 * (x : ℝ)) := by
    have hx0 : x ≠ 0 := by omega
    have hsize_pos : 0 < x.size := by
      rw [Nat.size_pos]
      omega
    have h_lt : x.size - 1 < x.size := by
      omega
    have h_pow_le : 2 ^ (x.size - 1) ≤ x :=
      (Nat.lt_size.mp h_lt)
    -- convert to ℝ
    have h_pow_le' : (2 : ℝ) ^ (x.size - 1 : ℕ) ≤ (x : ℝ) := by
      exact_mod_cast h_pow_le
    -- 2^(x.size) = 2 * 2^(x.size - 1)
    have h_two_pow_size_le : (2 : ℝ) ^ (x.size : ℕ) ≤ 2 * (x : ℝ) := by
      calc
        (2 : ℝ) ^ (x.size : ℕ) = (2 : ℝ) * (2 : ℝ) ^ (x.size - 1 : ℕ) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ x.size)]
        _ ≤ (2 : ℝ) * (x : ℝ) := by
          nlinarith
    -- take log of both sides
    have h_log_le : Real.log ((2 : ℝ) ^ (x.size : ℕ)) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by
        exact pow_pos (by norm_num) _
      ) h_two_pow_size_le
    -- log(2^(size x)) = (size x) * log 2
    simpa [Real.log_pow] using h_log_le
  -- Now use the lemma for n and M
  have hn_bound : (n.size : ℝ) * Real.log 2 ≤ Real.log (2 * (n : ℝ)) :=
    hsize_log_bound n hn
  have hM_bound : (M.size : ℝ) * Real.log 2 ≤ Real.log (2 * (M : ℝ)) :=
    hsize_log_bound M hM
  -- From these, get (size + 1) * log 2 ≤ 2 * log(2*x)
  -- (size+1)*log 2 = size*log 2 + log 2 ≤ log(2*x) + log 2 ≤ log(2*x) + log(2*x) = 2*log(2*x)
  -- The last step uses log 2 ≤ log(2*x), which holds since 2 ≤ 2*x when x ≥ 1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_le_log2x (x : ℕ) (hx : 1 ≤ x) : Real.log 2 ≤ Real.log (2 * (x : ℝ)) := by
    have hx' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hpos : (0 : ℝ) < 2 * (x : ℝ) := by nlinarith
    have h_le : (2 : ℝ) ≤ 2 * (x : ℝ) := by nlinarith
    exact le_trans (by norm_num) (Real.log_le_log (by norm_num) h_le)
  have hn_bound' : ((n.size : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log (2 * (n : ℝ)) := by
    have h := add_le_add_right hn_bound (Real.log 2)
    -- h: (n.size)*log 2 + log 2 ≤ log(2*n) + log 2
    -- i.e., (n.size+1)*log 2 ≤ log(2*n) + log 2
    -- and log(2*n) + log 2 ≤ log(2*n) + log(2*n) = 2*log(2*n)
    have h2 : Real.log (2 * (n : ℝ)) + Real.log 2 ≤ 2 * Real.log (2 * (n : ℝ)) := by
      have hlog2_le := hlog2_le_log2x n hn
      nlinarith
    nlinarith
  have hM_bound' : ((M.size : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log (2 * (M : ℝ)) := by
    have h := add_le_add_right hM_bound (Real.log 2)
    have h2 : Real.log (2 * (M : ℝ)) + Real.log 2 ≤ 2 * Real.log (2 * (M : ℝ)) := by
      have hlog2_le := hlog2_le_log2x M hM
      nlinarith
    nlinarith
  -- Multiply the two inequalities
  have h_mul_bound : ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) * (Real.log 2) ^ 2 ≤
      4 * Real.log (2 * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
    have h_nonneg_n : 0 ≤ ((n.size : ℝ) + 1) * Real.log 2 := by
      have : 0 ≤ (n.size : ℝ) := by exact_mod_cast Nat.zero_le _
      nlinarith [hlog2pos]
    have h_nonneg_M : 0 ≤ ((M.size : ℝ) + 1) * Real.log 2 := by
      have : 0 ≤ (M.size : ℝ) := by exact_mod_cast Nat.zero_le _
      nlinarith [hlog2pos]
    have h_nonneg_log_n : 0 ≤ Real.log (2 * (n : ℝ)) := by
      have : (1 : ℝ) < 2 * (n : ℝ) := by
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      exact le_of_lt (Real.log_pos this)
    have h_nonneg_log_M : 0 ≤ Real.log (2 * (M : ℝ)) := by
      have : (1 : ℝ) < 2 * (M : ℝ) := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        nlinarith
      exact le_of_lt (Real.log_pos this)
    nlinarith
  -- Now we need to relate log(2*n) and log(2*d*n)
  have h_log_n_le : Real.log (2 * (n : ℝ)) ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) := by
    refine Real.log_le_log ?_ ?_
    · positivity
    · have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith
  -- Combine
  have h_main : (d : ℝ) * (m : ℝ) * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) ≤
      (4 / (Real.log 2) ^ 2) * (d : ℝ) * (m : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
    have hdpos : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have hmpos : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
    have hdm_nonneg : 0 ≤ (d : ℝ) * (m : ℝ) := mul_nonneg hdpos hmpos
    have h_log_M_nonneg : 0 ≤ Real.log (2 * (M : ℝ)) := by
      have : (1 : ℝ) < 2 * (M : ℝ) := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        nlinarith
      exact le_of_lt (Real.log_pos this)
    have h_log_n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
      have : (1 : ℝ) < 2 * (n : ℝ) := by
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      exact le_of_lt (Real.log_pos this)
    have h_intermediate : ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) * (Real.log 2) ^ 2 ≤
        4 * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
      have h_mul_log : Real.log (2 * (n : ℝ)) * Real.log (2 * (M : ℝ)) ≤
          Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
        -- Since log(2*M) ≥ 0, we can multiply the inequality
        nlinarith
      nlinarith
    have h_log2_sq_pos : 0 < (Real.log 2) ^ 2 := by
      positivity
    -- h_intermediate: A * (log 2)^2 ≤ 4 * B * C
    -- We want: d*m*A ≤ (4/(log 2)^2) * d*m*B*C
    -- Multiply both sides of h_intermediate by d*m and divide by (log 2)^2
    -- Rearranging: A ≤ (4/(log 2)^2) * B * C
    -- Then multiply by d*m
    have h_A_le : ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) ≤
        (4 / (Real.log 2) ^ 2) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
      -- From h_intermediate: A * (log 2)^2 ≤ 4 * B * C
      -- Divide both sides by (log 2)^2
      calc
        ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) =
            (((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) * (Real.log 2) ^ 2) / (Real.log 2) ^ 2 := by
          field_simp [ne_of_gt h_log2_sq_pos]
        _ ≤ (4 * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ))) / (Real.log 2) ^ 2 := by
          exact (div_le_div_of_nonneg_right h_intermediate (by positivity : 0 ≤ (Real.log 2) ^ 2))
        _ = (4 / (Real.log 2) ^ 2) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
          ring
    -- Now multiply by d*m
    calc
      (d : ℝ) * (m : ℝ) * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) =
          ((d : ℝ) * (m : ℝ)) * (((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) := by ring
      _ ≤ ((d : ℝ) * (m : ℝ)) * ((4 / (Real.log 2) ^ 2) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ))) := by
        exact mul_le_mul_of_nonneg_left h_A_le hdm_nonneg
      _ = (4 / (Real.log 2) ^ 2) * (d : ℝ) * (m : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by ring
  -- Now raise both sides to power k
  have h_nonneg_left : 0 ≤ (d : ℝ) * (m : ℝ) * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1) := by
    positivity
  have h_nonneg_right : 0 ≤ (4 / (Real.log 2) ^ 2) * (d : ℝ) * (m : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ)) := by
    have hlogpos : 0 ≤ Real.log (2 * (d : ℝ) * (n : ℝ)) := by
      have : (1 : ℝ) < 2 * (d : ℝ) * (n : ℝ) := by
        have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      exact le_of_lt (Real.log_pos this)
    have hlogMpos : 0 ≤ Real.log (2 * (M : ℝ)) := by
      have : (1 : ℝ) < 2 * (M : ℝ) := by
        have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        nlinarith
      exact le_of_lt (Real.log_pos this)
    positivity
  have h_pow_le : ((d : ℝ) * (m : ℝ) * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) ^ k ≤
      ((4 / (Real.log 2) ^ 2) * (d : ℝ) * (m : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ))) ^ k :=
    pow_le_pow_left₀ h_nonneg_left h_main k
  -- Now multiply both sides by c (≥ 0)
  have h_final : c * ((d : ℝ) * (m : ℝ) * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) ^ k ≤
      c * ((4 / (Real.log 2) ^ 2) * (d : ℝ) * (m : ℝ) * Real.log (2 * (d : ℝ) * (n : ℝ)) * Real.log (2 * (M : ℝ))) ^ k :=
    mul_le_mul_of_nonneg_left h_pow_le hc
  -- Expand the right side to match the goal
  simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using h_final

private lemma AdversarialBco.Bit.Transfer.nat_size_add_le (m n : ℕ) : Nat.size (m + n) ≤ max (Nat.size m) (Nat.size n) + 1 := by
  have hm : m < 2 ^ (Nat.size m) := Nat.lt_size_self m
  have hn : n < 2 ^ (Nat.size n) := Nat.lt_size_self n
  have hmax_m : Nat.size m ≤ max (Nat.size m) (Nat.size n) := le_max_left _ _
  have hmax_n : Nat.size n ≤ max (Nat.size m) (Nat.size n) := le_max_right _ _
  have hpow_m : 2 ^ (Nat.size m) ≤ 2 ^ (max (Nat.size m) (Nat.size n)) :=
    Nat.pow_le_pow_right (by decide) hmax_m
  have hpow_n : 2 ^ (Nat.size n) ≤ 2 ^ (max (Nat.size m) (Nat.size n)) :=
    Nat.pow_le_pow_right (by decide) hmax_n
  have hsum : m + n < 2 ^ (max (Nat.size m) (Nat.size n)) + 2 ^ (max (Nat.size m) (Nat.size n)) := by
    exact Nat.add_lt_add (lt_of_lt_of_le hm hpow_m) (lt_of_lt_of_le hn hpow_n)
  have hsum' : m + n < 2 ^ (max (Nat.size m) (Nat.size n) + 1) := by
    rw [Nat.pow_succ]
    calc
      m + n < 2 ^ (max (Nat.size m) (Nat.size n)) + 2 ^ (max (Nat.size m) (Nat.size n)) := hsum
      _ = 2 * 2 ^ (max (Nat.size m) (Nat.size n)) := by ring
      _ = 2 ^ (max (Nat.size m) (Nat.size n) + 1) := by ring
  exact ((Nat.size_le (m := m + n) (n := max (Nat.size m) (Nat.size n) + 1)).mpr hsum')

theorem AdversarialBco.Bit.Transfer.len_sub_le (a b : ℤ) : len (a - b) ≤ max (len a) (len b) + 1 := by
  unfold len
  have h := Int.natAbs_sub_le a b
  have hsize := Nat.size_le_size h
  have hmax := nat_size_add_le (Int.natAbs a) (Int.natAbs b)
  exact le_trans hsize hmax

theorem AdversarialBco.Bit.Transfer.spaceLE_of_support {d : ℕ} (s : State d) (S : Finset ℤ) (f : ℤ → ℕ)
    (h : ∀ c, s.mem c ≠ 0 → c ∈ S ∧ len c + len (s.mem c) ≤ f c) : SpaceLE s (∑ c ∈ S, f c : ℕ) := by
  intro F hF
  have h_sub : F ⊆ S := by
    intro c hc
    exact (h c (hF c hc)).1
  have h_pointwise : ∀ c ∈ F, (len c + len (s.mem c) : ℕ) ≤ f c := by
    intro c hc
    exact (h c (hF c hc)).2
  have h_sum1 : (∑ c ∈ F, (len c + len (s.mem c)) : ℕ) ≤ (∑ c ∈ F, f c : ℕ) :=
    Finset.sum_le_sum h_pointwise
  have h_sum2 : (∑ c ∈ F, f c : ℕ) ≤ (∑ c ∈ S, f c : ℕ) :=
    Finset.sum_le_sum_of_subset h_sub
  exact_mod_cast h_sum1.trans h_sum2

theorem AdversarialBco.Bit.Transfer.spaceLE_update {d : ℕ} (s s' : State d) (c v : ℤ) (B : ℝ)
    (hm : s'.mem = Function.update s.mem c v) (h : SpaceLE s B) :
    SpaceLE s' (B + (len c + len v : ℕ)) := by
  intro F hF
  by_cases hc : c ∈ F
  · -- case c ∈ F
    have h_erase : ∀ x ∈ F.erase c, s.mem x ≠ 0 := by
      intro x hx
      have hx' := hF x (Finset.mem_of_mem_erase hx)
      have hx_ne_c := Finset.ne_of_mem_erase hx
      rw [hm, Function.update_of_ne hx_ne_c] at hx'
      exact hx'
    have hsum_erase := h (F.erase c) h_erase
    -- hsum_erase : ((∑ x ∈ F.erase c, (len x + len (s.mem x)) : ℕ) : ℝ) ≤ B
    have hsum_eq : (∑ x ∈ F, (len x + len (s'.mem x)) : ℕ) =
                  (∑ x ∈ F.erase c, (len x + len (s.mem x)) : ℕ) + (len c + len v : ℕ) := by
      calc
        (∑ x ∈ F, (len x + len (s'.mem x)) : ℕ) =
          ((∑ x ∈ F.erase c, (len x + len (s'.mem x))) + (len c + len (s'.mem c)) : ℕ) := by
          rw [← Finset.sum_erase_add F (fun x => (len x + len (s'.mem x) : ℕ)) (a := c) hc]
        _ = ((∑ x ∈ F.erase c, (len x + len (s.mem x))) + (len c + len v) : ℕ) := by
          have hmem_erase : ∀ x ∈ F.erase c, s'.mem x = s.mem x := by
            intro x hx
            have hx_ne_c := Finset.ne_of_mem_erase hx
            rw [hm, Function.update_of_ne hx_ne_c]
          have hsum_erase_eq : (∑ x ∈ F.erase c, (len x + len (s'.mem x))) = (∑ x ∈ F.erase c, (len x + len (s.mem x))) :=
            Finset.sum_congr rfl (fun x hx => by rw [hmem_erase x hx])
          rw [hsum_erase_eq, hm]
          simp
    have hsum_eq' : ((∑ x ∈ F, (len x + len (s'.mem x)) : ℕ) : ℝ) =
                   ((∑ x ∈ F.erase c, (len x + len (s.mem x)) : ℕ) : ℝ) + ((len c + len v : ℕ) : ℝ) := by
      exact_mod_cast hsum_eq
    rw [hsum_eq']
    linarith
  · -- case c ∉ F
    have h_erase : ∀ x ∈ F, s.mem x ≠ 0 := by
      intro x hx
      have hne := hF x hx
      rw [hm] at hne
      have hx_ne_c : x ≠ c := by
        intro heq; rw [heq] at hx; exact hc hx
      rw [Function.update_of_ne hx_ne_c] at hne
      exact hne
    have hsum := h F h_erase
    -- hsum : ((∑ x ∈ F, (len x + len (s.mem x)) : ℕ) : ℝ) ≤ B
    have hsum_eq : (∑ x ∈ F, (len x + len (s'.mem x)) : ℕ) = (∑ x ∈ F, (len x + len (s.mem x)) : ℕ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx_ne_c : x ≠ c := by
        intro heq; rw [heq] at hx; exact hc hx
      rw [hm, Function.update_of_ne hx_ne_c]
    have hsum_eq' : ((∑ x ∈ F, (len x + len (s'.mem x)) : ℕ) : ℝ) = ((∑ x ∈ F, (len x + len (s.mem x)) : ℕ) : ℝ) := by
      exact_mod_cast hsum_eq
    rw [hsum_eq']
    have h_nonneg : (0 : ℝ) ≤ ((len c + len v : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

theorem AdversarialBco.Bit.Transfer.space_step_le {d : ℕ} (P : List Instr) (w : World d) (s : State d) (B : ℝ)
    (h : SpaceLE s B) : SpaceLE (step P w s) (B + ((step P w s).cost - s.cost : ℝ)) := by
  have hup : ∀ (s' : State d) (c v : ℤ) (k : ℕ), s'.mem = Function.update s.mem c v → s'.cost = s.cost + k →
      len c + len v ≤ k → SpaceLE s' (B + ((s'.cost : ℝ) - s.cost)) := fun s' c v k hm hc hk => by
    have h1 := AdversarialBco.Bit.Transfer.spaceLE_update s s' c v B hm h
    have h2 : ((len c + len v : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    intro F hF
    refine (h1 F hF).trans ?_
    rw [hc]; push_cast at h1 h2 ⊢; linarith
  have hsame : ∀ (s' : State d) (k : ℕ), s'.mem = s.mem → s'.cost = s.cost + k →
      SpaceLE s' (B + ((s'.cost : ℝ) - s.cost)) := fun s' k hm hc F hF => by
    have h1 := h F (by simpa [hm] using hF)
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    simp only [hm]
    rw [hc]; push_cast at h1 h2 ⊢; linarith
  have hmul : ∀ x y : ℕ, x + y + 1 ≤ (x + 1) * (y + 1) := fun x y => by
    have : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
    omega
  unfold step
  split
  · exact hsame s 0 rfl rfl
  · split
    · exact hup _ _ _ _ rfl rfl (by omega)
    · rename_i dst a b _
      exact hup _ _ _ _ rfl rfl (by have := AdversarialBco.Bit.Transfer.len_add_le (s.mem a) (s.mem b); omega)
    · rename_i dst a b _
      exact hup _ _ _ _ rfl rfl (by have := AdversarialBco.Bit.Transfer.len_sub_le (s.mem a) (s.mem b); omega)
    · rename_i dst a b _
      refine hup _ _ _ _ rfl rfl ?_
      have := AdversarialBco.Bit.Transfer.len_mul_le (s.mem a) (s.mem b)
      have := hmul (len (s.mem a)) (len (s.mem b))
      omega
    · rename_i dst a b _
      refine hup _ _ _ _ rfl rfl ?_
      have := AdversarialBco.Bit.Transfer.len_ediv_le (s.mem a) (s.mem b)
      have := hmul (len (s.mem a)) (len (s.mem b))
      omega
    · exact hup _ _ _ _ rfl rfl (by omega)
    · exact hup _ _ _ _ rfl rfl (by omega)
    · exact hsame _ _ rfl rfl
    · exact hsame _ _ rfl rfl
    · rename_i dst cnt _
      exact hup _ _ _ _ rfl rfl (by have := AdversarialBco.Bit.Transfer.len_readCoins_le w.cs s.coins (s.mem cnt).toNat; omega)
    · exact hsame _ _ rfl rfl
    · exact hup _ _ _ _ rfl rfl (by omega)

theorem AdversarialBco.Bit.Transfer.seg_driver {α : Type} (f : α → α) (rd cost : α → ℕ) (Sp Start : α → Prop)
    (n Bp Bc : ℕ) (hmono : ∀ a, rd a ≤ rd (f a) ∧ cost a ≤ cost (f a)) (a0 : α) (j0 : ℕ)
    (h0 : Start (f^[j0] a0)) (hc0 : cost (f^[j0] a0) ≤ cost a0 + Bp) (hsp0 : ∀ i ≤ j0, Sp (f^[i] a0))
    (hseg : ∀ a, Start a → rd a < n → ∃ j, Start (f^[j] a) ∧ rd a < rd (f^[j] a) ∧
      cost (f^[j] a) ≤ cost a + Bc ∧ ∀ i ≤ j, Sp (f^[i] a)) :
    (∀ k, rd (f^[k] a0) < n → ∃ j, rd (f^[k] a0) < rd (f^[k + j] a0) ∧
        cost (f^[k + j] a0) ≤ cost (f^[k] a0) + (Bp + 2 * Bc)) ∧
      ∀ k, rd (f^[k] a0) < n → Sp (f^[k] a0) := by
  classical
  have hmono_rd : ∀ a, rd a ≤ rd (f a) := λ a => (hmono a).1
  have hmono_cost : ∀ a, cost a ≤ cost (f a) := λ a => (hmono a).2
  have h_succ_apply' : ∀ (a : α) (n : ℕ), f (f^[n] a) = f^[n+1] a := by
    intro a n; rw [Function.iterate_succ_apply']
  have hmono_rd_iter : ∀ (a : α) (j : ℕ), rd a ≤ rd (f^[j] a) := by
    intro a j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hmono_rd (f^[j] a)
      rw [h_succ_apply'] at h
      exact le_trans ih h
  have hmono_rd_iter' : ∀ (a : α) (i j : ℕ), rd (f^[i] a) ≤ rd (f^[i + j] a) := by
    intro a i j
    have h := hmono_rd_iter (f^[i] a) j
    rw [← Function.iterate_add_apply f j i a, add_comm j i] at h
    exact h
  have hmono_cost_iter : ∀ (a : α) (j : ℕ), cost a ≤ cost (f^[j] a) := by
    intro a j
    induction j with
    | zero => rfl
    | succ j ih =>
      have h := hmono_cost (f^[j] a)
      rw [h_succ_apply'] at h
      exact le_trans ih h
  have hmono_cost_iter' : ∀ (a : α) (i j : ℕ), cost (f^[i] a) ≤ cost (f^[i + j] a) := by
    intro a i j
    have h := hmono_cost_iter (f^[i] a) j
    rw [← Function.iterate_add_apply f j i a, add_comm j i] at h
    exact h
  let seg_j (a : α) (hStart : Start a) (hrd : rd a < n) : ℕ :=
    Classical.choose (hseg a hStart hrd)
  have seg_j_spec (a : α) (hStart : Start a) (hrd : rd a < n) :
      Start (f^[seg_j a hStart hrd] a) ∧
      rd a < rd (f^[seg_j a hStart hrd] a) ∧
      cost (f^[seg_j a hStart hrd] a) ≤ cost a + Bc ∧
      ∀ i ≤ seg_j a hStart hrd, Sp (f^[i] a) :=
    Classical.choose_spec (hseg a hStart hrd)
  have h_add_apply : ∀ (a : α) (i j : ℕ), f^[i + j] a = f^[i] (f^[j] a) :=
    λ a i j => Function.iterate_add_apply f i j a
  have hmono_rd_iter'_zero : ∀ (a : α) (j : ℕ), rd a ≤ rd (f^[j] a) := by
    intro a j
    simpa [Function.iterate_zero, add_zero] using hmono_rd_iter' a 0 j
  have hmono_cost_iter'_zero : ∀ (a : α) (j : ℕ), cost a ≤ cost (f^[j] a) := by
    intro a j
    simpa [Function.iterate_zero, add_zero] using hmono_cost_iter' a 0 j
  have hsp : ∀ k, rd (f^[k] a0) < n → Sp (f^[k] a0) := by
    intro k hrd_k
    by_cases hk_le_j0 : k ≤ j0
    · exact hsp0 k hk_le_j0
    · have hj0_le_k : j0 ≤ k := by omega
      let starts : Finset ℕ := Finset.filter (λ i => Start (f^[i] a0)) (Finset.Icc j0 k)
      have hstarts_nonempty : starts.Nonempty := by
        refine ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hj0_le_k⟩, h0⟩⟩
      obtain ⟨i_star, hi_star_mem, hi_star_max⟩ : ∃ i ∈ starts, ∀ b ∈ starts, b ≤ i :=
        ⟨starts.max' hstarts_nonempty, Finset.max'_mem _ _, fun b hb => Finset.le_max' starts b hb⟩
      rcases Finset.mem_filter.mp hi_star_mem with ⟨hi_star_Icc, hi_star_Start⟩
      rcases Finset.mem_Icc.mp hi_star_Icc with ⟨hj0_le_i, hi_le_k⟩
      have hrd_i : rd (f^[i_star] a0) < n := by
        have hle : rd (f^[i_star] a0) ≤ rd (f^[k] a0) := by
          have h_eq : f^[k] a0 = f^[k - i_star] (f^[i_star] a0) := by
            rw [← h_add_apply, Nat.sub_add_cancel hi_le_k]
          rw [h_eq]
          exact hmono_rd_iter'_zero (f^[i_star] a0) (k - i_star)
        exact lt_of_le_of_lt hle hrd_k
      obtain ⟨j, hj_start, hj_rd, hj_cost, hj_sp⟩ := hseg (f^[i_star] a0) hi_star_Start hrd_i
      by_cases hk_lt_i_plus_j : k < i_star + j
      · have hpos : k - i_star ≤ j := by omega
        have h_eq : f^[k] a0 = f^[k - i_star] (f^[i_star] a0) := by
          rw [← h_add_apply, Nat.sub_add_cancel (by omega : i_star ≤ k)]
        rw [h_eq]
        exact hj_sp (k - i_star) hpos
      · have h_start_at_i_plus_j : Start (f^[i_star + j] a0) := by
          rw [add_comm i_star j, h_add_apply a0 j i_star]
          exact hj_start
        have hi_plus_j_le_k : i_star + j ≤ k := by omega
        have hi_plus_j_ge_j0 : j0 ≤ i_star + j := by omega
        have h_mem : i_star + j ∈ starts :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi_plus_j_ge_j0, hi_plus_j_le_k⟩,
            h_start_at_i_plus_j⟩
        have h_le := hi_star_max (i_star + j) h_mem
        have hj_zero : j = 0 := by omega
        subst hj_zero
        simp at hj_rd
  have hgrowth : ∀ k, rd (f^[k] a0) < n → ∃ j, rd (f^[k] a0) < rd (f^[k + j] a0) ∧
      cost (f^[k + j] a0) ≤ cost (f^[k] a0) + (Bp + 2 * Bc) := by
    intro k hrd_k
    by_cases hk_le_j0 : k ≤ j0
    · by_cases hrd_lt : rd (f^[k] a0) < rd (f^[j0] a0)
      · have h_eq : k + (j0 - k) = j0 := by omega
        refine ⟨j0 - k, ?_, ?_⟩
        · rw [h_eq]; exact hrd_lt
        · rw [h_eq]
          have h_cost_a0_le : cost a0 ≤ cost (f^[k] a0) := by
            simpa [Function.iterate_zero] using hmono_cost_iter a0 k
          have h_cost_le : cost (f^[j0] a0) ≤ cost (f^[k] a0) + Bp :=
            le_trans hc0 (Nat.add_le_add_right h_cost_a0_le Bp)
          exact le_trans h_cost_le (by omega)
      · have hrd_eq : rd (f^[k] a0) = rd (f^[j0] a0) := by
          have hle1 : rd (f^[k] a0) ≤ rd (f^[j0] a0) := by
            have h_eq : f^[j0] a0 = f^[j0 - k] (f^[k] a0) := by
              rw [← h_add_apply, Nat.sub_add_cancel hk_le_j0]
            rw [h_eq]
            exact hmono_rd_iter'_zero (f^[k] a0) (j0 - k)
          have hle2 : rd (f^[j0] a0) ≤ rd (f^[k] a0) := by omega
          exact le_antisymm hle1 hle2
        have hrd_j0 : rd (f^[j0] a0) < n := by rwa [← hrd_eq]
        obtain ⟨j, hj_start, hj_rd, hj_cost, hj_sp⟩ := hseg (f^[j0] a0) h0 hrd_j0
        have h_eq : f^[k + ((j0 - k) + j)] a0 = f^[j] (f^[j0] a0) := by
          rw [← Function.iterate_add_apply]; congr 1; omega
        refine ⟨(j0 - k) + j, ?_, ?_⟩
        · rw [h_eq, hrd_eq]; exact hj_rd
        · rw [h_eq]
          have h_cost1 : cost (f^[j] (f^[j0] a0)) ≤ cost (f^[j0] a0) + Bc := hj_cost
          have h_cost_a0_le : cost a0 ≤ cost (f^[k] a0) := by
            simpa [Function.iterate_zero] using hmono_cost_iter a0 k
          have h_cost2 : cost (f^[j0] a0) ≤ cost (f^[k] a0) + Bp :=
            le_trans hc0 (Nat.add_le_add_right h_cost_a0_le Bp)
          omega
    · have hj0_le_k : j0 ≤ k := by omega
      let starts : Finset ℕ := Finset.filter (λ i => Start (f^[i] a0)) (Finset.Icc j0 k)
      have hstarts_nonempty : starts.Nonempty := by
        refine ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hj0_le_k⟩, h0⟩⟩
      obtain ⟨i_star, hi_star_mem, hi_star_max⟩ : ∃ i ∈ starts, ∀ b ∈ starts, b ≤ i :=
        ⟨starts.max' hstarts_nonempty, Finset.max'_mem _ _, fun b hb => Finset.le_max' starts b hb⟩
      rcases Finset.mem_filter.mp hi_star_mem with ⟨hi_star_Icc, hi_star_Start⟩
      rcases Finset.mem_Icc.mp hi_star_Icc with ⟨hj0_le_i, hi_le_k⟩
      have hrd_i : rd (f^[i_star] a0) < n := by
        have hle : rd (f^[i_star] a0) ≤ rd (f^[k] a0) := by
          have h_eq : f^[k] a0 = f^[k - i_star] (f^[i_star] a0) := by
            rw [← h_add_apply, Nat.sub_add_cancel hi_le_k]
          rw [h_eq]
          exact hmono_rd_iter'_zero (f^[i_star] a0) (k - i_star)
        exact lt_of_le_of_lt hle hrd_k
      obtain ⟨j, hj_start, hj_rd, hj_cost, hj_sp⟩ := hseg (f^[i_star] a0) hi_star_Start hrd_i
      by_cases hi_eq_k : i_star = k
      · subst hi_eq_k
        refine ⟨j, ?_, ?_⟩
        · rw [add_comm, h_add_apply]; exact hj_rd
        · rw [add_comm, h_add_apply]
          omega
      · have hi_lt_k : i_star < k := Nat.lt_of_le_of_ne hi_le_k hi_eq_k
        by_cases hrd_lt : rd (f^[k] a0) < rd (f^[i_star + j] a0)
        · have hk_lt_i_plus_j : k < i_star + j := by
            by_contra! H
            have h_start_at_i_plus_j : Start (f^[i_star + j] a0) := by
              rw [add_comm i_star j, h_add_apply a0 j i_star]
              exact hj_start
            have hi_plus_j_le_k : i_star + j ≤ k := H
            have hi_plus_j_ge_j0 : j0 ≤ i_star + j := by omega
            have h_mem : i_star + j ∈ starts :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi_plus_j_ge_j0, hi_plus_j_le_k⟩,
                h_start_at_i_plus_j⟩
            have h_le := hi_star_max (i_star + j) h_mem
            have hj_zero : j = 0 := by omega
            subst hj_zero
            simp at hj_rd
          have h_eq : k + ((i_star + j) - k) = i_star + j := by omega
          refine ⟨(i_star + j) - k, ?_, ?_⟩
          · rw [h_eq]; exact hrd_lt
          · rw [h_eq]
            have h_cost1 : cost (f^[i_star + j] a0) ≤ cost (f^[i_star] a0) + Bc := by
              rw [add_comm i_star j, h_add_apply a0 j i_star]
              exact hj_cost
            have h_cost2 : cost (f^[i_star] a0) ≤ cost (f^[k] a0) := by
              have h_eq' : f^[k] a0 = f^[k - i_star] (f^[i_star] a0) := by
                rw [← h_add_apply, Nat.sub_add_cancel hi_le_k]
              rw [h_eq']
              exact hmono_cost_iter'_zero (f^[i_star] a0) (k - i_star)
            omega
        · have hk_le : k ≤ i_star + j := by
            by_contra! H
            have h_start_at : Start (f^[i_star + j] a0) := by
              rw [add_comm i_star j, h_add_apply a0 j i_star]; exact hj_start
            have h_mem : i_star + j ∈ starts :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h_start_at⟩
            have h_le := hi_star_max (i_star + j) h_mem
            have hj_zero : j = 0 := by omega
            subst hj_zero
            simp at hj_rd
          have hrd_eq : rd (f^[k] a0) = rd (f^[i_star + j] a0) := by
            have hle1 : rd (f^[k] a0) ≤ rd (f^[i_star + j] a0) := by
              have h_eq : f^[i_star + j] a0 = f^[i_star + j - k] (f^[k] a0) := by
                rw [← h_add_apply, Nat.sub_add_cancel (by omega : k ≤ i_star + j)]
              rw [h_eq]
              exact hmono_rd_iter'_zero (f^[k] a0) (i_star + j - k)
            have hle2 : rd (f^[i_star + j] a0) ≤ rd (f^[k] a0) := by omega
            exact le_antisymm hle1 hle2
          have hrd_i_plus_j : rd (f^[i_star + j] a0) < n := by rwa [← hrd_eq]
          have h_start_next : Start (f^[i_star + j] a0) := by
            rw [add_comm i_star j, h_add_apply a0 j i_star]
            exact hj_start
          obtain ⟨j', hj'_start, hj'_rd, hj'_cost, hj'_sp⟩ := hseg (f^[i_star + j] a0) h_start_next hrd_i_plus_j
          have e' : f^[k + ((i_star + j - k) + j')] a0 = f^[j'] (f^[i_star + j] a0) := by
            rw [← Function.iterate_add_apply]; congr 1; omega
          refine ⟨(i_star + j - k) + j', ?_, ?_⟩
          · rw [e', hrd_eq]
            exact hj'_rd
          · rw [e']
            have h_cost_i : cost (f^[i_star + j] a0) ≤ cost (f^[i_star] a0) + Bc := by
              rw [add_comm i_star j, h_add_apply a0 j i_star]
              exact hj_cost
            have h_cost_k : cost (f^[i_star] a0) ≤ cost (f^[k] a0) := by
              have h_eq' : f^[k] a0 = f^[k - i_star] (f^[i_star] a0) := by
                rw [← h_add_apply, Nat.sub_add_cancel hi_le_k]
              rw [h_eq']
              exact hmono_cost_iter'_zero (f^[i_star] a0) (k - i_star)
            omega
  exact And.intro hgrowth hsp
