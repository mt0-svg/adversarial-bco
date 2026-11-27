/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriC

@[expose] public section

/-!
# TRI-M, lemmas of the integer model

Polynomial bounds of the constants, the cleared rows as rationals, the magnitude of the composition of stages, the
bounds of `qn` and of the scan.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.pow_triJaQ_le {d : ℕ} (hd : 1 ≤ d) : 2 ^ triJaQ d ≤ 2 ^ 11 * d ^ 2 := by
  have htriSQ_low := (AdversarialBco.Bit.TriM.triSQ_bounds d).1
  have htriSQ_high := (AdversarialBco.Bit.TriM.triSQ_bounds d).2
  have hdpos : 0 < d := by omega
  set n := 9 * d * triSQ d with hn
  have hn_gt_one : 1 < n := by
    have : 1 ≤ triSQ d := by omega
    nlinarith
  have hclog_lt : 2 ^ ((Nat.clog 2 n).pred) < n :=
    Nat.pow_pred_clog_lt_self (by norm_num) hn_gt_one
  have hpow_le : 2 ^ (Nat.clog 2 n) ≤ 2 * 2 ^ ((Nat.clog 2 n).pred) := by
    by_cases hk : Nat.clog 2 n = 0
    · rw [hk]
      norm_num
    · have hkpos : 0 < Nat.clog 2 n := Nat.pos_of_ne_zero hk
      have hsucc : (Nat.clog 2 n).pred.succ = Nat.clog 2 n := Nat.succ_pred_eq_of_pos hkpos
      have heq : 2 ^ (Nat.clog 2 n) = 2 * 2 ^ ((Nat.clog 2 n).pred) := by
        calc
          2 ^ (Nat.clog 2 n) = 2 ^ ((Nat.clog 2 n).pred.succ) := by rw [hsucc]
          _ = 2 ^ (Nat.clog 2 n).pred * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (Nat.clog 2 n).pred := by rw [mul_comm]
      exact le_of_eq heq
  have h_lt : 2 ^ (Nat.clog 2 n) < 2 * n := by
    apply lt_of_le_of_lt hpow_le
    have := Nat.mul_lt_mul_of_pos_left hclog_lt (by norm_num : 0 < 2)
    omega
  have h_triSQ_bound : triSQ d ≤ 7 * (d + 10) := htriSQ_high
  have h_n_bound : n ≤ 693 * d ^ 2 := by
    have h_add : d + 10 ≤ 11 * d := by omega
    calc
      n = 9 * d * triSQ d := rfl
      _ ≤ 9 * d * (7 * (d + 10)) := Nat.mul_le_mul_left (9 * d) h_triSQ_bound
      _ ≤ 9 * d * (7 * (11 * d)) := Nat.mul_le_mul_left (9 * d) (Nat.mul_le_mul_left 7 h_add)
      _ = 693 * d ^ 2 := by ring
  have h_final : 2 * n ≤ 2 ^ 11 * d ^ 2 := by
    calc
      2 * n ≤ 2 * (693 * d ^ 2) := Nat.mul_le_mul_left 2 h_n_bound
      _ = 1386 * d ^ 2 := by ring
      _ ≤ 2048 * d ^ 2 := Nat.mul_le_mul_right (d ^ 2) (by norm_num)
      _ = 2 ^ 11 * d ^ 2 := by norm_num
  unfold triJaQ
  rw [← hn]
  omega

theorem AdversarialBco.Bit.TriM.eloI_le {d : ℕ} (hd : 1 ≤ d) : eloI d ≤ 2 ^ 112 * d ^ 14 := by
  set L := triLh (triSQ d) with hL
  have h258 : 258986112 ≤ 2 ^ 28 := by norm_num
  have hL_le : L ≤ 2 ^ L := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow_sub : 2 ^ L - 1 ≤ 2 ^ L := Nat.sub_le _ _
  have hpow_bound : 2 ^ L ≤ 2 ^ 42 * d ^ 6 := pow_triLh_le hd
  calc
    eloI d = 258986112 * d ^ 2 * L * (2 ^ L - 1) := rfl
    _ ≤ 2 ^ 28 * d ^ 2 * (2 ^ L) * (2 ^ L) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul h258 (le_refl _)) hL_le)
        hpow_sub
    _ = 2 ^ 28 * d ^ 2 * ((2 ^ L) ^ 2) := by ring
    _ ≤ 2 ^ 28 * d ^ 2 * ((2 ^ 42 * d ^ 6) ^ 2) :=
      Nat.mul_le_mul_left (2 ^ 28 * d ^ 2) (Nat.pow_le_pow_left hpow_bound 2)
    _ = 2 ^ 28 * d ^ 2 * (2 ^ 84 * d ^ 12) := by ring
    _ = 2 ^ 112 * d ^ 14 := by ring

theorem AdversarialBco.Bit.TriM.triKgQ_le {d : ℕ} (hd : 1 ≤ d) : triKgQ d ≤ 2 ^ 154 * d ^ 21 := by
  rw [triKgQ_eq hd]
  have hL := pow_triLa_le hd
  have hE := eloI_le hd
  have hs := (triSQ_bounds d).1
  have hL10 : 10 ≤ triLa (triSQ d) := by
    unfold triLa
    have : 16 ≤ triSQ d ^ 2 := by nlinarith
    omega
  have hb : bI d ≤ 2 ^ 32 * d ^ 4 := by
    unfold bI
    obtain ⟨k, hk⟩ : ∃ k, triLa (triSQ d) = k + 10 := ⟨_, (Nat.sub_add_cancel hL10).symm⟩
    rw [hk, Nat.add_sub_cancel]
    rw [hk, pow_add] at hL
    have h10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    rw [h10] at hL
    omega
  have hk : kgN d ≤ 2 ^ 153 * d ^ 21 := by
    unfold kgN
    calc 16 * bI d * (d + 1) * d * (8 * d + 2) * eloI d
        ≤ 16 * (2 ^ 32 * d ^ 4) * (2 * d) * d * (10 * d) * (2 ^ 112 * d ^ 14) := by
          gcongr <;> omega
      _ = 320 * 2 ^ 144 * d ^ 21 := by ring
      _ ≤ 2 ^ 153 * d ^ 21 := by gcongr; norm_num
  have hq : (kgN d + 19999) / 20000 ≤ kgN d + 1 := by omega
  have hc : Nat.clog 2 ((kgN d + 19999) / 20000) ≤ kgN d + 1 :=
    le_trans (Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_two_pow_self))) hq
  have hd21 : 1 ≤ d ^ 21 := Nat.one_le_pow _ _ hd
  have : 2 ^ 153 * d ^ 21 + 2 ≤ 2 ^ 154 * d ^ 21 := by
    have : (2 : ℕ) ^ 154 = 2 * 2 ^ 153 := by norm_num
    rw [this]; nlinarith
  omega



theorem AdversarialBco.Bit.TriM.d2N_le {d : ℕ} (hd : 1 ≤ d) : d2N d ≤ 2 ^ 90 * d ^ 14 := by
  have hSQ := triSQ_bounds d
  rcases hSQ with ⟨hSQ4, hSQ7⟩
  have hLle := pow_triLa_le hd
  have hja_le := pow_triJaQ_le hd
  set L := triLa (triSQ d) with hLdef
  set ja := triJaQ d with hjadef
  -- Prove L ≥ 10 from triSQ d ≥ 4
  have hLge10 : 10 ≤ L := by
    rw [hLdef]
    have hsq : 16 ≤ (triSQ d) ^ 2 := Nat.pow_le_pow_left hSQ4 2
    have hdiv : 11 ≤ 5 * (triSQ d) ^ 2 / 7 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 7)]
      nlinarith
    exact Nat.le_trans (by norm_num : 10 ≤ 11) hdiv
  -- Bound rI d: rI d = 2^(L-3) ≤ 2^L
  have hrI_le : rI d ≤ 2 ^ L := by
    rw [rI]
    have hsub : L - 3 ≤ L := Nat.sub_le _ _
    exact Nat.pow_le_pow_right (by norm_num) hsub
  -- Bound bI d: bI d = 161 * 2^(L-10) ≤ 1024 * 2^(L-10) = 2^L
  have hbI_le : bI d ≤ 2 ^ L := by
    rw [bI]
    have h : 161 * 2 ^ (L - 10) ≤ 1024 * 2 ^ (L - 10) :=
      Nat.mul_le_mul_right _ (by norm_num : 161 ≤ 1024)
    have h_eq : 1024 * 2 ^ (L - 10) = 2 ^ L := by
      have h1024 : (1024 : ℕ) = 2 ^ 10 := by norm_num
      rw [h1024, mul_comm, ← pow_add, Nat.sub_add_cancel hLge10]
    rw [h_eq] at h
    exact h
  -- Bound 4^ja = (2^ja)^2 ≤ (2^11 * d^2)^2 = 2^22 * d^4
  have h4ja_le : 4 ^ ja ≤ 2 ^ 22 * d ^ 4 := by
    have h2ja : 2 ^ ja ≤ 2 ^ 11 * d ^ 2 := hja_le
    have hsq : (2 ^ ja) ^ 2 ≤ (2 ^ 11 * d ^ 2) ^ 2 := Nat.pow_le_pow_left h2ja 2
    have h_eq : 4 ^ ja = (2 ^ ja) ^ 2 := by
      calc
        4 ^ ja = ((2:ℕ)^2) ^ ja := by norm_num
        _ = (2 ^ ja) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
    rw [h_eq]
    -- Now we need (2^ja)^2 ≤ 2^22 * d^4
    -- From hsq: (2^ja)^2 ≤ (2^11 * d^2)^2 = 2^22 * (d^2)^2 = 2^22 * d^4
    have h_sq_eq : (2 ^ 11 * d ^ 2) ^ 2 = 2 ^ 22 * d ^ 4 := by
      push_cast
      ring
    rw [h_sq_eq] at hsq
    exact hsq
  -- Bound (d-1) ≤ d
  have hd_sub : d - 1 ≤ d := Nat.sub_le _ _
  -- Bound (bI d * 2^ja - 1)^2 ≤ (bI d * 2^ja)^2
  have h_sq_sub : (bI d * 2 ^ ja - 1) ^ 2 ≤ (bI d * 2 ^ ja) ^ 2 :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  rw [d2N]
  -- Now bound each term of d2N d
  have hterm1 : 4 * d * rI d ^ 2 * 4 ^ ja ≤ 2 ^ 88 * d ^ 13 := by
    have h1 : 4 * d * rI d ^ 2 ≤ 4 * d * (2 ^ L) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrI_le 2)
    have h2 : 4 * d * rI d ^ 2 * 4 ^ ja ≤ 4 * d * (2 ^ L) ^ 2 * 4 ^ ja :=
      Nat.mul_le_mul h1 (le_refl _)
    have h3 : 4 * d * (2 ^ L) ^ 2 * 4 ^ ja ≤ 4 * d * (2 ^ L) ^ 2 * (2 ^ 22 * d ^ 4) :=
      Nat.mul_le_mul (le_refl _) h4ja_le
    -- Now rewrite the goal as ((4*d) * (2^L)^2 * (2^22)) * d^4 ≤ ((4*d) * (2^32*d^4)^2 * (2^22)) * d^4
    have h_inner : 4 * d * (2 ^ L) ^ 2 * (2 ^ 22) ≤ 4 * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLle 2)) (le_refl _)
    have h4 : 4 * d * (2 ^ L) ^ 2 * (2 ^ 22) * d ^ 4 ≤ 4 * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * d ^ 4 :=
      Nat.mul_le_mul h_inner (le_refl _)
    calc
      4 * d * rI d ^ 2 * 4 ^ ja ≤ 4 * d * (2 ^ L) ^ 2 * 4 ^ ja := h2
      _ ≤ 4 * d * (2 ^ L) ^ 2 * (2 ^ 22 * d ^ 4) := h3
      _ = 4 * d * (2 ^ L) ^ 2 * (2 ^ 22) * (d ^ 4) := by ring
      _ ≤ 4 * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * (d ^ 4) := h4
      _ = (2 ^ 88 * d ^ 13 : ℕ) := by
        push_cast
        ring
  have hterm2 : d * (bI d * 2 ^ ja - 1) ^ 2 ≤ 2 ^ 86 * d ^ 13 := by
    have h_sq_eq : (2 ^ ja) ^ 2 = 4 ^ ja := by
      calc
        (2 ^ ja) ^ 2 = ((2:ℕ)^2) ^ ja := by rw [← pow_mul, mul_comm, pow_mul]
        _ = 4 ^ ja := by norm_num
    have h1 : d * (bI d * 2 ^ ja - 1) ^ 2 ≤ d * (bI d * 2 ^ ja) ^ 2 :=
      Nat.mul_le_mul_left _ h_sq_sub
    have h2 : d * (bI d * 2 ^ ja) ^ 2 = d * (bI d ^ 2) * ((2 ^ ja) ^ 2) := by ring
    have h3 : d * (bI d ^ 2) * ((2 ^ ja) ^ 2) ≤ d * ((2 ^ L) ^ 2) * ((2 ^ ja) ^ 2) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbI_le 2)) (le_refl _)
    have h4 : d * ((2 ^ L) ^ 2) * ((2 ^ ja) ^ 2) = d * ((2 ^ L) ^ 2) * (4 ^ ja) := by rw [h_sq_eq]
    have h5 : d * ((2 ^ L) ^ 2) * (4 ^ ja) ≤ d * ((2 ^ L) ^ 2) * (2 ^ 22 * d ^ 4) :=
      Nat.mul_le_mul (le_refl _) h4ja_le
    have h_inner : d * (2 ^ L) ^ 2 * (2 ^ 22) ≤ d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLle 2)) (le_refl _)
    have h6 : d * (2 ^ L) ^ 2 * (2 ^ 22) * d ^ 4 ≤ d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * d ^ 4 :=
      Nat.mul_le_mul h_inner (le_refl _)
    calc
      d * (bI d * 2 ^ ja - 1) ^ 2 ≤ d * (bI d * 2 ^ ja) ^ 2 := h1
      _ = d * (bI d ^ 2) * ((2 ^ ja) ^ 2) := h2
      _ ≤ d * ((2 ^ L) ^ 2) * ((2 ^ ja) ^ 2) := h3
      _ = d * ((2 ^ L) ^ 2) * (4 ^ ja) := h4
      _ ≤ d * ((2 ^ L) ^ 2) * (2 ^ 22 * d ^ 4) := h5
      _ = d * ((2 ^ L) ^ 2) * (2 ^ 22) * (d ^ 4) := by ring
      _ ≤ d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * (d ^ 4) := h6
      _ = (2 ^ 86 * d ^ 13 : ℕ) := by
        push_cast
        ring
  have hterm3 : 2 * d * (d - 1) * bI d ^ 2 * 4 ^ ja ≤ 2 ^ 87 * d ^ 14 := by
    have h1 : 2 * d * (d - 1) * bI d ^ 2 * 4 ^ ja ≤ 2 * d * d * bI d ^ 2 * 4 ^ ja := by
      -- Goal: (2*d*(d-1)*bI^2) * 4^ja ≤ (2*d*d*bI^2) * 4^ja
      apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hd_sub) (le_refl _)) (le_refl _)
    have h2 : 2 * d * d * (bI d ^ 2) * (4 ^ ja) ≤ 2 * d * d * ((2 ^ L) ^ 2) * (4 ^ ja) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left hbI_le 2)) (le_refl _)
    have h3 : 2 * d * d * ((2 ^ L) ^ 2) * (4 ^ ja) ≤ 2 * d * d * ((2 ^ L) ^ 2) * (2 ^ 22 * d ^ 4) := by
      apply Nat.mul_le_mul (le_refl _) h4ja_le
    have h_inner : 2 * d * d * (2 ^ L) ^ 2 * (2 ^ 22) ≤ 2 * d * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left hLle 2)) (le_refl _)
    have h4 : 2 * d * d * (2 ^ L) ^ 2 * (2 ^ 22) * d ^ 4 ≤ 2 * d * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * d ^ 4 :=
      Nat.mul_le_mul h_inner (le_refl _)
    calc
      2 * d * (d - 1) * bI d ^ 2 * 4 ^ ja ≤ 2 * d * d * bI d ^ 2 * 4 ^ ja := h1
      _ = 2 * d * d * (bI d ^ 2) * (4 ^ ja) := rfl
      _ ≤ 2 * d * d * ((2 ^ L) ^ 2) * (4 ^ ja) := h2
      _ ≤ 2 * d * d * ((2 ^ L) ^ 2) * (2 ^ 22 * d ^ 4) := h3
      _ = 2 * d * d * ((2 ^ L) ^ 2) * (2 ^ 22) * (d ^ 4) := by ring
      _ ≤ 2 * d * d * (2 ^ 32 * d ^ 4) ^ 2 * (2 ^ 22) * (d ^ 4) := h4
      _ = (2 ^ 87 * d ^ 14 : ℕ) := by
        push_cast
        ring
  -- Now sum the three bounds
  have hsum : 2 ^ 88 * d ^ 13 + 2 ^ 86 * d ^ 13 + 2 ^ 87 * d ^ 14 ≤ 2 ^ 90 * d ^ 14 := by
    have h_factor : (2^88 * d^13 + 2^86 * d^13 + 2^87 * d^14 : ℤ) = (2^86 * d^13 : ℤ) * (5 + 2*(d : ℤ)) := by
      ring
    have h_rhs : (2^90 * d^14 : ℤ) = (2^86 * d^13 : ℤ) * (16*(d : ℤ)) := by
      ring
    have h_ineq : (5 : ℤ) + 2*(d : ℤ) ≤ 16*(d : ℤ) := by
      have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      nlinarith
    have h_goal : (2^88 * d^13 + 2^86 * d^13 + 2^87 * d^14 : ℤ) ≤ (2^90 * d^14 : ℤ) := by
      rw [h_factor, h_rhs]
      apply mul_le_mul_of_nonneg_left h_ineq
      positivity
    exact_mod_cast h_goal
  -- Combine all bounds
  apply le_trans (add_le_add (add_le_add hterm1 hterm2) hterm3) hsum



theorem AdversarialBco.Bit.TriM.clipZ_mem (lo hi v : ℤ) (h : lo ≤ hi) : lo ≤ clipZ lo hi v ∧ clipZ lo hi v ≤ hi := by
  unfold clipZ
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem AdversarialBco.Bit.TriM.tzUpd_bound {d : ℕ} (c : DC) (X : PosZ d) (A Y : Fin d → ℤ) (Bb : ℤ)
    (hR : 0 ≤ c.R) (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al) (hAB : c.Al ≤ c.Bh) :
    (∀ i, |(tzUpd c X A Y Bb).1 i| ≤ c.Bh) ∧ (∀ i l, |(tzUpd c X A Y Bb).2 i l| ≤ c.Bh) ∧
    ∀ i, c.Al ≤ (tzUpd c X A Y Bb).2 i i := by
  have hBh_nonneg : 0 ≤ c.Bh := by linarith
  have hAl_le_Bh : c.Al ≤ c.Bh := hAB
  have hnegR_le_R : -c.R ≤ c.R := by linarith
  have hnegBh_le_Bh : -c.Bh ≤ c.Bh := by linarith
  have hnegR_le_Bh : -c.R ≤ c.Bh := by linarith
  unfold tzUpd
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp
    have hmem := clipZ_mem (-c.R) c.R (X.1 i - tzRMu A Bb c.PB i * c.Pj) hnegR_le_R
    have habs : |clipZ (-c.R) c.R (X.1 i - tzRMu A Bb c.PB i * c.Pj)| ≤ c.R :=
      abs_le.mpr ⟨hmem.1, hmem.2⟩
    linarith
  · intro i l
    simp
    split_ifs with hlt heq
    · -- l < i
      have hmem := clipZ_mem (-c.Bh) c.Bh (X.2 i l - tzRLow A Y Bb c.PB c.P2 i l * c.Pj) hnegBh_le_Bh
      have habs : |clipZ (-c.Bh) c.Bh (X.2 i l - tzRLow A Y Bb c.PB c.P2 i l * c.Pj)| ≤ c.Bh :=
        abs_le.mpr ⟨hmem.1, hmem.2⟩
      exact habs
    · -- l = i
      have hmem := clipZ_mem c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj) hAl_le_Bh
      have hlower : -c.Bh ≤ clipZ c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj) := by
        linarith
      have habs : |clipZ c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj)| ≤ c.Bh :=
        abs_le.mpr ⟨hlower, hmem.2⟩
      exact habs
    · -- l > i (else case)
      exact hBh_nonneg
  · intro i
    simp
    have hmem := clipZ_mem c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj) hAl_le_Bh
    exact hmem.1



theorem AdversarialBco.Bit.TriM.comp_eq {d : ℕ} (P : StZ d) (S : PosZ d) (Gc : ℕ) (hD : 0 < P.D) :
    pgCompQ (fun i => (P.mu i : ℚ) / P.D, fun i l => (P.T i l : ℚ) / P.D)
        (fun i => (S.1 i : ℚ) / 2 ^ Gc, fun i l => (S.2 i l : ℚ) / 2 ^ Gc) =
      (fun i => ((tzComp P S Gc).mu i : ℚ) / (tzComp P S Gc).D,
       fun i l => ((tzComp P S Gc).T i l : ℚ) / (tzComp P S Gc).D) := by
  have hD_ne : (P.D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have h2_ne : ((2 : ℚ) ^ Gc) ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)
  simp [pgCompQ, tzComp]
  refine Prod.ext ?_ ?_
  · simp
    funext i
    simp [Matrix.mulVec, dotProduct]
    field_simp [hD_ne, h2_ne]
    simp [Finset.mul_sum]
    field_simp [hD_ne, h2_ne]
    rw [← Finset.sum_div]
    field_simp [h2_ne]
  · simp
    ext i j
    field_simp [hD_ne, h2_ne]
    have hR : ((P.T * S.2) i j : ℚ) = ∑ x, (P.T i x : ℚ) * (S.2 x j : ℚ) := by
      simp [Matrix.mul_apply]
    rw [hR]
    have hL := Matrix.mul_apply (M := (fun i l => (P.T i l : ℚ) / (P.D : ℚ))) (N := (fun i l => (S.2 i l : ℚ) / ((2 : ℚ) ^ Gc))) (i := i) (k := j)
    rw [hL]
    simp [Finset.mul_sum]
    field_simp [hD_ne, h2_ne]


theorem AdversarialBco.Bit.TriM.avg_eq {d : ℕ} (r a b s : ℚ) (Vt : PosQ d → (Fin d → ℚ) → PosQ d)
    (y : ℕ → Fin d → ℚ) (Xs : ℕ → PosZ d) (G Ne : ℕ)
    (h : ∀ t, triIterQ r a b s Vt y t = (fun i => ((Xs t).1 i : ℚ) / 2 ^ G, fun i l => ((Xs t).2 i l : ℚ) / 2 ^ G)) :
    triAvgQ r a b s Vt y (2 ^ Ne) =
      (fun i => ((∑ t ∈ Finset.range (2 ^ Ne), Xs t).1 i : ℚ) / 2 ^ (G + Ne),
       fun i l => ((∑ t ∈ Finset.range (2 ^ Ne), Xs t).2 i l : ℚ) / 2 ^ (G + Ne)) := by
  dsimp [triAvgQ]
  simp [h]
  apply Prod.ext
  · ext i
    have hsmul := Prod.smul_fst (c := (2 ^ Ne : ℚ)⁻¹) (p := ∑ t ∈ Finset.range (2 ^ Ne),
      (fun i => ((Xs t).1 i : ℚ) / 2 ^ G, fun i l => ((Xs t).2 i l : ℚ) / 2 ^ G))
    have hsmul_i := congrArg (fun f : Fin d → ℚ => f i) hsmul
    apply hsmul_i.trans
    rw [Pi.smul_apply, smul_eq_mul, Prod.fst_sum, Finset.sum_apply]
    simp
    calc
      (2 ^ Ne : ℚ)⁻¹ * (∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).1 i : ℚ) / (2 ^ G : ℚ))
          = (2 ^ Ne : ℚ)⁻¹ * ((∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).1 i : ℚ)) / (2 ^ G : ℚ)) := by
            rw [Finset.sum_div]
      _ = ((∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).1 i : ℚ)) / ((2 ^ Ne : ℚ) * (2 ^ G : ℚ))) := by ring
      _ = (∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).1 i : ℚ)) / ((2 : ℚ) ^ (G + Ne)) := by
        rw [← pow_add, add_comm G Ne]
      _ = ((∑ x ∈ Finset.range (2 ^ Ne), (Xs x).1 i : ℤ) : ℚ) / ((2 : ℚ) ^ (G + Ne)) := by rw [Int.cast_sum]
      _ = ((∑ x ∈ Finset.range (2 ^ Ne), Xs x).1 i : ℚ) / ((2 : ℚ) ^ (G + Ne)) := by
        rw [Prod.fst_sum, Finset.sum_apply]
      _ = ((∑ x ∈ Finset.range (2 ^ Ne), Xs x).1 i : ℚ) / 2 ^ (G + Ne) := by norm_num
  · ext i l
    have hsmul := Prod.smul_snd (c := (2 ^ Ne : ℚ)⁻¹) (p := ∑ t ∈ Finset.range (2 ^ Ne),
      (fun i => ((Xs t).1 i : ℚ) / 2 ^ G, fun i l => ((Xs t).2 i l : ℚ) / 2 ^ G))
    have hsmul_il := congrArg (fun f : Matrix (Fin d) (Fin d) ℚ => f i l) hsmul
    apply hsmul_il.trans
    have h := Matrix.smul_apply (r := (2 ^ Ne : ℚ)⁻¹) (A := (∑ t ∈ Finset.range (2 ^ Ne),
      (fun i => ((Xs t).1 i : ℚ) / 2 ^ G, fun i l => ((Xs t).2 i l : ℚ) / 2 ^ G)).2) (i := i) (j := l)
    apply h.trans
    simp [smul_eq_mul, Prod.snd_sum, Matrix.sum_apply]
    have hsum := Finset.sum_div (s := Finset.range (2 ^ Ne)) (f := fun c => ((Xs c).2 i l : ℚ)) (a := (2 ^ G : ℚ))
    rw [← hsum]
    calc
      (2 ^ Ne : ℚ)⁻¹ * ((∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).2 i l : ℚ)) / (2 ^ G : ℚ))
          = ((∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).2 i l : ℚ)) / ((2 ^ Ne : ℚ) * (2 ^ G : ℚ))) := by ring
      _ = (∑ x ∈ Finset.range (2 ^ Ne), ((Xs x).2 i l : ℚ)) / ((2 : ℚ) ^ (G + Ne)) := by
        rw [← pow_add, add_comm G Ne]
