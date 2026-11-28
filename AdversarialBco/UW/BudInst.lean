/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.BudReg
public import AdversarialBco.UW.ParamT4U
public import AdversarialBco.Unified.BudInst

@[expose] public section

/-!
# Theorem BUD-W: the base constants of BL-OW at `(d, n, k, ρ)` as a `RegW`

`regW d n k ρ` reads the level constants of Theorem U at `k` (Unified/BudDefs.lean: `N_e = 2^k N_0`, `δe = 1/N_e`,
`Le = 36 ln N_e`, `2^{-p}`, `ê`, `2^{B/2}`, `Q = N_e^{1/40}`) and the reference's parameters at the scale `ρ.u`
(`parW d n ρ.u`: `λ`, `η`, `ε`, `ρ`, `R`, `κ_c = η κ λ κ₀`), the floor `L_f = 36 ln N_0`, the scale and the sure ranges
`b0`, `y0` of `ρ`. `reg_okW` proves `RegW.OK (regW d n k ρ)` from `RegimeW d n ρ` alone:
the level facts read only `N_e ≥ N_0 > 2^700` (`le40_of_gt`: `(360 ln N)^40 ≤ N` for every `N > 2^700`, Piece A's
`regime_Le40` with `N` free), the floor facts read `ε(u) ≤ 1/4` and `u ≥ 1`.
-/

namespace AdversarialBco.UW.BudW

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.UW

/-- (W-F3) at any level: `(10 · 36 ln N)^40 ≤ N` for `N > 2^700` (Piece A's `regime_Le40` with `N` free). -/
theorem le40_of_gt (N : ℝ) (h : (2 : ℝ) ^ 700 < N) : (10 * (36 * Real.log N)) ^ 40 ≤ N := by
  set x := Real.log N with hx_def
  have hN_pos : 0 < N := lt_trans (by positivity) h
  have hN_gt_one : 1 < N := lt_trans (one_lt_pow₀ (by norm_num) (by norm_num)) h
  have hx_pos : 0 < x := by
    rw [hx_def]
    exact Real.log_pos hN_gt_one
  have hx_gt : 700 * Real.log 2 < x := by
    rw [hx_def]
    have hpos : 0 < (2 : ℝ) ^ 700 := by positivity
    have hlog := Real.log_lt_log hpos h
    have hlog_pow : Real.log ((2 : ℝ) ^ 700) = 700 * Real.log 2 :=
      Real.log_pow (2 : ℝ) 700
    rw [hlog_pow] at hlog
    exact hlog
  -- key inequality: 40 * log(360 * x) ≤ x
  have h_key : 40 * Real.log (360 * x) ≤ x := by
    set x₀ := 700 * Real.log 2 with hx₀_def
    have hx₀_pos : 0 < x₀ := by
      rw [hx₀_def]
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
      positivity
    have hx_gt_x₀ : x₀ < x := hx_gt
    have h_ratio_pos : 0 < x / x₀ := div_pos hx_pos hx₀_pos
    have h_log_ratio : Real.log (x / x₀) ≤ x / x₀ - 1 :=
      Real.log_le_sub_one_of_pos h_ratio_pos
    have h_log_prod : Real.log (360 * x) = Real.log (360 * x₀) + Real.log (x / x₀) := by
      calc
        Real.log (360 * x) = Real.log ((360 * x₀) * (x / x₀)) := by
          field_simp [hx₀_pos.ne']
        _ = Real.log (360 * x₀) + Real.log (x / x₀) :=
          Real.log_mul (by positivity) (by positivity)
    rw [h_log_prod]
    -- need: 40 * (log(360*x₀) + log(x/x₀)) ≤ x
    -- using log(x/x₀) ≤ x/x₀ - 1, it suffices: 40*log(360*x₀) - 40 + 40*x/x₀ ≤ x
    -- i.e., 40*log(360*x₀) - 40 ≤ x*(1 - 40/x₀)
    -- since x > x₀ and 1 - 40/x₀ > 0, it suffices: 40*log(360*x₀) - 40 ≤ x₀ - 40
    -- i.e., 40*log(360*x₀) ≤ x₀
    have h_core : 40 * Real.log (360 * x₀) ≤ x₀ := by
      rw [hx₀_def]
      -- goal: 40 * Real.log (360 * (700 * Real.log 2)) ≤ 700 * Real.log 2
      -- simplify 360 * 700 = 252000
      have h_simp : (360 : ℝ) * (700 * Real.log 2) = (252000 : ℝ) * Real.log 2 := by ring
      rw [h_simp]
      -- goal: 40 * Real.log (252000 * Real.log 2) ≤ 700 * Real.log 2
      have hlog2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      -- First, bound 252000 * log 2 above by 174674
      have h_prod_bound : (252000 : ℝ) * Real.log 2 < 174674 := by
        have h_mul : (252000 : ℝ) * Real.log 2 < (252000 : ℝ) * 0.6931471808 :=
          mul_lt_mul_of_pos_left hlog2_lt (by norm_num : 0 < (252000 : ℝ))
        have h_lt : (252000 : ℝ) * 0.6931471808 < 174674 := by norm_num
        nlinarith
      have h_prod_pos : 0 < (252000 : ℝ) * Real.log 2 := by
        have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
        positivity
      -- So log(252000 * log 2) < log(174674)
      have h_log_lt : Real.log ((252000 : ℝ) * Real.log 2) < Real.log 174674 :=
        Real.log_lt_log h_prod_pos h_prod_bound
      -- Now bound log(174674) using the decomposition 174674 = 2^17 * (174674/131072)
      have h_log_174674 : Real.log (174674 : ℝ) ≤ 17 * Real.log 2 + (43602 : ℝ) / 131072 := by
        have h174674_eq : (174674 : ℝ) = (131072 : ℝ) * ((174674 : ℝ) / 131072) := by
          field_simp
        rw [h174674_eq]
        have hpos1 : 0 < (131072 : ℝ) := by norm_num
        have hpos2 : 0 < (174674 : ℝ) / 131072 := by norm_num
        rw [Real.log_mul hpos1.ne' hpos2.ne']
        have h_log_131072 : Real.log (131072 : ℝ) = 17 * Real.log 2 := by
          have h_pow : (131072 : ℝ) = (2 : ℝ) ^ 17 := by norm_num
          rw [h_pow, Real.log_pow (2 : ℝ) 17, Nat.cast_ofNat]
        rw [h_log_131072]
        have h_log_ratio : Real.log ((174674 : ℝ) / 131072) ≤ (174674 : ℝ) / 131072 - 1 :=
          Real.log_le_sub_one_of_pos hpos2
        have h_ratio_bound : (174674 : ℝ) / 131072 - 1 = (43602 : ℝ) / 131072 := by
          norm_num
        rw [h_ratio_bound] at h_log_ratio
        nlinarith
      -- Now combine: log(252000 * log 2) < log(174674) ≤ 17*log(2) + 43602/131072
      have h_log_bound : Real.log ((252000 : ℝ) * Real.log 2) < 17 * Real.log 2 + (43602 : ℝ) / 131072 := by
        nlinarith
      -- Multiply by 40
      have h_mul_bound : 40 * Real.log ((252000 : ℝ) * Real.log 2) < 40 * (17 * Real.log 2 + (43602 : ℝ) / 131072) := by
        nlinarith
      -- Compute RHS: 40*(17*log(2) + 43602/131072) = 680*log(2) + 40*43602/131072
      have h_rhs_simp : 40 * (17 * Real.log 2 + (43602 : ℝ) / 131072) = 680 * Real.log 2 + (40 * 43602 : ℝ) / 131072 := by
        ring
      rw [h_rhs_simp] at h_mul_bound
      -- Now we need to show: 680*log(2) + 40*43602/131072 ≤ 700*log(2)
      -- i.e., 40*43602/131072 ≤ 20*log(2)
      -- i.e., log(2) ≥ (40*43602)/(131072*20) = 43602/(131072*0.5) = 43602/65536 = 21801/32768 ≈ 0.6653
      have h_final_bound : 680 * Real.log 2 + (40 * 43602 : ℝ) / 131072 ≤ 700 * Real.log 2 := by
        have h_ineq : (40 * 43602 : ℝ) / 131072 ≤ 20 * Real.log 2 := by
          have h_log2_gt' : 87202 / 262144 < Real.log 2 := by
            -- 87202/262144 ≈ 0.3326, but we need ≈ 0.6653
            -- Let me recompute: 40*43602/131072 / 20 = 43602/(131072*0.5) = 43602/65536 = 21801/32768 ≈ 0.6653
            -- 21801/32768 = ?
            -- Actually, let me just use the numeric bound directly
            have h := hlog2_gt
            -- 0.6931471803 < log 2
            -- 21801/32768 ≈ 0.6653 < 0.6931471803
            have h_frac : (21801 : ℝ) / 32768 < 0.6931471803 := by norm_num
            nlinarith
          -- Actually, we can just use nlinarith with the known bounds
          have h_log2_gt_val : 0.6931471803 < Real.log 2 := hlog2_gt
          have h_target : (40 * 43602 : ℝ) / 131072 / 20 < 0.6931471803 := by norm_num
          nlinarith
        nlinarith
      have h_lt : 40 * Real.log ((252000 : ℝ) * Real.log 2) < 700 * Real.log 2 := by
        apply lt_of_lt_of_le h_mul_bound h_final_bound
      exact h_lt.le
    have hpos_factor : 0 < 1 - 40 / x₀ := by
      have hx₀_gt_40 : 40 < x₀ := by
        rw [hx₀_def]
        have hlog2_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
        nlinarith
      exact sub_pos.mpr ((div_lt_one hx₀_pos).mpr hx₀_gt_40)
    have h_main : 40 * (Real.log (360 * x₀) + (x / x₀ - 1)) ≤ x := by
      have hcalc : 40 * (Real.log (360 * x₀) + (x / x₀ - 1)) = 40 * Real.log (360 * x₀) - 40 + 40 * (x / x₀) := by ring
      rw [hcalc]
      have hineq1 : 40 * Real.log (360 * x₀) - 40 ≤ x₀ - 40 := by nlinarith
      have hineq2 : x₀ - 40 + 40 * (x / x₀) ≤ x := by
        have h_diff : x - (x₀ - 40 + 40 * (x / x₀)) = (x - x₀) * (1 - 40 / x₀) := by
          field_simp [hx₀_pos.ne']
          ring
        have h_pos : 0 < x - (x₀ - 40 + 40 * (x / x₀)) := by
          rw [h_diff]
          apply mul_pos
          · nlinarith
          · exact hpos_factor
        nlinarith
      nlinarith
    have h_log_sum_le : Real.log (360 * x₀) + Real.log (x / x₀) ≤ Real.log (360 * x₀) + (x / x₀ - 1) := by
      nlinarith
    have h_final : 40 * (Real.log (360 * x₀) + Real.log (x / x₀)) ≤ x := by
      nlinarith
    exact h_final
  -- Now use h_key to prove the target
  have h_exp : (10 * (36 * x)) ^ 40 ≤ N := by
    -- (10 * (36 * x)) ^ 40 ≤ exp(x)
    have h_expand : (10 * (36 * x)) ^ 40 = Real.exp (40 * Real.log (360 * x)) := by
      have hpos : 0 < 360 * x := by positivity
      calc
        (10 * (36 * x)) ^ 40 = ((360 : ℝ) * x) ^ 40 := by ring
        _ = Real.exp (Real.log (((360 : ℝ) * x) ^ 40)) := by
          rw [Real.exp_log (pow_pos hpos 40)]
        _ = Real.exp (40 * Real.log ((360 : ℝ) * x)) := by
          rw [Real.log_pow, Nat.cast_ofNat]
        _ = Real.exp (40 * Real.log (360 * x)) := by ring
    rw [h_expand]
    have h_exp_le : Real.exp (40 * Real.log (360 * x)) ≤ Real.exp x :=
      Real.exp_le_exp.mpr h_key
    have h_exp_x : Real.exp x = N := by
      rw [hx_def, Real.exp_log hN_pos]
    rw [h_exp_x] at h_exp_le
    exact h_exp_le
  exact h_exp


/-- BL-OW's base constants at `(d, n, k)` and the reference `ρ`. -/
noncomputable def regW (d n k : ℕ) (ρ : RefW) : RegW where
  d := d
  n := n
  Ne := Unified.BudK.Ne d n k
  de := 1 / Unified.BudK.Ne d n k
  Le := Unified.BudK.Le d n k
  lam := (parW d n ρ.u).lam
  eta := (parW d n ρ.u).eta
  eps := (parW d n ρ.u).eps
  rho := (parW d n ρ.u).rho
  R := (parW d n ρ.u).R
  kc := (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0
  tp := Unified.BudK.tp d n k
  eh := Unified.BudK.eh d n k
  t2 := 2 ^ ((parK d n k).B / 2)
  Q := Unified.BudK.Ne d n k ^ ((1 : ℝ) / 40)
  Lf := Bit.PieceA.Le d n
  uu := ρ.u
  b0 := ρ.b0
  y0 := ρ.y0

/-- From `ε(u) ≤ 1/4`: `n ≥ 58000² d³ L_f^10 u`. -/
theorem n_ge_of_epsW (d n : ℕ) (L u : ℝ) (hn : 1 ≤ n) (hu : 0 ≤ u)
    (h : 14500 * d * Real.sqrt d * L ^ 5 * Real.sqrt u / Real.sqrt n ≤ 1 / 4) (hL : 0 ≤ L) :
    (58000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * u ≤ n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have h2 : 58000 * (d : ℝ) * Real.sqrt d * L ^ 5 * Real.sqrt u ≤ Real.sqrt n := by
    rw [div_le_iff₀ hs] at h; linarith
  have h0 : 0 ≤ 58000 * (d : ℝ) * Real.sqrt d * L ^ 5 * Real.sqrt u := by positivity
  have hsq := pow_le_pow_left₀ h0 h2 2
  rw [Real.sq_sqrt hnpos.le] at hsq
  have e : (58000 * (d : ℝ) * Real.sqrt d * L ^ 5 * Real.sqrt u) ^ 2 = 58000 ^ 2 * (d : ℝ) ^ 3 * L ^ 10 * u := by
    have h1 : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
    calc (58000 * (d : ℝ) * Real.sqrt d * L ^ 5 * Real.sqrt u) ^ 2 =
          58000 ^ 2 * (d : ℝ) ^ 2 * Real.sqrt d ^ 2 * L ^ 10 * Real.sqrt u ^ 2 := by ring
      _ = _ := by rw [h1, h2]; ring
  linarith

/-- `RegW.OK` at BL-OW's constants, in the regime of the reference. -/
theorem reg_okW (d n k : ℕ) (ρ : RefW) (hρ : RegimeW d n ρ) : (regW d n k ρ).OK := by
  have hd := hρ.hd
  have hn := hρ.hn
  have hu := hρ.hu
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he4 : (parW d n ρ.u).eps ≤ 1 / 4 := hρ.heps
  have he0 : Bit.PieceA.eps d n ≤ 1 / 2 := (eps_le_of_regime hu he4).trans (by norm_num)
  have hN0 := Ne_ge0 d n k hd hn
  have hN700 : (2 : ℝ) ^ 700 < Unified.BudK.Ne d n k := lt_of_lt_of_le (Bit.PieceA.regime_N hd hn he0) hN0
  have hNpos : (0 : ℝ) < Unified.BudK.Ne d n k := lt_trans (by positivity) hN700
  have hLf1 : 17467 ≤ Bit.PieceA.Le d n := regW_Le hd hn hu he4
  have hLf0 : 0 ≤ Bit.PieceA.Le d n := by linarith
  have hNe : 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 ≤ Unified.BudK.Ne d n k := by
    refine le_trans (le_of_eq ?_) hN0
    unfold Bit.PieceA.Ne Bit.PieceA.NeN; push_cast; ring
  have hLe := Le_eq d n k hd hn
  have hl0 : 36 * lam0 d n = Bit.PieceA.Le d n := rfl
  refine
    { hd := hd'
      hn := hn'
      hNe := hNe
      hde := rfl
      hLe := hLe
      hLf := ?_
      hu := hu
      hlam := parW_lam d n ρ.u
      heta := parW_eta d n ρ.u
      heps := ?_
      hrho := ?_
      hkc := ?_
      heps4 := he4
      hN700 := hN700
      hLf1 := hLf1
      hLfLe := Le_ge0 d n k hd hn
      hd15 := le_trans (Bit.PieceA.regime_d15 hd hn he0) hN0
      hn4 := le_trans (Bit.PieceA.regime_n4 hd) hN0
      hnge := ?_
      hL40 := ?_
      hQ0 := Real.rpow_pos_of_pos hNpos _
      hQ := ?_
      htp0 := by show (0 : ℝ) < Unified.BudK.tp d n k; rw [tp_eq]; positivity
      htp := ?_
      heh1 := ?_
      heh2 := ?_
      hR1 := Bit.PieceA.ref_R_lower hd
      hR2 := Bit.PieceA.ref_R_upper hd
      ht20 := by show (0 : ℝ) < 2 ^ ((parK d n k).B / 2); positivity
      ht2 := t2_tpK d n k
      hb0 := ?_
      hb1 := ?_
      hy00 := ?_
      hy0 := ?_ }
  · show Bit.PieceA.Le d n = 36 * Real.log (15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4)
    unfold Bit.PieceA.Le Bit.PieceA.Ne Bit.PieceA.NeN; norm_num
  · show (parW d n ρ.u).eps = 14500 * d * Real.sqrt d * Bit.PieceA.Le d n ^ 5 * Real.sqrt ρ.u / Real.sqrt n
    rw [parW_eps, Bit.PieceA.eps]; ring
  · show (parW d n ρ.u).rho = 1450 * (d : ℝ) ^ 2 * Bit.PieceA.Le d n ^ 3
    show 2 * df2oClam * (d : ℝ) ^ 2 * (parW d n ρ.u).Le ^ 3 = _
    rw [parW_Le, df2oClam]; ring
  · show (parW d n ρ.u).eta * (parW d n ρ.u).kap * (parW d n ρ.u).lam * (parW d n ρ.u).k0 =
      (parW d n ρ.u).eta * (parW d n ρ.u).lam / (4 * (1 - (parW d n ρ.u).lam) ^ 2)
    rw [parW_kap, parW_k0]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · show (58000 : ℝ) ^ 2 * (d : ℝ) ^ 3 * Bit.PieceA.Le d n ^ 10 * ρ.u ≤ n
    refine n_ge_of_epsW d n (Bit.PieceA.Le d n) ρ.u hn (by linarith) ?_ hLf0
    have := he4
    rw [parW_eps, Bit.PieceA.eps] at this
    calc 14500 * (d : ℝ) * Real.sqrt d * Bit.PieceA.Le d n ^ 5 * Real.sqrt ρ.u / Real.sqrt n =
        14500 * d * Real.sqrt d * Bit.PieceA.Le d n ^ 5 / Real.sqrt n * Real.sqrt ρ.u := by ring
      _ ≤ 1 / 4 := this
  · show (10 * Unified.BudK.Le d n k) ^ 40 ≤ Unified.BudK.Ne d n k
    rw [hLe]
    exact le40_of_gt _ hN700
  · show (Unified.BudK.Ne d n k ^ ((1 : ℝ) / 40)) ^ 40 = Unified.BudK.Ne d n k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
  · show (2 : ℝ) ^ 160 * Unified.BudK.Ne d n k ^ 10 * (d : ℝ) ^ 16 * Unified.BudK.tp d n k ≤ 1
    exact gen_u (NeO d n k) d
  · show (2 : ℝ) ^ 64 * (d : ℝ) ^ 6 * Unified.BudK.Ne d n k ^ 3 * Unified.BudK.tp d n k ≤ Unified.BudK.eh d n k
    rw [eh_eq]; exact (gen_eh (NeO d n k) d (NeO_pos d n k hd hn) hd).1
  · show Unified.BudK.eh d n k ≤ (2 : ℝ) ^ 73 * (d : ℝ) ^ 6 * Unified.BudK.Ne d n k ^ 3 * Unified.BudK.tp d n k
    rw [eh_eq]; exact (gen_eh (NeO d n k) d (NeO_pos d n k hd hn) hd).2
  · show 2 * (d : ℝ) + 2 ≤ ρ.b0
    have := hρ.b0_lo
    have : 0 ≤ 36 * lam0 d n := by rw [hl0]; exact hLf0
    linarith
  · show ρ.b0 + 1 ≤ 2 * (d : ℝ) + Bit.PieceA.Le d n + 4
    have := hρ.b0_hi
    rw [hl0] at this
    linarith
  · show 0 < ρ.y0
    have h1 := hρ.y0_lo
    have h2 : 0 ≤ 18 / (parW d n ρ.u).eps := by
      have : 0 ≤ (parW d n ρ.u).eps := by
        rw [parW_eps, Bit.PieceA.eps]; positivity
      positivity
    have h3 : 0 ≤ 10 * Real.sqrt (12 * lam0 d n) := by positivity
    linarith
  · show ρ.y0 ≤ 11 + 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (Bit.PieceA.Le d n)
    have := hρ.y0_hi
    rw [hl0] at this
    exact this

end AdversarialBco.UW.BudW
