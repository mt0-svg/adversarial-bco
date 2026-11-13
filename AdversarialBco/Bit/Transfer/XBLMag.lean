/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMagC

@[expose] public section

/-!
# The magnitudes of BL's state: `magBL : MagBL`

The unit is `T = 2^K`, `K = 76 G + 343 + 2 E₀ + (d + 2) size M` with `G = parG d n`: PARAM's fields are at most
`2^(75 G + 343)` (`fld_abs`), `1/ε'` at most `2^{pF}` (`eps_grid`), the kept rows `α̃_i = A_Sᵀ a_i` at most
`d 2^{E₀} M` and `1/β̃_i` at most `2^{E₀} M^{d+1}` under `PosBnd` (`cfg_alpha`, `cfg_beta`), so the configuration is
bounded at `T` (`cfgB_of`). By induction over the rounds (`run_bnd`, with `step_bnd`), in every round `t ≤ n` in mode
`run` the entries of `A', B'` are at most `T`, `μ'` is in the box of radius `R_int`, and `b', k', G', l'` are at most
`t T^30 ≤ T^31`; their numerators on the grid `2^{-p}` are at most `T^33 = 2^{33K}`, and `33 K ≤ 2·10^7 W^2` with
`W = d + m + size M + size n + E₀ + 1` (`parG_le`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ AdversarialBco.Bit.Asm Matrix
open AdversarialBco.BitRAM (toE)
open AdversarialBco.RealRAM (Strategy polytope HeightLE)

variable {d : ℕ}

/-! ## PARAM's fields -/

theorem parG_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : parG d n ≤ 4000 * (d.size + n.size + 1) := by
  unfold parG gsm_prec
  exact parG_bound d n (BLP.Ne d n).size d.size (par d n).p (par d n).q (par d n).pF (par d n).B hd hn rfl rfl rfl
    rfl rfl rfl

/-- A grid point is at most the bound of its numerator. -/
theorem grid_abs {k N : ℕ} {x : ℚ} (hx : OnG k x) (hz : |qn k x| ≤ 2 ^ N) : |x| ≤ 2 ^ N := by
  have hk1 : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h1 : |x| * 2 ^ k = |(qn k x : ℚ)| := by
    unfold OnG at hx; rw [hx, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ k)]
  have h2 : |(qn k x : ℚ)| ≤ 2 ^ N := by exact_mod_cast hz
  have h3 := mul_le_mul_of_nonneg_left hk1 (abs_nonneg x)
  linarith

theorem onG_up (k : ℕ) (x : ℚ) : OnG k (up k x) := by
  unfold OnG; rw [qn_up]; unfold up; field_simp

/-- **PARAM's fields at the magnitude `75 G + 343`.** -/
theorem fld_abs {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    |(par d n).lam| ≤ 2 ^ (75 * parG d n + 343) ∧ |(par d n).kapc| ≤ 2 ^ (75 * parG d n + 343) ∧
    |(par d n).nu| ≤ 2 ^ (75 * parG d n + 343) ∧ |(par d n).A0| ≤ 2 ^ (75 * parG d n + 343) ∧
    |(par d n).B0| ≤ 2 ^ (75 * parG d n + 343) ∧ ((par d n).Rint : ℚ) ≤ 2 ^ (75 * parG d n + 343) ∧
    ((par d n).Lam : ℚ) ≤ 2 ^ (75 * parG d n + 343) := by
  have hpv : ∀ k < 93, |pv d n k| ≤ 2 ^ (75 * parG d n + 343) := fun k hk => pv_abs hd hn hk
  refine ⟨grid_abs (by rw [PieceA.par_lam]; exact onG_rnd_s _ _) ?_,
    grid_abs (by rw [PieceA.par_kapc]; exact onG_rnd_s _ _) ?_, grid_abs (by rw [PieceA.par_nu]; exact onG_rnd_s _ _) ?_,
    grid_abs (by rw [PieceA.par_A0]; exact onG_rnd_s _ _) ?_, grid_abs (by rw [PieceA.par_B0]; exact onG_rnd_s _ _) ?_,
    ?_, ?_⟩
  · rw [qn_par_lam hd hn, ← pv_70 (d := d) (n := n) hd hn]; exact hpv 70 (by norm_num)
  · rw [qn_par_kapc hd hn, ← pv_74 (d := d) (n := n) hd hn]; exact hpv 74 (by norm_num)
  · rw [qn_par_nu hd hn, ← pv_75 (d := d) (n := n) hd hn]; exact hpv 75 (by norm_num)
  · rw [qn_par_A0 hd hn, ← pv_89 (d := d) (n := n) hd hn]; exact hpv 89 (by norm_num)
  · rw [qn_par_B0 hd hn, ← pv_90 (d := d) (n := n) hd hn]; exact hpv 90 (by norm_num)
  · have h := hpv 91 (by norm_num)
    rw [pv_91 (d := d) (n := n), ← Rint_eq, abs_of_nonneg (Int.natCast_nonneg _)] at h
    exact_mod_cast h
  · have h := hpv 40 (by norm_num)
    rw [pv_40 (d := d) (n := n), abs_of_nonneg (Int.natCast_nonneg _)] at h
    rw [par_Lam]; exact_mod_cast h

/-- `1/ε'` is at most `2^{pF}` (`0` when `ε' = 0`). -/
theorem eps_grid {n : ℕ} : |(par d n).eps⁻¹| ≤ 2 ^ (par d n).pF := by
  have h : OnG (par d n).pF (par d n).eps := by rw [PieceA.par_eps]; exact onG_up _ _
  have e : (par d n).eps = (qn (par d n).pF (par d n).eps : ℚ) / 2 ^ (par d n).pF := by
    unfold OnG at h; rw [h]; field_simp
  rw [e]
  exact grid_inv_abs _ _

/-! ## The configuration -/

theorem rat_abs_le_num (q : ℚ) : |q| ≤ q.num.natAbs := by
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  calc |q| = |(q.num : ℚ) / q.den| := by rw [Rat.num_div_den]
    _ = |(q.num : ℚ)| / q.den := by rw [abs_div, Nat.abs_cast]
    _ ≤ |(q.num : ℚ)| := div_le_self (abs_nonneg _) hd
    _ = q.num.natAbs := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The kept rows `α̃_i = A_Sᵀ a_i`. -/
theorem cfg_alpha {n m M E0 : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (hH : HeightLE A b M) (hS : ∀ i j, |S.2 i j| ≤ 2 ^ E0)
    (i : Fin (keptIdx A).length) (j : Fin d) : |(mkCfg d n m A b c S).α i j| ≤ d * 2 ^ E0 * M := by
  show |(S.2ᵀ *ᵥ A ((keptIdx A).get i)) j| ≤ _
  exact mulVecQ_abs_le _ _ _ _ (fun i' j' => hS j' i')
    (fun k => (rat_abs_le_num _).trans (by exact_mod_cast (hH.1 _ k).1)) j

/-- `1/β̃_i` for a position over the denominator `D_S`. -/
theorem cfg_beta {n m M E0 : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (hH : HeightLE A b M) (DS : ℤ) (hDS : 0 < DS) (hDSE : DS ≤ 2 ^ E0)
    (x : Fin d → ℤ) (hx : S.1 = fun k => (x k : ℚ) / DS) (i : Fin (keptIdx A).length)
    (hpos : 0 < (mkCfg d n m A b c S).β i) : ((mkCfg d n m A b c S).β i)⁻¹ ≤ 2 ^ E0 * M ^ (d + 1) := by
  have e : (mkCfg d n m A b c S).β i =
      b ((keptIdx A).get i) - A ((keptIdx A).get i) ⬝ᵥ (fun k => (x k : ℚ) / DS) := by
    show _ - _ ⬝ᵥ S.1 = _; rw [hx]
  rw [e] at hpos ⊢
  rw [inv_eq_one_div]
  exact beta_inv_le _ _ x DS M E0 hDS hDSE (hH.2 _).2 (fun k => (hH.1 _ k).2) hpos

/-- The exponent of the unit. -/
def Kmag (d n M E0 : ℕ) : ℕ := 76 * parG d n + 343 + 2 * E0 + (d + 2) * M.size

/-- **The configuration of a run in mode `run` is bounded at `2^K`.** -/
theorem cfgB_of {n m M E0 : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool)
    (hI : InputOK d n m M A b) (hP : PosBnd (cfgOf RoutinesQ d n m A b cs) E0) (heps : (par d n).eps ≤ 1 / 2)
    (hβ : ∀ i, 0 < (cfgOf RoutinesQ d n m A b cs).β i) :
    CfgB (2 ^ Kmag d n M E0 : ℚ) (cfgOf RoutinesQ d n m A b cs) := by
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨DS, hDS, hDSE, hμ, hAS⟩ := hP
  choose xμ _ hxμ2 using hμ
  have hS1 : (RoutinesQ.pos d n m A b cs).1 = fun k => (xμ k : ℚ) / DS := funext fun k => (hxμ2 k).symm
  have hDS0 : (0 : ℚ) < DS := by exact_mod_cast hDS
  have hDS1 : (1 : ℚ) ≤ DS := by exact_mod_cast hDS
  have hS2 : ∀ i j, |(RoutinesQ.pos d n m A b cs).2 i j| ≤ 2 ^ E0 := fun i j => by
    obtain ⟨x, hx, e⟩ := hAS i j
    show |(cfgOf RoutinesQ d n m A b cs).AS i j| ≤ _
    rw [← e, abs_div, abs_of_pos hDS0]
    have h1 : |(x : ℚ)| ≤ 2 ^ E0 := by exact_mod_cast hx
    exact (div_le_self (abs_nonneg _) hDS1).trans h1
  have hG := parG_ge (d := d) (n := n)
  have hK : ∀ a, a ≤ Kmag d n M E0 → (2 : ℚ) ^ a ≤ 2 ^ Kmag d n M E0 := fun a h =>
    pow_le_pow_right₀ (by norm_num) h
  have hMs : (M : ℚ) ≤ 2 ^ M.size := by exact_mod_cast (Nat.lt_size_self M).le
  have hdG : (d : ℚ) ≤ 2 ^ parG d n := by exact_mod_cast (d_le_G (n := n))
  obtain ⟨flam, fkap, fnu, fA0, fB0, fR, fLam⟩ := fld_abs (d := d) (n := n) hd hn
  have hN : 75 * parG d n + 343 ≤ Kmag d n M E0 := by unfold Kmag; omega
  have hdM : M.size * (d + 1) ≤ (d + 2) * M.size := by rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  have hMs2 : M.size ≤ (d + 2) * M.size := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, hdG.trans (hK _ (by unfold Kmag; omega)), fun i j => ?_, fun i => ⟨hβ i, ?_⟩, eps_nonneg hd hn, heps,
    eps_grid.trans (hK _ (by unfold Kmag; omega)), flam.trans (hK _ hN), fkap.trans (hK _ hN),
    fnu.trans (hK _ hN), fLam.trans (hK _ hN), fA0.trans (hK _ hN), fB0.trans (hK _ hN), fR.trans (hK _ hN)⟩
  · calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ _ := hK 2 (by unfold Kmag; omega)
  · calc |(cfgOf RoutinesQ d n m A b cs).α i j| ≤ (d : ℚ) * 2 ^ E0 * M :=
          cfg_alpha (n := n) A b (RoutinesQ.ctr d n m A b) (RoutinesQ.pos d n m A b cs) hI.height hS2 i j
      _ ≤ 2 ^ parG d n * 2 ^ E0 * 2 ^ M.size :=
          mul_le_mul (mul_le_mul_of_nonneg_right hdG (by positivity)) hMs (Nat.cast_nonneg M) (by positivity)
      _ = 2 ^ (parG d n + E0 + M.size) := by rw [pow_add, pow_add]
      _ ≤ _ := hK (parG d n + E0 + M.size) (by unfold Kmag; omega)
  · calc ((cfgOf RoutinesQ d n m A b cs).β i)⁻¹ ≤ 2 ^ E0 * (M : ℚ) ^ (d + 1) :=
          cfg_beta (n := n) A b (RoutinesQ.ctr d n m A b) (RoutinesQ.pos d n m A b cs) hI.height DS hDS hDSE xμ hS1
            i (hβ i)
      _ ≤ 2 ^ E0 * (2 ^ M.size) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg M) hMs _) (by positivity)
      _ = 2 ^ (E0 + M.size * (d + 1)) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := hK (E0 + M.size * (d + 1)) (by unfold Kmag; omega)

/-! ## The run -/

/-- A zero row of the input has `0 ≤ b_i` (the polytope holds a ball). -/
theorem hzero_of {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) :
    ∀ i, A i = 0 → 0 ≤ b i := by
  intro i hA
  obtain ⟨c, hc⟩ := hI.ball
  have h : ∑ j, (A i j : ℝ) * c j ≤ b i := hc (Metric.mem_closedBall_self zero_le_one) i
  have h0 : ∀ j, A i j = 0 := fun j => by simp [hA]
  simp only [h0, Rat.cast_zero, zero_mul, Finset.sum_const_zero] at h
  exact_mod_cast h

/-- **The bounds in every round `t ≤ n` in mode `run`.** -/
theorem run_bnd {n m M : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (hI : InputOK d n m M A b)
    (σ : Strategy d) (hσ : AdmStrat (polytope A b) n σ) (cs : ℕ → Bool) {T : ℚ}
    (hc : CfgB T (cfgOf RoutinesQ d n m A b cs)) (hB : ((par d n).B : ℚ) ≤ T) (hB8 : 8 ≤ (par d n).B) :
    ∀ t, t ≤ n → ∀ st, modeAt RoutinesQ d n m A b σ cs t = .run st → StI T (par d n).Rint t st
  | 0, _, st, h => by
    obtain ⟨-, -, e⟩ := mode0_run h
    subst e
    exact init_bnd (by linarith [hc.T4]) (Nat.cast_nonneg _) _ hc.A0 hc.B0 _
  | t + 1, ht, st, h => by
    have hξ := draw_abs (d := d) cs (RoutinesQ.K0 d n) (par d n).B t hB8
    unfold modeAt at h
    simp only [traj] at h
    rcases hm : (traj RoutinesQ d n m A b σ cs t).1 with _ | _ | st1
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h
    rw [hm] at h
    have hs := run_bnd A b hI σ hσ cs hc hB hB8 t (by omega) st1 hm
    have hx := play_mem (n := n) A b (RoutinesQ.ctr d n m A b) (RoutinesQ.pos d n m A b cs) st1
      (drawAt RoutinesQ d n cs t).1 (hzero_of hI) hc.eps1 hc.eps0 (fun i => (hc.β i).1)
    refine step_bnd _ (fun D y hy j => apQ_abs D y hy j) hc n hs _ _ _ (fun i => (hξ.1 i).trans hB)
      (hξ.2.trans hB) ?_ ?_ h
    · exact_mod_cast (obs_bnd hσ t (by omega) _ _ hx _).1
    · exact_mod_cast (obs_bnd hσ t (by omega) _ _ hx _).2

/-- The numerator on the grid `2^{-p}` of a value at most `T^a`, for `2^p ≤ T`. -/
theorem qn_bnd {T : ℚ} (hT : 2 ≤ T) {p : ℕ} (hp : (2 : ℚ) ^ p ≤ T) {x : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) :
    |(qn p x : ℚ)| ≤ T ^ (a + 2) := by
  have h1 := Int.floor_le (x * 2 ^ p)
  have h2 := Int.lt_floor_add_one (x * 2 ^ p)
  have h3 : |x * 2 ^ p| ≤ T ^ (a + 1) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ p), pow_succ]
    exact mul_le_mul hx hp (by positivity) ((abs_nonneg _).trans hx)
  have hT1 : 1 ≤ T ^ (a + 1) := one_le_pow₀ (by linarith)
  apply two_mul_pw hT
  unfold qn
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

/-- The exponent `33 K` is quadratic in `W = d + m + size M + size n + E₀ + 1`. -/
theorem kmag_le {n m M E0 : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    33 * Kmag d n M E0 ≤ 20000000 * (d + m + M.size + n.size + E0 + 1) ^ 2 := by
  have hG := parG_le (d := d) hd hn
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  have hdM : (d + 2) * M.size ≤ 2 * ((d + m + M.size + n.size + E0 + 1) * (d + m + M.size + n.size + E0 + 1)) := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hW : d + m + M.size + n.size + E0 + 1 ≤
      (d + m + M.size + n.size + E0 + 1) * (d + m + M.size + n.size + E0 + 1) := Nat.le_mul_self _
  unfold Kmag
  rw [sq]
  generalize (d + 2) * M.size = X at hdM ⊢
  generalize (d + m + M.size + n.size + E0 + 1) * (d + m + M.size + n.size + E0 + 1) = Y at hdM hW ⊢
  omega

/-- **`magBL`: the magnitudes of BL's state.** -/
theorem magBL : MagBL := by
  refine ⟨20000000, 2, ?_⟩
  intro d n m M E0 A b hI σ hσ cs hP t st ht hst
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨st0, h0⟩ := modeAt_run RoutinesQ n m A b σ cs t st hst
  obtain ⟨heps, hβ, -⟩ := mode0_run h0
  have hc := cfgB_of A b cs hI hP heps hβ
  have hG := parG_ge (d := d) (n := n)
  have hB4 := B_le (d := d) (n := n) hd
  have hK : ∀ a, a ≤ Kmag d n M E0 → (2 : ℚ) ^ a ≤ 2 ^ Kmag d n M E0 := fun a h =>
    pow_le_pow_right₀ (by norm_num) h
  have hT2 : (2 : ℚ) ≤ 2 ^ Kmag d n M E0 := by linarith [hc.T4]
  have hT1 : (1 : ℚ) ≤ 2 ^ Kmag d n M E0 := by linarith
  have hB : ((par d n).B : ℚ) ≤ 2 ^ Kmag d n M E0 := by
    have : (par d n).B < 2 ^ (par d n).B := Nat.lt_two_pow_self
    have h1 : ((par d n).B : ℚ) ≤ 2 ^ (par d n).B := by exact_mod_cast this.le
    exact h1.trans (hK _ (by unfold Kmag; omega))
  have hB8 : 8 ≤ (par d n).B := by simp only [par]; omega
  have hs := run_bnd A b hI σ hσ cs hc hB hB8 t ht st hst
  have hp : (2 : ℚ) ^ (par d n).p ≤ 2 ^ Kmag d n M E0 := hK _ (by unfold Kmag; omega)
  have hnT : (n : ℚ) ≤ 2 ^ Kmag d n M E0 := by
    have h1 : (n : ℚ) ≤ 2 ^ parG d n := by exact_mod_cast n_le_G hd hn
    exact h1.trans (hK _ (by unfold Kmag; omega))
  have hE := kmag_le (d := d) (m := m) (M := M) (E0 := E0) hd hn
  have key : ∀ x : ℚ, |x| ≤ (2 ^ Kmag d n M E0) ^ 31 →
      |qn (par d n).p x| ≤ 2 ^ (20000000 * (d + m + M.size + n.size + E0 + 1) ^ 2) := fun x hx => by
    have h := qn_bnd hT2 hp hx
    have h2 : ((2 : ℚ) ^ Kmag d n M E0) ^ (31 + 2) ≤ 2 ^ (20000000 * (d + m + M.size + n.size + E0 + 1) ^ 2) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast h.trans h2
  have hsum : ∀ y : ℚ, |y| ≤ t * (2 ^ Kmag d n M E0) ^ 30 → |y| ≤ (2 ^ Kmag d n M E0) ^ 31 := fun y hy => by
    have ht' : (t : ℚ) ≤ 2 ^ Kmag d n M E0 := (by exact_mod_cast ht : (t : ℚ) ≤ n).trans hnT
    have h30 : (0 : ℚ) ≤ (2 ^ Kmag d n M E0) ^ 30 := by positivity
    calc |y| ≤ t * (2 ^ Kmag d n M E0) ^ 30 := hy
      _ ≤ 2 ^ Kmag d n M E0 * (2 ^ Kmag d n M E0) ^ 30 := mul_le_mul_of_nonneg_right ht' h30
      _ = (2 ^ Kmag d n M E0) ^ 31 := by ring
  have hent : ∀ y : ℚ, |y| ≤ 2 ^ Kmag d n M E0 → |y| ≤ (2 ^ Kmag d n M E0) ^ 31 := fun y hy =>
    bnd_up hT1 (pw1 hy) (by norm_num)
  exact ⟨fun i j => key _ (hent _ (hs.A i j)), fun i j => key _ (hent _ (hs.B i j)), fun j => key _ (hsum _ (hs.b j)),
    key _ (hsum _ hs.k), fun j => key _ (hsum _ (hs.G j)), key _ (hsum _ hs.l), hs.mu⟩

end AdversarialBco.Bit.Transfer.BLM
