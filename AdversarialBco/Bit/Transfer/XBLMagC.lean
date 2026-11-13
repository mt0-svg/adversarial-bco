/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMagB

@[expose] public section

/-!
# The magnitudes of BL's state, part C: one round

At a unit `T ≥ 4` that bounds the configuration (`CfgB`: `d`, the kept rows `α̃_i`, `1/β̃_i`, `1/ε'`, the fields
`λ', κ_c', ν', Λ, A_0, B_0, R_int`), one round of BL from a state with `A', B'` entries at most `T`, `μ'` in the box of
radius `R_int` and the sums `b', k', G', l'` at most `t T^30` (`StI`) leaves a state of the same kind at `t + 1`
(`step_bnd`): `A', B'` pass the test `frob2 ≤ 2Λ` of R10, `μ'` is the projection routine's point, `Y' ≤ T^14`
(`Y_bnd`), and each increment is at most `T^27`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## Powers of the unit -/

section Pw

variable {T : ℚ}

theorem rnd_abs_le (k : ℕ) (x : ℚ) : |rnd k x| ≤ |x| + 1 := by
  unfold rnd
  have hk : (0 : ℚ) < 2 ^ k := by positivity
  have hk1 : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  have h1 := Int.floor_le (x * 2 ^ k + 1 / 2)
  have h2 := Int.lt_floor_add_one (x * 2 ^ k + 1 / 2)
  have h3 := mul_le_mul_of_nonneg_right (le_abs_self x) hk.le
  have h4 := mul_le_mul_of_nonneg_right (neg_abs_le x) hk.le
  rw [abs_le]
  constructor <;> nlinarith

theorem bnd_up (hT : 1 ≤ T) {x : ℚ} {a b : ℕ} (hx : |x| ≤ T ^ a) (h : a ≤ b) : |x| ≤ T ^ b :=
  hx.trans (pow_le_pow_right₀ hT h)

theorem bnd_mul {x y : ℚ} {a b : ℕ} (hx : |x| ≤ T ^ a) (hy : |y| ≤ T ^ b) : |x * y| ≤ T ^ (a + b) := by
  rw [abs_mul, pow_add]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem two_mul_pw (hT : 2 ≤ T) {x : ℚ} {a : ℕ} (hx : x ≤ 2 * T ^ a) : x ≤ T ^ (a + 1) := by
  have h0 : 0 ≤ T ^ a := pow_nonneg (by linarith) a
  calc x ≤ 2 * T ^ a := hx
    _ ≤ T * T ^ a := mul_le_mul_of_nonneg_right hT h0
    _ = T ^ (a + 1) := by ring

theorem bnd_add (hT : 2 ≤ T) {x y : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) (hy : |y| ≤ T ^ a) : |x + y| ≤ T ^ (a + 1) :=
  two_mul_pw hT (by have := abs_add_le x y; linarith)

theorem bnd_sub (hT : 2 ≤ T) {x y : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) (hy : |y| ≤ T ^ a) : |x - y| ≤ T ^ (a + 1) :=
  two_mul_pw hT (by have := abs_sub x y; linarith)

theorem bnd_rnd (hT : 2 ≤ T) (k : ℕ) {x : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) : |rnd k x| ≤ T ^ (a + 1) := by
  have h1 : 1 ≤ T ^ a := one_le_pow₀ (by linarith)
  exact two_mul_pw hT (by have := rnd_abs_le k x; linarith)

theorem bnd_div2 {x : ℚ} {a : ℕ} (hx : |x| ≤ T ^ a) : |x / 2| ≤ T ^ a := by
  rw [abs_div, abs_two]; have := abs_nonneg x; linarith

theorem bnd_dot (hT : 1 ≤ T) (hd : (d : ℚ) ≤ T) {v w : Fin d → ℚ} {a b : ℕ} (hv : ∀ j, |v j| ≤ T ^ a)
    (hw : ∀ j, |w j| ≤ T ^ b) : |v ⬝ᵥ w| ≤ T ^ (a + b + 1) := by
  have ha : 0 ≤ T ^ a := pow_nonneg (by linarith) a
  have hb : 0 ≤ T ^ b := pow_nonneg (by linarith) b
  calc |v ⬝ᵥ w| ≤ d * T ^ a * T ^ b := dotQ_abs_le v w _ _ hv hw
    _ ≤ T * T ^ a * T ^ b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd ha) hb
    _ = T ^ (a + b + 1) := by ring

theorem bnd_mulVec (hT : 1 ≤ T) (hd : (d : ℚ) ≤ T) {M : Matrix (Fin d) (Fin d) ℚ} {v : Fin d → ℚ} {a b : ℕ}
    (hM : ∀ i j, |M i j| ≤ T ^ a) (hv : ∀ j, |v j| ≤ T ^ b) (i : Fin d) : |(M *ᵥ v) i| ≤ T ^ (a + b + 1) := by
  have ha : 0 ≤ T ^ a := pow_nonneg (by linarith) a
  have hb : 0 ≤ T ^ b := pow_nonneg (by linarith) b
  calc |(M *ᵥ v) i| ≤ d * T ^ a * T ^ b := mulVecQ_abs_le M v _ _ hM hv i
    _ ≤ T * T ^ a * T ^ b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd ha) hb
    _ = T ^ (a + b + 1) := by ring

theorem pw1 {x : ℚ} (h : |x| ≤ T) : |x| ≤ T ^ 1 := by rwa [pow_one]

end Pw

/-! ## The bounds of a configuration and of a state -/

/-- The configuration at the unit `T`. -/
structure CfgB (T : ℚ) (cfg : Cfg d) : Prop where
  T4 : 4 ≤ T
  d : (d : ℚ) ≤ T
  α : ∀ i j, |cfg.α i j| ≤ T
  β : ∀ i, 0 < cfg.β i ∧ (cfg.β i)⁻¹ ≤ T
  eps0 : 0 ≤ cfg.par.eps
  eps1 : cfg.par.eps ≤ 1 / 2
  epsI : |cfg.par.eps⁻¹| ≤ T
  lam : |cfg.par.lam| ≤ T
  kapc : |cfg.par.kapc| ≤ T
  nu : |cfg.par.nu| ≤ T
  Lam : (cfg.par.Lam : ℚ) ≤ T
  A0 : |cfg.par.A0| ≤ T
  B0 : |cfg.par.B0| ≤ T
  R : (cfg.par.Rint : ℚ) ≤ T

/-- BL's state in round `t`: `A', B'` entries at most `T`, `μ'` in the box of radius `R`, the sums at most `t T^30`. -/
structure StI (T R : ℚ) (t : ℕ) (st : St d) : Prop where
  A : ∀ i j, |st.A i j| ≤ T
  B : ∀ i j, |st.B i j| ≤ T
  mu : ∀ j, |st.mu j| ≤ R
  b : ∀ j, |st.b j| ≤ t * T ^ 30
  k : |st.k| ≤ t * T ^ 30
  G : ∀ j, |st.G j| ≤ t * T ^ 30
  l : |st.l| ≤ t * T ^ 30

theorem init_bnd {T R : ℚ} (hT : 0 ≤ T) (hR : 0 ≤ R) (P : Par) (hA0 : |P.A0| ≤ T) (hB0 : |P.B0| ≤ T) (t : ℕ) :
    StI T R t (init P d) := by
  have h0 : (0 : ℚ) ≤ t * T ^ 30 := mul_nonneg (Nat.cast_nonneg t) (pow_nonneg hT 30)
  refine ⟨fun i j => ?_, fun i j => ?_, fun j => ?_, fun j => ?_, ?_, fun j => ?_, ?_⟩
  · simp only [init, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rwa [mul_one]
    · rw [mul_zero, abs_zero]; exact hT
  · simp only [init, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rwa [mul_one]
    · rw [mul_zero, abs_zero]; exact hT
  · simp only [init, Pi.zero_apply, abs_zero]; exact hR
  · simp only [init, Pi.zero_apply, abs_zero]; exact h0
  · simp only [init, abs_zero]; exact h0
  · simp only [init, Pi.zero_apply, abs_zero]; exact h0
  · simp only [init, abs_zero]; exact h0

/-- An entry of a matrix that passes the test `frob2 ≤ 2Λ` is at most `T`. -/
theorem frob_entry_le {T : ℚ} (hT : 2 ≤ T) {L : ℕ} (hL : (L : ℚ) ≤ T) (M : Matrix (Fin d) (Fin d) ℚ)
    (hM : ¬ 2 * (L : ℚ) < frob2 M) (i j : Fin d) : |M i j| ≤ T := by
  have h1 : M i j ^ 2 ≤ frob2 M := by
    unfold frob2
    have hi : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
        (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg (M i' j')) (Finset.mem_univ i)
    have hj : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
      Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun j' _ => sq_nonneg (M i j')) (Finset.mem_univ j)
    linarith
  have h2 : M i j ^ 2 ≤ T ^ 2 := by push_neg at hM; nlinarith
  have := sq_le_sq.1 h2
  rwa [abs_of_nonneg (by linarith : (0 : ℚ) ≤ T)] at this

/-! ## The reading `Y'` -/

/-- **`|Y'| ≤ T^14`.** -/
theorem Y_bnd {cfg : Cfg d} {T : ℚ} (hc : CfgB T cfg) {st : St d} {t : ℕ} (hs : StI T cfg.par.Rint t st)
    (ξ : Fin d → ℚ) (ζ : ℚ) (o : ℤ) (hξ : ∀ i, |ξ i| ≤ T) (hζ : |ζ| ≤ T) (ho0 : 0 ≤ (o : ℚ))
    (ho1 : (o : ℚ) ≤ 2 ^ cfg.par.p) :
    |rnd cfg.par.p (ptQ cfg (XQ cfg st ξ) * ((o : ℚ) / 2 ^ cfg.par.p + ζ) / 2 +
      2 * (ptQ cfg (XQ cfg st ξ) - 1) / cfg.par.eps)| ≤ T ^ 14 := by
  have hT2 : (2 : ℚ) ≤ T := by linarith [hc.T4]
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hw : ∀ i, |(st.A *ᵥ ξ) i| ≤ T ^ 3 := bnd_mulVec (a := 1) (b := 1) hT1 hc.d
    (fun i j => pw1 (hs.A i j)) (fun j => pw1 (hξ j))
  have hlam : |1 - cfg.par.lam| ≤ T ^ 2 :=
    bnd_sub (a := 1) hT2 (pw1 (by rw [abs_one]; exact hT1)) (pw1 hc.lam)
  have hX : ∀ i, |XQ cfg st ξ i| ≤ T ^ 6 := fun i => by
    show |st.mu i + (1 - cfg.par.lam) * (st.A *ᵥ ξ) i| ≤ T ^ 6
    exact bnd_add (a := 5) hT2 (bnd_up hT1 (pw1 ((hs.mu i).trans hc.R)) (by norm_num)) (bnd_mul hlam (hw i))
  have hterm : ∀ i, |cfg.α i ⬝ᵥ XQ cfg st ξ / cfg.β i| ≤ T ^ 9 := fun i => by
    rw [div_eq_mul_inv]
    have hb := hc.β i
    exact bnd_mul (a := 8) (b := 1) (bnd_dot (a := 1) (b := 6) hT1 hc.d (fun j => pw1 (hc.α i j)) hX)
      (pw1 (by rw [abs_of_pos (inv_pos.2 hb.1)]; exact hb.2))
  have hg0 := (gauge_spec cfg (XQ cfg st ξ)).1
  have hg1 : gaugeQ cfg (XQ cfg st ξ) ≤ T ^ 9 :=
    gauge_le cfg _ _ (pow_nonneg (by linarith) 9) fun i => (le_abs_self _).trans (hterm i)
  obtain ⟨hpt1, -⟩ := ptQ_ge cfg (XQ cfg st ξ) hc.eps0 (by linarith [hc.eps1])
  have hT9 : 1 ≤ T ^ 9 := one_le_pow₀ hT1
  have hpt2 : ptQ cfg (XQ cfg st ξ) ≤ T ^ 10 := by
    unfold ptQ
    refine max_le (one_le_pow₀ hT1) (two_mul_pw hT2 ?_)
    have he : (1 : ℚ) / 2 ≤ 1 - cfg.par.eps := by linarith [hc.eps1]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  set pt := ptQ cfg (XQ cfg st ξ)
  have hpt : |pt| ≤ T ^ 10 := by rw [abs_of_nonneg (by linarith)]; exact hpt2
  have hpt' : |pt - 1| ≤ T ^ 10 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hp : (0 : ℚ) < 2 ^ cfg.par.p := by positivity
  have ho : |(o : ℚ) / 2 ^ cfg.par.p| ≤ T ^ 1 := by
    rw [abs_of_nonneg (div_nonneg ho0 hp.le), pow_one, div_le_iff₀ hp]; nlinarith
  have h1 : |pt * ((o : ℚ) / 2 ^ cfg.par.p + ζ) / 2| ≤ T ^ 12 :=
    bnd_div2 (bnd_mul hpt (bnd_add hT2 ho (pw1 hζ)))
  have h2 : |2 * (pt - 1) / cfg.par.eps| ≤ T ^ 12 := by
    rw [div_eq_mul_inv]
    exact bnd_mul (a := 11) (b := 1) (bnd_mul (a := 1) (pw1 (by rw [abs_two]; exact hT2)) hpt') (pw1 hc.epsI)
  exact bnd_rnd hT2 _ (bnd_up hT1 (bnd_add hT2 h1 h2) (by norm_num))

/-! ## The increments -/

section Incr

variable {T : ℚ} (hT : 4 ≤ T) (hd : (d : ℚ) ≤ T) (p : ℕ) (Y : ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
  (mu ξ : Fin d → ℚ) (hB : ∀ i j, |B i j| ≤ T) (hmu : ∀ j, |mu j| ≤ T) (hξ : ∀ j, |ξ j| ≤ T) (hY : |Y| ≤ T ^ 14)

include hT hd hB hmu hξ hY

theorem incr_u : (∀ j, |(B *ᵥ ξ) j| ≤ T ^ 3) ∧ (∀ j, |(Bᵀ *ᵥ mu) j| ≤ T ^ 3) ∧ |(B *ᵥ ξ) ⬝ᵥ mu| ≤ T ^ 5 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hu : ∀ j, |(B *ᵥ ξ) j| ≤ T ^ 3 := bnd_mulVec (a := 1) (b := 1) hT1 hd (fun i j => pw1 (hB i j)) (fun j => pw1 (hξ j))
  refine ⟨hu, bnd_mulVec (a := 1) (b := 1) hT1 hd (fun i j => pw1 (hB j i)) (fun j => pw1 (hmu j)), ?_⟩
  exact bnd_dot (a := 3) (b := 1) hT1 hd hu (fun j => pw1 (hmu j))

theorem incr_b (kap : ℚ) (hk : |kap| ≤ T) (j : Fin d) :
    |rndV p ((kap * Y) • (((B *ᵥ ξ) ⬝ᵥ mu) • (B *ᵥ ξ) - B *ᵥ (Bᵀ *ᵥ mu))) j| ≤ T ^ 27 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  obtain ⟨hu, hv, huv⟩ := incr_u hT hd Y B mu ξ hB hmu hξ hY
  have hBv : |(B *ᵥ (Bᵀ *ᵥ mu)) j| ≤ T ^ 8 :=
    bnd_up hT1 (bnd_mulVec (a := 1) (b := 3) hT1 hd (fun i j => pw1 (hB i j)) hv j) (by norm_num)
  have hdiff : |(((B *ᵥ ξ) ⬝ᵥ mu) • (B *ᵥ ξ) - B *ᵥ (Bᵀ *ᵥ mu)) j| ≤ T ^ 9 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact bnd_sub hT2 (bnd_mul huv (hu j)) hBv
  show |rnd p ((kap * Y) * (((B *ᵥ ξ) ⬝ᵥ mu) • (B *ᵥ ξ) - B *ᵥ (Bᵀ *ᵥ mu)) j)| ≤ T ^ 27
  exact bnd_up hT1 (bnd_rnd hT2 p (bnd_mul (bnd_mul (pw1 hk) hY) hdiff)) (by norm_num)

theorem incr_k (kap : ℚ) (hk : |kap| ≤ T) :
    |rnd p (kap * Y / 2 * (((B *ᵥ ξ) ⬝ᵥ mu) ^ 2 - (Bᵀ *ᵥ mu) ⬝ᵥ (Bᵀ *ᵥ mu)))| ≤ T ^ 27 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  obtain ⟨-, hv, huv⟩ := incr_u hT hd Y B mu ξ hB hmu hξ hY
  have hsq : |((B *ᵥ ξ) ⬝ᵥ mu) ^ 2| ≤ T ^ 10 := by rw [sq]; exact bnd_mul huv huv
  have hvv : |(Bᵀ *ᵥ mu) ⬝ᵥ (Bᵀ *ᵥ mu)| ≤ T ^ 10 := bnd_up hT1 (bnd_dot hT1 hd hv hv) (by norm_num)
  exact bnd_up hT1 (bnd_rnd hT2 p (bnd_mul (bnd_div2 (bnd_mul (pw1 hk) hY)) (bnd_sub hT2 hsq hvv))) (by norm_num)

theorem incr_g (nu : ℚ) (hn : |nu| ≤ T) (j : Fin d) : |rndV p ((Y * nu) • (B *ᵥ ξ)) j| ≤ T ^ 19 := by
  have hT2 : (2 : ℚ) ≤ T := by linarith
  obtain ⟨hu, -, -⟩ := incr_u hT hd Y B mu ξ hB hmu hξ hY
  show |rnd p ((Y * nu) * (B *ᵥ ξ) j)| ≤ T ^ 19
  exact bnd_rnd hT2 p (bnd_mul (bnd_mul hY (pw1 hn)) (hu j))

theorem incr_l (nu : ℚ) (hn : |nu| ≤ T) : |rnd p (rndV p ((Y * nu) • (B *ᵥ ξ)) ⬝ᵥ mu)| ≤ T ^ 27 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  exact bnd_up hT1 (bnd_rnd hT2 p (bnd_dot (a := 19) (b := 1) hT1 hd (incr_g hT hd p Y B mu ξ hB hmu hξ hY nu hn)
    (fun j => pw1 (hmu j)))) (by norm_num)

end Incr

theorem acc_bnd {T : ℚ} (hT : 1 ≤ T) {t : ℕ} {x y : ℚ} (hx : |x| ≤ t * T ^ 30) (hy : |y| ≤ T ^ 27) :
    |x + y| ≤ ((t + 1 : ℕ) : ℚ) * T ^ 30 := by
  have h := pow_le_pow_right₀ hT (show 27 ≤ 30 by norm_num)
  have := abs_add_le x y
  push_cast
  linarith

/-! ## One round -/

/-- The state that R15 COMMIT writes keeps the bounds. -/
theorem commit_bnd {cfg : Cfg d} {T : ℚ} (hc : CfgB T cfg) {st : St d} {t : ℕ} (hs : StI T cfg.par.Rint t st)
    (ξ : Fin d → ℚ) (hξ : ∀ i, |ξ i| ≤ T) (mu' : Fin d → ℚ) (hmu : ∀ j, |mu' j| ≤ cfg.par.Rint)
    (A' B' : Matrix (Fin d) (Fin d) ℚ)
    (hfr : ¬(2 * (cfg.par.Lam : ℚ) < frob2 B' ∨ 2 * (cfg.par.Lam : ℚ) < frob2 A')) (Y : ℚ) (hY : |Y| ≤ T ^ 14) :
    StI T cfg.par.Rint (t + 1) ⟨false, mu', A', B',
      st.b + rndV cfg.par.p ((cfg.par.kapc * Y) • (((st.B *ᵥ ξ) ⬝ᵥ st.mu) • (st.B *ᵥ ξ) - st.B *ᵥ (st.Bᵀ *ᵥ st.mu))),
      st.k + rnd cfg.par.p (cfg.par.kapc * Y / 2 * (((st.B *ᵥ ξ) ⬝ᵥ st.mu) ^ 2 - (st.Bᵀ *ᵥ st.mu) ⬝ᵥ (st.Bᵀ *ᵥ st.mu))),
      st.G + rndV cfg.par.p ((Y * cfg.par.nu) • (st.B *ᵥ ξ)),
      st.l + rnd cfg.par.p (rndV cfg.par.p ((Y * cfg.par.nu) • (st.B *ᵥ ξ)) ⬝ᵥ st.mu)⟩ := by
  have hT1 : (1 : ℚ) ≤ T := by linarith [hc.T4]
  have hT2 : (2 : ℚ) ≤ T := by linarith [hc.T4]
  have hmuT : ∀ j, |st.mu j| ≤ T := fun j => (hs.mu j).trans hc.R
  push_neg at hfr
  refine ⟨frob_entry_le hT2 hc.Lam _ (not_lt.2 hfr.2), frob_entry_le hT2 hc.Lam _ (not_lt.2 hfr.1), hmu,
    fun j => ?_, ?_, fun j => ?_, ?_⟩
  · exact acc_bnd hT1 (hs.b j) (incr_b hc.T4 hc.d _ _ st.B st.mu ξ hs.B hmuT hξ hY _ hc.kapc j)
  · exact acc_bnd hT1 hs.k (incr_k hc.T4 hc.d _ _ st.B st.mu ξ hs.B hmuT hξ hY _ hc.kapc)
  · exact acc_bnd hT1 (hs.G j)
      (bnd_up hT1 (incr_g hc.T4 hc.d _ _ st.B st.mu ξ hs.B hmuT hξ hY _ hc.nu j) (by norm_num))
  · exact acc_bnd hT1 hs.l (incr_l hc.T4 hc.d _ _ st.B st.mu ξ hs.B hmuT hξ hY _ hc.nu)

/-- **One round keeps the bounds.** -/
theorem step_bnd (ap : CallQ d → Option (Fin d → ℚ)) (hap : ∀ D y, ap D = some y → ∀ j, |y j| ≤ D.R)
    {cfg : Cfg d} {T : ℚ} (hc : CfgB T cfg) (n : ℕ) {st : St d} {t : ℕ} (hs : StI T cfg.par.Rint t st)
    (ξ : Fin d → ℚ) (ζ : ℚ) (o : ℤ) (hξ : ∀ i, |ξ i| ≤ T) (hζ : |ζ| ≤ T) (ho0 : 0 ≤ (o : ℚ))
    (ho1 : (o : ℚ) ≤ 2 ^ cfg.par.p) {st' : St d} (h : step ap cfg n (.run st) ξ ζ o = .run st') :
    StI T cfg.par.Rint (t + 1) st' := by
  have hY := Y_bnd hc hs ξ ζ o hξ hζ ho0 ho1
  simp only [step] at h
  repeat' (first | split at h | split_ifs at h)
  all_goals (try (cases h))
  all_goals first
    | exact init_bnd (by linarith [hc.T4]) (Nat.cast_nonneg _) _ hc.A0 hc.B0 _
    | exact commit_bnd hc hs ξ hξ _ (hap _ _ ‹_›) _ _ ‹_› _ hY

end AdversarialBco.Bit.Transfer.BLM
