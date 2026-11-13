/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMag
public import AdversarialBco.Bit.ApQ.Clear

@[expose] public section

/-!
# The exponent of BL's calls: `expBL : ExpBL`

The exponent of the routine's point is `λ + 1` or `p`, both at most `3 j + lg R̄ + lg(d²(d + 1)) + 7`
(`ellExp_le`), with `j = lg(1/(θ min(r, 1)))`. On the cleared call the factor `D_P` cancels in `θ`:
`1/θ` is `1` or `3 (tr(P) R̄ + |f|₁) R̄ / e` (`invθ_le`), with `tr(B'B'ᵀ) = frob2 B' ≤ 2Λ`. For each of BL's three
pairs (radius, accuracy), `1/e` and `1/r` are products of PARAM's values and of inverses of points of the grid
`2^{-pF}` (`pair_bnd`), so at the unit `T = 2^K`, `K = 80 G + 400 + E₀`, `1/(θ min(r, 1)) ≤ T^15`, `j ≤ 15 K` and the
exponent is at most `48 K ≤ 2·10^7 (d + size n + E₀ + 1)`. The junk values of `x/0 = 0` need no case: every identity
used holds in a field with `0⁻¹ = 0`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The exponent from `j` -/

theorem lgQ_le (x : ℚ) (u : ℕ) (h : x ≤ 2 ^ u) : lgQ x ≤ u := by
  unfold lgQ
  exact Nat.clog_le_of_le_pow (Nat.ceil_le.2 (by exact_mod_cast h))

/-- The exponent of the routine's point. -/
theorem ellExp_le (I : EllI d) : ellExp I ≤ 3 * I.j + Nat.clog 2 I.Rb + Nat.clog 2 (d ^ 2 * (d + 1)) + 7 := by
  unfold ellExp EllI.lam EllI.p
  split_ifs <;> omega

/-- `1/(θ min(r, 1))` from `1/θ` and `1/r`. -/
theorem X_le (I : EllI d) {T : ℚ} (hT : 1 ≤ T) {a b : ℕ} (hθ : |1 / I.θ| ≤ T ^ a) (hr : |I.r⁻¹| ≤ T ^ b) :
    1 / (I.θ * min I.r 1) ≤ T ^ (a + b) := by
  have hm : |1 / min I.r 1| ≤ T ^ b := by
    rcases le_total I.r 1 with h | h
    · rw [min_eq_left h, one_div]; exact hr
    · rw [min_eq_right h, div_one, abs_one]; exact one_le_pow₀ hT
  rw [← one_div_mul_one_div]
  exact (le_abs_self _).trans (bnd_mul hθ hm)

/-! ## The cleared objective -/

theorem LG_clear (D : BLP.CallQ d) :
    (clearQ D).LG = objDen D * (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) := by
  unfold EllI.LG
  have h1 : (((clearQ D).P.trace : ℤ) : ℚ) = objDen D * D.P.trace := by
    simp only [Matrix.trace, Matrix.diag, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ApQ.clearQ_P D i i
    exact_mod_cast this
  have h2 : (∑ i, |((clearQ D).f i : ℚ)|) / (clearQ D).Df = objDen D * ∑ i, |D.f i| := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := ApQ.clearQ_f D i
    have hq : ((clearQ D).f i : ℚ) / (clearQ D).Df = objDen D * D.f i := by exact_mod_cast h
    have hDf : (0 : ℚ) < (clearQ D).Df := by exact_mod_cast ApQ.linDen_pos D
    calc |((clearQ D).f i : ℚ)| / (clearQ D).Df = |((clearQ D).f i : ℚ) / (clearQ D).Df| := by
          rw [abs_div, abs_of_pos hDf]
      _ = |(objDen D : ℚ) * D.f i| := by rw [hq]
      _ = objDen D * |D.f i| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [h1, h2]
  ring

/-- **`1/θ` on a cleared call**: `1`, or `3 (tr(P) R̄ + |f|₁) R̄ / e`. -/
theorem invθ_le (D : BLP.CallQ d) {T : ℚ} (hT : 3 ≤ T) {a b : ℕ}
    (hL : abs (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) ≤ T ^ a) (hRb : ((clearQ D).Rb : ℚ) ≤ T)
    (he : |1 / D.e| ≤ T ^ b) : |1 / (clearQ D).θ| ≤ T ^ (1 + a + 1 + b) := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  unfold EllI.θ
  split_ifs
  · rw [div_one, abs_one]; exact one_le_pow₀ hT1
  · have hD : (objDen D : ℚ) ≠ 0 := by exact_mod_cast (ApQ.objDen_pos D).ne'
    rw [one_div_div, LG_clear, ApQ.clearQ_e]
    rw [show 3 * (↑(objDen D) * (D.P.trace * ↑(clearQ D).Rb + ∑ i, |D.f i|)) * ↑(clearQ D).Rb =
        ↑(objDen D) * (3 * (D.P.trace * ↑(clearQ D).Rb + ∑ i, |D.f i|) * ↑(clearQ D).Rb) by ring,
      mul_div_mul_left _ _ hD, div_eq_mul_one_div]
    exact bnd_mul (bnd_mul (bnd_mul (pw1 (by rw [abs_of_pos (by norm_num : (0 : ℚ) < 3)]; exact hT)) hL)
      (pw1 (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hRb))) he

theorem trace_mul_tr (Bp : Matrix (Fin d) (Fin d) ℚ) : (Bp * Bpᵀ).trace = frob2 Bp := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, frob2, sq]

theorem frob2_nonneg (Bp : Matrix (Fin d) (Fin d) ℚ) : 0 ≤ frob2 Bp :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## BL's three pairs (radius, accuracy) -/

theorem inv_grid {k : ℕ} {x : ℚ} (hx : OnG k x) : |x⁻¹| ≤ 2 ^ k := by
  have e : x = (qn k x : ℚ) / 2 ^ k := by
    unfold OnG at hx; rw [hx, eq_div_iff (by positivity)]
  rw [e]
  exact grid_inv_abs _ _

theorem inv_one_sub_grid {k : ℕ} {x : ℚ} (hx : OnG k x) : |(1 - x)⁻¹| ≤ 2 ^ k := by
  have e : 1 - x = (((2 : ℤ) ^ k - qn k x : ℤ) : ℚ) / 2 ^ k := by
    unfold OnG at hx; push_cast; rw [hx, eq_div_iff (by positivity)]; ring
  rw [e]
  exact grid_inv_abs _ _

theorem onG_dn (k : ℕ) (x : ℚ) : OnG k (dn k x) := by
  unfold OnG; rw [qn_dn]; unfold dn; field_simp

/-- **`1/e` and `1/r` for BL's three calls.** -/
theorem pair_bnd {n : ℕ} {T : ℚ} (hT : 128 ≤ T) (hNe : ((par d n).Ne : ℚ) ≤ T) (hdT : (d : ℚ) ≤ T)
    (hnT : (n : ℚ) ≤ T) (hR : |(par d n).R| ≤ T) (hpF : 2 * (2 : ℚ) ^ (par d n).pF ≤ T) {r e : ℚ}
    (h : (r, e) ∈ callRE (par d n) d n) : 0 ≤ e ∧ |1 / e| ≤ T ^ 7 ∧ |r⁻¹| ≤ T ^ 2 := by
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  have hp1 : (2 : ℚ) ^ (par d n).pF ≤ T := by
    have : (0 : ℚ) < 2 ^ (par d n).pF := by positivity
    linarith
  have he1 : |(1 - (par d n).eps)⁻¹| ≤ T := (inv_one_sub_grid (by rw [PieceA.par_eps]; exact onG_up _ _)).trans hp1
  have hsb : |(par d n).sb⁻¹| ≤ T := (inv_grid (by rw [PieceA.par_sb]; exact onG_dn _ _)).trans hp1
  have hNe0 : (0 : ℚ) ≤ (par d n).Ne := Nat.cast_nonneg _
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg _
  have habs : ∀ {x : ℚ}, 0 ≤ x → x ≤ T → |x| ≤ T ^ 1 := fun h0 h1 => by rw [abs_of_nonneg h0, pow_one]; exact h1
  have h8 : |(8 : ℚ)| ≤ T ^ 1 := habs (by norm_num) (by linarith)
  have hNd8 : |((par d n).Ne : ℚ) * d * 8| ≤ T ^ 3 := bnd_mul (bnd_mul (habs hNe0 hNe) (habs hd0 hdT)) h8
  -- `1/(r'/2)` for `r' = rB = s_b (1 - ε')`
  have hrB : |(BLP.rB (par d n))⁻¹| ≤ T ^ 2 := by
    unfold BLP.rB; rw [mul_inv, abs_mul, sq]
    exact mul_le_mul hsb he1 (abs_nonneg _) (by linarith)
  have hrB2 : |(BLP.rB (par d n) / 2)⁻¹| ≤ T ^ 2 := by
    unfold BLP.rB
    rw [inv_div, div_eq_mul_inv, mul_inv, abs_mul, abs_mul, abs_two, sq]
    have hs := inv_grid (k := (par d n).pF) (x := (par d n).sb) (by rw [PieceA.par_sb]; exact onG_dn _ _)
    calc 2 * (|(par d n).sb⁻¹| * |(1 - (par d n).eps)⁻¹|) = (2 * |(par d n).sb⁻¹|) * |(1 - (par d n).eps)⁻¹| := by
          ring
      _ ≤ T * T := mul_le_mul (by linarith) he1 (abs_nonneg _) (by linarith)
  simp only [callRE, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨by positivity, ?_, bnd_up hT1 (pw1 he1) (by norm_num)⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul (pw1 he1) (pw1 he1))) (by norm_num)
  · refine ⟨by positivity, ?_, hrB2⟩
    rw [one_div_div, div_eq_mul_inv, ← inv_pow]
    exact bnd_up hT1 (bnd_mul hNd8 (by rw [sq]; exact bnd_mul hrB hrB)) (by norm_num)
  · refine ⟨by unfold BLP.eBL; positivity, ?_, hrB2⟩
    unfold BLP.eBL
    rw [one_div_one_div]
    have h128 : |(128 : ℚ)| ≤ T ^ 1 := habs (by norm_num) hT
    have hn2 : |(n : ℚ) ^ 2| ≤ T ^ 2 := by rw [sq]; exact bnd_mul (habs (Nat.cast_nonneg _) hnT) (habs (Nat.cast_nonneg _) hnT)
    have hR2 : |(par d n).R ^ 2| ≤ T ^ 2 := by rw [sq]; exact bnd_mul (pw1 hR) (pw1 hR)
    have h3 : |128 * (n : ℚ) ^ 2| ≤ T ^ 3 := bnd_mul (a := 1) (b := 2) h128 hn2
    have h5 : |128 * (n : ℚ) ^ 2 * (par d n).R ^ 2| ≤ T ^ 5 := bnd_mul (a := 3) (b := 2) h3 hR2
    have h6 : |128 * (n : ℚ) ^ 2 * (par d n).R ^ 2 * d| ≤ T ^ 6 := bnd_mul (a := 5) (b := 1) h5 (habs hd0 hdT)
    exact bnd_mul (a := 1) (b := 6) (habs hNe0 hNe) h6

/-! ## The exponent -/

/-- The exponent of the unit. -/
def Kexp (d n E0 : ℕ) : ℕ := 80 * parG d n + 400 + E0

/-- **`expBL`: the exponent of BL's calls.** -/
theorem expBL : ExpBL := by
  refine ⟨20000000, 1, ?_⟩
  intro d n m E0 A b c S H g ℓq Bp f r e hd hn _ hfr hf hre
  set D := callOf (mkCfg d n m A b c S) H g ℓq r (Bp * Bpᵀ) f e with hDdef
  have hG := parG_ge (d := d) (n := n)
  obtain ⟨T, hTdef⟩ : ∃ T : ℚ, T = 2 ^ Kexp d n E0 := ⟨_, rfl⟩
  have hK : ∀ a, a ≤ Kexp d n E0 → (2 : ℚ) ^ a ≤ T := fun a h => hTdef ▸ pow_le_pow_right₀ (by norm_num) h
  have hT : (128 : ℚ) ≤ T := by
    calc (128 : ℚ) = 2 ^ 7 := by norm_num
      _ ≤ T := hK 7 (by unfold Kexp; omega)
  have hT1 : (1 : ℚ) ≤ T := by linarith
  have hT2 : (2 : ℚ) ≤ T := by linarith
  have hN : 75 * parG d n + 343 ≤ Kexp d n E0 := by unfold Kexp; omega
  obtain ⟨-, -, -, -, -, fR, fLam⟩ := fld_abs (d := d) (n := n) hd hn
  have hNe : ((par d n).Ne : ℚ) ≤ T := by
    have h := pv_abs (d := d) (n := n) hd hn (k := 18) (by norm_num)
    rw [pv_18 (d := d) (n := n), abs_of_nonneg (Int.natCast_nonneg _)] at h
    rw [par_Ne]
    exact (by exact_mod_cast h : ((BLP.Ne d n : ℕ) : ℚ) ≤ 2 ^ (75 * parG d n + 343)).trans (hK _ hN)
  have hdT : (d : ℚ) ≤ T := (by exact_mod_cast (d_le_G (n := n)) : (d : ℚ) ≤ 2 ^ parG d n).trans (hK _ (by unfold Kexp; omega))
  have hnT : (n : ℚ) ≤ T := (by exact_mod_cast (n_le_G hd hn) : (n : ℚ) ≤ 2 ^ parG d n).trans (hK _ (by unfold Kexp; omega))
  have hR : |(par d n).R| ≤ T := by
    refine (grid_abs (k := (par d n).pF) (by rw [PieceA.par_R]; exact onG_up _ _) ?_).trans (hK _ hN)
    rw [qn_par_R, ← pv_80 (d := d) (n := n)]
    exact pv_abs hd hn (by norm_num)
  have hpF : 2 * (2 : ℚ) ^ (par d n).pF ≤ T := by
    rw [← pow_succ']; exact hK _ (by unfold Kexp; omega)
  obtain ⟨he0, he, hr⟩ := pair_bnd hT hNe hdT hnT hR hpF hre
  -- `R̄ = R_int`
  have hRb : (clearQ D).Rb = (par d n).Rint := Nat.ceil_natCast _
  have hRbT : ((clearQ D).Rb : ℚ) ≤ T := by rw [hRb]; exact fR.trans (hK _ hN)
  have hRb0 : (0 : ℚ) ≤ (clearQ D).Rb := Nat.cast_nonneg _
  -- `tr(P) R̄ + |f|₁ ≤ T^4`
  have hL : abs (D.P.trace * (clearQ D).Rb + ∑ i, |D.f i|) ≤ T ^ 4 := by
    have htr : D.P.trace = frob2 Bp := trace_mul_tr Bp
    have h0 := frob2_nonneg Bp
    have hLam : (2 : ℚ) * (par d n).Lam ≤ T ^ 2 := by
      have h1 : ((par d n).Lam : ℚ) ≤ T := fLam.trans (hK _ hN)
      calc (2 : ℚ) * (par d n).Lam ≤ T * T := mul_le_mul hT2 h1 (Nat.cast_nonneg _) (by linarith)
        _ = T ^ 2 := by ring
    have hf1 : abs (∑ i, |D.f i|) ≤ T ^ 3 := by
      have hs : ∑ i, |D.f i| ≤ d * 2 ^ E0 := by
        calc ∑ i, |D.f i| ≤ ∑ _i : Fin d, (2 : ℚ) ^ E0 := Finset.sum_le_sum fun i _ => hf i
          _ = d * 2 ^ E0 := by simp
      have hE0 : (2 : ℚ) ^ E0 ≤ T := hK _ (by unfold Kexp; omega)
      rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      calc ∑ i, |D.f i| ≤ d * 2 ^ E0 := hs
        _ ≤ T * T := mul_le_mul hdT hE0 (by positivity) (by linarith)
        _ ≤ T * T * T := le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hT1
        _ = T ^ 3 := by ring
    have hP : |D.P.trace * (clearQ D).Rb| ≤ T ^ 3 := by
      rw [htr, abs_of_nonneg (mul_nonneg h0 hRb0), pow_succ]
      exact mul_le_mul (hfr.trans hLam) hRbT hRb0 (pow_nonneg (by linarith) _)
    exact bnd_add hT2 hP hf1
  have hθ := invθ_le D (by linarith) hL hRbT he
  have hX := X_le (clearQ D) hT1 hθ hr
  have hj : (clearQ D).j ≤ 15 * Kexp d n E0 := by
    apply lgQ_le
    rw [pow_mul', ← hTdef]
    exact hX.trans (pow_le_pow_right₀ hT1 (by norm_num))
  have hc1 : Nat.clog 2 (clearQ D).Rb ≤ Kexp d n E0 := by
    rw [hRb]
    apply Nat.clog_le_of_le_pow
    have h := pv_abs (d := d) (n := n) hd hn (k := 91) (by norm_num)
    rw [pv_91 (d := d) (n := n), ← Rint_eq, abs_of_nonneg (Int.natCast_nonneg _)] at h
    have h' : (par d n).Rint ≤ 2 ^ (75 * parG d n + 343) := by exact_mod_cast h
    exact h'.trans (Nat.pow_le_pow_right (by norm_num) hN)
  have hc2 : Nat.clog 2 (d ^ 2 * (d + 1)) ≤ Kexp d n E0 := by
    apply Nat.clog_le_of_le_pow
    have h1 : d ≤ 2 ^ parG d n := d_le_G (n := n)
    have h2 : d + 1 ≤ 2 ^ (parG d n + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := parG d n); omega
    calc d ^ 2 * (d + 1) ≤ (2 ^ parG d n) ^ 2 * 2 ^ (parG d n + 1) := Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) h2
      _ = 2 ^ (3 * parG d n + 1) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ Kexp d n E0 := Nat.pow_le_pow_right (by norm_num) (by unfold Kexp; omega)
  have hGle := parG_le (d := d) hd hn
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  calc ellExp (clearQ D) ≤ 3 * (clearQ D).j + Nat.clog 2 (clearQ D).Rb + Nat.clog 2 (d ^ 2 * (d + 1)) + 7 :=
        ellExp_le _
    _ ≤ 20000000 * (d + n.size + E0 + 1) ^ 1 := by
        rw [pow_one]; unfold Kexp at hj hc1 hc2; omega

end AdversarialBco.Bit.Transfer.BLM
