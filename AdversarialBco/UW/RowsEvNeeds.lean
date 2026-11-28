/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.EvCNeeds
public import AdversarialBco.Poly.Df2EvSIArith

@[expose] public section

/-!
# The needs of the events (c), (d), (e) of Theorem UW at T4U

`evNeedsUW : EvNeedsUW`, in two layers.

* **On a record with the facts of T4U** (`EvNeedsArith.TU`, `EvNeedsArith.SR`): `needC_gen`, `needE_gen`,
  `needD_gen`. The facts are those of Theorem U's arithmetic (Poly/Df2EvSIArith.lean: `14 + 3 log(dn) ≤ x`,
  `λ = 1/(725 d (36x)²)`, `1/√n ≤ ε`, `n δ_e/λ² ≤ 1`, ...) with `x = log(1/δ_e) ≥ 342`, `ε ≤ 1/4`, `u ≤ n` and the
  sure ranges `36x + 2 ≤ b0`, `b0 + 1 ≤ 3dL`, `18/ε ≤ y0 ≤ 7√L/ε`, the level `δc ≤ δ_e`,
  `log(1/δc) ≤ x + 7dx(u - 1)`. Theorem U's leaves give the tails, `V_c ≤ 1.1 n/λ²`, `V_e ≤ n/λ²`, the net
  (`lq_card`) and the logarithm at `δ_e` (`ev_log`, and `log_levelD`, a copy of `log_level_le`); `log_shift` moves the
  failure from `δ_e` to `δc`, which gives Lemma L: `ℓ^(c), ℓ^(e) ≤ 7dxu`, `0 ≤ ℓ^(d) ≤ 12dxu`. The ranges with the
  bias: `R'_c ≤ 7 √d x/(ελ)`, `R'_e ≤ 9 d x/(ελ)`, `R'_d ≤ 361 λ d x²/ε`; the bias of Lemma SK' is at most
  `156 d δ_e⁴/ε` per unit, so the bias and discretization terms are below `λ⁶`.
* **At T4U on the regime**: `tu_parW`, `sr_parW` derive the facts from `RegimeW` (Lemma D: the bootstrap
  `n ≥ 16 · 14500² L^{10}` from `ε ≤ 1/4`, hence `Λ_0 ≥ 342`; `n δ_0/λ² = 725² d² L⁴ n/N_0 ≤ 1`).
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly AdversarialBco.Poly.EvSI
open AdversarialBco.Unified.BLO (NeO)

namespace EvNeedsArith

/-! ## T4U on the regime -/

theorem n0W_real (d n : ℕ) : (n0W d n : ℝ) = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
  simp only [n0W, NeO, add_zero]
  push_cast
  ring

theorem exp14_le_c0 : Real.exp 14 ≤ 15 * 2 ^ 17 := by
  have h := Real.exp_one_lt_d9
  have h14 : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h14]
  calc Real.exp 1 ^ 14 ≤ (2.7182818286 : ℝ) ^ 14 := by gcongr
    _ ≤ 15 * 2 ^ 17 := by norm_num

theorem lvX_parW (d n : ℕ) (u : ℝ) : lvX (parW d n u) = Real.log (n0W d n : ℝ) := by
  show Real.log (1 / (1 / (n0W d n : ℝ))) = _
  rw [one_div_one_div]

theorem parW_de (d n : ℕ) (u : ℝ) : (parW d n u).δe = 1 / (n0W d n : ℝ) := rfl

theorem parW_Le_x (d n : ℕ) (u : ℝ) : (parW d n u).Le = 36 * lvX (parW d n u) := by
  show df2C0 * Real.log (1 / (1 / (n0W d n : ℝ))) = 36 * Real.log (1 / (1 / (n0W d n : ℝ)))
  rw [df2C0]

theorem parW_lam_x (d n : ℕ) (u : ℝ) :
    (parW d n u).lam = 1 / (725 * d * (36 * lvX (parW d n u)) ^ 2) := by
  rw [← parW_Le_x]
  show 1 / (df2oClam * d * _ ^ 2) = _
  rw [df2oClam]
  rfl

theorem parW_eps_eq (d n : ℕ) (u : ℝ) :
    (parW d n u).eps = 20 * 725 * (d * Real.sqrt d) * (parW d n u).Le ^ 5 * Real.sqrt u / Real.sqrt n := by
  show 20 * df2oClam * _ * _ ^ 5 * _ / _ = _
  rw [df2oClam]
  rfl

theorem parW_eps_sq (d n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    (parW d n u).eps ^ 2 * n = 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n u).Le ^ 10 * u := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  calc (parW d n u).eps ^ 2 * n = (20 * 725) ^ 2 * (d : ℝ) ^ 2 * Real.sqrt d ^ 2 * (parW d n u).Le ^ 10 *
        Real.sqrt u ^ 2 / Real.sqrt n ^ 2 * n := by rw [parW_eps_eq]; ring
    _ = 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n u).Le ^ 10 * u := by
        rw [Real.sq_sqrt (Nat.cast_nonneg d), Real.sq_sqrt hu, Real.sq_sqrt hn0.le]
        field_simp
        ring

/-- `14 + 3 log(d n) ≤ Λ_0`. -/
theorem parW_x14 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (u : ℝ) :
    14 + 3 * Real.log ((d : ℝ) * n) ≤ lvX (parW d n u) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdn : (0 : ℝ) < d * n := by positivity
  rw [lvX_parW, n0W_real]
  have e : (15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4) = (15 * 2 ^ 17 * n) * ((d : ℝ) * n) ^ 3 := by ring
  have hm : Real.log ((15 * 2 ^ 17 * n) * ((d : ℝ) * n) ^ 3) =
      Real.log (15 * 2 ^ 17 * (n : ℝ)) + 3 * Real.log ((d : ℝ) * n) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e, hm]
  have h1 : 14 ≤ Real.log (15 * 2 ^ 17 * (n : ℝ)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := exp14_le_c0
    nlinarith
  linarith

/-- The bootstrap of Lemma D: `ε ≤ 1/4` forces `n ≥ 16 · 14500² L^{10}`, hence `Λ_0 ≥ 342`. -/
theorem parW_x342 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) (heps : (parW d n u).eps ≤ 1 / 4) :
    342 ≤ lvX (parW d n u) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx14 := parW_x14 hd hn u
  have hlog0 : 0 ≤ Real.log ((d : ℝ) * n) := Real.log_nonneg (by nlinarith)
  have hL : 504 ≤ (parW d n u).Le := by rw [parW_Le_x]; linarith
  have hsq := parW_eps_sq d n hn (by linarith : (0 : ℝ) ≤ u)
  have he0 : 0 ≤ (parW d n u).eps := by
    rw [parW_eps_eq]; positivity
  have he2 : (parW d n u).eps ^ 2 ≤ 1 / 16 := by nlinarith
  -- `16 · 14500² · 504^{10} ≤ n`
  have hK : (16 * 14500 ^ 2 * 504 ^ 10 : ℝ) ≤ n := by
    have h1 : (504 : ℝ) ^ 10 ≤ (parW d n u).Le ^ 10 := pow_le_pow_left₀ (by norm_num) hL 10
    have h2 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
    have h3 : 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n u).Le ^ 10 * u ≤ n / 16 := by
      rw [← hsq]; nlinarith
    have h4 : 14500 ^ 2 * (504 : ℝ) ^ 10 ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n u).Le ^ 10 * u := by
      have h5 : (0 : ℝ) ≤ (parW d n u).Le ^ 10 := by positivity
      calc 14500 ^ 2 * (504 : ℝ) ^ 10 = 14500 ^ 2 * 1 * 504 ^ 10 * 1 := by ring
        _ ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n u).Le ^ 10 * u := by gcongr
    linarith
  -- `e^{82} ≤ 16 · 14500² · 504^{10}`
  have he82 : Real.exp 82 ≤ 16 * 14500 ^ 2 * 504 ^ 10 := by
    have h := Real.exp_one_lt_d9
    have h82 : Real.exp 82 = Real.exp 1 ^ 82 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h82]
    calc Real.exp 1 ^ 82 ≤ (2.7182818286 : ℝ) ^ 82 := by gcongr
      _ ≤ 16 * 14500 ^ 2 * 504 ^ 10 := by norm_num
  have hn82 : Real.exp 82 ≤ n := he82.trans hK
  rw [lvX_parW, n0W_real, Real.le_log_iff_exp_le (by positivity)]
  have e : Real.exp 342 = Real.exp 14 * Real.exp 82 ^ 4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h4 : Real.exp 82 ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le hn82 4
  have h3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  have hc := exp14_le_c0
  calc Real.exp 14 * Real.exp 82 ^ 4 ≤ (15 * 2 ^ 17) * (n : ℝ) ^ 4 := by gcongr
    _ = 15 * 2 ^ 17 * 1 * (n : ℝ) ^ 4 := by ring
    _ ≤ 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by gcongr


/-! ## Real helpers -/

theorem sqrt_le_of_le_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : Real.sqrt a ≤ b :=
  (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hb)

theorem le_sqrt_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ b) : a ≤ Real.sqrt b :=
  (Real.sqrt_sq ha).symm.trans_le (Real.sqrt_le_sqrt h)

theorem csqrt_le {c X Y : ℝ} (hc : 0 ≤ c) (hY : 0 ≤ Y) (h : c ^ 2 * X ≤ Y ^ 2) : c * Real.sqrt X ≤ Y := by
  have e : c * Real.sqrt X = Real.sqrt (c ^ 2 * X) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [e]
  exact sqrt_le_of_le_sq hY h

theorem le_of_sq_le_sq'' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h1 : |a| ≤ b := by
    rw [← Real.sqrt_sq_eq_abs]
    exact sqrt_le_of_le_sq hb h
  exact (le_abs_self a).trans h1

theorem sqrt_le_self_of_one_le {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ y :=
  sqrt_le_of_le_sq (by linarith) (by nlinarith)

/-- `log(A/(δc/k)) = log(A/(δ/k)) + (log(1/δc) - log(1/δ))`. -/
theorem log_shift (A δ δc k : ℝ) (hA : 0 < A) (hδ : 0 < δ) (hδc : 0 < δc) (hk : 0 < k) :
    Real.log (A / (δc / k)) = Real.log (A / (δ / k)) + (Real.log (1 / δc) - Real.log (1 / δ)) := by
  have e : A / (δc / k) = A / (δ / k) * (1 / δc) / (1 / δ) := by field_simp
  rw [e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  ring

/-- Theorem U's `log_level_le` (Poly/Df2EvSISDF.lean), copied: the logarithm of (d) at the failure `δ/7`. -/
theorem log_levelD (d : ℕ) (hd : 1 ≤ d) (δ n Cc Rc q lk Xv : ℝ) (hδ0 : 0 < δ)
    (hx : 14 ≤ Real.log (1 / δ)) (hn0 : 1 ≤ n) (hn : n * δ ≤ 1) (hC0 : 1 ≤ Cc) (hC : Cc ≤ (1 + 2 * 1 / δ ^ 4) ^ d)
    (hRc0 : 0 ≤ Rc) (hRc : Rc * δ ≤ 1) (hq0 : 0 ≤ q) (hq : q * δ ≤ 1) (hlk : 0 ≤ lk) (_hXv : 0 ≤ Xv)
    (hlX : lk * Real.sqrt Xv * δ ≤ 1) :
    0 ≤ Real.log (4 * (n * Cc) * max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) /
        (δ / 7)) ∧
      Real.log (4 * (n * Cc) * max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) /
        (δ / 7)) ≤ 12 * d * Real.log (1 / δ) := by
  set Y := 1 / δ with hYdef
  have hY0 : 0 < Y := by positivity
  have hδY : δ * Y = 1 := by rw [hYdef]; field_simp
  have hYe : Real.exp 14 ≤ Y := by
    have h := Real.exp_le_exp.2 hx
    rwa [Real.exp_log hY0] at h
  have hY56 : 56 ≤ Y := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 14)
    linarith
  have hY1 : 1 ≤ Y := by linarith
  have hinv2 : (δ ^ 2)⁻¹ = Y ^ 2 := by rw [hYdef]; field_simp
  have hle (z : ℝ) (hz : z * δ ≤ 1) : z ≤ Y := by
    rw [hYdef, le_div_iff₀ hδ0]; exact hz
  have hnY : n ≤ Y := hle n hn
  have hRcY : Rc ≤ Y := hle Rc hRc
  have hqY : q ≤ Y := hle q hq
  have hlkY : lk * Real.sqrt Xv ≤ Y := hle _ hlX
  set M := max ((δ ^ 2)⁻¹ * (Rc * q + δ ^ 2)) ((δ ^ 2)⁻¹ * Real.sqrt (lk ^ 2 * q ^ 2 * Xv)) with hM
  have hM1 : 1 ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    rw [hinv2]
    have hYd : Y ^ 2 * δ ^ 2 = 1 := by rw [← mul_pow, mul_comm, hδY, one_pow]
    nlinarith [mul_nonneg hRc0 hq0, sq_nonneg Y]
  have hM2 : M ≤ 2 * Y ^ 4 := by
    have hYd : Y ^ 2 * δ ^ 2 = 1 := by rw [← mul_pow, mul_comm, hδY, one_pow]
    apply max_le
    · rw [hinv2]
      have hRq : Rc * q ≤ Y * Y := mul_le_mul hRcY hqY hq0 hY0.le
      nlinarith [sq_nonneg Y]
    · rw [hinv2]
      have hs : Real.sqrt (lk ^ 2 * q ^ 2 * Xv) = lk * q * Real.sqrt Xv := by
        rw [show lk ^ 2 * q ^ 2 * Xv = (lk * q) ^ 2 * Xv by ring, Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg hlk hq0)]
      rw [hs]
      have h1 : lk * q * Real.sqrt Xv ≤ Y * Y := by
        calc lk * q * Real.sqrt Xv = (lk * Real.sqrt Xv) * q := by ring
          _ ≤ Y * Y := mul_le_mul hlkY hqY hq0 hY0.le
      nlinarith [sq_nonneg Y]
  have hArg : 4 * (n * Cc) * M / (δ / 7) = 28 * n * Cc * M * Y := by
    rw [hYdef]; field_simp; ring
  have hCcY : Cc ≤ Y ^ (5 * d) := by
    have h1 : (1 : ℝ) + 2 * 1 / δ ^ 4 = 1 + 2 * Y ^ 4 := by rw [hYdef]; field_simp
    have h2 : 1 + 2 * Y ^ 4 ≤ Y ^ 5 := by
      have : Y ^ 5 = Y * Y ^ 4 := by ring
      have : 1 ≤ Y ^ 4 := one_le_pow₀ hY1
      nlinarith
    calc Cc ≤ (1 + 2 * 1 / δ ^ 4) ^ d := hC
      _ = (1 + 2 * Y ^ 4) ^ d := by rw [h1]
      _ ≤ (Y ^ 5) ^ d := pow_le_pow_left₀ (by positivity) h2 d
      _ = Y ^ (5 * d) := by rw [← pow_mul]
  have hn0' : 0 < n := by linarith
  have hC0' : 0 < Cc := by linarith
  have hM0 : 0 < M := by linarith
  have hpos : 0 < 28 * n * Cc * M * Y := by positivity
  rw [hArg]
  constructor
  · apply Real.log_nonneg
    have h1 : 1 ≤ n * Cc := one_le_mul_of_one_le_of_one_le hn0 hC0
    have h2 : 1 ≤ n * Cc * M := one_le_mul_of_one_le_of_one_le h1 hM1
    have h3 : 1 ≤ n * Cc * M * Y := one_le_mul_of_one_le_of_one_le h2 hY1
    nlinarith
  · have hup : 28 * n * Cc * M * Y ≤ Y ^ (12 * d) := by
      calc 28 * n * Cc * M * Y ≤ 28 * Y * Y ^ (5 * d) * (2 * Y ^ 4) * Y := by
            gcongr
        _ = 56 * Y ^ (5 * d + 6) := by ring
        _ ≤ Y * Y ^ (5 * d + 6) := by gcongr
        _ = Y ^ (5 * d + 7) := by ring
        _ ≤ Y ^ (12 * d) := pow_le_pow_right₀ hY1 (by omega)
    calc Real.log (28 * n * Cc * M * Y) ≤ Real.log (Y ^ (12 * d)) := Real.log_le_log hpos hup
      _ = 12 * d * Real.log (1 / δ) := by rw [Real.log_pow]; push_cast; ring

/-! ## The facts of T4U that the needs read -/

/-- The facts of the record (T4U on the regime). -/
structure TU (p : Df2OPar) (d n : ℕ) (u : ℝ) : Prop where
  hd : 1 ≤ d
  hn : 1 ≤ n
  hu : 1 ≤ u
  de0 : 0 < p.δe
  de1 : p.δe < 1
  hx14 : 14 + 3 * Real.log ((d : ℝ) * n) ≤ lvX p
  hx : 342 ≤ lvX p
  hLe : p.Le = 36 * lvX p
  hlam : p.lam = 1 / (725 * d * (36 * lvX p) ^ 2)
  eps0 : 0 < p.eps
  eps1 : p.eps ≤ 1 / 4
  epsn : 1 / Real.sqrt n ≤ p.eps
  hR : p.R = 134 * d * Real.sqrt (Real.log (2 * d + 2))
  hk0 : p.k0 = ((1 - p.lam) ^ 2)⁻¹
  cnu : n * p.δe / p.lam ^ 2 ≤ 1
  hsig : p.sig2 = 1 / (8 * p.Le)
  un : u ≤ n

/-- The facts of the sure ranges and the level. -/
structure SR (p : Df2OPar) (d : ℕ) (u b0 y0 δc : ℝ) : Prop where
  b0lo : 36 * lvX p + 2 ≤ b0
  b0hi : b0 + 1 ≤ 3 * d * p.Le
  y0lo : 18 / p.eps ≤ y0
  y0hi : y0 ≤ 7 * Real.sqrt p.Le / p.eps
  dc0 : 0 < δc
  dc1 : δc ≤ p.δe
  dcl : Real.log (1 / δc) ≤ lvX p + 7 * d * lvX p * (u - 1)

variable {p : Df2OPar} {d n : ℕ} {u b0 y0 δc : ℝ}

theorem TU.F (H : TU p d n u) :
    14 ≤ lvX p ∧ 0 < p.lam ∧ p.lam ≤ 1 / 1000 ∧ 144 * lvX p * p.lam ≤ 1 ∧ (d : ℝ) * p.lam ≤ 1 / 1000 ∧
      0 ≤ p.R * p.lam ∧ p.R * p.lam ≤ 1 / 10000 ∧ 1 / p.eps ≤ n ∧ n * p.δe ≤ p.lam ^ 2 ∧ p.δe ≤ p.lam ^ 2 ∧
      1 ≤ p.k0 ∧ p.k0 ≤ 21 / 20 :=
  arF d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.hx14 H.hlam H.eps0 H.epsn H.hR H.hk0 H.cnu

theorem TU.Qeq (H : TU p d n u) :
    lvQ p = (1 + p.δe) / (2 * (36 * lvX p) * p.lam ^ 2) + 2 * p.δe ^ 6 := by
  unfold lvQ; rw [H.hLe]

/-- `λ q ≤ (1 + 10⁻³)/(72 x λ) ≤ 1/(50 x λ)`. -/
theorem TU.Q (H : TU p d n u) : p.lam * lvQ p ≤ 1 / (50 * lvX p * p.lam) := by
  obtain ⟨hx1, hl0, hls, hlx, -, -, -, -, -, hde2, -, -⟩ := H.F
  have h := arQ p.δe (lvX p) p.lam H.de0 hx1 hl0 hls hlx hde2
  rw [← H.Qeq] at h
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 1) (by linarith : (0:ℝ) < lvX p)) hl0]

/-- `q ≥ 1/(72 x λ²)`. -/
theorem TU.Q_lo (H : TU p d n u) : 1 / (72 * lvX p * p.lam ^ 2) ≤ lvQ p := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have hde0 := H.de0
  rw [H.Qeq]
  have h1 : 1 / (72 * lvX p * p.lam ^ 2) ≤ (1 + p.δe) / (2 * (36 * lvX p) * p.lam ^ 2) := by
    rw [show (2 : ℝ) * (36 * lvX p) * p.lam ^ 2 = 72 * lvX p * p.lam ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h2 : 0 ≤ 2 * p.δe ^ 6 := by positivity
  linarith

theorem TU.Q0 (H : TU p d n u) : 0 < lvQ p := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  exact lt_of_lt_of_le (by positivity) H.Q_lo

/-- `q ≤ 1/λ²`. -/
theorem TU.Q_le (H : TU p d n u) : lvQ p ≤ 1 / p.lam ^ 2 := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have h := H.Q
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  have h2 : p.lam * lvQ p * (50 * lvX p * p.lam) = lvQ p * p.lam ^ 2 * (50 * lvX p) := by ring
  rw [h2] at h
  have hq := H.Q0
  nlinarith [mul_pos hq (pow_pos hl0 2)]

theorem TU.tailL (H : TU p d n u) :
    Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 105 * Real.exp (-(8 * lvX p) / 4)) ≤ 1 :=
  lq_tail d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu

theorem TU.tailD (H : TU p d n u) :
    Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * lvX p) ^ 2) / 4)) ≤ 1 :=
  dq_tail d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu

/-- `y_0 ≤ 3 x/ε`: `√L ≤ L/110` as `L ≥ 12312`. -/
theorem SR.y0x (H : TU p d n u) (S : SR p d u b0 y0 δc) : y0 ≤ 3 * lvX p / p.eps := by
  have hx := H.hx
  have he := H.eps0
  have hL : p.Le = 36 * lvX p := H.hLe
  have hsL : Real.sqrt p.Le ≤ p.Le / 110 :=
    sqrt_le_of_le_sq (by rw [hL]; positivity) (by rw [hL]; nlinarith)
  calc y0 ≤ 7 * Real.sqrt p.Le / p.eps := S.y0hi
    _ ≤ 7 * (p.Le / 110) / p.eps := by gcongr
    _ ≤ 3 * lvX p / p.eps := by
        apply div_le_div_of_nonneg_right _ he.le
        rw [hL]; linarith

theorem SR.y0_72 (H : TU p d n u) (S : SR p d u b0 y0 δc) : 72 ≤ y0 := by
  have he := H.eps0
  have h : 72 ≤ 18 / p.eps := by rw [le_div_iff₀ he]; linarith [H.eps1]
  linarith [S.y0lo]

/-! ## The bias of Lemma SK' -/

theorem TU.bias (H : TU p d n u) : 0 ≤ lvBias p d ∧ lvBias p d ≤ 156 * d * p.δe ^ 4 / p.eps := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have he0 := H.eps0
  have he1 : 1 ≤ 1 / p.eps := by rw [le_div_iff₀ he0]; linarith [H.eps1]
  have hde0 := H.de0
  have hde1 := H.de1
  have hsd : Real.sqrt d ≤ d := sqrt_le_self_of_one_le hd1
  have hs9 : Real.sqrt (p.δe ^ 9) ≤ p.δe ^ 4 := sqrt_le_of_le_sq (by positivity) (by
    rw [← pow_mul]; exact pow_le_pow_of_le_one hde0.le hde1.le (by norm_num))
  have h3 : 1 + 2 / p.eps ≤ 3 / p.eps := by
    have e1 : 2 / p.eps = 2 * (1 / p.eps) := by ring
    have e2 : 3 / p.eps = 3 * (1 / p.eps) := by ring
    linarith
  unfold lvBias
  constructor
  · positivity
  · calc 52 * Real.sqrt d * (1 + 2 / p.eps) * Real.sqrt (p.δe ^ 9) ≤ 52 * d * (3 / p.eps) * p.δe ^ 4 := by
          gcongr
      _ = 156 * d * p.δe ^ 4 / p.eps := by ring

/-! ## Event (c) -/

theorem TU.Vc (H : TU p d n u) : lvVc p d n ≤ 11 / 10 * n / p.lam ^ 2 := by
  have ht := H.tailL
  have ht0 : 0 ≤ Real.sqrt (lvWb p d) * Real.sqrt (Real.sqrt 105 * Real.exp (-(8 * lvX p) / 4)) := by positivity
  unfold lvVc
  rw [H.Qeq]
  exact lq_V d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu _ ht0 ht

theorem TU.Vc0 (H : TU p d n u) : 0 ≤ lvVc p d n := by
  obtain ⟨hx1, hl0, -, -, -, -, -, -, -, -, hk1, -⟩ := H.F
  have hq := H.Q0
  have hx0 : 0 ≤ lvX p := by linarith
  unfold lvVc
  apply mul_nonneg (by linarith)
  apply mul_nonneg hq.le
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hx0) (by positivity)
  · positivity

/-- The first term of the range of (c): `2/λ ≤ y0 √κ₀ √((b0 + 1) q) ≤ 4 √d x/(ε λ)`. -/
theorem rc1_bounds (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    2 / p.lam ≤ y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) * lvQ p) ∧
      y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) * lvQ p) ≤ 5 * (Real.sqrt d * lvX p / (p.eps * p.lam)) := by
  obtain ⟨hx1, hl0, hls, hlx, -, -, -, -, -, -, hk1, hk2⟩ := H.F
  have hx := H.hx
  have he := H.eps0
  have hq0 := H.Q0
  have hqlo := H.Q_lo
  have hq := H.Q
  have hy72 := S.y0_72 H
  have hy := S.y0x H
  have hb0 := S.b0lo
  have hb1 := S.b0hi
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hLe := H.hLe
  have hx0 : 0 < lvX p := by linarith
  have hbq0 : 0 ≤ (b0 + 1) * lvQ p := mul_nonneg (by linarith) hq0.le
  constructor
  · -- `(b0 + 1) q ≥ 36 x/(72 x λ²) = 1/(2λ²) ≥ (1/(2λ))²`
    have h1 : 1 / (2 * p.lam) ≤ Real.sqrt ((b0 + 1) * lvQ p) := by
      apply le_sqrt_of_sq_le (by positivity)
      calc (1 / (2 * p.lam)) ^ 2 ≤ (36 * lvX p) * (1 / (72 * lvX p * p.lam ^ 2)) := by
            rw [div_pow, mul_pow, show (36 * lvX p) * (1 / (72 * lvX p * p.lam ^ 2)) = 1 / (2 * p.lam ^ 2) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [pow_pos hl0 2]
        _ ≤ (b0 + 1) * lvQ p := by
            apply mul_le_mul (by linarith) hqlo (by positivity) (by linarith)
    have hsk : 1 ≤ Real.sqrt p.k0 := by rw [Real.one_le_sqrt]; exact hk1
    calc 2 / p.lam ≤ 72 * 1 * (1 / (2 * p.lam)) := by
          rw [show (72 : ℝ) * 1 * (1 / (2 * p.lam)) = 36 / p.lam by field_simp; ring]
          apply div_le_div_of_nonneg_right (by norm_num) hl0.le
      _ ≤ y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) * lvQ p) := by
          gcongr
  · apply le_of_sq_le_sq'' (by positivity)
    have hk0 : 0 ≤ p.k0 := by linarith
    rw [mul_pow, mul_pow, Real.sq_sqrt hk0, Real.sq_sqrt hbq0]
    have hy2 : y0 ^ 2 ≤ (3 * lvX p / p.eps) ^ 2 := pow_le_pow_left₀ (by linarith) hy 2
    have hqq : lvQ p ≤ 1 / (50 * lvX p * p.lam ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hq
      nlinarith
    have hbb : b0 + 1 ≤ 108 * d * lvX p := by rw [hLe] at hb1; linarith
    calc y0 ^ 2 * p.k0 * ((b0 + 1) * lvQ p) ≤
          (3 * lvX p / p.eps) ^ 2 * (21 / 20) * ((108 * d * lvX p) * (1 / (50 * lvX p * p.lam ^ 2))) := by
          gcongr
      _ = (9 * (21 / 20) * 108 / 50) * (d * lvX p ^ 2 / (p.eps ^ 2 * p.lam ^ 2)) := by
          field_simp; norm_num
      _ ≤ 25 * (d * lvX p ^ 2 / (p.eps ^ 2 * p.lam ^ 2)) := by
          gcongr
          norm_num
      _ = (5 * (Real.sqrt d * lvX p / (p.eps * p.lam))) ^ 2 := by
          rw [show (5 * (Real.sqrt d * lvX p / (p.eps * p.lam))) ^ 2 =
            25 * (Real.sqrt d ^ 2 * lvX p ^ 2 / (p.eps ^ 2 * p.lam ^ 2)) by ring, Real.sq_sqrt (by linarith)]

theorem TU.Bc (H : TU p d n u) : 0 ≤ lvBc p d ∧ lvBc p d ≤ 624 * d * p.δe ^ 4 / (p.eps * p.lam) := by
  obtain ⟨hx1, hl0, -, -, -, -, -, -, -, -, hk1, hk2⟩ := H.F
  obtain ⟨hb0, hb⟩ := H.bias
  have he := H.eps0
  have hq0 := H.Q0
  have hsk : Real.sqrt p.k0 ≤ 2 := sqrt_le_of_le_sq (by norm_num) (by linarith)
  have hsq : Real.sqrt (lvQ p) ≤ 1 / p.lam := sqrt_le_of_le_sq (by positivity) (by
    rw [div_pow, one_pow]; exact H.Q_le)
  unfold lvBc
  constructor
  · positivity
  · calc lvBias p d * (2 * Real.sqrt p.k0 * Real.sqrt (lvQ p)) ≤
          (156 * d * p.δe ^ 4 / p.eps) * (2 * 2 * (1 / p.lam)) := by gcongr
      _ = 624 * d * p.δe ^ 4 / (p.eps * p.lam) := by field_simp; ring

theorem TU.Rc (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    2 / p.lam ≤ lvRc p d b0 y0 ∧ lvRc p d b0 y0 ≤ 7 * (Real.sqrt d * lvX p / (p.eps * p.lam)) := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨h1lo, h1hi⟩ := rc1_bounds H S
  obtain ⟨hB0, hB⟩ := H.Bc
  have he := H.eps0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hR0 : 0 ≤ p.R := by rw [H.hR]; positivity
  have hR2 : 8 / p.eps * (2 * p.R) ≤ Real.sqrt d * lvX p / (p.eps * p.lam) :=
    lqd_R d (lvX p) p.lam p.eps p.R H.hd hx1 hl0 he hR0 hRl
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd1
  have hde0 := H.de0
  have hd4 : p.δe ^ 4 ≤ p.lam ^ 8 := by
    calc p.δe ^ 4 ≤ (p.lam ^ 2) ^ 4 := pow_le_pow_left₀ hde0.le hde2 4
      _ = p.lam ^ 8 := by ring
  have hB' : lvBc p d ≤ Real.sqrt d * lvX p / (p.eps * p.lam) := by
    refine hB.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have h8 : p.lam ^ 8 ≤ 1 := pow_le_one₀ hl0.le (by linarith)
    have h1 : (d : ℝ) * p.δe ^ 4 ≤ d * p.lam ^ 8 := by gcongr
    have h2 : (d : ℝ) * p.lam ^ 8 = (d * p.lam) * p.lam ^ 7 := by ring
    have h7 : p.lam ^ 7 ≤ 1 := pow_le_one₀ hl0.le (by linarith)
    have h3 : (d * p.lam) * p.lam ^ 7 ≤ 1 / 1000 * 1 := by
      apply mul_le_mul hdl h7 (by positivity) (by norm_num)
    nlinarith
  have hR20 : 0 ≤ 8 / p.eps * (2 * p.R) := by positivity
  unfold lvRc
  constructor
  · linarith
  · linarith

theorem TU.sqrtVc (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    Real.sqrt (lvVc p d n) ≤ Real.sqrt n * lvRc p d b0 y0 := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have hV := H.Vc
  have hRc := (H.Rc S).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have h1 : Real.sqrt (lvVc p d n) ≤ Real.sqrt n * (2 / p.lam) := by
    apply sqrt_le_of_le_sq (by positivity)
    rw [mul_pow, Real.sq_sqrt (by linarith), div_pow]
    calc lvVc p d n ≤ 11 / 10 * n / p.lam ^ 2 := hV
      _ ≤ n * (2 ^ 2 / p.lam ^ 2) := by
          rw [show (n : ℝ) * (2 ^ 2 / p.lam ^ 2) = 4 * n / p.lam ^ 2 by ring]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  calc Real.sqrt (lvVc p d n) ≤ Real.sqrt n * (2 / p.lam) := h1
    _ ≤ Real.sqrt n * lvRc p d b0 y0 := by gcongr

/-- **Lemma L (L1)**: `ℓ^(c) ≤ 7 d x u`. -/
theorem logC_le (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * p.R / p.δe ^ 4) ^ d) :
    lvLogC p d n b0 y0 δc Cc ≤ 7 * d * lvX p * u := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have hRc : 0 < lvRc p d b0 y0 := lt_of_lt_of_le (by positivity) (H.Rc S).1
  have hsV := H.sqrtVc S
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hsn : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  set Mx := max ((lvRc p d b0 y0)⁻¹ * lvRc p d b0 y0) ((lvRc p d b0 y0)⁻¹ * Real.sqrt (lvVc p d n)) with hMx
  have hM1 : 1 ≤ Mx := by rw [hMx, inv_mul_cancel₀ hRc.ne']; exact le_max_left _ _
  have hMn : Mx ≤ Real.sqrt n := by
    rw [hMx, inv_mul_cancel₀ hRc.ne']
    refine max_le hsn ?_
    rw [inv_mul_le_iff₀ hRc, mul_comm]
    exact hsV
  have hcard := lq_card d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu Cc hC1 hC
  have hlog := ev_log d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu Cc Mx 21 (by norm_num) le_rfl hC1 hcard hM1 hMn
  have hA : 0 < 4 * (n * Cc) * Mx := by positivity
  unfold lvLogC
  rw [← hMx, log_shift _ p.δe δc 21 hA H.de0 S.dc0 (by norm_num)]
  have hx : Real.log (1 / p.δe) = lvX p := rfl
  rw [hx]
  have hl := S.dcl
  nlinarith

/-- `n G δ⁴ ≤ 1/2` and `n β̄_c ≤ 1/2`. -/
theorem TU.smallC (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    n * lvGc p b0 y0 * p.δe ^ 4 + n * lvBc p d ≤ 1 := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨hB0, hB⟩ := H.Bc
  have he := H.eps0
  have hde0 := H.de0
  have hde1 := H.de1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hy := S.y0x H
  have hy72 := S.y0_72 H
  have hb1 := S.b0hi
  rw [H.hLe] at hb1
  have hbb : b0 + 1 ≤ 108 * d * lvX p := by linarith
  have hsk : Real.sqrt p.k0 ≤ 2 := sqrt_le_of_le_sq (by norm_num) (by linarith)
  have hbd1 : 1 ≤ (b0 + 1) / p.δe := by
    rw [le_div_iff₀ hde0]; have := S.b0lo; nlinarith
  have hsb : Real.sqrt ((b0 + 1) / p.δe) ≤ (b0 + 1) / p.δe := sqrt_le_self_of_one_le hbd1
  have hyn : y0 ≤ 3 * lvX p * n := by
    calc y0 ≤ 3 * lvX p / p.eps := hy
      _ = 3 * lvX p * (1 / p.eps) := by ring
      _ ≤ 3 * lvX p * n := by gcongr
  have hxl : lvX p * p.lam ≤ 1 / 144 := by linarith
  -- the discretization
  have hG : n * lvGc p b0 y0 * p.δe ^ 4 ≤ 1 / 4 := by
    unfold lvGc
    have e1 : (n : ℝ) * (y0 * Real.sqrt p.k0 * Real.sqrt ((b0 + 1) / p.δe) + 8 / p.eps) * p.δe ^ 4 =
        n * y0 * Real.sqrt p.k0 * (Real.sqrt ((b0 + 1) / p.δe) * p.δe ^ 4) + 8 * (n * (1 / p.eps)) * p.δe ^ 4 := by
      ring
    have e2 : (b0 + 1) / p.δe * p.δe ^ 4 = (b0 + 1) * p.δe ^ 3 := by field_simp
    rw [e1]
    calc (n : ℝ) * y0 * Real.sqrt p.k0 * (Real.sqrt ((b0 + 1) / p.δe) * p.δe ^ 4) +
          8 * (n * (1 / p.eps)) * p.δe ^ 4 ≤
          n * (3 * lvX p * n) * 2 * ((b0 + 1) / p.δe * p.δe ^ 4) + 8 * (n * n) * p.δe ^ 4 := by
          gcongr
      _ = n * (3 * lvX p * n) * 2 * ((b0 + 1) * p.δe ^ 3) + 8 * (n * n) * p.δe ^ 4 := by rw [e2]
      _ ≤ n * (3 * lvX p * n) * 2 * ((108 * d * lvX p) * p.δe ^ 3) + 8 * (n * n) * p.δe ^ 4 := by gcongr
      _ = 648 * (d : ℝ) * lvX p ^ 2 * ((n * p.δe) ^ 2 * p.δe) + 8 * ((n * p.δe) ^ 2 * p.δe ^ 2) := by ring
      _ ≤ 648 * (d : ℝ) * lvX p ^ 2 * ((p.lam ^ 2) ^ 2 * p.lam ^ 2) + 8 * ((p.lam ^ 2) ^ 2 * (p.lam ^ 2) ^ 2) := by
          gcongr
      _ = 648 * ((d : ℝ) * p.lam) * (lvX p * p.lam) ^ 2 * p.lam ^ 3 + 8 * p.lam ^ 8 := by ring
      _ ≤ 648 * (1 / 1000) * (1 / 144) ^ 2 * (1 / 1000) ^ 3 + 8 * (1 / 1000) ^ 8 := by gcongr
      _ ≤ 1 / 4 := by norm_num
  -- the bias
  have hBn : n * lvBc p d ≤ 1 / 4 := by
    calc (n : ℝ) * lvBc p d ≤ n * (624 * d * p.δe ^ 4 / (p.eps * p.lam)) := by gcongr
      _ = 624 * (n * (1 / p.eps)) * d * p.δe ^ 4 / p.lam := by field_simp
      _ ≤ 624 * (n * n) * d * p.δe ^ 4 / p.lam := by gcongr
      _ = 624 * ((d : ℝ) * p.lam) * ((n * p.δe) ^ 2 * p.δe ^ 2) / p.lam ^ 2 := by field_simp
      _ ≤ 624 * (1 / 1000) * ((p.lam ^ 2) ^ 2 * (p.lam ^ 2) ^ 2) / p.lam ^ 2 := by gcongr
      _ = 624 * (1 / 1000) * p.lam ^ 6 := by field_simp
      _ ≤ 624 * (1 / 1000) * (1 / 1000) ^ 6 := by gcongr
      _ ≤ 1 / 4 := by norm_num
  linarith

/-- **The need of (c)**. -/
theorem needC_gen (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * p.R / p.δe ^ 4) ^ d) :
    3 * Real.sqrt (lvVc p d n * lvLogC p d n b0 y0 δc Cc) +
      2 * lvRc p d b0 y0 * lvLogC p d n b0 y0 δc Cc +
      n * lvGc p b0 y0 * p.δe ^ 4 + n * lvBc p d ≤ b1W p d n u := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have he := H.eps0
  have hu := H.hu
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hV := H.Vc
  have hV0 := H.Vc0
  have hlog := logC_le H S Cc hC1 hC
  obtain ⟨hRlo, hRhi⟩ := H.Rc S
  have hR0 : 0 ≤ lvRc p d b0 y0 := le_trans (by positivity) hRlo
  have hsm := H.smallC S
  set ℓ := lvLogC p d n b0 y0 δc Cc
  have hx0 : 0 ≤ lvX p := by linarith
  have hlm0 : 0 ≤ 7 * d * lvX p * u := by positivity
  -- Freedman's variance term against `T₁`
  have h1 : 3 * Real.sqrt (lvVc p d n * ℓ) ≤ 1 / p.lam * (11 / 20 * Real.sqrt (10 * d * n * p.Le * u)) := by
    have hVl : lvVc p d n * ℓ ≤ 11 / 10 * n / p.lam ^ 2 * (7 * d * lvX p * u) :=
      (mul_le_mul_of_nonneg_left hlog hV0).trans (mul_le_mul_of_nonneg_right hV hlm0)
    apply csqrt_le (by norm_num) (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by rw [H.hLe]; positivity), H.hLe]
    calc (3 : ℝ) ^ 2 * (lvVc p d n * ℓ) ≤ 3 ^ 2 * (11 / 10 * n / p.lam ^ 2 * (7 * d * lvX p * u)) := by gcongr
      _ = 693 / 10 * (d * n * lvX p * u / p.lam ^ 2) := by field_simp; ring
      _ ≤ 1089 / 10 * (d * n * lvX p * u / p.lam ^ 2) := by gcongr; norm_num
      _ = (1 / p.lam) ^ 2 * ((11 / 20) ^ 2 * (10 * d * n * (36 * lvX p) * u)) := by field_simp; ring
  -- the range term against `T₂`
  have h2 : 2 * lvRc p d b0 y0 * ℓ ≤ 1 / p.lam * (13 / 100 * (d * Real.sqrt d) * p.Le ^ 2 * u / p.eps) := by
    have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    calc 2 * lvRc p d b0 y0 * ℓ ≤ 2 * lvRc p d b0 y0 * (7 * d * lvX p * u) := by gcongr
      _ ≤ 2 * (7 * (Real.sqrt d * lvX p / (p.eps * p.lam))) * (7 * d * lvX p * u) := by gcongr
      _ = 98 * (d * Real.sqrt d * lvX p ^ 2 * u / (p.eps * p.lam)) := by field_simp; ring
      _ ≤ 16848 / 100 * (d * Real.sqrt d * lvX p ^ 2 * u / (p.eps * p.lam)) := by gcongr; norm_num
      _ = 1 / p.lam * (13 / 100 * (d * Real.sqrt d) * p.Le ^ 2 * u / p.eps) := by
          rw [H.hLe]; field_simp; ring
  unfold b1W
  linarith



/-! ## Event (e) -/

theorem TU.Ve (H : TU p d n u) : lvVe p d n ≤ n / p.lam ^ 2 := by
  have ht := H.tailD
  have ht0 : 0 ≤ Real.sqrt (lvWb p d) *
      Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * lvX p) ^ 2) / 4)) := by positivity
  unfold lvVe
  rw [H.Qeq]
  exact dq_V d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu _ ht0 ht

theorem TU.Ve0 (_H : TU p d n u) : 0 ≤ lvVe p d n := by
  unfold lvVe; positivity

/-- `1 - λ ≥ 1/2` and `σ²`-facts. -/
theorem TU.lam1 (H : TU p d n u) : 0 < 1 - p.lam ∧ 1 / (1 - p.lam) ≤ 2 ∧ Real.sqrt (2 * d * p.sig2) ≤ d := by
  obtain ⟨hx1, hl0, hls, -⟩ := H.F
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  refine ⟨by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith)]; linarith
  · rw [H.hsig, H.hLe]
    apply (Real.sqrt_le_sqrt (show 2 * (d : ℝ) * (1 / (8 * (36 * lvX p))) ≤ d by
      rw [show 2 * (d : ℝ) * (1 / (8 * (36 * lvX p))) = d / (144 * lvX p) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]; nlinarith)).trans
    exact sqrt_le_self_of_one_le hd1

theorem TU.Re (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    1 / p.lam ≤ lvRe p d b0 y0 ∧ lvRe p d b0 y0 ≤ 9 * (d * lvX p / (p.eps * p.lam)) := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨hb0, hb⟩ := H.bias
  obtain ⟨h1l, h1l2, hsg⟩ := H.lam1
  have he := H.eps0
  have hde0 := H.de0
  have hde1 := H.de1
  have hx := H.hx
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hq0 := H.Q0
  have hq := H.Q
  have hqlo := H.Q_lo
  have hy72 := S.y0_72 H
  have hy := S.y0x H
  have hblo := S.b0lo
  have hb1 := S.b0hi
  rw [H.hLe] at hb1
  have hx0 : 0 < lvX p := by linarith
  have hbb : b0 + 2 ≤ 109 * d * lvX p := by nlinarith
  have hb00 : 0 ≤ b0 := by linarith
  have hb36 : 36 * lvX p ≤ b0 + 2 := by linarith
  have hy0 : 0 ≤ y0 := by linarith
  have hk0 : 0 ≤ p.k0 := by linarith
  have hlq : 1 / (72 * lvX p * p.lam) ≤ p.lam * lvQ p := by
    calc 1 / (72 * lvX p * p.lam) = p.lam * (1 / (72 * lvX p * p.lam ^ 2)) := by field_simp
      _ ≤ p.lam * lvQ p := by gcongr
  set c := 1 - p.lam with hc
  have hR1 : lvRe p d b0 y0 = y0 * p.k0 * (b0 + 2) * (p.lam * lvQ p) +
      8 / p.eps * (1 / c) * Real.sqrt (2 * d * p.sig2) * (p.lam * lvQ p) + lvBe p d := by
    unfold lvRe; rw [← hc]; ring
  have hBe : 0 ≤ lvBe p d ∧ lvBe p d ≤ d * lvX p / (p.eps * p.lam) := by
    unfold lvBe
    constructor
    · positivity
    · have hd4 : p.δe ^ 4 ≤ 1 := pow_le_one₀ hde0.le hde1.le
      calc lvBias p d * (7 * (p.lam * p.k0) * lvQ p) = lvBias p d * (7 * p.k0 * (p.lam * lvQ p)) := by ring
        _ ≤ (156 * d * p.δe ^ 4 / p.eps) * (7 * (21 / 20) * (1 / (50 * lvX p * p.lam))) := by gcongr
        _ ≤ (156 * d * 1 / p.eps) * (7 * (21 / 20) * (1 / (50 * lvX p * p.lam))) := by gcongr
        _ = (156 * 7 * (21 / 20) / 50) * (d / (lvX p * p.eps * p.lam)) := by field_simp
        _ ≤ (lvX p) ^ 2 * (d / (lvX p * p.eps * p.lam)) := by
            gcongr; nlinarith
        _ = d * lvX p / (p.eps * p.lam) := by field_simp
  rw [hR1]
  constructor
  · have h1 : 1 / p.lam ≤ y0 * p.k0 * (b0 + 2) * (p.lam * lvQ p) := by
      calc 1 / p.lam ≤ 72 * 1 * (36 * lvX p) * (1 / (72 * lvX p * p.lam)) := by
            rw [show (72 : ℝ) * 1 * (36 * lvX p) * (1 / (72 * lvX p * p.lam)) = 36 / p.lam by field_simp]
            apply div_le_div_of_nonneg_right (by norm_num) hl0.le
        _ ≤ y0 * p.k0 * (b0 + 2) * (p.lam * lvQ p) := by gcongr
    have h2 : 0 ≤ 8 / p.eps * (1 / c) * Real.sqrt (2 * d * p.sig2) * (p.lam * lvQ p) := by positivity
    linarith [hBe.1]
  · have h1 : y0 * p.k0 * (b0 + 2) * (p.lam * lvQ p) ≤ 7 * (d * lvX p / (p.eps * p.lam)) := by
      calc y0 * p.k0 * (b0 + 2) * (p.lam * lvQ p) ≤
            (3 * lvX p / p.eps) * (21 / 20) * (109 * d * lvX p) * (1 / (50 * lvX p * p.lam)) := by
            gcongr
        _ = (3 * (21 / 20) * 109 / 50) * (d * lvX p / (p.eps * p.lam)) := by field_simp
        _ ≤ 7 * (d * lvX p / (p.eps * p.lam)) := by gcongr; norm_num
    have h2 : 8 / p.eps * (1 / c) * Real.sqrt (2 * d * p.sig2) * (p.lam * lvQ p) ≤ d * lvX p / (p.eps * p.lam) := by
      calc 8 / p.eps * (1 / c) * Real.sqrt (2 * d * p.sig2) * (p.lam * lvQ p) ≤
            8 / p.eps * 2 * d * (1 / (50 * lvX p * p.lam)) := by gcongr
        _ = (16 / 50) * (d / (lvX p * p.eps * p.lam)) := by field_simp; ring
        _ ≤ (lvX p) ^ 2 * (d / (lvX p * p.eps * p.lam)) := by gcongr; nlinarith
        _ = d * lvX p / (p.eps * p.lam) := by field_simp
    linarith [hBe.2]

theorem TU.sqrtVe (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    Real.sqrt (lvVe p d n) ≤ Real.sqrt n * lvRe p d b0 y0 := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have hV := H.Ve
  have hRe := (H.Re S).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have h1 : Real.sqrt (lvVe p d n) ≤ Real.sqrt n * (1 / p.lam) := by
    apply sqrt_le_of_le_sq (by positivity)
    rw [mul_pow, Real.sq_sqrt (by linarith), div_pow, one_pow]
    calc lvVe p d n ≤ n / p.lam ^ 2 := hV
      _ = n * (1 / p.lam ^ 2) := by ring
  calc Real.sqrt (lvVe p d n) ≤ Real.sqrt n * (1 / p.lam) := h1
    _ ≤ Real.sqrt n * lvRe p d b0 y0 := by gcongr

/-- **Lemma L (L2)**: `ℓ^(e) ≤ 7 d x u`. -/
theorem logE_le (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * p.R / p.δe ^ 4) ^ d) :
    lvLogE p d n b0 y0 δc Cc ≤ 7 * d * lvX p * u := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have hRe : 0 < lvRe p d b0 y0 := lt_of_lt_of_le (by positivity) (H.Re S).1
  have hsV := H.sqrtVe S
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hsn : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  set Mx := max ((lvRe p d b0 y0)⁻¹ * lvRe p d b0 y0) ((lvRe p d b0 y0)⁻¹ * Real.sqrt (lvVe p d n)) with hMx
  have hM1 : 1 ≤ Mx := by rw [hMx, inv_mul_cancel₀ hRe.ne']; exact le_max_left _ _
  have hMn : Mx ≤ Real.sqrt n := by
    rw [hMx, inv_mul_cancel₀ hRe.ne']
    refine max_le hsn ?_
    rw [inv_mul_le_iff₀ hRe, mul_comm]
    exact hsV
  have hcard := lq_card d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu Cc hC1 hC
  have hlog := ev_log d n p.δe (lvX p) p.lam p.eps p.R p.k0 H.hd H.hn H.de0 H.de1 rfl H.hx14 H.hlam H.eps0
    (H.eps1.trans (by norm_num)) H.epsn H.hR H.hk0 H.cnu Cc Mx 8 (by norm_num) (by norm_num) hC1 hcard hM1 hMn
  have hA : 0 < 4 * (n * Cc) * Mx := by positivity
  unfold lvLogE
  rw [← hMx, log_shift _ p.δe δc 8 hA H.de0 S.dc0 (by norm_num)]
  have hx : Real.log (1 / p.δe) = lvX p := rfl
  rw [hx]
  have hl := S.dcl
  nlinarith

/-- The discretization and the bias of (e). -/
theorem TU.smallE (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    n * lvKe p d b0 y0 * (p.δe ^ 4 * (4 * p.R)) + n * lvBe p d ≤ 1 := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨hb0, hb⟩ := H.bias
  obtain ⟨h1l, h1l2, -⟩ := H.lam1
  have he := H.eps0
  have hde0 := H.de0
  have hde1 := H.de1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hy := S.y0x H
  have hy72 := S.y0_72 H
  have hblo := S.b0lo
  have hb1 := S.b0hi
  rw [H.hLe] at hb1
  have hx0 : 0 < lvX p := by linarith
  have hbb : b0 + 2 ≤ 109 * d * lvX p := by nlinarith
  have hb00 : 0 ≤ b0 := by linarith
  have hy0 : 0 ≤ y0 := by linarith
  have hk0 : 0 ≤ p.k0 := by linarith
  have hq := H.Q
  have hq0 := H.Q0
  have hR0 : 0 ≤ p.R := by rw [H.hR]; positivity
  have hyn : y0 ≤ 3 * lvX p * n := by
    calc y0 ≤ 3 * lvX p / p.eps := hy
      _ = 3 * lvX p * (1 / p.eps) := by ring
      _ ≤ 3 * lvX p * n := by gcongr
  have hxl : lvX p * p.lam ≤ 1 / 144 := by linarith
  have hdd : 1 ≤ (d : ℝ) / p.δe := by rw [le_div_iff₀ hde0]; linarith
  have hsdd : Real.sqrt ((d : ℝ) / p.δe) ≤ d / p.δe := sqrt_le_self_of_one_le hdd
  set c := 1 - p.lam with hc
  have hK : n * lvKe p d b0 y0 * (p.δe ^ 4 * (4 * p.R)) ≤ 1 / 4 := by
    have e1 : (n : ℝ) * lvKe p d b0 y0 * (p.δe ^ 4 * (4 * p.R)) =
        4 * n * (p.R * p.lam) * p.k0 * y0 * (b0 + 2) * p.δe ^ 3 +
          4 * n * (p.R * p.lam) * (8 * (1 / p.eps)) * (1 / c) * (Real.sqrt (d / p.δe) * p.δe ^ 4) := by
      unfold lvKe; rw [← hc]; field_simp
    have e2 : (d : ℝ) / p.δe * p.δe ^ 4 = d * p.δe ^ 3 := by field_simp
    rw [e1]
    calc 4 * n * (p.R * p.lam) * p.k0 * y0 * (b0 + 2) * p.δe ^ 3 +
          4 * n * (p.R * p.lam) * (8 * (1 / p.eps)) * (1 / c) * (Real.sqrt (d / p.δe) * p.δe ^ 4) ≤
          4 * n * (1 / 10000) * (21 / 20) * (3 * lvX p * n) * (109 * d * lvX p) * p.δe ^ 3 +
          4 * n * (1 / 10000) * (8 * n) * 2 * ((d : ℝ) / p.δe * p.δe ^ 4) := by gcongr
      _ = (4 * (21 / 20) * 3 * 109 / 10000) * (d : ℝ) * lvX p ^ 2 * ((n * p.δe) ^ 2 * p.δe) +
          (64 / 10000) * d * ((n * p.δe) ^ 2 * p.δe) := by rw [e2]; ring
      _ ≤ (4 * (21 / 20) * 3 * 109 / 10000) * (d : ℝ) * lvX p ^ 2 * ((p.lam ^ 2) ^ 2 * p.lam ^ 2) +
          (64 / 10000) * d * ((p.lam ^ 2) ^ 2 * p.lam ^ 2) := by gcongr
      _ = (4 * (21 / 20) * 3 * 109 / 10000) * ((d : ℝ) * p.lam) * (lvX p * p.lam) ^ 2 * p.lam ^ 3 +
          (64 / 10000) * ((d : ℝ) * p.lam) * p.lam ^ 5 := by ring
      _ ≤ (4 * (21 / 20) * 3 * 109 / 10000) * (1 / 1000) * (1 / 144) ^ 2 * (1 / 1000) ^ 3 +
          (64 / 10000) * (1 / 1000) * (1 / 1000) ^ 5 := by gcongr
      _ ≤ 1 / 4 := by norm_num
  have hB : n * lvBe p d ≤ 1 / 4 := by
    unfold lvBe
    calc (n : ℝ) * (lvBias p d * (7 * (p.lam * p.k0) * lvQ p)) =
          n * lvBias p d * (7 * p.k0 * (p.lam * lvQ p)) := by ring
      _ ≤ n * (156 * d * p.δe ^ 4 / p.eps) * (7 * (21 / 20) * (1 / (50 * lvX p * p.lam))) := by gcongr
      _ = (156 * 7 * (21 / 20) / 50) * (n * (1 / p.eps)) * d * p.δe ^ 4 / (lvX p * p.lam) := by
          field_simp
      _ ≤ (156 * 7 * (21 / 20) / 50) * (n * n) * d * p.δe ^ 4 / (lvX p * p.lam) := by gcongr
      _ = (156 * 7 * (21 / 20) / 50) * ((d : ℝ) * p.lam) * ((n * p.δe) ^ 2 * p.δe ^ 2) /
          (lvX p * p.lam ^ 2) := by field_simp
      _ ≤ (156 * 7 * (21 / 20) / 50) * (1 / 1000) * ((p.lam ^ 2) ^ 2 * (p.lam ^ 2) ^ 2) / (lvX p * p.lam ^ 2) := by
          gcongr
      _ = (156 * 7 * (21 / 20) / 50) * (1 / 1000) * p.lam ^ 6 / lvX p := by field_simp
      _ ≤ (156 * 7 * (21 / 20) / 50) * (1 / 1000) * 1 / 1 := by
          gcongr
          · exact pow_le_one₀ hl0.le (by linarith)
          · linarith
      _ ≤ 1 / 4 := by norm_num
  linarith

/-- **The need of (e)**. -/
theorem needE_gen (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * p.R / p.δe ^ 4) ^ d) :
    3 * Real.sqrt (lvVe p d n * lvLogE p d n b0 y0 δc Cc) +
      2 * lvRe p d b0 y0 * lvLogE p d n b0 y0 δc Cc +
      n * lvKe p d b0 y0 * (p.δe ^ 4 * (4 * p.R)) + n * lvBe p d ≤
    bnW p d n u / (p.Le * p.lam ^ 2) := by
  obtain ⟨hx1, hl0, hls, -⟩ := H.F
  have he := H.eps0
  have hu := H.hu
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hV := H.Ve
  have hV0 := H.Ve0
  have hlog := logE_le H S Cc hC1 hC
  obtain ⟨hRlo, hRhi⟩ := H.Re S
  have hR0 : 0 ≤ lvRe p d b0 y0 := le_trans (by positivity) hRlo
  have hsm := H.smallE S
  set ℓ := lvLogE p d n b0 y0 δc Cc
  have hx0 : 0 ≤ lvX p := by linarith
  have hlm0 : 0 ≤ 7 * d * lvX p * u := by positivity
  have hLe := H.hLe
  have hB : bnW p d n u / (p.Le * p.lam ^ 2) = p.Le / p.lam + p.Le / p.lam * Real.sqrt (10 * d * n * u) +
      p.Le / p.lam * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by
    unfold bnW; rw [hLe]; field_simp
  have h1 : 3 * Real.sqrt (lvVe p d n * ℓ) ≤ p.Le / p.lam * Real.sqrt (10 * d * n * u) := by
    have hVl : lvVe p d n * ℓ ≤ n / p.lam ^ 2 * (7 * d * lvX p * u) :=
      (mul_le_mul_of_nonneg_left hlog hV0).trans (mul_le_mul_of_nonneg_right hV hlm0)
    apply csqrt_le (by norm_num) (by rw [hLe]; positivity)
    rw [mul_pow, Real.sq_sqrt (by positivity), hLe]
    calc (3 : ℝ) ^ 2 * (lvVe p d n * ℓ) ≤ 3 ^ 2 * (n / p.lam ^ 2 * (7 * d * lvX p * u)) := by gcongr
      _ = 63 * (d * n * lvX p * u / p.lam ^ 2) := by field_simp; ring
      _ ≤ 12960 * lvX p * (d * n * lvX p * u / p.lam ^ 2) := by gcongr; nlinarith
      _ = (36 * lvX p / p.lam) ^ 2 * (10 * d * n * u) := by field_simp; ring
  have h2 : 2 * lvRe p d b0 y0 * ℓ ≤ p.Le / p.lam * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by
    calc 2 * lvRe p d b0 y0 * ℓ ≤ 2 * lvRe p d b0 y0 * (7 * d * lvX p * u) := by gcongr
      _ ≤ 2 * (9 * (d * lvX p / (p.eps * p.lam))) * (7 * d * lvX p * u) := by gcongr
      _ = 126 * ((d : ℝ) ^ 2 * lvX p ^ 2 * u / (p.eps * p.lam)) := by field_simp; ring
      _ ≤ 1296 * ((d : ℝ) ^ 2 * lvX p ^ 2 * u / (p.eps * p.lam)) := by gcongr; norm_num
      _ = p.Le / p.lam * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by rw [hLe]; field_simp; ring
  have h3 : 1 ≤ p.Le / p.lam := by
    rw [le_div_iff₀ hl0, hLe]; linarith
  rw [hB]
  linarith

/-! ## Event (d) -/

theorem TU.Xv (H : TU p d n u) : 0 ≤ lvXv p d n ∧ lvXv p d n ≤ 2305 * lvX p ^ 2 * n := by
  obtain ⟨hx1, -⟩ := H.F
  have ht := H.tailD
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  unfold lvXv
  constructor
  · positivity
  · have h1 : (n : ℝ) * (Real.sqrt (lvWb p d) *
        Real.sqrt (Real.sqrt 2027025 * Real.exp (-Real.sqrt ((16 * lvX p) ^ 2) / 4))) ≤ n * 1 := by gcongr
    have hx2 : (1 : ℝ) ≤ lvX p ^ 2 := by nlinarith
    have h2 : (n : ℝ) * 1 ≤ lvX p ^ 2 * n := by
      have := mul_le_mul_of_nonneg_right hx2 (by linarith : (0 : ℝ) ≤ n)
      linarith
    nlinarith

theorem TU.Rd (H : TU p d n u) (S : SR p d u b0 y0 δc) :
    0 ≤ lvRd0 p d b0 y0 ∧ lvRd0 p d b0 y0 ≤ 360 * (p.lam * d * lvX p ^ 2 / p.eps) ∧
      0 ≤ lvBd p d ∧ lvBd p d ≤ 1147 * (p.lam * d * p.δe ^ 4 / p.eps) ∧
      0 ≤ lvRd p d b0 y0 ∧ lvRd p d b0 y0 ≤ 361 * (p.lam * d * lvX p ^ 2 / p.eps) := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨hb0, hb⟩ := H.bias
  obtain ⟨h1l, h1l2, hsg⟩ := H.lam1
  have he := H.eps0
  have hde0 := H.de0
  have hde1 := H.de1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hy := S.y0x H
  have hy72 := S.y0_72 H
  have hblo := S.b0lo
  have hb1 := S.b0hi
  rw [H.hLe] at hb1
  have hx0 : 0 < lvX p := by linarith
  have hbb : b0 + 2 ≤ 109 * d * lvX p := by nlinarith
  have hb00 : 0 ≤ b0 := by linarith
  have hy0 : 0 ≤ y0 := by linarith
  have hk0 : 0 ≤ p.k0 := by linarith
  set c := 1 - p.lam with hc
  have hR0 : lvRd0 p d b0 y0 = p.lam * p.k0 * y0 * (b0 + 2) +
      p.lam * (8 / p.eps) * (1 / c) * Real.sqrt (2 * d * p.sig2) := by
    unfold lvRd0; rw [← hc]; ring
  have hRd0 : 0 ≤ lvRd0 p d b0 y0 ∧ lvRd0 p d b0 y0 ≤ 360 * (p.lam * d * lvX p ^ 2 / p.eps) := by
    rw [hR0]
    constructor
    · have : 0 ≤ b0 + 2 := by linarith
      positivity
    · have hld : p.lam * d / p.eps ≤ p.lam * d * lvX p ^ 2 / p.eps := by
        apply div_le_div_of_nonneg_right _ he.le
        have hx2 : (1 : ℝ) ≤ lvX p ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ p.lam * d)
        linarith
      have hA0 : 0 ≤ p.lam * d * lvX p ^ 2 / p.eps := by positivity
      calc p.lam * p.k0 * y0 * (b0 + 2) + p.lam * (8 / p.eps) * (1 / c) * Real.sqrt (2 * d * p.sig2) ≤
            p.lam * (21 / 20) * (3 * lvX p / p.eps) * (109 * d * lvX p) + p.lam * (8 / p.eps) * 2 * d := by
            gcongr
        _ = (21 / 20 * 3 * 109) * (p.lam * d * lvX p ^ 2 / p.eps) + 16 * (p.lam * d / p.eps) := by ring
        _ ≤ 360 * (p.lam * d * lvX p ^ 2 / p.eps) := by linarith
  have hBd : 0 ≤ lvBd p d ∧ lvBd p d ≤ 1147 * (p.lam * d * p.δe ^ 4 / p.eps) := by
    unfold lvBd
    constructor
    · positivity
    · calc lvBias p d * (7 * (p.lam * p.k0)) ≤ (156 * d * p.δe ^ 4 / p.eps) * (7 * (p.lam * (21 / 20))) := by
            gcongr
        _ = (156 * 7 * (21 / 20)) * (p.lam * d * p.δe ^ 4 / p.eps) := by field_simp
        _ ≤ 1147 * (p.lam * d * p.δe ^ 4 / p.eps) := by gcongr; norm_num
  have hd4 : p.δe ^ 4 ≤ lvX p ^ 2 / 1147 := by
    have h1 : p.δe ^ 4 ≤ 1 := pow_le_one₀ hde0.le hde1.le
    have h2 : (1147 : ℝ) ≤ lvX p ^ 2 := by have := H.hx; nlinarith
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hBd' : lvBd p d ≤ p.lam * d * lvX p ^ 2 / p.eps := by
    refine hBd.2.trans ?_
    rw [show 1147 * (p.lam * d * p.δe ^ 4 / p.eps) = (p.lam * d / p.eps) * (1147 * p.δe ^ 4) by ring,
      show p.lam * d * lvX p ^ 2 / p.eps = (p.lam * d / p.eps) * lvX p ^ 2 by ring]
    gcongr
    rw [le_div_iff₀ (by norm_num)] at hd4; linarith
  refine ⟨hRd0.1, hRd0.2, hBd.1, hBd.2, ?_, ?_⟩
  · unfold lvRd; linarith [hRd0.1, hBd.1]
  · unfold lvRd; linarith [hRd0.2]

/-- **Lemma L (L3)**: `0 ≤ ℓ^(d) ≤ 12 d x u`. -/
theorem logD_le (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc q : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * 1 / p.δe ^ 4) ^ d) (hq0 : 0 ≤ q) (hq : q * p.δe ≤ 1) :
    0 ≤ lvLogD p d n b0 y0 δc Cc q ∧ lvLogD p d n b0 y0 δc Cc q ≤ 12 * d * lvX p * u := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨-, -, -, -, hRd0, hRd⟩ := H.Rd S
  obtain ⟨hXv0, hXv⟩ := H.Xv
  have he := H.eps0
  have hde0 := H.de0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hu := H.hu
  have hx0 : 0 < lvX p := by linarith
  have hxl : lvX p * p.lam ≤ 1 / 144 := by linarith
  have hnde : (n : ℝ) * p.δe ≤ 1 := hnd.trans (pow_le_one₀ hl0.le (by linarith))
  have hRdd : lvRd p d b0 y0 * p.δe ≤ 1 := by
    calc lvRd p d b0 y0 * p.δe ≤ 361 * (p.lam * d * lvX p ^ 2 / p.eps) * p.δe := by gcongr
      _ = 361 * ((d : ℝ) * p.lam) * lvX p ^ 2 * ((1 / p.eps) * p.δe) := by ring
      _ ≤ 361 * ((d : ℝ) * p.lam) * lvX p ^ 2 * (n * p.δe) := by gcongr
      _ ≤ 361 * ((d : ℝ) * p.lam) * lvX p ^ 2 * p.lam ^ 2 := by gcongr
      _ = 361 * ((d : ℝ) * p.lam) * (lvX p * p.lam) ^ 2 := by ring
      _ ≤ 361 * (1 / 1000) * (1 / 144) ^ 2 := by gcongr
      _ ≤ 1 := by norm_num
  have hlk : 0 ≤ p.lam * p.k0 := by positivity
  have hde1' : p.δe ≤ 1 := H.de1.le
  have hlX : p.lam * p.k0 * Real.sqrt (lvXv p d n) * p.δe ≤ 1 := by
    apply le_of_sq_le_sq'' (by norm_num)
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hXv0, one_pow]
    calc p.lam ^ 2 * p.k0 ^ 2 * lvXv p d n * p.δe ^ 2 ≤
          p.lam ^ 2 * (21 / 20) ^ 2 * (2305 * lvX p ^ 2 * n) * p.δe ^ 2 := by gcongr
      _ = (21 / 20) ^ 2 * 2305 * (lvX p * p.lam) ^ 2 * ((n * p.δe) * p.δe) := by ring
      _ ≤ (21 / 20) ^ 2 * 2305 * (1 / 144) ^ 2 * (1 * 1) := by
          gcongr
      _ ≤ 1 := by norm_num
  have hx14 : 14 ≤ Real.log (1 / p.δe) := hx1
  obtain ⟨hl0', hl12⟩ := log_levelD d H.hd p.δe n Cc (lvRd p d b0 y0) q (p.lam * p.k0) (lvXv p d n) hde0 hx14
    hn1 hnde hC1 hC hRd0 hRdd hq0 hq hlk hXv0 hlX
  set Mx := max ((p.δe ^ 2)⁻¹ * (lvRd p d b0 y0 * q + p.δe ^ 2))
    ((p.δe ^ 2)⁻¹ * Real.sqrt ((p.lam * p.k0) ^ 2 * q ^ 2 * lvXv p d n)) with hMx
  have hM0 : 0 < Mx := lt_max_of_lt_left (by positivity)
  have hA : 0 < 4 * (n * Cc) * Mx := by
    have : (0 : ℝ) < Cc := by linarith
    positivity
  have hshift : Real.log (1 / p.δe) ≤ Real.log (1 / δc) := by
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le S.dc0 S.dc1
  unfold lvLogD
  rw [← hMx, log_shift _ p.δe δc 7 hA hde0 S.dc0 (by norm_num)]
  have hx : Real.log (1 / p.δe) = lvX p := rfl
  rw [hx] at hl12 hshift ⊢
  have hl := S.dcl
  constructor
  · linarith
  · have h5 : 5 * d * lvX p ≤ 5 * d * lvX p * u := by
      have : 0 ≤ 5 * d * lvX p := by positivity
      nlinarith
    nlinarith

/-- `B_n = λL² + λL² √(10dnu) + λL² d²Lu/ε` with `λL² = 1296 λ x² > 0`. -/
theorem TU.Bn (H : TU p d n u) :
    bnW p d n u = p.lam * p.Le ^ 2 + p.lam * p.Le ^ 2 * Real.sqrt (10 * d * n * u) +
      p.lam * p.Le ^ 2 * ((d : ℝ) ^ 2 * p.Le * u / p.eps) ∧
    p.lam * p.Le ^ 2 = 1296 * (p.lam * lvX p ^ 2) ∧ p.lam * p.Le ^ 2 ≤ bnW p d n u := by
  obtain ⟨hx1, hl0, -⟩ := H.F
  have he := H.eps0
  have hu := H.hu
  have hLe := H.hLe
  have hB : bnW p d n u = p.lam * p.Le ^ 2 + p.lam * p.Le ^ 2 * Real.sqrt (10 * d * n * u) +
      p.lam * p.Le ^ 2 * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by
    unfold bnW; ring
  refine ⟨hB, by rw [hLe]; ring, ?_⟩
  rw [hB]
  have h1 : 0 ≤ p.lam * p.Le ^ 2 * Real.sqrt (10 * d * n * u) := by positivity
  have h2 : 0 ≤ p.lam * p.Le ^ 2 * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by
    rw [hLe]
    have : 0 ≤ lvX p := by linarith
    have : 0 ≤ u := by linarith
    positivity
  linarith

/-- The sum form of (d). -/
theorem needD_sum (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc q : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * 1 / p.δe ^ 4) ^ d) (hq0 : 0 ≤ q) (hq : q * p.δe ≤ 1) :
    3 * (p.lam * p.k0) * Real.sqrt (lvXv p d n * lvLogD p d n b0 y0 δc Cc q) +
      2 * lvRd p d b0 y0 * lvLogD p d n b0 y0 δc Cc q + n * lvBd p d ≤ bnW p d n u := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨-, -, hBd0, hBd, hRdn, hRd⟩ := H.Rd S
  obtain ⟨hXv0, hXv⟩ := H.Xv
  obtain ⟨hl0', hl⟩ := logD_le H S Cc q hC1 hC hq0 hq
  obtain ⟨hBn, hA, -⟩ := H.Bn
  have he := H.eps0
  have hde0 := H.de0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast H.hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hu := H.hu
  have hx0 : 0 < lvX p := by linarith
  have hLe := H.hLe
  set ℓ := lvLogD p d n b0 y0 δc Cc q
  have hlm0 : 0 ≤ 12 * d * lvX p * u := by positivity
  have h1 : 3 * (p.lam * p.k0) * Real.sqrt (lvXv p d n * ℓ) ≤ p.lam * p.Le ^ 2 * Real.sqrt (10 * d * n * u) := by
    have hVl : lvXv p d n * ℓ ≤ 2305 * lvX p ^ 2 * n * (12 * d * lvX p * u) :=
      (mul_le_mul_of_nonneg_left hl hXv0).trans (mul_le_mul_of_nonneg_right hXv hlm0)
    have hk0 : 0 ≤ p.k0 := by linarith
    apply csqrt_le (by positivity) (by rw [hLe]; positivity)
    have hs : Real.sqrt (10 * d * n * u) ^ 2 = 10 * d * n * u := Real.sq_sqrt (by positivity)
    have hdnu : 0 ≤ (d : ℝ) * n * u := by positivity
    calc (3 * (p.lam * p.k0)) ^ 2 * (lvXv p d n * ℓ) = 9 * (p.lam ^ 2 * p.k0 ^ 2) * (lvXv p d n * ℓ) := by ring
      _ ≤ 9 * (p.lam ^ 2 * (21 / 20) ^ 2) * (2305 * lvX p ^ 2 * n * (12 * d * lvX p * u)) := by gcongr
      _ = (9 * (21 / 20) ^ 2 * 2305 * 12) * (p.lam ^ 2 * lvX p ^ 3 * (d * n * u)) := by ring
      _ ≤ (1296 ^ 2 * 10 * lvX p) * (p.lam ^ 2 * lvX p ^ 3 * (d * n * u)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
      _ = (p.lam * (36 * lvX p) ^ 2) ^ 2 * Real.sqrt (10 * d * n * u) ^ 2 := by rw [hs]; ring
      _ = (p.lam * p.Le ^ 2 * Real.sqrt (10 * d * n * u)) ^ 2 := by rw [hLe]; ring
  have h2 : 2 * lvRd p d b0 y0 * ℓ ≤ p.lam * p.Le ^ 2 * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by
    calc 2 * lvRd p d b0 y0 * ℓ ≤ 2 * lvRd p d b0 y0 * (12 * d * lvX p * u) := by gcongr
      _ ≤ 2 * (361 * (p.lam * d * lvX p ^ 2 / p.eps)) * (12 * d * lvX p * u) := by gcongr
      _ = 8664 * (p.lam * d ^ 2 * lvX p ^ 3 * u / p.eps) := by ring
      _ ≤ 46656 * (p.lam * d ^ 2 * lvX p ^ 3 * u / p.eps) := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = p.lam * p.Le ^ 2 * ((d : ℝ) ^ 2 * p.Le * u / p.eps) := by rw [hLe]; ring
  have h3 : n * lvBd p d ≤ p.lam * p.Le ^ 2 := by
    have h7 : p.lam ^ 7 ≤ 1 := pow_le_one₀ hl0.le (by linarith)
    calc (n : ℝ) * lvBd p d ≤ n * (1147 * (p.lam * d * p.δe ^ 4 / p.eps)) := by gcongr
      _ = 1147 * p.lam * d * (n * (1 / p.eps)) * p.δe ^ 4 := by ring
      _ ≤ 1147 * p.lam * d * (n * n) * p.δe ^ 4 := by gcongr
      _ = 1147 * p.lam * d * ((n * p.δe) ^ 2 * p.δe ^ 2) := by ring
      _ ≤ 1147 * p.lam * d * ((p.lam ^ 2) ^ 2 * (p.lam ^ 2) ^ 2) := by gcongr
      _ = 1147 * p.lam * ((d : ℝ) * p.lam) * p.lam ^ 7 := by ring
      _ ≤ 1147 * p.lam * (1 / 1000) * 1 := by gcongr
      _ ≤ 1296 * (p.lam * lvX p ^ 2) := by
          have hx2 : (1 : ℝ) ≤ lvX p ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hx2 hl0.le]
      _ = p.lam * p.Le ^ 2 := hA.symm
  rw [hBn]
  linarith

/-- The side rows of the net step of (d). -/
theorem needD_side (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc q : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * 1 / p.δe ^ 4) ^ d) (hq0 : 0 ≤ q) (hq : q * p.δe ≤ 1) :
    bnW p d n u * (2 * p.δe ^ 3) + 2 * p.δe ^ 2 * lvLogD p d n b0 y0 δc Cc q +
      2 * n * lvRd0 p d b0 y0 * p.δe ^ 3 ≤ 4 * p.δe * bnW p d n u := by
  obtain ⟨hx1, hl0, hls, hlx, hdl, hRl0, hRl, hen, hnd, hde2, hk1, hk2⟩ := H.F
  obtain ⟨hRd00, hRd0, -⟩ := H.Rd S
  obtain ⟨-, hl⟩ := logD_le H S Cc q hC1 hC hq0 hq
  obtain ⟨-, hA, hAB⟩ := H.Bn
  have he := H.eps0
  have hde0 := H.de0
  have hde1 := H.de1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hun := H.un
  have hx0 : 0 < lvX p := by linarith
  set ℓ := lvLogD p d n b0 y0 δc Cc q
  set B := bnW p d n u
  have hlx0 : 0 < p.lam * lvX p ^ 2 := by positivity
  have hB0 : 0 ≤ B := le_trans (by rw [hA]; positivity) hAB
  have hd2 : p.δe ^ 2 ≤ 1 := pow_le_one₀ hde0.le hde1.le
  have hAB' : 1296 * (p.lam * lvX p ^ 2) ≤ B := hA ▸ hAB
  have k1 : u * p.δe ≤ p.lam ^ 2 := (mul_le_mul_of_nonneg_right hun hde0.le).trans hnd
  have k2 : 24 * d * lvX p * u * p.δe ≤ 1296 * (p.lam * lvX p ^ 2) := by
    calc 24 * d * lvX p * u * p.δe = 24 * lvX p * d * (u * p.δe) := by ring
      _ ≤ 24 * lvX p * d * p.lam ^ 2 := by gcongr
      _ = 24 * (lvX p * p.lam) * (d * p.lam) := by ring
      _ ≤ 24 * (lvX p * p.lam) * (1 / 1000) := by gcongr
      _ ≤ 1296 * (p.lam * lvX p ^ 2) := by nlinarith [mul_pos hx0 hl0]
  have k3 : 2 * n * lvRd0 p d b0 y0 * p.δe ^ 2 ≤ 1296 * (p.lam * lvX p ^ 2) := by
    have h3 : p.lam ^ 3 ≤ 1 := pow_le_one₀ hl0.le (by linarith)
    calc 2 * n * lvRd0 p d b0 y0 * p.δe ^ 2 ≤ 2 * n * (360 * (p.lam * d * lvX p ^ 2 / p.eps)) * p.δe ^ 2 := by
          gcongr
      _ = 720 * (p.lam * lvX p ^ 2) * (d * (n * (1 / p.eps)) * p.δe ^ 2) := by ring
      _ ≤ 720 * (p.lam * lvX p ^ 2) * (d * (n * n) * p.δe ^ 2) := by gcongr
      _ = 720 * (p.lam * lvX p ^ 2) * (d * (n * p.δe) ^ 2) := by ring
      _ ≤ 720 * (p.lam * lvX p ^ 2) * (d * (p.lam ^ 2) ^ 2) := by gcongr
      _ = 720 * (p.lam * lvX p ^ 2) * (((d : ℝ) * p.lam) * p.lam ^ 3) := by ring
      _ ≤ 720 * (p.lam * lvX p ^ 2) * ((1 / 1000) * 1) := by gcongr
      _ ≤ 1296 * (p.lam * lvX p ^ 2) := by nlinarith
  have s1 : B * (2 * p.δe ^ 3) ≤ 2 * p.δe * B := by
    have e : B * (2 * p.δe ^ 3) = 2 * p.δe * B * p.δe ^ 2 := by ring
    rw [e]
    have : 0 ≤ 2 * p.δe * B := by positivity
    nlinarith
  have s2 : 2 * p.δe ^ 2 * ℓ ≤ p.δe * B := by
    calc 2 * p.δe ^ 2 * ℓ ≤ 2 * p.δe ^ 2 * (12 * d * lvX p * u) := by gcongr
      _ = p.δe * (24 * d * lvX p * u * p.δe) := by ring
      _ ≤ p.δe * (1296 * (p.lam * lvX p ^ 2)) := by gcongr
      _ ≤ p.δe * B := by gcongr
  have s3 : 2 * n * lvRd0 p d b0 y0 * p.δe ^ 3 ≤ p.δe * B := by
    calc 2 * n * lvRd0 p d b0 y0 * p.δe ^ 3 = p.δe * (2 * n * lvRd0 p d b0 y0 * p.δe ^ 2) := by ring
      _ ≤ p.δe * (1296 * (p.lam * lvX p ^ 2)) := by gcongr
      _ ≤ p.δe * B := by gcongr
  linarith

/-- **The need of (d)**. -/
theorem needD_gen (H : TU p d n u) (S : SR p d u b0 y0 δc) (Cc q : ℝ) (hC1 : 1 ≤ Cc)
    (hC : Cc ≤ (1 + 2 * 1 / p.δe ^ 4) ^ d) (hq0 : 0 ≤ q) (hq : q * p.δe ≤ 1) :
    0 ≤ lvLogD p d n b0 y0 δc Cc q ∧
    3 * (p.lam * p.k0) * Real.sqrt (lvXv p d n * lvLogD p d n b0 y0 δc Cc q) +
      2 * lvRd p d b0 y0 * lvLogD p d n b0 y0 δc Cc q + n * lvBd p d ≤ bnW p d n u ∧
    bnW p d n u * (2 * p.δe ^ 3) + 2 * p.δe ^ 2 * lvLogD p d n b0 y0 δc Cc q +
      2 * n * lvRd0 p d b0 y0 * p.δe ^ 3 ≤ 4 * p.δe * bnW p d n u :=
  ⟨(logD_le H S Cc q hC1 hC hq0 hq).1, needD_sum H S Cc q hC1 hC hq0 hq, needD_side H S Cc q hC1 hC hq0 hq⟩


/-- **The facts of T4U on the regime.** -/
theorem tu_parW {d n : ℕ} {ρ : RefW} (R : RegimeW d n ρ) : TU (parW d n ρ.u) d n ρ.u := by
  have hd := R.hd
  have hn := R.hn
  have hu := R.hu
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN := n0W_real d n
  have h3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have hNge : (15 * 2 ^ 17 : ℝ) ≤ n0W d n := by
    rw [hN]
    have : (1 : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le h3 h4
    nlinarith
  have hx14 := parW_x14 hd hn ρ.u
  have hx := parW_x342 hd hn hu R.heps
  have hLe := parW_Le_x d n ρ.u
  have hsq := parW_eps_sq d n hn (by linarith : (0 : ℝ) ≤ ρ.u)
  have hL1 : 1 ≤ (parW d n ρ.u).Le := by rw [hLe]; linarith
  have heps0 : 0 < (parW d n ρ.u).eps := by
    rw [parW_eps_eq]
    have : 0 < (parW d n ρ.u).Le := by linarith
    have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by linarith)
    have : 0 < Real.sqrt ρ.u := Real.sqrt_pos.2 (by linarith)
    have : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have : (0 : ℝ) < d := by linarith
    positivity
  have hL10 : (1 : ℝ) ≤ (parW d n ρ.u).Le ^ 10 := one_le_pow₀ hL1
  -- `16 · 14500² d³ L^{10} u ≤ n` from `ε ≤ 1/4`
  have hbig : 16 * (14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n ρ.u).Le ^ 10 * ρ.u) ≤ n := by
    rw [← hsq]
    have := R.heps
    have h2 : (parW d n ρ.u).eps ^ 2 ≤ 1 / 16 := by nlinarith
    nlinarith
  have hK1 : (1 : ℝ) ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n ρ.u).Le ^ 10 := by
    have : (1 : ℝ) ≤ 14500 ^ 2 * (d : ℝ) ^ 3 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le this hL10
  refine
    { hd := hd, hn := hn, hu := hu, de0 := ?_, de1 := ?_, hx14 := hx14, hx := hx, hLe := hLe,
      hlam := parW_lam_x d n ρ.u, eps0 := heps0, eps1 := R.heps, epsn := ?_, hR := rfl, hk0 := rfl,
      cnu := ?_, hsig := rfl, un := ?_ }
  · rw [parW_de]; positivity
  · rw [parW_de, div_lt_one (by linarith)]; linarith
  · have h1 : 1 ≤ (parW d n ρ.u).eps ^ 2 * n := by
      rw [hsq]; exact one_le_mul_of_one_le_of_one_le hK1 hu
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hsn]
    have h2 : 0 ≤ (parW d n ρ.u).eps * Real.sqrt n := by positivity
    have h3 : ((parW d n ρ.u).eps * Real.sqrt n) ^ 2 = (parW d n ρ.u).eps ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith
  · -- `n δ/λ² = 725² d² L⁴ n/N ≤ 1`
    have hNpos : (0 : ℝ) < n0W d n := by linarith
    have hLp : 0 < (parW d n ρ.u).Le := by linarith
    have e : (n : ℝ) * (parW d n ρ.u).δe / (parW d n ρ.u).lam ^ 2 =
        (n : ℝ) * (725 * d * (parW d n ρ.u).Le ^ 2) ^ 2 / n0W d n := by
      rw [parW_de, parW_lam_x, ← hLe]
      field_simp
    rw [e, div_le_one hNpos, hN]
    have hL4 : (parW d n ρ.u).Le ^ 4 ≤ (parW d n ρ.u).Le ^ 10 := pow_le_pow_right₀ hL1 (by norm_num)
    have hc : 725 ^ 2 * (parW d n ρ.u).Le ^ 4 ≤ n := by
      have h5 : 725 ^ 2 * (parW d n ρ.u).Le ^ 4 ≤ 16 * (14500 ^ 2 * 1 * (parW d n ρ.u).Le ^ 10 * 1) := by
        nlinarith
      have h6 : 16 * (14500 ^ 2 * 1 * (parW d n ρ.u).Le ^ 10 * 1) ≤
          16 * (14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n ρ.u).Le ^ 10 * ρ.u) := by
        gcongr
      linarith
    have hdn : (d : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := by
      have hd2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := pow_le_pow_right₀ hd1 (by norm_num)
      have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
      have : (d : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 :=
        mul_le_mul hd2 hn2 (by positivity) (by positivity)
      nlinarith [mul_pos (pow_pos (by linarith : (0 : ℝ) < d) 3) (pow_pos (by linarith : (0 : ℝ) < n) 4)]
    calc (n : ℝ) * (725 * d * (parW d n ρ.u).Le ^ 2) ^ 2 = (d : ℝ) ^ 2 * n * (725 ^ 2 * (parW d n ρ.u).Le ^ 4) := by
          ring
      _ ≤ (d : ℝ) ^ 2 * n * n := by gcongr
      _ = (d : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
      _ ≤ 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := hdn
  · have : ρ.u ≤ 14500 ^ 2 * (d : ℝ) ^ 3 * (parW d n ρ.u).Le ^ 10 * ρ.u := by
      have := mul_le_mul_of_nonneg_right hK1 (by linarith : (0 : ℝ) ≤ ρ.u)
      linarith
    linarith

/-- **The sure ranges and the level on the regime.** -/
theorem sr_parW {d n : ℕ} {ρ : RefW} (R : RegimeW d n ρ) : SR (parW d n ρ.u) d ρ.u ρ.b0 ρ.y0 ρ.δc := by
  have H := tu_parW R
  have hx := H.hx
  have hlx : lvX (parW d n ρ.u) = lam0 d n := lvX_parW d n ρ.u
  have hLe := parW_Le_x d n ρ.u
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast R.hd
  have he := H.eps0
  have he4 := R.heps
  refine ⟨?_, ?_, ?_, ?_, R.dc_pos, R.dc_le, ?_⟩
  · have := R.b0_lo; rw [hlx]; linarith
  · have hb := R.b0_hi
    rw [hLe, hlx]
    rw [hlx] at hx
    nlinarith
  · have := R.y0_lo
    have : 0 ≤ 10 * Real.sqrt (12 * lam0 d n) := by positivity
    linarith
  · have hy := R.y0_hi
    have h36 : 36 * lam0 d n = (parW d n ρ.u).Le := by rw [hLe, hlx]
    rw [h36] at hy
    have hL : 504 ≤ (parW d n ρ.u).Le := by rw [hLe]; linarith
    have hsL : 22 ≤ Real.sqrt (parW d n ρ.u).Le :=
      le_sqrt_of_sq_le (by norm_num) (by linarith)
    rw [le_div_iff₀ he]
    have h18 : 18 / (parW d n ρ.u).eps * (parW d n ρ.u).eps = 18 := div_mul_cancel₀ _ he.ne'
    calc ρ.y0 * (parW d n ρ.u).eps
        ≤ (11 + 18 / (parW d n ρ.u).eps + 10 * Real.sqrt (parW d n ρ.u).Le) * (parW d n ρ.u).eps :=
          mul_le_mul_of_nonneg_right hy he.le
      _ = 11 * (parW d n ρ.u).eps + 18 + 10 * Real.sqrt (parW d n ρ.u).Le * (parW d n ρ.u).eps := by
          rw [add_mul, add_mul, h18]
      _ ≤ 7 * Real.sqrt (parW d n ρ.u).Le := by nlinarith
  · have := R.dc_lvl
    unfold lvl at this
    rw [hlx]
    exact this

/-- The three needs at T4U on the regime. -/
theorem evNeedsW_of {d n : ℕ} {ρ : RefW} (R : RegimeW d n ρ) : EvNeedsW d n ρ := by
  have H := tu_parW R
  have S := sr_parW R
  exact ⟨fun Cc h1 h2 => needC_gen H S Cc h1 h2, fun Cc h1 h2 => needE_gen H S Cc h1 h2,
    fun Cc q h1 h2 h3 h4 => needD_gen H S Cc q h1 h2 h3 h4⟩

end EvNeedsArith

/-- **The needs of the events (c), (d), (e) on the regime.** -/
theorem evNeedsUW : EvNeedsUW := fun _ _ _ R => EvNeedsArith.evNeedsW_of R

end AdversarialBco.UW
