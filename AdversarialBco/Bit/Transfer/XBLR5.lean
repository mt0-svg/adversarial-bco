/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLInv
public import AdversarialBco.Bit.Transfer.XExpr

@[expose] public section

/-!
# BL's round on the machine, R5 YOBS

R5 computes `Y' = rnd_p(pt' (obs/2^p + ζ')/2 + 2 (pt' - 1)/ε')` (`step`, Bit/BLPure.lean). On the machine every
quantity is an integer: `pt' = ptN/ptD` (`ptD > 0`), `ζ' = Γ/(2 G)` with `G = 2^(2 p_B)` (`gOut`), `ε' = ε̂/2^pF`
(`ε̂ > 0`). With `U` and `V` of `yU`, `yV`, the quantity is `U/V`, and `rnd_p(U/V) = ⌊(2 U 2^p + V)/(2 V)⌋/2^p`
(`rnd_div`), one Euclidean quotient (`yHat`). `ieY` is that expression over the slots.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

/-! ## The integer layer -/

theorem floor_div_int (a b : ℤ) (hb : 0 < b) : ⌊(a : ℚ) / b⌋ = a / b := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
  exact_mod_cast Rat.floor_intCast_div_natCast a k

/-- `rnd_k (U/V) = ⌊(2 U 2^k + V)/(2 V)⌋/2^k` for `V > 0`. -/
theorem rnd_div (k : ℕ) (U V : ℤ) (hV : 0 < V) :
    rnd k ((U : ℚ) / V) = (((2 * U * 2 ^ k + V) / (2 * V) : ℤ) : ℚ) / 2 ^ k := by
  unfold rnd
  rw [← floor_div_int _ _ (by positivity)]
  have hV' : (V : ℚ) ≠ 0 := by exact_mod_cast hV.ne'
  congr 3
  push_cast
  field_simp

/-- The numerator of R5's quantity over the integers: `P = 2^p`, `PF = 2^pF`, `G = 2^(2 p_B)`. -/
def yU (P PF G ptN ptD obs gz eN : ℤ) : ℤ :=
  ptN * (obs * (G + G) + gz * P) * eN + ((ptN - ptD) + (ptN - ptD)) * PF * P * ((G + G) + (G + G))

/-- The denominator of R5's quantity. -/
def yV (P G ptD eN : ℤ) : ℤ := ptD * P * ((G + G) + (G + G)) * eN

/-- R5 as the program computes it: `⌊(2 U P + V)/(2 V)⌋`. -/
def yHat (P PF G ptN ptD obs gz eN : ℤ) : ℤ :=
  (yU P PF G ptN ptD obs gz eN * P + yU P PF G ptN ptD obs gz eN * P + yV P G ptD eN) /
    (yV P G ptD eN + yV P G ptD eN)

/-- **R5 on the integers.** -/
theorem yHat_eq (p pF g : ℕ) (ptN ptD obs gz eN : ℤ) (hD : 0 < ptD) (he : 0 < eN) :
    rnd p ((ptN : ℚ) / ptD * ((obs : ℚ) / 2 ^ p + (gz : ℚ) / 2 ^ g / 2) / 2 +
        2 * ((ptN : ℚ) / ptD - 1) / ((eN : ℚ) / 2 ^ pF)) =
      (yHat (2 ^ p) (2 ^ pF) (2 ^ g) ptN ptD obs gz eN : ℚ) / 2 ^ p := by
  have hV : 0 < yV (2 ^ p) (2 ^ g) ptD eN := by unfold yV; positivity
  have hx : (ptN : ℚ) / ptD * ((obs : ℚ) / 2 ^ p + (gz : ℚ) / 2 ^ g / 2) / 2 +
      2 * ((ptN : ℚ) / ptD - 1) / ((eN : ℚ) / 2 ^ pF) =
      (yU (2 ^ p) (2 ^ pF) (2 ^ g) ptN ptD obs gz eN : ℚ) / yV (2 ^ p) (2 ^ g) ptD eN := by
    have h1 : (ptD : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    have h2 : (eN : ℚ) ≠ 0 := by exact_mod_cast he.ne'
    unfold yU yV
    push_cast
    field_simp
    ring
  rw [hx, rnd_div _ _ _ hV]
  unfold yHat
  congr 3 <;> ring

/-- A point `z/2^k` of the grid: its numerator `qn k` is `z`. -/
theorem qn_div_pow (k : ℕ) (z : ℤ) : qn k ((z : ℚ) / 2 ^ k) = z := by
  unfold qn
  rw [div_mul_cancel₀ _ (by positivity), Int.floor_intCast]

theorem onG_div_pow (k : ℕ) (z : ℤ) : OnG k ((z : ℚ) / 2 ^ k) := by
  unfold OnG
  rw [qn_div_pow, div_mul_cancel₀ _ (by positivity)]

/-- A point of the grid is its numerator over `2^k`. -/
theorem eq_qn_div (k : ℕ) {x : ℚ} (h : OnG k x) : x = (qn k x : ℚ) / 2 ^ k := by
  unfold OnG at h
  rw [h, mul_div_cancel_right₀ _ (by positivity)]

/-- **R5 in BL's terms**: with `pt' = ptN/ptD`, `ζ' = Γ/2^g/2` and `ε'` on the grid `2^{-pF}` and positive, the
numerator of `Y'` on the grid `2^{-p}` is `yHat`. -/
theorem qn_Y (p pF g : ℕ) (pt ζ eps : ℚ) (obs ptN ptD gz : ℤ) (hD : 0 < ptD) (hpt : pt = (ptN : ℚ) / ptD)
    (hζ : ζ = (gz : ℚ) / 2 ^ g / 2) (he : OnG pF eps) (he0 : 0 < eps) :
    qn p (rnd p (pt * ((obs : ℚ) / 2 ^ p + ζ) / 2 + 2 * (pt - 1) / eps)) =
      yHat (2 ^ p) (2 ^ pF) (2 ^ g) ptN ptD obs gz (qn pF eps) := by
  have heN : 0 < qn pF eps := by
    have h := eq_qn_div pF he
    have : (0 : ℚ) < (qn pF eps : ℚ) / 2 ^ pF := h ▸ he0
    have : (0 : ℚ) < (qn pF eps : ℚ) := by
      rwa [div_pos_iff_of_pos_right (by positivity)] at this
    exact_mod_cast this
  conv_lhs => rw [hpt, hζ, eq_qn_div pF he]
  rw [yHat_eq p pF g ptN ptD obs gz _ hD heN, qn_div_pow]

/-! ## The expression -/

/-- `yU` over the slots `sP, sPF, sG, sN, sD, sO, sZ, sE` (`2^p, 2^pF, G, ptN, ptD, obs, Γ, ε̂`). -/
def ieYU (sP sPF sG sN sD sO sZ sE : ℕ) : IE :=
  let G2 : IE := .op .add (.sc sG) (.sc sG)
  .op .add (.op .mul (.op .mul (.sc sN) (.op .add (.op .mul (.sc sO) G2) (.op .mul (.sc sZ) (.sc sP)))) (.sc sE))
    (.op .mul (.op .mul (.op .mul (.op .add (.op .sub (.sc sN) (.sc sD)) (.op .sub (.sc sN) (.sc sD))) (.sc sPF))
      (.sc sP)) (.op .add G2 G2))

/-- `yV` over the slots. -/
def ieYV (sP sG sD sE : ℕ) : IE :=
  let G2 : IE := .op .add (.sc sG) (.sc sG)
  .op .mul (.op .mul (.op .mul (.sc sD) (.sc sP)) (.op .add G2 G2)) (.sc sE)

/-- `yHat` over the slots. -/
def ieY (sP sPF sG sN sD sO sZ sE : ℕ) : IE :=
  let U := ieYU sP sPF sG sN sD sO sZ sE
  let V := ieYV sP sG sD sE
  .ediv (.op .add (.op .add (.op .mul U (.sc sP)) (.op .mul U (.sc sP))) V) (.op .add V V)


/-! ## Linear bounds on the exponents -/

/-- `(a, b)` with `mag E ≤ a E + b` for every `E`. -/
def magL : IE → ℕ × ℕ
  | .sc _ => (1, 0)
  | .arr _ _ => (1, 0)
  | .op .mul a b => ((magL a).1 + (magL b).1, (magL a).2 + (magL b).2)
  | .op _ a b => (max (magL a).1 (magL b).1, max (magL a).2 (magL b).2 + 1)
  | .ediv a _ => magL a

/-- `(a, b)` with `top E ≤ a E + b` for every `E`. -/
def topL : IE → ℕ × ℕ
  | .sc _ => (1, 0)
  | .arr _ _ => (1, 0)
  | .op o a b => (max (magL (IE.op o a b)).1 (max (topL a).1 (topL b).1),
      max (magL (IE.op o a b)).2 (max (topL a).2 (topL b).2))
  | .ediv a b => (max (magL a).1 (max (topL a).1 (topL b).1), max (magL a).2 (max (topL a).2 (topL b).2))

theorem max_le_lin {x y a1 b1 a2 b2 E : ℕ} (hx : x ≤ a1 * E + b1) (hy : y ≤ a2 * E + b2) :
    max x y ≤ max a1 a2 * E + max b1 b2 := by
  have h1 : a1 * E ≤ max a1 a2 * E := Nat.mul_le_mul_right _ (le_max_left _ _)
  have h2 : a2 * E ≤ max a1 a2 * E := Nat.mul_le_mul_right _ (le_max_right _ _)
  have := le_max_left b1 b2
  have := le_max_right b1 b2
  omega

theorem mag_le_lin (E : ℕ) : ∀ e : IE, e.mag E ≤ (magL e).1 * E + (magL e).2
  | .sc _ => by simp [IE.mag, magL]
  | .arr _ _ => by simp [IE.mag, magL]
  | .op o a b => by
    have ha := mag_le_lin E a
    have hb := mag_le_lin E b
    cases o with
    | mul => simp only [IE.mag, magL]; rw [Nat.add_mul]; omega
    | add => simp only [IE.mag, magL]; have := max_le_lin ha hb; omega
    | sub => simp only [IE.mag, magL]; have := max_le_lin ha hb; omega
    | div => simp only [IE.mag, magL]; have := max_le_lin ha hb; omega
  | .ediv a _ => by simp only [IE.mag, magL]; exact mag_le_lin E a

theorem top_le_lin (E : ℕ) : ∀ e : IE, e.top E ≤ (topL e).1 * E + (topL e).2
  | .sc _ => by simp [IE.top, topL]
  | .arr _ _ => by simp [IE.top, topL]
  | .op o a b => by
    have hm := mag_le_lin E (.op o a b)
    simp only [IE.top, topL]
    exact max_le_lin hm (max_le_lin (top_le_lin E a) (top_le_lin E b))
  | .ediv a b => by
    simp only [IE.top, topL]
    exact max_le_lin (mag_le_lin E a) (max_le_lin (top_le_lin E a) (top_le_lin E b))

/-- The top exponent below `ℓ` from the linear bound. -/
theorem top_lt {e : IE} {a b E ℓ : ℕ} (h : topL e = (a, b)) (hl : a * E + b < ℓ) : e.top E < ℓ := by
  have := top_le_lin E e
  rw [h] at this
  exact lt_of_le_of_lt this hl

end AdversarialBco.Bit.Transfer.BLM
