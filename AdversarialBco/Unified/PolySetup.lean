/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyGcd

@[expose] public section

/-!
# UNI-POLY, part 14: `SETUP`, the input of `P` in `P`'s cells

After the language prologue (`lp_run`, PolyLP.lean) the frame centre is in an array of the language, a denominator `D`
and numerators `x_j`. `SETUP` writes `P`'s input `inputU d n (1/(n+1)) (1/2) n a` into the cells `φ 0, φ 1, ...`: the
header `d, n, 1, n + 1, 1, 2, n, 1`, then each coordinate `x_j / D` in lowest terms (Euclid, `GCD`), and the address of
the buffer `Y` into `cYB`. The text reads `d` from the cell `0`; nothing in it depends on `d`.

* `rs_SETUP`: the cells `φ y` hold `hdr`, `cYB` the buffer address, every cell above `-500` and every scratch cell of
  the blocks as before.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM RCmd

/-! ## The text -/

/-- The header, first part: `zOne := 1`, `φ 0 := d`, `φ 1 := n`, `φ 2 := 1`, `φ 3 := n + 1`. -/
def HEAD1 : List Instr := [.const zOne 1, .add (-1000) 0 cZ, .add (-1002) 1 cZ, .const (-1004) 1, .add (-1006) 1 zOne]

/-- The header, second part: `φ 4 := 1`, `φ 5 := 2`, `φ 6 := n`, `φ 7 := 1`. -/
def HEAD2 : List Instr := [.const (-1008) 1, .const (-1010) 2, .add (-1012) 1 cZ, .const (-1014) 1]

/-- `cYB := off + 264 + d d + d`, `off` in the cell `-3`. -/
def YBF1 : List Instr := [.mul zT 0 0, .add zT zT 0, .const zFour 264, .add zT zT zFour, .add cYB (-3) zT]

/-- `zFB := off + M rF` (the frame centre), `zD := M zFB`, and the constants `4`, `-1016`, `2`. -/
def YBF2 (rF : ℤ) : List Instr :=
  [.add zFB (-3) rF, .load zD zFB, .const zFour 4, .const zP0 (-1016), .const zTwo 2, .const zT 0]

/-- `zX := x_j`, `zA := x_j`, `zB := D`. -/
def CO1 : List Instr := [.add zX zFB zOne, .add zX zX zJ, .load zX zX, .add zA zX cZ, .add zB zD cZ]

/-- `zN := x_j / g`, `zDn := D / g`, `zP := -1016 - 4 j`. -/
def CO2 : List Instr := [.div zN zX zA, .div zDn zD zA, .mul zP zJ zFour, .sub zP zP0 zP]

/-- `φ (8 + 2 j) := zN`, `φ (9 + 2 j) := zDn`, `zJ := j + 1`. -/
def CO3 : List Instr := [.store zP zN, .sub zP zP zTwo, .store zP zDn, .add zJ zJ zOne]

/-- The cells of the coordinate back at `0`. -/
def CO4 : List Instr := [.const zX 0, .const zA 0, .const zN 0, .const zDn 0, .const zP 0]

/-- One coordinate. -/
def COORD : RCmd := seqL [seqI CO1, GCD, seqI CO2, seqI CO3, seqI CO4]

/-- The setup, the frame centre's array base in the register `rF`. -/
def SETUPf (rF : ℤ) : RCmd := seqL [seqI HEAD1, seqI HEAD2, seqI YBF1, seqI (YBF2 rF), .whileLt zJ 0 COORD]

/-! ## The values -/

/-- The coordinate cells: `x_k / g_k` at `8 + 2 k`, `D / g_k` at `9 + 2 k`, `g_k = gcd(x_k, D)`. -/
def cv (x : ℕ → ℤ) (D : ℤ) (y : ℤ) : ℤ :=
  if (y - 8) % 2 = 0 then x ((y - 8) / 2).toNat / (Int.gcd (x ((y - 8) / 2).toNat) D : ℤ)
  else D / (Int.gcd (x ((y - 8) / 2).toNat) D : ℤ)

/-- `P`'s input cells. -/
def hdr (d n : ℕ) (x : ℕ → ℤ) (D : ℤ) (y : ℤ) : ℤ :=
  if y = 0 then d else if y = 1 then n else if y = 2 then 1 else if y = 3 then (n : ℤ) + 1 else if y = 4 then 1
  else if y = 5 then 2 else if y = 6 then n else if y = 7 then 1 else if 8 ≤ y ∧ y < 8 + 2 * d then cv x D y else 0

theorem φ_nat (y : ℤ) (hy : 0 ≤ y) : φ y = -1000 - 2 * y := by unfold φ; simp [hy, N0]

theorem φ_neg (y : ℤ) (hy : y < 0) : φ y = -1000 + 2 * y + 1 := by
  unfold φ; simp [show ¬ (0 ≤ y) by omega, N0]

/-! ## One coordinate -/

variable {d : ℕ} {w : World d} {L : ℕ}

set_option maxHeartbeats 1000000 in
/-- One coordinate: `φ (8 + 2 j) := x_j / g`, `φ (9 + 2 j) := D / g`, `zJ := j + 1`, `g = gcd(x_j, D)`. -/
theorem rs_COORD {v : State d} {j : ℕ} {FB D xj : ℤ} {s : ℕ}
    (hJ : v.mem zJ = j) (hFB : v.mem zFB = FB) (hOne : v.mem zOne = 1) (hD : v.mem zD = D)
    (hFour : v.mem zFour = 4) (hP0 : v.mem zP0 = -1016) (hTwo : v.mem zTwo = 2) (hz : v.mem cZ = 0)
    (hX : v.mem zX = 0) (hA : v.mem zA = 0) (hB : v.mem zB = 0) (hQ : v.mem zQ = 0) (hN : v.mem zN = 0)
    (hDn : v.mem zDn = 0) (hP : v.mem zP = 0)
    (hFB0 : 0 ≤ FB) (hx : v.mem (FB + 1 + j) = xj) (hD0 : 0 < D) (hDs : D < 2 ^ s) (hxs : |xj| < 2 ^ s)
    (hL1 : s + 2 ≤ L) (hL3 : FB + j + 2 < 2 ^ L) (hL5 : 4 * (j : ℤ) + 1020 < 2 ^ L) (h10 : 10 ≤ L) :
    RS w L COORD v (fun n v' => n ≤ 8 * (2 * s + 1) + 20 ∧ Same' v v' ∧
      v'.mem = Function.update (Function.update (Function.update v.mem (-1016 - (j : ℤ) * 4)
        (xj / (Int.gcd xj D : ℤ))) (-1016 - (j : ℤ) * 4 - 2) (D / (Int.gcd xj D : ℤ))) zJ ((j : ℤ) + 1)) := by
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hnat : ∀ y : ℤ, 0 ≤ y → y < 2 ^ L → len y ≤ L := fun y h0 hy => len_of_abs (by rw [abs_of_nonneg h0]) hy
  have hsL : (2 : ℤ) ^ s ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
  have lS : ∀ y : ℤ, |y| < 2 ^ s → len y ≤ L := fun y hy => len_of_abs le_rfl (hy.trans_le hsL)
  set g : ℤ := (Int.gcd xj D : ℤ) with hg
  have hg0 : 0 < g := by rw [hg]; exact_mod_cast Int.gcd_pos_of_ne_zero_right xj hD0.ne'
  have hgD : g ≤ D := by
    rw [hg]; exact Int.le_of_dvd hD0 (Int.gcd_dvd_right xj D)
  have hnu : |xj / g| < 2 ^ s := by
    have : |xj / g| ≤ |xj| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_ediv_le_natAbs xj g
    omega
  have hde0 : 0 ≤ D / g := Int.ediv_nonneg hD0.le hg0.le
  have hde : D / g ≤ D := Int.ediv_le_self g hD0.le
  have hj4 : |(j : ℤ) * 4| < 2 ^ L := by rw [abs_of_nonneg (by positivity)]; omega
  have hA1 : |-1016 - (j : ℤ) * 4| < 2 ^ L := by rw [abs_of_neg (by omega)]; omega
  have hA2 : |-1016 - (j : ℤ) * 4 - 2| < 2 ^ L := by rw [abs_of_neg (by omega)]; omega
  unfold COORD; simp only [seqL]
  -- `zX := x_j`, `zA := x_j`, `zB := D`
  have okA : OKI w L CO1 v ∧ (runI w CO1 v).mem = Function.update (Function.update (Function.update
      (Function.update (Function.update v.mem zX (FB + 1)) zX (FB + 1 + j)) zX xj) zA xj) zB D := by
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by rw [hFB]; exact hnat _ hFB0 (by omega), by rw [hOne]; exact h1⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [hFB, hOne]; exact hnat _ (by omega) (by omega), by evl; rw [hJ]; exact hnat _ (by omega) (by omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [hFB, hOne, hJ]; exact hnat _ (by omega) (by omega),
        by evl; rw [hFB, hOne, hJ, hx]; exact lS _ hxs⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [hFB, hOne, hJ, hx]; exact lS _ hxs, by evl; rw [hz]; exact l0⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [hD]; exact lS _ (by rw [abs_of_pos hD0]; exact hDs), by evl; rw [hz]; exact l0⟩, trivial⟩, ?_⟩
    simp only [CO1, runI, stepI_add_mem, stepI_load_mem]
    evl
    simp only [hFB, hOne, hJ, hx, hz, hD, add_zero]
  obtain ⟨okA, mA⟩ := okA
  refine RS.seq (rs_seqI okA) ?_
  rintro n₁ v₁ ⟨hn₁, rfl⟩
  -- Euclid
  refine RS.seq (rs_GCD (s := s) (a := xj) (b := D) (by rw [mA]; evl) (by rw [mA]; evl) (by rw [mA]; evl; exact hQ)
    (by rw [mA]; evl; exact hz) hD0 hxs hDs hL1 h10) ?_
  rintro n₂ v₂ ⟨hn₂, m₂, s₂⟩
  rw [mA] at m₂
  -- `zN`, `zDn`, `zP`
  have okB : OKI w L CO2 v₂ ∧ (runI w CO2 v₂).mem = Function.update (Function.update (Function.update
      (Function.update v₂.mem zN (xj / g)) zDn (D / g)) zP ((j : ℤ) * 4)) zP (-1016 - (j : ℤ) * 4) := by
    have fX : v₂.mem zX = xj := by rw [m₂]; evl
    have fA : v₂.mem zA = g := by rw [m₂]; evl; exact hg.symm
    have fD : v₂.mem zD = D := by rw [m₂]; evl; exact hD
    have fJ : v₂.mem zJ = j := by rw [m₂]; evl; exact hJ
    have fF : v₂.mem zFour = 4 := by rw [m₂]; evl; exact hFour
    have fP0 : v₂.mem zP0 = -1016 := by rw [m₂]; evl; exact hP0
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by rw [fX]; exact lS _ hxs,
        by rw [fA]; exact lS _ (by rw [abs_of_pos hg0]; omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fD]; exact lS _ (by rw [abs_of_pos hD0]; exact hDs),
        by evl; rw [fA]; exact lS _ (by rw [abs_of_pos hg0]; omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fJ]; exact hnat _ (by omega) (by omega), by evl; rw [fF]; exact len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fP0]; exact len_scr (by decide) (by decide) h10, by evl; rw [fJ, fF]; exact len_of_abs le_rfl hj4⟩,
      trivial⟩, ?_⟩
    simp only [CO2, runI, stepI_div_mem, stepI_mul_mem, stepI_sub_mem]
    evl
    simp only [fX, fA, fD, fJ, fF, fP0]
  obtain ⟨okB, mB⟩ := okB
  refine RS.seq (rs_seqI okB) ?_
  rintro n₃ v₃ ⟨hn₃, rfl⟩
  -- the two stores, `zJ := j + 1`
  have okC : OKI w L CO3 (runI w CO2 v₂) ∧ (runI w CO3 (runI w CO2 v₂)).mem = Function.update (Function.update
      (Function.update (Function.update (runI w CO2 v₂).mem (-1016 - (j : ℤ) * 4) (xj / g)) zP
        (-1016 - (j : ℤ) * 4 - 2)) (-1016 - (j : ℤ) * 4 - 2) (D / g)) zJ ((j : ℤ) + 1) := by
    have fP : (runI w CO2 v₂).mem zP = -1016 - (j : ℤ) * 4 := by rw [mB]; evl
    have fN : (runI w CO2 v₂).mem zN = xj / g := by rw [mB]; evl
    have fDn : (runI w CO2 v₂).mem zDn = D / g := by rw [mB]; evl
    have fT : (runI w CO2 v₂).mem zTwo = 2 := by rw [mB, m₂]; evl; exact hTwo
    have fJ : (runI w CO2 v₂).mem zJ = j := by rw [mB, m₂]; evl; exact hJ
    have fO : (runI w CO2 v₂).mem zOne = 1 := by rw [mB, m₂]; evl; exact hOne
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [fP]; exact len_of_abs le_rfl hA1, by rw [fN]; exact lS _ hnu⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fP]; exact len_of_abs le_rfl hA1, by evl; rw [fT]; exact len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fP, fT]; exact len_of_abs le_rfl hA2,
        by evl; rw [fDn]; exact lS _ (by rw [abs_of_nonneg hde0]; omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fJ]; exact hnat _ (by omega) (by omega), by evl; rw [fO]; exact h1⟩, trivial⟩, ?_⟩
    simp only [CO3, runI, stepI_store_mem, stepI_sub_mem, stepI_add_mem]
    evl
    simp only [fP, fN, fDn, fT, fJ, fO]
  obtain ⟨okC, mC⟩ := okC
  refine RS.seq (rs_seqI okC) ?_
  rintro n₄ v₄ ⟨hn₄, rfl⟩
  -- the cells of the coordinate back at `0`
  refine (rs_seqI (is := CO4) (t := runI w CO3 (runI w CO2 v₂))
    ⟨⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
  rintro n₅ v₅ ⟨hn₅, rfl⟩
  refine ⟨by simp [CO1, CO2, CO3, CO4] at hn₁ hn₃ hn₄ hn₅; omega, ?_, ?_⟩
  · exact (((((runI_same (by simp [CO1, Plain, NJ])).trans s₂).trans (runI_same (by simp [CO2, Plain, NJ]))).trans
      (runI_same (by simp [CO3, Plain, NJ]))).trans (runI_same (by simp [CO4, Plain, NJ])))
  · simp only [CO4, runI, stepI_const_mem]
    rw [mC, mB, m₂]
    funext c
    by_cases hc1 : c = -1016 - (j : ℤ) * 4
    · subst hc1; evl
    by_cases hc2 : c = -1016 - (j : ℤ) * 4 - 2
    · subst hc2; evl
    by_cases hc3 : -714 ≤ c ∧ c ≤ -700
    · obtain ⟨hc3, hc4⟩ := hc3
      interval_cases c <;> evl <;> first | rfl | (symm; assumption)
    · evl

/-! ## The setup -/

theorem cv_even (x : ℕ → ℤ) (D : ℤ) (j : ℕ) : cv x D (8 + 2 * j) = x j / (Int.gcd (x j) D : ℤ) := by
  unfold cv
  have e : ((8 + 2 * (j : ℤ) - 8) / 2).toNat = j := by omega
  rw [e, ite_eq_left (by omega)]

theorem cv_odd (x : ℕ → ℤ) (D : ℤ) (j : ℕ) : cv x D (9 + 2 * j) = D / (Int.gcd (x j) D : ℤ) := by
  unfold cv
  have e : ((9 + 2 * (j : ℤ) - 8) / 2).toNat = j := by omega
  rw [e, ite_eq_right (by omega)]

set_option maxHeartbeats 2000000 in
/-- **The setup.** -/
theorem rs_SETUP {u : State d} {n off bF : ℕ} {D : ℤ} {s : ℕ} {x : ℕ → ℤ} {rF : ℤ}
    (hrF1 : -500 < rF) (hrF2 : rF < -3)
    (h0 : u.mem 0 = d) (h1 : u.mem 1 = n) (hTO : u.mem (-3) = off) (hrF : u.mem rF = bF)
    (hD : u.mem ((off : ℤ) + bF) = D) (hD0 : 0 < D) (hDs : D < 2 ^ s)
    (hx : ∀ j < d, u.mem ((off : ℤ) + bF + 1 + j) = x j) (hxs : ∀ j < d, |x j| < 2 ^ s)
    (hlow : ∀ c ≤ -500, u.mem c = 0)
    (hL1 : s + 2 ≤ L) (hL2 : (n : ℤ) + 2 < 2 ^ L) (hL3 : (off : ℤ) + bF + d + 2 < 2 ^ L)
    (hL4 : (off : ℤ) + d * d + d + 264 < 2 ^ L) (hL5 : 4 * (d : ℤ) + 1020 < 2 ^ L) (h10 : 10 ≤ L) :
    RS w L (SETUPf rF) u (fun k t => k ≤ 50 + d * (8 * (2 * s + 1) + 22) ∧ Same' u t ∧
      t.mem cYB = (off : ℤ) + 264 + d * d + d ∧ (∀ c, -500 < c → t.mem c = u.mem c) ∧
      (∀ c, IsScr c → t.mem c = 0) ∧ ∀ y : ℤ, t.mem (φ y) = hdr d n x D y) := by
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have l1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hnat : ∀ y : ℤ, 0 ≤ y → y < 2 ^ L → len y ≤ L := fun y h0 hy => len_of_abs (by rw [abs_of_nonneg h0]) hy
  have hd2 : (d : ℤ) * d ≤ (d : ℤ) * d + d := by omega
  unfold SETUPf; simp only [seqL]
  -- the header
  have okH1 : OKI w L HEAD1 u ∧ (runI w HEAD1 u).mem = Function.update (Function.update (Function.update
      (Function.update (Function.update u.mem zOne 1) (-1000) d) (-1002) n) (-1004) 1) (-1006) ((n : ℤ) + 1) := by
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, l1⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [h0]; exact hnat _ (by omega) (by omega), by evl; rw [hlow _ (by norm_num)]; exact l0⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [h1]; exact hnat _ (by omega) (by omega), by evl; rw [hlow _ (by norm_num)]; exact l0⟩,
      ⟨len_scr (by decide) (by decide) h10, l1⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [h1]; exact hnat _ (by omega) (by omega), by evl; exact l1⟩, trivial⟩, ?_⟩
    simp only [HEAD1, runI, stepI_add_mem, stepI_const_mem]
    evl
    simp only [h0, h1, hlow (-600) (by norm_num), add_zero]
  obtain ⟨okH1, mH1⟩ := okH1
  refine RS.seq (rs_seqI okH1) ?_
  rintro n₁ v₁ ⟨hn₁, rfl⟩
  have okH2 : OKI w L HEAD2 (runI w HEAD1 u) ∧ (runI w HEAD2 (runI w HEAD1 u)).mem = Function.update
      (Function.update (Function.update (Function.update (runI w HEAD1 u).mem (-1008) 1) (-1010) 2) (-1012) n)
      (-1014) 1 := by
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, l1⟩, ⟨len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [mH1]; evl; rw [h1]; exact hnat _ (by omega) (by omega),
        by evl; rw [mH1]; evl; rw [hlow _ (by norm_num)]; exact l0⟩,
      ⟨len_scr (by decide) (by decide) h10, l1⟩, trivial⟩, ?_⟩
    simp only [HEAD2, runI, stepI_add_mem, stepI_const_mem]
    evl
    rw [mH1]; evl
    simp only [h1, hlow (-600) (by norm_num), add_zero]
  obtain ⟨okH2, mH2⟩ := okH2
  refine RS.seq (rs_seqI okH2) ?_
  rintro n₂ v₂ ⟨hn₂, rfl⟩
  rw [mH1] at mH2
  set M2 := (runI w HEAD2 (runI w HEAD1 u)) with hM2
  -- `cYB`
  have okY1 : OKI w L YBF1 M2 ∧ (runI w YBF1 M2).mem = Function.update (Function.update (Function.update
      (Function.update (Function.update M2.mem zT ((d : ℤ) * d)) zT ((d : ℤ) * d + d)) zFour 264) zT
      ((d : ℤ) * d + d + 264)) cYB ((off : ℤ) + ((d : ℤ) * d + d + 264)) := by
    have f0 : M2.mem 0 = d := by rw [mH2]; evl; exact h0
    have fTO : M2.mem (-3) = off := by rw [mH2]; evl; exact hTO
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by rw [f0]; exact hnat _ (by omega) (by omega),
        by rw [f0]; exact hnat _ (by omega) (by omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [f0]; exact hnat _ (by positivity) (by nlinarith), by evl; rw [f0]; exact hnat _ (by omega) (by omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [f0]; exact hnat _ (by positivity) (by nlinarith), by evl; exact len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fTO]; exact hnat _ (by omega) (by omega),
        by evl; rw [f0]; exact hnat _ (by positivity) (by nlinarith)⟩, trivial⟩, ?_⟩
    simp only [YBF1, runI, stepI_add_mem, stepI_mul_mem, stepI_const_mem]
    evl
    simp only [f0, fTO]
  obtain ⟨okY1, mY1⟩ := okY1
  refine RS.seq (rs_seqI okY1) ?_
  rintro n₃ v₃ ⟨hn₃, rfl⟩
  set M3 := runI w YBF1 M2 with hM3
  -- `zFB`, `zD`, the constants
  have okY2 : OKI w L (YBF2 rF) M3 ∧ (runI w (YBF2 rF) M3).mem = Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update M3.mem zFB ((off : ℤ) + bF)) zD D) zFour 4)
      zP0 (-1016)) zTwo 2) zT 0 := by
    have fTO : M3.mem (-3) = off := by rw [mY1, mH2]; evl; exact hTO
    have frF : M3.mem rF = bF := by rw [mY1, mH2]; evl; exact hrF
    have fD : M3.mem ((off : ℤ) + bF) = D := by rw [mY1, mH2]; evl; exact hD
    refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by omega) (by omega) h10, by rw [fTO]; exact hnat _ (by omega) (by omega),
        by rw [frF]; exact hnat _ (by omega) (by omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [fTO, frF]; exact hnat _ (by omega) (by omega),
        by evl; rw [fTO, frF, fD]; exact hnat _ hD0.le (by
          have : (2 : ℤ) ^ s ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
          omega)⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10⟩,
      ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩, ?_⟩
    simp only [YBF2, runI, stepI_add_mem, stepI_load_mem, stepI_const_mem]
    evl
    simp only [fTO, frF, fD]
  obtain ⟨okY2, mY2⟩ := okY2
  refine RS.seq (rs_seqI okY2) ?_
  rintro n₄ v₄ ⟨hn₄, rfl⟩
  set M4 := runI w (YBF2 rF) M3 with hM4
  have hS4 : Same' u M4 := (((runI_same (by simp [HEAD1, Plain, NJ])).trans (runI_same (by simp [HEAD2, Plain, NJ]))).trans
    (runI_same (by simp [YBF1, Plain, NJ]))).trans (runI_same (by simp [YBF2, Plain, NJ]))
  have m4 : M4.mem = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update u.mem zOne 1) (-1000) d) (-1002) n) (-1004) 1) (-1006)
      ((n : ℤ) + 1)) (-1008) 1) (-1010) 2) (-1012) n) (-1014) 1) zT ((d : ℤ) * d)) zT ((d : ℤ) * d + d)) zFour 264)
      zT ((d : ℤ) * d + d + 264)) cYB ((off : ℤ) + ((d : ℤ) * d + d + 264))) zFB ((off : ℤ) + bF)) zD D) zFour 4)
      zP0 (-1016)) zTwo 2) zT 0 := by rw [mY2, mY1, mH2]
  -- the coordinates
  refine RS.loop (fun j v => j ≤ d ∧ Same' u v ∧ v.mem zJ = j ∧ (∀ c, -1000 < c → c ≠ zJ → v.mem c = M4.mem c) ∧
      ∀ y : ℤ, v.mem (φ y) = if 8 ≤ y ∧ y < 8 + 2 * (j : ℤ) then cv x D y else M4.mem (φ y)) d
      (8 * (2 * s + 1) + 20)
      ⟨Nat.zero_le d, hS4, by rw [m4]; evl; exact hlow _ (by norm_num), fun c _ _ => rfl,
        fun y => by simp only [Nat.cast_zero, mul_zero, add_zero]; rw [ite_eq_right (by omega)]⟩ ?_ ?_ ?_
  · rintro j v ⟨hj, -, hvJ, hvc, -⟩
    have e0 : v.mem 0 = d := by rw [hvc 0 (by norm_num) (by norm_num), m4]; evl; exact h0
    refine ⟨⟨len_scr (by decide) (by decide) h10, l0, by rw [hvJ]; exact hnat _ (by omega) (by omega),
      by rw [e0]; exact hnat _ (by omega) (by omega)⟩, ?_⟩
    rw [hvJ, e0]; omega
  · rintro j v ⟨hj, hsv, hvJ, hvc, hvy⟩ hjd
    have hc : ∀ c, -1000 < c → c ≠ zJ → (addC v (tcost zJ 0 v)).mem c = M4.mem c := fun c h1 h2 => by
      rw [addC_mem]; exact hvc c h1 h2
    have hxj : (addC v (tcost zJ 0 v)).mem ((off : ℤ) + bF + 1 + j) = x j := by
      rw [hc _ (by omega) (by omega), m4]; evl; exact hx j hjd
    refine (rs_COORD (s := s) (j := j) (FB := (off : ℤ) + bF) (D := D) (by rw [addC_mem]; exact hvJ)
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl) (by rw [hc _ (by norm_num) (by norm_num), m4]; evl)
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl) (by rw [hc _ (by norm_num) (by norm_num), m4]; evl)
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl) (by rw [hc _ (by norm_num) (by norm_num), m4]; evl)
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by rw [hc _ (by norm_num) (by norm_num), m4]; evl; exact hlow _ (by norm_num))
      (by omega) hxj hD0 hDs (hxs j hjd) hL1 (by omega) (by omega) h10).mono ?_
    rintro n v' ⟨hn, hsv', hm⟩
    refine ⟨hn, by omega, hsv.trans ((Same'.addC _ _).trans (hsv'.trans (Same'.addC _ 1))), ?_, ?_, ?_⟩
    · rw [addC_mem, hm, Function.update_self]; norm_cast
    · intro c h1 h2
      rw [addC_mem, hm]
      rw [Function.update_of_ne h2, Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), addC_mem]
      exact hvc c h1 h2
    · intro y
      have hφ : φ y ≤ -1000 := φ_le y
      rw [addC_mem, hm, Function.update_of_ne (by omega), addC_mem]
      by_cases hy1 : y = 8 + 2 * j
      · subst hy1
        rw [φ_nat _ (by omega), show (-1000 - 2 * (8 + 2 * (j : ℤ))) = -1016 - (j : ℤ) * 4 by ring,
          Function.update_of_ne (by omega), Function.update_self, ite_eq_left (by push_cast; omega), cv_even]
      by_cases hy2 : y = 9 + 2 * j
      · subst hy2
        rw [φ_nat _ (by omega), show (-1000 - 2 * (9 + 2 * (j : ℤ))) = -1016 - (j : ℤ) * 4 - 2 by ring,
          Function.update_self, ite_eq_left (by push_cast; omega), cv_odd]
      · have n1 : φ y ≠ -1016 - (j : ℤ) * 4 := fun e => hy1 (φ_inj (by rw [e, φ_nat _ (by omega)]; ring))
        have n2 : φ y ≠ -1016 - (j : ℤ) * 4 - 2 := fun e => hy2 (φ_inj (by rw [e, φ_nat _ (by omega)]; ring))
        rw [Function.update_of_ne n2, Function.update_of_ne n1, hvy y]
        have : (8 ≤ y ∧ y < 8 + 2 * (j : ℤ)) ↔ (8 ≤ y ∧ y < 8 + 2 * ((j + 1 : ℕ) : ℤ)) := by push_cast; omega
        simp only [this]
  · rintro k v ⟨hj, hsv, hvJ, hvc, hvy⟩ hk
    have hdk : d * (8 * (2 * s + 1) + 20 + 2) = d * (8 * (2 * s + 1) + 22) := by ring
    have hc : ∀ c, -1000 < c → c ≠ zJ → v.mem c = M4.mem c := hvc
    refine ⟨by simp [HEAD1, HEAD2, YBF1, YBF2] at hn₁ hn₂ hn₃ hn₄; omega, hsv.trans (Same'.addC _ _), ?_, ?_, ?_, ?_⟩
    · rw [addC_mem, hc _ (by norm_num) (by norm_num), m4]; evl; ring
    · intro c hc5
      rw [addC_mem, hc _ (by omega) (by omega), m4]; evl
    · intro c hcs
      have hcs' : -627 ≤ c ∧ c ≤ -600 ∧ c ≠ -601 := by rcases hcs with h | h <;> omega
      rw [addC_mem, hc _ (by omega) (by omega), m4]; evl; exact hlow c (by omega)
    · intro y
      rw [addC_mem, hvy y, hdr]
      by_cases hy : 0 ≤ y ∧ y ≤ 7
      · obtain ⟨hy0, hy7⟩ := hy
        rw [ite_eq_right (by omega), φ_nat _ hy0, m4]
        interval_cases y <;> simp
      · rw [ite_eq_right (show ¬ (y = 0) by omega), ite_eq_right (show ¬ (y = 1) by omega),
          ite_eq_right (show ¬ (y = 2) by omega), ite_eq_right (show ¬ (y = 3) by omega),
          ite_eq_right (show ¬ (y = 4) by omega), ite_eq_right (show ¬ (y = 5) by omega),
          ite_eq_right (show ¬ (y = 6) by omega), ite_eq_right (show ¬ (y = 7) by omega)]
        by_cases hy8 : 8 ≤ y ∧ y < 8 + 2 * (d : ℤ)
        · rw [ite_eq_left hy8, ite_eq_left hy8]
        · rw [ite_eq_right hy8, ite_eq_right hy8]
          have hφ : φ y ≤ -1016 ∨ (φ y < -1000 ∧ φ y % 2 = 1) := by
            rcases le_or_gt 0 y with h | h
            · left; rw [φ_nat _ h]; omega
            · right; rw [φ_neg _ h]; omega
          rw [m4]; evl; exact hlow _ (by omega)

end AdversarialBco.UniPoly
