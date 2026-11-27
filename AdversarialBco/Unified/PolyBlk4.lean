/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk
public import AdversarialBco.Unified.PolyRow

@[expose] public section

/-!
# UNI-POLY, part 7: `ROWMEM`, the exact membership in the polytope of the input rows

* `rs_ROWIN`: the inner loop of a row: `(S, Q)` of `rowSQ` after the `d` columns.
* `rs_ROWMEM`: `cR := 1` if every row passes the test `S dn_d ≤ nm_d Q Y_0`, `0` otherwise.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

/-- A bound on the absolute value gives a bound on the length. -/
theorem len_of_abs {x V : ℤ} {L : ℕ} (hx : |x| ≤ V) (hV : V < 2 ^ L) : len x ≤ L := by
  rw [len_le_iff]
  have : (x.natAbs : ℤ) < 2 ^ L := by rw [Int.natCast_natAbs]; omega
  exact_mod_cast this

theorem abs_mul_le {x y a b : ℤ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem runI_append (l₁ l₂ : List Instr) (u : State d) : runI w (l₁ ++ l₂) u = runI w l₂ (runI w l₁ u) := by
  induction l₁ generalizing u with
  | nil => rfl
  | cons i l ih => exact ih _

theorem OKI_append {l₁ l₂ : List Instr} {u : State d} (h₁ : OKI w L l₁ u) (h₂ : OKI w L l₂ (runI w l₁ u)) :
    OKI w L (l₁ ++ l₂) u := by
  induction l₁ generalizing u with
  | nil => exact h₂
  | cons i l ih => exact ⟨h₁.1, ih h₁.2 h₂⟩

/-! ## The column step in four straight lines -/

/-- The entry `num/den` of the column and the coordinate `Y_{1+j}`. -/
theorem rowA {u : State d} {E P a1 a2 a3 : ℤ} (fE : u.mem cE = E) (fOne : u.mem cOne = 1) (fYP : u.mem cYP = P)
    (fN : u.mem E = a1) (fD : u.mem (E + 1) = a2) (fY : u.mem P = a3) (hE3 : 3 ≤ E) (hP0 : 0 ≤ P)
    (lE : len E ≤ L) (lE1 : len (E + 1) ≤ L) (lP : len P ≤ L) (l1 : len a1 ≤ L) (l2 : len a2 ≤ L) (l3 : len a3 ≤ L)
    (h10 : 10 ≤ L) :
    OKI w L [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY cYP] u ∧
      (runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY cYP] u).mem =
        Function.update (Function.update (Function.update (Function.update u.mem cN a1) cE1 (E + 1)) cDD a2) cY a3 := by
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [fE]; exact lE,
      by rw [fE, fN]; exact l1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fE]; exact lE, by evl; rw [fOne]; exact h1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fE, fOne]; exact lE1, by evl; rw [fE, fOne, fD]; exact l2⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fYP]; exact lP, by evl; rw [fYP, fY]; exact l3⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_load_mem, stepI_add_mem]
  evl
  simp only [fE, fOne, fYP, fN, fD, fY]

/-- `S := S dn`, `T := nm Y_{1+j} Q`. -/
theorem rowB1 {u : State d} {S Q a1 a2 a3 : ℤ} (fS : u.mem cS = S) (fQ : u.mem cQ = Q) (fN : u.mem cN = a1)
    (fD : u.mem cDD = a2) (fY : u.mem cY = a3) (lS : len S ≤ L) (lQ : len Q ≤ L) (l1 : len a1 ≤ L)
    (l2 : len a2 ≤ L) (l3 : len a3 ≤ L) (l13 : len (a1 * a3) ≤ L) (h10 : 10 ≤ L) :
    OKI w L [.mul cS cS cDD, .mul cT cN cY, .mul cT cT cQ] u ∧
      (runI w [.mul cS cS cDD, .mul cT cN cY, .mul cT cT cQ] u).mem =
        Function.update (Function.update (Function.update u.mem cS (S * a2)) cT (a1 * a3)) cT (a1 * a3 * Q) := by
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by rw [fS]; exact lS, by rw [fD]; exact l2⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fN]; exact l1, by evl; rw [fY]; exact l3⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fN, fY]; exact l13, by evl; rw [fQ]; exact lQ⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_mul_mem]
  evl
  simp only [fS, fD, fN, fY, fQ]

/-- `S := S + T`, `Q := Q dn`. -/
theorem rowB2 {u : State d} {S T Q a2 : ℤ} (fS : u.mem cS = S) (fT : u.mem cT = T) (fQ : u.mem cQ = Q)
    (fD : u.mem cDD = a2) (lS : len S ≤ L) (lT : len T ≤ L) (lQ : len Q ≤ L) (l2 : len a2 ≤ L) (h10 : 10 ≤ L) :
    OKI w L [.add cS cS cT, .mul cQ cQ cDD] u ∧
      (runI w [.add cS cS cT, .mul cQ cQ cDD] u).mem =
        Function.update (Function.update u.mem cS (S + T)) cQ (Q * a2) := by
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by rw [fS]; exact lS, by rw [fT]; exact lT⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fQ]; exact lQ, by evl; rw [fD]; exact l2⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_mul_mem, stepI_add_mem]
  evl
  simp only [fS, fT, fQ, fD]

/-- The pointers move on, the scratch cells of the column back at `0`. -/
theorem rowC {u : State d} {E1 P j : ℤ} (fE1 : u.mem cE1 = E1) (fOne : u.mem cOne = 1) (fYP : u.mem cYP = P)
    (fJ : u.mem cJ = j) (lE1 : len E1 ≤ L) (lP : len P ≤ L) (lj : len j ≤ L) (h10 : 10 ≤ L) :
    OKI w L [.add cE cE1 cOne, .add cYP cYP cOne, .add cJ cJ cOne, .const cN 0, .const cE1 0, .const cDD 0,
      .const cY 0, .const cT 0] u ∧
      (runI w [.add cE cE1 cOne, .add cYP cYP cOne, .add cJ cJ cOne, .const cN 0, .const cE1 0, .const cDD 0,
        .const cY 0, .const cT 0] u).mem =
        Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update u.mem cE (E1 + 1)) cYP (P + 1)) cJ (j + 1)) cN 0) cE1 0) cDD 0) cY 0)
          cT 0 := by
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by rw [fE1]; exact lE1, by rw [fOne]; exact h1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fYP]; exact lP, by evl; rw [fOne]; exact h1⟩,
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by evl; rw [fJ]; exact lj, by evl; rw [fOne]; exact h1⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩, ?_⟩
  simp only [runI, stepI_add_mem, stepI_const_mem]
  evl
  simp only [fE1, fOne, fYP, fJ]

set_option maxHeartbeats 1000000 in
/-- The inner loop of `ROWMEM` on row `i`: after the `d` columns, `cS`, `cQ` hold `rowSQ`, and the column pointers
have moved on. -/
theorem rs_ROWIN {v0 : State d} {i : ℕ} {YB M B : ℤ} {nm dn Y : ℕ → ℤ} (hYB0 : 0 ≤ YB)
    (hS : v0.mem cS = 0) (hQ : v0.mem cQ = 1) (hJ : v0.mem cJ = 0) (hYP : v0.mem cYP = YB + 1)
    (hE : v0.mem cE = 3 + 2 * (((d : ℤ) + 1) * i)) (hOne : v0.mem cOne = 1) (hd : v0.mem 0 = d)
    (hN : v0.mem cN = 0) (hE1 : v0.mem cE1 = 0) (hDD : v0.mem cDD = 0) (hY : v0.mem cY = 0) (hT : v0.mem cT = 0)
    (hnm : ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j)) = nm j)
    (hdn : ∀ j : ℕ, j ≤ d → v0.mem (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = dn j)
    (hYv : ∀ j : ℕ, j < d → v0.mem (YB + 1 + j) = Y (1 + j))
    (hM1 : 1 ≤ M) (hB : 1 ≤ B) (hMb : ∀ j : ℕ, j ≤ d → |nm j| ≤ M ∧ 0 < dn j ∧ dn j ≤ M)
    (hYb : ∀ j : ℕ, j < d → |Y (1 + j)| ≤ B)
    (hLV : ((d : ℤ) + 1) * M ^ (d + 1) * B < 2 ^ L)
    (hLA : 3 + 2 * (((d : ℤ) + 1) * i + d) + 2 < 2 ^ L) (hLY : YB + d + 1 < 2 ^ L) (h10 : 10 ≤ L) :
    RS w L ROWIN v0 (fun n v => n ≤ d * 19 + 2 ∧
      v.mem = Function.update (Function.update (Function.update (Function.update (Function.update v0.mem
        cS (rowSQ nm dn Y d).1) cQ (rowSQ nm dn Y d).2) cJ d) cYP (YB + 1 + d))
        cE (3 + 2 * (((d : ℤ) + 1) * i + d)) ∧ Same' v0 v) := by
  have hLd : ((d : ℤ) + 1) < 2 ^ L := by
    have h1 : (1 : ℤ) ≤ M ^ (d + 1) * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) hB
    have : ((d : ℤ) + 1) * 1 ≤ ((d : ℤ) + 1) * (M ^ (d + 1) * B) := mul_le_mul_of_nonneg_left h1 (by omega)
    rw [← mul_assoc] at this; omega
  have hpow : ∀ j ≤ d + 1, M ^ j ≤ M ^ (d + 1) := fun j hj => pow_le_pow_right₀ hM1 hj
  set V : ℤ := ((d : ℤ) + 1) * M ^ (d + 1) * B with hVd
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have hnat : ∀ x : ℤ, 0 ≤ x → x < 2 ^ L → len x ≤ L := fun x h0 hx =>
    len_of_abs (by rw [abs_of_nonneg h0]) hx
  have hV : ∀ (a e : ℕ), a ≤ d + 1 → e ≤ d + 1 → (a : ℤ) * M ^ e * B ≤ V := fun a e ha he => by
    have h1 : (a : ℤ) ≤ (d : ℤ) + 1 := by omega
    have h2 := hpow e he
    have : (a : ℤ) * M ^ e ≤ ((d : ℤ) + 1) * M ^ (d + 1) := mul_le_mul h1 h2 (by positivity) (by omega)
    exact mul_le_mul_of_nonneg_right this (by omega)
  have lV : ∀ x : ℤ, |x| ≤ V → len x ≤ L := fun x hx => len_of_abs hx hLV
  have bM : M ≤ V := by
    have := hV 1 1 (by omega) (by omega)
    have : M ≤ (1 : ℕ) * M ^ 1 * B := by simp only [Nat.cast_one, one_mul, pow_one]; nlinarith
    omega
  unfold ROWIN
  refine RS.loop (fun j v => j ≤ d ∧ v.mem = Function.update (Function.update (Function.update (Function.update
      (Function.update v0.mem cS (rowSQ nm dn Y j).1) cQ (rowSQ nm dn Y j).2) cJ j) cYP (YB + 1 + j))
      cE (3 + 2 * (((d : ℤ) + 1) * i + j)) ∧ Same' v0 v) d 17 ⟨Nat.zero_le d, ?_, Same'.refl _⟩ ?_ ?_ ?_
  · funext c; simp only [rowSQ, Nat.cast_zero, add_zero]
    by_cases hc : -627 ≤ c ∧ c ≤ -600
    · obtain ⟨hc1, hc2⟩ := hc
      interval_cases c <;> evl <;> first | rfl | omega
    · evl
  · rintro j v ⟨hj, hv, -⟩
    have e1 : v.mem cJ = j := by rw [hv]; evl
    have e2 : v.mem 0 = d := by rw [hv]; evl; exact hd
    refine ⟨⟨len_scr (by decide) (by decide) h10, l0, ?_, ?_⟩, ?_⟩
    · rw [e1]; exact hnat _ (by omega) (by omega)
    · rw [e2]; exact hnat _ (by omega) (by omega)
    · rw [e1, e2]; omega
  · rintro j v ⟨hj, hv, hsv⟩ hjd
    set E : ℤ := 3 + 2 * (((d : ℤ) + 1) * i + j) with hEd
    have hE3 : 3 ≤ E := by
      have : (0 : ℤ) ≤ ((d : ℤ) + 1) * i + j := by positivity
      rw [hEd]; linarith
    have hEL : E + 2 < 2 ^ L := by
      have : (((d : ℤ) + 1) * i + j) ≤ ((d : ℤ) + 1) * i + d := by omega
      omega
    set P : ℤ := YB + 1 + j with hPd
    have hP0 : 0 ≤ P := by omega
    have hPL : P + 1 < 2 ^ L := by omega
    set S := (rowSQ nm dn Y j).1 with hSd
    set Q := (rowSQ nm dn Y j).2 with hQd
    obtain ⟨bS, bQ0, bQ⟩ := rowSQ_bound (nm := nm) (dn := dn) (Y := Y) (j := j) hM1 (by omega)
      (fun k hk => hMb k (by omega)) (fun k hk => hYb k (by omega))
    obtain ⟨bn, bd0, bd⟩ := hMb j (by omega)
    have bY := hYb j hjd
    have bD : |dn j| ≤ M := by rw [abs_of_pos bd0]; exact bd
    have bQ' : |Q| ≤ M ^ j := by rw [abs_of_pos bQ0]; exact bQ
    have lS : len S ≤ L := lV S (bS.trans (hV j j (by omega) (by omega)))
    have lQ : len Q ≤ L := lV Q (bQ'.trans (by
      have := hV 1 j (by omega) (by omega)
      have : M ^ j ≤ (1 : ℕ) * M ^ j * B := by
        simp only [Nat.cast_one, one_mul]; exact le_mul_of_one_le_right (by positivity) hB
      omega))
    have lN : len (nm j) ≤ L := lV _ (bn.trans bM)
    have lD : len (dn j) ≤ L := lV _ (bD.trans bM)
    have lY : len (Y (1 + j)) ≤ L := lV _ (bY.trans (by
      have := hV 1 0 (by omega) (by omega); simp only [Nat.cast_one, one_mul, pow_zero] at this; exact this))
    have lNY : len (nm j * Y (1 + j)) ≤ L := lV _ ((abs_mul_le bn bY).trans (by
      have := hV 1 1 (by omega) (by omega); simp only [Nat.cast_one, one_mul, pow_one] at this; exact this))
    have lSD : len (S * dn j) ≤ L := lV _ ((abs_mul_le bS bD).trans (by
      have := hV j (j + 1) (by omega) (by omega)
      calc (j : ℤ) * M ^ j * B * M = (j : ℤ) * M ^ (j + 1) * B := by ring
        _ ≤ V := this))
    have lNYQ : len (nm j * Y (1 + j) * Q) ≤ L := lV _ ((abs_mul_le (abs_mul_le bn bY) bQ').trans (by
      have := hV 1 (j + 1) (by omega) (by omega)
      calc M * B * M ^ j = ((1 : ℕ) : ℤ) * M ^ (j + 1) * B := by push_cast; ring
        _ ≤ V := this))
    have lE : len E ≤ L := hnat E (by omega) (by omega)
    have lE1 : len (E + 1) ≤ L := hnat _ (by omega) (by omega)
    have lP : len P ≤ L := hnat P hP0 (by omega)
    have lj : len (j : ℤ) ≤ L := hnat _ (by omega) (by omega)
    -- the state at the start of the column
    set u := addC v (tcost cJ 0 v) with hu
    have hum : u.mem = Function.update (Function.update (Function.update (Function.update
        (Function.update v0.mem cS S) cQ Q) cJ j) cYP P) cE E := by rw [hu, addC_mem, hv]
    have fE : u.mem cE = E := by rw [hum]; evl
    have fOne : u.mem cOne = 1 := by rw [hum]; evl; exact hOne
    have fYP : u.mem cYP = P := by rw [hum]; evl
    have fN : u.mem E = nm j := by rw [hum]; evl; exact hnm j (by omega)
    have fD : u.mem (E + 1) = dn j := by rw [hum]; evl; exact hdn j (by omega)
    have fY : u.mem P = Y (1 + j) := by rw [hum]; evl; exact hYv j hjd
    obtain ⟨okA, mA⟩ := rowA (w := w) fE fOne fYP fN fD fY hE3 hP0 lE lE1 lP lN lD lY h10
    set uA := runI w [.load cN cE, .add cE1 cE cOne, .load cDD cE1, .load cY cYP] u with huA
    obtain ⟨okB1, mB1⟩ := rowB1 (w := w) (u := uA) (S := S) (Q := Q) (a1 := nm j) (a2 := dn j) (a3 := Y (1 + j))
      (by rw [mA]; evl; rw [hum]; evl) (by rw [mA]; evl; rw [hum]; evl) (by rw [mA]; evl) (by rw [mA]; evl)
      (by rw [mA]; evl) lS lQ lN lD lY lNY h10
    set uB1 := runI w [.mul cS cS cDD, .mul cT cN cY, .mul cT cT cQ] uA with huB1
    obtain ⟨okB2, mB2⟩ := rowB2 (w := w) (u := uB1) (S := S * dn j) (T := nm j * Y (1 + j) * Q) (Q := Q)
      (a2 := dn j) (by rw [mB1]; evl) (by rw [mB1]; evl) (by rw [mB1]; evl; rw [mA]; evl; rw [hum]; evl)
      (by rw [mB1]; evl; rw [mA]; evl) lSD lNYQ lQ lD h10
    set uB2 := runI w [.add cS cS cT, .mul cQ cQ cDD] uB1 with huB2
    obtain ⟨okC, mC⟩ := rowC (w := w) (u := uB2) (E1 := E + 1) (P := P) (j := j)
      (by rw [mB2]; evl; rw [mB1]; evl; rw [mA]; evl) (by rw [mB2]; evl; rw [mB1]; evl; rw [mA]; evl; exact fOne)
      (by rw [mB2]; evl; rw [mB1]; evl; rw [mA]; evl; exact fYP)
      (by rw [mB2]; evl; rw [mB1]; evl; rw [mA]; evl; rw [hum]; evl) lE1 lP lj h10
    refine (rs_seqI (OKI_append okA (OKI_append okB1 (OKI_append okB2 okC)))).mono ?_
    rintro n v' ⟨hn, rfl⟩
    refine ⟨by simp at hn; omega, by omega, ?_, (hsv.trans ((Same'.addC _ _).trans
      (runI_same (by simp [Plain, NJ])))).trans (Same'.addC _ 1)⟩
    rw [addC_mem, runI_append, runI_append, runI_append, ← huA, ← huB1, ← huB2, mC, mB2, mB1, mA, hum]
    funext c
    by_cases hc : -627 ≤ c ∧ c ≤ -600
    · obtain ⟨hc1, hc2⟩ := hc
      interval_cases c <;> evl <;> (try simp only [rowSQ, hSd, hQd, hEd, hPd]) <;>
        first | rfl | (symm; assumption) | (push_cast; ring)
    · evl
  · rintro n v ⟨hj, hv, hsv⟩ hn
    exact ⟨by omega, hv, hsv.trans (Same'.addC _ _)⟩

end AdversarialBco.UniPoly
