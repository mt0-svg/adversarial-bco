/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR8M
public import AdversarialBco.Bit.Transfer.XTriScanLoop

@[expose] public section

/-!
# BL's round on the machine: R9's products and scalars

`v̂ = B̂ᵀ μ̂` into the array `31`, `B̂ v̂` into the array `28`, `u·μ̂` into the slot `54`, `v̂·v̂` into the slot `55`, then
the straight line `sl3St` (region from slot `56`): `V_b = F Q³ G² D`, `U_k`, `V_k = 2 V_b D`, the numerator of `k'`,
`Ŷ ν̂`, `V_g = F Q² G`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The third straight line -/

/-- The value of step `j` of the third line (the slot `56 + j`). -/
abbrev qz (j : ℕ) : IE := .sc (56 + j)

/-- R9's scalars. -/
def sl3St : List SStep :=
  [ .ie (.op .mul (.op .mul (.op .mul (.op .mul (.op .mul (.sc s2pF) (.sc s2p)) (.sc s2p)) (.sc s2p)) (qv 4))
      (.sc sDmu)),
    .ie (.op .mul (qv 1) (.op .sub (.op .mul (.sc 54) (.sc 54)) (.op .mul (qv 4) (.sc 55)))),
    .ie (.op .add (.op .mul (qz 0) (.sc sDmu)) (.op .mul (qz 0) (.sc sDmu))),
    .ie (.op .add (.sc sK) (rndE (qz 1) (qz 2))),
    .ie (.op .mul (qv 0) (.sc sNu)),
    .ie (.op .mul (.op .mul (.op .mul (.sc s2pF) (.sc s2p)) (.sc s2p)) (.sc s2g)) ]

/-- The input slots of the third line. -/
def sl3Ins : List ℕ := [s2pF, s2p, 49, sDmu, 46, 54, 55, sK, 45, sNu, s2g]

/-- The pairs of the inputs: the first line's, `(3, 0)` for the two dot products, `(1, 0)` for the rest. -/
def sl3In (y : ℕ) : ℕ × ℕ := if 45 ≤ y ∧ y < 54 then sl1Et (y - 45) else if y = 54 ∨ y = 55 then (3, 0) else (1, 0)

/-- The pairs of the steps. -/
def sl3Et (j : ℕ) : ℕ × ℕ := [(7, 0), (12, 8), (8, 1), (13, 11), (6, 7), (4, 0)].getD j (0, 0)

/-- The largest pair. -/
def sl3T : ℕ × ℕ := (13, 11)

/-- The cells of the third line: the region from `56`, the rest as the first line. -/
def sl3C : SLC := ⟨56, 256, sZ, 41, 42, 43, 19, 20, rOne⟩

theorem sl3St_length : sl3St.length = 6 := rfl

theorem sl3St_chk : SL.chk 56 sl3Ins sl3In sl3Et sl3T 14 sl3St = true := by decide

/-- The inputs of the third line. -/
def sl3I (F Q G2 D kY su sv kh yh nh G : ℤ) : ℕ → ℤ := fun y =>
  if y = s2pF then F else if y = s2p then Q else if y = 49 then G2 else if y = sDmu then D else
  if y = 46 then kY else if y = 54 then su else if y = 55 then sv else if y = sK then kh else
  if y = 45 then yh else if y = sNu then nh else if y = s2g then G else 0

section Values

variable (F Q G2 D kY su sv kh yh nh G : ℤ)

/-- The value of step `k`. -/
abbrev w3 (k : ℕ) : ℤ := SL.val sl3St 56 (sl3I F Q G2 D kY su sv kh yh nh G) k

theorem w3_c (k : ℕ) : w3 F Q G2 D kY su sv kh yh nh G k =
    (sl3St.getD k (.cst 0)).sem 56 (sl3I F Q G2 D kY su sv kh yh nh G)
      (fun j => if j < k then w3 F Q G2 D kY su sv kh yh nh G j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the third line unfolded. -/
macro "w3s" : tactic => `(tactic| (rw [w3_c]; simp only [sl3St, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, qv, qz, rndE, sl3I, s2p, s2pF, sDmu, sK, sNu, s2g, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte]))

theorem w3_0 : w3 F Q G2 D kY su sv kh yh nh G 0 = F * Q * Q * Q * G2 * D := by w3s
theorem w3_1 : w3 F Q G2 D kY su sv kh yh nh G 1 = kY * (su * su - G2 * sv) := by w3s
theorem w3_2 : w3 F Q G2 D kY su sv kh yh nh G 2 = 2 * (F * Q * Q * Q * G2 * D * D) := by
  w3s; rw [w3_0]; ring
theorem w3_3 : w3 F Q G2 D kY su sv kh yh nh G 3 =
    kh + rndZ (kY * (su * su - G2 * sv)) (2 * (F * Q * Q * Q * G2 * D * D)) Q := by
  w3s; rw [w3_1, w3_2, rndZ]
theorem w3_4 : w3 F Q G2 D kY su sv kh yh nh G 4 = yh * nh := by w3s
theorem w3_5 : w3 F Q G2 D kY su sv kh yh nh G 5 = F * Q * Q * G := by w3s

end Values

theorem sl3C_ok {L : Layout} (hlay : BLLay L) : sl3C.OK L 14 := by
  obtain ⟨hS, hN, -⟩ := hlay
  simp only [oE, rEE] at hS hN
  exact ⟨by simp only [sl3C]; omega, by simp only [sl3C]; omega, by simp only [sl3C]; omega,
    by simp only [sl3C, rOne]; omega, by simp only [sl3C]; omega, by simp only [sl3C, rOne]; omega,
    by simp only [sl3C, rOne]; omega, by simp only [sl3C, sZ]; omega, by simp only [sl3C]; omega,
    by simp only [sl3C]; omega, by simp only [sl3C]; omega, by simp [sl3C, sZ], by simp only [sl3C]; omega⟩

/-! ## R9, first part -/

/-- `v̂ = B̂ᵀ μ̂` into `31`, `B̂ v̂` into `28`, `u·μ̂` into `54`, `v̂·v̂` into `55`, the third line. -/
def xR9a (L : Layout) : XCmd :=
  .seq (xmatvecT L sZ 30 tR aB aMu 31 24 22 23 rD rOne)
    (.seq (xmatvec L sZ 30 tR aB 31 28 24 22 23 rD rOne)
      (.seq (xdot L sZ 54 tR aU aMu 22 23 rD rOne)
        (.seq (xdot L sZ 55 tR 31 31 22 23 rD rOne) (SL.code L sl3C sl3St))))

/-- The units of `xR9a`. -/
def r9aUnits (d Gu : ℕ) : ℕ :=
  (d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3) +
    ((d * (d * 10 + 9) + 4) + ((d * 10 + 5) + ((d * 10 + 5) + ev Gu (SL.unitsP sl3Et sl3St))))

/-- The cells that `xR9a` changes. -/
def S9a (y : ℕ) : Prop := y = 30 ∨ (54 ≤ y ∧ y < 62) ∨ tR ≤ y
def N9a (j : ℕ) : Prop := j = 19 ∨ j = 20 ∨ j = 22 ∨ j = 23 ∨ j = 24
def A9a (b c : ℕ) : Prop := (b = 31 ∧ c < d) ∨ (b = 28 ∧ c < d)

/-- `romega` with the cells of R9 unfolded. -/
macro "r9omega" : tactic => `(tactic| ((try simp only [S9a, N9a, A9a, aU, aAp, aBp] at *) <;> romega))

theorem dot_le_three {x y : Fin d → ℤ} {Gu : ℕ} (bx : ∀ k, |x k| ≤ 2 ^ Gu) (by' : ∀ k, |y k| ≤ 2 ^ Gu)
    (hd : (d : ℤ) ≤ 2 ^ Gu) : |x ⬝ᵥ y| ≤ 2 ^ (3 * Gu) := by
  calc |x ⬝ᵥ y| ≤ ∑ k, |x k * y k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (2 ^ Gu * 2 ^ Gu : ℤ) := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul (bx k) (by' k) (abs_nonneg _) (by positivity)
    _ = (d : ℤ) * (2 ^ Gu * 2 ^ Gu) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 ^ Gu * (2 ^ Gu * 2 ^ Gu) := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = 2 ^ (3 * Gu) := by ring

set_option maxHeartbeats 1600000 in
/-- **R9's products and scalars on the machine.** -/
theorem XV.r9a {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Bh : Matrix (Fin d) (Fin d) ℤ} {mu Γ : Fin d → ℤ} {F Q G2 D kY kh yh nh G : ℤ} {Gu : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2)
    (c4 : σ.sc 43 = 4) (eB : ∀ i j : Fin d, σ.arr aB (d * i + j) = Bh i j) (eMu : ∀ j : Fin d, σ.arr aMu j = mu j)
    (eU : ∀ j : Fin d, σ.arr aU j = (Bh *ᵥ Γ) j)
    (eF : σ.sc s2pF = F) (eQ : σ.sc s2p = Q) (eG2 : σ.sc 49 = G2) (eD : σ.sc sDmu = D) (eKY : σ.sc 46 = kY)
    (eK : σ.sc sK = kh) (eY : σ.sc 45 = yh) (eN : σ.sc sNu = nh) (eG : σ.sc s2g = G)
    (bF : |F| ≤ 2 ^ Gu) (bQ : |Q| ≤ 2 ^ Gu) (bD : |D| ≤ 2 ^ Gu) (bK : |kh| ≤ 2 ^ Gu) (bN : |nh| ≤ 2 ^ Gu)
    (bG : |G| ≤ 2 ^ Gu) (bG2 : |G2| ≤ 2 ^ (2 * Gu)) (bKY : |kY| ≤ 2 ^ (6 * Gu + 7)) (bY : |yh| ≤ 2 ^ (5 * Gu + 7))
    (bB : ∀ i j, |Bh i j| ≤ 2 ^ Gu) (bMu : ∀ j, |mu j| ≤ 2 ^ Gu) (bU : ∀ j, |(Bh *ᵥ Γ) j| ≤ 2 ^ Gu)
    (bV : ∀ j, |(Bhᵀ *ᵥ mu) j| ≤ 2 ^ Gu) (hd : (d : ℤ) ≤ 2 ^ Gu)
    (hE : 2 * Gu < ℓ) (hℓ : d * 2 ^ (2 * Gu) < 2 ^ ℓ) (hT : 13 * Gu + 11 < ℓ) (hTa : 13 * Gu + 11 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR9a L) σ (r9aUnits d Gu) (fun σ' =>
      (∀ j : Fin d, σ'.arr 31 j = (Bhᵀ *ᵥ mu) j) ∧ (∀ j : Fin d, σ'.arr 28 j = (Bh *ᵥ (Bhᵀ *ᵥ mu)) j) ∧
      σ'.sc 54 = (((Bh *ᵥ Γ) ⬝ᵥ mu : ℤ) : ℝ) ∧ σ'.sc 55 = (((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu) : ℤ) : ℝ) ∧
      (∀ k < 6, σ'.sc (56 + k) =
        w3 F Q G2 D kY ((Bh *ᵥ Γ) ⬝ᵥ mu) ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)) kh yh nh G k) ∧
      σ'.draws = σ.draws ∧ FrameA S9a N9a (A9a (d := d)) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  -- v̂ = B̂ᵀ μ̂
  refine XV.seq (XV.matvecT hL (σ := σ) (z := sZ) (r := 30) (t := tR) (aM := aB) (ax := aMu) (ay := 31) (ni := 24)
    (nr := 22) (nk := 23) (nd := rD) (none := rOne) (E := Gu) (M := Bh) (x := mu) (by r9omega) (by r9omega)
    (by r9omega) (by r9omega) hz (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega)
    (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by decide) hD h1 eB eMu bB bMu hE hℓ)
    fun σ1 ⟨v1, d1, F1⟩ => ?_
  have s1 : ∀ y, y < tR → y ≠ 30 → σ1.sc y = σ.sc y := fun y h h' => F1.2.1 y (by omega)
  have n1 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ1.nat j = σ.nat j := fun j a b c => F1.1 j (by omega)
  have r1 : ∀ b k, b ≠ 31 → σ1.arr b k = σ.arr b k := fun b k hb => F1.2.2.1 b k (fun h => hb h.1)
  -- B̂ v̂
  refine XV.seq (XV.matvec hL (σ := σ1) (z := sZ) (r := 30) (t := tR) (aM := aB) (ax := 31) (ay := 28) (ni := 24)
    (nr := 22) (nk := 23) (nd := rD) (none := rOne) (E := Gu) (M := Bh) (x := Bhᵀ *ᵥ mu) (by r9omega)
    (by r9omega) (by r9omega) (by r9omega) (by rw [s1 _ (by r9omega) (by r9omega), hz]) (by r9omega)
    (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by r9omega)
    (by r9omega) (by decide) (by rw [n1 _ (by decide) (by decide) (by decide), hD])
    (by rw [n1 _ (by decide) (by decide) (by decide), h1]) (fun i j => by rw [r1 _ _ (by decide), eB]) v1 bB bV
    hE hℓ) fun σ2 ⟨v2, d2, F2⟩ => ?_
  have s2 : ∀ y, y < tR → y ≠ 30 → σ2.sc y = σ.sc y := fun y h h' => by
    rw [F2.2.1 y (by omega), s1 y h h']
  have n2 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ2.nat j = σ.nat j := fun j a b c => by
    rw [F2.1 j (by omega), n1 j a b c]
  have r2 : ∀ b k, b ≠ 31 → b ≠ 28 → σ2.arr b k = σ.arr b k := fun b k hb hb' => by
    rw [F2.2.2.1 b k (fun h => hb' h.1), r1 b k hb]
  -- u·μ̂
  refine XV.seq (XV.dot hL (σ := σ2) (z := sZ) (r := 54) (t := tR) (ax := aU) (ay := aMu) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := Gu) (x := Bh *ᵥ Γ) (y := mu) (by r9omega) (by r9omega) (by r9omega)
    (by r9omega) (by rw [s2 _ (by r9omega) (by r9omega), hz]) (by r9omega) (by r9omega) (by r9omega) (by r9omega)
    (by r9omega) (by r9omega) (by decide) (by rw [n2 _ (by decide) (by decide) (by decide), hD])
    (by rw [n2 _ (by decide) (by decide) (by decide), h1]) (fun k => by rw [r2 _ _ (by decide) (by decide), eU])
    (fun k => by rw [r2 _ _ (by decide) (by decide), eMu]) bU bMu hE hℓ) fun σ3 ⟨v3, d3, F3⟩ => ?_
  have s3 : ∀ y, y < tR → y ≠ 30 → y ≠ 54 → σ3.sc y = σ.sc y := fun y h h' h'' => by
    rw [F3.2.1 y (by omega), s2 y h h']
  have n3 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ3.nat j = σ.nat j := fun j a b c => by
    rw [F3.1 j (by omega), n2 j a b c]
  have r3 : ∀ b k, σ3.arr b k = σ2.arr b k := fun b k => F3.2.2.1 b k id
  -- v̂·v̂
  refine XV.seq (XV.dot hL (σ := σ3) (z := sZ) (r := 55) (t := tR) (ax := 31) (ay := 31) (nr := 22) (nk := 23)
    (nd := rD) (none := rOne) (E := Gu) (x := Bhᵀ *ᵥ mu) (y := Bhᵀ *ᵥ mu) (by r9omega) (by r9omega)
    (by r9omega) (by r9omega) (by rw [s3 _ (by r9omega) (by r9omega) (by r9omega), hz]) (by r9omega) (by r9omega)
    (by r9omega) (by r9omega) (by r9omega) (by r9omega) (by decide)
    (by rw [n3 _ (by decide) (by decide) (by decide), hD]) (by rw [n3 _ (by decide) (by decide) (by decide), h1])
    (fun k => by rw [r3, F2.2.2.1 _ _ (fun h => absurd h.1 (by decide)), v1])
    (fun k => by rw [r3, F2.2.2.1 _ _ (fun h => absurd h.1 (by decide)), v1]) bV bV hE hℓ)
    fun σ4 ⟨v4, d4, F4⟩ => ?_
  have s4 : ∀ y, y < tR → y ≠ 30 → y ≠ 54 → y ≠ 55 → σ4.sc y = σ.sc y := fun y h h' h'' h''' => by
    rw [F4.2.1 y (by omega), s3 y h h' h'']
  have n4 : ∀ j, j ≠ 22 → j ≠ 23 → j ≠ 24 → σ4.nat j = σ.nat j := fun j a b c => by
    rw [F4.1 j (by omega), n3 j a b c]
  have r4 : ∀ b k, σ4.arr b k = σ2.arr b k := fun b k => by rw [F4.2.2.1 b k id, r3]
  have e54 : σ4.sc 54 = (((Bh *ᵥ Γ) ⬝ᵥ mu : ℤ) : ℝ) := by rw [F4.2.1 54 (by r9omega), v3]
  -- the third line
  set su := (Bh *ᵥ Γ) ⬝ᵥ mu with hsu
  set sv := (Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu) with hsv
  have hin : ∀ y ∈ sl3Ins, σ4.sc y = sl3I F Q G2 D kY su sv kh yh nh G y := by
    intro y hy
    simp only [sl3Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eF]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eQ]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eG2]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eD]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eKY]; simp [sl3I]
    · rw [e54]; simp [sl3I]
    · rw [v4]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eK]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eY]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eN]; simp [sl3I]
    · rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), eG]; simp [sl3I]
  have bsu : |su| ≤ 2 ^ (3 * Gu) := dot_le_three bU bMu hd
  have bsv : |sv| ≤ 2 ^ (3 * Gu) := dot_le_three bV bV hd
  have hinB : ∀ y ∈ sl3Ins, |sl3I F Q G2 D kY su sv kh yh nh G y| ≤ 2 ^ ev Gu (sl3In y) := by
    intro y hy
    simp only [sl3Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sl3I, sl3In, sl1Et, ev, s2p, s2pF, sDmu, sK, sNu, s2g, bF, bQ, bG2, bD, bKY, bsu, bsv, bK, bY, bN, bG]
  refine XV.mono (XV.sl hL (sl3C_ok hlay) sl3St_chk (fun k hk => by
      simp only [sl3St_length] at hk; interval_cases k <;> trivial)
    (by simp [sl3C, sl3St_length]) (by simp only [ev, sl3T]; omega) (by simp only [ev, sl3T]; omega) hinB
    (σ := σ4) hin (by simp only [sl3C]; rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), hz])
    (by simp only [sl3C]; rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), c1])
    (by simp only [sl3C]; rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), c2])
    (by simp only [sl3C]; rw [s4 _ (by r9omega) (by r9omega) (by r9omega) (by r9omega), c4])
    (by simp only [sl3C]; rw [n4 _ (by decide) (by decide) (by decide), h1])) le_rfl fun σ5 ⟨v5, d5, F5⟩ => ?_
  have r5 : ∀ b k, σ5.arr b k = σ2.arr b k := fun b k => by rw [F5.2.2.1, r4]
  refine ⟨fun j => by rw [r5, F2.2.2.1 _ _ (fun h => absurd h.1 (by decide)), v1], fun j => by rw [r5, v2],
    by rw [F5.2.1 54 (by simp only [sl3C, sl3St_length]; omega), e54],
    by rw [F5.2.1 55 (by simp only [sl3C, sl3St_length]; omega), v4],
    fun k hk => v5 k (by simpa [sl3St_length] using hk), by rw [d5, d4, d3, d2, d1], ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k hb => ?_, ?_, ?_⟩
  · simp only [N9a, not_or] at hj
    rw [F5.1 j (by simp only [sl3C]; omega), n4 j hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2]
  · simp only [S9a, tR, not_or, not_and, not_le, not_lt] at hy
    rw [F5.2.1 y (by simp only [sl3C, sl3St_length]; omega),
      s4 y (by simp only [tR]; omega) hy.1 (by omega) (by omega)]
  · simp only [A9a, not_or, not_and, not_lt] at hb
    rw [r5, F2.2.2.1 b k (fun h => by have := hb.2 h.1; omega), F1.2.2.1 b k (fun h => by have := hb.1 h.1; omega)]
  · rw [F5.2.2.2.1, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]
  · rw [F5.2.2.2.2, F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]

end AdversarialBco.Bit.Transfer.BLM
