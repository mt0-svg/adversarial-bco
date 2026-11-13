/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllConst

@[expose] public section

/-!
# The constants of ELL-R and BIS-R, second part

`L_G` as the fraction `LGn / LGd`, the fraction `Nx / Dx` of `ellJ_eq` and its ceiling `X`, then `j = lg X`,
`lg R̄` and `λ` in registers; `XV.ellJ` chains the four stages from the inputs of the projection routine.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## `L_G` as a fraction -/

/-- `L_G = LGn / LGd`: if `0 < D_f`, `LGn = tr(P) R̄ D_f + |f|₁` into `c + 3` and `LGd = D_f` into `c + 4`; else
`tr(P) R̄` and `1`. -/
def xellJb (L : Layout) (B : EllBlk) (u c : ℕ) : XCmd :=
  xifS L u B.sDf
    (.seq ((IE.op .add (.op .mul (.op .mul (.sc (c + 1)) (.sc c)) (.sc B.sDf)) (.sc (c + 2))).code L u (c + 3) (c + 24))
      ((IE.sc B.sDf).code L u (c + 4) (c + 24)))
    (.seq ((IE.op .mul (.sc (c + 1)) (.sc c)).code L u (c + 3) (c + 24)) ((IE.sc (u + 1)).code L u (c + 4) (c + 24)))

set_option maxHeartbeats 2000000 in
/-- The rule of `xellJb`. -/
theorem XV.ellJb {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {u c E : ℕ} {Rb trP F1 : ℤ} {Df : ℕ} (hDu : B.sDf < u) (hc : u + 2 ≤ c) (hS : c + 60 ≤ L.NS)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hR : σ.sc c = Rb) (hT : σ.sc (c + 1) = trP)
    (hF : σ.sc (c + 2) = F1) (hD : σ.sc B.sDf = Df) (bR : |Rb| ≤ 2 ^ E) (bT : |trP| ≤ 2 ^ E) (bF : |F1| ≤ 2 ^ E)
    (bD : |(Df : ℤ)| ≤ 2 ^ E) (hℓ : 3 * E + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xellJb L B u c) σ 10 (fun σ' =>
      σ'.sc (c + 3) = ((if Df = 0 then trP * Rb else trP * Rb * Df + F1 : ℤ) : ℝ) ∧
      σ'.sc (c + 4) = ((if Df = 0 then 1 else Df : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = c + 3 ∨ y = c + 4 ∨ c + 24 ≤ y) (fun _ => False) σ σ') := by
  have hEℓ : E < ℓ := by omega
  have hz' : |σ.sc u| < 2 ^ ℓ := by rw [hz, abs_zero]; positivity
  have hD' : |σ.sc B.sDf| < 2 ^ ℓ := by rw [hD]; exact_mod_cast absR_lt bD hEℓ
  have b1 : |(1 : ℤ)| ≤ 2 ^ E := one_le_two_pow E
  by_cases hD0 : Df = 0
  · refine XV.mono (XV.ifS_f (K := 8) hL (by omega) (by omega) hz' hD' (by rw [hz, hD, hD0]; simp) ?_) (by norm_num)
      (fun _ h => h)
    refine XV.mono (K := 3 + 1) ?_ (by norm_num) (fun _ h => h)
    refine XV.seq (XV.ieRun (E := E) (e := IE.op .mul (.sc (c + 1)) (.sc c)) (v := trP * Rb) (ℓ := ℓ) (X := X) hL
      (z := u) (x := c + 3) (t := c + 24) (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
      (by omega) (by omega) (by simp only [IE.scr]; omega) hz
      (by simp only [IE.Leaves]; exact ⟨⟨trP, hT, bT⟩, ⟨Rb, hR, bR⟩⟩)
      (by simp only [IE.top, IE.mag]; omega) (by simp only [IE.eval, RealRAM.Op2.eval, hT, hR]; push_cast; ring))
      fun σ1 ⟨v1, _, d1, F1'⟩ => ?_
    refine XV.mono (XV.ieRun (E := E) (e := IE.sc (u + 1)) (v := 1) (ℓ := ℓ) (X := X) hL
      (z := u) (x := c + 4) (t := c + 24) (by simp only [IE.WF]; omega) (by omega) (by omega)
      (by simp only [IE.scr]; omega) (by rw [F1'.2.1 _ (by omega), hz])
      (by simp only [IE.Leaves]; exact ⟨1, by rw [F1'.2.1 _ (by omega), h1, Int.cast_one], b1⟩)
      (by simp only [IE.top]; omega) (by simp only [IE.eval]; rw [F1'.2.1 _ (by omega), h1, Int.cast_one]))
      (by simp only [IE.units]; norm_num) fun σ2 ⟨v2, _, d2, F2⟩ => ?_
    refine ⟨by rw [F2.2.1 _ (by omega), v1]; simp [hD0], by rw [v2]; simp [hD0], by rw [d2, d1], ?_⟩
    exact (F1'.mono (fun y h => by omega) (fun _ h => h)).trans (F2.mono (fun y h => by omega) (fun _ h => h))
  · have hDp : (0 : ℝ) < Df := by exact_mod_cast Nat.pos_of_ne_zero hD0
    refine XV.mono (XV.ifS_t (K := 9) hL (by omega) (by omega) hz' hD' (by rw [hz, hD]; exact hDp) ?_) (by norm_num)
      (fun _ h => h)
    refine XV.mono (K := 7 + 1) ?_ (by norm_num) (fun _ h => h)
    refine XV.seq (XV.ieRun (E := E)
      (e := IE.op .add (.op .mul (.op .mul (.sc (c + 1)) (.sc c)) (.sc B.sDf)) (.sc (c + 2)))
      (v := trP * Rb * Df + F1) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 3) (t := c + 24)
      (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
      (by omega) (by omega) (by simp only [IE.scr]; omega) hz
      (by
        simp only [IE.Leaves]
        exact ⟨⟨⟨⟨trP, hT, bT⟩, ⟨Rb, hR, bR⟩⟩, ⟨Df, by rw [hD, Int.cast_natCast], bD⟩⟩, ⟨F1, hF, bF⟩⟩)
      (by simp only [IE.top, IE.mag]; omega)
      (by simp only [IE.eval, RealRAM.Op2.eval, hT, hR, hD, hF]; push_cast; ring))
      fun σ1 ⟨v1, _, d1, F1'⟩ => ?_
    refine XV.mono (XV.ieRun (E := E) (e := IE.sc B.sDf) (v := Df) (ℓ := ℓ) (X := X) hL
      (z := u) (x := c + 4) (t := c + 24) (by simp only [IE.WF]; omega) (by omega) (by omega)
      (by simp only [IE.scr]; omega) (by rw [F1'.2.1 _ (by omega), hz])
      (by simp only [IE.Leaves]; exact ⟨Df, by rw [F1'.2.1 _ (by omega), hD, Int.cast_natCast], bD⟩)
      (by simp only [IE.top]; omega) (by simp only [IE.eval]; rw [F1'.2.1 _ (by omega), hD, Int.cast_natCast]))
      (by simp only [IE.units]; norm_num) fun σ2 ⟨v2, _, d2, F2⟩ => ?_
    refine ⟨by rw [F2.2.1 _ (by omega), v1]; simp [hD0], by rw [v2]; simp [hD0], by rw [d2, d1], ?_⟩
    exact (F1'.mono (fun y h => by omega) (fun _ h => h)).trans (F2.mono (fun y h => by omega) (fun _ h => h))

/-! ## The fraction `Nx / Dx` and its ceiling -/

/-- `Nx` of `ellJ_eq`. -/
def jNx (Rb LGn LGd en ed rn rd : ℤ) : ℤ :=
  (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else 3 * LGn * Rb * ed) * (if rn ≤ rd then rd else 1)

/-- `Dx` of `ellJ_eq`. -/
def jDx (Rb LGn LGd en ed rn rd : ℤ) : ℤ :=
  (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else LGd * en) * (if rn ≤ rd then rn else 1)

/-- `T₁ = 3 LGn R̄ e_d` into `c + 5`, `T₂ = e_n LGd` into `c + 6`; into `c + 7, c + 8` the pair `T₁, LGd e_n` if
`T₂ < T₁`, else `1, 1`; into `c + 9, c + 10` that pair if `r_d < r_n`, else times `r_d, r_n`; `⌈Nx / Dx⌉` into
`c + 11`. -/
def xellJc (L : Layout) (B : EllBlk) (u c : ℕ) : XCmd :=
  .seq ((IE.op .mul (.op .mul (.op .add (.op .add (.sc (c + 3)) (.sc (c + 3))) (.sc (c + 3))) (.sc c))
    (.sc B.sed)).code L u (c + 5) (c + 24))
  (.seq ((IE.op .mul (.sc B.sen) (.sc (c + 4))).code L u (c + 6) (c + 24))
  (.seq (xifS L (c + 6) (c + 5)
      (.seq ((IE.sc (c + 5)).code L u (c + 7) (c + 24))
        ((IE.op .mul (.sc (c + 4)) (.sc B.sen)).code L u (c + 8) (c + 24)))
      (.seq ((IE.sc (u + 1)).code L u (c + 7) (c + 24)) ((IE.sc (u + 1)).code L u (c + 8) (c + 24))))
  (.seq (xifS L B.srd B.srn
      (.seq ((IE.sc (c + 7)).code L u (c + 9) (c + 24)) ((IE.sc (c + 8)).code L u (c + 10) (c + 24)))
      (.seq ((IE.op .mul (.sc (c + 7)) (.sc B.srd)).code L u (c + 9) (c + 24))
        ((IE.op .mul (.sc (c + 8)) (.sc B.srn)).code L u (c + 10) (c + 24))))
    ((ieCeil (c + 9) (c + 10) (u + 1)).code L u (c + 11) (c + 24)))))

/-- A copy `x := y` by the code of `IE.sc y`, for an integer `v` below `2^E`. -/
theorem XV.copyI {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z x y t E : ℕ} {v : ℤ}
    (hy : y < t) (hz : z < t) (hx : x < t) (hS : t ≤ L.NS) (hz0 : σ.sc z = 0) (hv : σ.sc y = v) (bv : |v| ≤ 2 ^ E)
    (hE : E < ℓ) : XRunsB L X ℓa ℓ ((IE.sc y).code L z x t) σ 1 (XV.ExprPost ℓ σ x t v) :=
  XV.ieRun (E := E) hL (by simp only [IE.WF]; omega) hz hx (by simp only [IE.scr]; omega) hz0
    (by simp only [IE.Leaves]; exact ⟨v, hv, bv⟩) (by simp only [IE.top]; omega) (by simp only [IE.eval]; rw [hv])

/-- A product `x := a b` by the code of `IE.op .mul`, for integers below `2^E`. -/
theorem XV.mulIE {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z x a b t E : ℕ}
    {va vb : ℤ} (ha : a < t) (hb : b < t) (hz : z < t) (hx : x < t) (hS : t + 2 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hva : σ.sc a = va) (hvb : σ.sc b = vb) (ba : |va| ≤ 2 ^ E) (bb : |vb| ≤ 2 ^ E) (hE : 2 * E < ℓ) :
    XRunsB L X ℓa ℓ ((IE.op .mul (.sc a) (.sc b)).code L z x t) σ 3 (XV.ExprPost ℓ σ x t (va * vb)) :=
  XV.ieRun (E := E) hL (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) hz hx
    (by simp only [IE.scr]; omega) hz0 (by simp only [IE.Leaves]; exact ⟨⟨va, hva, ba⟩, ⟨vb, hvb, bb⟩⟩)
    (by simp only [IE.top, IE.mag]; omega) (by simp only [IE.eval, RealRAM.Op2.eval, hva, hvb]; push_cast; ring)

set_option maxHeartbeats 4000000 in
/-- The rule of `xellJc`. -/
theorem XV.ellJc {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {u c E : ℕ} {Rb LGn LGd en ed rn rd : ℤ} (hBu : B.sed < u ∧ B.sen < u ∧ B.srn < u ∧ B.srd < u)
    (hc : u + 2 ≤ c) (hS : c + 60 ≤ L.NS) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hR : σ.sc c = Rb)
    (hLn : σ.sc (c + 3) = LGn) (hLd : σ.sc (c + 4) = LGd) (hen : σ.sc B.sen = en) (hed : σ.sc B.sed = ed)
    (hrn : σ.sc B.srn = rn) (hrd : σ.sc B.srd = rd) (bR : |Rb| ≤ 2 ^ E) (bLn : |LGn| ≤ 2 ^ E)
    (bLd : |LGd| ≤ 2 ^ E) (ben : |en| ≤ 2 ^ E) (bed : |ed| ≤ 2 ^ E) (brn : |rn| ≤ 2 ^ E) (brd : |rd| ≤ 2 ^ E)
    (bT1 : |3 * LGn * Rb * ed| ≤ 2 ^ E) (bD1 : |LGd * en| ≤ 2 ^ E) (bNx : |jNx Rb LGn LGd en ed rn rd| ≤ 2 ^ E)
    (bDx : |jDx Rb LGn LGd en ed rn rd| ≤ 2 ^ E) (hℓ : 3 * E + 3 < ℓ) :
    XRunsB L X ℓa ℓ (xellJc L B u c) σ 32 (fun σ' =>
      σ'.sc (c + 11) = (((jNx Rb LGn LGd en ed rn rd + jDx Rb LGn LGd en ed rn rd - 1) /
        jDx Rb LGn LGd en ed rn rd : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => c + 5 ≤ y) (fun _ => False) σ σ') := by
  obtain ⟨hsed, hsen, hsrn, hsrd⟩ := hBu
  have b1 : |(1 : ℤ)| ≤ 2 ^ E := one_le_two_pow E
  have hEℓ : E < ℓ := by omega
  -- `T₁`, `T₂`
  refine XV.mono (K := 9 + (3 + (5 + (8 + 7)))) ?_ (by norm_num) (fun _ h => h)
  refine XV.seq (XV.ieRun (E := E)
    (e := IE.op .mul (.op .mul (.op .add (.op .add (.sc (c + 3)) (.sc (c + 3))) (.sc (c + 3))) (.sc c)) (.sc B.sed))
    (v := 3 * LGn * Rb * ed) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 5) (t := c + 24)
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
    (by simp only [IE.scr]; omega) hz
    (by simp only [IE.Leaves]; exact ⟨⟨⟨⟨⟨LGn, hLn, bLn⟩, ⟨LGn, hLn, bLn⟩⟩, ⟨LGn, hLn, bLn⟩⟩, ⟨Rb, hR, bR⟩⟩,
      ⟨ed, hed, bed⟩⟩)
    (by simp only [IE.top, IE.mag]; omega)
    (by simp only [IE.eval, RealRAM.Op2.eval, hLn, hR, hed]; push_cast; ring)) fun σ1 ⟨v1, _, d1, F1⟩ => ?_
  have e1 : ∀ y, y ≠ c + 5 → y < c + 24 → σ1.sc y = σ.sc y := fun y h h' => F1.2.1 _ (by omega)
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 6) (t := c + 24) (a := B.sen)
    (b := c + 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [e1 _ (by omega) (by omega), hz])
    (by rw [e1 _ (by omega) (by omega), hen]) (by rw [e1 _ (by omega) (by omega), hLd]) ben bLd (by omega))
    fun σ2 ⟨v2, _, d2, F2⟩ => ?_
  have e2 : ∀ y, y ≠ c + 5 → y ≠ c + 6 → y < c + 24 → σ2.sc y = σ.sc y := fun y h h' h'' => by
    rw [F2.2.1 _ (by omega), e1 _ h h'']
  have c2 : σ2.sc (c + 5) = ((3 * LGn * Rb * ed : ℤ) : ℝ) := by rw [F2.2.1 _ (by omega), v1]
  -- `Nx₁`, `Dx₁`
  obtain ⟨Nx1, eN1⟩ : ∃ x : ℤ, x = if 3 * LGn * Rb * ed ≤ en * LGd then 1 else 3 * LGn * Rb * ed := ⟨_, rfl⟩
  obtain ⟨Dx1, eD1⟩ : ∃ x : ℤ, x = if 3 * LGn * Rb * ed ≤ en * LGd then 1 else LGd * en := ⟨_, rfl⟩
  have bN1 : |Nx1| ≤ 2 ^ E := by rw [eN1]; split_ifs <;> assumption
  have bD1' : |Dx1| ≤ 2 ^ E := by rw [eD1]; split_ifs <;> assumption
  have hv5 : |σ2.sc (c + 5)| < 2 ^ ℓ := by rw [c2]; exact absR_lt bT1 hEℓ
  have hv6 : |σ2.sc (c + 6)| < 2 ^ ℓ := by
    rw [v2]; exact absR_lt (by rw [mul_comm]; exact bD1) hEℓ
  refine XV.seq (K₁ := 5) (Q₁ := fun σ3 => σ3.sc (c + 7) = Nx1 ∧ σ3.sc (c + 8) = Dx1 ∧ σ3.draws = σ2.draws ∧
    FrameP (fun y => y = c + 7 ∨ y = c + 8 ∨ c + 24 ≤ y) (fun _ => False) σ2 σ3) ?_ fun σ3 ⟨n3, m3, d3, F3⟩ => ?_
  · by_cases hT : 3 * LGn * Rb * ed ≤ en * LGd
    · have hN1 : Nx1 = 1 := by rw [eN1, if_pos hT]
      have hD1 : Dx1 = 1 := by rw [eD1, if_pos hT]
      refine XV.mono (XV.ifS_f (K := 1 + 1) hL (by omega) (by omega) hv6 hv5 (by
        rw [v2, c2, not_lt]; exact_mod_cast hT) ?_) (by norm_num) (fun _ h => h)
      refine XV.seq (XV.copyI (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 7) (t := c + 24) (y := u + 1)
        (v := 1) (by omega) (by omega) (by omega) (by omega) (by rw [e2 _ (by omega) (by omega) (by omega), hz])
        (by rw [e2 _ (by omega) (by omega) (by omega), h1, Int.cast_one]) b1 hEℓ) fun σ' ⟨w1, _, g1, G1⟩ => ?_
      refine XV.mono (XV.copyI (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 8) (t := c + 24) (y := u + 1)
        (v := 1) (by omega) (by omega) (by omega) (by omega)
        (by rw [G1.2.1 _ (by omega), e2 _ (by omega) (by omega) (by omega), hz])
        (by rw [G1.2.1 _ (by omega), e2 _ (by omega) (by omega) (by omega), h1, Int.cast_one]) b1 hEℓ) le_rfl
        fun σ'' ⟨w2, _, g2, G2⟩ => ?_
      exact ⟨by rw [G2.2.1 _ (by omega), w1, hN1], by rw [w2, hD1], by rw [g2, g1],
        (G1.mono (fun y h => by omega) (fun _ h => h)).trans (G2.mono (fun y h => by omega) (fun _ h => h))⟩
    · have hN1 : Nx1 = 3 * LGn * Rb * ed := by rw [eN1, if_neg hT]
      have hD1 : Dx1 = LGd * en := by rw [eD1, if_neg hT]
      refine XV.mono (XV.ifS_t (K := 1 + 3) hL (by omega) (by omega) hv6 hv5 (by
        rw [v2, c2]; exact_mod_cast (not_le.1 hT)) ?_) (by norm_num) (fun _ h => h)
      refine XV.seq (XV.copyI (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 7) (t := c + 24) (y := c + 5)
        (v := 3 * LGn * Rb * ed) (by omega) (by omega) (by omega) (by omega)
        (by rw [e2 _ (by omega) (by omega) (by omega), hz]) c2 bT1 hEℓ) fun σ' ⟨w1, _, g1, G1⟩ => ?_
      refine XV.mono (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 8) (t := c + 24) (a := c + 4)
        (b := B.sen) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [G1.2.1 _ (by omega), e2 _ (by omega) (by omega) (by omega), hz])
        (by rw [G1.2.1 _ (by omega), e2 _ (by omega) (by omega) (by omega), hLd])
        (by rw [G1.2.1 _ (by omega), e2 _ (by omega) (by omega) (by omega), hen]) bLd ben (by omega)) (by norm_num)
        fun σ'' ⟨w2, _, g2, G2⟩ => ?_
      exact ⟨by rw [G2.2.1 _ (by omega), w1, hN1], by rw [w2, hD1], by rw [g2, g1],
        (G1.mono (fun y h => by omega) (fun _ h => h)).trans (G2.mono (fun y h => by omega) (fun _ h => h))⟩
  have e3 : ∀ y, y ≠ c + 5 → y ≠ c + 6 → y ≠ c + 7 → y ≠ c + 8 → y < c + 24 → σ3.sc y = σ.sc y :=
    fun y h h' h'' h''' h4 => by rw [F3.2.1 _ (by omega), e2 _ h h' h4]
  -- `Nx`, `Dx`
  have hNx : jNx Rb LGn LGd en ed rn rd = Nx1 * (if rn ≤ rd then rd else 1) := by rw [jNx, eN1]
  have hDx : jDx Rb LGn LGd en ed rn rd = Dx1 * (if rn ≤ rd then rn else 1) := by rw [jDx, eD1]
  have hvrd : |σ3.sc B.srd| < 2 ^ ℓ := by
    rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrd]; exact absR_lt brd hEℓ
  have hvrn : |σ3.sc B.srn| < 2 ^ ℓ := by
    rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrn]; exact absR_lt brn hEℓ
  have z3 : σ3.sc u = 0 := by rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hz]
  refine XV.seq (K₁ := 8) (Q₁ := fun σ4 => σ4.sc (c + 9) = jNx Rb LGn LGd en ed rn rd ∧
    σ4.sc (c + 10) = jDx Rb LGn LGd en ed rn rd ∧ σ4.draws = σ3.draws ∧
    FrameP (fun y => y = c + 9 ∨ y = c + 10 ∨ c + 24 ≤ y) (fun _ => False) σ3 σ4) ?_ fun σ4 ⟨n4, m4, d4, F4⟩ => ?_
  · by_cases hr : rn ≤ rd
    · rw [hNx, hDx, if_pos hr, if_pos hr]
      refine XV.mono (XV.ifS_f (K := 3 + 3) hL (by omega) (by omega) hvrd hvrn (by
        rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrd,
          e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrn, not_lt]; exact_mod_cast hr) ?_)
        (by norm_num) (fun _ h => h)
      refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 9) (t := c + 24) (a := c + 7)
        (b := B.srd) (by omega) (by omega) (by omega) (by omega) (by omega) z3 n3
        (by rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrd]) bN1 brd (by omega))
        fun σ' ⟨w1, _, g1, G1⟩ => ?_
      refine XV.mono (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 10) (t := c + 24) (a := c + 8)
        (b := B.srn) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [G1.2.1 _ (by omega), z3])
        (by rw [G1.2.1 _ (by omega), m3])
        (by rw [G1.2.1 _ (by omega), e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrn]) bD1' brn
        (by omega)) (by norm_num) fun σ'' ⟨w2, _, g2, G2⟩ => ?_
      exact ⟨by rw [G2.2.1 _ (by omega), w1], by rw [w2], by rw [g2, g1],
        (G1.mono (fun y h => by omega) (fun _ h => h)).trans (G2.mono (fun y h => by omega) (fun _ h => h))⟩
    · rw [hNx, hDx, if_neg hr, if_neg hr, mul_one, mul_one]
      refine XV.mono (XV.ifS_t (K := 1 + 1) hL (by omega) (by omega) hvrd hvrn (by
        rw [e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrd,
          e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), hrn]; exact_mod_cast (not_le.1 hr)) ?_)
        (by norm_num) (fun _ h => h)
      refine XV.seq (XV.copyI (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 9) (t := c + 24) (y := c + 7)
        (by omega) (by omega) (by omega) (by omega) z3 n3 bN1 hEℓ) fun σ' ⟨w1, _, g1, G1⟩ => ?_
      refine XV.mono (XV.copyI (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 10) (t := c + 24) (y := c + 8)
        (by omega) (by omega) (by omega) (by omega) (by rw [G1.2.1 _ (by omega), z3])
        (by rw [G1.2.1 _ (by omega), m3]) bD1' hEℓ) (by norm_num) fun σ'' ⟨w2, _, g2, G2⟩ => ?_
      exact ⟨by rw [G2.2.1 _ (by omega), w1], by rw [w2], by rw [g2, g1],
        (G1.mono (fun y h => by omega) (fun _ h => h)).trans (G2.mono (fun y h => by omega) (fun _ h => h))⟩
  -- the ceiling
  have z4 : σ4.sc u = 0 := by rw [F4.2.1 _ (by omega), z3]
  have o4 : σ4.sc (u + 1) = 1 := by
    rw [F4.2.1 _ (by omega), e3 _ (by omega) (by omega) (by omega) (by omega) (by omega), h1]
  refine XV.mono (XV.ieRun (E := E) (e := ieCeil (c + 9) (c + 10) (u + 1))
    (v := (jNx Rb LGn LGd en ed rn rd + jDx Rb LGn LGd en ed rn rd - 1) / jDx Rb LGn LGd en ed rn rd)
    (ℓ := ℓ) (X := X) hL (z := u) (x := c + 11) (t := c + 24)
    (by simp only [ieCeil, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
    (by simp only [ieCeil, IE.scr]; omega) z4
    (by
      simp only [ieCeil, IE.Leaves]
      exact ⟨⟨⟨⟨_, n4, bNx⟩, ⟨_, m4, bDx⟩⟩, ⟨1, by rw [o4, Int.cast_one], b1⟩⟩, ⟨_, m4, bDx⟩⟩)
    (by simp only [ieCeil, IE.top, IE.mag]; omega)
    (by
      simp only [ieCeil, IE.eval, RealRAM.Op2.eval, n4, m4, o4]
      rw [show ((jNx Rb LGn LGd en ed rn rd : ℤ) : ℝ) + (jDx Rb LGn LGd en ed rn rd : ℝ) - 1 =
        ((jNx Rb LGn LGd en ed rn rd + jDx Rb LGn LGd en ed rn rd - 1 : ℤ) : ℝ) by push_cast; ring,
        Int.floor_intCast, Int.floor_intCast])) (by simp only [ieCeil, IE.units]; norm_num)
    fun σ5 ⟨v5, _, d5, F5⟩ => ?_
  refine ⟨v5, by rw [d5, d4, d3, d2, d1], ?_⟩
  exact ((((F1.mono (fun y h => by omega) (fun _ h => h)).trans (F2.mono (fun y h => by omega) (fun _ h => h))).trans
    (F3.mono (fun y h => by omega) (fun _ h => h))).trans (F4.mono (fun y h => by omega) (fun _ h => h))).trans
    (F5.mono (fun y h => by omega) (fun _ h => h))

/-! ## `j`, `lg R̄`, `λ` -/

/-- `lg X` into the register `n0 + 8`, `lg R̄` into `n0 + 9`, their sum into `n0 + 10`; `c + 12` is scratch. -/
def xellJd (L : Layout) (c n0 : ℕ) : XCmd :=
  .seq (xclogS L (c + 12) (c + 11) (n0 + 8) (n0 + 4))
  (.seq (xclogS L (c + 12) c (n0 + 9) (n0 + 4)) (.prim (.frag (.nadd (n0 + 10) (n0 + 9) (n0 + 8)))))

theorem clog_le_of_le {v : ℤ} {G : ℕ} (h : v ≤ 2 ^ G) : Nat.clog 2 v.toNat ≤ G := by
  apply Nat.clog_le_of_le_pow
  have : (v.toNat : ℤ) ≤ 2 ^ G := by
    rcases le_or_gt 0 v with h0 | h0
    · rw [Int.toNat_of_nonneg h0]; exact h
    · rw [Int.toNat_of_nonpos h0.le]; positivity
  exact_mod_cast this

/-- The rule of `xellJd`. -/
theorem XV.ellJd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {c n0 G : ℕ} {Xv Rb : ℤ}
    (hS : c + 13 ≤ L.NS) (hN : n0 + 11 ≤ L.NN) (hX : σ.sc (c + 11) = Xv) (hR : σ.sc c = Rb) (hX0 : 0 ≤ Xv)
    (hR0 : 0 ≤ Rb) (bX : Xv ≤ 2 ^ G) (bR : Rb ≤ 2 ^ G) (h1 : σ.nat (n0 + 4) = 1) (hGa : 2 * G < 2 ^ ℓa)
    (hGl : G < ℓ) :
    XRunsB L X ℓa ℓ (xellJd L c n0) σ (8 * G + 9) (fun σ' =>
      σ'.nat (n0 + 8) = Nat.clog 2 Xv.toNat ∧ σ'.nat (n0 + 9) = Nat.clog 2 Rb.toNat ∧
      σ'.nat (n0 + 10) = Nat.clog 2 Rb.toNat + Nat.clog 2 Xv.toNat ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = c + 12) (fun j => n0 + 8 ≤ j ∧ j ≤ n0 + 10) σ σ') := by
  refine XV.mono (K := (4 * G + 4) + ((4 * G + 4) + 1)) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.clogS hL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hX hX0 bX h1
    (by omega) hGl) fun σ1 ⟨n1, d1, F1⟩ => ?_
  refine XV.seq (XV.clogS hL (G := G) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [F1.2.1 _ (by omega), hR]) hR0 bR (by rw [F1.1 _ (by omega), h1]) (by omega) hGl)
    fun σ2 ⟨n2, d2, F2⟩ => ?_
  have m2 : σ2.nat (n0 + 8) = Nat.clog 2 Xv.toNat := by rw [F2.1 _ (by omega), n1]
  have cX := clog_le_of_le bX
  have cR := clog_le_of_le bR
  refine XV.mono (XV.nadd hL (i := n0 + 10) (a := n0 + 9) (b := n0 + 8) (by omega) (by omega) (by omega)
    (by rw [n2]; omega) (by rw [m2]; omega)) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [m2], by simp [n2], by simp [n2, m2], by simp [d2, d1], ?_⟩
  exact (((F1.mono (fun y h => h) (fun j h => by omega)).trans (F2.mono (fun y h => h) (fun j h => by omega))).setNat
    ⟨by omega, le_rfl⟩ _)

/-! ## The four stages -/

/-- The bounds of `ellJ_bounds` on integer variables. -/
theorem jb_gen {σ d Df : ℕ} {trP F1 Rb rn rd en ed : ℤ}
    (hT : |trP| ≤ 2 ^ (σ + d)) (hF0 : 0 ≤ F1) (hF : F1 ≤ 2 ^ (σ + d)) (hR0 : 0 ≤ Rb) (hR : Rb ≤ 2 ^ σ)
    (hD : (Df : ℤ) ≤ 2 ^ σ) (hrn : 0 < rn) (hrn' : rn ≤ 2 ^ σ) (hrd : 0 < rd) (hrd' : rd ≤ 2 ^ σ)
    (hen : 0 < en) (hen' : en ≤ 2 ^ σ) (hed : 0 < ed) (hed' : ed ≤ 2 ^ σ) :
    let LGn : ℤ := if Df = 0 then trP * Rb else trP * Rb * Df + F1
    let LGd : ℤ := if Df = 0 then 1 else Df
    let Nx : ℤ := (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else 3 * LGn * Rb * ed) * (if rn ≤ rd then rd else 1)
    let Dx : ℤ := (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else LGd * en) * (if rn ≤ rd then rn else 1)
    |LGn| ≤ 2 ^ (3 * σ + d + 1) ∧ 0 < LGd ∧ LGd ≤ 2 ^ σ ∧
      |3 * LGn * Rb * ed| ≤ 2 ^ (5 * σ + d + 3) ∧ |en * LGd| ≤ 2 ^ (2 * σ) ∧ |LGd * en| ≤ 2 ^ (2 * σ) ∧
      0 < Nx ∧ Nx ≤ 2 ^ (6 * σ + d + 3) ∧ 0 < Dx ∧ Dx ≤ 2 ^ (3 * σ) ∧
      0 ≤ (Nx + Dx - 1) / Dx ∧ (Nx + Dx - 1) / Dx ≤ 2 ^ (6 * σ + d + 3) := by
  intro LGn LGd Nx Dx
  have aR : |Rb| ≤ 2 ^ σ := by rwa [abs_of_nonneg hR0]
  have aD : |(Df : ℤ)| ≤ 2 ^ σ := by rwa [Nat.abs_cast]
  have aF : |F1| ≤ 2 ^ (σ + d) := by rwa [abs_of_nonneg hF0]
  have aed : |ed| ≤ 2 ^ σ := by rwa [abs_of_pos hed]
  have aen : |en| ≤ 2 ^ σ := by rwa [abs_of_pos hen]
  have one_le : ∀ k : ℕ, (1 : ℤ) ≤ 2 ^ k := fun k => one_le_pow₀ (by norm_num)
  have hLGn : |LGn| ≤ 2 ^ (3 * σ + d + 1) := by
    by_cases h0 : Df = 0
    · have e : LGn = trP * Rb := by simp [LGn, h0]
      rw [e]; exact abs_le_pow_mono (abs_mul_le_pow hT aR) (by omega)
    · have e : LGn = trP * Rb * Df + F1 := by simp [LGn, h0]
      rw [e]
      exact abs_add_le_pow (abs_le_pow_mono (abs_mul_le_pow (abs_mul_le_pow hT aR) aD) (by omega))
        (abs_le_pow_mono aF (by omega))
  have hLGd : 0 < LGd ∧ LGd ≤ 2 ^ σ := by
    by_cases h0 : Df = 0
    · have e : LGd = 1 := by simp [LGd, h0]
      rw [e]; exact ⟨one_pos, one_le σ⟩
    · have e : LGd = Df := by simp [LGd, h0]
      rw [e]; exact ⟨by exact_mod_cast Nat.pos_of_ne_zero h0, hD⟩
  obtain ⟨hLd0, hLd⟩ := hLGd
  have aLd : |LGd| ≤ 2 ^ σ := by rwa [abs_of_pos hLd0]
  have h3 : |3 * LGn * Rb * ed| ≤ 2 ^ (5 * σ + d + 3) :=
    abs_le_pow_mono (abs_mul_le_pow (abs_mul_le_pow (abs_mul_le_pow (show |(3 : ℤ)| ≤ 2 ^ 2 by norm_num) hLGn)
      aR) aed) (by omega)
  have h4 : |en * LGd| ≤ 2 ^ (2 * σ) := abs_le_pow_mono (abs_mul_le_pow aen aLd) (by omega)
  have h5 : |LGd * en| ≤ 2 ^ (2 * σ) := abs_le_pow_mono (abs_mul_le_pow aLd aen) (by omega)
  have hp : (0 : ℤ) < en * LGd := mul_pos hen hLd0
  have hA : 0 < (if 3 * LGn * Rb * ed ≤ en * LGd then (1 : ℤ) else 3 * LGn * Rb * ed) ∧
      (if 3 * LGn * Rb * ed ≤ en * LGd then (1 : ℤ) else 3 * LGn * Rb * ed) ≤ 2 ^ (5 * σ + d + 3) := by
    split_ifs with h
    · exact ⟨one_pos, one_le _⟩
    · exact ⟨hp.trans (not_le.1 h), (le_abs_self _).trans h3⟩
  have hB : 0 < (if 3 * LGn * Rb * ed ≤ en * LGd then (1 : ℤ) else LGd * en) ∧
      (if 3 * LGn * Rb * ed ≤ en * LGd then (1 : ℤ) else LGd * en) ≤ 2 ^ (2 * σ) := by
    split_ifs with h
    · exact ⟨one_pos, one_le _⟩
    · exact ⟨mul_pos hLd0 hen, (le_abs_self _).trans h5⟩
  have hC : 0 < (if rn ≤ rd then rd else (1 : ℤ)) ∧ (if rn ≤ rd then rd else (1 : ℤ)) ≤ 2 ^ σ := by
    split_ifs
    · exact ⟨hrd, hrd'⟩
    · exact ⟨one_pos, one_le σ⟩
  have hD' : 0 < (if rn ≤ rd then rn else (1 : ℤ)) ∧ (if rn ≤ rd then rn else (1 : ℤ)) ≤ 2 ^ σ := by
    split_ifs
    · exact ⟨hrn, hrn'⟩
    · exact ⟨one_pos, one_le σ⟩
  have hNx0 : 0 < Nx := mul_pos hA.1 hC.1
  have hNx : Nx ≤ 2 ^ (6 * σ + d + 3) := by
    calc Nx ≤ 2 ^ (5 * σ + d + 3) * 2 ^ σ := mul_le_mul hA.2 hC.2 hC.1.le (by positivity)
      _ = 2 ^ (6 * σ + d + 3) := by rw [← pow_add]; congr 1; ring
  have hDx0 : 0 < Dx := mul_pos hB.1 hD'.1
  have hDx : Dx ≤ 2 ^ (3 * σ) := by
    calc Dx ≤ 2 ^ (2 * σ) * 2 ^ σ := mul_le_mul hB.2 hD'.2 hD'.1.le (by positivity)
      _ = 2 ^ (3 * σ) := by rw [← pow_add]; congr 1; ring
  refine ⟨hLGn, hLd0, hLd, h3, h4, h5, hNx0, hNx, hDx0, hDx, Int.ediv_nonneg (by omega) hDx0.le, ?_⟩
  have hle : Nx + Dx - 1 ≤ Nx * Dx := by
    nlinarith [mul_nonneg (sub_nonneg.2 (show (1 : ℤ) ≤ Nx by omega)) (sub_nonneg.2 (show (1 : ℤ) ≤ Dx by omega))]
  calc (Nx + Dx - 1) / Dx ≤ Nx * Dx / Dx := Int.ediv_le_ediv hDx0 hle
    _ = Nx := Int.mul_ediv_cancel Nx (ne_of_gt hDx0)
    _ ≤ 2 ^ (6 * σ + d + 3) := hNx

/-- The magnitudes of the constants of `ellJ_eq`. -/
theorem ellJ_bounds {d : ℕ} (I : EllI d) (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e) :
    let σ := ellSz I
    let trP : ℤ := I.P.trace
    let F1 : ℤ := ∑ i, |I.f i|
    let rn : ℤ := I.r.num
    let rd : ℤ := I.r.den
    let en : ℤ := I.e.num
    let ed : ℤ := I.e.den
    let LGn : ℤ := if I.Df = 0 then trP * I.Rb else trP * I.Rb * I.Df + F1
    let LGd : ℤ := if I.Df = 0 then 1 else I.Df
    let Nx : ℤ := (if 3 * LGn * I.Rb * ed ≤ en * LGd then 1 else 3 * LGn * I.Rb * ed) * (if rn ≤ rd then rd else 1)
    let Dx : ℤ := (if 3 * LGn * I.Rb * ed ≤ en * LGd then 1 else LGd * en) * (if rn ≤ rd then rn else 1)
    |trP| ≤ 2 ^ (σ + d) ∧ 0 ≤ F1 ∧ F1 ≤ 2 ^ (σ + d) ∧ |LGn| ≤ 2 ^ (3 * σ + d + 1) ∧ 0 < LGd ∧ LGd ≤ 2 ^ σ ∧
      |3 * LGn * I.Rb * ed| ≤ 2 ^ (5 * σ + d + 3) ∧ |en * LGd| ≤ 2 ^ (2 * σ) ∧ |LGd * en| ≤ 2 ^ (2 * σ) ∧
      0 < Nx ∧ Nx ≤ 2 ^ (6 * σ + d + 3) ∧ 0 < Dx ∧ Dx ≤ 2 ^ (3 * σ) ∧
      0 ≤ (Nx + Dx - 1) / Dx ∧ (Nx + Dx - 1) / Dx ≤ 2 ^ (6 * σ + d + 3) := by
  intro σ trP F1 rn rd en ed LGn LGd Nx Dx
  have hM := ellMx_le I
  have hdd : (d : ℤ) * 2 ^ σ ≤ 2 ^ (σ + d) := by
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le) (by positivity)
  have aT : |trP| ≤ 2 ^ (σ + d) := by
    calc |trP| = |∑ i, I.P i i| := rfl
      _ ≤ ∑ i, |I.P i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (2 : ℤ) ^ σ := Finset.sum_le_sum fun i _ => ellP_le le_rfl i i
      _ = d * 2 ^ σ := by simp
      _ ≤ 2 ^ (σ + d) := hdd
  have hF0 : 0 ≤ F1 := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hF : F1 ≤ 2 ^ (σ + d) := by
    calc F1 = ∑ i, |I.f i| := rfl
      _ ≤ ∑ _i : Fin d, (2 : ℤ) ^ σ := Finset.sum_le_sum fun i _ => ellF_le le_rfl i
      _ = d * 2 ^ σ := by simp
      _ ≤ 2 ^ (σ + d) := hdd
  have hR0 : (0 : ℤ) ≤ I.Rb := by positivity
  have hR : (I.Rb : ℤ) ≤ 2 ^ σ := by exact_mod_cast (ellRb_lt I).le
  have hD : (I.Df : ℤ) ≤ 2 ^ σ := (le_abs_self _).trans (ellDf_le le_rfl)
  have hrn : 0 < rn := Rat.num_pos.2 hr
  have hrn' : rn ≤ 2 ^ σ := (le_abs_self _).trans (abs_le_sz hM.2.2.2.2.2.2.2.2.2.2.1)
  have hrd : 0 < rd := show (0 : ℤ) < (I.r.den : ℤ) by exact_mod_cast I.r.pos
  have hrd' : rd ≤ 2 ^ σ := (le_abs_self _).trans (abs_le_sz' hM.2.2.2.2.2.2.2.2.2.2.2.1)
  have hen : 0 < en := Rat.num_pos.2 he
  have hen' : en ≤ 2 ^ σ := (le_abs_self _).trans (abs_le_sz hM.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hed : 0 < ed := show (0 : ℤ) < (I.e.den : ℤ) by exact_mod_cast I.e.pos
  have hed' : ed ≤ 2 ^ σ := (le_abs_self _).trans (abs_le_sz' hM.2.2.2.2.2.2.2.2.2.2.2.2.2)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
    jb_gen (σ := σ) (d := d) (Df := I.Df) aT hF0 hF hR0 hR hD hrn hrn' hrd hrd' hen hen' hed hed'
  exact ⟨aT, hF0, hF, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩

/-- The constants up to `λ`: `R̄` into `c`; `j`, `lg R̄`, `λ` into the registers `n0 + 8, n0 + 9, n0 + 10`. -/
def xellJ (L : Layout) (B : EllBlk) (u c n0 : ℕ) : XCmd :=
  .seq (xellJa L B u c n0) (.seq (xellJb L B u c) (.seq (xellJc L B u c) (xellJd L c n0)))

theorem abs_le_pow_of {x : ℤ} {a E : ℕ} (h : |x| ≤ 2 ^ a) (hE : a ≤ E) : |x| ≤ 2 ^ E :=
  h.trans (pow_le_pow_right₀ (by norm_num) hE)

set_option maxHeartbeats 4000000 in
/-- The rule of `xellJ`. -/
theorem XV.ellJ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA u c n0 E : ℕ} (hB : B.OK L nS nN nA) (hu : B.o ≤ u) (hc : u + 2 ≤ c) (hS : c + 60 ≤ L.NS)
    (hn : B.rE ≤ n0) (hN : n0 + 14 ≤ L.NN) (hin : EllIn B I σ) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1)
    (hone : σ.nat (n0 + 4) = 1) (hd : 1 ≤ d) (hR : ¬ I.R < 1) (hr : 0 < I.r) (he : 0 < I.e)
    (hE : 6 * ellSz I + d + 4 ≤ E) (hℓ : 3 * E + 3 < ℓ) (hEa : 2 * E < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellJ L B u c n0) σ (38 * d + 18 + (10 + (32 + (8 * E + 9)))) (fun σ' =>
      σ'.sc c = ((I.Rb : ℤ) : ℝ) ∧ σ'.nat (n0 + 8) = I.j ∧ σ'.nat (n0 + 9) = Nat.clog 2 I.Rb ∧
      σ'.nat (n0 + 10) = I.lam ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => c ≤ y) (fun j => n0 + 8 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ σ') := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, hsDf, -, -, hsrn, hsrd, hsen, hsed, -, -, -, -⟩ := hB'
  have hin' := hin
  obtain ⟨-, -, -, e_Df, -, -, e_rn, e_rd, e_en, e_ed, -, -, -, -⟩ := hin'
  have hb := ellJ_bounds I hd hr he
  have hj := ellJ_eq I hr he
  dsimp only at hb hj
  obtain ⟨bT, bF0, bF, bLn, bLd0, bLd, bT1, bT2, bD1, bNx0, bNx, bDx0, bDx, bX0, bX⟩ := hb
  have hσE : ellSz I ≤ E := by omega
  have bRb : |(I.Rb : ℤ)| ≤ 2 ^ E := by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast (ellRb_lt I).le.trans (pow_le_pow_right₀ (by norm_num) hσE)
  have b_rn : |(I.r.num : ℤ)| ≤ 2 ^ E := (abs_le_sz (ellMx_le I).2.2.2.2.2.2.2.2.2.2.1).trans
    (pow_le_pow_right₀ (by norm_num) hσE)
  have b_rd : |(I.r.den : ℤ)| ≤ 2 ^ E := (abs_le_sz' (ellMx_le I).2.2.2.2.2.2.2.2.2.2.2.1).trans
    (pow_le_pow_right₀ (by norm_num) hσE)
  have b_en : |(I.e.num : ℤ)| ≤ 2 ^ E := (abs_le_sz (ellMx_le I).2.2.2.2.2.2.2.2.2.2.2.2.1).trans
    (pow_le_pow_right₀ (by norm_num) hσE)
  have b_ed : |(I.e.den : ℤ)| ≤ 2 ^ E := (abs_le_sz' (ellMx_le I).2.2.2.2.2.2.2.2.2.2.2.2.2).trans
    (pow_le_pow_right₀ (by norm_num) hσE)
  refine XV.seq (XV.ellJa (E := E) hL hB hu hc hS hn hN hin hz h1 hone hR (by omega) (by omega))
    fun σ1 ⟨r1, t1, f1, d1, G1⟩ => ?_
  have k1 : ∀ y, y < c → σ1.sc y = σ.sc y := fun y hy => G1.2.1 y (by omega)
  refine XV.seq (XV.ellJb hL (B := B) (E := E) (by omega) hc hS (by rw [k1 _ (by omega), hz])
    (by rw [k1 _ (by omega), h1]) r1 t1 f1 (by rw [k1 _ (by omega), e_Df]) bRb (abs_le_pow_of bT (by omega))
    (by rw [abs_of_nonneg bF0]; exact bF.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
    (ellDf_le hσE) (by omega)) fun σ2 ⟨l2, g2, d2, F2⟩ => ?_
  have k2 : ∀ y, y < c → σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 _ (by omega), k1 y hy]
  have r2 : σ2.sc c = ((I.Rb : ℤ) : ℝ) := by rw [F2.2.1 _ (by omega), r1]
  refine XV.seq (XV.ellJc hL (B := B) (E := E) (Rb := (I.Rb : ℤ)) ⟨by omega, by omega, by omega, by omega⟩ hc hS
    (by rw [k2 _ (by omega), hz]) (by rw [k2 _ (by omega), h1]) r2 l2 g2 (by rw [k2 _ (by omega), e_en])
    (by rw [k2 _ (by omega), e_ed, Int.cast_natCast]) (by rw [k2 _ (by omega), e_rn])
    (by rw [k2 _ (by omega), e_rd, Int.cast_natCast]) bRb (abs_le_pow_of bLn (by omega))
    (by rw [abs_of_pos bLd0]; exact bLd.trans (pow_le_pow_right₀ (by norm_num) (by omega))) b_en b_ed b_rn b_rd
    (abs_le_pow_of bT1 (by omega)) (abs_le_pow_of bD1 (by omega))
    (by unfold jNx; rw [abs_of_pos bNx0]; exact bNx.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
    (by unfold jDx; rw [abs_of_pos bDx0]; exact bDx.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
    hℓ) fun σ3 ⟨x3, d3, F3⟩ => ?_
  have r3 : σ3.sc c = ((I.Rb : ℤ) : ℝ) := by rw [F3.2.1 _ (by omega), r2]
  have o3 : σ3.nat (n0 + 4) = 1 := by
    rw [F3.1 _ not_false, F2.1 _ not_false, G1.1 _ (by omega), hone]
  refine XV.mono (XV.ellJd hL (G := E) (by omega) (by omega) x3 r3 (by unfold jNx jDx; exact bX0) (by positivity)
    (by unfold jNx jDx; exact bX.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
    (by exact_mod_cast (ellRb_lt I).le.trans (pow_le_pow_right₀ (by norm_num) hσE)) o3 hEa (by omega))
    le_rfl fun σ4 ⟨j4, c4, l4, d4, F4⟩ => ?_
  have hjj : Nat.clog 2 ((jNx (I.Rb : ℤ) (if I.Df = 0 then I.P.trace * I.Rb else I.P.trace * I.Rb * I.Df +
      ∑ i, |I.f i|) (if I.Df = 0 then 1 else (I.Df : ℤ)) I.e.num I.e.den I.r.num I.r.den +
      jDx (I.Rb : ℤ) (if I.Df = 0 then I.P.trace * I.Rb else I.P.trace * I.Rb * I.Df + ∑ i, |I.f i|)
        (if I.Df = 0 then 1 else (I.Df : ℤ)) I.e.num I.e.den I.r.num I.r.den - 1) /
      jDx (I.Rb : ℤ) (if I.Df = 0 then I.P.trace * I.Rb else I.P.trace * I.Rb * I.Df + ∑ i, |I.f i|)
        (if I.Df = 0 then 1 else (I.Df : ℤ)) I.e.num I.e.den I.r.num I.r.den).toNat = I.j := by
    rw [hj.2.2]; unfold jNx jDx; rfl
  refine ⟨by rw [F4.2.1 _ (by omega), r3], by rw [j4, hjj], by rw [c4, Int.toNat_natCast],
    by rw [l4, Int.toNat_natCast, hjj]; rfl, by rw [d4, d3, d2, d1], ?_⟩
  have G2 : FrameA (fun y => c ≤ y) (fun j => n0 + 8 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ1 σ2 :=
    FrameA.ofP (F2.mono (fun y h => by omega) (fun _ h => h.elim))
  have G3 : FrameA (fun y => c ≤ y) (fun j => n0 + 8 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ2 σ3 :=
    FrameA.ofP (F3.mono (fun y h => by omega) (fun _ h => h.elim))
  have G4 : FrameA (fun y => c ≤ y) (fun j => n0 + 8 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ3 σ4 :=
    FrameA.ofP (F4.mono (fun y h => by omega) (fun j h => by omega))
  exact (((G1.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h)).trans G2).trans G3).trans G4

end AdversarialBco.Bit.Transfer
