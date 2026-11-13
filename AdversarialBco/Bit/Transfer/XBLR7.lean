/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR4
public import AdversarialBco.Bit.Transfer.XBLSetupSL
public import AdversarialBco.Bit.Transfer.XBLRq

@[expose] public section

/-!
# BL's round on the machine: R5 YOBS and the scalars of R7 FACTOR

After the reading (`XV.r24`), the straight line `sl1St` (region from slot `45`) computes `Ŷ` (R5, `ieY`), `κ̂Ŷ`,
`F Q`, `a_N = F Q - κ̂Ŷ`, `G²`, `q_N = a_N G² + κ̂Ŷ (Γ·Γ)`, the test values `F Q - 2 a_N` (positive iff `a < 1/2`),
`F Q G²` and `F Q G² - 2 q_N` (positive iff `q < 1/2`), with `F = 2^pF`, `Q = 2^p`, `G = 2^(2 p_B)`; `Γ·Γ` in slot `40`
first (`xdot`), the constants `1, 2, 4` in the slots `41, 42, 43`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The straight line -/

/-- The value of step `j` of the first line (the slot `45 + j`). -/
abbrev qv (j : ℕ) : IE := .sc (45 + j)

/-- The slot of `Γ·Γ`. -/
abbrev sGG : ℕ := 40

/-- R5 and the scalars of R7. -/
def sl1St : List SStep :=
  [ .ie (ieY s2p s2pF s2g sPtN sPtD sObs sZeta sEps),
    .ie (.op .mul (.sc sKapc) (qv 0)),
    .ie (.op .mul (.sc s2pF) (.sc s2p)),
    .ie (.op .sub (qv 2) (qv 1)),
    .ie (.op .mul (.sc s2g) (.sc s2g)),
    .ie (.op .add (.op .mul (qv 3) (qv 4)) (.op .mul (qv 1) (.sc sGG))),
    .ie (.op .sub (qv 2) (.op .add (qv 3) (qv 3))),
    .ie (.op .mul (qv 2) (qv 4)),
    .ie (.op .sub (qv 7) (.op .add (qv 5) (qv 5))) ]

/-- The input slots of the first line. -/
def sl1Ins : List ℕ := [s2p, s2pF, s2g, sEps, sKapc, sZeta, sPtN, sPtD, sGG, sObs]

/-- The pairs of the inputs: `Γ·Γ` below `2^(3G)`, the others below `2^G`. -/
def sl1In (y : ℕ) : ℕ × ℕ := if y = sGG then (3, 0) else (1, 0)

/-- The pairs of the steps. -/
def sl1Et (j : ℕ) : ℕ × ℕ := [(5, 7), (6, 7), (2, 0), (6, 8), (2, 0), (9, 9), (6, 10), (4, 0), (9, 11)].getD j (0, 0)

/-- The largest pair. -/
def sl1T : ℕ × ℕ := (9, 11)

/-- The cells of the first line: the region from `45`, the scratch from `256`, `0, 1, 2, 4` in the slots `0, 41, 42,
43`, the scratch registers `19`, `20`, `1` in the register `rOne`. -/
def sl1C : SLC := ⟨45, 256, sZ, 41, 42, 43, 19, 20, rOne⟩

theorem sl1St_length : sl1St.length = 9 := rfl

theorem sl1St_chk : SL.chk 45 sl1Ins sl1In sl1Et sl1T 112 sl1St = true := by decide

/-- The inputs of the first line. -/
def sl1I (Q F G eN kN gz pN pD GG obs : ℤ) : ℕ → ℤ := fun y =>
  if y = s2p then Q else if y = s2pF then F else if y = s2g then G else if y = sEps then eN else
  if y = sKapc then kN else if y = sZeta then gz else if y = sPtN then pN else if y = sPtD then pD else
  if y = sGG then GG else if y = sObs then obs else 0

section Values

variable (Q F G eN kN gz pN pD GG obs : ℤ)

/-- The value of step `k`. -/
abbrev v1 (k : ℕ) : ℤ := SL.val sl1St 45 (sl1I Q F G eN kN gz pN pD GG obs) k

theorem v1_c (k : ℕ) : v1 Q F G eN kN gz pN pD GG obs k =
    (sl1St.getD k (.cst 0)).sem 45 (sl1I Q F G eN kN gz pN pD GG obs)
      (fun j => if j < k then v1 Q F G eN kN gz pN pD GG obs j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the first line unfolded. -/
macro "v1s" : tactic => `(tactic| (rw [v1_c]; simp only [sl1St, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, qv, sl1I, ieY, ieYU, ieYV, s2p, s2pF, s2g, sEps, sKapc, sZeta, sPtN, sPtD, sGG, sObs,
  Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]))

theorem v1_0 : v1 Q F G eN kN gz pN pD GG obs 0 = yHat Q F G pN pD obs gz eN := by
  v1s; unfold yHat yU yV; ring_nf

theorem v1_1 : v1 Q F G eN kN gz pN pD GG obs 1 = kN * yHat Q F G pN pD obs gz eN := by
  v1s; rw [v1_0]

theorem v1_2 : v1 Q F G eN kN gz pN pD GG obs 2 = F * Q := by v1s

theorem v1_3 : v1 Q F G eN kN gz pN pD GG obs 3 = F * Q - kN * yHat Q F G pN pD obs gz eN := by
  v1s; rw [v1_1, v1_2]

theorem v1_4 : v1 Q F G eN kN gz pN pD GG obs 4 = G * G := by v1s

theorem v1_5 : v1 Q F G eN kN gz pN pD GG obs 5 =
    (F * Q - kN * yHat Q F G pN pD obs gz eN) * (G * G) + kN * yHat Q F G pN pD obs gz eN * GG := by
  v1s; rw [v1_3, v1_4, v1_1]

theorem v1_6 : v1 Q F G eN kN gz pN pD GG obs 6 =
    F * Q - 2 * (F * Q - kN * yHat Q F G pN pD obs gz eN) := by
  v1s; rw [v1_2, v1_3]; ring

theorem v1_7 : v1 Q F G eN kN gz pN pD GG obs 7 = F * Q * (G * G) := by
  v1s; rw [v1_2, v1_4]

theorem v1_8 : v1 Q F G eN kN gz pN pD GG obs 8 =
    F * Q * (G * G) - 2 * ((F * Q - kN * yHat Q F G pN pD obs gz eN) * (G * G) +
      kN * yHat Q F G pN pD obs gz eN * GG) := by
  v1s; rw [v1_7, v1_5]; ring

end Values

/-! ## The run of R5 and R7's scalars -/

/-- `Γ·Γ` into slot `40`, the constants `1, 2, 4`, then the first line. -/
def xR57 (L : Layout) : XCmd :=
  .seq (xdot L sZ sGG tR aGam aGam rD1 rK rD rOne)
    (.seq (toX (VL.sconst L 41 1)) (.seq (toX (VL.sconst L 42 2)) (.seq (toX (VL.sconst L 43 4))
      (SL.code L sl1C sl1St))))

/-- The units of `xR57`. -/
def r57Units (d Gu : ℕ) : ℕ := (d * 10 + 5) + (1 + (1 + (1 + ev Gu (SL.unitsP sl1Et sl1St))))

/-- The cells that `xR57` changes. -/
def S57 (y : ℕ) : Prop := (sGG ≤ y ∧ y < 54) ∨ tR ≤ y
def N57 (j : ℕ) : Prop := j = 19 ∨ j = 20 ∨ j = rD1 ∨ j = rK

/-- `romega` with the cells of R5 to R7 unfolded. -/
macro "r7omega" : tactic => `(tactic| ((try simp only [sGG, sObs, S57, N57] at *) <;> romega))

theorem sl1C_ok {L : Layout} (hlay : BLLay L) : sl1C.OK L 112 := by
  obtain ⟨hS, hN, -⟩ := hlay
  simp only [oE, rEE] at hS hN
  exact ⟨by simp only [sl1C]; omega, by simp only [sl1C]; omega, by simp only [sl1C]; omega,
    by simp only [sl1C, rOne]; omega, by simp only [sl1C]; omega, by simp only [sl1C, rOne]; omega,
    by simp only [sl1C, rOne]; omega, by simp only [sl1C, sZ]; omega, by simp only [sl1C]; omega,
    by simp only [sl1C]; omega, by simp only [sl1C]; omega, by simp [sl1C, sZ], by simp only [sl1C]; omega⟩

set_option maxHeartbeats 800000 in
/-- **R5 and R7's scalars on the machine**: from the inputs in their slots (`2^p`, `2^pF`, `G`, `ε̂`, `κ̂`, the dither
`gz`, the pair `pN/pD`, the reading) and `Γ` in `aGam`, the slots `45 + k` hold the values `v1 .. k` of the first line
and slot `40` holds `Γ·Γ`; the slots `41, 42, 43` hold `1, 2, 4`. -/
theorem XV.r57 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q F G eN kN gz pN pD obs : ℤ} {Γ : Fin d → ℤ} {Gu E1 : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (eQ : σ.sc s2p = Q) (eF : σ.sc s2pF = F) (eG : σ.sc s2g = G) (eE : σ.sc sEps = eN) (eK : σ.sc sKapc = kN)
    (eZ : σ.sc sZeta = gz) (eN' : σ.sc sPtN = pN) (eD : σ.sc sPtD = pD) (eO : σ.sc sObs = obs)
    (eΓ : ∀ i : Fin d, σ.arr aGam i = Γ i)
    (bQ : |Q| ≤ 2 ^ Gu) (bF : |F| ≤ 2 ^ Gu) (bG : |G| ≤ 2 ^ Gu) (bE : |eN| ≤ 2 ^ Gu) (bK : |kN| ≤ 2 ^ Gu)
    (bZ : |gz| ≤ 2 ^ Gu) (bN : |pN| ≤ 2 ^ Gu) (bD : |pD| ≤ 2 ^ Gu) (bO : |obs| ≤ 2 ^ Gu)
    (bΓ : ∀ i, |Γ i| ≤ 2 ^ E1) (hdE : (d : ℤ) * 2 ^ (2 * E1) ≤ 2 ^ (3 * Gu))
    (hE1 : 2 * E1 < ℓ) (hd1 : d * 2 ^ (2 * E1) < 2 ^ ℓ) (hT : 9 * Gu + 11 < ℓ) (hTa : 9 * Gu + 11 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR57 L) σ (r57Units d Gu) (fun σ' =>
      (∀ k < 9, σ'.sc (45 + k) = v1 Q F G eN kN gz pN pD (Γ ⬝ᵥ Γ) obs k) ∧ σ'.sc sGG = ((Γ ⬝ᵥ Γ : ℤ) : ℝ) ∧
      (σ'.sc 41 = 1 ∧ σ'.sc 42 = 2 ∧ σ'.sc 43 = 4) ∧ σ'.draws = σ.draws ∧ FrameA S57 N57 (fun _ _ => False) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  -- Γ·Γ
  refine XV.seq (XV.dot (E := E1) hL (σ := σ) (z := sZ) (r := sGG) (t := tR) (ax := aGam) (ay := aGam) (nr := rD1)
    (nk := rK) (nd := rD) (none := rOne) (x := Γ) (y := Γ) (by r7omega) (by r7omega) (by r7omega) (by r7omega) hz
    (by r7omega) (by r7omega) (by r7omega) (by r7omega) (by r7omega) (by r7omega) (by decide) hD h1 eΓ eΓ bΓ bΓ hE1 hd1)
    fun σ1 ⟨g1, d1, F1⟩ => ?_
  have s1 : ∀ y, y ≠ sGG → y < tR → σ1.sc y = σ.sc y := fun y h h' => F1.2.1 y (by omega)
  have n1 : ∀ j, j ≠ rD1 → j ≠ rK → σ1.nat j = σ.nat j := fun j h h' => F1.1 j (by omega)
  have hℓ0 : ∀ {a : ℕ}, a < ℓ → |((2 : ℤ) ^ a : ℝ)| < 2 ^ ℓ := fun h => by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast pow_lt_pow_right₀ (by norm_num) h
  have c1 : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by simpa using hℓ0 (a := 0) (by omega)
  have c2 : |((2 : ℚ) : ℝ)| < 2 ^ ℓ := by simpa using hℓ0 (a := 1) (by omega)
  have c4 : |((4 : ℚ) : ℝ)| < 2 ^ ℓ := by
    have := hℓ0 (a := 2) (by omega); norm_num at this ⊢; exact this
  refine XV.seq (XV.sconst hL (x := 41) (by r7omega) 1 rfl c1) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.sconst hL (x := 42) (by r7omega) 2 rfl c2) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.sconst hL (x := 43) (by r7omega) 4 rfl c4) fun σ4 e4 => ?_
  subst e4
  set σ4 := ((σ1.setSc 41 ((1 : ℚ) : ℝ)).setSc 42 ((2 : ℚ) : ℝ)).setSc 43 ((4 : ℚ) : ℝ) with hσ4
  have s4 : ∀ y, y ≠ 41 → y ≠ 42 → y ≠ 43 → σ4.sc y = σ1.sc y := fun y a b c => by
    simp only [hσ4, Env.setSc_sc]; rw [if_neg c, if_neg b, if_neg a]
  have n4 : σ4.nat = σ1.nat := by simp only [hσ4, Env.setSc_nat]
  have hin : ∀ y ∈ sl1Ins, σ4.sc y = sl1I Q F G eN kN gz pN pD (Γ ⬝ᵥ Γ) obs y := by
    intro y hy
    simp only [sl1Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [s4 _ (by decide) (by decide) (by decide), g1]; simp [sl1I])
      | (rw [s4 _ (by decide) (by decide) (by decide), s1 _ (by decide) (by decide)]
         simp [sl1I, eQ, eF, eG, eE, eK, eZ, eN', eD, eO])
  have bGG : |Γ ⬝ᵥ Γ| ≤ 2 ^ (3 * Gu) := by
    calc |Γ ⬝ᵥ Γ| ≤ ∑ k, |Γ k * Γ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, (2 ^ E1 * 2 ^ E1 : ℤ) := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_mul (bΓ k) (bΓ k) (abs_nonneg _) (by positivity)
      _ = (d : ℤ) * 2 ^ (2 * E1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ 2 ^ (3 * Gu) := hdE
  have hinB : ∀ y ∈ sl1Ins, |sl1I Q F G eN kN gz pN pD (Γ ⬝ᵥ Γ) obs y| ≤ 2 ^ ev Gu (sl1In y) := by
    intro y hy
    simp only [sl1Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sl1I, sl1In, ev, bQ, bF, bG, bE, bK, bZ, bN, bD, bO, bGG]
  refine XV.mono (XV.sl hL (sl1C_ok hlay) sl1St_chk (fun k hk => by
      simp only [sl1St_length] at hk; interval_cases k <;> trivial)
    (by simp [sl1C, sl1St_length]) (by simp only [ev, sl1T]; omega) (by simp only [ev, sl1T]; omega) hinB
    (σ := σ4) hin (by simp only [sl1C]; rw [s4 _ (by decide) (by decide) (by decide), s1 _ (by decide) (by decide), hz])
    (by simp [sl1C, hσ4]) (by simp [sl1C, hσ4]) (by simp [sl1C, hσ4])
    (by simp only [sl1C]; rw [n4, n1 _ (by decide) (by decide), h1])) le_rfl fun σ5 ⟨v5, d5, F5⟩ => ?_
  refine ⟨fun k hk => v5 k (by simpa [sl1St_length] using hk), ?_, ?_, ?_, ?_⟩
  · rw [F5.2.1 _ (by simp only [sl1C, sl1St_length, sGG]; omega)]
    rw [s4 _ (by decide) (by decide) (by decide), g1]
  · refine ⟨?_, ?_, ?_⟩ <;> rw [F5.2.1 _ (by simp only [sl1C, sl1St_length]; omega)] <;> simp [hσ4]
  · rw [d5]; simp only [hσ4, Env.setSc_draws]; exact d1
  · refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k _ => ?_, ?_, ?_⟩
    · simp only [N57, not_or] at hj
      rw [F5.1 j (by simp only [sl1C]; omega), n4, F1.1 j (by simp only [rD1, rK] at hj ⊢; omega)]
    · simp only [S57, sGG, tR, not_or, not_and, not_le] at hy
      rw [F5.2.1 y (by simp only [sl1C, sl1St_length]; omega),
        s4 _ (by omega) (by omega) (by omega), F1.2.1 y (by simp only [tR, sGG] at hy ⊢; omega)]
    · rw [F5.2.2.1]; simp only [hσ4, Env.setSc_arr]; exact F1.2.2.1 b k (by simp)
    · rw [F5.2.2.2.1]; simp only [hσ4, Env.setSc_rounds]; exact F1.2.2.2.1
    · rw [F5.2.2.2.2]; simp only [hσ4, Env.setSc_pts]; exact F1.2.2.2.2

/-! ## The values in BL's terms -/

/-- **R5 and R7's scalars in BL's terms**: with `pt = pN/pD`, `ζ = gz/2^g/2`, `ξ = Γ/2^g`, `ε'` and `κ_c'` on the grid
`2^{-pF}`, `ε' > 0`: `Y' = v₀/2^p`, `c = κ_c' Y' = (κ̂/F)(v₀/Q)`, `a = v₃/v₂`, `q = v₅/v₇`, and the tests `a < 1/2`,
`q < 1/2` are `0 < v₆`, `0 < v₈`. -/
theorem r57_pure (P : Par) (pt ζ : ℚ) (ξ : Fin d → ℚ) (obs pN pD gz : ℤ) (Γ : Fin d → ℤ) (g : ℕ) (hD : 0 < pD)
    (hpt : pt = (pN : ℚ) / pD) (hζ : ζ = (gz : ℚ) / 2 ^ g / 2) (hξ : ξ = fun i => (Γ i : ℚ) / 2 ^ g)
    (he : OnG P.pF P.eps) (he0 : 0 < P.eps) (hk : OnG P.pF P.kapc) :
    rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps) =
        (yHat (2 ^ P.p) (2 ^ P.pF) (2 ^ g) pN pD obs gz (qn P.pF P.eps) : ℚ) / 2 ^ P.p ∧
      P.kapc * rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps) =
        (qn P.pF P.kapc : ℚ) / ((2 ^ P.pF : ℤ) : ℚ) *
          ((yHat (2 ^ P.p) (2 ^ P.pF) (2 ^ g) pN pD obs gz (qn P.pF P.eps) : ℚ) / ((2 ^ P.p : ℤ) : ℚ)) := by
  have hY := qn_Y P.p P.pF g pt ζ P.eps obs pN pD gz hD hpt hζ he he0
  have hr : rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps) =
      (qn P.p (rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)) : ℚ) / 2 ^ P.p := by
    rw [qn_rnd]; rfl
  rw [hY] at hr
  refine ⟨hr, ?_⟩
  rw [hr]
  conv_lhs => rw [eq_qn_div P.pF hk]
  push_cast
  ring

/-- The tests of R7 in BL's terms (`r7_aq` on the values of the first line). -/
theorem r57_tests (F Q G kN yh : ℤ) (Γ : Fin d → ℤ) (hF : 0 < F) (hQ : 0 < Q) (hG : 0 < G) :
    (1 - (kN : ℚ) / F * ((yh : ℚ) / Q) = ((F * Q - kN * yh : ℤ) : ℚ) / ((F * Q : ℤ) : ℚ)) ∧
      (1 - (kN : ℚ) / F * ((yh : ℚ) / Q) + (kN : ℚ) / F * ((yh : ℚ) / Q) *
          ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) =
        (((F * Q - kN * yh) * (G * G) + kN * yh * (Γ ⬝ᵥ Γ) : ℤ) : ℚ) / ((F * Q * (G * G) : ℤ) : ℚ)) ∧
      (1 - (kN : ℚ) / F * ((yh : ℚ) / Q) < 1 / 2 ↔ 0 < F * Q - 2 * (F * Q - kN * yh)) ∧
      (1 - (kN : ℚ) / F * ((yh : ℚ) / Q) + (kN : ℚ) / F * ((yh : ℚ) / Q) *
          ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G) < 1 / 2 ↔
        0 < F * Q * (G * G) - 2 * ((F * Q - kN * yh) * (G * G) + kN * yh * (Γ ⬝ᵥ Γ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := r7_aq F Q G kN yh Γ hF hQ hG
  refine ⟨h1, by rw [h2, ← sq], by rw [h3]; constructor <;> intro h <;> linarith, ?_⟩
  rw [h4, ← sq]
  constructor <;> intro h <;> linarith

end AdversarialBco.Bit.Transfer.BLM
