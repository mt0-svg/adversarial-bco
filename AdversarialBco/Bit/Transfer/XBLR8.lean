/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR7
public import AdversarialBco.Bit.Transfer.XBLRr
public import AdversarialBco.Bit.Transfer.XBLLoop

@[expose] public section

/-!
# BL's round on the machine: the square roots and the scalars of R7, R13

Once the tests of R7 fail (`a ≥ 1/2`, `q ≥ 1/2`), the straight line `sl2St` (region from slot `70`) computes, from the
values of the first line: `F q_N`, `η̂ Ŷ ν̂ G²` and `ŝ5` (R13's `s5`, slot `72`), the square roots `ŝ1` (slot `74`),
`ŝ3` (slot `76`), `r̂q` (slot `78`), then `ŝ2` (slot `81`) and `ŝ4` (slot `83`) of R7.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The straight line -/

/-- The value of step `j` of the second line (the slot `70 + j`). -/
abbrev qw (j : ℕ) : IE := .sc (70 + j)

/-- `rnd_p (U/V)` on the grid: `(2 U 2^p + V) / (2 V)`. -/
def rndE (U V : IE) : IE :=
  .ediv (.op .add (.op .add (.op .mul U (.sc s2p)) (.op .mul U (.sc s2p))) V) (.op .add V V)

/-- The square roots of R7 and the scalars `s2`, `s4`, `s5`. -/
def sl2St : List SStep :=
  [ .ie (.op .mul (.sc s2pF) (qv 5)),
    .ie (.op .mul (.op .mul (.op .mul (.sc sEta) (qv 0)) (.sc sNu)) (qv 4)),
    .ie (rndE (qw 1) (qw 0)),
    .ie (.ediv (.op .mul (.op .mul (qv 2) (.sc s2p)) (.sc s2p)) (qv 3)),
    .sq 3,
    .ie (.ediv (.op .mul (.op .mul (qv 3) (.sc s2p)) (.sc s2p)) (qv 2)),
    .sq 5,
    .ie (.ediv (.op .mul (.op .mul (qv 5) (.sc s2p)) (.sc s2p)) (qv 7)),
    .sq 7,
    .ie (.op .mul (.op .mul (.op .mul (.sc s2pF) (qw 6)) (qw 8)) (.op .add (qw 6) (qw 8))),
    .ie (.op .mul (.op .mul (qv 1) (.sc s2p)) (.sc s2p)),
    .ie (rndE (qw 10) (qw 9)),
    .ie (.op .mul (.sc s2pF) (.op .add (qw 6) (qw 8))),
    .ie (rndE (qv 1) (qw 12)) ]

/-- The input slots of the second line. -/
def sl2Ins : List ℕ := [s2p, s2pF, sEta, sNu, 45, 46, 47, 48, 49, 50, 52]

/-- The pairs of the inputs: the values of the first line, `(1, 0)` for the parameters. -/
def sl2In (y : ℕ) : ℕ × ℕ := if 45 ≤ y then sl1Et (y - 45) else (1, 0)

/-- The pairs of the steps. -/
def sl2Et (j : ℕ) : ℕ × ℕ :=
  [(10, 9), (9, 7), (10, 10), (4, 0), (4, 0), (8, 8), (8, 8), (11, 9), (11, 9), (31, 27), (8, 7), (31, 28),
    (12, 10), (12, 11)].getD j (0, 0)

/-- The largest pair. -/
def sl2T : ℕ × ℕ := (31, 28)

/-- The cells of the second line: the region from `70`, the rest as the first line. -/
def sl2C : SLC := ⟨70, 256, sZ, 41, 42, 43, 19, 20, rOne⟩

theorem sl2St_length : sl2St.length = 14 := rfl

theorem sl2St_chk : SL.chk 70 sl2Ins sl2In sl2Et sl2T 12 sl2St = true := by decide

/-- The inputs of the second line: `2^p`, `2^pF`, `η̂`, `ν̂` and the values `v` of the first line. -/
def sl2I (Q F eh nh : ℤ) (v : ℕ → ℤ) : ℕ → ℤ := fun y =>
  if y = s2p then Q else if y = s2pF then F else if y = sEta then eh else if y = sNu then nh else
  if 45 ≤ y then v (y - 45) else 0

section Values

variable (Q F eh nh : ℤ) (v : ℕ → ℤ)

/-- The value of step `k`. -/
abbrev w2 (k : ℕ) : ℤ := SL.val sl2St 70 (sl2I Q F eh nh v) k

theorem w2_c (k : ℕ) : w2 Q F eh nh v k =
    (sl2St.getD k (.cst 0)).sem 70 (sl2I Q F eh nh v) (fun j => if j < k then w2 Q F eh nh v j else 0) :=
  SL.val_eq _ _ _ _

/-- One step of the second line unfolded. -/
macro "w2s" : tactic => `(tactic| (rw [w2_c]; simp only [sl2St, List.getD_cons_succ, List.getD_cons_zero,
  SStep.sem, slZ, qv, qw, rndE, sl2I, s2p, s2pF, sEta, sNu, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
  Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte]))

theorem w2_0 : w2 Q F eh nh v 0 = F * v 5 := by w2s
theorem w2_1 : w2 Q F eh nh v 1 = eh * v 0 * nh * v 4 := by w2s
theorem w2_2 : w2 Q F eh nh v 2 = (2 * (eh * v 0 * nh * v 4) * Q + F * v 5) / (2 * (F * v 5)) := by
  w2s; rw [w2_1, w2_0]; ring_nf
theorem w2_3 : w2 Q F eh nh v 3 = v 2 * Q * Q / v 3 := by w2s
theorem w2_4 : w2 Q F eh nh v 4 = Nat.sqrt (v 2 * Q * Q / v 3).toNat := by w2s; rw [w2_3]
theorem w2_5 : w2 Q F eh nh v 5 = v 3 * Q * Q / v 2 := by w2s
theorem w2_6 : w2 Q F eh nh v 6 = Nat.sqrt (v 3 * Q * Q / v 2).toNat := by w2s; rw [w2_5]
theorem w2_7 : w2 Q F eh nh v 7 = v 5 * Q * Q / v 7 := by w2s
theorem w2_8 : w2 Q F eh nh v 8 = Nat.sqrt (v 5 * Q * Q / v 7).toNat := by w2s; rw [w2_7]
theorem w2_9 : w2 Q F eh nh v 9 = F * w2 Q F eh nh v 6 * w2 Q F eh nh v 8 *
    (w2 Q F eh nh v 6 + w2 Q F eh nh v 8) := by w2s
theorem w2_10 : w2 Q F eh nh v 10 = v 1 * Q * Q := by w2s
theorem w2_11 : w2 Q F eh nh v 11 =
    (2 * (v 1 * Q * Q) * Q + w2 Q F eh nh v 9) / (2 * w2 Q F eh nh v 9) := by
  w2s; rw [w2_10]; ring_nf
theorem w2_12 : w2 Q F eh nh v 12 = F * (w2 Q F eh nh v 6 + w2 Q F eh nh v 8) := by w2s
theorem w2_13 : w2 Q F eh nh v 13 =
    (2 * v 1 * Q + w2 Q F eh nh v 12) / (2 * w2 Q F eh nh v 12) := by
  w2s; ring_nf

end Values

/-! ## The bounds of the first line -/

/-- The values of the first line are bounded by their pairs. -/
theorem v1_bound {Q F G eN kN gz pN pD GG obs : ℤ} {Gu : ℕ} (bQ : |Q| ≤ 2 ^ Gu) (bF : |F| ≤ 2 ^ Gu)
    (bG : |G| ≤ 2 ^ Gu) (bE : |eN| ≤ 2 ^ Gu) (bK : |kN| ≤ 2 ^ Gu) (bZ : |gz| ≤ 2 ^ Gu) (bN : |pN| ≤ 2 ^ Gu)
    (bD : |pD| ≤ 2 ^ Gu) (bO : |obs| ≤ 2 ^ Gu) (bGG : |GG| ≤ 2 ^ (3 * Gu)) :
    ∀ k < 9, |v1 Q F G eN kN gz pN pD GG obs k| ≤ 2 ^ ev Gu (sl1Et k) := by
  have hinB : ∀ y ∈ sl1Ins, |sl1I Q F G eN kN gz pN pD GG obs y| ≤ 2 ^ ev Gu (sl1In y) := by
    intro y hy
    simp only [sl1Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sl1I, sl1In, ev, bQ, bF, bG, bE, bK, bZ, bN, bD, bO, bGG]
  intro k hk
  exact SL.val_bound sl1St 45 _ sl1Ins sl1In sl1Et sl1T 112 Gu (SL.chk_get sl1St_chk).2
    (fun k hk => by simp only [sl1St_length] at hk; interval_cases k <;> trivial) hinB k
    (by rw [sl1St_length]; exact hk)

/-! ## The run of the second line -/

/-- The second line. -/
def xR8s (L : Layout) : XCmd := SL.code L sl2C sl2St

/-- The cells that `xR8s` changes. -/
def S8s (y : ℕ) : Prop := (70 ≤ y ∧ y < 84) ∨ tR ≤ y
def N8s (j : ℕ) : Prop := j = 19 ∨ j = 20

theorem sl2C_ok {L : Layout} (hlay : BLLay L) : sl2C.OK L 12 := by
  obtain ⟨hS, hN, -⟩ := hlay
  simp only [oE, rEE] at hS hN
  exact ⟨by simp only [sl2C]; omega, by simp only [sl2C]; omega, by simp only [sl2C]; omega,
    by simp only [sl2C, rOne]; omega, by simp only [sl2C]; omega, by simp only [sl2C, rOne]; omega,
    by simp only [sl2C, rOne]; omega, by simp only [sl2C, sZ]; omega, by simp only [sl2C]; omega,
    by simp only [sl2C]; omega, by simp only [sl2C]; omega, by simp [sl2C, sZ], by simp only [sl2C]; omega⟩

set_option maxHeartbeats 800000 in
/-- **R7's square roots and R13's `s5` on the machine**: from `2^p`, `2^pF`, `η̂`, `ν̂` in their slots and the values `v`
of the first line in the slots `45 + k`, the slots `70 + k` hold the values `w2 .. k` of the second line. -/
theorem XV.r8s {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q F eh nh : ℤ} {v : ℕ → ℤ} {Gu : ℕ}
    (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2) (c4 : σ.sc 43 = 4)
    (eQ : σ.sc s2p = Q) (eF : σ.sc s2pF = F) (eE : σ.sc sEta = eh) (eN : σ.sc sNu = nh)
    (eV : ∀ k < 9, σ.sc (45 + k) = v k)
    (bQ : |Q| ≤ 2 ^ Gu) (bF : |F| ≤ 2 ^ Gu) (bE : |eh| ≤ 2 ^ Gu) (bN : |nh| ≤ 2 ^ Gu)
    (bV : ∀ k < 9, |v k| ≤ 2 ^ ev Gu (sl1Et k))
    (p3 : 0 ≤ w2 Q F eh nh v 3) (p5 : 0 ≤ w2 Q F eh nh v 5) (p7 : 0 ≤ w2 Q F eh nh v 7)
    (hT : 31 * Gu + 28 < ℓ) (hTa : 31 * Gu + 28 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR8s L) σ (ev Gu (SL.unitsP sl2Et sl2St)) (fun σ' =>
      (∀ k < 14, σ'.sc (70 + k) = w2 Q F eh nh v k) ∧ σ'.draws = σ.draws ∧
      FrameA S8s N8s (fun _ _ => False) σ σ') := by
  have hin : ∀ y ∈ sl2Ins, σ.sc y = sl2I Q F eh nh v y := by
    intro y hy
    simp only [sl2Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [sl2I, eQ]
    · simp [sl2I, eF]
    · simp [sl2I, eE]
    · simp [sl2I, eN]
    all_goals
      first
        | (have := eV 0 (by norm_num); simp only [Nat.add_zero] at this; rw [this]; simp [sl2I])
        | (have := eV 1 (by norm_num); rw [this]; simp [sl2I])
        | (have := eV 2 (by norm_num); rw [this]; simp [sl2I])
        | (have := eV 3 (by norm_num); rw [this]; simp [sl2I])
        | (have := eV 4 (by norm_num); rw [this]; simp [sl2I])
        | (have := eV 5 (by norm_num); rw [this]; simp [sl2I])
        | (have := eV 7 (by norm_num); rw [this]; simp [sl2I])
  have hinB : ∀ y ∈ sl2Ins, |sl2I Q F eh nh v y| ≤ 2 ^ ev Gu (sl2In y) := by
    intro y hy
    simp only [sl2Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [sl2I, sl2In, ev, s2p] using bQ
    · simpa [sl2I, sl2In, ev, s2p, s2pF] using bF
    · simpa [sl2I, sl2In, ev, s2p, s2pF, sEta] using bE
    · simpa [sl2I, sl2In, ev, s2p, s2pF, sEta, sNu] using bN
    · simpa [sl2I, sl2In] using bV 0 (by norm_num)
    · simpa [sl2I, sl2In] using bV 1 (by norm_num)
    · simpa [sl2I, sl2In] using bV 2 (by norm_num)
    · simpa [sl2I, sl2In] using bV 3 (by norm_num)
    · simpa [sl2I, sl2In] using bV 4 (by norm_num)
    · simpa [sl2I, sl2In] using bV 5 (by norm_num)
    · simpa [sl2I, sl2In] using bV 7 (by norm_num)
  refine XV.mono (XV.sl hL (sl2C_ok hlay) sl2St_chk (fun k hk => by
      simp only [sl2St_length] at hk
      interval_cases k
      all_goals trivial)
    (by simp [sl2C, sl2St_length]) (by simp only [ev, sl2T]; omega) (by simp only [ev, sl2T]; omega) hinB
    (σ := σ) hin (by simpa [sl2C] using hz) (by simpa [sl2C] using c1) (by simpa [sl2C] using c2)
    (by simpa [sl2C] using c4) (by simpa [sl2C] using h1)) le_rfl fun σ' ⟨v', d', F'⟩ => ?_
  refine ⟨fun k hk => v' k (by simpa [sl2St_length] using hk), d', ?_⟩
  refine (FrameA.ofP F').mono (fun y hy => ?_) (fun j hj => ?_) (fun _ _ h => h)
  · simp only [sl2C, sl2St_length] at hy
    simp only [S8s, tR]; omega
  · simpa [sl2C, N8s] using hj

/-! ## The values in BL's terms -/

/-- **R7's square roots, `s2`, `s4` and R13's `s5` in BL's terms**: with `Q = 2^p`, `p ≥ 1`, `c = (κ̂/F)(Ŷ/Q)`,
`a = 1 - c ≥ 1/2`, `q = a + c ξ·ξ ≥ 1/2` (`ξ = Γ/G`) and the values `v` of the first line, the points `s1, s3, r_q`
lie on the grid `2^{-p}`, and the numerators of `s1, s3, r_q, s2, s4` and of `rnd_p (η Y ν/q)` (`η = η̂/F`,
`ν = ν̂/F`) are the values of the second line; `ŝ3, r̂q > 0`. -/
theorem r8s_pure (p : ℕ) (hp : 1 ≤ p) (Q F G kN yh eh nh : ℤ) (Γ : Fin d → ℤ) (v : ℕ → ℤ)
    (hQ : Q = 2 ^ p) (hF : 0 < F) (hG : 0 < G)
    (h0 : v 0 = yh) (h1 : v 1 = kN * yh) (h2 : v 2 = F * Q) (h3 : v 3 = F * Q - kN * yh) (h4 : v 4 = G * G)
    (h5 : v 5 = (F * Q - kN * yh) * (G * G) + kN * yh * (Γ ⬝ᵥ Γ)) (h7 : v 7 = F * Q * (G * G))
    {c a q : ℚ} (hc : c = (kN : ℚ) / F * ((yh : ℚ) / Q)) (ha : a = 1 - c)
    (hq : q = a + c * ((fun i => (Γ i : ℚ) / G) ⬝ᵥ fun i => (Γ i : ℚ) / G))
    (ha2 : ¬ a < 1 / 2) (hq2 : ¬ q < 1 / 2) :
    (OnG p (sqrtDn p (1 / a)) ∧ qn p (sqrtDn p (1 / a)) = w2 Q F eh nh v 4) ∧
      (OnG p (sqrtDn p a) ∧ qn p (sqrtDn p a) = w2 Q F eh nh v 6) ∧
      (OnG p (sqrtDn p q) ∧ qn p (sqrtDn p q) = w2 Q F eh nh v 8) ∧
      qn p (rnd p (c / (sqrtDn p a * sqrtDn p q * (sqrtDn p a + sqrtDn p q)))) = w2 Q F eh nh v 11 ∧
      qn p (rnd p (c / (sqrtDn p a + sqrtDn p q))) = w2 Q F eh nh v 13 ∧
      qn p (rnd p ((eh : ℚ) / F * ((yh : ℚ) / Q) * ((nh : ℚ) / F) / q)) = w2 Q F eh nh v 2 ∧
      0 < w2 Q F eh nh v 6 ∧ 0 < w2 Q F eh nh v 8 ∧ v 2 ≤ 2 * v 3 ∧ v 7 ≤ 2 * v 5 := by
  have hQp : 0 < Q := by rw [hQ]; positivity
  have hQq : ((Q : ℤ) : ℚ) = (2 : ℚ) ^ p := by rw [hQ]; push_cast; rfl
  have h4p : (4 : ℤ) ^ p = Q * Q := by rw [hQ, ← mul_pow]; norm_num
  obtain ⟨e1, e2, e3, e4⟩ := r7_aq F Q G kN yh Γ hF hQp hG
  have haf : a = ((v 3 : ℤ) : ℚ) / ((v 2 : ℤ) : ℚ) := by rw [ha, hc, e1, h3, h2]
  have hqf : q = ((v 5 : ℤ) : ℚ) / ((v 7 : ℤ) : ℚ) := by
    rw [hq, ha, hc, e2, h5, h7, sq]
  have hv23 : v 2 ≤ 2 * v 3 := by
    rw [ha, hc, e3] at ha2
    rw [h2, h3]; linarith
  have hv75 : v 7 ≤ 2 * v 5 := by
    rw [hq, ha, hc, e4] at hq2
    rw [h7, h5]; rw [sq] at hq2; linarith
  have hv2 : 0 < v 2 := by rw [h2]; exact mul_pos hF hQp
  have hv7 : 0 < v 7 := by rw [h7]; exact mul_pos (mul_pos hF hQp) (mul_pos hG hG)
  have hv3 : 0 < v 3 := by linarith
  have hv5 : 0 < v 5 := by linarith
  -- the square roots
  have hia : 1 / a = ((v 2 : ℤ) : ℚ) / ((v 3 : ℤ) : ℚ) := by rw [haf, one_div_div]
  obtain ⟨q1, o1⟩ := qn_sqrtDn_div p (v 2) (v 3) hv2.le hv3
  obtain ⟨q3, o3⟩ := qn_sqrtDn_div p (v 3) (v 2) hv3.le hv2
  obtain ⟨q8, o8⟩ := qn_sqrtDn_div p (v 5) (v 7) hv5.le hv7
  rw [h4p, ← mul_assoc] at q1 q3 q8
  rw [← hia] at q1 o1
  rw [← haf] at q3 o3
  rw [← hqf] at q8 o8
  have w4 : qn p (sqrtDn p (1 / a)) = w2 Q F eh nh v 4 := by rw [q1, w2_4]
  have w6 : qn p (sqrtDn p a) = w2 Q F eh nh v 6 := by rw [q3, w2_6]
  have w8 : qn p (sqrtDn p q) = w2 Q F eh nh v 8 := by rw [q8, w2_8]
  have p6 : 0 < w2 Q F eh nh v 6 := by
    rw [w2_6]
    have := sqrtNum_pos p (v 3) (v 2) hp hv2 hv23
    rw [h4p, ← mul_assoc] at this
    exact_mod_cast this
  have p8 : 0 < w2 Q F eh nh v 8 := by
    rw [w2_8]
    have := sqrtNum_pos p (v 5) (v 7) hp hv7 hv75
    rw [h4p, ← mul_assoc] at this
    exact_mod_cast this
  have hs3 : sqrtDn p a = ((w2 Q F eh nh v 6 : ℤ) : ℚ) / ((Q : ℤ) : ℚ) := by
    rw [hQq, ← w6]; exact eq_qn_div p o3
  have hs8 : sqrtDn p q = ((w2 Q F eh nh v 8 : ℤ) : ℚ) / ((Q : ℤ) : ℚ) := by
    rw [hQq, ← w8]; exact eq_qn_div p o8
  obtain ⟨f2, f4⟩ := r7_s2s4 F Q kN yh _ _ hF hQp p6 p8
  have hV9 : 0 < F * w2 Q F eh nh v 6 * w2 Q F eh nh v 8 * (w2 Q F eh nh v 6 + w2 Q F eh nh v 8) := by
    have := add_pos p6 p8
    positivity
  have hV12 : 0 < F * (w2 Q F eh nh v 6 + w2 Q F eh nh v 8) := mul_pos hF (add_pos p6 p8)
  refine ⟨⟨o1, w4⟩, ⟨o3, w6⟩, ⟨o8, w8⟩, ?_, ?_, ?_, p6, p8, hv23, hv75⟩
  · rw [hs3, hs8, hc, f2, qn_rnd_div p _ _ hV9, ← hQ, w2_11, w2_9, h1]
    all_goals (congr 1; ring)
  · rw [hs3, hs8, hc, f4, qn_rnd_div p _ _ hV12, ← hQ, w2_13, w2_12, h1]
  · have hqf' : q = ((v 5 : ℤ) : ℚ) / ((F * Q * G ^ 2 : ℤ) : ℚ) := by rw [hqf, h7, sq]
    rw [hqf', (r13_s5w F Q G 1 (v 5) eh yh nh 0 0 0 Γ 0 hF hQp hG one_pos hv5).1,
      qn_rnd_div p _ _ (mul_pos hF hv5), ← hQ, w2_2, h0, h4]
    all_goals (congr 1; ring)

end AdversarialBco.Bit.Transfer.BLM
