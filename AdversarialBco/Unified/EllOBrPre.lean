/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOStep
public import AdversarialBco.Bit.Transfer.XEllRoute

@[expose] public section

/-!
# UNI-ELL (c): the pieces of the ELL-O branch

The pure loops of ELL-O and BIS-O as `loopT` and `bisT` over the test `tfO` (`ellLoopO_eq`, `bisLoopO_eq`); ELL-R's
start state (`xellPre`, the first four parts of ELL-R's branch, `XV.ellPre`); the tests' data of
the inner block below its bases (`TestEnv.below`); the command of the ELL-O branch (`xellBrO`) and its units.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

-- One declaration at a time: the proofs below are large, and a parallel elaboration exceeds the memory cap of the
-- build.
set_option Elab.async false

/-! ## The loops of ELL-O and BIS-O -/

theorem ellLoopO_eq (I : EllOI d) (T : (Fin d → ℚ) → Bool) : ∀ (N : ℕ) (st : ESt d),
    ellLoopO I T N st = loopT (tfO I.base T I.base.p (sepO I T I.base.p)) I.base.p I.base.q I.base.j
      ((2 : ℤ) ^ I.base.p * I.base.Lam) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) N st
  | 0, st => rfl
  | N + 1, st => by
    rw [ellLoopO, loopT, ← ellTestO_eq]
    rcases ellTestO I T I.base.p st.a st.kept with x | ⟨c, kept⟩
    · rfl
    · simp only
      split_ifs
      · rfl
      · rcases ellUpd I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
          ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) st.A st.a c with _ | ⟨A', a'⟩
        · rfl
        · exact ellLoopO_eq I T N _

theorem bisLoopO_eq (I : EllOI d) (T : (Fin d → ℚ) → Bool) : ∀ (N : ℕ) (lo hi : ℤ) kept,
    bisLoopO I T N lo hi kept = bisT (tfO I.base T (I.base.lam + 1) (sepO I T (I.base.lam + 1))) N lo hi kept
  | 0, lo, hi, kept => rfl
  | N + 1, lo, hi, kept => by
    rw [bisLoopO, bisT, ← ellTestO_eq]
    rcases ellTestO I T (I.base.lam + 1) (fun _ => (lo + hi) / 2) kept with x | ⟨c, kept'⟩
    · rfl
    · simp only
      split_ifs
      · rfl
      · exact bisLoopO_eq I T N _ _ _
      · exact bisLoopO_eq I T N _ _ _

/-! ## ELL-R's start state -/

/-- The first four parts of ELL-R's branch: `d` and its logarithms, the registers, the slots, the start state. -/
def xellPre (L : Layout) (B : EllBlk) (P u c a0 n0 : ℕ) : XCmd :=
  .seq (xellS0 L B u c n0) (.seq (xellSetR B n0) (.seq (xellSlots L B P u c n0) (xellArr L B P u c a0 n0)))

/-- The units of `xellPre`. -/
def ellPreU (d : ℕ) (I : EllI d) : ℕ :=
  (24 * d + 16) + (30 + ((32 * I.p + 12 * I.q + 36 * I.lam + 111) + (7 * (d * d) + 14 * d + 13)))

set_option maxHeartbeats 16000000 in
/-- The rule of `xellPre` (ELL-R's branch up to its loop): the tests' data at the scale `2^p`, the update's
data, ELL-R's start state, and `N`, `j`, `lg R̄`, `p` in registers, `p` in the slot `o + 1`. -/
theorem XV.ellPre {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u c a0 n0 : ℕ} (hB : B.OK L nS nN nA) (hP : P = B.o + 3) (hu : u = P + 12) (hc : c = u + 60)
    (hn : n0 = B.rE + 1) (ha : a0 = B.aW + 2) (hS : c + 60 ≤ L.NS) (hNN : n0 + 47 ≤ L.NN) (hNA : a0 + 7 ≤ L.NA)
    (hin : EllIn B I σ) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hone : σ.nat (n0 + 4) = 1)
    (hRb : σ.sc c = ((I.Rb : ℤ) : ℝ)) (hj : σ.nat (n0 + 8) = I.j) (hcR : σ.nat (n0 + 9) = Nat.clog 2 I.Rb)
    (hl : σ.nat (n0 + 10) = I.lam) (hd : 2 ≤ d) (hr : 0 < I.r) (he : 0 < I.e)
    (hℓ : 4500 * (ellSz I + d + 2) ≤ ℓ) (hℓa : 1000 * (d + I.m + ellSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellPre L B P u c a0 n0) σ (ellPreU d I) (fun σ' =>
      TestEnv B I I.p P u (n0 + 4) σ' ∧
      UpdEnv u I.p I.q I.j ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) σ' ∧
      LoopSt P a0 (a0 + 6) ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) (ellF d (ellSz I))
        (⟨((2 : ℤ) ^ I.p * I.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩ : ESt d) σ' ∧
      σ'.nat (n0 + 7) = I.N ∧ σ'.nat (n0 + 8) = I.j ∧ σ'.nat (n0 + 9) = Nat.clog 2 I.Rb ∧
      σ'.nat (n0 + 22) = I.p ∧ σ'.sc (B.o + 1) = ((I.p : ℕ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, hrd, hrm, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  have hd1 : 1 ≤ d := by omega
  obtain ⟨blam, bp, bq, bcR⟩ := ellLam_le I hd1 hr he
  have bj := ellJ_le I hd1 hr he
  obtain ⟨rN, rW, rdd, rA2, rA2'⟩ := ell_regs (m := I.m) blam hℓa
  have hdd1 : d * (d + 1) = d * d + d := by ring
  have hRb0 : (0 : ℤ) ≤ I.Rb := by positivity
  have hRbs : (I.Rb : ℤ) ≤ 2 ^ ellSz I := by exact_mod_cast (ellRb_lt I).le
  obtain ⟨pRR, pL, pLH, pRL, ppRR, pcA, pca⟩ := ell_pows (lam := I.lam) (p := I.p) hRb0 hRbs
  have ep : I.p = 6 + Nat.clog 2 (d ^ 2 * (d + 1)) + 2 * I.j := rfl
  have eq : I.q = 9 + Nat.clog 2 d + Nat.clog 2 I.Rb + 3 * I.lam + 2 * I.j := rfl
  have eN : I.N = 2 * d * (d + 1) * I.lam + 1 := rfl
  have hin' := hin
  obtain ⟨e_rd, -⟩ := hin'
  refine XV.mono (K := (24 * d + 16) + (30 + ((32 * I.p + 12 * I.q + 36 * I.lam + 111) +
    (7 * (d * d) + 14 * d + 13)))) ?_ (by unfold ellPreU; omega) (fun _ h => h)
  -- `d`, `d²(d + 1)`, their logarithms
  refine XV.seq (XV.ellS0 hL (B := B) (u := u) (c := c) (n0 := n0) (by omega) (by omega) (by omega) (by omega)
    e_rd hz h1 hone (by omega) (by omega)) fun σ1 ⟨d13, c1v, cdv, d1, F1⟩ => ?_
  have n1 : ∀ j, j ≠ n0 + 17 → j ≠ n0 + 18 → σ1.nat j = σ.nat j := fun j h h' => F1.1 j (by omega)
  -- the registers
  refine XV.seq (XV.ellSetR hL (B := B) (n0 := n0) (j := I.j) (cR := Nat.clog 2 I.Rb) (lam := I.lam)
    (c1 := Nat.clog 2 (d ^ 2 * (d + 1))) (cd := Nat.clog 2 d) (by omega) (by omega) hd1
    (by rw [n1 _ (by omega) (by omega), hone]) (by rw [n1 _ (by omega) (by omega), e_rd])
    (by rw [n1 _ (by omega) (by omega), hj]) (by rw [n1 _ (by omega) (by omega), hcR])
    (by rw [n1 _ (by omega) (by omega), hl]) c1v cdv rfl (by omega) rA2 rA2' (by omega))
    fun σ2 ⟨r4, rdv, r8, _, r14, r15, r22, r30, r7, r34, r35, r36, r38, r39, r42, r45, d2, F2⟩ => ?_
  have s2 : ∀ y, ¬ (y = c + 12 ∨ y = c + 13 ∨ c + 21 ≤ y) → σ2.sc y = σ.sc y := fun y h => by
    rw [F2.2.1 _ id, F1.2.1 _ h]
  -- the slots
  have hE : ellSz I + 6 * I.lam + 2 + I.p + ellSz I ≤ ellE d (ellSz I) := by unfold ellE; omega
  refine XV.seq (XV.ellSlots hL (B := B) (P := P) (u := u) (c := c) (n0 := n0) (p := I.p) (q := I.q) (j := I.j)
    (lam := I.lam) (E := ellE d (ellSz I)) (Rb := I.Rb) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [s2 _ (by omega), hz]) (by rw [s2 _ (by omega), h1]) (by rw [s2 _ (by omega), hRb])
    (by rw [F2.2.1 _ id, d13]) r4 r14 (by rw [r22, ep]) (by rw [r30, eq]) (by rw [r34, ep]) (by rw [r35, ep])
    (by rw [r36, ep]) (by rw [r38, ep]) (by rw [r39, eq]) r42 r45
    (abs_le_of_le hRb0 hRbs (by omega)) (abs_le_of_le (mul_nonneg hRb0 hRb0) pRR (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) pL (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) le_rfl (by omega))
    (abs_le_of_le (by positivity) pLH (by omega)) (abs_le_of_le (by positivity) pRL (by omega))
    (by omega) (by omega) (by unfold ellE at hE ⊢; omega) (by omega))
    fun σ3 ⟨o3v, t3, t4, t5, t6, hU, c20, z3, o3, d3, F3⟩ => ?_
  have n3 : ∀ j, j ≠ n0 + 46 → σ3.nat j = σ2.nat j := fun j h => F3.1 j h
  -- the start state
  refine XV.mono (XV.ellArr hL (B := B) (P := P) (u := u) (c := c) (a0 := a0) (n0 := n0)
    (E := ellE d (ellSz I)) (D := 2 ^ I.p * (I.Rb * I.Rb)) hd1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) z3 c20 (abs_le_of_le (by positivity) ppRR (by omega)) (by unfold ellE at hE ⊢; omega)
    (by rw [n3 _ (by omega), r4]) (by rw [n3 _ (by omega), r14]) (by rw [n3 _ (by omega), r15])
    (by rw [n3 _ (by omega), rdv])) le_rfl fun σ4 ⟨A4, a4, k4, d4, F4⟩ => ?_
  -- the frame so far
  have G4 : FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ4 :=
    (((F1.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => h.elim) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      (F3.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      (F4.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => by omega))
  have D4 : σ4.draws = σ.draws := by rw [d4, d3, d2, d1]
  have hin4 : EllIn B I σ4 := EllIn.frame hB hin G4 (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
  have s4 : ∀ y, ¬ (y = P + 1 ∨ c + 24 ≤ y) → σ4.sc y = σ3.sc y := fun y h => F4.2.1 y h
  have n4 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → j ≠ n0 + 46 → σ4.nat j = σ2.nat j := fun j h h' h'' => by
    rw [F4.1 _ (by omega), n3 _ h'']
  -- the loop
  have eA : (2 : ℤ) ^ I.p * (I.Rb * I.Rb * 2 ^ (6 * I.lam + 2)) = 2 ^ I.p * (I.Lam : ℤ) := by
    unfold EllI.Lam; push_cast; ring
  have ea : (2 : ℤ) ^ I.p * (I.Rb + I.Rb * 2 ^ (3 * I.lam + 1)) = 2 ^ I.p * ((I.Rb : ℤ) + (I.LamH : ℤ)) := by
    unfold EllI.LamH; push_cast; ring
  rw [eA, ea] at hU
  have hU4 : UpdEnv u I.p I.q I.j ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) σ4 :=
    hU.frame F4 (fun y h => by omega)
  have hT4 : TestEnv B I I.p P u (n0 + 4) σ4 :=
    ⟨hin4, by rw [s4 _ (by omega), z3], by rw [s4 _ (by omega), o3], by rw [n4 _ (by omega) (by omega) (by omega), r4],
      by rw [s4 _ (by omega), t3], by rw [s4 _ (by omega), t4], by rw [s4 _ (by omega), t5],
      by rw [s4 _ (by omega), t6]⟩
  have bA : ∀ i k, |(((2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)) i k| ≤
      (2 : ℤ) ^ I.p * I.Lam := by
    intro i k
    have h0 : (0 : ℤ) ≤ (2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2 := by positivity
    have hle : (2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2 ≤ (2 : ℤ) ^ I.p * I.Lam := by
      unfold EllI.Lam; push_cast
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
        (by positivity)
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one, abs_of_nonneg h0]; exact hle
    · rw [smul_eq_mul, mul_zero, abs_zero]; exact h0.trans hle
  have eD : (2 : ℤ) ^ I.p * (I.Rb * I.Rb) = 2 ^ I.p * (I.Rb : ℤ) ^ 2 := by ring
  have hS4 : LoopSt P a0 (a0 + 6) ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) (ellF d (ellSz I))
      (⟨((2 : ℤ) ^ I.p * I.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩ : ESt d) σ4 :=
    ⟨fun i k => (A4 i k).trans (by rw [eD]), a4, k4, bA, fun k => by simp only [Pi.zero_apply, abs_zero]; positivity,
      fun b W h => by cases h⟩
  exact ⟨hT4, hU4, hS4, by rw [n4 _ (by omega) (by omega) (by omega), r7, eN],
    by rw [n4 _ (by omega) (by omega) (by omega), r8],
    by rw [n4 _ (by omega) (by omega) (by omega), F2.1 _ (by omega), n1 _ (by omega) (by omega), hcR],
    by rw [n4 _ (by omega) (by omega) (by omega), r22, ep],
    by rw [s4 _ (by omega), o3v, Int.cast_natCast], D4, G4⟩

/-! ## The data of the inner block below its bases -/

/-- The tests' data of the inner block survive a change of the ELL-O block's own cells below the inner block (the
register `rE + 2` excepted). -/
theorem TestEnv.below {L : Layout} {B : EllOBlk} {Ib : EllI d} {s P u one : ℕ} {S N : ℕ → Prop}
    {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (hB : B.OK L 215 112 14) (hT : TestEnv B.inner Ib s P u one σ)
    (hF : FrameA S N Ar σ σ') (hS : ∀ y, S y → B.o ≤ y ∧ y < B.o + 80)
    (hN : ∀ j, N j → B.rE ≤ j ∧ j < B.rE + 64 ∧ j ≠ B.rE + 2) (hA : ∀ b k, ¬ Ar b k) (hu : B.o + 80 ≤ u)
    (hP : B.o + 80 ≤ P) (hone : B.rE + 64 ≤ one) : TestEnv B.inner Ib s P u one σ' := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hac⟩ := hB'
  refine TestEnv.frame (SR := S) (NR := N) (AR := fun _ => False) (inner_OK hB) ?_ ?_ ?_ (fun _ h => h.elim)
    (by simp only [EllOBlk.inner]; omega) (by simp only [EllOBlk.inner]; omega)
    (by simp only [EllOBlk.inner]; omega) hT hF (fun y h => Or.inr h) (fun j h => Or.inr h)
    (fun b k h => (hA b k h).elim)
  · simp only [EllBlk.Avoid, EllOBlk.inner]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_, id, id, id, id⟩
    all_goals first | (have := hN _ h; omega) | (have := hS _ h; omega)
  · intro y h; have := hS y h; simp only [EllOBlk.inner]; omega
  · intro j h; have := hN j h; simp only [EllOBlk.inner]; omega

/-! ## The ELL-O branch -/

/-- The exponent bound of ELL-O's cuts: ELL-R's and SEP's. -/
def ellOE (I : EllOI d) (s : ℕ) : ℕ := ellE d (ellOSz I) + I.sepEx s + I.jg + 1

/-- The bound of the centres in the test step. -/
def ellOF (I : EllOI d) (s : ℕ) : ℕ := ellF d (ellOSz I) + I.sepEx s

/-- The ELL-O branch: ELL-R's start state, the constants of step 2, the loop, ELL-R's output. The inner block's
`P = o + 83`, `u = o + 95`, `c = o + 155`, `a0 = aW + 2`, `n0 = rE + 65`. -/
def xellBrO (L : Layout) (B : EllOBlk) (sepc gc : XCmdO → XCmdO) (TB : XCmdO) : XCmdO :=
  .seq (.base (xellPre L B.inner (B.o + 83) (B.o + 95) (B.o + 155) (B.aW + 2) (B.rE + 65)))
  (.seq (.base (xconstO L B (B.rE + 73) (B.rE + 74) (B.rE + 58) (B.rE + 87) (B.rE + 69)))
  (.seq (xloopT L B.inner (xtestOB L B sepc gc TB) (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65))
    (.base (xellOut L B.inner (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65)))))

/-- The units of the ELL-O branch with a test block of `Kt` units. -/
def ellBrOU (I : EllOI d) (κ Kt : ℕ) : ℕ :=
  ellPreU d I.base + (constOU (cstX I I.base.p κ) + ((I.base.N * (kbT d (ellOE I I.base.p) (stepU I Kt) + 2) + 4) +
    (8 * d + 8)))

end AdversarialBco.Uni.EllO
