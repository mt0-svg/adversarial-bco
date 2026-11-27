/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOConst

@[expose] public section

/-!
# UNI-ELL (c): one test of ELL-O inside its block

The test command of ELL-O in its block, `xtestOB`: `xtestO` (EllOTest.lean) on ELL-R's inner block `B.inner`, with
the test block `TB` and, as its SEP command, the SEP block run on the gauge block run on `TB` (EllOSep.lean). The
context `CxO` holds the data of the step: the tests' data of the inner block at the scale `2^s`, `0` in the register
`rE + 2`, `2^{E-s}` in the slot `o + 76`, the test's data at the precision `k` (`TDatK`) and the constants of SEP and
of the gauge (`SepEnvO`); it survives every change of the inner block's own cells (its data excepted) and of the
three blocks (`CxO.frame`). `XVO.testStepO` is `XVO.testO` with `sepCallO`. For the loops: the outcome `.ret x` has
`x = a` (`tfO_ret`); a cut is bounded and keeps the kept point in bounds (`tfO_cut`, with `sepO_G_le` for SEP's cut).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The cuts of a test -/

/-- SEP's cut in ELL-O: each value of the evaluator lies in `[0, 2^{jg+1})`, so `|G_i| ≤ 2^{jg+1} 2^E`. -/
theorem sepO_G_le (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (a : Fin d → ℤ) {Y Gv : Fin d → ℤ}
    (h : sepO I T s a = some (Y, Gv)) (k : Fin d) : |Gv k| ≤ 2 ^ (I.sepEx s + I.jg + 1) := by
  unfold sepO sepE sepZ at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨st, -, hst⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨-, rfl⟩ := hst
  have h1 := evO_lt I T (I.sepEx s) (st.1 + st.2.2 k • eZ k)
  have h2 := evO_lt I T (I.sepEx s) (st.1 - st.2.2 k • eZ k)
  have hdiff : |I.evO T (I.sepEx s) (st.1 + st.2.2 k • eZ k) - I.evO T (I.sepEx s) (st.1 - st.2.2 k • eZ k)| ≤
      2 ^ (I.jg + 1) := by
    rw [abs_le]; constructor <;> omega
  have hq : |(2 : ℤ) ^ I.sepEx s / st.2.2 k| ≤ 2 ^ I.sepEx s :=
    (Int.abs_ediv_le_abs _ _).trans (by rw [abs_of_nonneg (by positivity)])
  dsimp only
  rw [abs_mul, show I.sepEx s + I.jg + 1 = (I.jg + 1) + I.sepEx s by omega, pow_add]
  exact mul_le_mul hdiff hq (abs_nonneg _) (by positivity)

theorem tfO_ret {Ib : EllI d} {T : (Fin d → ℚ) → Bool} {s : ℕ}
    {sepF : (Fin d → ℤ) → Option ((Fin d → ℤ) × (Fin d → ℤ))} {a x : Fin d → ℤ}
    {kept : Option ((Fin d → ℤ) × ℤ)} (h : tfO Ib T s sepF a kept = .ret x) : x = a := by
  unfold tfO at h
  split_ifs at h
  all_goals first | exact ellTest_ret Ib s a x kept h | (split at h <;> simp at h) | simp at h

/-- The cuts of a test: below `2^E` for `E` above ELL-R's bound and SEP's; the kept point stays in bounds. -/
theorem tfO_cut {Ib : EllI d} {T : (Fin d → ℚ) → Bool} {s : ℕ}
    {sepF : (Fin d → ℤ) → Option ((Fin d → ℤ) × (Fin d → ℤ))} {a c : Fin d → ℤ}
    {kept kept' : Option ((Fin d → ℤ) × ℤ)} {capa : ℤ} {F G E : ℕ}
    (ha : ∀ k, |a k| ≤ capa) (hcap : capa ≤ 2 ^ F) (bK : KeptOK capa F kept)
    (bG : ∀ Y Gv, sepF a = some (Y, Gv) → ∀ k, |Gv k| ≤ 2 ^ G)
    (hσF : ellSz Ib ≤ F) (hsF : s + 1 ≤ F) (hdF : d ≤ F) (hFE : F + 2 * ellSz Ib + d + s + 2 ≤ E) (hGE : G ≤ E)
    (h : tfO Ib T s sepF a kept = .cut c kept') : (∀ k, |c k| ≤ 2 ^ E) ∧ KeptOK capa F kept' := by
  have ba : ∀ k, |a k| ≤ 2 ^ F := fun k => (ha k).trans hcap
  have hFE' : (2 : ℤ) ^ F ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold tfO at h
  split_ifs at h
  · obtain ⟨rfl, rfl⟩ := Cut.cut.inj h
    exact ⟨fun k => (ba k).trans hFE', bK⟩
  · refine ⟨fun k => (ellCut_le Ib s F a c kept kept' ba h k).trans (pow_le_pow_right₀ (by norm_num) hFE), ?_⟩
    rcases (ellTest_cut Ib s a c kept kept' h).2 with e | e
    · rw [e]; exact bK
    · rw [e]
      intro b W hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨ha, ellV_le ba hσF hsF hdF⟩
  · split at h
    · obtain ⟨rfl, rfl⟩ := Cut.cut.inj h
      exact ⟨fun k => by simp only [Pi.zero_apply, abs_zero]; positivity, bK⟩
    · rename_i Y Gv hY
      obtain ⟨rfl, rfl⟩ := Cut.cut.inj h
      exact ⟨fun k => (bG Y Gv hY k).trans (pow_le_pow_right₀ (by norm_num) hGE), bK⟩

/-! ## The context of the step -/

/-- The data of a test of ELL-O at the scale `2^s` and the precision `k`. -/
def CxO (B : EllOBlk) (I : EllOI d) (TDat : Env d → Prop) (k s : ℕ) (σ : Env d) : Prop :=
  TestEnv B.inner I.base s (B.o + 83) (B.o + 95) (B.rE + 69) σ ∧ σ.nat (B.rE + 2) = 0 ∧
    σ.sc (B.o + 76) = ((2 ^ (I.sepEx s - s) : ℤ) : ℝ) ∧ TDatK B TDat k σ ∧ SepEnvO B I s σ

/-- `SepEnvO` survives a change that avoids its cells. -/
theorem SepEnvO.keep {B : EllOBlk} {I : EllOI d} {s : ℕ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (h : SepEnvO B I s σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → ¬ (B.o + 4 ≤ y ∧ y ≤ B.o + 8) ∧ ¬ (B.o + 57 ≤ y ∧ y ≤ B.o + 59))
    (hN : ∀ j, N j → j ≠ B.rE + 3 ∧ j ≠ B.rE + 21) (hA : ∀ b k, Ar b k → b ≠ B.ac) : SepEnvO B I s σ' := by
  have nS : ∀ y, (B.o + 4 ≤ y ∧ y ≤ B.o + 8) ∨ (B.o + 57 ≤ y ∧ y ≤ B.o + 59) → σ'.sc y = σ.sc y := fun y hy =>
    hF.2.1 y (fun h' => by have := hS y h'; omega)
  have nN : ∀ j, j = B.rE + 3 ∨ j = B.rE + 21 → σ'.nat j = σ.nat j := fun j hj =>
    hF.1 j (fun h' => by have := hN j h'; omega)
  have nA : ∀ k, σ'.arr B.ac k = σ.arr B.ac k := fun k => hF.2.2.1 _ _ (fun h' => hA _ _ h' rfl)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h
  exact ⟨by rw [nS _ (by omega), e1], by rw [nS _ (by omega), e2], by rw [nS _ (by omega), e3],
    by rw [nS _ (by omega), e4], by rw [nS _ (by omega), e5], by rw [nN _ (by omega), e6],
    by rw [nS _ (by omega), e7], by rw [nS _ (by omega), e8], by rw [nN _ (by omega), e9],
    by rw [nS _ (by omega), e10], by rw [nA, e11], fun j => by rw [nA, e12]⟩

theorem sepS_le {B : EllOBlk} {y : ℕ} (h : sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y) :
    B.o + 3 ≤ y ∧ y < B.o + 76 ∧ ¬ (B.o + 4 ≤ y ∧ y ≤ B.o + 8) ∧ ¬ (B.o + 57 ≤ y ∧ y ≤ B.o + 59) := by
  simp only [sepS, gaugeS, sepLayO, gaugeLayO] at h; omega

theorem sepN_le {B : EllOBlk} {j : ℕ} (h : sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j) :
    B.rE ≤ j ∧ j < B.rE + 26 ∧ j ≠ B.rE + 1 ∧ j ≠ B.rE + 2 ∧ j ≠ B.rE + 3 ∧ j ≠ B.rE + 21 := by
  simp only [sepN, gaugeN, sepLayO, gaugeLayO] at h; omega

theorem sepA_le {B : EllOBlk} {b k : ℕ} (h : sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k) :
    b = B.aW + 1 ∨ (B.aW + 10 ≤ b ∧ b ≤ B.aW + 13) := by
  simp only [sepAr, gaugeAr, sepLayO, gaugeLayO] at h; omega

set_option maxHeartbeats 4000000 in
/-- **The context survives** every change of the inner block's own cells (its scales, `0`, `1` and the register
`rE + 69` excepted), of SEP's, of the gauge's and of the test block's. -/
theorem CxO.frame {L : Layout} {B : EllOBlk} {I : EllOI d} {TDat : Env d → Prop} {k s : ℕ} {St Nt : ℕ → Prop}
    {Art : ℕ → ℕ → Prop} {S N : ℕ → Prop} {A : ℕ → ℕ → Prop} {σ σ' : Env d}
    (hB : B.OK L 215 112 14) (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (h : CxO B I TDat k s σ) (hd : σ'.draws = σ.draws) (hF : FrameA S N A σ σ')
    (hS : ∀ y, S y → (B.o + 80 ≤ y ∧ y ≠ B.o + 95 ∧ y ≠ B.o + 96 ∧ (y < B.o + 86 ∨ B.o + 89 < y)) ∨
      sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
    (hN : ∀ j, N j → (B.rE + 64 ≤ j ∧ j ≠ B.rE + 69) ∨ sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
    (hA : ∀ b k, A b k → B.aW ≤ b ∨ Art b k) : CxO B I TDat k s σ' := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hac⟩ := hB'
  have hav' := hav
  obtain ⟨avS, avN, avA⟩ := hav'
  have stS : ∀ y, St y → y < B.o := fun y h => by
    have := (avS y h).1; simp only [EllOBlk.ownS] at this; omega
  have ntN : ∀ j, Nt j → j ≤ B.rE := fun j h => by
    rcases (avN j h).1 with h' | h'
    · simp only [EllOBlk.ownN] at h'; omega
    · omega
  have arA : ∀ b k, Art b k → b < B.aW := fun b k h => by
    have := (avA b k h).1; simp only [EllOBlk.ownA] at this; omega
  obtain ⟨hT, hz, hcF, hK, hE⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine TestEnv.frame (SR := fun y => (B.o ≤ y ∧ y < B.o + 80) ∨ St y)
      (NR := fun j => (B.rE ≤ j ∧ j < B.rE + 64 ∧ j ≠ B.rE + 2) ∨ Nt j) (AR := fun b => ∃ k, Art b k)
      (inner_OK hB) ?_ ?_ ?_ ?_ (by simp [EllOBlk.inner]) (by simp [EllOBlk.inner]) (by simp [EllOBlk.inner]) hT hF
      ?_ ?_ ?_
    · show ¬ ((B.rE ≤ B.rd ∧ B.rd < B.rE + 64 ∧ B.rd ≠ B.rE + 2) ∨ Nt B.rd) ∧
        ¬ ((B.rE ≤ B.rE + 2 ∧ B.rE + 2 < B.rE + 64 ∧ B.rE + 2 ≠ B.rE + 2) ∨ Nt (B.rE + 2)) ∧
        ¬ ((B.o ≤ B.sl ∧ B.sl < B.o + 80) ∨ St B.sl) ∧ ¬ ((B.o ≤ B.sDf ∧ B.sDf < B.o + 80) ∨ St B.sDf) ∧
        ¬ ((B.o ≤ B.sRn ∧ B.sRn < B.o + 80) ∨ St B.sRn) ∧ ¬ ((B.o ≤ B.sRd ∧ B.sRd < B.o + 80) ∨ St B.sRd) ∧
        ¬ ((B.o ≤ B.srn ∧ B.srn < B.o + 80) ∨ St B.srn) ∧ ¬ ((B.o ≤ B.srd ∧ B.srd < B.o + 80) ∨ St B.srd) ∧
        ¬ ((B.o ≤ B.sen ∧ B.sen < B.o + 80) ∨ St B.sen) ∧ ¬ ((B.o ≤ B.sed ∧ B.sed < B.o + 80) ∨ St B.sed) ∧
        ¬ (∃ k, Art B.aH k) ∧ ¬ (∃ k, Art B.ag k) ∧ ¬ (∃ k, Art B.aP k) ∧ ¬ (∃ k, Art B.af k)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rintro (h | h)
        · omega
        · exact (avN _ h).2.1 rfl
      · rintro (h | h)
        · omega
        · rcases (avN _ h).1 with h' | h'
          · exact h' (by simp only [EllOBlk.ownN]; omega)
          · omega
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.2.2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.2.2.2.2.1 rfl
      · rintro (h | h)
        · omega
        · exact (avS _ h).2.2.2.2.2.2.2.2 rfl
      · rintro ⟨k, h⟩; exact (avA _ _ h).2.1 rfl
      · rintro ⟨k, h⟩; exact (avA _ _ h).2.2.1 rfl
      · rintro ⟨k, h⟩; exact (avA _ _ h).2.2.2.1 rfl
      · rintro ⟨k, h⟩; exact (avA _ _ h).2.2.2.2.1 rfl
    · intro y h; simp only [EllOBlk.inner]
      rcases h with h | h
      · omega
      · have := stS y h; omega
    · intro j h; simp only [EllOBlk.inner]
      rcases h with h | h
      · omega
      · have := ntN j h; omega
    · intro b ⟨k, h⟩; simp only [EllOBlk.inner]; exact arA b k h
    · intro y hy; simp only [EllOBlk.inner]
      rcases hS y hy with h | h | h | h
      · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
      · have := sepS_le (Or.inl h); exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · have := sepS_le (Or.inr h); exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr h)
    · intro j hj; simp only [EllOBlk.inner]
      rcases hN j hj with h | h | h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · have := sepN_le (Or.inl h); exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
      · have := sepN_le (Or.inr h); exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
      · exact Or.inr (Or.inr h)
    · intro b k hb; simp only [EllOBlk.inner]
      rcases hA b k hb with h | h
      · exact Or.inl h
      · exact Or.inr ⟨k, h⟩
  · rw [hF.1 _ (fun h' => by
      rcases hN _ h' with h | h | h | h
      · omega
      · have := sepN_le (Or.inl h); omega
      · have := sepN_le (Or.inr h); omega
      · rcases (avN _ h).1 with h'' | h''
        · exact h'' (by simp only [EllOBlk.ownN]; omega)
        · omega), hz]
  · rw [hF.2.1 _ (fun h' => by
      rcases hS _ h' with h | h | h | h
      · omega
      · have := sepS_le (Or.inl h); omega
      · have := sepS_le (Or.inr h); omega
      · have := stS _ h; omega), hcF]
  · refine TDatK.frame hav hst hK hd (hF.mono (fun y hy => ?_) (fun j hj => ?_) (fun b k hb => ?_))
    · rcases hS y hy with h | h | h | h
      · exact Or.inl ⟨by simp only [EllOBlk.ownS]; omega, by omega⟩
      · have := sepS_le (Or.inl h); exact Or.inl ⟨by simp only [EllOBlk.ownS]; omega, by omega⟩
      · have := sepS_le (Or.inr h); exact Or.inl ⟨by simp only [EllOBlk.ownS]; omega, by omega⟩
      · exact Or.inr h
    · rcases hN j hj with h | h | h | h
      · exact Or.inl ⟨by simp only [EllOBlk.ownN]; omega, by omega⟩
      · have := sepN_le (Or.inl h); exact Or.inl ⟨by simp only [EllOBlk.ownN]; omega, by omega⟩
      · have := sepN_le (Or.inr h); exact Or.inl ⟨by simp only [EllOBlk.ownN]; omega, by omega⟩
      · exact Or.inr h
    · rcases hA b k hb with h | h
      · exact Or.inl h
      · exact Or.inr h
  · refine SepEnvO.keep hE hF (fun y hy => ?_) (fun j hj => ?_) (fun b k hb => ?_)
    · rcases hS y hy with h | h | h | h
      · omega
      · exact (sepS_le (Or.inl h)).2.2
      · exact (sepS_le (Or.inr h)).2.2
      · have := stS _ h; omega
    · rcases hN j hj with h | h | h | h
      · omega
      · have := sepN_le (Or.inl h); omega
      · have := sepN_le (Or.inr h); omega
      · have := ntN _ h; omega
    · rcases hA b k hb with h | h
      · omega
      · exact (avA _ _ h).2.2.2.2.2

/-! ## The step -/

/-- The test command of ELL-O in its block. -/
def xtestOB (L : Layout) (B : EllOBlk) (sepc gc : XCmdO → XCmdO) (TB : XCmdO) : XCmdO :=
  xtestO L B.inner TB (sepc (gc TB)) (sepLayO B) (B.o + 83) (B.o + 95) (B.aW + 2) (B.rE + 65) (B.aW + 1) B.rE
    (B.rE + 2) (B.o + 76)

/-- The slots of SEP, of the gauge and of the test block. -/
abbrev sSO (B : EllOBlk) (St : ℕ → Prop) (y : ℕ) : Prop := sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y

abbrev sNO (B : EllOBlk) (Nt : ℕ → Prop) (j : ℕ) : Prop := sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j

abbrev sAO (B : EllOBlk) (Art : ℕ → ℕ → Prop) (b k : ℕ) : Prop :=
  sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k

/-- The units of a test of ELL-O with a test block of `Kt` units. -/
def stepU (I : EllOI d) (Kt : ℕ) : ℕ := testOU d Kt (sepK d (I.eL + I.eτ + 3) (gaugeK d I.jg Kt))

set_option maxHeartbeats 16000000 in
/-- **A test of ELL-O in its block**: `xtestOB` computes `tfO I.base T s (sepO I T s) a kept`, from the context
`CxO` at the scale `2^s` and the centre `a` in the array `aW + 3`, for a SEP block, a gauge block and a test block
meeting their contracts. -/
theorem XVO.testStepO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool}
    {k Kt bt s F : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop} {a : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOK L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat k) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hC : CxO B I TDat k s σ) (hK : KeptIn (B.o + 83) (B.aW + 8) kept σ)
    (bW : ∀ b W, kept = some (b, W) → |W| ≤ 2 ^ (6 * F + 1))
    (ha : ∀ k : Fin d, σ.arr (B.aW + 3) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F)
    (hσF : ellOSz I ≤ F) (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hEs : I.sepEx s - s ≤ F) (hFb : F < bt)
    (hbt : 3 * (I.sepEx s + F + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx s + I.eτ + I.eu + (I.sepEx s - s + F + 1) + (I.jg + 1) + 8 ≤ ℓ)
    (hℓa : I.sepEx s + I.eτ + 8 < 2 ^ ℓa) (hja : I.jg + 1 < 2 ^ ℓa) (hGl : I.sepEx s + I.jg + 1 < ℓ)
    (hℓF : 64 * F + 16 < ℓ) :
    XRunsBO L XO ℓa ℓ (xtestOB L B sepc gc TB) σ (stepU I Kt) (fun σ' =>
      TestOut (B.o + 83) (B.aW + 2) (B.aW + 2 + 6) (tfO I.base T s (sepO I T s) a kept) σ' ∧
      σ'.draws = σ.draws ∧
      FrameA (tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St)) (tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt))
        (taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art)) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB'
  have hav' := hav
  obtain ⟨avS, avN, avA⟩ := hav'
  have stS : ∀ y, St y → y < B.o := fun y h => by
    have := (avS y h).1; simp only [EllOBlk.ownS] at this; omega
  have ntN : ∀ j, Nt j → j ≤ B.rE := fun j h => by
    rcases (avN j h).1 with h' | h'
    · simp only [EllOBlk.ownN] at h'; omega
    · omega
  have arA : ∀ b k, Art b k → b < B.aW := fun b k h => by
    have := (avA b k h).1; simp only [EllOBlk.ownA] at this; omega
  refine XVO.testO hL (B := B.inner) (Ib := I.base) (s := s) (P := B.o + 83) (u := B.o + 95) (a0 := B.aW + 2)
    (n0 := B.rE + 65) (F := F) (G := I.sepEx s + I.jg + 1) (tp := B.aW + 1) (ans := B.rE) (zr := B.rE + 2)
    (cF := B.o + 76) (E := I.sepEx s) (Kt := Kt) (Ks := sepK d (I.eL + I.eτ + 3) (gaugeK d I.jg Kt)) (bt := bt)
    (TB := TB) (SC := sepc (gc TB)) (sl := sepLayO B) (T := T) (sepF := sepO I T s) (Cx := CxO B I TDat k s)
    (Dat := TDatK B TDat k) (St := St) (Nt := Nt) (SS := sSO B St) (SN := sNO B Nt) (Art := Art)
    (SA := sAO B Art) hd (inner_OK hB) rfl
    ⟨by simp only [EllOBlk.inner]; omega, by omega, by omega, by simp only [EllOBlk.inner]; omega, rfl, by omega,
      by simp only [EllOBlk.inner]; omega, rfl, rfl, by omega⟩
    (by omega) (Or.inl (by omega)) (by simp only [sepLayO]; omega) (Or.inr (by simp only [sepLayO]; omega))
    (by simp only [sepLayO]; omega) (by simp only [sepLayO]; omega) (by simp only [sepLayO, EllOBlk.inner]; omega)
    (by simp only [EllOBlk.inner]; omega) (by simp only [EllOBlk.inner]; omega)
    (by simp only [EllOBlk.inner]; omega)
    (fun y h => by have := stS y h; simp only [EllOBlk.inner]; omega)
    (fun j h => by have := ntN j h; simp only [EllOBlk.inner]; omega)
    (fun b k h => Or.inl (by have := arA b k h; omega))
    (fun y h => by
      simp only [EllOBlk.inner]
      rcases h with h | h | h
      · have := sepS_le (Or.inl h); omega
      · have := sepS_le (Or.inr h); omega
      · have := stS y h; omega)
    (fun j h => by
      simp only [EllOBlk.inner]
      rcases h with h | h | h
      · have := sepN_le (Or.inl h); omega
      · have := sepN_le (Or.inr h); omega
      · have := ntN j h; omega)
    (fun b k h => by
      rcases h with h | h | h
      · have := sepA_le (Or.inl h); omega
      · have := sepA_le (Or.inr h); omega
      · have := arA b k h; omega)
    (fun σ' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    (fun σa σb hCa hdab hF => CxO.frame hB hav hst hCa hdab hF (fun y hy => ?_) (fun j hj => ?_)
      (fun b k hb => ?_))
    hTB
    (fun σ' hC' hY => sepCallO hL hd hB hDc hS hG hTB hav hst hC'.2.2.2.1 hC'.2.2.2.2 hY ba hbt hℓ hℓS hℓa hja)
    (fun Y Gv h k => sepO_G_le I T s a h k) hC hK bW ha ba ((ellSz_base_le I).trans hσF) hsF hdF hEs hFb hGl hℓF
  · simp only [tsO, EllOBlk.inner] at hy
    rcases hy with h | h | h
    · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · simp only [tnO, EllOBlk.inner] at hj
    rcases hj with h | h | h
    · rcases h with h | h | h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inr (Or.inl (by simp only [gaugeN, gaugeLayO]; omega)))
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · simp only [taO, EllOBlk.inner, sepLayO] at hb
    rcases hb with h | h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
    · rcases h with h | h | h
      · exact Or.inl (by have := sepA_le (Or.inl h); omega)
      · exact Or.inl (by have := sepA_le (Or.inr h); omega)
      · exact Or.inr h

/-! ## The cells of a test step -/

theorem tsO_cases {B : EllOBlk} {St : ℕ → Prop} {y : ℕ} (h : tsO B.inner (B.o + 83) (B.o + 95) St (sSO B St) y) :
    (y = B.o + 82 ∨ y = B.o + 83 ∨ y = B.o + 84 ∨ y = B.o + 85 ∨ y = B.o + 90 ∨ B.o + 108 ≤ y) ∨
      (B.o + 3 ≤ y ∧ y < B.o + 76 ∧ (sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y)) ∨ St y := by
  simp only [tsO, EllOBlk.inner] at h
  rcases h with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨(sepS_le (Or.inl h)).1, (sepS_le (Or.inl h)).2.1, Or.inl h⟩)
  · exact Or.inr (Or.inl ⟨(sepS_le (Or.inr h)).1, (sepS_le (Or.inr h)).2.1, Or.inr h⟩)
  · exact Or.inr (Or.inr h)

theorem tnO_cases {B : EllOBlk} {Nt : ℕ → Prop} {j : ℕ} (h : tnO B.inner (B.rE + 65) B.rE Nt (sNO B Nt) j) :
    (j = B.rE + 64 ∨ (B.rE + 65 ≤ j ∧ j ≤ B.rE + 67) ∨ j = B.rE + 70) ∨
      (B.rE ≤ j ∧ j < B.rE + 26 ∧ (sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j)) ∨ Nt j := by
  simp only [tnO, EllOBlk.inner] at h
  rcases h with h | h | h | h | h
  · rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inr (Or.inr (by omega)))
    · exact Or.inr (Or.inl ⟨by omega, by omega, Or.inr (by simp only [gaugeN, gaugeLayO]; omega)⟩)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl ⟨(sepN_le (Or.inl h)).1, (sepN_le (Or.inl h)).2.1, Or.inl h⟩)
  · exact Or.inr (Or.inl ⟨(sepN_le (Or.inr h)).1, (sepN_le (Or.inr h)).2.1, Or.inr h⟩)
  · exact Or.inr (Or.inr h)

theorem taO_cases {B : EllOBlk} {Art : ℕ → ℕ → Prop} {b k : ℕ}
    (h : taO B.inner (B.aW + 2) (B.aW + 1) (B.aW + 9) Art (sAO B Art) b k) :
    (b = B.aW + 1 ∨ (B.aW + 4 ≤ b ∧ b ≤ B.aW + 13)) ∨ Art b k := by
  simp only [taO, EllOBlk.inner] at h
  rcases h with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr h
  · exact Or.inl (by have := sepA_le (Or.inl h); omega)
  · exact Or.inl (by have := sepA_le (Or.inr h); omega)
  · exact Or.inr h

end AdversarialBco.Uni.EllO
