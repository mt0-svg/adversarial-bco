/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOTest

@[expose] public section

/-!
# UNI-ELL (c): the layout of the ELL-O block and its SEP call

The block `B : EllOBlk` holds, above its bases: the output (slots `o`, `o + 1`, array `aW`), the test's point (array
`aW + 1`), answer (register `rE`), precision (register `rE + 1`, slot `o + 2`); a register `rE + 2` holding `0` (the
row count `m = 0` of ELL-R's block); the SEP block (`sepLayO`: slots `o + 3, ..., o + 56`, registers
`rE + 3, ..., rE + 20`, arrays `aW + 9, ..., aW + 13`); the gauge block (`gaugeLayO`: slots `o + 57, ..., o + 75`,
registers `rE + 21, ..., rE + 25`; its point is SEP's evaluator point, its value SEP's value, its test point the
test's point); the factor `2^{E-s}` (slot `o + 76`); the exponents of step 2 (registers `rE + 26, ..., rE + 63`); ELL-R's
block `B.inner` (slots from `o + 80`, registers from `rE + 64`, arrays from `aW`, the output array shared).

`sepCallO`: the SEP block run on the gauge block run on the test block computes `sepO I T s a` (EllOTest.lean) from
`Y₀ = 2^{E-s} a`, from the contracts of SepSpec.lean.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The layout -/

/-- ELL-R's block inside the ELL-O block: the same inputs, `m` in the register `rE + 2`, its own cells from
`o + 80`, `rE + 64`, `aW`. -/
def _root_.AdversarialBco.Uni.EllOBlk.inner (B : EllOBlk) : EllBlk :=
  ⟨B.rd, B.rE + 2, B.sl, B.sDf, B.sRn, B.sRd, B.srn, B.srd, B.sen, B.sed, B.aH, B.ag, B.aP, B.af, B.o + 80,
    B.rE + 64, B.aW⟩

/-- The SEP block inside the ELL-O block. -/
def sepLayO (B : EllOBlk) : SepLay :=
  ⟨B.aW + 9, B.aW + 10, B.aW + 11, B.aW + 12, B.aW + 13, B.o + 3, B.o + 4, B.o + 5, B.o + 6, B.o + 7, B.o + 8,
    B.rE + 3, B.rE + 4, B.o + 9, B.rE + 5⟩

/-- The gauge block inside the ELL-O block: its point is SEP's evaluator point, its centre the input centre, its value
SEP's value, its test point and answer the test's. -/
def gaugeLayO (B : EllOBlk) : GaugeLay :=
  ⟨B.aW + 13, B.ac, B.o + 57, B.o + 58, B.rE + 21, B.o + 59, B.aW + 1, B.rE, B.o + 3, B.o + 60, B.rE + 22⟩


theorem sepLayO_OK {L : Layout} {B : EllOBlk} (hB : B.OK L 215 112 14) : SepLay.OK L (sepLayO B) := by
  obtain ⟨hS, hN, hA, -⟩ := hB
  refine ⟨⟨by simp [sepLayO]; omega, by simp [sepLayO]; omega, by simp [sepLayO]; omega, by simp [sepLayO]; omega,
    by simp [sepLayO]; omega⟩, by simp [sepLayO], ⟨by simp [sepLayO]; omega, by simp [sepLayO]; omega,
    by simp [sepLayO]; omega, by simp [sepLayO]; omega, by simp [sepLayO]; omega, by simp [sepLayO]; omega,
    by simp [sepLayO]; omega⟩, ⟨by simp [sepLayO], by simp [sepLayO], by simp [sepLayO], by simp [sepLayO],
    by simp [sepLayO], by simp [sepLayO], by simp [sepLayO]⟩, ⟨by simp [sepLayO]; omega, by simp [sepLayO]; omega,
    by simp [sepLayO]; omega⟩, ⟨by simp [sepLayO], by simp [sepLayO], by simp [sepLayO]⟩⟩

theorem gaugeLayO_OK {L : Layout} {B : EllOBlk} (hB : B.OK L 215 112 14) : GaugeLay.OK L (gaugeLayO B) := by
  obtain ⟨hS, hN, hA, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB
  exact ⟨⟨by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega⟩,
    ⟨by simp [gaugeLayO], by simp [gaugeLayO]; omega⟩,
    ⟨by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega,
      by simp [gaugeLayO]; omega⟩,
    ⟨by simp [gaugeLayO], by simp [gaugeLayO], by simp [gaugeLayO], by simp [gaugeLayO], by simp [gaugeLayO],
      by simp [gaugeLayO], by simp [gaugeLayO]⟩,
    ⟨by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega, by simp [gaugeLayO]; omega⟩,
    ⟨by simp [gaugeLayO], by simp [gaugeLayO], by simp [gaugeLayO]⟩⟩

theorem inner_OK {L : Layout} {B : EllOBlk} (hB : B.OK L 215 112 14) : B.inner.OK L 135 48 9 := by
  obtain ⟨hS, hN, hA, -, -, -, hrd, hrK, hrk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [EllOBlk.inner] <;> omega

/-! ## The sizes of the call -/

theorem ellOMx_le (I : EllOI d) : I.Dc.natAbs ≤ ellOMx I ∧ ∀ j, (I.Nc j).natAbs ≤ ellOMx I := by
  refine ⟨?_, fun j => ?_⟩
  · unfold ellOMx
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · unfold ellOMx
    refine le_max_of_le_right (le_max_of_le_left ?_)
    exact (le_max_right _ _).trans (Finset.le_sup (f := fun j => max (max (I.g j).natAbs (I.f j).natAbs)
      (I.Nc j).natAbs) (Finset.mem_univ j))

theorem ellMx_base_le (I : EllOI d) : ellMx I.base ≤ ellOMx I := by
  unfold ellMx ellOMx EllOI.base
  simp only [Finset.univ_eq_empty, Finset.sup_empty, bot_eq_zero', zero_le, max_eq_right]
  refine max_le_max le_rfl (max_le_max (Finset.sup_mono_fun fun j _ => le_max_left _ _)
    (max_le_max le_rfl (max_le_max le_rfl (le_max_right _ _))))

theorem ellSz_base_le (I : EllOI d) : ellSz I.base ≤ ellOSz I := by
  unfold ellSz ellOSz
  exact (Nat.size_le_size (ellMx_base_le I)).trans (Nat.le_add_right _ _)

theorem abs_lt_ellOSz {x : ℤ} {I : EllOI d} (h : x.natAbs ≤ ellOMx I) : |x| < 2 ^ ellOSz I := by
  have := Nat.lt_size_self (ellOMx I)
  rw [Int.abs_eq_natAbs]
  have h2 : (ellOMx I).size ≤ ellOSz I := Nat.le_add_right _ _
  have h3 : x.natAbs < 2 ^ ellOSz I := h.trans_lt (this.trans_le (Nat.pow_le_pow_right (by norm_num) h2))
  exact_mod_cast h3

/-! ## The SEP call -/

/-- The constants of SEP and of the gauge in their cells (`sepLayO`, `gaugeLayO`), at the scale `2^s`, and the centre
`c` of the K-part. -/
def SepEnvO (B : EllOBlk) (I : EllOI d) (s : ℕ) (σ : Env d) : Prop :=
  σ.sc (B.o + 4) = 2 ^ I.sepEx s ∧ σ.sc (B.o + 5) = 2 ^ (I.sepEx s - I.e1) ∧
  σ.sc (B.o + 6) = 2 ^ (I.eτ + 4 + I.eL) ∧ σ.sc (B.o + 7) = 2 ^ (I.sepEx s + I.eτ + 1) ∧
  σ.sc (B.o + 8) = 2 ^ I.eu ∧ σ.nat (B.rE + 3) = I.eL + I.eτ + 3 ∧
  σ.sc (B.o + 57) = ((2 ^ I.eH : ℤ) : ℝ) ∧ σ.sc (B.o + 58) = ((1 : ℤ) : ℝ) ∧
  σ.nat (B.rE + 21) = I.jg ∧ σ.sc (B.o + 59) = 2 ^ I.jg ∧
  σ.arr B.ac 0 = I.Dc ∧ ∀ j : Fin d, σ.arr B.ac (1 + (j : ℕ)) = I.Nc j

/-- The gauge's data (the constants and the centre) survive the writes of SEP, of the gauge and of a test block that
avoids the block. -/
theorem SepEnvO.frame {B : EllOBlk} {I : EllOI d} {s : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop} {σ σ' : Env d}
    (hac : B.ac < B.aW) (hav : B.TestAvoid St Nt Art) (h : SepEnvO B I s σ)
    (hF : FrameA (fun y => sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
      (fun j => sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k) σ σ') :
    SepEnvO B I s σ' := by
  obtain ⟨avS, avN, avA⟩ := hav
  have nS : ∀ y, B.o + 3 < y → y < B.o + 9 ∨ (B.o + 57 ≤ y ∧ y < B.o + 60) → σ'.sc y = σ.sc y := fun y h1 h2 =>
    hF.2.1 y (fun h => by
      rcases h with h | h | h
      · simp only [sepS, sepLayO] at h; omega
      · simp only [gaugeS, gaugeLayO] at h; omega
      · have := (avS y h).1; simp only [EllOBlk.ownS] at this; omega)
  have nN : ∀ j, j = B.rE + 3 ∨ j = B.rE + 21 → σ'.nat j = σ.nat j := fun j hj => hF.1 j (fun h => by
    rcases h with h | h | h
    · simp only [sepN, sepLayO] at h; omega
    · simp only [gaugeN, gaugeLayO] at h; omega
    · have := (avN j h).1; simp only [EllOBlk.ownN] at this; omega)
  have nA : ∀ k, σ'.arr B.ac k = σ.arr B.ac k := fun k => hF.2.2.1 _ _ (fun h => by
    rcases h with h | h | h
    · simp only [sepAr, sepLayO] at h; omega
    · simp only [gaugeAr, gaugeLayO] at h; omega
    · exact (avA _ _ h).2.2.2.2.2 rfl)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h
  exact ⟨by rw [nS _ (by omega) (by omega), e1], by rw [nS _ (by omega) (by omega), e2],
    by rw [nS _ (by omega) (by omega), e3], by rw [nS _ (by omega) (by omega), e4],
    by rw [nS _ (by omega) (by omega), e5], by rw [nN _ (by omega), e6], by rw [nS _ (by omega) (by omega), e7],
    by rw [nS _ (by omega) (by omega), e8], by rw [nN _ (by omega), e9], by rw [nS _ (by omega) (by omega), e10],
    by rw [nA, e11], fun j => by rw [nA, e12]⟩

/-- `TDatK` survives the writes of SEP, of the gauge and of the test block. -/
theorem TDatK.frame {B : EllOBlk} {TDat : Env d → Prop} {k : ℕ} {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop}
    {σ σ' : Env d} (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (h : TDatK B TDat k σ) (hd : σ'.draws = σ.draws)
    (hF : FrameA (fun y => (B.ownS y ∧ y ≠ B.o + 2) ∨ St y) (fun j => (B.ownN j ∧ j ≠ B.rE + 1) ∨ Nt j)
      (fun b k => B.ownA b k ∨ Art b k) σ σ') : TDatK B TDat k σ' := by
  obtain ⟨avS, avN, -⟩ := hav
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hst σ σ' h1 (hF.mono (fun y h => by rcases h with h | h; exacts [Or.inl h.1, Or.inr h])
    (fun j h => by rcases h with h | h; exacts [Or.inl h.1, Or.inr h]) (fun b k h => h)) hd, ?_, ?_⟩
  · rw [hF.1 _ (fun h => by
      rcases h with h | h
      · exact h.2 rfl
      · rcases (avN _ h).1 with h' | h'
        · exact h' (by simp only [EllOBlk.ownN]; omega)
        · omega), h2]
  · rw [hF.2.1 _ (fun h => by
      rcases h with h | h
      · exact h.2 rfl
      · exact (avS _ h).1 (by simp only [EllOBlk.ownS]; omega)), h3]

/-- The counter of the gauge's bisection stays in `[0, 2^j]`. -/
theorem gaugeIt_le (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) :
    ∀ k, (gaugeIt T a0 x H j k).1 ≤ (gaugeIt T a0 x H j k).2 ∧ (gaugeIt T a0 x H j k).2 ≤ 2 ^ j := by
  intro k
  induction k with
  | zero => simp [gaugeIt]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [gaugeIt]
    split_ifs
    · exact ⟨Nat.le_div_iff_mul_le (by norm_num) |>.2 (by omega), by omega⟩
    · exact ⟨Nat.div_le_iff_le_mul_add_pred (by norm_num) |>.2 (by omega), h2⟩

theorem evO_lt (I : EllOI d) (T : (Fin d → ℚ) → Bool) (E : ℕ) (X : Fin d → ℤ) :
    0 ≤ I.evO T E X ∧ I.evO T E X < 2 ^ (I.jg + 1) := by
  unfold EllOI.evO
  have := (gaugeIt_le T I.c (ptDN (2 ^ E) X) ((2 : ℚ) ^ I.eH) I.jg I.jg).2
  refine ⟨by positivity, ?_⟩
  have h : (gaugeIt T I.c (ptDN (2 ^ E) X) ((2 : ℚ) ^ I.eH) I.jg I.jg).2 < 2 ^ (I.jg + 1) :=
    this.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact_mod_cast h

set_option maxHeartbeats 4000000 in
/-- **The SEP call of ELL-O**: the SEP block on the gauge block (about the centre `c`, `H = 2^{eH}`, `jg` steps) on the
test block computes `sepO I T s a` from `Y₀ = 2^{E-s} a` in SEP's array, `E = sepEx s`, and writes only the cells of
the three blocks. -/
theorem sepCallO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {B : EllOBlk} {I : EllOI d}
    {sepc gc : XCmdO → XCmdO} {TB : XCmdO} {TDat : Env d → Prop} {T : (Fin d → ℚ) → Bool} {k Kt bt s F : ℕ}
    {St Nt : ℕ → Prop} {Art : ℕ → ℕ → Prop} {σ : Env d} {a : Fin d → ℤ}
    (hd : 1 ≤ d) (hB : B.OK L 215 112 14) (hDc : 0 < I.Dc)
    (hS : SepBlockOK L XO ℓa ℓ (sepLayO B) sepc) (hG : GaugeBlockOK L XO ℓa ℓ (gaugeLayO B) gc)
    (hTB : TestOK L XO ℓa ℓ TB (TDatK B TDat k) (B.aW + 1) B.rE bt T Kt St Nt Art)
    (hav : B.TestAvoid St Nt Art)
    (hst : Stable TDat (fun y => B.ownS y ∨ St y) (fun j => B.ownN j ∨ Nt j) (fun b k => B.ownA b k ∨ Art b k))
    (hT : TDatK B TDat k σ) (hE : SepEnvO B I s σ)
    (hY : ∀ i : Fin d, σ.arr (B.aW + 9) i = ((2 : ℤ) ^ (I.sepEx s - s) • a) i) (ba : ∀ i, |a i| ≤ 2 ^ F)
    (hbt : 3 * (I.sepEx s + F + I.eH + ellOSz I + 3) + I.jg + 2 ≤ bt) (hℓ : bt + 4 ≤ ℓ)
    (hℓS : I.sepEx s + I.eτ + I.eu + (I.sepEx s - s + F + 1) + (I.jg + 1) + 8 ≤ ℓ)
    (hℓa : I.sepEx s + I.eτ + 8 < 2 ^ ℓa) (hja : I.jg + 1 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (sepc (gc TB)) σ (sepK d (I.eL + I.eτ + 3) (gaugeK d I.jg Kt)) (fun σ' =>
      SepOut (sepLayO B) (sepO I T s a) σ' ∧
      FrameA (fun y => sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
        (fun j => sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
        (fun b k => sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k) σ σ' ∧ σ'.draws = σ.draws) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hac⟩ := hB'
  have hav' := hav
  obtain ⟨avS, avN, avA⟩ := hav'
  -- the frames of the inner blocks
  have mT : ∀ σa σb : Env d, FrameA (fun y => sepS (sepLayO B) y ∨ gaugeS (gaugeLayO B) y ∨ St y)
      (fun j => sepN (sepLayO B) j ∨ gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => sepAr (sepLayO B) b k ∨ gaugeAr (gaugeLayO B) b k ∨ Art b k) σa σb →
      FrameA (fun y => (B.ownS y ∧ y ≠ B.o + 2) ∨ St y) (fun j => (B.ownN j ∧ j ≠ B.rE + 1) ∨ Nt j)
        (fun b k => B.ownA b k ∨ Art b k) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h
      · left; simp only [sepS, sepLayO, EllOBlk.ownS] at h ⊢; omega
      · left; simp only [gaugeS, gaugeLayO, EllOBlk.ownS] at h ⊢; omega
      · exact Or.inr h) (fun j h => by
      rcases h with h | h | h
      · left; simp only [sepN, sepLayO, EllOBlk.ownN] at h ⊢; omega
      · left; simp only [gaugeN, gaugeLayO, EllOBlk.ownN] at h ⊢; omega
      · exact Or.inr h) (fun b k h => by
      rcases h with h | h | h
      · left; simp only [sepAr, sepLayO, EllOBlk.ownA] at h ⊢; omega
      · left; simp only [gaugeAr, gaugeLayO, EllOBlk.ownA] at h ⊢; omega
      · exact Or.inr h)
  have stT : Stable (TDatK B TDat k) (fun y => gaugeS (gaugeLayO B) y ∨ St y)
      (fun j => gaugeN (gaugeLayO B) j ∨ Nt j) (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) :=
    fun σa σb h hF hd' => TDatK.frame hav hst h hd' (mT σa σb (hF.mono (fun y h => Or.inr h) (fun j h => Or.inr h)
      (fun b k h => Or.inr h)))
  have gdisj : GaugeDisj (gaugeLayO B) St Nt Art := by
    refine ⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩
    · have := (avS y h).1; simp only [EllOBlk.ownS] at this; simp only [gaugeLayO]; omega
    · rcases (avN j h).1 with h' | h'
      · simp only [EllOBlk.ownN] at h'; simp only [gaugeLayO]; omega
      · simp only [gaugeLayO]; omega
    · have := (avA b k h).1; have := (avA b k h).2.2.2.2.2; simp only [EllOBlk.ownA] at *
      simp only [gaugeLayO]; omega
  have sdisj : SepDisj (sepLayO B) (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) := by
    refine ⟨fun y h => ?_, fun j h => ?_, fun b k h => ?_⟩
    · rcases h with h | h
      · simp only [gaugeS, gaugeLayO] at h; simp only [sepLayO]; omega
      · have := (avS y h).1; simp only [EllOBlk.ownS] at this; simp only [sepLayO]; omega
    · rcases h with h | h
      · simp only [gaugeN, gaugeLayO] at h; simp only [sepLayO]; omega
      · rcases (avN j h).1 with h' | h'
        · simp only [EllOBlk.ownN] at h'; simp only [sepLayO]; omega
        · simp only [sepLayO]; omega
    · rcases h with h | h
      · simp only [gaugeAr, gaugeLayO] at h; simp only [sepLayO]; omega
      · have := (avA b k h).1; simp only [EllOBlk.ownA] at this; simp only [sepLayO]; omega
  -- the evaluator: the gauge block on the test block
  set E := I.sepEx s with hEdef
  set b := E + F + I.eH + ellOSz I + 3 with hb
  have bY : ∀ i, |((2 : ℤ) ^ (E - s) • a) i| ≤ 2 ^ (E - s + F) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by positivity), pow_add]
    exact mul_le_mul_of_nonneg_left (ba i) (by positivity)
  obtain ⟨mDc, mNc⟩ := ellOMx_le I
  have hpow : ∀ m, m ≤ b → (2 : ℤ) ^ m ≤ 2 ^ b := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hEV : EvalOK L XO ℓa ℓ (gc TB) (fun σ' => TDatK B TDat k σ' ∧ SepEnvO B I s σ') (sepLayO B).aev
      (sepLayO B).vout E (SepDom ((2 : ℤ) ^ (E - s) • a) E I.e1) (I.evO T E) (gaugeK d I.jg Kt)
      (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
      (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) := by
    intro σ' X ⟨hT', hE'⟩ hX h0 hXi
    obtain ⟨-, -, -, -, -, -, e7, e8, e9, e10, e11, e12⟩ := hE'
    have bX : ∀ i, |X i| < 2 ^ b := fun i => by
      have h1 := hX i
      have h2 := bY i
      have h3 : (2 : ℤ) ^ (E - s + F) ≤ 2 ^ (b - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : 2 * (2 : ℤ) ^ (E - I.e1) ≤ 2 ^ (b - 2) := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h5 : (2 : ℤ) ^ b = 4 * 2 ^ (b - 2) := by
        have hb2 : b = 2 + (b - 2) := by omega
        conv_lhs => rw [hb2, pow_add]
        norm_num
      have h6 : 0 < (2 : ℤ) ^ (b - 2) := by positivity
      rw [abs_le] at h2; rw [abs_le] at h1; rw [abs_lt]; constructor <;> linarith
    have bDc : I.Dc < 2 ^ b := lt_of_le_of_lt (le_abs_self _)
      ((abs_lt_ellOSz mDc).trans_le (hpow _ (by omega)))
    have bNc : ∀ i, |I.Nc i| < 2 ^ b := fun i => (abs_lt_ellOSz (mNc i)).trans_le (hpow _ (by omega))
    refine XVO.mono (hG TB (TDatK B TDat k) T Kt bt St Nt Art σ' (2 ^ E) X I.Dc I.Nc (2 ^ I.eH) 1 I.jg b hL
      (gaugeLayO_OK hB) hd hTB gdisj stT hT' (by push_cast; exact h0) hXi e11 e12 e7 e8 e9 e10 (by positivity) hDc
      (by positivity) one_pos (pow_lt_pow_right₀ (by norm_num) (by omega)) bX bDc bNc
      (pow_lt_pow_right₀ (by norm_num) (by omega)) (one_lt_pow₀ (by norm_num) (by omega)) hbt hℓ hja) le_rfl ?_
    rintro σ'' ⟨v, Fv, dv⟩
    refine ⟨?_, Fv, dv⟩
    have hH : ((2 ^ I.eH : ℤ) : ℚ) / ((1 : ℤ) : ℚ) = (2 : ℚ) ^ I.eH := by push_cast; ring
    show σ''.sc (B.o + 3) = ((I.evO T E X : ℤ) : ℝ)
    rw [show B.o + 3 = (gaugeLayO B).gout from rfl, v, hH]
    unfold EllOI.evO EllOI.c
    push_cast
    rfl
  refine hS (gc TB) (fun σ' => TDatK B TDat k σ' ∧ SepEnvO B I s σ') (I.evO T E) (gaugeK d I.jg Kt) (I.jg + 1)
    (fun y => gaugeS (gaugeLayO B) y ∨ St y) (fun j => gaugeN (gaugeLayO B) j ∨ Nt j)
    (fun b k => gaugeAr (gaugeLayO B) b k ∨ Art b k) σ ((2 : ℤ) ^ (E - s) • a) E I.e1 I.eτ I.eL I.eu
    (E - s + F + 1) hL (sepLayO_OK hB) hd hEV ?_ sdisj ?_ ⟨hT, hE⟩ hY ?_ hE.1 hE.2.1 hE.2.2.1 hE.2.2.2.1
    hE.2.2.2.2.1 hE.2.2.2.2.2.1 ?_ hℓS hℓa
  · intro X _
    obtain ⟨h0, h1⟩ := evO_lt I T E X
    rw [abs_of_nonneg h0]; exact h1
  · intro σa σb ⟨h1, h2⟩ hF hd'
    exact ⟨TDatK.frame hav hst h1 hd' (mT σa σb hF), SepEnvO.frame hac hav h2 hF⟩
  · intro i; exact (bY i).trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  · rw [hEdef]; unfold EllOI.sepEx; omega

end AdversarialBco.Uni.EllO
