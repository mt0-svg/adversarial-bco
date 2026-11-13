/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriScanLoop
public import AdversarialBco.Bit.Transfer.XEllSet
public import AdversarialBco.Bit.Transfer.XDriver
public import AdversarialBco.Bit.Transfer.XFrame1Lem

@[expose] public section

/-!
# Procedure FRAME on the machine, the read-off F2 for `d = 1`

The scan `f1scan` (Bit/Transfer/XFrameLem.lean) on the slots: instead of the indices of the best rows, the machine
keeps their values. Slots from `o`: `o + 6` holds `0`, `o + 7` holds `1`, `o + 8` the entry `α_t` of the current row;
the lower end `o + 9` (present), `o + 10` (`α`), `o + 11` (`β`); the upper end `o + 12, o + 13, o + 14`; the bad-row
flag `o + 15`; scratch `o + 16`, `o + 17`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## One row of the scan -/

/-- The lower end on a row with `α_t < 0`: take the row if there is none yet, or if `β_k α_t < β_t α_k`. -/
def xf1lo (L : Layout) (o sB : ℕ) : XCmd :=
  xifS L (o + 9) (o + 7)
    (.seq (xset L (o + 9) (o + 7) (o + 6)) (.seq (xset L (o + 10) (o + 8) (o + 6)) (xset L (o + 11) sB (o + 6))))
    (.seq (toX (VL.sop2 L .mul (o + 16) (o + 11) (o + 8))) (.seq (toX (VL.sop2 L .mul (o + 17) sB (o + 10)))
      (xifS L (o + 16) (o + 17) (.seq (xset L (o + 10) (o + 8) (o + 6)) (xset L (o + 11) sB (o + 6))) .skip)))

/-- The upper end on a row with `α_t > 0`: take the row if there is none yet, or if `β_t α_k < β_k α_t`. -/
def xf1hi (L : Layout) (o sB : ℕ) : XCmd :=
  xifS L (o + 12) (o + 7)
    (.seq (xset L (o + 12) (o + 7) (o + 6)) (.seq (xset L (o + 13) (o + 8) (o + 6)) (xset L (o + 14) sB (o + 6))))
    (.seq (toX (VL.sop2 L .mul (o + 16) sB (o + 13))) (.seq (toX (VL.sop2 L .mul (o + 17) (o + 14) (o + 8)))
      (xifS L (o + 16) (o + 17) (.seq (xset L (o + 13) (o + 8) (o + 6)) (xset L (o + 14) sB (o + 6))) .skip)))

/-- A zero row with `β_t < 0` sets the bad-row flag. -/
def xf1zero (L : Layout) (o sB : ℕ) : XCmd := xifS L sB (o + 6) (xset L (o + 15) (o + 7) (o + 6)) .skip

/-- One row of the scan, `α_t` in `o + 8`, `β_t` in `sB`. -/
def xf1step (L : Layout) (o sB : ℕ) : XCmd :=
  xifS L (o + 8) (o + 6) (xf1lo L o sB) (xifS L (o + 6) (o + 8) (xf1hi L o sB) (xf1zero L o sB))

/-- The state of the scan in the slots. -/
abbrev F1In (al be : ℕ → ℤ) (o : ℕ) (st : Option ℕ × Option ℕ × Bool) (σ : Env d) : Prop :=
  (match st.1 with
    | none => σ.sc (o + 9) = 0
    | some i => σ.sc (o + 9) = 1 ∧ σ.sc (o + 10) = al i ∧ σ.sc (o + 11) = be i) ∧
  (match st.2.1 with
    | none => σ.sc (o + 12) = 0
    | some k => σ.sc (o + 12) = 1 ∧ σ.sc (o + 13) = al k ∧ σ.sc (o + 14) = be k) ∧
  σ.sc (o + 15) = (if st.2.2 then 1 else 0)

/-- `x := y + z` with `z` holding `0`: a copy. -/
theorem XV.cpy {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {x y z : ℕ} (hx : x < L.NS)
    (hy : y < L.NS) (hz : z < L.NS) (h0 : σ.sc z = 0) (hb : |σ.sc y| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xset L x y z) σ 1 (· = σ.setSc x (σ.sc y)) := by
  have e : RealRAM.Op2.eval .add (σ.sc y) (σ.sc z) = σ.sc y := by simp [RealRAM.Op2.eval, h0]
  exact XV.mono (XV.sop2 hL hx hy hz .add (by intro h; cases h) hb (by rw [h0, abs_zero]; positivity)
    (by rw [e]; exact hb)) le_rfl fun σ' h => by rw [h, e]

theorem abs_cast_lt_of {x M : ℤ} {ℓ : ℕ} (h : |x| ≤ M) (hM : M < 2 ^ ℓ) : |(x : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (h.trans_lt hM)

set_option maxHeartbeats 4000000 in
/-- **One row of the scan on the machine.** -/
theorem XV.f1step {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o sB t : ℕ}
    {al be : ℕ → ℤ} {Mx : ℤ} {st : Option ℕ × Option ℕ × Bool} (hS : o + 18 ≤ L.NS) (hsB : sB < L.NS)
    (hBo : sB < o + 6 ∨ o + 18 ≤ sB) (hz : σ.sc (o + 6) = 0) (h1 : σ.sc (o + 7) = 1) (hA : σ.sc (o + 8) = al t)
    (hBv : σ.sc sB = be t) (hst : F1In al be o st σ) (bal : ∀ i, |al i| ≤ Mx) (bbe : ∀ i, |be i| ≤ Mx)
    (hM1 : 1 ≤ Mx) (hM : Mx * Mx < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xf1step L o sB) σ 12 (fun σ' => F1In al be o (f1step al be st t) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => o + 9 ≤ y ∧ y < o + 18) (fun _ => False) (fun _ _ => False) σ σ') := by
  have hMM : Mx ≤ Mx * Mx := le_mul_of_one_le_left (by omega) hM1
  have hMl : Mx < 2 ^ ℓ := lt_of_le_of_lt hMM hM
  have bz : |σ.sc (o + 6)| < 2 ^ ℓ := by rw [hz, abs_zero]; positivity
  have hℓ1 : (1 : ℤ) < 2 ^ ℓ := lt_of_le_of_lt (by nlinarith) hM
  have b1r : (1 : ℝ) < 2 ^ ℓ := by exact_mod_cast hℓ1
  have b1 : |σ.sc (o + 7)| < 2 ^ ℓ := by rw [h1, abs_one]; exact b1r
  have bA : |σ.sc (o + 8)| < 2 ^ ℓ := by rw [hA]; exact abs_cast_lt_of (bal t) hMl
  have bB : |σ.sc sB| < 2 ^ ℓ := by rw [hBv]; exact abs_cast_lt_of (bbe t) hMl
  have bprod : ∀ x y : ℤ, |x| ≤ Mx → |y| ≤ Mx → |x * y| < 2 ^ ℓ := fun x y hx hy => by
    rw [abs_mul]; exact lt_of_le_of_lt (mul_le_mul hx hy (abs_nonneg _) (by omega)) hM
  obtain ⟨st1, st2, st3⟩ := st
  obtain ⟨hlo, hhi, hbad⟩ := hst
  simp only at hlo hhi hbad
  have F0 := FrameA.refl (fun y => o + 9 ≤ y ∧ y < o + 18) (fun _ => False) (fun _ _ => False) σ
  have sB9 : ∀ k, 9 ≤ k → k < 18 → sB ≠ o + k := fun k h1 h2 => by omega
  have sB9' : sB ≠ o + 9 := sB9 9 (by omega) (by omega)
  have sB10 : sB ≠ o + 10 := sB9 10 (by omega) (by omega)
  have sB12 : sB ≠ o + 12 := sB9 12 (by omega) (by omega)
  have sB13 : sB ≠ o + 13 := sB9 13 (by omega) (by omega)
  have sB16 : sB ≠ o + 16 := sB9 16 (by omega) (by omega)
  have sB17 : sB ≠ o + 17 := sB9 17 (by omega) (by omega)
  rcases lt_trichotomy (al t) 0 with hneg | hzero | hpos
  · -- `α_t < 0`: the lower end
    rw [f1step_neg hneg]
    have c1 : σ.sc (o + 8) < σ.sc (o + 6) := by rw [hA, hz]; exact_mod_cast hneg
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) bA bz c1 (K := 11) ?_) (by omega) (fun _ h => h)
    unfold xf1lo
    cases st1 with
    | none =>
      have c2 : σ.sc (o + 9) < σ.sc (o + 7) := by rw [hlo, h1]; norm_num
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [hlo, abs_zero]; positivity) b1 c2 (K := 3) ?_)
        (by omega) (fun _ h => h)
      refine XV.seq (K₂ := 2) (XV.cpy hL (x := o + 9) (y := o + 7) (z := o + 6) (by omega) (by omega) (by omega) hz b1)
        fun σ1 e1 => ?_
      subst e1
      refine XV.seq (K₂ := 1) (XV.cpy hL (x := o + 10) (y := o + 8) (z := o + 6) (by omega) (by omega) (by omega)
        (by simp [hz]) (by simpa using bA)) fun σ2 e2 => ?_
      subst e2
      refine XV.mono (XV.cpy hL (x := o + 11) (y := sB) (z := o + 6) (by omega) hsB (by omega)
        (by simp [hz]) (by simpa [sB9', sB10] using bB)) le_rfl
        fun σ3 e3 => ?_
      subst e3
      refine ⟨⟨?_, ?_⟩, rfl, ?_⟩
      · simp only
        refine ⟨by simp [h1], by simp [hA], by simp [sB9', sB10, hBv]⟩
      · simp only
        refine ⟨?_, by simp [hbad]⟩
        cases st2 with
        | none => simpa using hhi
        | some k => simpa using hhi
      · exact ((F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
    | some k =>
      obtain ⟨p9, p10, p11⟩ := hlo
      have c2 : ¬ σ.sc (o + 9) < σ.sc (o + 7) := by rw [p9, h1]; norm_num
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [p9, abs_one]; exact b1r) b1 c2 (K := 9) ?_)
        (by omega) (fun _ h => h)
      refine XV.seq (K₂ := 8) (XV.mulI hL (x := o + 16) (a := o + 11) (b := o + 8) (u := be k) (v := al t) (by omega)
        (by omega) (by omega) p11 hA (lt_of_le_of_lt (bbe k) hMl) (lt_of_le_of_lt (bal t) hMl)
        (bprod _ _ (bbe k) (bal t))) fun σ1 e1 => ?_
      subst e1
      refine XV.seq (K₂ := 7) (XV.mulI hL (x := o + 17) (a := sB) (b := o + 10) (u := be t) (v := al k) (by omega)
        hsB (by omega) (by simp [sB16, hBv]) (by simp [p10])
        (lt_of_le_of_lt (bbe t) hMl) (lt_of_le_of_lt (bal k) hMl) (bprod _ _ (bbe t) (bal k))) fun σ2 e2 => ?_
      subst e2
      have qkt : |((be k * al t : ℤ) : ℝ)| < 2 ^ ℓ := abs_cast_lt_of le_rfl (bprod _ _ (bbe k) (bal t))
      have qtk : |((be t * al k : ℤ) : ℝ)| < 2 ^ ℓ := abs_cast_lt_of le_rfl (bprod _ _ (bbe t) (bal k))
      by_cases hc : be k * al t < be t * al k
      · have c3 : ((σ.setSc (o + 16) ((be k * al t : ℤ) : ℝ)).setSc (o + 17) ((be t * al k : ℤ) : ℝ)).sc (o + 16) <
            ((σ.setSc (o + 16) ((be k * al t : ℤ) : ℝ)).setSc (o + 17) ((be t * al k : ℤ) : ℝ)).sc (o + 17) := by
          simp; exact_mod_cast hc
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa using qkt)
          (by simpa using qtk) c3
          (K := 2) ?_) (by omega) (fun _ h => h)
        refine XV.seq (K₂ := 1) (XV.cpy hL (x := o + 10) (y := o + 8) (z := o + 6) (by omega) (by omega) (by omega)
          (by simp [hz]) (by simpa using bA)) fun σ3 e3 => ?_
        subst e3
        refine XV.mono (XV.cpy hL (x := o + 11) (y := sB) (z := o + 6) (by omega) hsB (by omega)
          (by simp [hz]) (by simpa [sB10, sB16, sB17] using bB)) le_rfl fun σ4 e4 => ?_
        subst e4
        refine ⟨⟨?_, ?_⟩, rfl, ?_⟩
        · simp only [hc, ite_true]
          refine ⟨by simp [p9], by simp [hA], by simp [sB10, sB16, sB17, hBv]⟩
        · simp only
          refine ⟨?_, by simp [hbad]⟩
          cases st2 with
          | none => simpa using hhi
          | some k => simpa using hhi
        · exact (((F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩
            _).setSc ⟨by omega, by omega⟩ _
      · have c3 : ¬ ((σ.setSc (o + 16) ((be k * al t : ℤ) : ℝ)).setSc (o + 17) ((be t * al k : ℤ) : ℝ)).sc
            (o + 16) < ((σ.setSc (o + 16) ((be k * al t : ℤ) : ℝ)).setSc (o + 17) ((be t * al k : ℤ) : ℝ)).sc
            (o + 17) := by
          simp; exact_mod_cast not_lt.1 hc
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa using qkt)
          (by simpa using qtk) c3
          (XV.skip _)) (by omega) fun σ3 e3 => ?_
        subst e3
        refine ⟨⟨?_, ?_⟩, rfl, ?_⟩
        · simp only [hc, ite_false]
          exact ⟨by simp [p9], by simp [p10], by simp [p11]⟩
        · simp only
          refine ⟨?_, by simp [hbad]⟩
          cases st2 with
          | none => simpa using hhi
          | some k => simpa using hhi
        · exact (F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
  · -- `α_t = 0`: the bad-row flag
    rw [f1step_zero hzero]
    have c1 : ¬ σ.sc (o + 8) < σ.sc (o + 6) := by rw [hA, hz, hzero]; simp
    have c2 : ¬ σ.sc (o + 6) < σ.sc (o + 8) := by rw [hA, hz, hzero]; simp
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) bA bz c1 (K := 4) (XV.ifS_f hL (by omega) (by omega) bz bA c2
      (K := 2) ?_)) (by omega) (fun _ h => h)
    unfold xf1zero
    by_cases hb : be t < 0
    · have c3 : σ.sc sB < σ.sc (o + 6) := by rw [hBv, hz]; exact_mod_cast hb
      refine XV.mono (XV.ifS_t hL hsB (by omega) bB bz c3 (XV.cpy hL (x := o + 15) (y := o + 7) (z := o + 6)
        (by omega) (by omega) (by omega) hz b1)) le_rfl fun σ1 e1 => ?_
      subst e1
      refine ⟨⟨?_, ?_, by simp [h1, hb]⟩, rfl, F0.setSc ⟨by omega, by omega⟩ _⟩
      · cases st1 with
        | none => simpa using hlo
        | some i => simpa using hlo
      · cases st2 with
        | none => simpa using hhi
        | some k => simpa using hhi
    · have c3 : ¬ σ.sc sB < σ.sc (o + 6) := by rw [hBv, hz]; exact_mod_cast hb
      refine XV.mono (XV.ifS_f hL hsB (by omega) bB bz c3 (XV.skip _)) (by omega) fun σ1 e1 => ?_
      subst e1
      exact ⟨⟨hlo, hhi, by simp [hbad, hb]⟩, rfl, F0⟩
  · -- `α_t > 0`: the upper end
    rw [f1step_pos hpos]
    have c1 : ¬ σ.sc (o + 8) < σ.sc (o + 6) := by rw [hA, hz]; exact_mod_cast not_lt.2 hpos.le
    have c2 : σ.sc (o + 6) < σ.sc (o + 8) := by rw [hA, hz]; exact_mod_cast hpos
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) bA bz c1 (K := 10) (XV.ifS_t hL (by omega) (by omega) bz bA c2
      (K := 9) ?_)) (by omega) (fun _ h => h)
    unfold xf1hi
    cases st2 with
    | none =>
      have c3 : σ.sc (o + 12) < σ.sc (o + 7) := by rw [hhi, h1]; norm_num
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [hhi, abs_zero]; positivity) b1 c3 (K := 3) ?_)
        (by omega) (fun _ h => h)
      refine XV.seq (K₂ := 2) (XV.cpy hL (x := o + 12) (y := o + 7) (z := o + 6) (by omega) (by omega) (by omega) hz b1)
        fun σ1 e1 => ?_
      subst e1
      refine XV.seq (K₂ := 1) (XV.cpy hL (x := o + 13) (y := o + 8) (z := o + 6) (by omega) (by omega) (by omega)
        (by simp [hz]) (by simpa using bA)) fun σ2 e2 => ?_
      subst e2
      refine XV.mono (XV.cpy hL (x := o + 14) (y := sB) (z := o + 6) (by omega) hsB (by omega)
        (by simp [hz]) (by simpa [sB12, sB13] using bB)) le_rfl
        fun σ3 e3 => ?_
      subst e3
      refine ⟨⟨?_, ?_, by simp [hbad]⟩, rfl, ?_⟩
      · cases st1 with
        | none => simpa using hlo
        | some i => simpa using hlo
      · simp only
        exact ⟨by simp [h1], by simp [hA], by simp [sB12, sB13, hBv]⟩
      · exact ((F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
    | some k =>
      obtain ⟨p12, p13, p14⟩ := hhi
      have c3 : ¬ σ.sc (o + 12) < σ.sc (o + 7) := by rw [p12, h1]; norm_num
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [p12, abs_one]; exact b1r) b1 c3 (K := 6) ?_)
        (by omega) (fun _ h => h)
      refine XV.seq (K₂ := 5) (XV.mulI hL (x := o + 16) (a := sB) (b := o + 13) (u := be t) (v := al k) (by omega)
        hsB (by omega) hBv p13 (lt_of_le_of_lt (bbe t) hMl) (lt_of_le_of_lt (bal k) hMl)
        (bprod _ _ (bbe t) (bal k))) fun σ1 e1 => ?_
      subst e1
      refine XV.seq (K₂ := 4) (XV.mulI hL (x := o + 17) (a := o + 14) (b := o + 8) (u := be k) (v := al t) (by omega)
        (by omega) (by omega) (by simp [p14]) (by simp [hA])
        (lt_of_le_of_lt (bbe k) hMl) (lt_of_le_of_lt (bal t) hMl) (bprod _ _ (bbe k) (bal t))) fun σ2 e2 => ?_
      subst e2
      have qkt : |((be k * al t : ℤ) : ℝ)| < 2 ^ ℓ := abs_cast_lt_of le_rfl (bprod _ _ (bbe k) (bal t))
      have qtk : |((be t * al k : ℤ) : ℝ)| < 2 ^ ℓ := abs_cast_lt_of le_rfl (bprod _ _ (bbe t) (bal k))
      by_cases hc : be t * al k < be k * al t
      · have c4 : ((σ.setSc (o + 16) ((be t * al k : ℤ) : ℝ)).setSc (o + 17) ((be k * al t : ℤ) : ℝ)).sc (o + 16) <
            ((σ.setSc (o + 16) ((be t * al k : ℤ) : ℝ)).setSc (o + 17) ((be k * al t : ℤ) : ℝ)).sc (o + 17) := by
          simp; exact_mod_cast hc
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa using qtk)
          (by simpa using qkt) c4
          (K := 2) ?_) (by omega) (fun _ h => h)
        refine XV.seq (K₂ := 1) (XV.cpy hL (x := o + 13) (y := o + 8) (z := o + 6) (by omega) (by omega) (by omega)
          (by simp [hz]) (by simpa using bA)) fun σ3 e3 => ?_
        subst e3
        refine XV.mono (XV.cpy hL (x := o + 14) (y := sB) (z := o + 6) (by omega) hsB (by omega)
          (by simp [hz]) (by simpa [sB13, sB16, sB17] using bB)) le_rfl fun σ4 e4 => ?_
        subst e4
        refine ⟨⟨?_, ?_, by simp [hbad]⟩, rfl, ?_⟩
        · cases st1 with
          | none => simpa using hlo
          | some i => simpa using hlo
        · simp only [hc, ite_true]
          exact ⟨by simp [p12], by simp [hA], by simp [sB13, sB16, sB17, hBv]⟩
        · exact (((F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩
            _).setSc ⟨by omega, by omega⟩ _
      · have c4 : ¬ ((σ.setSc (o + 16) ((be t * al k : ℤ) : ℝ)).setSc (o + 17) ((be k * al t : ℤ) : ℝ)).sc
            (o + 16) < ((σ.setSc (o + 16) ((be t * al k : ℤ) : ℝ)).setSc (o + 17) ((be k * al t : ℤ) : ℝ)).sc
            (o + 17) := by
          simp; exact_mod_cast not_lt.1 hc
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa using qtk)
          (by simpa using qkt) c4
          (XV.skip _)) (by omega) fun σ3 e3 => ?_
        subst e3
        refine ⟨⟨?_, ?_, by simp [hbad]⟩, rfl, ?_⟩
        · cases st1 with
          | none => simpa using hlo
          | some i => simpa using hlo
        · simp only [hc, ite_false]
          exact ⟨by simp [p12], by simp [p13], by simp [p14]⟩
        · exact (F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _

theorem F1In.congr {al be : ℕ → ℤ} {o : ℕ} {st : Option ℕ × Option ℕ × Bool} {σ σ' : Env d}
    (h : ∀ k, 9 ≤ k → k ≤ 15 → σ'.sc (o + k) = σ.sc (o + k)) (hs : F1In al be o st σ) : F1In al be o st σ' := by
  simp only [F1In] at hs ⊢
  rw [h 9 (by omega) (by omega), h 10 (by omega) (by omega), h 11 (by omega) (by omega),
    h 12 (by omega) (by omega), h 13 (by omega) (by omega), h 14 (by omega) (by omega), h 15 (by omega) (by omega)]
  exact hs

/-! ## The rows -/

set_option maxHeartbeats 1000000 in
/-- **An input row on the machine** (`xinRow` on the input cells of `ctxOf`): row `k < m` cleared,
`frAl A b k` into the cells `0, ..., d - 1` of `aRow`, `frBe A b k * D` into `sB` (`D` in `sDn`). -/
theorem XV.frRow {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none k : ℕ} {D : ℤ}
    (hsD : sD < L.NS) (hsT : sT < L.NS) (hsN : sN < L.NS) (hsQ : sQ < L.NS) (hsB : sB < L.NS)
    (hsDn : sDn < L.NS) (hss : [sD, sT, sN, sQ, sB, sDn].Nodup) (hR : aRow < L.NA)
    (hnI : nI < L.NN) (hnT : nT < L.NN) (hnj : nj < L.NN) (hnd : nd < L.NN) (hn1 : nd1 < L.NN)
    (hnk : nk < L.NN) (hno : none < L.NN) (hne : [nI, nT, nj, nd, nd1, nk, none].Nodup)
    (hσd : σ.nat nd = d) (hσd1 : σ.nat nd1 = d + 1) (hσk : σ.nat nk = k) (hσ1 : σ.nat none = 1)
    (hσDn : σ.sc sDn = D) (hk : k < m) (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa)
    (hda : d * d + d < 2 ^ ℓa) (hD1 : 1 ≤ D) (hb : (frMhat A b : ℤ) ^ (d + 2) * D < 2 ^ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xinRow L sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none) σ (18 * d + 28)
      (fun σ' => (∀ j : Fin d, σ'.arr aRow j = frAl A b ⟨k, hk⟩ j) ∧
        σ'.sc sB = ((frBe A b ⟨k, hk⟩ * D : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB) (fun j => j = nI ∨ j = nT ∨ j = nj)
          (fun b k' => b = aRow ∧ k' < d) σ σ') := by
  obtain ⟨hM1, -, -⟩ := frMhat_le A b
  have hM1' : (1 : ℤ) ≤ frMhat A b := by exact_mod_cast hM1
  refine XV.mono (XV.inRow hL (k := k) (Mh := (frMhat A b : ℤ)) (D := D)
    (Nm := fun j => (BitRAM.entry A b ⟨k, hk⟩ j).num) (Dn := fun j => (BitRAM.entry A b ⟨k, hk⟩ j).den)
    hsD hsT hsN hsQ hsB hsDn hss hR hnI hnT hnj hnd hn1 hnk hno hne hσd hσd1 hσk hσ1 hσDn ?_ ?_ hda ?_ ?_ hD1 hM1'
    (fun j _ => (entry_le A b _ j).1) (fun j _ => (entry_le A b _ j).2) hb) le_rfl ?_
  · show 3 + 2 * ((d + 1) * (k + 1)) ≤ offOf d m
    unfold offOf
    have := Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ m by omega)
    nlinarith
  · have := Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ m + 1 by omega)
    omega
  · intro j hj; exact BitRAM.Conj1BitSanity.inputMem_num (n := n) A b ⟨k, hk⟩ j hj
  · intro j hj; exact BitRAM.Conj1BitSanity.inputMem_den (n := n) A b ⟨k, hk⟩ j hj
  · rintro σ' ⟨hrow, hsB', hdr, hF⟩
    refine ⟨fun j => ?_, ?_, hdr, hF⟩
    · rw [hrow j j.2, ← TriM.frAl_inp]
    · rw [hsB', ← TriM.frBe_inp]

/-! ## The scan -/

/-- One row of the scan: the row (`xinRow`, `D = 1`), `α_t` into `o + 8`, the step. Registers: `rE, rE + 1, rE + 2`
for `xinRow`, `rE + 3` holds `d + 1`, `rE + 4` the row, `rE + 5` holds `1`, `rE + 6` holds `0`. -/
def xf1row (L : Layout) (B : PrBlk) : XCmd :=
  .seq (xinRow L B.o (B.o + 1) (B.o + 2) (B.o + 3) (B.o + 4) (B.o + 5) (B.aW + 1) B.rE (B.rE + 1) (B.rE + 2) B.rd
    (B.rE + 3) (B.rE + 4) (B.rE + 5))
  (.seq (toX (VL.aget L (B.o + 8) (B.aW + 1) (B.rE + 6))) (xf1step L B.o (B.o + 4)))

/-- The scan over the `m` input rows. -/
def xf1scan (L : Layout) (B : PrBlk) : XCmd := xforN (B.rE + 4) B.rm (B.rE + 5) (xf1row L B)

/-- The slots the scan writes. -/
abbrev f1S (o y : ℕ) : Prop := (o ≤ y ∧ y ≤ o + 4) ∨ (o + 8 ≤ y ∧ y < o + 18)

/-- The registers the scan writes. -/
abbrev f1N (r j : ℕ) : Prop := j = r ∨ j = r + 1 ∨ j = r + 2 ∨ j = r + 4

set_option maxHeartbeats 4000000 in
/-- **The scan on the machine** (`d = 1`): `f1scan` over the cleared input rows. -/
theorem XV.f1scan {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} (hd : d = 1) (hS : B.o + 18 ≤ L.NS)
    (hN : B.rE + 7 ≤ L.NN) (hA : B.aW + 2 ≤ L.NA) (hrd : B.rd < B.rE) (hrm : B.rm < B.rE)
    (e_d : σ.nat B.rd = d) (e_m : σ.nat B.rm = m) (e5 : σ.sc (B.o + 5) = 1) (e6 : σ.sc (B.o + 6) = 0)
    (e7 : σ.sc (B.o + 7) = 1) (n3 : σ.nat (B.rE + 3) = d + 1) (n5 : σ.nat (B.rE + 5) = 1)
    (n6 : σ.nat (B.rE + 6) = 0) (h0 : F1In (frAlN A b 0) (frBeN A b) B.o (none, none, false) σ)
    (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hma : m < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa)
    (hb : (frMhat A b : ℤ) ^ 4 < 2 ^ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xf1scan L B) σ (m * ((18 * d + 28) + (2 + 12) + 3) + 3) (fun σ' =>
      F1In (frAlN A b 0) (frBeN A b) B.o (Transfer.f1scan (frAlN A b 0) (frBeN A b) m) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (f1S B.o) (f1N B.rE) (fun b' _ => b' = B.aW + 1) σ σ') := by
  subst hd
  obtain ⟨hM1, -, -⟩ := frMhat_le A b
  have hM1' : (1 : ℤ) ≤ frMhat A b := by exact_mod_cast hM1
  set M : ℤ := (frMhat A b : ℤ) with hMdef
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1'
  have hMM : M ^ 2 * M ^ 2 < 2 ^ ℓ := by rw [← pow_add]; exact hb
  have hb3 : M ^ (1 + 2) * 1 < 2 ^ ℓ := by
    rw [mul_one]; exact lt_of_le_of_lt (pow_le_pow_right₀ hM1' (by norm_num)) hb
  let J : ℕ → Env 1 → Prop := fun t σ' =>
    F1In (frAlN A b 0) (frBeN A b) B.o (Transfer.f1scan (frAlN A b 0) (frBeN A b) t) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (f1S B.o) (f1N B.rE) (fun b' _ => b' = B.aW + 1) σ σ'
  have F0 := FrameA.refl (f1S B.o) (f1N B.rE) (fun b' _ => b' = B.aW + 1) σ
  refine XV.mono (XV.forN hL (i := B.rE + 4) (n := B.rm) (one := B.rE + 5) (by omega) (by omega) (by omega)
    (by omega) (by omega) m ((18 * 1 + 28) + (2 + 12)) hma J σ e_m n5
    ⟨F1In.congr (fun k _ _ => by simp) h0, by simp, F0.setNat (Or.inr (Or.inr (Or.inr rfl))) 0⟩ ?_) le_rfl
    (fun σ' h => h.1)
  intro t ht σ' ⟨hI, hdr, hF⟩ hσt hσm hσ1
  -- the fixed cells
  have s5 : σ'.sc (B.o + 5) = 1 := by rw [hF.2.1 _ (by simp only [f1S]; omega), e5]
  have s6 : σ'.sc (B.o + 6) = 0 := by rw [hF.2.1 _ (by simp only [f1S]; omega), e6]
  have s7 : σ'.sc (B.o + 7) = 1 := by rw [hF.2.1 _ (by simp only [f1S]; omega), e7]
  have r_d : σ'.nat B.rd = 1 := by rw [hF.1 _ (by simp only [f1N]; omega), e_d]
  have r3 : σ'.nat (B.rE + 3) = 1 + 1 := by rw [hF.1 _ (by simp only [f1N]; omega), n3]
  have r6 : σ'.nat (B.rE + 6) = 0 := by rw [hF.1 _ (by simp only [f1N]; omega), n6]
  -- the row
  refine XV.seq (K₂ := 2 + 12) (XV.frRow hL (k := t) (D := 1) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by simp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by simp; omega) r_d r3 hσt hσ1
    (by rw [s5, Int.cast_one]) ht hka hda le_rfl hb3) fun σ1 ⟨w1, b1, d1, F1⟩ => ?_
  have q1 : ∀ k, 6 ≤ k → σ1.sc (B.o + k) = σ'.sc (B.o + k) := fun k hk => F1.2.1 _ (by omega)
  have m1 : ∀ j, j ≠ B.rE → j ≠ B.rE + 1 → j ≠ B.rE + 2 → σ1.nat j = σ'.nat j := fun j h1 h2 h3 =>
    F1.1 _ (by omega)
  -- `α_t`
  have a0 : σ1.arr (B.aW + 1) (σ1.nat (B.rE + 6)) = frAlN A b 0 t := by
    rw [m1 _ (by omega) (by omega) (by omega), r6]
    have := w1 ⟨0, by omega⟩
    simp only [Fin.val_mk] at this
    rw [this]; unfold frAlN; rw [dite_eq_left ⟨ht, by omega⟩]
  have bA : |(frAlN A b 0 t : ℝ)| < 2 ^ ℓ := abs_cast_lt_of ((frAlN_le A b 0 t).trans_eq (by ring))
    (lt_of_le_of_lt (le_mul_of_one_le_right (by positivity) hM2) hMM)
  refine XV.seq (K₂ := 12) (XV.aget hL (x := B.o + 8) (a := B.aW + 1) (i := B.rE + 6) (by omega) (by omega)
    (by omega) (by rw [m1 _ (by omega) (by omega) (by omega), r6]; unfold asz; omega) (by rw [a0]; exact bA))
    fun σ2 e2 => ?_
  subst e2
  -- the step
  refine XV.mono (XV.f1step hL (o := B.o) (sB := B.o + 4) (t := t) (Mx := M ^ 2) (by omega) (by omega)
    (by omega) (by simp [q1 6 (by omega), s6]) (by simp [q1 7 (by omega), s7]) (by simp [a0])
    (by simp [b1]; unfold frBeN; rw [dite_eq_left ht])
    (F1In.congr (fun k hk hk' => by rw [sc_setSc_ne _ (by omega), q1 k (by omega)]) hI)
    (fun i => frAlN_le A b 0 i) (fun i => frBeN_le A b i) hM2 hMM) le_rfl ?_
  rintro σ3 ⟨hI3, d3, F3⟩
  have n3' : ∀ j, σ3.nat j = σ1.nat j := fun j => by rw [F3.1 j id]; simp
  refine ⟨by rw [n3', m1 _ (by omega) (by omega) (by omega), hσt], by rw [n3', m1 _ (by omega) (by omega) (by omega),
    hσm], by rw [n3', m1 _ (by omega) (by omega) (by omega), hσ1], ?_, by simp [d3, d1, hdr], ?_⟩
  · exact F1In.congr (fun k _ _ => by simp) hI3
  · refine ((hF.trans (F1.mono (fun y h => by simp only [f1S]; omega) (fun j h => by simp only [f1N]; omega)
      (fun b' k h => h.1))).trans ?_).setNat (Or.inr (Or.inr (Or.inr rfl))) _
    exact ((FrameA.refl _ _ _ σ1).setSc (by simp only [f1S]; omega) _).trans
      (F3.mono (fun y h => by simp only [f1S]; omega) (fun _ h => h.elim) (fun _ _ h => h.elim))

/-! ## The output -/

/-- The midpoint: from `P, U, V` in the slots `o + 16, o + 17, o + 18`, `-(P + P)` into the cell `0` of `aW` and
`-(V + U)` into the cell `1` (`i0, i1` hold `0, 1`). -/
def xf1mid (L : Layout) (o aW i0 i1 : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add (o + 20) (o + 18) (o + 17)))
  (.seq (toX (VL.sop2 L .sub (o + 20) (o + 6) (o + 20)))
  (.seq (toX (VL.sop2 L .add (o + 21) (o + 16) (o + 16)))
  (.seq (toX (VL.sop2 L .sub (o + 21) (o + 6) (o + 21)))
  (.seq (toX (VL.aset L aW i0 (o + 21))) (toX (VL.aset L aW i1 (o + 20)))))))

/-- The gap test `α_i α_k < β_k α_i - β_i α_k` (the gap below `1`, `gap_lt_iff`), else the midpoint. -/
def xf1gap (L : Layout) (o aW i0 i1 : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .mul (o + 16) (o + 10) (o + 13)))
  (.seq (toX (VL.sop2 L .mul (o + 17) (o + 14) (o + 10)))
  (.seq (toX (VL.sop2 L .mul (o + 18) (o + 11) (o + 13)))
  (.seq (toX (VL.sop2 L .sub (o + 19) (o + 17) (o + 18)))
  (xifS L (o + 16) (o + 19) .skip (xf1mid L o aW i0 i1)))))

/-- The read-off: `0 = 0/1` into the cells `0, 1` of `aW`, then the midpoint when both ends are present, no bad row
was seen and the gap is at least `1`. -/
def xf1out (L : Layout) (o aW i0 i1 : ℕ) : XCmd :=
  .seq (toX (VL.aset L aW i0 (o + 7)))
  (.seq (toX (VL.aset L aW i1 (o + 6)))
  (xifS L (o + 6) (o + 9) (xifS L (o + 6) (o + 12) (xifS L (o + 15) (o + 7) (xf1gap L o aW i0 i1) .skip) .skip)
    .skip))

set_option maxHeartbeats 1000000 in
/-- **The midpoint on the machine.** -/
theorem XV.f1mid {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o aW i0 i1 : ℕ}
    {P U V Q : ℤ} (hd : 1 ≤ d) (hS : o + 22 ≤ L.NS) (hA : aW < L.NA) (hi0 : i0 < L.NN) (hi1 : i1 < L.NN)
    (n0 : σ.nat i0 = 0) (n1 : σ.nat i1 = 1) (hz : σ.sc (o + 6) = 0) (hP : σ.sc (o + 16) = P)
    (hU : σ.sc (o + 17) = U) (hV : σ.sc (o + 18) = V) (bP : |P| ≤ Q) (bU : |U| ≤ Q) (bV : |V| ≤ Q)
    (hQ : 2 * Q < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xf1mid L o aW i0 i1) σ 8 (fun σ' => σ'.arr aW 0 = ((-(P + P) : ℤ) : ℝ) ∧
      σ'.arr aW 1 = ((-(V + U) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => o + 20 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ') := by
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans bP
  have l1 : ∀ x : ℤ, |x| ≤ Q → |x| < 2 ^ ℓ := fun x h => by linarith
  have l2 : ∀ x y : ℤ, |x| ≤ Q → |y| ≤ Q → |x + y| < 2 ^ ℓ := fun x y hx hy => by
    have := abs_add_le x y; linarith
  have l3 : ∀ x y : ℤ, |x| ≤ Q → |y| ≤ Q → |0 - (x + y)| < 2 ^ ℓ := fun x y hx hy => by
    rw [zero_sub, abs_neg]; exact l2 x y hx hy
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have ha0 : 0 < asz d := by unfold asz; nlinarith
  have ha1 : 1 < asz d := by unfold asz; nlinarith
  refine XV.seq (K₂ := 7) (XV.addI hL (x := o + 20) (a := o + 18) (b := o + 17) (by omega) (by omega) (by omega)
    hV hU (l1 V bV) (l1 U bU) (l2 V U bV bU)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (K₂ := 6) (XV.subI hL (x := o + 20) (a := o + 6) (b := o + 20) (u := 0) (v := V + U) (by omega)
    (by omega) (by omega) (by simp [hz]) (by simp) b0 (l2 V U bV bU) (l3 V U bV bU)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 5) (XV.addI hL (x := o + 21) (a := o + 16) (b := o + 16) (u := P) (v := P) (by omega)
    (by omega) (by omega) (by simp [hP]) (by simp [hP]) (l1 P bP) (l1 P bP) (l2 P P bP bP)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (K₂ := 4) (XV.subI hL (x := o + 21) (a := o + 6) (b := o + 21) (u := 0) (v := P + P) (by omega)
    (by omega) (by omega) (by simp [hz]) (by simp) b0 (l2 P P bP bP) (l3 P P bP bP)) fun σ4 e4 => ?_
  subst e4
  have q21 : |((0 - (P + P) : ℤ) : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (l3 P P bP bP)
  have q20 : |((0 - (V + U) : ℤ) : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (l3 V U bV bU)
  refine XV.seq (K₂ := 2) (XV.aset hL (a := aW) (i := i0) (x := o + 21) hA hi0 (by omega) (by simp [n0]; omega)
    (by simpa using q21)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.aset hL (a := aW) (i := i1) (x := o + 20) hA hi1 (by omega) (by simp [n1]; omega)
    (by simpa using q20)) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨by simp [n0, n1], by simp [n0, n1], by simp, ?_⟩
  exact ((((FrameA.refl _ _ _ σ).setSc ⟨le_rfl, by omega⟩ _).setSc ⟨le_rfl, by omega⟩ _).setSc ⟨by omega, by omega⟩
    _).setSc ⟨by omega, by omega⟩ _ |>.setArr ⟨rfl, by simp [n0]⟩ _ |>.setArr ⟨rfl, by simp [n1]⟩ _

set_option maxHeartbeats 2000000 in
/-- **The gap test and the midpoint on the machine**, the lower end `(α_i, β_i)` in the slots `o + 10, o + 11`, the
upper end `(α_k, β_k)` in `o + 13, o + 14`. -/
theorem XV.f1gap {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o aW i0 i1 : ℕ}
    {ai bi ak bk Mx : ℤ} (hd : 1 ≤ d) (hS : o + 22 ≤ L.NS) (hA : aW < L.NA) (hi0 : i0 < L.NN) (hi1 : i1 < L.NN)
    (n0 : σ.nat i0 = 0) (n1 : σ.nat i1 = 1) (hz : σ.sc (o + 6) = 0) (h10 : σ.sc (o + 10) = ai)
    (h11 : σ.sc (o + 11) = bi) (h13 : σ.sc (o + 13) = ak) (h14 : σ.sc (o + 14) = bk) (hi : ai < 0) (hk : 0 < ak)
    (bai : |ai| ≤ Mx) (bbi : |bi| ≤ Mx) (bak : |ak| ≤ Mx) (bbk : |bk| ≤ Mx) (hM : 2 * (Mx * Mx) < 2 ^ ℓ)
    (Q : Env d → Prop) (hQ0 : (bk : ℚ) / ak - bi / ai < 1 → ∀ σ', σ'.draws = σ.draws →
      FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ' →
      σ'.arr aW 0 = σ.arr aW 0 → σ'.arr aW 1 = σ.arr aW 1 → Q σ')
    (hQ1 : ¬ (bk : ℚ) / ak - bi / ai < 1 → ∀ σ', σ'.draws = σ.draws →
      FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ' →
      σ'.arr aW 0 = ((-2 * ai * ak : ℤ) : ℝ) → σ'.arr aW 1 = ((-(bi * ak + bk * ai) : ℤ) : ℝ) → Q σ') :
    XRunsB L X ℓa ℓ (xf1gap L o aW i0 i1) σ 14 Q := by
  have hM0 : 0 ≤ Mx := (abs_nonneg _).trans bai
  have hMM : Mx * Mx ≤ 2 * (Mx * Mx) := by nlinarith
  have l1 : ∀ x : ℤ, |x| ≤ Mx → |x| < 2 ^ ℓ := fun x h => by nlinarith
  have lm : ∀ x y : ℤ, |x| ≤ Mx → |y| ≤ Mx → |x * y| ≤ Mx * Mx := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hM0
  have lm' : ∀ x y : ℤ, |x| ≤ Mx → |y| ≤ Mx → |x * y| < 2 ^ ℓ := fun x y hx hy => by
    have := lm x y hx hy; linarith
  have F0 := FrameA.refl (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ
  refine XV.seq (K₂ := 13) (XV.mulI hL (x := o + 16) (a := o + 10) (b := o + 13) (by omega) (by omega) (by omega)
    h10 h13 (l1 _ bai) (l1 _ bak) (lm' _ _ bai bak)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (K₂ := 12) (XV.mulI hL (x := o + 17) (a := o + 14) (b := o + 10) (u := bk) (v := ai) (by omega)
    (by omega) (by omega) (by simp [h14]) (by simp [h10]) (l1 _ bbk) (l1 _ bai) (lm' _ _ bbk bai)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 11) (XV.mulI hL (x := o + 18) (a := o + 11) (b := o + 13) (u := bi) (v := ak) (by omega)
    (by omega) (by omega) (by simp [h11]) (by simp [h13]) (l1 _ bbi) (l1 _ bak) (lm' _ _ bbi bak)) fun σ3 e3 => ?_
  subst e3
  have bsub : |bk * ai - bi * ak| < 2 ^ ℓ := by
    have := abs_sub _ _ |>.trans (add_le_add (lm _ _ bbk bai) (lm _ _ bbi bak))
    linarith
  refine XV.seq (K₂ := 10) (XV.subI hL (x := o + 19) (a := o + 17) (b := o + 18) (u := bk * ai) (v := bi * ak)
    (by omega) (by omega) (by omega) (by simp) (by simp) (lm' _ _ bbk bai) (lm' _ _ bbi bak) bsub) fun σ4 e4 => ?_
  subst e4
  have q16 : |((ai * ak : ℤ) : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (lm' _ _ bai bak)
  have q19 : |((bk * ai - bi * ak : ℤ) : ℝ)| < 2 ^ ℓ := XV.abs_int_lt bsub
  by_cases hg : ai * ak < bk * ai - bi * ak
  · have c : (((((σ.setSc (o + 16) ((ai * ak : ℤ) : ℝ)).setSc (o + 17) ((bk * ai : ℤ) : ℝ)).setSc (o + 18)
        ((bi * ak : ℤ) : ℝ)).setSc (o + 19) ((bk * ai - bi * ak : ℤ) : ℝ))).sc (o + 16) <
        (((((σ.setSc (o + 16) ((ai * ak : ℤ) : ℝ)).setSc (o + 17) ((bk * ai : ℤ) : ℝ)).setSc (o + 18)
        ((bi * ak : ℤ) : ℝ)).setSc (o + 19) ((bk * ai - bi * ak : ℤ) : ℝ))).sc (o + 19) := by
      simp; exact_mod_cast hg
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa using q16) (by simpa using q19) c (XV.skip _))
      (by omega) fun σ' e => ?_
    subst e
    exact hQ0 ((gap_lt_iff bi bk ai ak hi hk).2 hg) _ (by simp)
      ((((F0.setSc ⟨le_rfl, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
        ⟨by omega, by omega⟩ _) (by simp) (by simp)
  · have c : ¬ (((((σ.setSc (o + 16) ((ai * ak : ℤ) : ℝ)).setSc (o + 17) ((bk * ai : ℤ) : ℝ)).setSc (o + 18)
        ((bi * ak : ℤ) : ℝ)).setSc (o + 19) ((bk * ai - bi * ak : ℤ) : ℝ))).sc (o + 16) <
        (((((σ.setSc (o + 16) ((ai * ak : ℤ) : ℝ)).setSc (o + 17) ((bk * ai : ℤ) : ℝ)).setSc (o + 18)
        ((bi * ak : ℤ) : ℝ)).setSc (o + 19) ((bk * ai - bi * ak : ℤ) : ℝ))).sc (o + 19) := by
      simp; exact_mod_cast (show bk * ai ≤ ai * ak + bi * ak by linarith [not_lt.1 hg])
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa using q16) (by simpa using q19) c
      (XV.f1mid hL (P := ai * ak) (U := bk * ai) (V := bi * ak) (Q := Mx * Mx) hd hS hA hi0 hi1 (by simp [n0])
        (by simp [n1]) (by simp [hz]) (by simp) (by simp) (by simp) (lm _ _ bai bak) (lm _ _ bbk bai)
        (lm _ _ bbi bak) hM)) (by omega) ?_
    rintro σ' ⟨w0, w1, dr, F⟩
    refine hQ1 (fun h => hg ((gap_lt_iff bi bk ai ak hi hk).1 h)) σ' (by simp [dr]) ?_ (by rw [w0]; push_cast; ring)
      (by rw [w1])
    exact (((((F0.setSc ⟨le_rfl, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
      ⟨by omega, by omega⟩ _).trans (F.mono (fun y h => ⟨by omega, h.2⟩) (fun _ h => h) (fun _ _ h => h)))

set_option maxHeartbeats 4000000 in
/-- **The read-off on the machine**: the point `(f1out al be st).getD 0` as `x / D`, `D` in the cell `0` of `aW` and
`x` in the cell `1`. -/
theorem XV.f1out {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o aW i0 i1 : ℕ}
    {al be : ℕ → ℤ} {Mx : ℤ} {st : Option ℕ × Option ℕ × Bool} (hd : 1 ≤ d) (hS : o + 22 ≤ L.NS) (hA : aW < L.NA)
    (hi0 : i0 < L.NN) (hi1 : i1 < L.NN) (n0 : σ.nat i0 = 0) (n1 : σ.nat i1 = 1) (hz : σ.sc (o + 6) = 0)
    (h1 : σ.sc (o + 7) = 1) (hst : F1In al be o st σ) (hlo : ∀ i, st.1 = some i → al i < 0)
    (hhi : ∀ k, st.2.1 = some k → 0 < al k) (bal : ∀ i, |al i| ≤ Mx) (bbe : ∀ i, |be i| ≤ Mx) (hM1 : 1 ≤ Mx)
    (hM : 2 * (Mx * Mx) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xf1out L o aW i0 i1) σ 21 (fun σ' => (∃ D x : ℤ, 0 < D ∧ D ≤ 2 * (Mx * Mx) ∧
      |x| ≤ 2 * (Mx * Mx) ∧ σ'.arr aW 0 = D ∧ σ'.arr aW 1 = x ∧ (x : ℚ) / D = (Transfer.f1out al be st).getD 0) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ') := by
  have hM0 : (0 : ℤ) ≤ Mx := by linarith
  have hMM : 1 ≤ Mx * Mx := by nlinarith
  have b0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have b1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact_mod_cast (by linarith : (1 : ℤ) < 2 ^ ℓ)
  have ha0 : 0 < asz d := by unfold asz; nlinarith
  have ha1 : 1 < asz d := by unfold asz; nlinarith
  have lm : ∀ x y : ℤ, |x| ≤ Mx → |y| ≤ Mx → |x * y| ≤ Mx * Mx := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hM0
  refine XV.seq (K₂ := 19) (XV.aset hL (a := aW) (i := i0) (x := o + 7) hA hi0 (by omega) (by rw [n0]; exact ha0)
    (by rw [h1]; exact b1)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (K₂ := 17) (XV.aset hL (a := aW) (i := i1) (x := o + 6) hA hi1 (by omega) (by simp [n1]; omega)
    (by simpa [hz] using b0)) fun σ2 e2 => ?_
  subst e2
  have F2 : FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ
      ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).setArr aW ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).nat i1)
        ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).sc (o + 6))) :=
    ((FrameA.refl _ _ _ σ).setArr ⟨rfl, by simp [n0]⟩ _).setArr ⟨rfl, by simp [n1]⟩ _
  have a0 : ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).setArr aW ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).nat i1)
      ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).sc (o + 6))).arr aW 0 = ((1 : ℤ) : ℝ) := by simp [n0, n1, h1]
  have a1 : ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).setArr aW ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).nat i1)
      ((σ.setArr aW (σ.nat i0) (σ.sc (o + 7))).sc (o + 6))).arr aW 1 = ((0 : ℤ) : ℝ) := by simp [n0, n1, hz]
  have hdef : ∀ σ', σ'.draws = σ.draws →
      FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ' →
      σ'.arr aW 0 = ((1 : ℤ) : ℝ) → σ'.arr aW 1 = ((0 : ℤ) : ℝ) → Transfer.f1out al be st = none →
      (∃ D x : ℤ, 0 < D ∧ D ≤ 2 * (Mx * Mx) ∧ |x| ≤ 2 * (Mx * Mx) ∧ σ'.arr aW 0 = D ∧ σ'.arr aW 1 = x ∧
        (x : ℚ) / D = (Transfer.f1out al be st).getD 0) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => o + 16 ≤ y ∧ y < o + 22) (fun _ => False) (fun b k => b = aW ∧ k < 2) σ σ' :=
    fun σ' dr F e0 e1 hn => ⟨⟨1, 0, one_pos, by linarith, by rw [abs_zero]; linarith, e0, e1, by simp [hn]⟩, dr, F⟩
  obtain ⟨st1, st2, st3⟩ := st
  obtain ⟨plo, phi, pbad⟩ := hst
  simp only at plo phi pbad hlo hhi
  cases st1 with
  | none =>
    have c : ¬ σ.sc (o + 6) < σ.sc (o + 9) := by rw [hz, plo]; exact lt_irrefl 0
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa [hz] using b0) (by simpa [plo] using b0)
      (by simpa using c) (XV.skip _)) (by omega) fun σ' e => ?_
    subst e
    exact hdef _ (by simp) F2 a0 a1 (by simp [Transfer.f1out])
  | some i =>
    obtain ⟨p9, p10, p11⟩ := plo
    have c : σ.sc (o + 6) < σ.sc (o + 9) := by rw [hz, p9]; exact zero_lt_one
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa [hz] using b0) (by simpa [p9] using b1)
      (by simpa using c) (K := 16) ?_) (by omega) (fun _ h => h)
    cases st2 with
    | none =>
      have c : ¬ σ.sc (o + 6) < σ.sc (o + 12) := by rw [hz, phi]; exact lt_irrefl 0
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa [hz] using b0) (by simpa [phi] using b0)
        (by simpa using c) (XV.skip _)) (by omega) fun σ' e => ?_
      subst e
      exact hdef _ (by simp) F2 a0 a1 (by simp [Transfer.f1out])
    | some k =>
      obtain ⟨p12, p13, p14⟩ := phi
      have c : σ.sc (o + 6) < σ.sc (o + 12) := by rw [hz, p12]; exact zero_lt_one
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa [hz] using b0) (by simpa [p12] using b1)
        (by simpa using c) (K := 15) ?_) (by omega) (fun _ h => h)
      cases st3 with
      | true =>
        have c : ¬ σ.sc (o + 15) < σ.sc (o + 7) := by rw [pbad, h1]; simp
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by simpa [pbad] using b1) (by simpa [h1] using b1)
          (by simpa using c) (XV.skip _)) (by omega) fun σ' e => ?_
        subst e
        exact hdef _ (by simp) F2 a0 a1 (by simp [Transfer.f1out])
      | false =>
        have c : σ.sc (o + 15) < σ.sc (o + 7) := by rw [pbad, h1]; simp
        have hi := hlo i rfl
        have hk := hhi k rfl
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by simpa [pbad] using b0) (by simpa [h1] using b1)
          (by simpa using c) (XV.f1gap hL (ai := al i) (bi := be i) (ak := al k) (bk := be k) (Mx := Mx) hd hS hA
            hi0 hi1 (by simp [n0]) (by simp [n1]) (by simp [hz]) (by simp [p10]) (by simp [p11]) (by simp [p13])
            (by simp [p14]) hi hk (bal i) (bbe i) (bal k) (bbe k) hM _ ?_ ?_)) (by omega) (fun _ h => h)
        · intro hg σ' dr F e0 e1
          exact hdef σ' (by rw [dr]; simp) (F2.trans F) (by rw [e0, a0]) (by rw [e1, a1]) (by simp [Transfer.f1out, hg])
        · intro hg σ' dr F e0 e1
          obtain ⟨hD, hmid⟩ := mid_eq (be i) (be k) (al i) (al k) hi hk
          have q1 := abs_le.1 (lm _ _ (bal i) (bal k))
          have q2 := lm _ _ (bbe i) (bal k)
          have q3 := lm _ _ (bbe k) (bal i)
          refine ⟨⟨-2 * al i * al k, -(be i * al k + be k * al i), hD, ?_, ?_, e0, e1, ?_⟩, by rw [dr]; simp,
            F2.trans F⟩
          · have : -2 * al i * al k = -2 * (al i * al k) := by ring
            rw [this]; linarith
          · rw [abs_neg]; exact (abs_add_le _ _).trans (by linarith)
          · simp only [Transfer.f1out, hg, ite_false, Option.getD_some]; exact hmid.symm

/-! ## The read-off F2 (`d = 1`) -/

/-- The constants of the read-off: the slots `o + 5 = 1` (the scale `D = 1` of `xinRow`), `o + 6 = 0`, `o + 7 = 1`,
the empty scan `o + 9 = o + 12 = o + 15 = 0`; the registers `rE + 3 = 2` (`d + 1`), `rE + 5 = 1`, `rE + 6 = 0`. -/
def xf1init (L : Layout) (B : PrBlk) : XCmd :=
  .seq (toX (VL.sconst L (B.o + 5) 1)) (.seq (toX (VL.sconst L (B.o + 6) 0)) (.seq (toX (VL.sconst L (B.o + 7) 1))
  (.seq (toX (VL.sconst L (B.o + 9) 0)) (.seq (toX (VL.sconst L (B.o + 12) 0)) (.seq (toX (VL.sconst L (B.o + 15) 0))
  (.seq (.prim (.frag (.nconst (B.rE + 3) 2))) (.seq (.prim (.frag (.nconst (B.rE + 5) 1)))
    (.prim (.frag (.nconst (B.rE + 6) 0))))))))))

/-- Procedure FRAME for `d = 1`: the constants, the scan, the read-off into the array `aW`. -/
def xframe1 (L : Layout) (B : PrBlk) : XCmd :=
  .seq (xf1init L B) (.seq (xf1scan L B) (xf1out L B.o B.aW (B.rE + 6) (B.rE + 5)))

set_option maxHeartbeats 2000000 in
theorem XV.f1init {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk}
    (hS : B.o + 16 ≤ L.NS) (hN : B.rE + 7 ≤ L.NN) (hℓ : 1 ≤ ℓ) (hℓa : 2 ≤ ℓa) :
    XRunsB L X ℓa ℓ (xf1init L B) σ 9 (fun σ' => σ'.sc (B.o + 5) = 1 ∧ σ'.sc (B.o + 6) = 0 ∧
      σ'.sc (B.o + 7) = 1 ∧ σ'.sc (B.o + 9) = 0 ∧ σ'.sc (B.o + 12) = 0 ∧ σ'.sc (B.o + 15) = 0 ∧
      σ'.nat (B.rE + 3) = 2 ∧ σ'.nat (B.rE + 5) = 1 ∧ σ'.nat (B.rE + 6) = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o + 5 ≤ y ∧ y < B.o + 16) (fun j => B.rE + 3 ≤ j ∧ j < B.rE + 7) (fun _ _ => False)
        σ σ') := by
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have b1 : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have a2 : 2 < 2 ^ ℓa := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓa := Nat.pow_le_pow_right (by norm_num) hℓa
  have F0 := FrameA.refl (fun y => B.o + 5 ≤ y ∧ y < B.o + 16) (fun j => B.rE + 3 ≤ j ∧ j < B.rE + 7)
    (fun _ _ => False) σ
  refine XV.seq (K₂ := 8) (XV.constI hL (x := B.o + 5) (by omega) 1 b1) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (K₂ := 7) (XV.constI hL (x := B.o + 6) (by omega) 0 b0) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 6) (XV.constI hL (x := B.o + 7) (by omega) 1 b1) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (K₂ := 5) (XV.constI hL (x := B.o + 9) (by omega) 0 b0) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (K₂ := 4) (XV.constI hL (x := B.o + 12) (by omega) 0 b0) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (K₂ := 3) (XV.constI hL (x := B.o + 15) (by omega) 0 b0) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (K₂ := 2) (XV.nconst hL (i := B.rE + 3) (by omega) 2 a2) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (K₂ := 1) (XV.nconst hL (i := B.rE + 5) (by omega) 1 (by omega)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.nconst hL (i := B.rE + 6) (by omega) 0 (by positivity)) le_rfl fun σ9 e9 => ?_
  subst e9
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
  exact ((((((((F0.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
    ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩
    _).setNat ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _

set_option maxHeartbeats 4000000 in
/-- **Procedure FRAME on the machine for `d = 1`**: the frame centre `frameQ` in the array `aW` in the form of the play
leaf, from the input rows of `ctxOf`. -/
theorem XV.frame1 {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ s : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} (hd : d = 1) (hS : B.o + 22 ≤ L.NS)
    (hN : B.rE + 7 ≤ L.NN) (hA : B.aW + 2 ≤ L.NA) (hrd : B.rd < B.rE) (hrm : B.rm < B.rE)
    (e_d : σ.nat B.rd = d) (e_m : σ.nat B.rm = m) (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa)
    (hma : m < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa) (hℓa : 2 ≤ ℓa)
    (hb : 2 * ((frMhat A b : ℤ) ^ (d + 1) * (frMhat A b : ℤ) ^ (d + 1)) < 2 ^ ℓ)
    (hs : 2 * ((frMhat A b : ℤ) ^ (d + 1) * (frMhat A b : ℤ) ^ (d + 1)) < 2 ^ s) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xframe1 L B) σ (9 + ((m * ((18 * d + 28) + (2 + 12) + 3) + 3) + 21))
      (fun σ' => PtIn σ' B.aW s (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ') := by
  subst hd
  obtain ⟨hM1, -, -⟩ := frMhat_le A b
  have hM1' : (1 : ℤ) ≤ frMhat A b := by exact_mod_cast hM1
  set M : ℤ := (frMhat A b : ℤ) with hMdef
  have hMx : 1 ≤ M ^ (1 + 1) := one_le_pow₀ hM1'
  have hb4 : M ^ 4 < 2 ^ ℓ := by
    have : M ^ 4 = M ^ (1 + 1) * M ^ (1 + 1) := by ring
    rw [this]; nlinarith
  have hℓ : 1 ≤ ℓ := by
    by_contra h
    have : ℓ = 0 := by omega
    subst this; nlinarith
  refine XV.seq (XV.f1init hL (B := B) (by omega) (by omega) hℓ hℓa) fun σ1 ⟨i5, i6, i7, i9, i12, i15, i3, i5n, i6n,
    d1, F1⟩ => ?_
  have r_d : σ1.nat B.rd = 1 := by rw [F1.1 _ (by omega), e_d]
  have r_m : σ1.nat B.rm = m := by rw [F1.1 _ (by omega), e_m]
  refine XV.seq (XV.f1scan hL (B := B) rfl (by omega) hN hA hrd hrm r_d r_m i5 i6 i7 (by rw [i3]) i5n i6n
    ⟨i9, i12, by rw [i15]; simp⟩ hka hma hda hb4) fun σ2 ⟨hI, d2, F2⟩ => ?_
  have sp := f1scan_spec (frAlN A b 0) (frBeN A b) m
  have s6 : σ2.sc (B.o + 6) = 0 := by rw [F2.2.1 _ (by simp only [f1S]; omega), i6]
  have s7 : σ2.sc (B.o + 7) = 1 := by rw [F2.2.1 _ (by simp only [f1S]; omega), i7]
  have n5 : σ2.nat (B.rE + 5) = 1 := by rw [F2.1 _ (by simp only [f1N]; omega), i5n]
  have n6 : σ2.nat (B.rE + 6) = 0 := by rw [F2.1 _ (by simp only [f1N]; omega), i6n]
  refine XV.mono (XV.f1out hL (o := B.o) (aW := B.aW) (i0 := B.rE + 6) (i1 := B.rE + 5) (Mx := M ^ (1 + 1))
    le_rfl hS (by omega) (by omega) (by omega) n6 n5 s6 s7 hI (fun i h => (sp.1 i h).2) (fun k h => (sp.2.2.1 k h).2)
    (fun i => frAlN_le A b 0 i) (fun i => frBeN_le A b i) hMx hb) le_rfl ?_
  rintro σ3 ⟨⟨D, x, hD, hDle, hx, e0, e1, hq⟩, d3, F3⟩
  refine ⟨⟨D, hD, lt_of_le_of_lt hDle hs, e0, fun j => ⟨x, lt_of_le_of_lt hx hs, ?_, ?_⟩⟩, by rw [d3, d2, d1], ?_⟩
  · have : (j : ℕ) = 0 := by omega
    rw [this, zero_add]; exact e1
  · rw [frameQ_one]; exact hq
  · refine ((F1.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => by simp only [f1S] at h; omega) (fun j h => by simp only [f1N] at h; omega)
        (fun b' _ h => by omega))).trans
      (F3.mono (fun y h => by omega) (fun _ h => h.elim) (fun b' _ h => by omega))

end AdversarialBco.Bit.Transfer
