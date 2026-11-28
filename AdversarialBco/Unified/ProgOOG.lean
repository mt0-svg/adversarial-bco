/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# The play of BL-O in the modes `off` and `guard`

In the modes `off` and `guard` BL-O plays the frame centre `a` (`playPtO`), which BL-O's invariant holds in the array
`aC` in the form of the play leaf (`BLInv.ctr` on `cfgV`). The block `xOG` copies the cells `0, ..., d` of `aC` into
`aPl`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- `aPl[k] := aC[k]` for `k ≤ d`, through the slot `sC1`. -/
def xOG (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rD1 rD rOne)))
    (xforN rk rD1 rOne (.seq (toX (VL.aget L sC1 aC rk)) (toX (VL.aset L aPl rk sC1))))

/-- The cells `xOG` changes. -/
def SOG (y : ℕ) : Prop := y = sC1
def NOG (j : ℕ) : Prop := j = rD1 ∨ j = rk
def AOG (a _k : ℕ) : Prop := a = aPl

theorem le_asz {j : ℕ} (hd : 1 ≤ d) (hj : j ≤ d) : j < asz d := by unfold asz; nlinarith

/-- **The copy on the bit machine's language.** -/
theorem XV.og {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} (hNS : sC1 < L.NS)
    (hNN : rk < L.NN) (hNA : aPl < L.NA) (hd1 : 1 ≤ d) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hda : d + 2 < 2 ^ ℓa)
    (hb : ∀ j ≤ d, |σ.arr aC j| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xOG L) σ (1 + ((d + 1) * (2 + 2 + 3) + 3)) (fun σ' =>
      (∀ j ≤ d, σ'.arr aPl j = σ.arr aC j) ∧ σ'.draws = σ.draws ∧ FrameA SOG NOG AOG σ σ') := by
  have hNN' : rD1 < L.NN := by simp only [rD1, rk] at *; omega
  refine XV.seq (XV.nadd hL (σ := σ) (i := rD1) (a := rD) (b := rOne) hNN' (by simp only [rD, rk] at *; omega)
    (by simp only [rOne, rk] at *; omega) (by rw [hD]; omega) (by rw [h1]; omega)) fun σ0 e0 => ?_
  subst e0
  set σ0 := σ.setNat rD1 (σ.nat rD + σ.nat rOne) with hσ0
  have n0 : σ0.nat rD1 = d + 1 := by simp [hσ0, hD, h1]
  have o0 : σ0.nat rOne = 1 := by simp [hσ0, h1]
  have F0 : FrameA SOG NOG AOG σ σ0 := (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) _
  let J : ℕ → Env d → Prop := fun j σ' => (∀ k < j, σ'.arr aPl k = σ.arr aC k) ∧ σ'.draws = σ.draws ∧
    FrameA SOG NOG AOG σ σ'
  refine XV.mono (XV.forN hL (i := rk) (n := rD1) (one := rOne) hNN hNN' (by simp only [rOne, rk] at *; omega)
    (by decide) (by decide) (d + 1) (2 + 2) (by omega) J σ0 n0 o0
    ⟨fun k hk => absurd hk (by omega), by simp [hσ0], F0.setNat (Or.inr rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨ha, hdr, F⟩, _⟩ => ⟨fun j hj => ha j (by omega), hdr, F⟩
  intro j hj σ' ⟨ha, hdr, F⟩ hjj hjn hj1
  have eC : ∀ k, σ'.arr aC k = σ.arr aC k := fun k => F.2.2.1 aC k (by simp [AOG, aC, aPl])
  refine XV.seq (XV.aget hL (σ := σ') (x := sC1) (a := aC) (i := rk) hNS (by simp only [aC, aPl] at *; omega) hNN
    (by rw [hjj]; exact le_asz hd1 (by omega)) (by rw [hjj, eC]; exact hb j (by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.aset hL (a := aPl) (i := rk) (x := sC1) hNA hNN hNS (by simp [hjj]; exact le_asz hd1 (by omega))
    (by simp [hjj, eC]; exact hb j (by omega))) le_rfl fun σ2 e2 => ?_
  subst e2
  refine ⟨by simp [hjj], by simp [hjn], by simp [hj1], fun k hk => ?_, by simp [hdr], ?_⟩
  · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_nat, hjj]
    by_cases hkj : k = j
    · subst hkj; simp [eC]
    · rw [ite_eq_right (fun h => hkj h.2), ha k (by omega)]
  · exact ((F.setSc rfl _).setArr rfl _).setNat (Or.inr rfl) _

/-- The constants of `xOG`. -/
def kOG : BlkK := ⟨20, 1, 0, 0, 64, 32, 32⟩

end AdversarialBco.Unified.ProgO
