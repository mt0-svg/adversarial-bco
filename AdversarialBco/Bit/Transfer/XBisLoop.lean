/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllLoop

@[expose] public section

/-!
# The loop of BIS-R on the machine: its pieces

The pieces of the loop of BIS-R for `d = 1`: the interval `[lo, hi]` in the slots `P + 9`, `P + 10` (`BisLay`), the
midpoint `(lo + hi)/2` into `P + 11` and the cell `0` of the array `a0 + 1` (`xbisMid`, `XV.bisMid`), and the halving
by the sign of the entry `c₀` of the cut (`xbisHalve`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- The midpoint `(lo + hi)/2` (`2` in `u + 2`) into `P + 11` and the cell `0` of the array `a0 + 1`. -/
def xbisMid (L : Layout) (P u a0 n0 : ℕ) : XCmd :=
  .seq ((IE.ediv (.op .add (.sc (P + 9)) (.sc (P + 10))) (.sc (u + 2))).code L u (u + 13) (u + 14))
  (.seq (xset L (P + 11) (u + 13) u)
  (.seq (.prim (.frag (.nconst (n0 + 3) 0))) (toX (VL.aset L (a0 + 1) (n0 + 3) (P + 11)))))

/-- The halving: `hi := mid` when the entry `c₀` of the cut is positive, else `lo := mid`; the next turn. -/
def xbisHalve (L : Layout) (P u a0 n0 : ℕ) : XCmd :=
  .seq (toX (VL.aget L (u + 13) (a0 + 2) (n0 + 3)))
  (.seq (xifS L u (u + 13) (xset L (P + 10) (P + 11) u) (xset L (P + 9) (P + 11) u))
    (.prim (.frag (.nadd (n0 + 6) (n0 + 6) (n0 + 4)))))

/-! ## The midpoint -/

theorem abs_mid_le {lo hi M : ℤ} (hl : |lo| ≤ M) (hh : |hi| ≤ M) : |(lo + hi) / 2| ≤ M := by
  rw [abs_le] at hl hh ⊢
  constructor <;> omega

/-! ## The loop on the machine -/

/-- The cells of BIS-R above those of ELL-R: the interval and the midpoint in `P + 9, P + 10, P + 11`. -/
structure BisLay (L : Layout) (B : EllBlk) (P u a0 kb n0 : ℕ) : Prop where
  loop : LoopLay L B P u a0 kb n0
  PS : P + 12 ≤ u

set_option maxHeartbeats 4000000 in
/-- The rule of `xbisMid`. -/
theorem XV.bisMid {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {P u a0 n0 F : ℕ}
    {lo hi : ℤ} (hd : 1 ≤ d) (hPu : P + 12 ≤ u) (hS : u + 18 ≤ L.NS) (hA : a0 + 1 < L.NA) (hN : n0 + 3 < L.NN)
    (hz : σ.sc u = 0) (h2 : σ.sc (u + 2) = 2) (hlo : σ.sc (P + 9) = lo) (hhi : σ.sc (P + 10) = hi)
    (blo : |lo| ≤ 2 ^ F) (bhi : |hi| ≤ 2 ^ F) (hF : 1 ≤ F) (hℓ : F + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xbisMid L P u a0 n0) σ 9 (fun σ' =>
      σ'.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) ∧ σ'.arr (a0 + 1) 0 = (((lo + hi) / 2 : ℤ) : ℝ) ∧
      σ'.nat (n0 + 3) = 0 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3) (fun b k => b = a0 + 1 ∧ k = 0) σ σ') := by
  have hda := asz_lt hL hA
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have b2 : |(2 : ℤ)| ≤ 2 ^ F := by
    rw [abs_two]; exact le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) hF)
  have bm : |(lo + hi) / 2| ≤ 2 ^ F := abs_mid_le blo bhi
  have bmℓ : |(((lo + hi) / 2 : ℤ) : ℝ)| < 2 ^ ℓ := absR_lt bm (by omega)
  refine XV.seq (K₂ := 4) (XV.ieRun (E := F) (e := IE.ediv (.op .add (.sc (P + 9)) (.sc (P + 10))) (.sc (u + 2)))
    (v := (lo + hi) / 2) hL (x := u + 13) (t := u + 14) (z := u)
    (by simp only [IE.WF]; exact ⟨⟨(by intro h; cases h), by omega, by omega⟩, by omega⟩) (by omega) (by omega)
    (by simp only [IE.scr]; omega) hz
    (by simp only [IE.Leaves]; exact ⟨⟨⟨lo, hlo, blo⟩, ⟨hi, hhi, bhi⟩⟩, ⟨2, by rw [h2]; norm_num, b2⟩⟩)
    (by simp only [IE.top, IE.mag]; omega) (by
      simp only [IE.eval, RealRAM.Op2.eval, hlo, hhi, h2]
      rw [show (lo : ℝ) + hi = ((lo + hi : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast,
        show (2 : ℝ) = ((2 : ℤ) : ℝ) by norm_num, Int.floor_intCast])) fun σ1 ⟨m1, _, d1, F1⟩ => ?_
  have z1 : σ1.sc u = 0 := by rw [F1.2.1 _ (by omega), hz]
  have e1 : RealRAM.Op2.eval .add (σ1.sc (u + 13)) (σ1.sc u) = (((lo + hi) / 2 : ℤ) : ℝ) := by
    simp [RealRAM.Op2.eval, m1, z1]
  refine XV.seq (K₂ := 3) (XV.sop2 hL (x := P + 11) (a := u + 13) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [m1]; exact bmℓ) (by rw [z1]; exact h0) (by rw [e1]; exact bmℓ)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 2) (XV.nconst hL (i := n0 + 3) hN 0 (by positivity)) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.aset hL (a := a0 + 1) (i := n0 + 3) (x := P + 11) hA hN (by omega)
    (by simp; unfold asz at hda ⊢; nlinarith [Nat.zero_le d]) (by simp [e1]; exact bmℓ)) le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by simp [e1], by simp [e1], by simp, by simp [d1], ?_⟩
  have G1 : FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3) (fun b k => b = a0 + 1 ∧ k = 0) σ σ1 :=
    (FrameA.ofP F1).mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim) (fun _ _ h => h)
  exact ((G1.setSc (Or.inl rfl) _).setNat rfl 0).setArr ⟨rfl, by simp⟩ _


end AdversarialBco.Bit.Transfer
