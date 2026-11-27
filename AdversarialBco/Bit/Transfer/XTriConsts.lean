/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriConstRun
public import AdversarialBco.Bit.Transfer.XBLSetupPrm

@[expose] public section

/-!
# TRI-M, the constants block

`xtcPro`, `XV.tcPro`: the prologue of the constants block, the registers `1, d + 1, m + (d + d), d d, m` and the slots
`0, 1, -1, 2, 4`, `s = 4`, `d`, `n`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

variable {d : ℕ}

/-! ## The prologue -/

/-- The prologue: `r := 1`, `r + 1 := d + 1`, `r + 25 := d d`, `r + 26 := m`, `r + 2 := m + (d + d)`; the slots
`o + 1, o + 2, o + 3 := 0, 1, -1`, `o + 116, o + 117 := 2, 4`, `o + 115 := 4`, `o + 113 := d`, `o + 114 := n`. -/
def xtcPro (L : Layout) (nd rm sn o r : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst r 1)))
  (.seq (.prim (.frag (.nadd (r + 1) nd r)))
  (.seq (xnmul (r + 25) nd nd)
  (.seq (.prim (.frag (.nconst (r + 26) 0)))
  (.seq (.prim (.frag (.nadd (r + 26) (r + 26) rm)))
  (.seq (.prim (.frag (.nadd (r + 2) nd nd)))
  (.seq (.prim (.frag (.nadd (r + 2) (r + 26) (r + 2))))
  (.seq (toX (VL.sconst L (o + 1) 0))
  (.seq (toX (VL.sconst L (o + 2) 1))
  (.seq (toX (VL.sconst L (o + 3) (-1)))
  (.seq (toX (VL.sconst L (o + 116) 2))
  (.seq (toX (VL.sconst L (o + 117) 4))
  (.seq (toX (VL.sconst L (o + 115) 4))
  (.seq (toX (VL.ncast L (o + 113) nd))
  (toX (VL.sop2 L .add (o + 114) sn (o + 1))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem XV.tcPro {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {nd rm sn o r m n : ℕ}
    (hS : o + 245 ≤ L.NS) (hN : r + 31 ≤ L.NN) (hnd : nd < r) (hrm : rm < r) (hsn : sn < o)
    (hσd : σ.nat nd = d) (hσm : σ.nat rm = m) (hσn : σ.sc sn = n)
    (hda : d * d + m + (d + d) + 2 < 2 ^ ℓa) (hdl : d + 4 < 2 ^ ℓ) (hnl : n + 4 < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xtcPro L nd rm sn o r) σ 15 (fun σ' =>
      σ'.nat r = 1 ∧ σ'.nat (r + 1) = d + 1 ∧ σ'.nat (r + 2) = m + (d + d) ∧ σ'.nat (r + 25) = d * d ∧
      σ'.nat (r + 26) = m ∧ σ'.sc (o + 1) = 0 ∧ σ'.sc (o + 2) = 1 ∧ σ'.sc (o + 3) = -1 ∧ σ'.sc (o + 116) = 2 ∧
      σ'.sc (o + 117) = 4 ∧ σ'.sc (o + 115) = (((4 : ℕ) : ℤ) : ℝ) ∧ σ'.sc (o + 113) = ((d : ℤ) : ℝ) ∧
      σ'.sc (o + 114) = ((n : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ σ') := by
  have n0 : nd ≠ r := by omega
  have n1 : nd ≠ r + 1 := by omega
  have n2 : nd ≠ r + 2 := by omega
  have n25 : nd ≠ r + 25 := by omega
  have n26 : nd ≠ r + 26 := by omega
  have m0 : rm ≠ r := by omega
  have m1 : rm ≠ r + 1 := by omega
  have m25 : rm ≠ r + 25 := by omega
  have m26 : rm ≠ r + 26 := by omega
  have s1 : sn ≠ o + 1 := by omega
  have s2 : sn ≠ o + 2 := by omega
  have s3 : sn ≠ o + 3 := by omega
  have s113 : sn ≠ o + 113 := by omega
  have s115 : sn ≠ o + 115 := by omega
  have s116 : sn ≠ o + 116 := by omega
  have s117 : sn ≠ o + 117 := by omega
  have hc : ∀ c : ℕ, c ≤ 4 → |((c : ℚ) : ℝ)| < 2 ^ ℓ := fun c hc => by
    rw [Rat.cast_natCast]; exact XV.abs_nat_lt (by omega)
  have h1 : (1 : ℕ) < 2 ^ ℓa := by omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))))
    ?_ (by norm_num) (fun _ h => h)
  unfold xtcPro
  refine XV.seq (XV.nconst hL (i := r) (by omega) 1 h1) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nadd hL (i := r + 1) (a := nd) (b := r) (by omega) (by omega) (by omega)
    (by simp [n0, hσd]; omega) (by simpa using h1)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nmul hL (i := r + 25) (a := nd) (b := nd) (by omega) (by omega) (by omega)
    (by simp [n0, n1, hσd]; nlinarith) (by simp [n0, n1, hσd]; nlinarith) (by simp [n0, n1, hσd]; omega))
    fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := r + 26) (by omega) 0 (by omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nadd hL (i := r + 26) (a := r + 26) (b := rm) (by omega) (by omega) (by omega)
    (by simp) (by simp [m0, m1, m25, m26, hσm]; omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nadd hL (i := r + 2) (a := nd) (b := nd) (by omega) (by omega) (by omega)
    (by simp [n0, n1, n25, n26, hσd]; nlinarith) (by simp [n0, n1, n25, n26, hσd]; nlinarith)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.nadd hL (i := r + 2) (a := r + 26) (b := r + 2) (by omega) (by omega) (by omega)
    (by simp [m0, m1, m25, m26, hσm]; omega) (by simp [n0, n1, n25, n26, hσd]; omega)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.sconst hL (x := o + 1) (by omega) 0 rfl (by simp)) fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.sconst hL (x := o + 2) (by omega) 1 rfl (by simpa using hc 1 (by omega))) fun σ9 e9 => ?_
  subst e9
  refine XV.seq (XV.sconst hL (x := o + 3) (by omega) (-1) rfl (by
    rw [show ((-1 : ℚ) : ℝ) = -((1 : ℕ) : ℚ) by push_cast; ring, abs_neg]; exact hc 1 (by omega)))
    fun σ10 e10 => ?_
  subst e10
  refine XV.seq (XV.sconst hL (x := o + 116) (by omega) 2 rfl (by simpa using hc 2 (by omega))) fun σ11 e11 => ?_
  subst e11
  refine XV.seq (XV.sconst hL (x := o + 117) (by omega) 4 rfl (by simpa using hc 4 (by omega))) fun σ12 e12 => ?_
  subst e12
  refine XV.seq (XV.sconst hL (x := o + 115) (by omega) 4 rfl (by simpa using hc 4 (by omega))) fun σ13 e13 => ?_
  subst e13
  refine XV.seq (XV.ncastI hL (x := o + 113) (i := nd) (by omega) (by omega)
    (by simp [n0, n1, n2, n25, n26, hσd]; omega))
    fun σ14 e14 => ?_
  subst e14
  have hn0 : |((n : ℕ) : ℝ)| < 2 ^ ℓ := XV.abs_nat_lt (by omega)
  refine XV.mono (XV.sop2 hL (x := o + 114) (a := sn) (b := o + 1) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by simp [s1, s2, s3, s113, s115, s116, s117, hσn]; exact_mod_cast (show n < 2 ^ ℓ by omega))
    (by simp)
    (by simp [s1, s2, s3, s113, s115, s116, s117, hσn, RealRAM.Op2.eval]; exact_mod_cast (show n < 2 ^ ℓ by omega)))
    le_rfl ?_
  rintro σ' rfl
  refine ⟨by simp, by simp [n0, hσd], by simp [m0, m1, m25, m26, hσm, n0, n1, n25, n26, hσd],
    by simp [n0, n1, hσd], by simp [m0, m1, m25, m26, hσm], by simp, by simp, by simp, by simp, by simp,
    by simp, by simp [n0, n1, n2, n25, n26, hσd], by simp [s1, s2, s3, s113, s115, s116, s117, hσn, RealRAM.Op2.eval],
    by simp, ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k _ => by simp, by simp, by simp⟩
  · simp only [not_le] at hj
    simp [show j ≠ r by omega, show j ≠ r + 1 by omega, show j ≠ r + 2 by omega, show j ≠ r + 25 by omega,
      show j ≠ r + 26 by omega]
  · simp only [not_le] at hy
    simp [show y ≠ o + 1 by omega, show y ≠ o + 2 by omega, show y ≠ o + 3 by omega, show y ≠ o + 113 by omega,
      show y ≠ o + 114 by omega, show y ≠ o + 115 by omega, show y ≠ o + 116 by omega, show y ≠ o + 117 by omega]

end AdversarialBco.Bit.Transfer
