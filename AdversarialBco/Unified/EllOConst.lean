/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOConstC

@[expose] public section

/-!
# UNI-ELL (c): the constants of step 2 on the machine

The slot steps `XV.constS` and the rule of `xconstO`, `XV.constO`: the constants of SEP and of the gauge (`SepEnvO`),
the precision `k = eK + κ` and `2^k` (`TDatK`), the factor `2^{E-s}` and the exponent `s` of the output.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

/-- The units of `xconstS`. -/
def constSU (X : ℕ) : ℕ := 36 * X + 38

set_option maxHeartbeats 16000000 in
/-- The rule of `xconstS`. -/
theorem XV.constS {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {rs one s κ : ℕ} (hB : B.OK L 215 112 14) (hrs : B.rE + 64 ≤ rs ∧ rs < L.NN)
    (hone : B.rE + 64 ≤ one ∧ one < L.NN)
    (R0 : RegsAre σ [(B.rE + 50, I.sepEx s), (B.rE + 51, I.sepEx s - I.e1), (B.rE + 57, I.eτ + 4 + I.eL),
        (B.rE + 53, I.sepEx s + I.eτ + 1), (B.rE + 47, I.eu), (B.rE + 36, I.eH), (B.rE + 21, I.jg),
        (B.rE + 54, I.sepEx s - s), (B.rE + 1, I.eK + κ), (B.rE + 3, I.eL + I.eτ + 3), (rs, s), (one, 1)])
    (hXl : cstX I s κ < ℓ) (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstS L B rs one) σ (constSU (cstX I s κ)) (fun σ' =>
      ScAre σ' [(B.o + 1, (s : ℝ)), (B.o + 2, (2 : ℝ) ^ (I.eK + κ)),
        (B.o + 76, ((2 ^ (I.sepEx s - s) : ℤ) : ℝ)), (B.o + 59, (2 : ℝ) ^ I.jg), (B.o + 58, ((1 : ℤ) : ℝ)),
        (B.o + 57, ((2 ^ I.eH : ℤ) : ℝ)), (B.o + 8, (2 : ℝ) ^ I.eu), (B.o + 7, (2 : ℝ) ^ (I.sepEx s + I.eτ + 1)),
        (B.o + 6, (2 : ℝ) ^ (I.eτ + 4 + I.eL)), (B.o + 5, (2 : ℝ) ^ (I.sepEx s - I.e1)),
        (B.o + 4, (2 : ℝ) ^ I.sepEx s)] ∧
      RegsAre σ' [(B.rE + 50, I.sepEx s), (B.rE + 51, I.sepEx s - I.e1), (B.rE + 57, I.eτ + 4 + I.eL),
        (B.rE + 53, I.sepEx s + I.eτ + 1), (B.rE + 47, I.eu), (B.rE + 36, I.eH), (B.rE + 21, I.jg),
        (B.rE + 54, I.sepEx s - s), (B.rE + 1, I.eK + κ), (B.rE + 3, I.eL + I.eτ + 3), (rs, s), (one, 1)] ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => B.o + 1 ≤ y ∧ y ≤ B.o + 76) (fun j => j = B.rE + 55) (fun _ _ => False) σ σ') := by
  obtain ⟨hoS, hrN, haA, -⟩ := hB
  obtain ⟨hrs, hrs'⟩ := hrs
  obtain ⟨hone, hone'⟩ := hone
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I s
  have hX : cstX I s κ = I.sepEx s + I.eτ + I.eK + κ + 12 := rfl
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 3 * d * (I.eL + I.eτ + 4) := ⟨_, rfl⟩
  rw [← hQ] at heη hE
  have S0 : ScAre σ [] := fun _ h => by simp at h
  have H0 := FrameA.refl (fun y => B.o + 1 ≤ y ∧ y ≤ B.o + 76) (fun j => j = B.rE + 55) (fun _ _ => False) σ
  have D0 : σ.draws = σ.draws := rfl
  refine XV.mono (K := (4 * I.sepEx s + 4) + ((4 * (I.sepEx s - I.e1) + 4) + ((4 * (I.eτ + 4 + I.eL) + 4) +
    ((4 * (I.sepEx s + I.eτ + 1) + 4) + ((4 * I.eu + 4) + ((4 * I.eH + 4) + (1 + ((4 * I.jg + 4) +
    ((4 * (I.sepEx s - s) + 4) + ((4 * (I.eK + κ) + 4) + 1)))))))))) ?_ (by unfold constSU; omega) (fun _ h => h)
  refine XV.seq (XV.pow2A hL (p := B.o + 4) (i := B.rE + 55) (n := B.rE + 50) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R0.get (by simp)) (R0.get (by simp)) (by omega) (by omega))
    fun σ1 ⟨w1, d1, G1⟩ => ?_
  have R1 := R0.frame G1 (by simp <;> omega)
  have S1 := ScAre.cons1 S0 (v := (2 : ℝ) ^ I.sepEx s) G1 (by simp <;> omega) (by rw [w1]; simp)
  have H1 := H0.trans (G1.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D1 := d1.trans D0
  refine XV.seq (XV.pow2A hL (p := B.o + 5) (i := B.rE + 55) (n := B.rE + 51) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp)) (by omega) (by omega))
    fun σ2 ⟨w2, d2, G2⟩ => ?_
  have R2 := R1.frame G2 (by simp <;> omega)
  have S2 := ScAre.cons1 S1 (v := (2 : ℝ) ^ (I.sepEx s - I.e1)) G2 (by simp <;> omega) (by rw [w2]; simp)
  have H2 := H1.trans (G2.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D2 := d2.trans D1
  refine XV.seq (XV.pow2A hL (p := B.o + 6) (i := B.rE + 55) (n := B.rE + 57) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R2.get (by simp)) (R2.get (by simp)) (by omega) (by omega))
    fun σ3 ⟨w3, d3, G3⟩ => ?_
  have R3 := R2.frame G3 (by simp <;> omega)
  have S3 := ScAre.cons1 S2 (v := (2 : ℝ) ^ (I.eτ + 4 + I.eL)) G3 (by simp <;> omega) (by rw [w3]; simp)
  have H3 := H2.trans (G3.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D3 := d3.trans D2
  refine XV.seq (XV.pow2A hL (p := B.o + 7) (i := B.rE + 55) (n := B.rE + 53) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R3.get (by simp)) (R3.get (by simp)) (by omega) (by omega))
    fun σ4 ⟨w4, d4, G4⟩ => ?_
  have R4 := R3.frame G4 (by simp <;> omega)
  have S4 := ScAre.cons1 S3 (v := (2 : ℝ) ^ (I.sepEx s + I.eτ + 1)) G4 (by simp <;> omega) (by rw [w4]; simp)
  have H4 := H3.trans (G4.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D4 := d4.trans D3
  refine XV.seq (XV.pow2A hL (p := B.o + 8) (i := B.rE + 55) (n := B.rE + 47) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R4.get (by simp)) (R4.get (by simp)) (by omega) (by omega))
    fun σ5 ⟨w5, d5, G5⟩ => ?_
  have R5 := R4.frame G5 (by simp <;> omega)
  have S5 := ScAre.cons1 S4 (v := (2 : ℝ) ^ I.eu) G5 (by simp <;> omega) (by rw [w5]; simp)
  have H5 := H4.trans (G5.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D5 := d5.trans D4
  refine XV.seq (XV.pow2A hL (p := B.o + 57) (i := B.rE + 55) (n := B.rE + 36) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp)) (by omega) (by omega))
    fun σ6 ⟨w6, d6, G6⟩ => ?_
  have R6 := R5.frame G6 (by simp <;> omega)
  have S6 := ScAre.cons1 S5 G6 (by simp <;> omega) w6
  have H6 := H5.trans (G6.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D6 := d6.trans D5
  refine XV.seq (XV.sconstA hL (x := B.o + 58) (by omega) 1 (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))
    fun σ7 ⟨w7, d7, G7⟩ => ?_
  have R7 := R6.frame G7 (fun _ _ h => h)
  have S7 := ScAre.cons1 S6 G7 (by simp <;> omega) w7
  have H7 := H6.trans (G7.mono (fun _ h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  have D7 := d7.trans D6
  refine XV.seq (XV.pow2A hL (p := B.o + 59) (i := B.rE + 55) (n := B.rE + 21) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp)) (by omega) (by omega))
    fun σ8 ⟨w8, d8, G8⟩ => ?_
  have R8 := R7.frame G8 (by simp <;> omega)
  have S8 := ScAre.cons1 S7 (v := (2 : ℝ) ^ I.jg) G8 (by simp <;> omega) (by rw [w8]; simp)
  have H8 := H7.trans (G8.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D8 := d8.trans D7
  refine XV.seq (XV.pow2A hL (p := B.o + 76) (i := B.rE + 55) (n := B.rE + 54) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R8.get (by simp)) (R8.get (by simp)) (by omega) (by omega))
    fun σ9 ⟨w9, d9, G9⟩ => ?_
  have R9 := R8.frame G9 (by simp <;> omega)
  have S9 := ScAre.cons1 S8 G9 (by simp <;> omega) w9
  have H9 := H8.trans (G9.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D9 := d9.trans D8
  refine XV.seq (XV.pow2A hL (p := B.o + 2) (i := B.rE + 55) (n := B.rE + 1) (one := one) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (R9.get (by simp)) (R9.get (by simp)) (by omega) (by omega))
    fun σ10 ⟨w10, d10, G10⟩ => ?_
  have R10 := R9.frame G10 (by simp <;> omega)
  have S10 := ScAre.cons1 S9 (v := (2 : ℝ) ^ (I.eK + κ)) G10 (by simp <;> omega) (by rw [w10]; simp)
  have H10 := H9.trans (G10.mono (fun _ h => by omega) (fun _ h => h) (fun _ _ h => h))
  have D10 := d10.trans D9
  refine XV.mono (XV.ncastA hL (x := B.o + 1) (i := rs) (v := s) (by omega) (by omega) (R10.get (by simp)) (by omega)) le_rfl
    fun σ11 ⟨w11, d11, G11⟩ => ?_
  have R11 := R10.frame G11 (fun _ _ h => h)
  have S11 := ScAre.cons1 S10 (v := (s : ℝ)) G11 (by simp <;> omega) (by rw [w11]; simp)
  have H11 := H10.trans (G11.mono (fun _ h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  exact ⟨S11, R11, d11.trans D10, H11⟩

set_option maxHeartbeats 4000000 in
/-- The rule of `xconstO`: the constants of step 2 at the scale `2^s`, within `constOU (cstX I s κ)` units, writing
the slots `o + 1, ..., o + 76` and the registers `rE + 1, rE + 3, ..., rE + 57` only. -/
theorem XV.constO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {rj rcR rcd rs one s κ : ℕ} (hB : B.OK L 215 112 14) (hI : ConstIn L B rj rcR rcd rs one)
    (vj : σ.nat rj = I.base.j) (vcR : σ.nat rcR = Nat.clog 2 I.base.Rb) (vcd : σ.nat rcd = Nat.clog 2 d)
    (vs : σ.nat rs = s) (v1 : σ.nat one = 1) (vd : σ.nat B.rd = d) (vK : σ.nat B.rK = I.erK)
    (vκ : σ.nat B.rκ = κ) (vc : σ.arr B.ac 0 = I.Dc ∧ ∀ j : Fin d, σ.arr B.ac (1 + (j : ℕ)) = I.Nc j)
    (hXl : cstX I s κ < ℓ) (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstO L B rj rcR rcd rs one) σ (constOU (cstX I s κ)) (fun σ' =>
      SepEnvO B I s σ' ∧ σ'.nat (B.rE + 1) = I.eK + κ ∧ σ'.sc (B.o + 2) = 2 ^ (I.eK + κ) ∧
      σ'.sc (B.o + 76) = ((2 ^ (I.sepEx s - s) : ℤ) : ℝ) ∧ σ'.sc (B.o + 1) = s ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o + 1 ≤ y ∧ y ≤ B.o + 76) (fun j => B.rE + 1 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 2)
        (fun _ _ => False) σ σ') := by
  refine XV.mono (XV.seq (XV.constR hL hB hI vj vcR vcd vs v1 vd vK vκ hXa) fun σ1 ⟨R1, d1, F1⟩ =>
    XV.mono (XV.constS hL hB hI.rs hI.one R1 hXl hXa) le_rfl fun σ2 h2 => ?_) (by unfold constOU constSU; omega)
    (fun _ h => h)
  obtain ⟨S2, R2, d2, F2⟩ := h2
  have F : FrameA (fun y => B.o + 1 ≤ y ∧ y ≤ B.o + 76) (fun j => B.rE + 1 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 2)
      (fun _ _ => False) σ σ2 :=
    (F1.mono (fun _ h => h.elim) (fun _ h => h) (fun _ _ h => h)).trans
      (F2.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  exact ⟨⟨S2.get (by simp), S2.get (by simp), S2.get (by simp), S2.get (by simp), S2.get (by simp),
    R2.get (by simp), S2.get (by simp), S2.get (by simp), R2.get (by simp), S2.get (by simp),
    by rw [F.2.2.1 _ _ id]; exact vc.1, fun j => by rw [F.2.2.1 _ _ id]; exact vc.2 j⟩,
    R2.get (by simp), S2.get (by simp), S2.get (by simp), S2.get (by simp), d2.trans d1, F⟩

end AdversarialBco.Uni.EllO
