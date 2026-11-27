/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOConstR

@[expose] public section

/-!
# UNI-ELL (c): the constants of step 2, the last register steps

`XV.constRC` (the exponents at the scale `2^s`) and `XV.constR`, the register steps of `xconstO` (EllOConstR.lean).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

set_option Elab.async false

set_option maxHeartbeats 4000000 in
/-- The rule of `xconstRC`. -/
theorem XV.constRC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {rs one s κ : ℕ} (hB : B.OK L 215 112 14) (hrs : B.rE + 64 ≤ rs ∧ rs < L.NN)
    (hone : B.rE + 64 ≤ one ∧ one < L.NN)
    (R0 : RegsAre σ [(rs, s), (one, 1), (B.rK, I.erK), (B.rE + 31, I.e1), (B.rE + 34, 4), (B.rE + 35, I.eτ),
      (B.rE + 41, 3 * d * (I.eL + I.eτ + 4))])
    (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstRC B rs one) σ 8 (fun σ' =>
      RegsAre σ' [(B.rE + 50, I.sepEx s), (B.rE + 51, I.sepEx s - I.e1), (B.rE + 53, I.sepEx s + I.eτ + 1),
        (B.rE + 54, I.sepEx s - s), (B.rE + 57, I.eτ + 4 + I.eL)] ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => B.rE + 49 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 55) (fun _ _ => False) σ σ') := by
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -⟩ := hB
  obtain ⟨hrs, hrs'⟩ := hrs
  obtain ⟨hone, hone'⟩ := hone
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I s
  have hX : cstX I s κ = I.sepEx s + I.eτ + I.eK + κ + 12 := rfl
  have H0 := FrameA.refl (fun _ => False) (fun j => B.rE + 49 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 55)
    (fun _ _ => False) σ
  have D0 : σ.draws = σ.draws := rfl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) ?_ (by norm_num) (fun _ h => h)
  refine XV.seq (XV.naddA hL (i := B.rE + 49) (a := rs) (b := B.rE + 31) (va := s) (vb := I.e1) (by omega)
    (by omega) (by omega) (R0.get (by simp)) (R0.get (by simp)) (by omega)) fun σ1 ⟨w1, d1, G1⟩ => ?_
  have R1 := R0.cons G1 (by simp <;> omega) (w1.trans (by omega : s + I.e1 = s + I.e1))
  have H1 := H0.trans (G1.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D1 := d1.trans D0
  refine XV.seq (XV.naddA hL (i := B.rE + 50) (a := B.rE + 49) (b := B.rE + 41) (va := s + I.e1) (vb := 3 * d * (I.eL + I.eτ + 4)) (by omega)
    (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp)) (by omega)) fun σ2 ⟨w2, d2, G2⟩ => ?_
  have R2 := R1.cons G2 (by simp <;> omega) (w2.trans (by omega : s + I.e1 + 3 * d * (I.eL + I.eτ + 4) = I.sepEx s))
  have H2 := H1.trans (G2.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D2 := d2.trans D1
  refine XV.seq (XV.naddA hL (i := B.rE + 51) (a := rs) (b := B.rE + 41) (va := s) (vb := 3 * d * (I.eL + I.eτ + 4)) (by omega)
    (by omega) (by omega) (R2.get (by simp)) (R2.get (by simp)) (by omega)) fun σ3 ⟨w3, d3, G3⟩ => ?_
  have R3 := R2.cons G3 (by simp <;> omega) (w3.trans (by omega : s + 3 * d * (I.eL + I.eτ + 4) = I.sepEx s - I.e1))
  have H3 := H2.trans (G3.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D3 := d3.trans D2
  refine XV.seq (XV.naddA hL (i := B.rE + 52) (a := B.rE + 50) (b := B.rE + 35) (va := I.sepEx s) (vb := I.eτ) (by omega)
    (by omega) (by omega) (R3.get (by simp)) (R3.get (by simp)) (by omega)) fun σ4 ⟨w4, d4, G4⟩ => ?_
  have R4 := R3.cons G4 (by simp <;> omega) (w4.trans (by omega : I.sepEx s + I.eτ = I.sepEx s + I.eτ))
  have H4 := H3.trans (G4.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D4 := d4.trans D3
  refine XV.seq (XV.naddA hL (i := B.rE + 53) (a := B.rE + 52) (b := one) (va := I.sepEx s + I.eτ) (vb := 1) (by omega)
    (by omega) (by omega) (R4.get (by simp)) (R4.get (by simp)) (by omega)) fun σ5 ⟨w5, d5, G5⟩ => ?_
  have R5 := R4.cons G5 (by simp <;> omega) (w5.trans (by omega : I.sepEx s + I.eτ + 1 = I.sepEx s + I.eτ + 1))
  have H5 := H4.trans (G5.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D5 := d5.trans D4
  refine XV.seq (XV.naddA hL (i := B.rE + 54) (a := B.rE + 31) (b := B.rE + 41) (va := I.e1) (vb := 3 * d * (I.eL + I.eτ + 4)) (by omega)
    (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp)) (by omega)) fun σ6 ⟨w6, d6, G6⟩ => ?_
  have R6 := R5.cons G6 (by simp <;> omega) (w6.trans (by omega : I.e1 + 3 * d * (I.eL + I.eτ + 4) = I.sepEx s - s))
  have H6 := H5.trans (G6.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D6 := d6.trans D5
  refine XV.seq (XV.naddA hL (i := B.rE + 56) (a := B.rE + 35) (b := B.rE + 34) (va := I.eτ) (vb := 4) (by omega)
    (by omega) (by omega) (R6.get (by simp)) (R6.get (by simp)) (by omega)) fun σ7 ⟨w7, d7, G7⟩ => ?_
  have R7 := R6.cons G7 (by simp <;> omega) (w7.trans (by omega : I.eτ + 4 = I.eτ + 4))
  have H7 := H6.trans (G7.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D7 := d7.trans D6
  refine XV.mono (XV.naddA hL (i := B.rE + 57) (a := B.rE + 56) (b := B.rK) (va := I.eτ + 4) (vb := I.erK) (by omega)
    (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp)) (by omega)) le_rfl fun σ8 ⟨w8, d8, G8⟩ => ?_
  have R8 := R7.cons G8 (by simp <;> omega) (w8.trans (by omega : I.eτ + 4 + I.erK = I.eτ + 4 + I.eL))
  have H8 := H7.trans (G8.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D8 := d8.trans D7
  refine ⟨fun p hp => ?_, D8, H8⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact R8.get (by simp)

set_option maxHeartbeats 4000000 in
/-- The rule of `xconstR`. -/
theorem XV.constR {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {rj rcR rcd rs one s κ : ℕ} (hB : B.OK L 215 112 14) (hI : ConstIn L B rj rcR rcd rs one)
    (vj : σ.nat rj = I.base.j) (vcR : σ.nat rcR = Nat.clog 2 I.base.Rb) (vcd : σ.nat rcd = Nat.clog 2 d)
    (vs : σ.nat rs = s) (v1 : σ.nat one = 1) (vd : σ.nat B.rd = d) (vK : σ.nat B.rK = I.erK)
    (vκ : σ.nat B.rκ = κ) (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstR B rj rcR rcd rs one) σ 34 (fun σ' =>
      RegsAre σ' [(B.rE + 50, I.sepEx s), (B.rE + 51, I.sepEx s - I.e1), (B.rE + 57, I.eτ + 4 + I.eL),
        (B.rE + 53, I.sepEx s + I.eτ + 1), (B.rE + 47, I.eu), (B.rE + 36, I.eH), (B.rE + 21, I.jg),
        (B.rE + 54, I.sepEx s - s), (B.rE + 1, I.eK + κ), (B.rE + 3, I.eL + I.eτ + 3), (rs, s), (one, 1)] ∧
      σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => B.rE + 1 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 2) (fun _ _ => False) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -⟩ := hB'
  have hI' := hI
  obtain ⟨⟨hrj, hrj'⟩, ⟨hrcR, hrcR'⟩, ⟨hrcd, hrcd'⟩, ⟨hrs, hrs'⟩, ⟨hone, hone'⟩⟩ := hI'
  refine XV.mono (K := 13 + (13 + 8)) ?_ (by norm_num) (fun _ h => h)
  refine XV.seq (XV.constRA hL hB hI vj vcR vcd vK hXa) fun σ1 ⟨R1, d1, F1⟩ => ?_
  have e1 : ∀ j, j < B.rE + 26 ∨ B.rE + 38 < j → σ1.nat j = σ.nat j := fun j h => F1.1 j (by omega)
  have RB : RegsAre σ1 [(B.rd, d), (B.rκ, κ), (one, 1), (B.rE + 31, I.e1), (B.rE + 34, 4), (B.rE + 35, I.eτ),
      (B.rE + 36, I.eH), (B.rE + 37, I.eL + I.eτ), (B.rE + 38, I.eL + I.eτ + 4)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e1 _ (by omega)]; exact vd
    · rw [e1 _ (by omega)]; exact vκ
    · rw [e1 _ (by omega)]; exact v1
    all_goals exact R1.get (by simp)
  refine XV.seq (XV.constRB hL hB ⟨hone, hone'⟩ RB hXa) fun σ2 ⟨R2, d2, F2⟩ => ?_
  have e2 : ∀ j, ¬ (j = B.rE + 1 ∨ j = B.rE + 3 ∨ j = B.rE + 21 ∨ (B.rE + 39 ≤ j ∧ j ≤ B.rE + 48)) →
      σ2.nat j = σ1.nat j := fun j h => F2.1 j h
  have RC : RegsAre σ2 [(rs, s), (one, 1), (B.rK, I.erK), (B.rE + 31, I.e1), (B.rE + 34, 4), (B.rE + 35, I.eτ),
      (B.rE + 41, 3 * d * (I.eL + I.eτ + 4))] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e2 _ (by omega), e1 _ (by omega)]; exact vs
    · rw [e2 _ (by omega), e1 _ (by omega)]; exact v1
    · rw [e2 _ (by omega), e1 _ (by omega)]; exact vK
    · rw [e2 _ (by omega)]; exact R1.get (by simp)
    · rw [e2 _ (by omega)]; exact R1.get (by simp)
    · rw [e2 _ (by omega)]; exact R1.get (by simp)
    · exact R2.get (by simp)
  refine XV.mono (XV.constRC hL hB ⟨hrs, hrs'⟩ ⟨hone, hone'⟩ RC hXa) le_rfl fun σ3 ⟨R3, d3, F3⟩ => ?_
  have e3 : ∀ j, ¬ (B.rE + 49 ≤ j ∧ j ≤ B.rE + 57 ∧ j ≠ B.rE + 55) → σ3.nat j = σ2.nat j := fun j h => F3.1 j h
  refine ⟨fun p hp => ?_, d3.trans (d2.trans d1), ((F1.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h)).trans
    (F2.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))).trans
    (F3.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R3.get (by simp)
  · exact R3.get (by simp)
  · exact R3.get (by simp)
  · exact R3.get (by simp)
  · rw [e3 _ (by omega)]; exact R2.get (by simp)
  · rw [e3 _ (by omega), e2 _ (by omega)]; exact R1.get (by simp)
  · rw [e3 _ (by omega)]; exact R2.get (by simp)
  · exact R3.get (by simp)
  · rw [e3 _ (by omega)]; exact R2.get (by simp)
  · rw [e3 _ (by omega)]; exact R2.get (by simp)
  · rw [e3 _ (by omega), e2 _ (by omega), e1 _ (by omega)]; exact vs
  · rw [e3 _ (by omega), e2 _ (by omega), e1 _ (by omega)]; exact v1

end AdversarialBco.Uni.EllO
