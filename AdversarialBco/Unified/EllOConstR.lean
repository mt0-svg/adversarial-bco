/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOSep
public import AdversarialBco.Bit.Transfer.XEllReg
public import AdversarialBco.Bit.Transfer.XEllSet

@[expose] public section

/-!
# UNI-ELL (c): the constants of step 2, the code and the first register steps

`xconstO`: from `j`, `lg R̄`, `lg d`, the scale exponent `s` in registers of ELL-R's block (and `erK`, `κ`, `d` in the
inputs), the exponents of EllSpec.lean in the registers `rE + 26, ..., rE + 57` (straight-line code, `RegsAre`), then
the constants of SEP and of the gauge (`SepEnvO`), the precision `k = eK + κ` and `2^k` (`TDatK`), the factor
`2^{E-s}` and the exponent `s` of the output into their slots. This file: the code, `XV.constRA`, `XV.constRB`;
EllOConstC.lean: `XV.constRC`, `XV.constR`; EllOConst.lean: `XV.constS`, `XV.constO`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

-- One theorem at a time: the straight-line proofs below are large, and a parallel elaboration exceeds the memory cap
-- of the build.
set_option Elab.async false

theorem ScAre.cons1 {σ σ' : Env d} {l : List (ℕ × ℝ)} {N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {x : ℕ} {v : ℝ}
    (h : ScAre σ l) (hF : FrameA (fun y => y = x) N Ar σ σ') (hl : ∀ p ∈ l, p.1 ≠ x) (hv : σ'.sc x = v) :
    ScAre σ' ((x, v) :: l) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hv
  · rw [hF.2.1 _ (hl p hp), h p hp]

/-- The register steps, first part: from `j` (`rj`), `lg R̄` (`rcR`), `lg d` (`rcd`) and the input `erK`: `eM`, `e1`
(`rE + 31`), `eτ` (`rE + 35`), `eH` (`rE + 36`), `eL + eτ`, `eL + eτ + 4` (`rE + 37`, `rE + 38`), `4` (`rE + 34`). -/
def xconstRA (B : EllOBlk) (rj rcR rcd : ℕ) : XCmd :=
  (.seq (.prim (.frag (.nconst (B.rE + 26) 2)))
  (.seq (.prim (.frag (.nadd (B.rE + 27) rcR (B.rE + 26))))
  (.seq (.prim (.frag (.nadd (B.rE + 28) rj (B.rE + 27))))
  (.seq (.prim (.frag (.nadd (B.rE + 29) (B.rE + 28) B.rK)))
  (.seq (.prim (.frag (.nconst (B.rE + 30) 5)))
  (.seq (.prim (.frag (.nadd (B.rE + 31) (B.rE + 29) (B.rE + 30))))
  (.seq (.prim (.frag (.nadd (B.rE + 32) (B.rE + 28) (B.rE + 27))))
  (.seq (.prim (.frag (.nadd (B.rE + 33) (B.rE + 32) rcd)))
  (.seq (.prim (.frag (.nconst (B.rE + 34) 4)))
  (.seq (.prim (.frag (.nadd (B.rE + 35) (B.rE + 33) (B.rE + 34))))
  (.seq (.prim (.frag (.nadd (B.rE + 36) (B.rE + 27) B.rK)))
  (.seq (.prim (.frag (.nadd (B.rE + 37) B.rK (B.rE + 35))))
    (.prim (.frag (.nadd (B.rE + 38) (B.rE + 37) (B.rE + 34))))))))))))))))

/-- The register steps, second part: with `d`, `κ` in the inputs and `1` in `one`: `3d(eL + eτ + 4)` (`rE + 41`),
`eη`, `jg` (`rE + 21`), `eu` (`rE + 47`), `eK`, `k = eK + κ` (`rE + 1`), `eL + eτ + 3` (`rE + 3`). -/
def xconstRB (B : EllOBlk) (one : ℕ) : XCmd :=
  (.seq (.prim (.frag (.nconst (B.rE + 39) 3)))
  (.seq (xnmul (B.rE + 40) (B.rE + 39) B.rd)
  (.seq (xnmul (B.rE + 41) (B.rE + 40) (B.rE + 38))
  (.seq (.prim (.frag (.nconst (B.rE + 42) 11)))
  (.seq (.prim (.frag (.nadd (B.rE + 43) (B.rE + 35) (B.rE + 31))))
  (.seq (.prim (.frag (.nadd (B.rE + 44) (B.rE + 43) (B.rE + 42))))
  (.seq (.prim (.frag (.nadd (B.rE + 45) (B.rE + 44) (B.rE + 41))))
  (.seq (.prim (.frag (.nadd (B.rE + 46) (B.rE + 45) (B.rE + 36))))
  (.seq (.prim (.frag (.nadd (B.rE + 21) (B.rE + 46) one)))
  (.seq (.prim (.frag (.nadd (B.rE + 47) (B.rE + 45) one)))
  (.seq (.prim (.frag (.nadd (B.rE + 48) (B.rE + 21) one)))
  (.seq (.prim (.frag (.nadd (B.rE + 1) (B.rE + 48) B.rκ)))
    (.prim (.frag (.nadd (B.rE + 3) (B.rE + 37) (B.rE + 39))))))))))))))))

/-- The register steps, third part: with `s` in `rs`: `E = sepEx s` (`rE + 50`), `E - e1` (`rE + 51`), `E + eτ + 1`
(`rE + 53`), `E - s` (`rE + 54`), `eτ + 4 + eL` (`rE + 57`). -/
def xconstRC (B : EllOBlk) (rs one : ℕ) : XCmd :=
  (.seq (.prim (.frag (.nadd (B.rE + 49) rs (B.rE + 31))))
  (.seq (.prim (.frag (.nadd (B.rE + 50) (B.rE + 49) (B.rE + 41))))
  (.seq (.prim (.frag (.nadd (B.rE + 51) rs (B.rE + 41))))
  (.seq (.prim (.frag (.nadd (B.rE + 52) (B.rE + 50) (B.rE + 35))))
  (.seq (.prim (.frag (.nadd (B.rE + 53) (B.rE + 52) one)))
  (.seq (.prim (.frag (.nadd (B.rE + 54) (B.rE + 31) (B.rE + 41))))
  (.seq (.prim (.frag (.nadd (B.rE + 56) (B.rE + 35) (B.rE + 34))))
    (.prim (.frag (.nadd (B.rE + 57) (B.rE + 56) B.rK))))))))))

/-- The register steps. -/
def xconstR (B : EllOBlk) (rj rcR rcd rs one : ℕ) : XCmd :=
  .seq (xconstRA B rj rcR rcd) (.seq (xconstRB B one) (xconstRC B rs one))

/-- The slot steps: `2^E`, `2^{E-e1}`, `2^{eτ+4+eL}`, `2^{E+eτ+1}`, `2^{eu}` (SEP), `2^{eH}`, `1`, `2^{jg}` (the
gauge), `2^{E-s}` (`o + 76`), `2^k` (`o + 2`), `s` (`o + 1`); the register `rE + 55` counts. -/
def xconstS (L : Layout) (B : EllOBlk) (rs one : ℕ) : XCmd :=
  .seq (xpow2 L (B.o + 4) (B.rE + 55) (B.rE + 50) one)
  (.seq (xpow2 L (B.o + 5) (B.rE + 55) (B.rE + 51) one)
  (.seq (xpow2 L (B.o + 6) (B.rE + 55) (B.rE + 57) one)
  (.seq (xpow2 L (B.o + 7) (B.rE + 55) (B.rE + 53) one)
  (.seq (xpow2 L (B.o + 8) (B.rE + 55) (B.rE + 47) one)
  (.seq (xpow2 L (B.o + 57) (B.rE + 55) (B.rE + 36) one)
  (.seq (toX (VL.sconst L (B.o + 58) ((1 : ℤ) : ℚ)))
  (.seq (xpow2 L (B.o + 59) (B.rE + 55) (B.rE + 21) one)
  (.seq (xpow2 L (B.o + 76) (B.rE + 55) (B.rE + 54) one)
  (.seq (xpow2 L (B.o + 2) (B.rE + 55) (B.rE + 1) one)
    (toX (VL.ncast L (B.o + 1) rs)))))))))))

/-- The constants of step 2. -/
def xconstO (L : Layout) (B : EllOBlk) (rj rcR rcd rs one : ℕ) : XCmd :=
  .seq (xconstR B rj rcR rcd rs one) (xconstS L B rs one)

/-- The bound on the exponents. -/
def cstX (I : EllOI d) (s κ : ℕ) : ℕ := I.sepEx s + I.eτ + I.eK + κ + 12

/-- The units of `xconstO`. -/
def constOU (X : ℕ) : ℕ := 40 * X + 80

/-- The exponents of EllSpec.lean as sums, for `omega`. -/
theorem expo_eqs (I : EllOI d) (s : ℕ) :
    I.eM = Nat.clog 2 I.base.Rb + 2 ∧ I.eL = I.erK ∧ I.e1 = I.base.j + I.eM + I.erK + 5 ∧
      I.eτ = I.base.j + 2 * I.eM + Nat.clog 2 d + 4 ∧ I.eH = I.eM + I.erK ∧
      I.eη = I.eτ + I.e1 + 11 + 3 * d * (I.eL + I.eτ + 4) ∧ I.jg = I.eη + I.eH + 1 ∧ I.eu = I.eη + 1 ∧
      I.eK = I.eη + I.eH + 2 ∧ I.sepEx s = s + I.e1 + 3 * d * (I.eL + I.eτ + 4) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  unfold EllOI.sepEx; ring

/-- The input registers of the constants: `j`, `lg R̄`, `lg d`, `s`, `1` in ELL-R's block (`lg d` may sit in the
registers `rE + 2` or `rE + 58`), `d`, `erK`, `κ` in the inputs. -/
structure ConstIn (L : Layout) (B : EllOBlk) (rj rcR rcd rs one : ℕ) : Prop where
  rj : B.rE + 64 ≤ rj ∧ rj < L.NN
  rcR : B.rE + 64 ≤ rcR ∧ rcR < L.NN
  rcd : (rcd = B.rE + 2 ∨ rcd = B.rE + 58 ∨ B.rE + 64 ≤ rcd) ∧ rcd < L.NN
  rs : B.rE + 64 ≤ rs ∧ rs < L.NN
  one : B.rE + 64 ≤ one ∧ one < L.NN

set_option maxHeartbeats 4000000 in
/-- The rule of `xconstRA`. -/
theorem XV.constRA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {rj rcR rcd rs one s κ : ℕ} (hB : B.OK L 215 112 14) (hI : ConstIn L B rj rcR rcd rs one)
    (vj : σ.nat rj = I.base.j) (vcR : σ.nat rcR = Nat.clog 2 I.base.Rb) (vcd : σ.nat rcd = Nat.clog 2 d)
    (vK : σ.nat B.rK = I.erK) (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstRA B rj rcR rcd) σ 13 (fun σ' =>
      RegsAre σ' [(B.rE + 31, I.e1), (B.rE + 34, 4), (B.rE + 35, I.eτ), (B.rE + 36, I.eH),
        (B.rE + 37, I.eL + I.eτ), (B.rE + 38, I.eL + I.eτ + 4)] ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => B.rE + 26 ≤ j ∧ j ≤ B.rE + 38) (fun _ _ => False) σ σ') := by
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -⟩ := hB
  obtain ⟨⟨hrj, hrj'⟩, ⟨hrcR, hrcR'⟩, ⟨hrcd, hrcd'⟩, -, -⟩ := hI
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I s
  have hX : cstX I s κ = I.sepEx s + I.eτ + I.eK + κ + 12 := rfl
  have R0 : RegsAre σ [(rj, I.base.j), (rcR, Nat.clog 2 I.base.Rb), (rcd, Nat.clog 2 d), (B.rK, I.erK)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have H0 := FrameA.refl (fun _ => False) (fun j => B.rE + 26 ≤ j ∧ j ≤ B.rE + 38) (fun _ _ => False) σ
  have D0 : σ.draws = σ.draws := rfl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) ?_ (by norm_num)
    (fun _ h => h)
  refine XV.seq (XV.nconstA hL (i := B.rE + 26) (by omega) 2 (by omega)) fun σ1 ⟨w1, d1, G1⟩ => ?_
  have R1 := R0.cons G1 (by simp <;> omega) w1
  have H1 := H0.trans (G1.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D1 := d1.trans D0
  refine XV.seq (XV.naddA hL (i := B.rE + 27) (a := rcR) (b := B.rE + 26) (va := Nat.clog 2 I.base.Rb) (vb := 2) (by omega)
    (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp)) (by omega)) fun σ2 ⟨w2, d2, G2⟩ => ?_
  have R2 := R1.cons G2 (by simp <;> omega) (w2.trans (by omega : Nat.clog 2 I.base.Rb + 2 = I.eM))
  have H2 := H1.trans (G2.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D2 := d2.trans D1
  refine XV.seq (XV.naddA hL (i := B.rE + 28) (a := rj) (b := B.rE + 27) (va := I.base.j) (vb := I.eM) (by omega)
    (by omega) (by omega) (R2.get (by simp)) (R2.get (by simp)) (by omega)) fun σ3 ⟨w3, d3, G3⟩ => ?_
  have R3 := R2.cons G3 (by simp <;> omega) (w3.trans (by omega : I.base.j + I.eM = I.base.j + I.eM))
  have H3 := H2.trans (G3.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D3 := d3.trans D2
  refine XV.seq (XV.naddA hL (i := B.rE + 29) (a := B.rE + 28) (b := B.rK) (va := I.base.j + I.eM) (vb := I.erK) (by omega)
    (by omega) (by omega) (R3.get (by simp)) (R3.get (by simp)) (by omega)) fun σ4 ⟨w4, d4, G4⟩ => ?_
  have R4 := R3.cons G4 (by simp <;> omega) (w4.trans (by omega : I.base.j + I.eM + I.erK = I.base.j + I.eM + I.erK))
  have H4 := H3.trans (G4.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D4 := d4.trans D3
  refine XV.seq (XV.nconstA hL (i := B.rE + 30) (by omega) 5 (by omega)) fun σ5 ⟨w5, d5, G5⟩ => ?_
  have R5 := R4.cons G5 (by simp <;> omega) w5
  have H5 := H4.trans (G5.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D5 := d5.trans D4
  refine XV.seq (XV.naddA hL (i := B.rE + 31) (a := B.rE + 29) (b := B.rE + 30) (va := I.base.j + I.eM + I.erK) (vb := 5) (by omega)
    (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp)) (by omega)) fun σ6 ⟨w6, d6, G6⟩ => ?_
  have R6 := R5.cons G6 (by simp <;> omega) (w6.trans (by omega : I.base.j + I.eM + I.erK + 5 = I.e1))
  have H6 := H5.trans (G6.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D6 := d6.trans D5
  refine XV.seq (XV.naddA hL (i := B.rE + 32) (a := B.rE + 28) (b := B.rE + 27) (va := I.base.j + I.eM) (vb := I.eM) (by omega)
    (by omega) (by omega) (R6.get (by simp)) (R6.get (by simp)) (by omega)) fun σ7 ⟨w7, d7, G7⟩ => ?_
  have R7 := R6.cons G7 (by simp <;> omega) (w7.trans (by omega : I.base.j + I.eM + I.eM = I.base.j + I.eM + I.eM))
  have H7 := H6.trans (G7.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D7 := d7.trans D6
  refine XV.seq (XV.naddA hL (i := B.rE + 33) (a := B.rE + 32) (b := rcd) (va := I.base.j + I.eM + I.eM) (vb := Nat.clog 2 d) (by omega)
    (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp)) (by omega)) fun σ8 ⟨w8, d8, G8⟩ => ?_
  have R8 := R7.cons G8 (by simp <;> omega) (w8.trans (by omega : I.base.j + I.eM + I.eM + Nat.clog 2 d = I.base.j + I.eM + I.eM + Nat.clog 2 d))
  have H8 := H7.trans (G8.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D8 := d8.trans D7
  refine XV.seq (XV.nconstA hL (i := B.rE + 34) (by omega) 4 (by omega)) fun σ9 ⟨w9, d9, G9⟩ => ?_
  have R9 := R8.cons G9 (by simp <;> omega) w9
  have H9 := H8.trans (G9.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D9 := d9.trans D8
  refine XV.seq (XV.naddA hL (i := B.rE + 35) (a := B.rE + 33) (b := B.rE + 34) (va := I.base.j + I.eM + I.eM + Nat.clog 2 d) (vb := 4) (by omega)
    (by omega) (by omega) (R9.get (by simp)) (R9.get (by simp)) (by omega)) fun σ10 ⟨w10, d10, G10⟩ => ?_
  have R10 := R9.cons G10 (by simp <;> omega) (w10.trans (by omega : I.base.j + I.eM + I.eM + Nat.clog 2 d + 4 = I.eτ))
  have H10 := H9.trans (G10.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D10 := d10.trans D9
  refine XV.seq (XV.naddA hL (i := B.rE + 36) (a := B.rE + 27) (b := B.rK) (va := I.eM) (vb := I.erK) (by omega)
    (by omega) (by omega) (R10.get (by simp)) (R10.get (by simp)) (by omega)) fun σ11 ⟨w11, d11, G11⟩ => ?_
  have R11 := R10.cons G11 (by simp <;> omega) (w11.trans (by omega : I.eM + I.erK = I.eH))
  have H11 := H10.trans (G11.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D11 := d11.trans D10
  refine XV.seq (XV.naddA hL (i := B.rE + 37) (a := B.rK) (b := B.rE + 35) (va := I.erK) (vb := I.eτ) (by omega)
    (by omega) (by omega) (R11.get (by simp)) (R11.get (by simp)) (by omega)) fun σ12 ⟨w12, d12, G12⟩ => ?_
  have R12 := R11.cons G12 (by simp <;> omega) (w12.trans (by omega : I.erK + I.eτ = I.eL + I.eτ))
  have H12 := H11.trans (G12.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D12 := d12.trans D11
  refine XV.mono (XV.naddA hL (i := B.rE + 38) (a := B.rE + 37) (b := B.rE + 34) (va := I.eL + I.eτ) (vb := 4) (by omega)
    (by omega) (by omega) (R12.get (by simp)) (R12.get (by simp)) (by omega)) le_rfl fun σ13 ⟨w13, d13, G13⟩ => ?_
  have R13 := R12.cons G13 (by simp <;> omega) (w13.trans (by omega : I.eL + I.eτ + 4 = I.eL + I.eτ + 4))
  have H13 := H12.trans (G13.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D13 := d13.trans D12
  refine ⟨fun p hp => ?_, D13, H13⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact R13.get (by simp)

set_option maxHeartbeats 4000000 in
/-- The rule of `xconstRB`. -/
theorem XV.constRB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllOBlk}
    {I : EllOI d} {one s κ : ℕ} (hB : B.OK L 215 112 14) (hone : B.rE + 64 ≤ one ∧ one < L.NN)
    (R0 : RegsAre σ [(B.rd, d), (B.rκ, κ), (one, 1), (B.rE + 31, I.e1), (B.rE + 34, 4), (B.rE + 35, I.eτ),
      (B.rE + 36, I.eH), (B.rE + 37, I.eL + I.eτ), (B.rE + 38, I.eL + I.eτ + 4)])
    (hXa : cstX I s κ < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconstRB B one) σ 13 (fun σ' =>
      RegsAre σ' [(B.rE + 41, 3 * d * (I.eL + I.eτ + 4)), (B.rE + 21, I.jg), (B.rE + 47, I.eu),
        (B.rE + 1, I.eK + κ), (B.rE + 3, I.eL + I.eτ + 3)] ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = B.rE + 1 ∨ j = B.rE + 3 ∨ j = B.rE + 21 ∨ (B.rE + 39 ≤ j ∧ j ≤ B.rE + 48))
        (fun _ _ => False) σ σ') := by
  obtain ⟨hoS, hrN, haA, -, -, -, hrd, hrK, hrκ, -⟩ := hB
  obtain ⟨hone, hone'⟩ := hone
  obtain ⟨heM, heL, he1, heτ, heH, heη, hjg, heu, heK, hE⟩ := expo_eqs I s
  have hX : cstX I s κ = I.sepEx s + I.eτ + I.eK + κ + 12 := rfl
  have hQd : 3 * d ≤ 3 * d * (I.eL + I.eτ + 4) := Nat.le_mul_of_pos_right _ (by omega)
  have H0 := FrameA.refl (fun _ => False)
    (fun j => j = B.rE + 1 ∨ j = B.rE + 3 ∨ j = B.rE + 21 ∨ (B.rE + 39 ≤ j ∧ j ≤ B.rE + 48)) (fun _ _ => False) σ
  have D0 : σ.draws = σ.draws := rfl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))) ?_ (by norm_num)
    (fun _ h => h)
  refine XV.seq (XV.nconstA hL (i := B.rE + 39) (by omega) 3 (by omega)) fun σ1 ⟨w1, d1, G1⟩ => ?_
  have R1 := R0.cons G1 (by simp <;> omega) w1
  have H1 := H0.trans (G1.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D1 := d1.trans D0
  refine XV.seq (XV.nmulA hL (i := B.rE + 40) (a := B.rE + 39) (b := B.rd) (va := 3) (vb := d) (by omega)
    (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp)) (by omega) (by omega) (by omega)) fun σ2 ⟨w2, d2, G2⟩ => ?_
  have R2 := R1.cons G2 (by simp <;> omega) w2
  have H2 := H1.trans (G2.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D2 := d2.trans D1
  refine XV.seq (XV.nmulA hL (i := B.rE + 41) (a := B.rE + 40) (b := B.rE + 38) (va := 3 * d) (vb := I.eL + I.eτ + 4) (by omega)
    (by omega) (by omega) (R2.get (by simp)) (R2.get (by simp)) (by omega) (by omega) (by omega)) fun σ3 ⟨w3, d3, G3⟩ => ?_
  have R3 := R2.cons G3 (by simp <;> omega) w3
  have H3 := H2.trans (G3.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D3 := d3.trans D2
  refine XV.seq (XV.nconstA hL (i := B.rE + 42) (by omega) 11 (by omega)) fun σ4 ⟨w4, d4, G4⟩ => ?_
  have R4 := R3.cons G4 (by simp <;> omega) w4
  have H4 := H3.trans (G4.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D4 := d4.trans D3
  refine XV.seq (XV.naddA hL (i := B.rE + 43) (a := B.rE + 35) (b := B.rE + 31) (va := I.eτ) (vb := I.e1) (by omega)
    (by omega) (by omega) (R4.get (by simp)) (R4.get (by simp)) (by omega)) fun σ5 ⟨w5, d5, G5⟩ => ?_
  have R5 := R4.cons G5 (by simp <;> omega) (w5.trans (by omega : I.eτ + I.e1 = I.eτ + I.e1))
  have H5 := H4.trans (G5.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D5 := d5.trans D4
  refine XV.seq (XV.naddA hL (i := B.rE + 44) (a := B.rE + 43) (b := B.rE + 42) (va := I.eτ + I.e1) (vb := 11) (by omega)
    (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp)) (by omega)) fun σ6 ⟨w6, d6, G6⟩ => ?_
  have R6 := R5.cons G6 (by simp <;> omega) (w6.trans (by omega : I.eτ + I.e1 + 11 = I.eτ + I.e1 + 11))
  have H6 := H5.trans (G6.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D6 := d6.trans D5
  refine XV.seq (XV.naddA hL (i := B.rE + 45) (a := B.rE + 44) (b := B.rE + 41) (va := I.eτ + I.e1 + 11) (vb := 3 * d * (I.eL + I.eτ + 4)) (by omega)
    (by omega) (by omega) (R6.get (by simp)) (R6.get (by simp)) (by omega)) fun σ7 ⟨w7, d7, G7⟩ => ?_
  have R7 := R6.cons G7 (by simp <;> omega) (w7.trans (by omega : I.eτ + I.e1 + 11 + 3 * d * (I.eL + I.eτ + 4) = I.eη))
  have H7 := H6.trans (G7.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D7 := d7.trans D6
  refine XV.seq (XV.naddA hL (i := B.rE + 46) (a := B.rE + 45) (b := B.rE + 36) (va := I.eη) (vb := I.eH) (by omega)
    (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp)) (by omega)) fun σ8 ⟨w8, d8, G8⟩ => ?_
  have R8 := R7.cons G8 (by simp <;> omega) (w8.trans (by omega : I.eη + I.eH = I.eη + I.eH))
  have H8 := H7.trans (G8.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D8 := d8.trans D7
  refine XV.seq (XV.naddA hL (i := B.rE + 21) (a := B.rE + 46) (b := one) (va := I.eη + I.eH) (vb := 1) (by omega)
    (by omega) (by omega) (R8.get (by simp)) (R8.get (by simp)) (by omega)) fun σ9 ⟨w9, d9, G9⟩ => ?_
  have R9 := R8.cons G9 (by simp <;> omega) (w9.trans (by omega : I.eη + I.eH + 1 = I.jg))
  have H9 := H8.trans (G9.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D9 := d9.trans D8
  refine XV.seq (XV.naddA hL (i := B.rE + 47) (a := B.rE + 45) (b := one) (va := I.eη) (vb := 1) (by omega)
    (by omega) (by omega) (R9.get (by simp)) (R9.get (by simp)) (by omega)) fun σ10 ⟨w10, d10, G10⟩ => ?_
  have R10 := R9.cons G10 (by simp <;> omega) (w10.trans (by omega : I.eη + 1 = I.eu))
  have H10 := H9.trans (G10.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D10 := d10.trans D9
  refine XV.seq (XV.naddA hL (i := B.rE + 48) (a := B.rE + 21) (b := one) (va := I.jg) (vb := 1) (by omega)
    (by omega) (by omega) (R10.get (by simp)) (R10.get (by simp)) (by omega)) fun σ11 ⟨w11, d11, G11⟩ => ?_
  have R11 := R10.cons G11 (by simp <;> omega) (w11.trans (by omega : I.jg + 1 = I.eK))
  have H11 := H10.trans (G11.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D11 := d11.trans D10
  refine XV.seq (XV.naddA hL (i := B.rE + 1) (a := B.rE + 48) (b := B.rκ) (va := I.eK) (vb := κ) (by omega)
    (by omega) (by omega) (R11.get (by simp)) (R11.get (by simp)) (by omega)) fun σ12 ⟨w12, d12, G12⟩ => ?_
  have R12 := R11.cons G12 (by simp <;> omega) (w12.trans (by omega : I.eK + κ = I.eK + κ))
  have H12 := H11.trans (G12.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D12 := d12.trans D11
  refine XV.mono (XV.naddA hL (i := B.rE + 3) (a := B.rE + 37) (b := B.rE + 39) (va := I.eL + I.eτ) (vb := 3) (by omega)
    (by omega) (by omega) (R12.get (by simp)) (R12.get (by simp)) (by omega)) le_rfl fun σ13 ⟨w13, d13, G13⟩ => ?_
  have R13 := R12.cons G13 (by simp <;> omega) (w13.trans (by omega : I.eL + I.eτ + 3 = I.eL + I.eτ + 3))
  have H13 := H12.trans (G13.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  have D13 := d13.trans D12
  refine ⟨fun p hp => ?_, D13, H13⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact R13.get (by simp)

end AdversarialBco.Uni.EllO
