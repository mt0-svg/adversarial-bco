/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriTestM
public import AdversarialBco.Unified.ProgOSepU

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the stage test

The test block `xtstT` of the stage gauge: for a point `(D; N)` in `aT + 24`, the position map into `aT + 25`
(`xtMapT`), the CM block `xcmU` on it at the precision `stK` (centre `(D_a; N_a)` in `aKa`, `r₀ = r_n/r_d` in
`sR0n`, `sR0d`), its answer into `rT + 34`, then the cube check (`xcube`). `tstT_OK`: a test block (`TestOK`,
SepSpec.lean) for the stage test `stTest orc a r₀ R₀ j (posZ P)` (BLOSpec.lean).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix

variable {d : ℕ}

/-! ## The cube check over the coordinates -/

/-- The units of `xcubeB`. -/
abbrev cubeBK : ℕ := 2 + (1 + (2 + (1 + (1 + (1 + (1 + ((1 + 2) + (1 + 2))))))))

/-- The units of `xcube`. -/
abbrev cubeK (d : ℕ) : ℕ := 1 + (2 + (2 + (1 + (1 + (1 + (d * ((1 + cubeBK) + 3) + 3))))))

/-- The slots of the cube check. -/
abbrev cbS (y : ℕ) : Prop := oT + 306 ≤ y ∧ y < oT + 311

/-- The registers of the cube check. -/
abbrev cbN (j : ℕ) : Prop := j = rT + 34 ∨ j = rT + 69 ∨ j = rT + 70

set_option maxHeartbeats 4000000 in
/-- **The cube check**: `rT + 34` keeps its value `c` when every coordinate passes
`|N_q,i D_a - N_a,i D_q| r_d ≤ 2^{j+1} r_n D_q D_a`, and drops to `0` otherwise. -/
theorem XV.cube {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    {Nq Na : Fin d → ℤ} {Da Dq rn rd : ℤ} {c j b1 m : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rT = 1) (eZ : σ.sc (oT + 1) = 0)
    (eq0 : σ.arr (aT + 25) 0 = Dq) (eNq : ∀ i : Fin d, σ.arr (aT + 25) (1 + (i : ℕ)) = Nq i)
    (ea0 : σ.arr aKa 0 = Da) (eNa : ∀ i : Fin d, σ.arr aKa (1 + (i : ℕ)) = Na i)
    (ern : σ.sc sR0n = rn) (erd : σ.sc sR0d = rd) (e2j : σ.sc (oT + 36) = ((2 ^ (j + 1) : ℤ) : ℝ))
    (ec : σ.nat (rT + 34) = c)
    (bNq : ∀ i, |Nq i| ≤ 2 ^ b1) (bDq : |Dq| ≤ 2 ^ b1) (bNa : ∀ i, |Na i| ≤ 2 ^ m) (bDa : |Da| ≤ 2 ^ m)
    (brn : |rn| ≤ 2 ^ m) (brd : |rd| ≤ 2 ^ m) (hrd : 0 < rd) (hj : j + 1 ≤ m) (hℓ : b1 + 3 * m + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xcube L) σ (cubeK d)
      (fun σ' => σ'.nat (rT + 34) =
          (if ∀ i : Fin d, |Nq i * Da - Na i * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da then c else 0) ∧
        σ'.draws = σ.draws ∧ FrameA cbS cbN (fun _ _ => False) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdasz : d ≤ asz d := by unfold asz; nlinarith
  have hlt : ∀ {z : ℤ} {a : ℕ}, |z| ≤ 2 ^ a → a < ℓ → |z| < 2 ^ ℓ := fun h ha => lt_of_le_of_lt h (powZ_lt ha)
  set R : ℤ := 2 ^ (j + 1) * rn * Dq * Da with hR
  have b2j : |(2 : ℤ) ^ (j + 1)| ≤ 2 ^ m := by rw [abs_of_pos (by positivity)]; exact powZ_le hj
  have bA : |(2 : ℤ) ^ (j + 1) * rn| ≤ 2 ^ (m + m) := absI_mul_le b2j brn
  have bB : |(2 : ℤ) ^ (j + 1) * rn * Dq| ≤ 2 ^ (m + m + b1) := absI_mul_le bA bDq
  have bC : |R| ≤ 2 ^ (m + m + b1 + m) := absI_mul_le bB bDa
  have bR : |R| ≤ 2 ^ (b1 + 3 * m) := bC.trans (powZ_le (by omega))
  -- the constants
  refine XV.seq (XV.nconst hL (σ := σ) (i := rT + 69) (by omega) 0 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL (x := oT + 306) (a := aKa) (i := rT + 69) (by omega) (by simp only [aKa]; omega)
    (by omega) (by simp only [nat_setNat_eq]; exact lt_aszT hd1 (by omega))
    (by simp only [nat_setNat_eq, Env.setNat_arr, ea0]; exact intR_lt bDa (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.aget hL (x := oT + 307) (a := aT + 25) (i := rT + 69) (by omega) (by omega)
    (by omega) (by simp only [Env.setSc_nat, nat_setNat_eq]; exact lt_aszT hd1 (by omega))
    (by simp only [Env.setSc_nat, Env.setSc_arr, nat_setNat_eq, Env.setNat_arr, eq0]; exact intR_lt bDq (by omega)))
    fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := oT + 308) (a := oT + 36) (b := sR0n) (by omega) (by omega)
    (by simp only [sR0n]; omega) (u := 2 ^ (j + 1)) (v := rn) (by simp [e2j]) (by simp [sR0n, ern])
    (hlt b2j (by omega)) (hlt brn (by omega)) (hlt bA (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := oT + 308) (a := oT + 308) (b := oT + 307) (by omega) (by omega) (by omega)
    (u := 2 ^ (j + 1) * rn) (v := Dq) (by simp) (by simp [eq0]) (hlt bA (by omega)) (hlt bDq (by omega))
    (hlt bB (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.mulI hL (x := oT + 308) (a := oT + 308) (b := oT + 306) (by omega) (by omega) (by omega)
    (u := 2 ^ (j + 1) * rn * Dq) (v := Da) (by simp) (by simp [ea0]) (hlt bB (by omega)) (hlt bDa (by omega))
    (hlt bC (by omega))) fun σ6 e6 => ?_
  subst e6
  set σ6 := (((((σ.setNat (rT + 69) 0).setSc (oT + 306) ((σ.setNat (rT + 69) 0).arr aKa
    ((σ.setNat (rT + 69) 0).nat (rT + 69)))).setSc (oT + 307) _).setSc (oT + 308) ((2 ^ (j + 1) * rn : ℤ) : ℝ)).setSc
    (oT + 308) ((2 ^ (j + 1) * rn * Dq : ℤ) : ℝ)).setSc (oT + 308) ((2 ^ (j + 1) * rn * Dq * Da : ℤ) : ℝ) with hσ6
  have F6 : FrameA cbS cbN (fun _ _ => False) σ σ6 := by
    rw [hσ6]
    exact ((((((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inl rfl)) _).setSc ⟨by omega, by omega⟩ _).setSc
      ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
      ⟨by omega, by omega⟩ _
  have s6 : σ6.sc (oT + 306) = Da := by simp [hσ6, ea0]
  have s7 : σ6.sc (oT + 307) = Dq := by simp [hσ6, eq0]
  have s8 : σ6.sc (oT + 308) = R := by simp [hσ6, hR]
  -- the loop
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat (rT + 34) = (if ∀ i : Fin d, (i : ℕ) < t →
      |Nq i * Da - Na i * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da then c else 0) ∧
    σ'.draws = σ.draws ∧ σ'.sc (oT + 306) = Da ∧ σ'.sc (oT + 307) = Dq ∧ σ'.sc (oT + 308) = R ∧
    FrameA cbS cbN (fun _ _ => False) σ σ'
  have hJ0 : J 0 (σ6.setNat (rT + 69) 0) := by
    refine ⟨?_, by simp [hσ6], by simp [s6], by simp [s7], by simp [s8], F6.setNat (Or.inr (Or.inl rfl)) _⟩
    simp [hσ6, ec]
  refine XV.mono (XV.forN hL (i := rT + 69) (n := rD) (one := rT) (by omega) (by simp only [rD]; omega)
    (by omega) (by simp only [rD]; omega) (by omega) d (1 + cubeBK) (by unfold asz at hda; nlinarith) J σ6
    (by rw [F6.1 _ (by simp only [cbN, rD]; omega), hD]) (by rw [F6.1 _ (by simp only [cbN]; omega), h1]) hJ0 ?_)
    le_rfl fun σ' h => ⟨by
      rw [h.1.1]
      by_cases hh : ∀ i : Fin d, |Nq i * Da - Na i * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da
      · rw [if_pos (fun i _ => hh i), if_pos hh]
      · rw [if_neg (fun h' => hh fun i => h' i i.2), if_neg hh], h.1.2.1, h.1.2.2.2.2.2⟩
  intro t ht σ' hJ ht' hn' h1'
  obtain ⟨n', d', s6', s7', s8', F'⟩ := hJ
  refine XV.seq (XV.nadd hL (σ := σ') (i := rT + 70) (a := rT + 69) (b := rT) (by omega) (by omega)
    (by omega) (by rw [ht']; unfold asz at hda; nlinarith) (by rw [h1']; omega)) fun σ1 e1 => ?_
  subst e1
  have hi : (σ'.setNat (rT + 70) (σ'.nat (rT + 69) + σ'.nat rT)).nat (rT + 70) = 1 + t := by
    rw [nat_setNat_eq, ht', h1']; omega
  refine XV.mono (XV.cubeB hL hS hN hA hd1 (i := t) ht (Nq := Nq ⟨t, ht⟩) (Na := Na ⟨t, ht⟩) (Da := Da)
    (Dq := Dq) (rd := rd) (R := R) (b1 := b1) (m := m)
    (c := if ∀ i : Fin d, (i : ℕ) < t → |Nq i * Da - Na i * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da then c else 0) hi
    (by rw [Env.setNat_sc, F'.2.1 _ (by simp only [cbS]; omega), eZ])
    (by rw [Env.setNat_arr, F'.2.2.1 _ _ id]; exact eNq ⟨t, ht⟩)
    (by rw [Env.setNat_arr, F'.2.2.1 _ _ id]; exact eNa ⟨t, ht⟩)
    (by rw [Env.setNat_sc, s6']) (by rw [Env.setNat_sc, s7']) (by rw [Env.setNat_sc, s8'])
    (by rw [Env.setNat_sc, F'.2.1 _ (by simp only [cbS, sR0d]; omega), erd])
    (by rw [nat_setNat_ne _ (by omega), n']) (bNq _) bDq (bNa _) bDa brd bR hrd hℓ) le_rfl
    fun σ2 ⟨n2, d2, F2⟩ => ?_
  have k69 : σ2.nat (rT + 69) = t := by rw [F2.1 _ (by omega), nat_setNat_ne _ (by omega), ht']
  refine ⟨k69, by rw [F2.1 _ (by simp only [rD]; omega), nat_setNat_ne _ (by simp only [rD]; omega), hn'],
    by rw [F2.1 _ (by omega), nat_setNat_ne _ (by omega), h1'], ?_, by rw [Env.setNat_draws, d2,
      Env.setNat_draws, d'], by rw [Env.setNat_sc, F2.2.1 _ (by omega), Env.setNat_sc, s6'],
    by rw [Env.setNat_sc, F2.2.1 _ (by omega), Env.setNat_sc, s7'],
    by rw [Env.setNat_sc, F2.2.1 _ (by omega), Env.setNat_sc, s8'], ?_⟩
  · rw [nat_setNat_ne _ (by omega), n2]
    by_cases ht2 : |Nq ⟨t, ht⟩ * Da - Na ⟨t, ht⟩ * Dq| * rd ≤ R
    · rw [if_pos ht2]
      by_cases hall : ∀ i : Fin d, (i : ℕ) < t → |Nq i * Da - Na i * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da
      · rw [if_pos hall, if_pos]
        intro i hi'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
        · exact hall i h
        · have : i = ⟨t, ht⟩ := Fin.ext h
          subst this; exact ht2
      · rw [if_neg hall, if_neg (fun h' => hall fun i hi' => h' i (by omega))]
    · rw [if_neg ht2, if_neg (fun h' => ht2 (h' ⟨t, ht⟩ (by simp)))]
  · exact ((F'.setNat (Or.inr (Or.inr rfl)) _).trans (F2.mono (fun y h => by simp only [cbS]; omega)
      (fun j h => by simp only [cbN]; omega) (fun _ _ h => h))).setNat (Or.inr (Or.inl rfl)) _

/-! ## The test block -/

/-- The cells of the CM block `xcmU` in the stage test: the centre in `aKa`, `r₀` in `sR0n`, `sR0d`, the precision in
`rNk` and its power of `2` in `sC2k`, the point in `aT + 25`, the answer in `rT + 35`, the query point in `aT + 26`,
scratch slots from `oT + 290`, registers from `rT + 60`. -/
def cLT : CMLay := ⟨aKa, sR0n, sR0d, rNk, sC2k, aT + 25, rT + 35, aT + 26, oT + 290, rT + 60⟩

theorem cLT_OK {L : Layout} (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) :
    CMLay.OKU L cLT := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_⟩ <;>
    simp only [cLT, aKa, sR0n, sR0d, rNk, sC2k, oT, rT, aT] at * <;> omega

/-- **The stage test** on the point `(D; N)` of `aT + 24`: the position map, the CM block, its answer into `rT + 34`,
the cube check. -/
def xtstT (L : Layout) : XCmdO :=
  .seq (.base (xtMapT L)) <| .seq (xcmU L cLT) <|
  .base (.seq (.prim (.frag (.nconst (rT + 34) 0))) (.seq (.prim (.frag (.nadd (rT + 34) (rT + 34) (rT + 35))))
    (xcube L)))

/-- The units of the stage test. -/
abbrev tstTK (d : ℕ) : ℕ := ((d * (1 + (2 + 2) + 3) + 3) + ((d * (d * 10 + 9) + 4) +
  (1 + (2 + (1 + (2 + (1 + (d * (ieMapT.units + 6) + 3)))))))) + (cmK d + (1 + (1 + cubeK d)))

/-- The data the stage test reads: `d`, `1`, `0`, the stage (`P`, `2^{j+1}`) and the CM block's data. -/
structure TDatT (P : StZ d) (j : ℕ) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (k : ℕ) (σ : Env d) : Prop where
  hd : σ.nat rD = d
  h1 : σ.nat rT = 1
  hz : σ.sc (oT + 1) = 0
  st : StAtO σ j P
  cm : CMDatU cLT Da Na rn rd k σ

/-- The slots the stage test writes. -/
abbrev tsS (y : ℕ) : Prop := oT + 290 ≤ y

/-- The registers the stage test writes. -/
abbrev tsN (j : ℕ) : Prop := j = rT + 34 ∨ j = rT + 35 ∨ rT + 60 ≤ j

/-- The arrays the stage test writes. -/
abbrev tsA (b _k : ℕ) : Prop := aT + 25 ≤ b

theorem posZ_map (P : StZ d) (D : ℤ) (Nv : Fin d → ℤ) (hP : P.D ≠ 0) (hD : D ≠ 0) :
    (posZ P).1 + (posZ P).2 *ᵥ ptDN D Nv = ptDN (P.D * D) (fun i => P.mu i * D + (P.T *ᵥ Nv) i) := by
  funext i
  have hP' : (P.D : ℚ) ≠ 0 := by exact_mod_cast hP
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  simp only [posZ, ptDN, Pi.add_apply, Matrix.mulVec, dotProduct]
  have hs : ∑ l, (P.T i l : ℚ) / P.D * ((Nv l : ℚ) / D) = (∑ l, (P.T i l : ℚ) * Nv l) / (P.D * D) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun l _ => by field_simp
  rw [hs]
  push_cast
  field_simp

theorem cube_iff {Nz Na Dq Da rn rd : ℤ} (hDq : 0 < Dq) (hDa : 0 < Da) (hrd : 0 < rd) (j : ℕ) :
    |(Nz : ℚ) / Dq - (Na : ℚ) / Da| ≤ 2 ^ (j + 1) * ((rn : ℚ) / rd) ↔
      |Nz * Da - Na * Dq| * rd ≤ 2 ^ (j + 1) * rn * Dq * Da := by
  have hDq' : (0 : ℚ) < Dq := by exact_mod_cast hDq
  have hDa' : (0 : ℚ) < Da := by exact_mod_cast hDa
  have hrd' : (0 : ℚ) < rd := by exact_mod_cast hrd
  have hpos : (0 : ℚ) < Dq * Da := mul_pos hDq' hDa'
  have e1 : (Nz : ℚ) / Dq - (Na : ℚ) / Da = ((Nz : ℚ) * Da - Na * Dq) / (Dq * Da) := by field_simp
  have e2 : 2 ^ (j + 1) * ((rn : ℚ) / rd) * (Dq * Da) = (2 ^ (j + 1) * rn * Dq * Da) / rd := by field_simp
  rw [e1, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, e2, le_div_iff₀ hrd']
  constructor <;> intro h <;> exact_mod_cast h

set_option maxHeartbeats 4000000 in
/-- **The stage test block** (`TestOK`): from the data `TDatT` (the stage `P` at `j`, the centre `N_a/D_a = a`,
`r₀ = r_n/r_d`, the precision `stK` and its power of `2`), for every point `(D; N)` of `aT + 24` below `2^bt`, `xtstT`
writes into `rT + 34` the stage test `stTest orc a r₀ R₀ j (posZ P)` at `N/D`; every datum below `2^m`. -/
theorem tstT_OK {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    {P : StZ d} {j : ℕ} {a : Fin d → ℚ} {r0 R0 : ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {m bt : ℕ}
    (hPD : 0 < P.D) (bPD : P.D ≤ 2 ^ m) (bmu : ∀ i, |P.mu i| ≤ 2 ^ m) (bT : ∀ i l, |P.T i l| ≤ 2 ^ m)
    (hdm : d ≤ 2 ^ m) (hDa : 0 < Da) (bDa : Da < 2 ^ m) (bNa : ∀ i, |Na i| < 2 ^ m) (hrn : 0 < rn)
    (brn : rn < 2 ^ m) (hrd : 0 < rd) (brd : rd < 2 ^ m) (ha : ∀ i, (Na i : ℚ) / Da = a i)
    (hr : (rn : ℚ) / rd = r0) (hj : j + 1 ≤ m) (hℓ : 8 * m + 2 * bt + stK d r0 R0 + 16 ≤ ℓ)
    (hk : stK d r0 R0 < 2 ^ ℓa) :
    TestOK L XO ℓa ℓ (xtstT L) (TDatT P j Da Na rn rd (stK d r0 R0)) (aT + 24) (rT + 34) bt
      (stTest XO.w.orc a r0 R0 j (posZ P)) (tstTK d) tsS tsN tsA := by
  intro σ D Nv hdat hD0 hDb hNvb hD hNv
  have hL1 := hL.1
  set k := stK d r0 R0 with hkdef
  have bD : |D| ≤ 2 ^ bt := by rw [abs_of_pos hD0]; exact hDb.le
  have bNv : ∀ i, |Nv i| ≤ 2 ^ bt := fun i => (hNvb i).le
  have bPD' : |P.D| ≤ 2 ^ m := by rw [abs_of_pos hPD]; exact bPD
  obtain ⟨st0, st1, st2, st3⟩ := hdat.st
  refine XVO.seq (XVO.ofX (XV.tMapT hL hS hN hA hd1 (DS := P.D) (muS := P.mu) (aS := P.T) (m := m) (bt := bt)
    hdat.hd hdat.h1 hdat.hz st2 st0 st1 hD hNv bPD' bmu bT hdm bD bNv (by omega))) fun σ1 h1 => ?_
  obtain ⟨a0, a1, d1, F1⟩ := h1
  -- the CM block
  set bt' := 2 * m + bt + 2 with hbt'
  set Nz : Fin d → ℤ := fun i => P.mu i * D + (P.T *ᵥ Nv) i with hNz
  have hDD : 0 < P.D * D := mul_pos hPD hD0
  have bDD : P.D * D < 2 ^ bt' := by
    calc P.D * D ≤ 2 ^ m * 2 ^ bt := mul_le_mul bPD hDb.le hD0.le (by positivity)
      _ = 2 ^ (m + bt) := by rw [pow_add]
      _ < 2 ^ bt' := powZ_lt (by omega)
  have bNz : ∀ i, |Nz i| < 2 ^ bt' := fun i => by
    have h1 : |P.mu i * D| ≤ 2 ^ (2 * m + bt) := (absI_mul_le (bmu i) bD).trans (powZ_le (by omega))
    have h2 : |(P.T *ᵥ Nv) i| ≤ 2 ^ (2 * m + bt) := by
      have := mulVec_abs_le (a := m) (b := bt) (c := m) bT bNv hdm i
      exact this.trans (powZ_le (by omega))
    calc |Nz i| ≤ |P.mu i * D| + |(P.T *ᵥ Nv) i| := abs_add_le _ _
      _ ≤ 2 ^ (2 * m + bt) + 2 ^ (2 * m + bt) := add_le_add h1 h2
      _ = 2 ^ (2 * m + bt + 1) := by ring
      _ < 2 ^ bt' := powZ_lt (by omega)
  have hcm : CMDatU cLT Da Na rn rd k σ1 := by
    obtain ⟨⟨c0, c1, c2, c3, c4, c5⟩, c6⟩ := hdat.cm
    refine ⟨⟨?_, fun i => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [F1.2.2.1 _ _ (by simp only [tmA, cLT, aKa]; omega)]; exact c0
    · rw [F1.2.2.1 _ _ (by simp only [tmA, cLT, aKa]; omega)]; exact c1 i
    · rw [F1.2.1 _ (by simp only [tmS, cLT, sR0n]; omega)]; exact c2
    · rw [F1.2.1 _ (by simp only [tmS, cLT, sR0d]; omega)]; exact c3
    · rw [F1.1 _ (by simp only [tmN, cLT, rNk]; omega)]; exact c4
    · rw [F1.2.1 _ (by simp only [tmS, cLT, sC2k]; omega)]; exact c5
    · rw [F1.1 _ (by simp only [tmN]; omega)]; exact c6
  refine XVO.seq (cmBlockOKU L XO ℓa ℓ cLT Da Na rn rd k m bt' hL (cLT_OK hS hN hA) hd1 hDa hrn hrd bDa bNa brn
    brd (by omega) hk σ1 (P.D * D) Nz hcm hDD bDD bNz (by simpa [cLT] using a0)
    (fun i => by show σ1.arr (aT + 25) (1 + (i : ℕ)) = _; rw [a1 i, hNz]; push_cast; ring)) fun σ2 h2 => ?_
  obtain ⟨t2, F2, d2⟩ := h2
  have G2 : FrameA tsS tsN tsA σ σ2 :=
    (F1.mono (fun y h => by simp only [tmS] at h; simp only [tsS]; omega)
      (fun j h => by simp only [tmN] at h; simp only [tsN]; omega)
      (fun b _ h => by simp only [tmA] at h; simp only [tsA]; omega)).trans
      (F2.mono (fun y h => by simp only [cmS, cLT] at h; simp only [tsS]; omega)
        (fun j h => by simp only [cmN, cLT] at h; simp only [tsN]; omega)
        (fun b _ h => by simp only [cmAr, cLT] at h; simp only [tsA]; omega))
  set cA : Bool := cmQ XO.w.orc (ptDN Da Na) ((rn : ℚ) / rd) k (ptDN (P.D * D) Nz) with hcA
  have ht2 : σ2.nat (rT + 35) = if cA = true then 1 else 0 := t2
  have t2b : σ2.nat (rT + 35) ≤ 1 := by rw [ht2]; split_ifs <;> omega
  -- the answer, then the cube
  refine XVO.ofX (XV.seq (XV.nconst hL (σ := σ2) (i := rT + 34) (by omega) 0 (by omega)) fun σ3 e3 => ?_)
  subst e3
  refine XV.seq (XV.nadd hL (σ := σ2.setNat (rT + 34) 0) (i := rT + 34) (a := rT + 34) (b := rT + 35) (by omega)
    (by omega) (by omega) (by rw [nat_setNat_eq]; positivity) (by rw [nat_setNat_ne _ (by omega)]; omega))
    fun σ4 e4 => ?_
  subst e4
  set σ4 := (σ2.setNat (rT + 34) 0).setNat (rT + 34)
    ((σ2.setNat (rT + 34) 0).nat (rT + 34) + (σ2.setNat (rT + 34) 0).nat (rT + 35)) with hσ4
  have n4 : σ4.nat (rT + 34) = if cA = true then 1 else 0 := by
    rw [hσ4, nat_setNat_eq, nat_setNat_eq, nat_setNat_ne _ (by omega), ht2, zero_add]
  have G4 : FrameA tsS tsN tsA σ σ4 := by
    rw [hσ4]; exact (G2.setNat (Or.inl rfl) _).setNat (Or.inl rfl) _
  have eq4 : ∀ y, ¬ tsS y → σ4.sc y = σ.sc y := fun y h => G4.2.1 y h
  have en4 : ∀ j, ¬ tsN j → σ4.nat j = σ.nat j := fun j h => G4.1 j h
  have a25 : ∀ q, σ4.arr (aT + 25) q = σ2.arr (aT + 25) q := fun q => by rw [hσ4]; simp
  have aKa4 : ∀ q, σ4.arr aKa q = σ.arr aKa q := fun q => G4.2.2.1 _ _ (by simp only [tsA, aKa]; omega)
  have bNz' : ∀ i, |Nz i| ≤ 2 ^ bt' := fun i => (bNz i).le
  have bDD' : |P.D * D| ≤ 2 ^ bt' := by rw [abs_of_pos hDD]; exact bDD.le
  obtain ⟨⟨c0, c1, c2, c3, _, _⟩, _⟩ := hdat.cm
  refine XV.mono (XV.cube hL hS hN hA hd1 (Nq := Nz) (Na := Na) (Da := Da) (Dq := P.D * D) (rn := rn) (rd := rd)
    (c := if cA = true then 1 else 0) (j := j) (b1 := bt') (m := m)
    (by rw [en4 _ (by simp only [tsN, rD]; omega), hdat.hd]) (by rw [en4 _ (by simp only [tsN]; omega), hdat.h1])
    (by rw [eq4 _ (by simp only [tsS]; omega), hdat.hz])
    (by rw [a25, F2.2.2.1 _ _ (by simp [cmAr, cLT]), a0]; push_cast; ring)
    (fun i => by rw [a25, F2.2.2.1 _ _ (by simp [cmAr, cLT]), a1 i, hNz]; push_cast; ring)
    (by rw [aKa4]; exact c0) (fun i => by rw [aKa4]; exact c1 i)
    (by rw [eq4 _ (by simp only [tsS, sR0n, oT]; omega)]; exact c2)
    (by rw [eq4 _ (by simp only [tsS, sR0d, oT]; omega)]; exact c3)
    (by rw [eq4 _ (by simp only [tsS]; omega)]; exact st3) n4 bNz' bDD' (fun i => (bNa i).le)
    (by rw [abs_of_pos hDa]; exact bDa.le) (by rw [abs_of_pos hrn]; exact brn.le)
    (by rw [abs_of_pos hrd]; exact brd.le) hrd hj (by omega)) (by simp only [tstTK, cubeK]; omega)
    fun σ5 ⟨n5, d5, F5⟩ => ⟨?_, ?_, ?_⟩
  · rw [n5]
    have hq : (posZ P).1 + (posZ P).2 *ᵥ ptDN D Nv = ptDN (P.D * D) Nz := posZ_map P D Nv hPD.ne' hD0.ne'
    have hae : a = ptDN Da Na := funext fun i => (ha i).symm
    have hiff : (∀ i, |ptDN (P.D * D) Nz i - a i| ≤ 2 ^ (j + 1) * r0) ↔
        ∀ i : Fin d, |Nz i * Da - Na i * (P.D * D)| * rd ≤ 2 ^ (j + 1) * rn * (P.D * D) * Da := by
      refine forall_congr' fun i => ?_
      rw [hae, ← hr]
      exact cube_iff hDD hDa hrd j
    have hT : stTest XO.w.orc a r0 R0 j (posZ P) (ptDN D Nv) =
        (cA && decide (∀ i, |ptDN (P.D * D) Nz i - a i| ≤ 2 ^ (j + 1) * r0)) := by
      unfold stTest
      rw [hq, hcA, hkdef, ← hae, hr]
    rw [hT]
    by_cases hall : ∀ i : Fin d, |Nz i * Da - Na i * (P.D * D)| * rd ≤ 2 ^ (j + 1) * rn * (P.D * D) * Da
    · have h2 := hiff.2 hall
      rw [if_pos hall]
      by_cases hc : cA = true <;> simp [hc, h2]
    · have h2 : ¬ ∀ i, |ptDN (P.D * D) Nz i - a i| ≤ 2 ^ (j + 1) * r0 := fun h => hall (hiff.1 h)
      rw [if_neg hall]
      by_cases hc : cA = true <;> simp [hc, h2]
  · exact (G4.trans (F5.mono (fun y h => by simp only [cbS] at h; simp only [tsS]; omega)
      (fun j h => by simp only [cbN] at h; simp only [tsN]; omega) (fun _ _ h => h.elim)))
  · rw [d5, hσ4]; simp [d2, d1]

end AdversarialBco.Unified.ProgO.TriO
