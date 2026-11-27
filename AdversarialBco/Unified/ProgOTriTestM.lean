/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStepZ

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the position map and the cube check of the stage test

Two base pieces of the stage test `stTest orc a r₀ R₀ j P` (BLOSpec.lean) on the machine, for a point `(D; N)` in the
array `aT + 24` (the gauge's test point):

* `xtMapT`: the position map `μ_P + T_P (N/D)` as `(P_D D; μ̂ D + T̂ N)` into the array `aT + 25` (`xtMap`
  of Unified/ProgOTst.lean with the stage cells: `P_D` in `oT`, `μ̂` in `aT`, `T̂` in `aT + 1`; scratch slots from
  `oT + 320`, registers `rT + 64, ..., rT + 68`, arrays `aT + 27`, `aT + 28`);
* `xcube`: the cube `|q - a|_∞ ≤ 2^{j+1} r₀` on the point `(D_q; N_q)` of `aT + 25`, as
  `|N_q,i D_a - N_a,i D_q| r_d ≤ 2^{j+1} r_n D_q D_a` for every `i`; the answer in `rT + 34` drops to `0` when a
  coordinate fails (slots `oT + 306, ..., oT + 310`, registers `rT + 69`, `rT + 70`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix

variable {d : ℕ}

theorem powZ_le {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

theorem powZ_lt {a b : ℕ} (h : a < b) : (2 : ℤ) ^ a < 2 ^ b := pow_lt_pow_right₀ (by norm_num) h

theorem intR_lt {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |(z : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (lt_of_le_of_lt h (powZ_lt ha))

theorem lt_aszT {j : ℕ} (hd : 1 ≤ d) (hj : j ≤ d) : j < asz d := by unfold asz; nlinarith

/-! ## The position map -/

/-- The copy `aT + 27 [k] := aT + 24 [1 + k]`, `k < d`. -/
def xtCopyT (L : Layout) : XCmd :=
  xforN (rT + 64) rD rT (.seq (.prim (.frag (.nadd (rT + 65) (rT + 64) rT)))
    (.seq (toX (VL.aget L (oT + 320) (aT + 24) (rT + 65))) (toX (VL.aset L (aT + 27) (rT + 64) (oT + 320)))))

/-- `μ̂_k D + y_k`, `k` in `rT + 68`, `D` in `oT + 321`, `y = T̂ N` in `aT + 28`. -/
def ieMapT : IE := .op .add (.op .mul (.arr aT (rT + 68)) (.sc (oT + 321))) (.arr (aT + 28) (rT + 68))

/-- The position map of the point `(D; N)` of `aT + 24`: `(P_D D; μ̂ D + T̂ N)` into `aT + 25`. -/
def xtMapT (L : Layout) : XCmd :=
  .seq (xtCopyT L) <|
  .seq (xmatvec L (oT + 1) (oT + 323) (oT + 324) (aT + 1) (aT + 27) (aT + 28) (rT + 66) (rT + 67) (rT + 68) rD rT) <|
  .seq (.prim (.frag (.nconst (rT + 64) 0))) <| .seq (toX (VL.aget L (oT + 321) (aT + 24) (rT + 64))) <|
  .seq (toX (VL.sop2 L .mul (oT + 322) oT (oT + 321))) <| .seq (toX (VL.aset L (aT + 25) (rT + 64) (oT + 322))) <|
  .seq (.prim (.frag (.nconst (rT + 67) 1))) <|
  xmapE L (oT + 1) (oT + 328) ieMapT (aT + 25) (rT + 67) rT (rT + 68) rD rT

set_option maxHeartbeats 2000000 in
/-- The copy of the numerators of the test point into `aT + 27`. -/
theorem XV.tCopyT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    (hD : σ.nat rD = d) (h1 : σ.nat rT = 1)
    {Nv : Fin d → ℤ} (hNv : ∀ i : Fin d, σ.arr (aT + 24) (1 + (i : ℕ)) = Nv i) (bN : ∀ i, |(Nv i : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xtCopyT L) σ (d * (1 + (2 + 2) + 3) + 3) (fun σ' =>
      (∀ i : Fin d, σ'.arr (aT + 27) i = Nv i) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = oT + 320) (fun j => j = rT + 64 ∨ j = rT + 65) (fun b _ => b = aT + 27) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdasz : d ≤ asz d := by unfold asz; nlinarith
  let J : ℕ → Env d → Prop := fun k σ' => (∀ k' (h : k' < k) (hd : k' < d), σ'.arr (aT + 27) k' = Nv ⟨k', hd⟩) ∧
    σ'.draws = σ.draws ∧
    FrameA (fun y => y = oT + 320) (fun j => j = rT + 64 ∨ j = rT + 65) (fun b _ => b = aT + 27) σ σ'
  refine XV.mono (XV.forN hL (i := rT + 64) (n := rD) (one := rT) (by omega) (by simp only [rD]; omega)
    (by omega) (by simp only [rD]; omega) (by omega) d (1 + (2 + 2))
    (by unfold asz at hda; nlinarith) J σ hD h1
    ⟨fun k' h => absurd h (Nat.not_lt_zero _), by simp, (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' h => ⟨fun i => h.1.1 i i.2 i.2, h.1.2.1, h.1.2.2⟩
  intro k hk σ' hJ hkk hkn hk1
  obtain ⟨hc, hdr, F⟩ := hJ
  have eA : ∀ j, σ'.arr (aT + 24) j = σ.arr (aT + 24) j := fun j => F.2.2.1 _ j (by omega)
  have hr1 : rT ≠ rT + 65 := by omega
  have hrD : rD ≠ rT + 65 := by simp only [rD]; omega
  refine XV.seq (XV.nadd hL (σ := σ') (i := rT + 65) (a := rT + 64) (b := rT) (by omega) (by omega)
    (by omega) (by rw [hkk]; omega) (by rw [hk1]; omega)) fun σ1 e1 => ?_
  have r7 : σ1.nat (rT + 65) = 1 + k := by rw [e1, Env.setNat_nat, if_pos rfl, hkk, hk1]; omega
  have v1 : σ1.arr (aT + 24) (1 + k) = Nv ⟨k, hk⟩ := by rw [e1, Env.setNat_arr, eA]; exact hNv ⟨k, hk⟩
  refine XV.seq (XV.aget hL (σ := σ1) (x := oT + 320) (a := aT + 24) (i := rT + 65) (by omega) (by omega)
    (by omega) (by rw [r7]; exact lt_aszT hd1 (by omega)) (by rw [r7, v1]; exact bN _)) fun σ2 e2 => ?_
  have v2 : σ2.sc (oT + 320) = Nv ⟨k, hk⟩ := by rw [e2]; simp [r7, v1]
  have n2 : σ2.nat (rT + 64) = k := by rw [e2, e1]; simp [hkk]
  refine XV.mono (XV.aset hL (σ := σ2) (a := aT + 27) (i := rT + 64) (x := oT + 320) (by omega) (by omega)
    (by omega) (by rw [n2]; exact lt_aszT hd1 (by omega)) (by rw [v2]; exact bN _)) le_rfl fun σ3 e3 => ?_
  have F2 : FrameA (fun y => y = oT + 320) (fun j => j = rT + 64 ∨ j = rT + 65) (fun b _ => b = aT + 27) σ σ2 := by
    rw [e2, e1]; exact (F.setNat (Or.inr rfl) _).setSc rfl _
  subst e3
  refine ⟨by rw [Env.setArr_nat, e2, e1]; simp [hkk], by rw [Env.setArr_nat, e2, e1]; simp [hkn, hrD],
    by rw [Env.setArr_nat, e2, e1]; simp [hk1, hr1], fun k' hk' hd' => ?_, by
      rw [Env.setNat_draws, Env.setArr_draws, e2, e1]; simp [hdr], ?_⟩
  · simp only [Env.setNat_arr, Env.setArr_arr, n2]
    by_cases hkj : k' = k
    · subst hkj; simp [v2]
    · rw [if_neg (fun h => hkj h.2), e2, e1]
      simp only [Env.setSc_arr, Env.setNat_arr]
      exact hc k' (by omega) hd'
  · exact (F2.setArr rfl _).setNat (Or.inl rfl) _

/-- The slots of the position map. -/
abbrev tmS (y : ℕ) : Prop := oT + 320 ≤ y

/-- The registers of the position map. -/
abbrev tmN (j : ℕ) : Prop := rT + 64 ≤ j ∧ j < rT + 69

/-- The arrays of the position map. -/
abbrev tmA (b _k : ℕ) : Prop := b = aT + 25 ∨ b = aT + 27 ∨ b = aT + 28

set_option maxHeartbeats 4000000 in
/-- **The position map** of the stage: for the point `(D; N)` of `aT + 24`, the array `aT + 25` gets `P_D D` in cell
`0` and `μ̂ D + T̂ N` in the cells `1, ..., d`. -/
theorem XV.tMapT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    {DS : ℤ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ} {D : ℤ} {Nv : Fin d → ℤ} {m bt : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rT = 1) (hz : σ.sc (oT + 1) = 0) (hds : σ.sc oT = DS)
    (hmu : ∀ i : Fin d, σ.arr aT i = muS i) (has : ∀ i j : Fin d, σ.arr (aT + 1) (d * i + j) = aS i j)
    (hap0 : σ.arr (aT + 24) 0 = D) (hNv : ∀ i : Fin d, σ.arr (aT + 24) (1 + (i : ℕ)) = Nv i)
    (bDS : |DS| ≤ 2 ^ m) (bmu : ∀ i, |muS i| ≤ 2 ^ m) (baS : ∀ i j, |aS i j| ≤ 2 ^ m) (hdm : d ≤ 2 ^ m)
    (bD : |D| ≤ 2 ^ bt) (bNv : ∀ i, |Nv i| ≤ 2 ^ bt) (hℓ : 4 * m + 2 * bt + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xtMapT L) σ ((d * (1 + (2 + 2) + 3) + 3) + ((d * (d * 10 + 9) + 4) +
      (1 + (2 + (1 + (2 + (1 + (d * (ieMapT.units + 6) + 3))))))))
      (fun σ' => σ'.arr (aT + 25) 0 = DS * D ∧
        (∀ i : Fin d, σ'.arr (aT + 25) (1 + (i : ℕ)) = muS i * D + (aS *ᵥ Nv) i) ∧ σ'.draws = σ.draws ∧
        FrameA tmS tmN tmA σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdasz : d ≤ asz d := by unfold asz; nlinarith
  have hdl : ∀ k < d, k < asz d := fun k hk => lt_aszT hd1 hk.le
  have hlt : ∀ {z : ℤ} {a : ℕ}, |z| ≤ 2 ^ a → a < ℓ → |(z : ℝ)| < 2 ^ ℓ := fun h ha => intR_lt h ha
  -- the copy
  refine XV.seq (XV.tCopyT hL hS hN hA hd1 hD h1 hNv (fun i => hlt (bNv i) (by omega)))
    fun σ1 ⟨c1, d1, F1⟩ => ?_
  have G1 : FrameA tmS tmN tmA σ σ1 := F1.mono (fun y h => by simp only [tmS]; omega)
    (fun j h => by simp only [tmN]; omega) (fun b _ h => by simp only [tmA]; omega)
  -- `y = T̂ N`
  set E := m + bt with hE
  have bM : ∀ i k, |aS i k| ≤ 2 ^ E := fun i k => (baS i k).trans (powZ_le (by omega))
  have bx : ∀ k, |Nv k| ≤ 2 ^ E := fun k => (bNv k).trans (powZ_le (by omega))
  have hdℓ : d * 2 ^ (2 * E) < 2 ^ ℓ := by
    calc d * 2 ^ (2 * E) ≤ 2 ^ m * 2 ^ (2 * E) := Nat.mul_le_mul_right _ hdm
      _ = 2 ^ (m + 2 * E) := by rw [pow_add]
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine XV.seq (XV.matvec hL (z := oT + 1) (r := oT + 323) (t := oT + 324) (aM := aT + 1) (ax := aT + 27)
    (ay := aT + 28) (ni := rT + 66) (nr := rT + 67) (nk := rT + 68) (nd := rD) (none := rT) (E := E) (M := aS)
    (x := Nv) (by omega) (by omega) (by omega) (by omega)
    (by rw [G1.2.1 _ (by simp only [tmS]; omega), hz]) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [rD]; omega)
    (by omega) (by simp only [rD, rT]; decide)
    (by rw [G1.1 _ (by simp only [tmN, rD]; omega), hD]) (by rw [G1.1 _ (by simp only [tmN]; omega), h1])
    (fun i k => by rw [G1.2.2.1 _ _ (by simp only [tmA]; omega), has]) c1 bM bx (by omega) hdℓ)
    fun σ2 ⟨y2, d2, F2⟩ => ?_
  have G2 : FrameA tmS tmN tmA σ σ2 := G1.trans (F2.mono (fun y h => by simp only [tmS]; omega)
    (fun j h => by simp only [tmN]; omega) (fun b _ h => by simp only [tmA]; omega))
  have eap : ∀ j, σ2.arr (aT + 24) j = σ.arr (aT + 24) j := fun j => G2.2.2.1 _ j (by simp only [tmA]; omega)
  -- `D`, `P_D D`
  refine XV.seq (XV.nconst hL (σ := σ2) (i := rT + 64) (by omega) 0 (by omega)) fun σ3 e3 => ?_
  have n3 : σ3.nat (rT + 64) = 0 := by rw [e3]; simp
  refine XV.seq (XV.aget hL (σ := σ3) (x := oT + 321) (a := aT + 24) (i := rT + 64) (by omega) (by omega)
    (by omega) (by rw [n3]; exact hdl 0 (by omega)) (by rw [n3, e3, Env.setNat_arr, eap, hap0]; exact hlt bD (by omega)))
    fun σ4 e4 => ?_
  have v4 : σ4.sc (oT + 321) = D := by rw [e4, n3, e3]; simp [eap, hap0]
  have s4 : σ4.sc oT = DS := by
    rw [e4, Env.setSc_sc, if_neg (by omega), e3, Env.setNat_sc, G2.2.1 _ (by simp only [tmS]; omega), hds]
  have bDSD : |DS * D| ≤ 2 ^ (m + bt) := absI_mul_le bDS bD
  refine XV.seq (XV.mulI hL (σ := σ4) (x := oT + 322) (a := oT) (b := oT + 321) (by omega)
    (by omega) (by omega) s4 v4 (lt_of_le_of_lt bDS (powZ_lt (by omega)))
    (lt_of_le_of_lt bD (powZ_lt (by omega))) (lt_of_le_of_lt bDSD (powZ_lt (by omega)))) fun σ5 e5 => ?_
  have n5 : σ5.nat (rT + 64) = 0 := by rw [e5, e4]; simp [n3]
  have hv5 : |σ5.sc (oT + 322)| < 2 ^ ℓ := by rw [e5]; simp only [Env.setSc_sc, if_pos]; exact hlt bDSD (by omega)
  refine XV.seq (XV.aset hL (σ := σ5) (a := aT + 25) (i := rT + 64) (x := oT + 322) (by omega) (by omega)
    (by omega) (by rw [n5]; exact hdl 0 (by omega)) hv5) fun σ6 e6 => ?_
  have a6 : σ6.arr (aT + 25) 0 = DS * D := by rw [e6, n5, e5]; simp
  refine XV.seq (XV.nconst hL (σ := σ6) (i := rT + 67) (by omega) 1 (by omega)) fun σ7 e7 => ?_
  have G7 : FrameA tmS tmN tmA σ σ7 := by
    rw [e7, e6, e5, e4, e3]
    exact (((((G2.setNat (by simp only [tmN]; omega) _).setSc (by simp only [tmS]; omega) _).setSc
      (by simp only [tmS]; omega) _).setArr (Or.inl rfl) _).setNat (by simp only [tmN]; omega) _)
  have dd7 : σ7.draws = σ.draws := by rw [e7, e6, e5, e4, e3]; simp [d2, d1]
  have q7 : σ7.sc (oT + 321) = D := by rw [e7, e6, e5]; simp [v4]
  have y7 : ∀ k : Fin d, σ7.arr (aT + 28) k = (aS *ᵥ Nv) k := fun k => by
    rw [e7, e6]; simp only [Env.setNat_arr, Env.setArr_arr]
    rw [if_neg (by omega), e5, e4, e3]; simp only [Env.setSc_arr, Env.setNat_arr]; exact y2 k
  have mu7 : ∀ k : Fin d, σ7.arr aT k = muS k := fun k => by
    rw [G7.2.2.1 _ _ (by simp only [tmA]; omega), hmu]
  -- the numerators
  set E2 := 2 * m + bt with hE2
  have by7 : ∀ k : Fin d, |(aS *ᵥ Nv) k| ≤ 2 ^ E2 := fun k => by
    have := mulVec_abs_le (a := m) (b := bt) (c := m) baS bNv hdm k
    exact this.trans (powZ_le (by omega))
  set F : ℕ → ℤ := fun k => if h : k < d then muS ⟨k, h⟩ * D + (aS *ᵥ Nv) ⟨k, h⟩ else 0 with hF
  refine XV.mono (XV.mapE hL (σ := σ7) (z := oT + 1) (t := oT + 328) (e := ieMapT) (aB := aT + 25) (nr := rT + 67)
    (nst := rT) (nk := rT + 68) (nn := rD) (none := rT) (E := E2) (N := d) (base := 1) (st := 1) (F := F)
    (by simp only [ieMapT, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by omega) (by simp only [ieMapT, IE.scr]; omega)
    (by rw [G7.2.1 _ (by simp only [tmS]; omega), hz]) (by omega) (by omega) (by omega)
    (by omega) (by simp only [rD]; omega) (by omega)
    (by simp only [rD, rT]; decide)
    (by omega) (by omega)
    (by rw [G7.1 _ (by simp only [tmN, rD]; omega), hD]) (by rw [G7.1 _ (by simp only [tmN]; omega), h1])
    (by rw [e7]; simp) (by rw [G7.1 _ (by simp only [tmN]; omega), h1]) one_pos
    (fun k hk => lt_aszT hd1 (by omega)) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by omega) (by simp only [ieMapT, IE.top, IE.mag]; omega) ?_) (le_refl _) fun σ8 ⟨a8, _, d8, F8⟩ => ?_
  · intro k hk σ' F' dd' hk' hr'
    have eD : σ'.sc (oT + 321) = D := by rw [F'.2.1 _ (by omega), q7]
    have eMu : σ'.arr aT k = muS ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega)]; exact mu7 ⟨k, hk⟩
    have eY : σ'.arr (aT + 28) k = (aS *ᵥ Nv) ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega)]; exact y7 ⟨k, hk⟩
    refine ⟨⟨⟨⟨by rw [hk']; exact hdl k hk, muS ⟨k, hk⟩, by rw [hk', eMu],
      (bmu _).trans (powZ_le (by omega))⟩, D, eD, bD.trans (powZ_le (by omega))⟩,
      by rw [hk']; exact hdl k hk, (aS *ᵥ Nv) ⟨k, hk⟩, by rw [hk', eY], by7 _⟩, ?_⟩
    simp only [IE.eval, ieMapT, RealRAM.Op2.eval, hk', eMu, eD, eY, hF, dite_eq_left hk]
    push_cast; ring
  · refine ⟨by rw [F8.2.2.1 _ _ (by omega), e7, Env.setNat_arr, a6], fun i => ?_, by rw [d8, dd7], ?_⟩
    · have := a8 i i.2
      simp only [one_mul, hF, dite_eq_left i.2] at this
      rw [this]; push_cast; simp only [Fin.eta]
    · exact G7.trans (F8.mono (fun y h => by simp only [tmS]; omega)
        (fun j h => by simp only [tmN, rD] at *; omega) (fun b _ h => by simp only [tmA]; omega))

/-! ## The cube check -/

/-- One coordinate of the cube check: `w = (N_q,i D_a - N_a,i D_q) r_d` against `R = 2^{j+1} r_n D_q D_a` in
`oT + 308`; `rT + 34 := 0` when `R < w` or `R < -w`. The cell `1 + i` in the register `rT + 70`. -/
def xcubeB (L : Layout) : XCmd :=
  .seq (toX (VL.aget L (oT + 309) (aT + 25) (rT + 70)))
  (.seq (toX (VL.sop2 L .mul (oT + 309) (oT + 309) (oT + 306)))
  (.seq (toX (VL.aget L (oT + 310) aKa (rT + 70)))
  (.seq (toX (VL.sop2 L .mul (oT + 310) (oT + 310) (oT + 307)))
  (.seq (toX (VL.sop2 L .sub (oT + 309) (oT + 309) (oT + 310)))
  (.seq (toX (VL.sop2 L .mul (oT + 309) (oT + 309) sR0d))
  (.seq (toX (VL.sop2 L .sub (oT + 310) (oT + 1) (oT + 309)))
  (.seq (xifS L (oT + 308) (oT + 309) (.prim (.frag (.nconst (rT + 34) 0))) .skip)
    (xifS L (oT + 308) (oT + 310) (.prim (.frag (.nconst (rT + 34) 0))) .skip))))))))

/-- The cube check: `D_a`, `D_q`, `R = 2^{j+1} r_n D_q D_a` into `oT + 306`, `oT + 307`, `oT + 308`, then `xcubeB`
over the coordinates. -/
def xcube (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst (rT + 69) 0)))
  (.seq (toX (VL.aget L (oT + 306) aKa (rT + 69)))
  (.seq (toX (VL.aget L (oT + 307) (aT + 25) (rT + 69)))
  (.seq (toX (VL.sop2 L .mul (oT + 308) (oT + 36) sR0n))
  (.seq (toX (VL.sop2 L .mul (oT + 308) (oT + 308) (oT + 307)))
  (.seq (toX (VL.sop2 L .mul (oT + 308) (oT + 308) (oT + 306)))
    (xforN (rT + 69) rD rT (.seq (.prim (.frag (.nadd (rT + 70) (rT + 69) rT))) (xcubeB L))))))))

theorem abs_le_iff_not_lt {w R : ℤ} : |w| ≤ R ↔ ¬ R < w ∧ ¬ R < 0 - w := by
  rw [abs_le]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨not_lt.2 h2, not_lt.2 (by linarith)⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith [not_lt.1 h2], not_lt.1 h1⟩

set_option maxHeartbeats 2000000 in
/-- The rule of one coordinate of the cube check. -/
theorem XV.cubeB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    (hS : oT + 340 ≤ L.NS) (hN : rT + 72 ≤ L.NN) (hA : aT + 29 ≤ L.NA) (hd1 : 1 ≤ d)
    {i : ℕ} (hi : i < d) {Nq Na Da Dq rd R : ℤ} {c : ℕ} {b1 m : ℕ}
    (hσi : σ.nat (rT + 70) = 1 + i) (eZ : σ.sc (oT + 1) = 0) (eNq : σ.arr (aT + 25) (1 + i) = Nq)
    (eNa : σ.arr aKa (1 + i) = Na) (eDa : σ.sc (oT + 306) = Da) (eDq : σ.sc (oT + 307) = Dq)
    (eR : σ.sc (oT + 308) = R) (erd : σ.sc sR0d = rd) (ec : σ.nat (rT + 34) = c)
    (bNq : |Nq| ≤ 2 ^ b1) (bDq : |Dq| ≤ 2 ^ b1) (bNa : |Na| ≤ 2 ^ m) (bDa : |Da| ≤ 2 ^ m) (brd : |rd| ≤ 2 ^ m)
    (bR : |R| ≤ 2 ^ (b1 + 3 * m)) (hrd : 0 < rd) (hℓ : b1 + 3 * m + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xcubeB L) σ (2 + (1 + (2 + (1 + (1 + (1 + (1 + ((1 + 2) + (1 + 2)))))))))
      (fun σ' => σ'.nat (rT + 34) = (if |Nq * Da - Na * Dq| * rd ≤ R then c else 0) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = oT + 309 ∨ y = oT + 310) (fun j => j = rT + 34) (fun _ _ => False) σ σ') := by
  have hlt : ∀ {z : ℤ} {a : ℕ}, |z| ≤ 2 ^ a → a < ℓ → |z| < 2 ^ ℓ := fun h ha => lt_of_le_of_lt h (powZ_lt ha)
  have hRl : |(R : ℝ)| < 2 ^ ℓ := intR_lt bR (by omega)
  set w : ℤ := (Nq * Da - Na * Dq) * rd with hw
  have b1' : |Nq * Da| ≤ 2 ^ (b1 + m) := absI_mul_le bNq bDa
  have b2' : |Na * Dq| ≤ 2 ^ (b1 + m) := by rw [add_comm]; exact absI_mul_le bNa bDq
  have b3' : |Nq * Da - Na * Dq| ≤ 2 ^ (b1 + m + 1) := by
    calc |Nq * Da - Na * Dq| ≤ |Nq * Da| + |Na * Dq| := abs_sub _ _
      _ ≤ 2 ^ (b1 + m) + 2 ^ (b1 + m) := add_le_add b1' b2'
      _ = 2 ^ (b1 + m + 1) := by ring
  have bw : |w| ≤ 2 ^ (b1 + m + 1 + m) := absI_mul_le b3' brd
  have bw' : |0 - w| ≤ 2 ^ (b1 + m + 1 + m) := by rw [zero_sub, abs_neg]; exact bw
  -- `N_q,i D_a`
  refine XV.seq (XV.aget hL (x := oT + 309) (a := aT + 25) (i := rT + 70) (by omega) (by omega) (by omega)
    (by rw [hσi]; exact lt_aszT hd1 (by omega)) (by rw [hσi, eNq]; exact intR_lt bNq (by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.mulI hL (x := oT + 309) (a := oT + 309) (b := oT + 306) (by omega) (by omega) (by omega)
    (u := Nq) (v := Da) (by simp [hσi, eNq]) (by simp [eDa]) (hlt bNq (by omega)) (hlt bDa (by omega))
    (hlt b1' (by omega))) fun σ2 e2 => ?_
  subst e2
  -- `N_a,i D_q`
  refine XV.seq (XV.aget hL (x := oT + 310) (a := aKa) (i := rT + 70) (by omega) (by simp only [aKa]; omega) (by omega)
    (by simp only [Env.setSc_nat, hσi]; exact lt_aszT hd1 (by omega))
    (by simp only [Env.setSc_nat, Env.setSc_arr, hσi, eNa]; exact intR_lt bNa (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := oT + 310) (a := oT + 310) (b := oT + 307) (by omega) (by omega) (by omega)
    (u := Na) (v := Dq) (by simp [hσi, eNa]) (by simp [eDq]) (hlt bNa (by omega)) (hlt bDq (by omega))
    (hlt b2' (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.subI hL (x := oT + 309) (a := oT + 309) (b := oT + 310) (by omega) (by omega) (by omega)
    (u := Nq * Da) (v := Na * Dq) (by simp) (by simp) (hlt b1' (by omega)) (hlt b2' (by omega))
    (hlt b3' (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.mulI hL (x := oT + 309) (a := oT + 309) (b := sR0d) (by omega) (by omega)
    (by simp only [sR0d]; omega) (u := Nq * Da - Na * Dq) (v := rd) (by simp) (by simp [sR0d, erd]) (hlt b3' (by omega))
    (hlt brd (by omega)) (hlt bw (by omega))) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.subI hL (x := oT + 310) (a := oT + 1) (b := oT + 309) (by omega) (by omega) (by omega)
    (u := 0) (v := w) (by simp [eZ]) (by simp [hw]) (by simp) (hlt bw (by omega))
    (hlt bw' (by omega))) fun σ7 e7 => ?_
  subst e7
  set σ7 := ((((((σ.setSc (oT + 309) (σ.arr (aT + 25) (σ.nat (rT + 70)))).setSc (oT + 309)
    ((Nq * Da : ℤ) : ℝ)).setSc (oT + 310) _).setSc (oT + 310) ((Na * Dq : ℤ) : ℝ)).setSc (oT + 309)
    ((Nq * Da - Na * Dq : ℤ) : ℝ)).setSc (oT + 309) ((w : ℤ) : ℝ)).setSc (oT + 310) ((0 - w : ℤ) : ℝ) with hσ7
  have s8 : σ7.sc (oT + 308) = R := by simp [hσ7, eR]
  have s9 : σ7.sc (oT + 309) = (w : ℝ) := by simp [hσ7]
  have s10 : σ7.sc (oT + 310) = ((0 - w : ℤ) : ℝ) := by simp [hσ7]
  have n7 : σ7.nat (rT + 34) = c := by simp [hσ7, ec]
  have dr7 : σ7.draws = σ.draws := by simp [hσ7]
  have F7 : FrameA (fun y => y = oT + 309 ∨ y = oT + 310) (fun j => j = rT + 34) (fun _ _ => False) σ σ7 := by
    rw [hσ7]
    exact ((((((((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _).setSc
      (Or.inr rfl) _).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _)
  have hab : |Nq * Da - Na * Dq| * rd = |w| := by rw [hw, abs_mul, abs_of_pos hrd]
  -- the two tests
  refine XV.seq (Q₁ := fun σ'' => σ''.nat (rT + 34) = (if R < w then 0 else c) ∧ σ''.sc (oT + 308) = R ∧
      σ''.sc (oT + 310) = ((0 - w : ℤ) : ℝ) ∧ σ''.draws = σ.draws ∧
      FrameA (fun y => y = oT + 309 ∨ y = oT + 310) (fun j => j = rT + 34) (fun _ _ => False) σ σ'')
    (XV.ifS_skip hL (by omega) (by omega) (by rw [s8]; exact hRl) (by rw [s9]; exact intR_lt bw (by omega))
      (fun hc => XV.mono (XV.nconst hL (by omega) 0 (by positivity)) le_rfl fun σ'' e => by
        subst e
        have hc' : R < w := by rw [s8, s9] at hc; exact_mod_cast hc
        exact ⟨by simp [hc'], by simp [s8], by simp [s10], by simp [dr7], F7.setNat rfl _⟩)
      (fun hc => by
        have hc' : ¬ R < w := by rw [s8, s9] at hc; exact_mod_cast hc
        exact ⟨by simp [hc', n7], s8, s10, dr7, F7⟩)) fun σ8 ⟨n8, r8, t8, dr8, F8⟩ => ?_
  refine XV.ifS_skip hL (by omega) (by omega) (by rw [r8]; exact hRl) (by rw [t8]; exact intR_lt bw' (by omega))
    (fun hc => XV.mono (XV.nconst hL (by omega) 0 (by positivity)) le_rfl fun σ'' e => by
      subst e
      have hc' : R < 0 - w := by rw [r8, t8] at hc; exact_mod_cast hc
      refine ⟨?_, by simp [dr8], F8.setNat rfl _⟩
      rw [nat_setNat_eq, hab, if_neg (fun h => (abs_le_iff_not_lt.1 h).2 hc')])
    (fun hc => by
      have hc' : ¬ R < 0 - w := by rw [r8, t8] at hc; exact_mod_cast hc
      refine ⟨?_, dr8, F8⟩
      rw [n8, hab]
      by_cases h1 : R < w
      · rw [if_pos h1, if_neg (fun h => (abs_le_iff_not_lt.1 h).1 h1)]
      · rw [if_neg h1, if_pos (abs_le_iff_not_lt.2 ⟨h1, hc'⟩)])

end AdversarialBco.Unified.ProgO.TriO
