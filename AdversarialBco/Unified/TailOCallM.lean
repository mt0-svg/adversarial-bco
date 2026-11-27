/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTst
public import AdversarialBco.Bit.Transfer.XBLRowT

@[expose] public section

/-!
# The scaled position map of ELL-O's test, with a bounded frame

BL-O's calls test the K-part with `c.T orc k (1 - ε')⁻¹ y = cmQ orc a r₀ k (μ_S + A_S ((1 - ε')⁻¹ y))`. With the
position as `(D_S; μ̂_S, Â_S)` and `D' = 2^pF - ε̂ = 2^pF (1 - ε')`, the point `y = N/D` maps to
`(D_S D' D; μ̂_S (D' D) + (Â_S N) 2^pF)`. The caller makes `D'` positive by a sign change (`dpp`, `pfp` of
TailOCallP.lean), so the factor in the slot `103` is `2^pF`, `-2^pF` or `0`. ELL-O's block owns every slot from its
base, so the test inside it may change only named cells: `xmapC` uses the copy `xtCopy` (ProgOTst.lean) and v2.1's
strided dot product `xsdot`, both with
tight frames, and plain steps.

Cells: the data `D'` in the slot `100`, `D_S D'` in `101`; the point `(D; N)` in the array `33`; `N` copied to the
array `13`; the image into the array `14`; scratch slots `104` to `111`, registers `40` to `45`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open Matrix

variable {d : ℕ}

/-- One row of the map: `arr14[1 + i] := μ̂_i (D' D) + (Â N)_i 2^pF`, `i` in the register `42`, the row of `Â` read
from the cell held by the register `43`. -/
def xrowC (L : Layout) : XCmd :=
  .seq (xsdot L sZ 108 109 110 aAS 13 43 rOne 44 rD rOne) <|
  .seq (toX (VL.aget L 111 aMuS 42)) <|
  .seq (toX (VL.sop2 L .mul 111 111 107)) <|
  .seq (toX (VL.sop2 L .mul 108 108 103)) <|
  .seq (toX (VL.sop2 L .add 111 111 108)) <|
  .seq (.prim (.frag (.nadd 45 42 rOne))) <|
  toX (VL.aset L 14 45 111)

/-- A vector extended by `0` to the naturals. -/
def vz (x : Fin d → ℤ) (k : ℕ) : ℤ := if h : k < d then x ⟨k, h⟩ else 0

theorem vz_lt (x : Fin d → ℤ) {k : ℕ} (h : k < d) : vz x k = x ⟨k, h⟩ := by unfold vz; rw [dif_pos h]

theorem sum_vz (M : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ) (i : Fin d) :
    ∑ k ∈ Finset.range d, vz (M i) k * vz x k = (M *ᵥ x) i := by
  rw [mulVec, dotProduct, ← Fin.sum_univ_eq_sum_range (fun k => vz (M i) k * vz x k)]
  exact Finset.sum_congr rfl fun k _ => by rw [vz_lt _ k.2, vz_lt _ k.2]

theorem absZ_lt {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |(z : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) ha))

theorem absZ_lt' {z : ℤ} {a ℓ : ℕ} (h : |z| ≤ 2 ^ a) (ha : a < ℓ) : |z| < 2 ^ ℓ :=
  lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) ha)

set_option maxHeartbeats 4000000 in
/-- **One row of the scaled map.** -/
theorem XV.rowC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 112 ≤ L.NS)
    (hN : 46 ≤ L.NN) (hA : 15 ≤ L.NA) {i m bt : ℕ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ}
    {Nv : Fin d → ℤ} {PF DD : ℤ} (hi : i < d)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hpf : σ.sc 103 = PF) (hdd : σ.sc 107 = DD)
    (hmu : ∀ j : Fin d, σ.arr aMuS j = muS j) (has : ∀ j k : Fin d, σ.arr aAS (d * j + k) = aS j k)
    (hy : ∀ k : Fin d, σ.arr 13 k = Nv k) (hσi : σ.nat 42 = i) (hσr : σ.nat 43 = d * i)
    (bmu : ∀ j, |muS j| ≤ 2 ^ m) (baS : ∀ j k, |aS j k| ≤ 2 ^ m) (bN : ∀ k, |Nv k| ≤ 2 ^ bt)
    (bPF : |PF| ≤ 2 ^ m) (bDD : |DD| ≤ 2 ^ (m + bt)) (hdm : d ≤ 2 ^ m) (hℓ : 4 * m + 2 * bt + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xrowC L) σ (sdotUnits d + 8) (fun σ' =>
      σ'.arr 14 (1 + i) = ((muS ⟨i, hi⟩ * DD + (aS *ᵥ Nv) ⟨i, hi⟩ * PF : ℤ) : ℝ) ∧ σ'.nat 43 = d * i + d ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 108 ≤ y ∧ y ≤ 111) (fun j => j = 43 ∨ j = 44 ∨ j = 45) (fun b k => b = 14 ∧ k = 1 + i)
        σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdA : d * d + d < 2 ^ ℓa := hda
  have hidx : ∀ k < d, d * i + k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.mono (K := sdotUnits d + (2 + (1 + (1 + (1 + (1 + 2)))))) ?_ (by omega) fun _ h => h
  set E := m + bt with hE
  -- the dot product of row `i`
  refine XV.seq (XV.sdot hL (z := sZ) (r := 108) (t1 := 109) (t2 := 110) (ax := aAS) (ay := 13) (nr := 43)
    (nst := rOne) (nk := 44) (nn := rD) (none := rOne) (N := d) (base := d * i) (st := 1) (E := E)
    (Xv := vz (aS ⟨i, hi⟩)) (Yv := vz Nv) (by simp only [sZ]; omega) (by omega) (by omega) (by omega)
    (by simp only [sZ]; decide) (by simp only [aAS]; omega) (by omega) (by omega) (by simp only [rOne]; omega)
    (by omega) (by simp only [rD]; omega) (by simp only [rOne]; omega) (by simp only [rD, rOne]; decide)
    (by simp only [rOne]; omega) (by simp only [rOne]; omega) hz hD h1 hσr h1
    (fun k hk => by rw [one_mul, vz_lt _ hk]; exact has ⟨i, hi⟩ ⟨k, hk⟩)
    (fun k hk => by rw [vz_lt _ hk]; exact hy ⟨k, hk⟩) (fun k hk => by rw [one_mul]; exact hidx k hk)
    (by unfold asz; nlinarith) (fun k hk => by rw [vz_lt _ hk]; exact (baS _ _).trans (pow_le_pow_right₀ (by norm_num) (by omega)))
    (fun k hk => by rw [vz_lt _ hk]; exact (bN _).trans (pow_le_pow_right₀ (by norm_num) (by omega))) (by omega)
    (by
      calc d * 2 ^ (2 * E) ≤ 2 ^ m * 2 ^ (2 * E) := Nat.mul_le_mul_right _ hdm
        _ = 2 ^ (m + 2 * E) := by rw [pow_add]
        _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega))
    (by omega) (by rw [one_mul]; nlinarith) (by omega)) fun σ1 ⟨r1, n1, d1, F1⟩ => ?_
  rw [sum_vz] at r1
  set dot := (aS *ᵥ Nv) ⟨i, hi⟩ with hdot
  have bdot : |dot| ≤ 2 ^ (2 * m + bt) := by
    have := mulVec_abs_le (a := m) (b := bt) (c := m) baS bN hdm ⟨i, hi⟩
    exact this.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have i1 : σ1.nat 42 = i := by rw [F1.1 _ (by omega), hσi]
  have o1 : σ1.nat rOne = 1 := by rw [F1.1 _ (by simp only [rOne]; omega), h1]
  have m1 : σ1.arr aMuS i = muS ⟨i, hi⟩ := by rw [F1.2.2.1 _ _ id]; exact hmu ⟨i, hi⟩
  have p1 : σ1.sc 103 = PF := by rw [F1.2.1 _ (by omega), hpf]
  have q1 : σ1.sc 107 = DD := by rw [F1.2.1 _ (by omega), hdd]
  -- `μ̂_i`
  have bm : |((muS ⟨i, hi⟩ : ℤ) : ℝ)| < 2 ^ ℓ := absZ_lt (bmu ⟨i, hi⟩) (show m < ℓ by omega)
  have hi42 : σ1.nat 42 < asz d := by rw [i1]; unfold asz; nlinarith
  refine XV.seq (XV.aget hL (σ := σ1) (x := 111) (a := aMuS) (i := 42) (by omega) (by simp only [aMuS]; omega)
    (by omega) hi42 (by rw [i1, m1]; exact bm))
    fun σ2 e2 => ?_
  have s2 : σ2.sc 111 = muS ⟨i, hi⟩ := by rw [e2, i1, m1]; simp
  have b2 : |muS ⟨i, hi⟩ * DD| ≤ 2 ^ (2 * m + bt) := by
    have := absI_mul_le (bmu ⟨i, hi⟩) bDD
    exact this.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine XV.seq (XV.mulI hL (σ := σ2) (x := 111) (a := 111) (b := 107) (u := muS ⟨i, hi⟩) (v := DD) (by omega)
    (by omega) (by omega) s2 (by rw [e2]; simp [q1]) (absZ_lt' (bmu _) (by omega)) (absZ_lt' bDD (by omega))
    (absZ_lt' b2 (by omega))) fun σ3 e3 => ?_
  have b3 : |dot * PF| ≤ 2 ^ (3 * m + bt) := by
    have := absI_mul_le bdot bPF
    exact this.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine XV.seq (XV.mulI hL (σ := σ3) (x := 108) (a := 108) (b := 103) (u := dot) (v := PF) (by omega)
    (by omega) (by omega) (by rw [e3, e2]; simp [r1])
    (by rw [e3, e2]; simp [p1]) (absZ_lt' bdot (by omega)) (absZ_lt' bPF (by omega))
    (absZ_lt' b3 (by omega))) fun σ4 e4 => ?_
  have b4 : |muS ⟨i, hi⟩ * DD + dot * PF| ≤ 2 ^ (3 * m + bt + 1) :=
    absI_add_le (b2.trans (pow_le_pow_right₀ (by norm_num) (by omega))) b3
  refine XV.seq (XV.addI hL (σ := σ4) (x := 111) (a := 111) (b := 108) (u := muS ⟨i, hi⟩ * DD) (v := dot * PF)
    (by omega) (by omega) (by omega) (by rw [e4, e3]; simp) (by rw [e4]; simp)
    (absZ_lt' b2 (by omega)) (absZ_lt' b3 (by omega)) (absZ_lt' b4 (by omega))) fun σ5 e5 => ?_
  have i5 : σ5.nat 42 = i := by rw [e5, e4, e3, e2]; simp [i1]
  have o5 : σ5.nat rOne = 1 := by rw [e5, e4, e3, e2]; simp [o1]
  refine XV.seq (XV.nadd hL (σ := σ5) (i := 45) (a := 42) (b := rOne) (by omega) (by omega)
    (by simp only [rOne]; omega) (by rw [i5]; omega) (by rw [o5]; omega)) fun σ6 e6 => ?_
  have n6 : σ6.nat 45 = 1 + i := by rw [e6, i5, o5]; simp; omega
  have v6 : σ6.sc 111 = ((muS ⟨i, hi⟩ * DD + dot * PF : ℤ) : ℝ) := by rw [e6, e5]; simp
  have bv6 : |σ6.sc 111| < 2 ^ ℓ := by rw [v6]; exact absZ_lt b4 (show 3 * m + bt + 1 < ℓ by omega)
  refine XV.mono (XV.aset hL (σ := σ6) (a := 14) (i := 45) (x := 111) (by omega) (by omega) (by omega)
    (by rw [n6]; unfold asz; nlinarith) bv6) le_rfl
    fun σ7 e7 => ?_
  subst e7
  refine ⟨by rw [n6, ← v6]; simp, by rw [e6, e5, e4, e3, e2]; simp [n1], by
    rw [Env.setArr_draws, e6, e5, e4, e3, e2]; simp [d1], ?_⟩
  have G : FrameA (fun y => 108 ≤ y ∧ y ≤ 111) (fun j => j = 43 ∨ j = 44 ∨ j = 45)
      (fun b k => b = 14 ∧ k = 1 + i) σ σ1 :=
    F1.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)
  rw [n6, e6, e5, e4, e3, e2]
  exact ((((((G.setSc (by omega) _).setSc (by omega) _).setSc (by omega) _).setSc (by omega) _).setNat
    (by omega) _).setArr ⟨rfl, rfl⟩ _)

/-- The bases of the copy `xtCopy` in the call: the slot `104`, the registers `40`, `41`, the array `13`. -/
def qC : TstLay := ⟨88, 34, 13⟩

theorem qC_ok {L : Layout} (hS : 144 ≤ L.NS) (hN : 50 ≤ L.NN) (hA : 17 ≤ L.NA) : qC.OK L :=
  ⟨⟨by decide, hS⟩, ⟨by decide, hN⟩, ⟨by decide, hA⟩⟩

/-- **The scaled map**: `N` copied to the array `13`, `D` into the slot `105`, `D_S D' D` into `arr14[0]`, `D' D`
into the slot `107`, then the rows `arr14[1 + i]`; the scale `2^pF/D'` as `PF/D'` with `PF` in the slot `103`. -/
def xmapC (L : Layout) : XCmd :=
  .seq (xtCopy L qC 33) <|
  .seq (.prim (.frag (.nconst 40 0))) <|
  .seq (toX (VL.aget L 105 33 40)) <|
  .seq (toX (VL.sop2 L .mul 106 101 105)) <|
  .seq (toX (VL.aset L 14 40 106)) <|
  .seq (toX (VL.sop2 L .mul 107 100 105)) <|
  .seq (.prim (.frag (.nconst 43 0))) <|
  xforN 42 rD rOne (xrowC L)

/-- The units of `xmapC`. -/
def mapCK (d : ℕ) : ℕ := (d * (1 + (2 + 2) + 3) + 3) + (1 + (2 + (1 + (2 + (1 + (1 + (d * (sdotUnits d + 8 + 3) + 3)))))))

set_option maxHeartbeats 4000000 in
/-- **The scaled map of a point** `(D; N)` of the array `33`. -/
theorem XV.mapC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 144 ≤ L.NS)
    (hN : 50 ≤ L.NN) (hA : 34 ≤ L.NA) (hd1 : 1 ≤ d) {m bt : ℕ} {muS : Fin d → ℤ} {aS : Matrix (Fin d) (Fin d) ℤ}
    {PF DS Dp D : ℤ} {Nv : Fin d → ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hpf : σ.sc 103 = PF) (hDp : σ.sc 100 = Dp)
    (hDSp : σ.sc 101 = ((DS * Dp : ℤ) : ℝ)) (hmu : ∀ j : Fin d, σ.arr aMuS j = muS j)
    (has : ∀ j k : Fin d, σ.arr aAS (d * j + k) = aS j k) (hap0 : σ.arr 33 0 = D)
    (hNv : ∀ i : Fin d, σ.arr 33 (1 + (i : ℕ)) = Nv i)
    (bDS : |DS| ≤ 2 ^ m) (bDp : |Dp| ≤ 2 ^ m) (bmu : ∀ j, |muS j| ≤ 2 ^ m) (baS : ∀ j k, |aS j k| ≤ 2 ^ m)
    (bPF : |PF| ≤ 2 ^ m) (hdm : d ≤ 2 ^ m) (bD : |D| ≤ 2 ^ bt) (bN : ∀ k, |Nv k| ≤ 2 ^ bt)
    (hℓ : 4 * m + 2 * bt + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xmapC L) σ (mapCK d) (fun σ' =>
      σ'.arr 14 0 = ((DS * Dp * D : ℤ) : ℝ) ∧
      (∀ i : Fin d, σ'.arr 14 (1 + (i : ℕ)) = ((muS i * (Dp * D) + (aS *ᵥ Nv) i * PF : ℤ) : ℝ)) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 104 ≤ y ∧ y ≤ 111) (fun j => 40 ≤ j ∧ j ≤ 45) (fun b _ => 13 ≤ b ∧ b ≤ 14) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdA : d * d + d < 2 ^ ℓa := hda
  set S : ℕ → Prop := fun y => 104 ≤ y ∧ y ≤ 111 with hSd
  set N : ℕ → Prop := fun j => 40 ≤ j ∧ j ≤ 45 with hNd
  set Ar : ℕ → ℕ → Prop := fun b _ => 13 ≤ b ∧ b ≤ 14 with hAd
  -- the copy
  refine XV.seq (XV.tCopy hL (qC_ok hS hN (by omega)) (ap := 33) (by omega) (by decide) hd1 hD h1 hNv
    (fun i => absZ_lt (bN i) (show bt < ℓ by omega))) fun σ1 ⟨c1, d1, F1⟩ => ?_
  have G1 : FrameA S N Ar σ σ1 := F1.mono (fun y h => by simp only [hSd, qC] at h ⊢; omega)
    (fun j h => by simp only [hNd, qC] at h ⊢; omega) (fun b _ h => by simp only [hAd, qC] at h ⊢; omega)
  -- `D`, `D_S D' D`, `D' D`
  refine XV.seq (XV.nconst hL (σ := σ1) (i := 40) (by omega) 0 (by omega)) fun σ2 e2 => ?_
  have n2 : σ2.nat 40 = 0 := by rw [e2]; simp
  have a2 : σ2.arr 33 0 = D := by rw [e2, Env.setNat_arr, G1.2.2.1 _ _ (by simp only [hAd]; omega), hap0]
  refine XV.seq (XV.aget hL (σ := σ2) (x := 105) (a := 33) (i := 40) (by omega) (by omega) (by omega)
    (by rw [n2]; unfold asz; nlinarith) (by rw [n2, a2]; exact absZ_lt bD (show bt < ℓ by omega)))
    fun σ3 e3 => ?_
  have v3 : σ3.sc 105 = D := by rw [e3, n2, a2]; simp
  have q3 : ∀ y, y < 104 → σ3.sc y = σ.sc y := fun y hy => by
    rw [e3, Env.setSc_sc, if_neg (by omega), e2, Env.setNat_sc, G1.2.1 _ (by simp only [hSd]; omega)]
  have bDSp : |DS * Dp| ≤ 2 ^ (2 * m) := (absI_mul_le bDS bDp).trans (by rw [two_mul])
  have bZ : |DS * Dp * D| ≤ 2 ^ (2 * m + bt) := absI_mul_le bDSp bD
  refine XV.seq (XV.mulI hL (σ := σ3) (x := 106) (a := 101) (b := 105) (u := DS * Dp) (v := D) (by omega)
    (by omega) (by omega) (by rw [q3 _ (by omega), hDSp]) v3 (absZ_lt' bDSp (by omega)) (absZ_lt' bD (by omega))
    (absZ_lt' bZ (by omega))) fun σ4 e4 => ?_
  have n4 : σ4.nat 40 = 0 := by rw [e4, e3]; simp [n2]
  refine XV.seq (XV.aset hL (σ := σ4) (a := 14) (i := 40) (x := 106) (by omega) (by omega) (by omega)
    (by rw [n4]; unfold asz; nlinarith) (by rw [e4, Env.setSc_sc, if_pos rfl]; exact absZ_lt bZ (show 2 * m + bt < ℓ by omega)))
    fun σ5 e5 => ?_
  have bDD : |Dp * D| ≤ 2 ^ (m + bt) := absI_mul_le bDp bD
  refine XV.seq (XV.mulI hL (σ := σ5) (x := 107) (a := 100) (b := 105) (u := Dp) (v := D) (by omega)
    (by omega) (by omega) (by rw [e5, e4]; simp; rw [q3 _ (by omega), hDp]) (by rw [e5, e4]; simp [v3])
    (absZ_lt' bDp (by omega)) (absZ_lt' bD (by omega)) (absZ_lt' bDD (by omega))) fun σ6 e6 => ?_
  refine XV.seq (XV.nconst hL (σ := σ6) (i := 43) (by omega) 0 (by omega)) fun σ7 e7 => ?_
  have z7 : σ7.arr 14 0 = ((DS * Dp * D : ℤ) : ℝ) := by rw [e7, e6, e5, n4, e4]; simp
  have G7 : FrameA S N Ar σ σ7 := by
    rw [e7, e6, e5, e4, e3, e2]
    exact (((((G1.setNat (by simp only [hNd]; omega) _).setSc (by simp only [hSd]; omega) _).setSc
      (by simp only [hSd]; omega) _).setArr (by simp only [hAd]; omega) _).setSc (by simp only [hSd]; omega) _).setNat
      (by simp only [hNd]; omega) _
  have dd7 : σ7.draws = σ.draws := by rw [e7, e6, e5, e4, e3, e2]; simp [d1]
  have k7 : σ7.sc 107 = ((Dp * D : ℤ) : ℝ) := by rw [e7, e6]; simp
  have y7 : ∀ k : Fin d, σ7.arr 13 k = Nv k := fun k => by
    rw [e7, e6, e5, e4, e3, e2]; simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_arr]
    rw [if_neg (by omega)]; exact c1 k
  have r7 : ∀ y, y < 104 → σ7.sc y = σ.sc y := fun y hy => G7.2.1 y (by simp only [hSd]; omega)
  have N7 : ∀ j, j < 40 → σ7.nat j = σ.nat j := fun j hj => G7.1 j (by simp only [hNd]; omega)
  have A7 : ∀ b k, b < 13 → σ7.arr b k = σ.arr b k := fun b k hb => G7.2.2.1 b k (by simp only [hAd]; omega)
  -- the rows
  set Nz : Fin d → ℤ := fun i => muS i * (Dp * D) + (aS *ᵥ Nv) i * PF with hNz
  let J : ℕ → Env d → Prop := fun t σ' => σ'.nat 43 = d * t ∧ σ'.draws = σ.draws ∧
    (∀ i' (h : i' < t) (hd : i' < d), σ'.arr 14 (1 + i') = ((Nz ⟨i', hd⟩ : ℤ) : ℝ)) ∧
    FrameA (fun y => 108 ≤ y ∧ y ≤ 111) (fun j => 42 ≤ j ∧ j ≤ 45) (fun b k => b = 14 ∧ 1 ≤ k) σ7 σ'
  refine XV.mono (XV.forN hL (i := 42) (n := rD) (one := rOne) (by omega) (by simp only [rD]; omega)
    (by simp only [rOne]; omega) (by simp only [rD]; omega) (by simp only [rOne]; omega) d (sdotUnits d + 8)
    (by omega) J σ7 (by rw [N7 _ (by simp only [rD]; omega), hD]) (by rw [N7 _ (by simp only [rOne]; omega), h1])
    ⟨by rw [Env.setNat_nat, if_neg (by omega), e7]; simp, by rw [Env.setNat_draws, dd7],
      fun i' h => absurd h (Nat.not_lt_zero _), (FrameA.refl _ _ _ σ7).setNat ⟨le_refl _, by omega⟩ 0⟩ ?_)
    le_rfl ?_
  · intro t ht σ' ⟨hr, hdr, hc, hF⟩ hkt hkn hk1
    refine XV.mono (XV.rowC hL (by omega) (by omega) (by omega) (i := t) (m := m) (bt := bt) (muS := muS)
      (aS := aS) (Nv := Nv) (PF := PF) (DD := Dp * D) ht hkn hk1
      (by rw [hF.2.1 _ (by simp only [sZ]; omega), r7 _ (by simp only [sZ]; omega), hz])
      (by rw [hF.2.1 _ (by omega), r7 _ (by omega), hpf])
      (by rw [hF.2.1 _ (by omega), k7])
      (fun j => by rw [hF.2.2.1 _ _ (by simp only [aMuS]; omega), A7 _ _ (by simp only [aMuS]; omega), hmu])
      (fun j k => by rw [hF.2.2.1 _ _ (by simp only [aAS]; omega), A7 _ _ (by simp only [aAS]; omega), has])
      (fun k => by rw [hF.2.2.1 _ _ (by omega), y7]) hkt hr bmu baS bN bPF bDD hdm hℓ) le_rfl ?_
    rintro σ'' ⟨w1, w2, w3, w4⟩
    refine ⟨by rw [w4.1 _ (by omega), hkt], by rw [w4.1 _ (by simp only [rD]; omega), hkn],
      by rw [w4.1 _ (by simp only [rOne]; omega), hk1], ?_, by rw [Env.setNat_draws, w3, hdr], ?_, ?_⟩
    · rw [Env.setNat_nat, if_neg (by omega), w2]; ring
    · intro i' hi' hd'
      rw [Env.setNat_arr]
      by_cases hit : i' = t
      · subst hit; rw [w1]
      · rw [w4.2.2.1 _ _ (by omega)]; exact hc i' (by omega) hd'
    · exact (hF.trans (w4.mono (fun y h => h) (fun j h => by omega) (fun b k h => ⟨h.1, by omega⟩))).setNat
        ⟨by omega, by omega⟩ _
  · rintro σ' ⟨⟨-, hdr, hc, hF⟩, -⟩
    refine ⟨by rw [hF.2.2.1 _ _ (by omega), z7], fun i => by rw [hc i i.2 i.2], hdr, ?_⟩
    exact G7.trans (hF.mono (fun y h => by simp only [hSd]; omega) (fun j h => by simp only [hNd]; omega)
      (fun b k h => by simp only [hAd]; omega))

end AdversarialBco.Unified.ProgO
