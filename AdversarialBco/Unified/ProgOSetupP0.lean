/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetup

@[expose] public section

/-!
# BL-O's setup: P0

`xp0O`: from the environment after the machine's setup, `1` into `rOne`, `n` (input cell `1`) into `sN`, `1, 2, 4`
into the slots `26, 27, 28`; `k_δ = size ⌊(den + num - 1)/num⌋` from the input cells `2, 3` of `δ` into `sKd`
(`kDel_eq`); the frame centre `a` (input cells `8 + 2 i`, `9 + 2 i`) into `aC` in the form of the play leaf, over the
common denominator `D = ∏ den_i`, numerators `num_j (D / den_j)` (two loops, `xdenL` and `xnumL`).
`p0SpecO : P0SpecO xp0O 64 1 172 48 16`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The input cells -/

section Input

variable {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}

theorem inputU_num (j : Fin d) : inputU d n δ r0 R0 a ((8 + 2 * (j : ℕ) : ℕ) : ℤ) = (a j).num := by
  have h1 : (((8 + 2 * (j : ℕ) : ℕ) : ℤ) - 8).toNat = 2 * (j : ℕ) := by push_cast; omega
  have h2 : 2 * (j : ℕ) / 2 = j := by omega
  have h3 : 2 * (j : ℕ) % 2 = 0 := by omega
  unfold inputU
  rw [if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    dif_pos ⟨by push_cast; omega, by rw [h1, h2]; exact j.2⟩]
  simp only [h1, h2, h3, if_true]

theorem inputU_den (j : Fin d) : inputU d n δ r0 R0 a ((9 + 2 * (j : ℕ) : ℕ) : ℤ) = (a j).den := by
  have h1 : (((9 + 2 * (j : ℕ) : ℕ) : ℤ) - 8).toNat = 2 * (j : ℕ) + 1 := by push_cast; omega
  have h2 : (2 * (j : ℕ) + 1) / 2 = j := by omega
  have h3 : (2 * (j : ℕ) + 1) % 2 = 1 := by omega
  unfold inputU
  rw [if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    if_neg (by push_cast; omega), if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    if_neg (by push_cast; omega), if_neg (by push_cast; omega),
    dif_pos ⟨by push_cast; omega, by rw [h1, h2]; exact j.2⟩]
  simp only [h1, h2, h3]
  simp

end Input

/-- Reads a cell of an environment built by `setNat`, `setSc`, `setArr`. -/
macro "esimp" : tactic => `(tactic| simp only [Env.setNat_nat, Env.setSc_nat, Env.setArr_nat, Env.setSc_sc,
  Env.setNat_sc, Env.setArr_sc, rOne, rD, ↓reduceIte, Nat.reduceEqDiff])

/-! ## The common denominator of the centre -/

/-- The partial product `∏_{j < t} dn j`. -/
def pdn (dn : ℕ → ℤ) (t : ℕ) : ℤ := ∏ j ∈ Finset.range t, dn j

theorem pdn_succ (dn : ℕ → ℤ) (t : ℕ) : pdn dn (t + 1) = pdn dn t * dn t := Finset.prod_range_succ _ _

theorem pdn_pos {dn : ℕ → ℤ} (h : ∀ j, 0 < dn j) (t : ℕ) : 0 < pdn dn t :=
  Finset.prod_pos fun j _ => h j

theorem pdn_mono {dn : ℕ → ℤ} (h : ∀ j, 0 < dn j) {t t' : ℕ} (htt : t ≤ t') : pdn dn t ≤ pdn dn t' := by
  induction htt with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [pdn_succ]
    have := pdn_pos h m
    have := h m
    nlinarith

theorem dn_le_pdn {dn : ℕ → ℤ} (h : ∀ j, 0 < dn j) {t N : ℕ} (ht : t < N) : dn t ≤ pdn dn N := by
  have h1 := pdn_mono h (Nat.succ_le_of_lt ht)
  rw [pdn_succ] at h1
  have := pdn_pos h t
  have := h t
  nlinarith

theorem pdn_dvd (dn : ℕ → ℤ) {t N : ℕ} (ht : t < N) : dn t ∣ pdn dn N :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 ht)

/-- Loop 1: `135 := ∏_{j < d} dn j`, the denominators read from the input cells `9 + 2 j`. -/
def xdenL (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 12 9))) (.seq (.prim (.frag (.nconst 13 2))) (.seq (toX (VL.sconst L 135 1))
    (xforN 11 rD rOne (.seq (xrdIn L 136 12) (.seq (toX (VL.sop2 L .mul 135 135 136))
      (.prim (.frag (.nadd 12 12 13))))))))

/-- The cells of the loops. -/
def SDen (y : ℕ) : Prop := 135 ≤ y ∧ y ≤ 138
def NDen (j : ℕ) : Prop := 11 ≤ j ∧ j ≤ 14

set_option maxHeartbeats 2000000 in
theorem XV.denL {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) {dn : ℕ → ℤ} (hdn : ∀ j, 0 < dn j) (hin : ∀ j < d, X.inp (9 + 2 * j) = dn j)
    (hoff : 8 + 2 * d ≤ X.off) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hP : pdn dn d < 2 ^ ℓ)
    (hda : 10 + 2 * d < 2 ^ ℓa) (hl : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xdenL L) σ (d * 6 + 6) (fun σ' =>
      σ'.sc 135 = pdn dn d ∧ σ'.draws = σ.draws ∧ FrameA SDen NDen (fun _ _ => False) σ σ') := by
  have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hPpos : ∀ t, 0 < pdn dn t := pdn_pos hdn
  refine XV.mono (K := 1 + (1 + (1 + (d * (3 + 3) + 3)))) ?_ (by ring_nf; omega) fun _ h => h
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 9 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nconst hL (i := 13) (by omega) 2 (by omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.sconst hL (x := 135) (by omega) 1 rfl h1l) fun σ3 e3 => ?_
  subst e3
  set σ3 := ((σ.setNat 12 9).setNat 13 2).setSc 135 ((1 : ℚ) : ℝ) with hσ3
  have F3 : FrameA SDen NDen (fun _ _ => False) σ σ3 :=
    (((FrameA.refl _ _ _ σ).setNat (i := 12) ⟨by omega, by omega⟩ _).setNat (i := 13) ⟨by omega, by omega⟩ _).setSc
      (x := 135) ⟨le_rfl, by omega⟩ _
  refine XV.mono (XV.forN hL (i := 11) (n := rD) (one := rOne) (by omega) (by bomega) (by bomega) (by decide)
    (by decide) d 3 (by omega)
    (fun t σ' => σ'.nat 12 = 9 + 2 * t ∧ σ'.nat 13 = 2 ∧ σ'.sc 135 = pdn dn t ∧ σ'.draws = σ.draws ∧
      FrameA SDen NDen (fun _ _ => False) σ σ') σ3 (by simp [hσ3, hD]) (by simp [hσ3, h1])
    ⟨by simp [hσ3], by simp [hσ3], by simp [hσ3, pdn], by simp [hσ3], F3.setNat ⟨le_rfl, by omega⟩ _⟩
    fun t ht σ' ⟨j12, j13, j135, jdr, jF⟩ ji jn jo => ?_) le_rfl fun σ' h => ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩
  have hdt : dn t ≤ pdn dn d := dn_le_pdn hdn ht
  have hPt : pdn dn t ≤ pdn dn d := pdn_mono hdn ht.le
  have hPt1 : pdn dn (t + 1) ≤ pdn dn d := pdn_mono hdn ht
  have hd0 := hdn t
  refine XV.mono (K := 1 + (1 + 1)) ?_ (by norm_num) fun _ h => h
  have e136 : ((X.inp (σ'.nat 12) : ℤ) : ℝ) = (dn t : ℝ) := by rw [j12, hin t ht]
  refine XV.seq (XV.rdIn (X := X) hL (x := 136) (i := 12) (by omega) (by omega) (by rw [j12]; omega)
    (by rw [j12]; omega) (by rw [e136, ← Int.cast_abs, abs_of_pos hd0]; exact_mod_cast hdt.trans_lt hP))
    fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := 135) (a := 135) (b := 136) (by omega) (by omega) (by omega) (u := pdn dn t)
    (v := dn t) (by simp [j135]) (by simp [e136]) (by rw [abs_of_pos (hPpos t)]; exact hPt.trans_lt hP)
    (by rw [abs_of_pos hd0]; exact hdt.trans_lt hP)
    (by rw [← pdn_succ, abs_of_pos (hPpos _)]; exact hPt1.trans_lt hP)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.nadd hL (i := 12) (a := 12) (b := 13) (by omega) (by omega) (by omega)
    (by esimp; rw [j12]; omega) (by esimp; rw [j13]; omega)) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨by simp [ji], by simp [jn], by simp [jo], by simp [j12, j13]; ring, by simp [j13], ?_, by simp [jdr], ?_⟩
  · simp [pdn_succ]
  · exact ((((jF.setSc (x := 136) ⟨by omega, by omega⟩ _).setSc (x := 135) ⟨le_rfl, by omega⟩ _).setNat
      (i := 12) ⟨by omega, by omega⟩ _).setNat (i := 11) ⟨le_rfl, by omega⟩ _)

/-! ## The numerators of the centre -/

/-- Loop 2: `aC[j + 1] := nm j (D / dn j)` for `j < d`, `D` in the slot `135`, the numerators and denominators read
from the input cells `8 + 2 j`, `9 + 2 j`. -/
def xnumL (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 12 8))) (xforN 11 rD rOne
    (.seq (xrdIn L 136 12) (.seq (.prim (.frag (.nadd 12 12 rOne))) (.seq (xrdIn L 137 12)
    (.seq (.prim (.frag (.nadd 12 12 rOne))) (.seq (xsidiv L 138 135 137) (.seq (toX (VL.sop2 L .mul 138 136 138))
    (.seq (.prim (.frag (.nadd 14 11 rOne))) (toX (VL.aset L aC 14 138))))))))))

/-- The numerator of coordinate `j` over `D`. -/
def cnum (nm dn : ℕ → ℤ) (D : ℤ) (j : ℕ) : ℤ := nm j * (D / dn j)

set_option maxHeartbeats 4000000 in
theorem XV.numL {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) (hNA : 16 ≤ L.NA) {dn nm : ℕ → ℤ} (hdn : ∀ j, 0 < dn j)
    (hin : ∀ j < d, X.inp (9 + 2 * j) = dn j) (hinN : ∀ j < d, X.inp (8 + 2 * j) = nm j)
    (hoff : 8 + 2 * d ≤ X.off) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (h135 : σ.sc 135 = pdn dn d)
    (haC : ∀ k, σ.arr aC k = 0) (hP : pdn dn d < 2 ^ ℓ) (hNP : ∀ j < d, |nm j| * pdn dn d < 2 ^ ℓ)
    (hda : 10 + 2 * d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xnumL L) σ (d * 12 + 4) (fun σ' =>
      (∀ k, σ'.arr aC k = if 1 ≤ k ∧ k ≤ d then cnum nm dn (pdn dn d) (k - 1) else 0) ∧
      σ'.sc 135 = pdn dn d ∧ σ'.draws = σ.draws ∧ FrameA SDen NDen (fun b _ => b = aC) σ σ') := by
  have hPpos : 0 < pdn dn d := pdn_pos hdn d

  refine XV.mono (K := 1 + (d * (9 + 3) + 3)) ?_ (by ring_nf; omega) fun _ h => h
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 8 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.forN hL (i := 11) (n := rD) (one := rOne) (by omega) (by bomega) (by bomega) (by decide)
    (by decide) d 9 (by omega)
    (fun t σ' => σ'.nat 12 = 8 + 2 * t ∧ σ'.sc 135 = pdn dn d ∧
      (∀ k, σ'.arr aC k = if 1 ≤ k ∧ k ≤ t then cnum nm dn (pdn dn d) (k - 1) else 0) ∧ σ'.draws = σ.draws ∧
      FrameA SDen NDen (fun b _ => b = aC) σ σ') (σ.setNat 12 8) (by simp [hD]) (by simp [h1])
    ⟨by simp, by simp [h135], fun k => by simp [haC]; omega, by simp,
      ((FrameA.refl _ _ _ σ).setNat (i := 12) ⟨by omega, by omega⟩ _).setNat ⟨le_rfl, by omega⟩ _⟩
    fun t ht σ' ⟨j12, j135, jaC, jdr, jF⟩ ji jn jo => ?_) le_rfl fun σ' h => ⟨h.1.2.2.1, h.1.2.1, h.1.2.2.2⟩
  have hdt : dn t ≤ pdn dn d := dn_le_pdn hdn ht
  have hd0 := hdn t
  have hq0 : 0 ≤ pdn dn d / dn t := Int.ediv_nonneg hPpos.le hd0.le
  have hq : pdn dn d / dn t ≤ pdn dn d := Int.ediv_le_self _ hPpos.le
  have hnt : |nm t| ≤ |nm t| * pdn dn d := le_mul_of_one_le_right (abs_nonneg _) (by omega)
  have hcn : |cnum nm dn (pdn dn d) t| < 2 ^ ℓ := by
    unfold cnum
    rw [abs_mul, abs_of_nonneg hq0]
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg _)).trans_lt (hNP t ht)
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + 2))))))) ?_ (by norm_num) fun _ h => h
  have eN : ((X.inp (σ'.nat 12) : ℤ) : ℝ) = (nm t : ℝ) := by rw [j12, hinN t ht]
  refine XV.seq (XV.rdIn (X := X) hL (x := 136) (i := 12) (by omega) (by omega) (by rw [j12]; omega)
    (by rw [j12]; omega) (by rw [eN, ← Int.cast_abs]; exact_mod_cast hnt.trans_lt (hNP t ht))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := 12) (a := 12) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [j12]; omega) (by esimp; rw [jo]; omega)) fun σ3 e3 => ?_
  subst e3
  have eD : ((X.inp (((σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).setNat 12
      ((σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).nat 12 + (σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).nat rOne)).nat 12)
      : ℤ) : ℝ) = (dn t : ℝ) := by
    simp only [Env.setNat_nat, if_pos, Env.setSc_nat, j12, jo]
    rw [show 8 + 2 * t + 1 = 9 + 2 * t by ring, hin t ht]
  refine XV.seq (XV.rdIn (X := X) hL (x := 137) (i := 12) (by omega) (by omega) (by esimp; rw [j12, jo]; omega)
    (by esimp; rw [j12, jo]; omega) (by rw [eD, ← Int.cast_abs, abs_of_pos hd0]; exact_mod_cast hdt.trans_lt hP))
    fun σ4 e4 => ?_
  subst e4
  rw [eD]
  refine XV.seq (XV.nadd hL (i := 12) (a := 12) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [j12, jo]; omega) (by esimp; rw [jo]; omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.divI hL (x := 138) (a := 135) (b := 137) (by omega) (by omega) (by omega)
    (u := pdn dn d) (v := dn t) (by simp [j135]) (by simp) (by rw [abs_of_pos hPpos]; exact hP)
    (by rw [abs_of_pos hd0]; exact hdt.trans_lt hP)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.mulI hL (x := 138) (a := 136) (b := 138) (by omega) (by omega) (by omega)
    (u := nm t) (v := pdn dn d / dn t) (by simp [eN]) (by simp)
    (by exact hnt.trans_lt (hNP t ht)) (by rw [abs_of_nonneg hq0]; exact hq.trans_lt hP) hcn) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.nadd hL (i := 14) (a := 11) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [ji]; omega) (by esimp; rw [jo]; omega)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.aset hL (a := aC) (i := 14) (x := 138) (by bomega) (by omega) (by omega)
    (by esimp; rw [ji, jo]; unfold asz; nlinarith)
    (by esimp; rw [← Int.cast_abs]; unfold cnum at hcn; exact_mod_cast hcn)) le_rfl fun σ9 e9 => ?_
  subst e9
  refine ⟨by simp [ji], by simp [jn], by simp [jo], by simp [j12, jo]; ring, by simp [j135], fun k => ?_,
    by simp [jdr], ?_⟩
  · by_cases hk : k = t + 1
    · subst hk
      have h' : 1 ≤ t + 1 ∧ t + 1 ≤ t + 1 := ⟨by omega, le_rfl⟩
      simp [ji, jo, h', cnum]
    · have h' : (1 ≤ k ∧ k ≤ t + 1) ↔ (1 ≤ k ∧ k ≤ t) := by omega
      simp [ji, jo, hk, jaC k, h']
  · exact (((((((((jF.setSc (x := 136) ⟨by omega, by omega⟩ _).setNat (i := 12) ⟨by omega, by omega⟩ _).setSc
      (x := 137) ⟨by omega, by omega⟩ _).setNat (i := 12) ⟨by omega, by omega⟩ _).setSc (x := 138)
      ⟨by omega, by omega⟩ _).setSc (x := 138) ⟨by omega, by omega⟩ _).setNat (i := 14) ⟨by omega, by omega⟩ _).setArr
      (b := aC) rfl _).setNat (i := 11) ⟨le_rfl, by omega⟩ _)

/-! ## `k_δ` -/

/-- `sKd := lg((den + num - 1)/num + 1) = size ⌈den/num⌉` from the input cells `2`, `3` (`num`, `den` of `δ`). -/
def xkd (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 8 2))) (.seq (xrdIn L 130 8) (.seq (.prim (.frag (.nconst 8 3)))
  (.seq (xrdIn L 131 8) (.seq (toX (VL.sop2 L .add 132 131 130)) (.seq (toX (VL.sop2 L .sub 132 132 26))
  (.seq (xsidiv L 133 132 130) (.seq (toX (VL.sop2 L .add 133 133 26)) (.seq (xclogS L 134 133 10 rOne)
    (toX (VL.ncast L sKd 10))))))))))

/-- The cells `xkd` changes. -/
def SKd (y : ℕ) : Prop := (130 ≤ y ∧ y ≤ 134) ∨ y = sKd

theorem kd_quot_le {num den : ℤ} (hnum : 0 < num) (hden : 0 < den) :
    0 ≤ (den + num - 1) / num ∧ (den + num - 1) / num ≤ den := by
  refine ⟨Int.ediv_nonneg (by omega) hnum.le, ?_⟩
  have h1 := Int.ediv_mul_le (den + num - 1) hnum.ne'
  by_contra h
  have h := lt_of_not_ge h
  have : (den + 1) * num ≤ (den + num - 1) / num * num := Int.mul_le_mul_of_nonneg_right (by omega) hnum.le
  nlinarith

set_option maxHeartbeats 2000000 in
theorem XV.kd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) {num den : ℤ} {G : ℕ} (hnum : 0 < num) (hden : 0 < den) (h2 : X.inp 2 = num)
    (h3 : X.inp 3 = den) (hoff : 4 ≤ X.off) (h1 : σ.nat rOne = 1) (h26 : σ.sc 26 = 1)
    (hb : den + num < 2 ^ ℓ) (hG : den + 1 ≤ 2 ^ G) (hGa : G < 2 ^ ℓa) (hGl : G < ℓ) (h4 : 4 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xkd L) σ (4 * G + 13) (fun σ' =>
      σ'.sc sKd = ((Nat.clog 2 ((den + num - 1) / num + 1).toNat : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA SKd (fun j => j = 8 ∨ j = 10) (fun _ _ => False) σ σ') := by
  obtain ⟨hq0, hq⟩ := kd_quot_le hnum hden
  have hnl : num < 2 ^ ℓ := by omega
  have hdl : den < 2 ^ ℓ := by omega
  have hG2 : (2 : ℤ) ^ G < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hGl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((4 * G + 4) + 1))))))))) ?_ (by omega)
    fun _ h => h
  refine XV.seq (XV.nconst hL (i := 8) (by omega) 2 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.rdIn (X := X) hL (x := 130) (i := 8) (by omega) (by omega) (by simp; omega) (by simp; omega)
    (by simp only [Env.setNat_nat, if_pos]; rw [h2, ← Int.cast_abs, abs_of_pos hnum]; exact_mod_cast hnl))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := 8) (by omega) 3 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.rdIn (X := X) hL (x := 131) (i := 8) (by omega) (by omega) (by simp; omega) (by simp; omega)
    (by simp only [Env.setNat_nat, if_pos]; rw [h3, ← Int.cast_abs, abs_of_pos hden]; exact_mod_cast hdl))
    fun σ4 e4 => ?_
  subst e4
  simp only [Env.setNat_nat, if_pos, h2, h3] at *
  refine XV.seq (XV.addI hL (x := 132) (a := 131) (b := 130) (by omega) (by omega) (by omega) (u := den) (v := num)
    (by simp) (by simp) (by rw [abs_of_pos hden]; exact hdl) (by rw [abs_of_pos hnum]; exact hnl)
    (by rw [abs_of_pos (by omega)]; exact hb)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.subI hL (x := 132) (a := 132) (b := 26) (by omega) (by omega) (by omega) (u := den + num)
    (v := 1) (by simp) (by simp [h26]) (by rw [abs_of_pos (by omega)]; exact hb)
    (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))
    (by rw [abs_of_nonneg (by omega)]; omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.divI hL (x := 133) (a := 132) (b := 130) (by omega) (by omega) (by omega)
    (u := den + num - 1) (v := num) (by simp) (by simp) (by rw [abs_of_nonneg (by omega)]; omega)
    (by rw [abs_of_pos hnum]; exact hnl)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.addI hL (x := 133) (a := 133) (b := 26) (by omega) (by omega) (by omega)
    (u := (den + num - 1) / num) (v := 1) (by simp) (by simp [h26]) (by rw [abs_of_nonneg hq0]; omega)
    (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))
    (by rw [abs_of_nonneg (by omega)]; omega)) fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.clogS hL (w := 134) (x := 133) (c := 10) (one := rOne) (G := G)
    (v := (den + num - 1) / num + 1) (by omega) (by omega) (by omega) (by bomega) (by decide) (by decide)
    (by simp) (by omega) (by omega) (by simp [h1]) hGa hGl) fun σ9 ⟨c9, d9, F9⟩ => ?_
  have e2G : (((2 : ℕ) ^ G : ℕ) : ℤ) = (2 : ℤ) ^ G := by push_cast; rfl
  refine XV.mono (XV.ncastA hL (x := sKd) (i := 10) (by simp only [sKd]; omega) (by omega) c9
    (lt_of_le_of_lt (Nat.clog_le_of_le_pow (show ((den + num - 1) / num + 1).toNat ≤ 2 ^ G by omega)) hGa))
    le_rfl fun σ' ⟨c', d', F'⟩ => ⟨c', by rw [d', d9]; simp, ?_⟩
  exact ((((((((((FrameA.refl _ _ _ σ).setNat (i := 8) (Or.inl rfl) _).setSc (x := 130)
    (Or.inl ⟨le_rfl, by omega⟩) _).setNat (i := 8) (Or.inl rfl) _).setSc (x := 131) (Or.inl ⟨by omega, by omega⟩)
    _).setSc (x := 132) (Or.inl ⟨by omega, by omega⟩) _).setSc (x := 132) (Or.inl ⟨by omega, by omega⟩) _).setSc
    (x := 133) (Or.inl ⟨by omega, by omega⟩) _).setSc (x := 133) (Or.inl ⟨by omega, by omega⟩) _).trans
    ((FrameA.ofP F9).mono (fun y h => Or.inl ⟨by omega, by omega⟩) (fun j h => Or.inr h)
      (fun _ _ h => h))).trans (F'.mono (fun y h => Or.inr h) (fun _ h => h.elim) (fun _ _ h => h))

/-! ## P0 -/

/-- The head of P0: `rOne := 1`, `n` (input cell `1`) into `sN`, `1, 2, 4` into the slots `26, 27, 28`. -/
def xp0hd (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst rOne 1))) (.seq (.prim (.frag (.nconst 8 1))) (.seq (xrdIn L sN 8)
  (.seq (toX (VL.sconst L 26 1)) (.seq (toX (VL.sconst L 27 2)) (toX (VL.sconst L 28 4))))))

/-- **P0 of BL-O**: the head, `k_δ`, the centre's denominator and numerators, then `aC[0] := D`. -/
def xp0O (L : Layout) : XCmdO :=
  .base (.seq (xp0hd L) (.seq (xkd L) (.seq (xdenL L) (.seq (xnumL L) (.seq (.prim (.frag (.nconst 14 0)))
    (toX (VL.aset L aC 14 135)))))))

theorem abs_lt_len (z : ℤ) : |z| < 2 ^ len z := by
  have h := Nat.lt_size_self z.natAbs
  unfold len
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

theorem pdn_le_pow {dn : ℕ → ℤ} {l : ℕ → ℕ} (h : ∀ j, 0 < dn j) (hl : ∀ j, dn j ≤ 2 ^ l j) (t : ℕ) :
    pdn dn t ≤ 2 ^ (∑ j ∈ Finset.range t, l j) := by
  induction t with
  | zero => simp [pdn]
  | succ t ih =>
    rw [pdn_succ, Finset.sum_range_succ, pow_add]
    exact mul_le_mul ih (hl t) (h t).le (by positivity)

/-- `k_δ` as the program computes it. -/
theorem kDel_clog {δ : ℚ} (h0 : 0 < δ) :
    Nat.clog 2 (((δ.den : ℤ) + δ.num - 1) / δ.num + 1).toNat = kDel δ := by
  have hnum : 0 < δ.num := Rat.num_pos.2 h0
  rw [kDel_eq h0, size_eq_clog]
  congr 1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, δ.num = M := ⟨δ.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
  rw [hM, Int.toNat_natCast]
  have hM1 : 1 ≤ M := by omega
  have e : (δ.den : ℤ) + M - 1 = ((δ.den + M - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]; push_cast; ring
  rw [e, ← Int.natCast_div, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, Int.toNat_natCast]

/-- The cells the head of P0 changes. -/
def SHd (y : ℕ) : Prop := y = sN ∨ (26 ≤ y ∧ y ≤ 28)

theorem XV.p0hd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) {n : ℕ} (hin1 : X.inp 1 = n) (hoff : 2 ≤ X.off) (hnl : (n : ℤ) < 2 ^ ℓ) (hl : 3 ≤ ℓ)
    (ha : 4 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xp0hd L) σ 6 (fun σ' => σ'.nat rOne = 1 ∧ σ'.sc sN = n ∧ σ'.sc 26 = 1 ∧ σ'.sc 27 = 2 ∧
      σ'.sc 28 = 4 ∧ σ'.draws = σ.draws ∧ FrameA SHd (fun j => j = rOne ∨ j = 8) (fun _ _ => False) σ σ') := by
  have hl2 : (4 : ℤ) < 2 ^ ℓ := lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ ℓ))
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + 1))))) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.nconst hL (i := rOne) (by bomega) 1 (by omega)) fun _ e => ?_
  subst e
  refine XV.seq (XV.nconst hL (i := 8) (by omega) 1 (by omega)) fun _ e => ?_
  subst e
  refine XV.seq (XV.rdIn (X := X) hL (x := sN) (i := 8) (by bomega) (by omega) (by esimp; omega)
    (by esimp; omega) (by esimp; rw [hin1, ← Int.cast_abs, abs_of_nonneg (by positivity)]; exact_mod_cast hnl))
    fun _ e => ?_
  subst e
  refine XV.seq (XV.constI hL (x := 26) (by omega) 1 (by rw [abs_one]; omega)) fun _ e => ?_
  subst e
  refine XV.seq (XV.constI hL (x := 27) (by omega) 2 (by rw [abs_two]; omega)) fun _ e => ?_
  subst e
  refine XV.mono (XV.constI hL (x := 28) (by omega) 4 (by norm_num; omega)) le_rfl fun _ e => ?_
  subst e
  refine ⟨by esimp, by esimp; rw [hin1]; simp, by esimp; simp, by esimp; simp, by esimp; simp, by simp, ?_⟩
  exact (((((FrameA.refl _ _ _ σ).setNat (i := rOne) (Or.inl rfl) _).setNat (i := 8) (Or.inr rfl) _).setSc
    (x := sN) (Or.inl rfl) _).setSc (x := 26) (Or.inr ⟨le_rfl, by omega⟩) _).setSc (x := 27)
    (Or.inr ⟨by omega, by omega⟩) _ |>.setSc (x := 28) (Or.inr ⟨by omega, le_rfl⟩) _

set_option maxHeartbeats 8000000 in
/-- **P0 on the machine**, within `64 (W + 1)` units, the centre's integers below `2^{64 (W + 1)}`. -/
theorem p0SpecO : P0SpecO xp0O 64 1 172 48 16 := by
  intro d L w n δ r0 R0 a ℓa ℓ hI hL hR hℓ hℓa
  obtain ⟨hNS, hNN, hNA⟩ := hR
  simp only [pow_one] at hℓ hℓa ⊢
  refine XVO.ofX ?_
  have hd := hI.hd
  have hnum : 0 < δ.num := Rat.num_pos.2 hI.hδ0
  have hden : (0 : ℤ) < δ.den := by exact_mod_cast δ.den_pos
  -- the sizes
  have hS : len δ.num + len (δ.den : ℤ) + ∑ i, (len (a i).num + len ((a i).den : ℤ)) ≤ sizeN δ r0 R0 a := by
    unfold sizeN; omega
  have hW : d + n.size + sizeN δ r0 R0 a + 1 = wU d n δ r0 R0 a := rfl
  have hSl : sizeN δ r0 R0 a + 1 < ℓ := by omega
  have hpl : ∀ m, m ≤ sizeN δ r0 R0 a + 1 → (2 : ℤ) ^ m < 2 ^ ℓ := fun m hm =>
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have hps : ∀ m, m ≤ sizeN δ r0 R0 a + 1 → (2 : ℤ) ^ m < 2 ^ (64 * (wU d n δ r0 R0 a + 1)) := fun m hm =>
    pow_lt_pow_right₀ (by norm_num) (by omega)
  -- the inputs
  set X := (ctxU w n δ r0 R0 a).X with hX
  have hoff : X.off = 8 + 2 * d := rfl
  have i1 : X.inp 1 = n := rfl
  have i2 : X.inp 2 = δ.num := rfl
  have i3 : X.inp 3 = δ.den := rfl
  set dn : ℕ → ℤ := fun j => if h : j < d then ((a ⟨j, h⟩).den : ℤ) else 1 with hdn
  set nm : ℕ → ℤ := fun j => if h : j < d then (a ⟨j, h⟩).num else 0 with hnm
  have dn0 : ∀ j, 0 < dn j := fun j => by
    simp only [hdn]; split_ifs
    · exact_mod_cast (a _).den_pos
    · norm_num
  have iD : ∀ j < d, X.inp (9 + 2 * j) = dn j := fun j hj => by
    simp only [hdn, dif_pos hj]; exact inputU_den (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) ⟨j, hj⟩
  have iN : ∀ j < d, X.inp (8 + 2 * j) = nm j := fun j hj => by
    simp only [hnm, dif_pos hj]; exact inputU_num (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) ⟨j, hj⟩
  -- the bounds of the centre
  set SD := ∑ i : Fin d, len ((a i).den : ℤ) with hSD
  have hPD : pdn dn d ≤ 2 ^ SD := by
    have h := pdn_le_pow (l := fun j => if h : j < d then len ((a ⟨j, h⟩).den : ℤ) else 0) dn0 (fun j => by
      simp only [hdn]; split_ifs with h
      · exact (le_abs_self _).trans (abs_lt_len _).le
      · simp) d
    refine h.trans (pow_le_pow_right₀ (by norm_num) (le_of_eq ?_))
    rw [hSD, ← Fin.sum_univ_eq_sum_range (fun j => if h : j < d then len ((a ⟨j, h⟩).den : ℤ) else 0) d]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  have hNP0 : ∀ j < d, |nm j| * pdn dn d ≤ 2 ^ sizeN δ r0 R0 a := fun j hj => by
    have h1 : |nm j| < 2 ^ len (a ⟨j, hj⟩).num := by simp only [hnm, dif_pos hj]; exact abs_lt_len _
    have h2 : len (a ⟨j, hj⟩).num + SD ≤ sizeN δ r0 R0 a := by
      have := Finset.single_le_sum (f := fun i : Fin d => len (a i).num) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ ⟨j, hj⟩)
      rw [Finset.sum_add_distrib] at hS
      omega
    calc |nm j| * pdn dn d ≤ 2 ^ len (a ⟨j, hj⟩).num * 2 ^ SD :=
          mul_le_mul h1.le hPD (pdn_pos dn0 d).le (by positivity)
      _ = 2 ^ (len (a ⟨j, hj⟩).num + SD) := (pow_add _ _ _).symm
      _ ≤ 2 ^ sizeN δ r0 R0 a := pow_le_pow_right₀ (by norm_num) h2
  have hNP : ∀ j < d, |nm j| * pdn dn d < 2 ^ ℓ := fun j hj => (hNP0 j hj).trans_lt (hpl _ (by omega))
  have hSDS : SD ≤ sizeN δ r0 R0 a := by rw [Finset.sum_add_distrib] at hS; omega
  have hPS : pdn dn d ≤ 2 ^ sizeN δ r0 R0 a := hPD.trans (pow_le_pow_right₀ (by norm_num) hSDS)
  have hPl : pdn dn d < 2 ^ ℓ := hPS.trans_lt (hpl _ (by omega))
  have hnl : (n : ℤ) < 2 ^ ℓ := by
    have : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : (2 : ℤ) ^ n.size < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
    exact lt_trans (by exact_mod_cast this) h2
  have hnumS : δ.num < 2 ^ sizeN δ r0 R0 a :=
    (le_abs_self _).trans_lt ((abs_lt_len _).trans_le (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hdenS : (δ.den : ℤ) < 2 ^ len (δ.den : ℤ) := (le_abs_self _).trans_lt (abs_lt_len _)
  have hdenS' : (2 : ℤ) ^ len (δ.den : ℤ) ≤ 2 ^ sizeN δ r0 R0 a := pow_le_pow_right₀ (by norm_num) (by omega)
  have hS2 : (2 : ℤ) ^ (sizeN δ r0 R0 a + 1) = 2 * 2 ^ sizeN δ r0 R0 a := by ring
  have hS1 := hpl (sizeN δ r0 R0 a + 1) le_rfl
  refine XV.mono (K := 6 + ((4 * len (δ.den : ℤ) + 13) + ((d * 6 + 6) + ((d * 12 + 4) + (1 + 2))))) ?_
    (by omega) fun _ h => h
  -- the head
  refine XV.seq (XV.p0hd (X := X) hL hNS hNN i1 (by omega) hnl (by omega) (by omega))
    fun σ1 ⟨h1One, h1N, h126, h127, h128, d1, F1⟩ => ?_
  -- `k_δ`
  refine XV.seq (XV.kd (X := X) hL hNS hNN (G := len (δ.den : ℤ)) hnum hden i2 i3 (by omega) h1One h126
    (by linarith) (by linarith) (by omega) (by omega) (by omega)) fun σ2 ⟨h2Kd, d2, F2⟩ => ?_
  have n21 : ∀ j, j ≠ 8 → j ≠ 10 → σ2.nat j = σ1.nat j := fun j h h' => F2.1 j (by tauto)
  have hD2 : σ2.nat rD = d := by
    rw [n21 rD (by decide) (by decide), F1.1 rD (by simp only [rOne, rD]; omega)]; simp [envSetup]
  have hO2 : σ2.nat rOne = 1 := by rw [n21 rOne (by decide) (by decide), h1One]
  -- the denominator
  refine XV.seq (XV.denL (X := X) hL hNS hNN dn0 iD (by omega) hD2 hO2 hPl (by omega) (by omega))
    fun σ3 ⟨h3P, d3, F3⟩ => ?_
  have hD3 : σ3.nat rD = d := (F3.1 rD (by simp only [NDen, rD]; omega)).trans hD2
  have hO3 : σ3.nat rOne = 1 := (F3.1 rOne (by simp only [NDen, rOne]; omega)).trans hO2
  have a31 : ∀ b k, σ3.arr b k = 0 := fun b k => by
    rw [F3.2.2.1 b k id, F2.2.2.1 b k id, F1.2.2.1 b k id]; simp [envSetup]
  -- the numerators
  refine XV.seq (XV.numL (X := X) hL hNS hNN hNA dn0 iD iN (by omega) hD3 hO3 h3P (a31 aC) hPl hNP (by omega))
    fun σ4 ⟨h4C, h4P, d4, F4⟩ => ?_
  -- `aC[0] := D`
  refine XV.seq (XV.nconst hL (i := 14) (by omega) 0 (by omega)) fun σ5 e5 => ?_
  subst e5
  have hk5 : (σ4.setNat 14 0).nat 14 < asz d := by
    rw [Env.setNat_nat, if_pos rfl]; unfold asz; nlinarith
  have hv5 : |(σ4.setNat 14 0).sc 135| < 2 ^ ℓ := by
    rw [Env.setNat_sc, h4P, ← Int.cast_abs, abs_of_pos (pdn_pos dn0 d)]; exact_mod_cast hPl
  refine XV.mono (XV.aset hL (a := aC) (i := 14) (x := 135) (by bomega) (by omega) (by omega) hk5 hv5) le_rfl
    fun σ6 e6 => ?_
  subst e6
  -- the frames from the setup to `σ4`
  have N41 : ∀ j, ¬ NDen j → j ≠ 8 → j ≠ 10 → ¬ (j = rOne ∨ j = 8) → σ4.nat j = (envSetup rD d).nat j :=
    fun j h1 h2 h3 h4 => (F4.1 j h1).trans ((F3.1 j h1).trans ((n21 j h2 h3).trans (F1.1 j h4)))
  have S4 : ∀ y, ¬ SDen y → ¬ SKd y → σ4.sc y = σ1.sc y := fun y h1 h2 =>
    (F4.2.1 y h1).trans ((F3.2.1 y h1).trans (F2.2.1 y h2))
  have S41 : ∀ y, ¬ SDen y → ¬ SKd y → ¬ SHd y → σ4.sc y = (envSetup rD d).sc y := fun y h1 h2 h3 =>
    (S4 y h1 h2).trans (F1.2.1 y h3)
  have hDpos := pdn_pos dn0 d
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Env.setArr_nat, Env.setNat_nat, if_neg (by decide)]
    exact (F4.1 rD (by simp only [NDen, rD]; omega)).trans hD3
  · rw [Env.setArr_nat, Env.setNat_nat, if_neg (by decide),
      N41 rM (by simp only [NDen, rM]; omega) (by decide) (by decide) (by decide)]
    simp [envSetup]
  · rw [Env.setArr_nat, Env.setNat_nat, if_neg (by decide),
      N41 rMk (by simp only [NDen, rMk]; omega) (by decide) (by decide) (by decide)]
    simp [envSetup]
  · rw [Env.setArr_nat, Env.setNat_nat, if_neg (by decide)]
    exact (F4.1 rOne (by simp only [NDen, rOne]; omega)).trans hO3
  · rw [Env.setArr_sc, Env.setNat_sc, S41 0 (by simp only [SDen]; omega) (by simp only [SKd, sKd]; omega)
      (by simp only [SHd, sN]; omega)]
    simp [envSetup]
  · rw [Env.setArr_sc, Env.setNat_sc, S41 sMode (by simp only [SDen, sMode]; omega)
      (by simp only [SKd, sKd, sMode]; omega) (by simp only [SHd, sN, sMode]; omega)]
    simp [envSetup]
  · rw [Env.setArr_sc, Env.setNat_sc, S4 sN (by simp only [SDen, sN]; omega) (by simp only [SKd, sKd, sN]; omega),
      h1N]
  · rw [Env.setArr_sc, Env.setNat_sc, S41 sK (by simp only [SDen, sK]; omega)
      (by simp only [SKd, sKd, sK]; omega) (by simp only [SHd, sN, sK]; omega)]
    simp [envSetup]
  · rw [Env.setArr_sc, Env.setNat_sc, S41 sL (by simp only [SDen, sL]; omega)
      (by simp only [SKd, sKd, sL]; omega) (by simp only [SHd, sN, sL]; omega)]
    simp [envSetup]
  · rw [Env.setArr_sc, Env.setNat_sc, S4 26 (by simp only [SDen]; omega) (by simp only [SKd, sKd]; omega), h126]
  · rw [Env.setArr_sc, Env.setNat_sc, S4 27 (by simp only [SDen]; omega) (by simp only [SKd, sKd]; omega), h127]
  · rw [Env.setArr_sc, Env.setNat_sc, S4 28 (by simp only [SDen]; omega) (by simp only [SKd, sKd]; omega), h128]
  · rw [Env.setArr_sc, Env.setNat_sc, F4.2.1 sKd (by simp only [SDen, sKd]; omega),
      F3.2.1 sKd (by simp only [SDen, sKd]; omega), h2Kd, kDel_clog hI.hδ0]
    push_cast; rfl
  · refine ⟨pdn dn d, hDpos, hPS.trans_lt (hps _ (by omega)), ?_, fun j => ?_⟩
    · rw [Env.setArr_arr, if_pos ⟨rfl, by rw [Env.setNat_nat, if_pos rfl]⟩, Env.setNat_sc, h4P]
    have hj := j.2
    refine ⟨cnum nm dn (pdn dn d) j, ?_, ?_, ?_⟩
    · have hq0 : 0 ≤ pdn dn d / dn j := Int.ediv_nonneg hDpos.le (dn0 j).le
      have hq : pdn dn d / dn j ≤ pdn dn d := Int.ediv_le_self _ hDpos.le
      unfold cnum
      rw [abs_mul, abs_of_nonneg hq0]
      calc |nm j| * (pdn dn d / dn j) ≤ |nm j| * pdn dn d := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
        _ ≤ 2 ^ sizeN δ r0 R0 a := hNP0 j j.2
        _ < _ := hps _ (by omega)
    · rw [Env.setArr_arr, if_neg (by simp), Env.setNat_arr, h4C, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    · obtain ⟨q, hq⟩ := pdn_dvd dn hj
      have hq0 : 0 < q := pos_of_mul_pos_right (hq ▸ hDpos) (dn0 j).le
      have hdq : pdn dn d / dn j = q := by rw [hq, Int.mul_ediv_cancel_left _ (dn0 j).ne']
      have hnmj : nm j = (a j).num := by simp only [hnm, dif_pos hj, Fin.eta]
      have hdnj : dn j = (a j).den := by simp only [hdn, dif_pos hj, Fin.eta]
      unfold cnum
      rw [hdq, hq, hnmj, hdnj]
      push_cast
      rw [mul_div_mul_right _ _ (by exact_mod_cast hq0.ne' : (q : ℚ) ≠ 0)]
      exact Rat.num_div_den (a j)
  · intro k hk
    rw [Env.setArr_arr, if_neg (by simp; omega), Env.setNat_arr, h4C, if_neg (by omega)]
    exact Int.cast_zero
  · intro b _ hb k
    rw [Env.setArr_arr, if_neg (fun h => hb h.1), Env.setNat_arr, F4.2.2.1 b k hb, a31 b k]
  · rw [Env.setArr_draws, Env.setNat_draws, d4, d3, d2, d1]; rfl
  · rw [Env.setArr_rounds, Env.setNat_rounds, F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]; rfl

end AdversarialBco.Unified.ProgO
