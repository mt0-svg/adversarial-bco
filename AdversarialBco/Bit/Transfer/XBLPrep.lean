/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLPrepR
public import AdversarialBco.Bit.Transfer.XBLCall
public import AdversarialBco.Bit.Transfer.XEllReg

@[expose] public section

/-!
# The preparation of BL's calls, part 2: the command on the machine

`xprep L` reduces every pair of the call data by the gcd (`H`, `g`, `ℓ` with the product `D_H` of their reduced
denominators in the slot `105`, `P` with `D_P` in `106`, `f` with `D_f` in `107`: block A), clears them into the
inputs of the block (`num (D / den)`, and `num (D_f / den) D_P` for `f`: block B), writes `D_f`, `R = R_int / 1`, the
reduced pair of `r` and the reduced pair of `D_P e` (block C). `XV.prep` states the result on the integers of the
input cells.
-/

namespace AdversarialBco.Bit.Transfer.BLM.PrepM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP AdversarialBco.Bit.Transfer.BLM.RowM

variable {d : ℕ}

/-- Side conditions on the named cells of XBLInv.lean and XBLCall.lean. -/
macro "pwgo" : tactic => `(tactic| first | omega | decide |
  ((simp only [rD, rM, rMk, rOne, rPF, sZ, sRint, aEH, aEg, aEP, aEf, aPHn, aPHd, aPgn, aPgd, aPPn, aPPd, aPfn, aPfd,
    sPl, sEl, SPrep, SRow, NPrep, NRow, APrep, ARow] at *) <;> omega) | fail "pwgo")

/-- Block A: `33 := d d`, the four units, the reductions. -/
def xprepA (L : Layout) : XCmd :=
  .seq (xnmul 33 rD rD) (.seq (toX (VL.sconst L 105 ((1 : ℤ) : ℚ))) (.seq (toX (VL.sconst L 106 ((1 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L 107 ((1 : ℤ) : ℚ))) (.seq (toX (VL.sconst L 108 ((1 : ℤ) : ℚ)))
  (.seq (xredArr L aPHn aPHd aEH 12 34 33 105) (.seq (xredArr L aPgn aPgd aEg 13 34 rD 105)
  (.seq (xred L sZ sPl (sPl + 1) 98 99 100 109 110) (.seq (toX (VL.sop2 L .mul 105 105 110))
  (.seq (xredArr L aPPn aPPd aEP 14 34 33 106) (xredArr L aPfn aPfd aEf 15 34 rD 107))))))))))

/-- Block B: the clearing of `H`, `g`, `ℓ`, `P`, `f`. -/
def xprepB (L : Layout) : XCmd :=
  .seq (xscaleArr L aEH 12 34 33 105 108) (.seq (xscaleArr L aEg 13 34 rD 105 108)
  (.seq (xsidiv L 111 105 110) (.seq (toX (VL.sop2 L .mul 80 109 111))
  (.seq (xscaleArr L aEP 14 34 33 106 108) (xscaleArr L aEf 15 34 rD 107 106)))))

/-- Block C: `D_f`, `R`, `r`, `D_P e`. -/
def xprepC (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add 81 107 sZ)) (.seq (toX (VL.sop2 L .add 82 sRint sZ))
  (.seq (toX (VL.sconst L 83 ((1 : ℤ) : ℚ))) (.seq (xred L sZ (sPl + 2) (sPl + 3) 98 99 100 84 85)
  (.seq (toX (VL.sop2 L .mul 112 106 (sPl + 4))) (xred L sZ 112 (sPl + 5) 98 99 100 86 87)))))

/-- The preparation command. -/
def xprep (L : Layout) : XCmd := .seq (xprepA L) (.seq (xprepB L) (xprepC L))

def prepAUnits (d s : ℕ) : ℕ :=
  1 + (1 + (1 + (1 + (1 + (redArrUnits (d * d) s + (redArrUnits d s + (redUnits s + (1 +
  (redArrUnits (d * d) s + redArrUnits d s)))))))))
def prepBUnits (d : ℕ) : ℕ :=
  scaleArrUnits (d * d) + (scaleArrUnits d + (1 + (1 + (scaleArrUnits (d * d) + scaleArrUnits d))))
def prepCUnits (d s : ℕ) : ℕ := 1 + (1 + (1 + (redUnits s + (1 + redUnits (s * (d * d) + s)))))

/-- The units of the preparation. -/
def prepUnits (d s : ℕ) : ℕ := prepAUnits d s + (prepBUnits d + prepCUnits d s)

/-- `D_H`: the product of the reduced denominators of `H`, `g`, `ℓ`. -/
def DH (d : ℕ) (uH vH ug vg : ℕ → ℤ) (ul vl : ℤ) : ℤ :=
  1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) * (∏ k ∈ Finset.range d, redD (ug k) (vg k)) * redD ul vl

/-- `D_P` and `D_f`. -/
def DPr (K : ℕ) (u v : ℕ → ℤ) : ℤ := 1 * ∏ k ∈ Finset.range K, redD (u k) (v k)

theorem prod_rD_le {K s : ℕ} {u v : ℕ → ℤ} (bv : ∀ k < K, 0 < v k ∧ v k ≤ 2 ^ s) :
    0 < ∏ k ∈ Finset.range K, redD (u k) (v k) ∧ ∏ k ∈ Finset.range K, redD (u k) (v k) ≤ 2 ^ (s * K) := by
  obtain ⟨p1, p2⟩ := prod_range_abs_le (fun k => redD (u k) (v k)) (2 ^ s) (one_le_pow₀ (by norm_num)) K
    (fun k hk => by
      obtain ⟨_, _, h3, h4⟩ := red_bounds (u k) (v k) (bv k hk).1
      exact ⟨h3, h4.trans (bv k hk).2⟩)
  exact ⟨by omega, by rw [pow_mul]; exact p2⟩

theorem rD_bounds {u v : ℤ} {s : ℕ} (hv : 0 < v) (bu : |u| ≤ 2 ^ s) (bv : v ≤ 2 ^ s) :
    |redN u v| ≤ 2 ^ s ∧ 1 ≤ redD u v ∧ redD u v ≤ 2 ^ s := by
  obtain ⟨_, h2, h3, h4⟩ := red_bounds u v hv
  exact ⟨h2.trans bu, h3, h4.trans bv⟩

theorem G_mono {σ σ' : Env d} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (hS : ∀ y, S y → (80 ≤ y ∧ y < 88) ∨ (96 ≤ y ∧ y < 256)) (hN : ∀ j, N j → 32 ≤ j ∧ j < 64)
    (hA : ∀ a k, Ar a k → 8 ≤ a ∧ a < 16) (h : FrameA S N Ar σ σ') :
    FrameA SPrep NPrep (fun a _ => APrep a) σ σ' :=
  h.mono (fun y hy => by have := hS y hy; simp only [SPrep, SRow, sEl]; omega)
    (fun j hj => by have := hN j hj; simp only [NPrep, NRow]; omega)
    (fun a k hk => by have := hA a k hk; simp only [APrep, ARow, aEH, aEf]; omega)

/-- The pairs `(u_k, v_k)`, `k < K`, of the arrays `an`, `ad`, below `2^s`. -/
def PairsA (σ : Env d) (an ad K s : ℕ) (u v : ℕ → ℤ) : Prop :=
  ∀ k < K, σ.arr an k = u k ∧ σ.arr ad k = v k ∧ |u k| ≤ 2 ^ s ∧ 0 < v k ∧ v k ≤ 2 ^ s

/-- The pair `(u, v)` of the slots `yn`, `yd`, below `2^s`. -/
def PairS' (σ : Env d) (yn yd s : ℕ) (u v : ℤ) : Prop :=
  σ.sc yn = u ∧ σ.sc yd = v ∧ |u| ≤ 2 ^ s ∧ 0 < v ∧ v ≤ 2 ^ s

set_option maxHeartbeats 32000000 in
/-- **Block A on the machine.** -/
theorem XV.prepA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    (hNN : 65 ≤ L.NN) (hNA : 34 ≤ L.NA) {s : ℕ} {uH vH ug vg uP vP uf vf : ℕ → ℤ} {ul vl : ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hH : PairsA σ aPHn aPHd (d * d) s uH vH) (hg : PairsA σ aPgn aPgd d s ug vg)
    (hP : PairsA σ aPPn aPPd (d * d) s uP vP) (hf : PairsA σ aPfn aPfd d s uf vf)
    (hl : PairS' σ sPl (sPl + 1) s ul vl) (hℓ : s * (d * d + d + 2) + 1 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xprepA L) σ (prepAUnits d s) (fun σ' =>
      (∀ k < d * d, σ'.arr aEH k = ((redN (uH k) (vH k) : ℤ) : ℝ) ∧ σ'.arr 12 k = ((redD (uH k) (vH k) : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEg k = ((redN (ug k) (vg k) : ℤ) : ℝ) ∧ σ'.arr 13 k = ((redD (ug k) (vg k) : ℤ) : ℝ)) ∧
      (∀ k < d * d, σ'.arr aEP k = ((redN (uP k) (vP k) : ℤ) : ℝ) ∧ σ'.arr 14 k = ((redD (uP k) (vP k) : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEf k = ((redN (uf k) (vf k) : ℤ) : ℝ) ∧ σ'.arr 15 k = ((redD (uf k) (vf k) : ℤ) : ℝ)) ∧
      σ'.sc 105 = ((DH d uH vH ug vg ul vl : ℤ) : ℝ) ∧ σ'.sc 106 = ((DPr (d * d) uP vP : ℤ) : ℝ) ∧
      σ'.sc 107 = ((DPr d uf vf : ℤ) : ℝ) ∧ σ'.sc 108 = ((1 : ℤ) : ℝ) ∧ σ'.sc 109 = ((redN ul vl : ℤ) : ℝ) ∧
      σ'.sc 110 = ((redD ul vl : ℤ) : ℝ) ∧ σ'.nat 33 = d * d ∧ σ'.draws = σ.draws ∧
      FrameA SPrep NPrep (fun a _ => APrep a) σ σ') := by
  have hdd : d * d < 2 ^ ℓa := by omega
  have hd0 : d < 2 ^ ℓa := by nlinarith
  have hKd : d * d ≤ asz d := by unfold asz; omega
  have hKd' : d ≤ asz d := by unfold asz; nlinarith
  have hs1 : s + 1 < ℓ := by nlinarith
  have h1l : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  -- what every later state keeps of `σ`
  have keepIn : ∀ σ' : Env d, FrameA SPrep NPrep (fun a _ => APrep a) σ σ' →
      σ'.nat rD = d ∧ σ'.nat rOne = 1 ∧ σ'.sc sZ = 0 ∧
      (∀ y, 64 ≤ y → y ≤ 69 → σ'.sc y = σ.sc y) ∧ (∀ a k, 16 ≤ a → σ'.arr a k = σ.arr a k) :=
    fun σ' G => ⟨by rw [G.1 rD (by pwgo), hD], by rw [G.1 rOne (by pwgo), h1], by rw [G.2.1 sZ (by pwgo), hz],
      fun y a b => G.2.1 y (by pwgo), fun a k h => G.2.2.1 a k (by pwgo)⟩
  -- `33 := d d`, the four units
  refine XV.seq (XV.nmulA hL (i := 33) (a := rD) (b := rD) (by omega) (by rwgo) (by rwgo) hD hD hd0 hd0 hdd)
    fun σ1 ⟨n1, d1, F1⟩ => ?_
  refine XV.seq (XV.constI hL (x := 105) (by omega) 1 h1l) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.constI hL (x := 106) (by omega) 1 h1l) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.constI hL (x := 107) (by omega) 1 h1l) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.constI hL (x := 108) (by omega) 1 h1l) fun σ5 e5 => ?_
  subst e5
  set σ5 := (((σ1.setSc 105 ((1 : ℤ) : ℝ)).setSc 106 ((1 : ℤ) : ℝ)).setSc 107 ((1 : ℤ) : ℝ)).setSc 108
    ((1 : ℤ) : ℝ) with hσ5
  have G5 : FrameA SPrep NPrep (fun a _ => APrep a) σ σ5 :=
    ((((G_mono (fun _ h => by exact h.elim) (fun j h => by omega) (fun _ _ h => by exact h.elim) F1).setSc
      (Or.inr ⟨by norm_num, by norm_num⟩) _).setSc (Or.inr ⟨by norm_num, by norm_num⟩) _).setSc
      (Or.inr ⟨by norm_num, by norm_num⟩) _).setSc (Or.inr ⟨by norm_num, by norm_num⟩) _
  obtain ⟨k5D, k5o, k5z, -, k5a⟩ := keepIn σ5 G5
  have n5 : σ5.nat 33 = d * d := by rw [hσ5]; rwenv; exact n1
  -- the reduction of `H`
  obtain ⟨Hp1, Hp2⟩ := prod_rD_le (K := d * d) (s := s) (u := uH) (v := vH)
    fun k hk => ⟨(hH k hk).2.2.2.1, (hH k hk).2.2.2.2⟩
  refine XV.seq (XV.redArr hL (by omega) (by omega) (an := aPHn) (ad := aPHd) (on := aEH) (dn := 12) (rk := 34) (rn := 33)
    (sP := 105) (K := d * d) (s := s) (S0 := 0) (u := uH) (v := vH) (P0 := 1) (by pwgo) (by pwgo) (by pwgo)
    (by omega) (by decide) (by omega) (by omega) (by omega) (by pwgo) (by omega) (by omega) n5 k5o k5z
    (by rw [hσ5]; rwenv) (fun k hk => by rw [k5a aPHn k (by pwgo), (hH k hk).1])
    (fun k hk => by rw [k5a aPHd k (by pwgo), (hH k hk).2.1]) (fun k hk => (hH k hk).2.2.1)
    (fun k hk => ⟨(hH k hk).2.2.2.1, (hH k hk).2.2.2.2⟩) ⟨one_pos, by simp⟩ hKd (by nlinarith) hdd hs1)
    fun σ6 ⟨R6a, R6p, R6d, R6F⟩ => ?_
  have G6 := G5.trans (G_mono (fun y h => by omega) (fun j h => by omega) (fun a k h => by pwgo) R6F)
  obtain ⟨k6D, k6o, k6z, -, k6a⟩ := keepIn σ6 G6
  -- the reduction of `g`
  obtain ⟨gp1, gp2⟩ := prod_rD_le (K := d) (s := s) (u := ug) (v := vg)
    fun k hk => ⟨(hg k hk).2.2.2.1, (hg k hk).2.2.2.2⟩
  refine XV.seq (XV.redArr hL (by omega) (by omega) (an := aPgn) (ad := aPgd) (on := aEg) (dn := 13) (rk := 34) (rn := rD)
    (sP := 105) (K := d) (s := s) (S0 := s * (d * d)) (u := ug) (v := vg)
    (P0 := 1 * ∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) (by pwgo) (by pwgo) (by pwgo)
    (by omega) (by decide) (by omega) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) k6D k6o k6z R6p
    (fun k hk => by rw [k6a aPgn k (by pwgo), (hg k hk).1])
    (fun k hk => by rw [k6a aPgd k (by pwgo), (hg k hk).2.1]) (fun k hk => (hg k hk).2.2.1)
    (fun k hk => ⟨(hg k hk).2.2.2.1, (hg k hk).2.2.2.2⟩) ⟨by omega, by omega⟩ hKd' (by nlinarith) hd0 hs1)
    fun σ7 ⟨R7a, R7p, R7d, R7F⟩ => ?_
  have G7 := G6.trans (G_mono (fun y h => by omega) (fun j h => by omega) (fun a k h => by pwgo) R7F)
  obtain ⟨k7D, k7o, k7z, k7s, k7a⟩ := keepIn σ7 G7
  -- the reduction of `ℓ`
  obtain ⟨lu, lv, lbu, lv0, lbv⟩ := hl
  refine XV.seq (XV.red hL (z := sZ) (sN := sPl) (sD := sPl + 1) (sa := 98) (sb := 99) (st := 100) (snum := 109)
    (sden := 110) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by decide) (N := ul) (D := vl) (s := s) k7z (by rw [k7s sPl (by pwgo) (by pwgo), lu])
    (by rw [k7s (sPl + 1) (by pwgo) (by pwgo), lv]) lv0 lbu lbv hs1) fun σ8 ⟨r8n, r8d, r8dr, r8F⟩ => ?_
  have G8 := G7.trans (G_mono (fun y h => by omega) (fun j h => by exact h.elim) (fun a k h => by exact h.elim) r8F)
  obtain ⟨lb1, lb2, lb3⟩ := rD_bounds lv0 lbu lbv
  -- `D_H`
  have bHg : |1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) * ∏ k ∈ Finset.range d, redD (ug k) (vg k)| ≤
      2 ^ (s * (d * d) + s * d) := by
    rw [abs_of_pos (by positivity), pow_add, one_mul]; exact mul_le_mul Hp2 gp2 (by omega) (by positivity)
  have b105 : σ8.sc 105 = ((1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) *
      ∏ k ∈ Finset.range d, redD (ug k) (vg k) : ℤ) : ℝ) := by rw [r8F.2.1 105 (by omega), R7p]
  have hDHb : |DH d uH vH ug vg ul vl| ≤ 2 ^ (s * (d * d) + s * d + s) := by
    unfold DH; exact absI_mul_le bHg (by rw [abs_of_pos (by omega)]; exact lb3)
  refine XV.seq (XV.mulI hL (x := 105) (a := 105) (b := 110) (by omega) (by omega) (by omega)
    (u := 1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) * ∏ k ∈ Finset.range d, redD (ug k) (vg k))
    (v := redD ul vl) b105 r8d (absI_le_pow bHg (by nlinarith))
    (absI_le_pow (by rw [abs_of_pos (by omega)]; exact lb3) (by omega)) (absI_le_pow hDHb (by nlinarith)))
    fun σ9 e9 => ?_
  subst e9
  have G9 := G8.setSc (x := 105) (Or.inr ⟨by norm_num, by norm_num⟩)
    ((1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) * (∏ k ∈ Finset.range d, redD (ug k) (vg k)) *
      redD ul vl : ℤ) : ℝ)
  obtain ⟨k9D, k9o, k9z, k9s, k9a⟩ := keepIn _ G9
  have n9 : ∀ j, j ≠ 34 → (σ8.setSc 105 ((1 * (∏ k ∈ Finset.range (d * d), redD (uH k) (vH k)) *
      (∏ k ∈ Finset.range d, redD (ug k) (vg k)) * redD ul vl : ℤ) : ℝ)).nat j = σ5.nat j := fun j hj => by
    rwenv; rw [r8F.1 j not_false, R7F.1 j hj, R6F.1 j hj]
  -- the reduction of `P`
  obtain ⟨Pp1, Pp2⟩ := prod_rD_le (K := d * d) (s := s) (u := uP) (v := vP)
    fun k hk => ⟨(hP k hk).2.2.2.1, (hP k hk).2.2.2.2⟩
  refine XV.seq (XV.redArr hL (by omega) (by omega) (an := aPPn) (ad := aPPd) (on := aEP) (dn := 14) (rk := 34) (rn := 33)
    (sP := 106) (K := d * d) (s := s) (S0 := 0) (u := uP) (v := vP) (P0 := 1) (by pwgo) (by pwgo) (by pwgo)
    (by omega) (by decide) (by omega) (by omega) (by omega) (by pwgo) (by omega) (by omega)
    (by rw [n9 33 (by omega), n5]) k9o k9z
    (by rwenv; rw [r8F.2.1 106 (by omega), R7F.2.1 106 (by omega), R6F.2.1 106 (by omega), hσ5]; rwenv)
    (fun k hk => by rw [k9a aPPn k (by pwgo), (hP k hk).1])
    (fun k hk => by rw [k9a aPPd k (by pwgo), (hP k hk).2.1]) (fun k hk => (hP k hk).2.2.1)
    (fun k hk => ⟨(hP k hk).2.2.2.1, (hP k hk).2.2.2.2⟩) ⟨one_pos, by simp⟩ hKd (by nlinarith) hdd hs1)
    fun σ10 ⟨R10a, R10p, R10d, R10F⟩ => ?_
  have G10 := G9.trans (G_mono (fun y h => by omega) (fun j h => by omega) (fun a k h => by pwgo) R10F)
  obtain ⟨k10D, k10o, k10z, -, k10a⟩ := keepIn σ10 G10
  -- the reduction of `f`
  refine XV.mono (XV.redArr hL (by omega) (by omega) (an := aPfn) (ad := aPfd) (on := aEf) (dn := 15) (rk := 34) (rn := rD)
    (sP := 107) (K := d) (s := s) (S0 := 0) (u := uf) (v := vf) (P0 := 1) (by pwgo) (by pwgo) (by pwgo)
    (by omega) (by decide) (by omega) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) k10D k10o k10z
    (by rw [R10F.2.1 107 (by omega)]; rwenv; rw [r8F.2.1 107 (by omega), R7F.2.1 107 (by omega),
      R6F.2.1 107 (by omega), hσ5]; rwenv)
    (fun k hk => by rw [k10a aPfn k (by pwgo), (hf k hk).1])
    (fun k hk => by rw [k10a aPfd k (by pwgo), (hf k hk).2.1]) (fun k hk => (hf k hk).2.2.1)
    (fun k hk => ⟨(hf k hk).2.2.2.1, (hf k hk).2.2.2.2⟩) ⟨one_pos, by simp⟩ hKd' (by nlinarith) hd0 hs1) le_rfl
    fun σ11 ⟨R11a, R11p, R11d, R11F⟩ => ?_
  have G11 := G10.trans (G_mono (fun y h => by omega) (fun j h => by omega) (fun a k h => by pwgo) R11F)
  -- the cells of the post through the later steps
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ⟨?_, ?_⟩, fun k hk => ⟨?_, ?_⟩, fun k hk => ⟨?_, ?_⟩, ?_, ?_, R11p, ?_,
    ?_, ?_, ?_, ?_, G11⟩
  · rw [R11F.2.2.1 aEH k (by pwgo), R10F.2.2.1 aEH k (by pwgo)]; rwenv
    rw [r8F.2.2.1 aEH k not_false, R7F.2.2.1 aEH k (by pwgo)]; exact (R6a k hk).1
  · rw [R11F.2.2.1 12 k (by pwgo), R10F.2.2.1 12 k (by pwgo)]; rwenv
    rw [r8F.2.2.1 12 k not_false, R7F.2.2.1 12 k (by pwgo)]; exact (R6a k hk).2
  · rw [R11F.2.2.1 aEg k (by pwgo), R10F.2.2.1 aEg k (by pwgo)]; rwenv
    rw [r8F.2.2.1 aEg k not_false]; exact (R7a k hk).1
  · rw [R11F.2.2.1 13 k (by pwgo), R10F.2.2.1 13 k (by pwgo)]; rwenv
    rw [r8F.2.2.1 13 k not_false]; exact (R7a k hk).2
  · rw [R11F.2.2.1 aEP k (by pwgo)]; exact (R10a k hk).1
  · rw [R11F.2.2.1 14 k (by pwgo)]; exact (R10a k hk).2
  · exact (R11a k hk).1
  · exact (R11a k hk).2
  · rw [R11F.2.1 105 (by omega), R10F.2.1 105 (by omega)]; rwenv; rfl
  · rw [R11F.2.1 106 (by omega)]; exact R10p
  · rw [R11F.2.1 108 (by omega), R10F.2.1 108 (by omega)]; rwenv
    rw [r8F.2.1 108 (by omega), R7F.2.1 108 (by omega), R6F.2.1 108 (by omega), hσ5]; rwenv
  · rw [R11F.2.1 109 (by omega), R10F.2.1 109 (by omega)]; rwenv; exact r8n
  · rw [R11F.2.1 110 (by omega), R10F.2.1 110 (by omega)]; rwenv; exact r8d
  · rw [R11F.1 33 (by omega), R10F.1 33 (by omega), n9 33 (by omega), n5]
  · rw [R11d, R10d]; rwenv; rw [r8dr, R7d, R6d, hσ5]; rwenv; exact d1

theorem DPr_bounds {K s : ℕ} {u v : ℕ → ℤ} (bv : ∀ k < K, 0 < v k ∧ v k ≤ 2 ^ s) :
    0 < DPr K u v ∧ DPr K u v ≤ 2 ^ (s * K) := by
  unfold DPr; rw [one_mul]; exact prod_rD_le bv

theorem DH_bounds {s : ℕ} {uH vH ug vg : ℕ → ℤ} {ul vl : ℤ} (bH : ∀ k < d * d, 0 < vH k ∧ vH k ≤ 2 ^ s)
    (bg : ∀ k < d, 0 < vg k ∧ vg k ≤ 2 ^ s) (hv : 0 < vl) (bu : |ul| ≤ 2 ^ s) (bv : vl ≤ 2 ^ s) :
    0 < DH d uH vH ug vg ul vl ∧ DH d uH vH ug vg ul vl ≤ 2 ^ (s * (d * d) + s * d + s) := by
  obtain ⟨p1, p2⟩ := prod_rD_le (u := uH) bH
  obtain ⟨q1, q2⟩ := prod_rD_le (u := ug) bg
  obtain ⟨-, r1, r2⟩ := rD_bounds hv bu bv
  unfold DH; rw [one_mul, pow_add, pow_add]
  exact ⟨mul_pos (mul_pos p1 q1) (by omega),
    mul_le_mul (mul_le_mul p2 q2 q1.le (by positivity)) r2 (by omega) (by positivity)⟩

set_option maxHeartbeats 32000000 in
/-- **Block B on the machine**: `on[k] := nu_k (D / de_k) M` on the four arrays, `80 := n_ℓ (D_H / d_ℓ)`. -/
theorem XV.prepB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    (hNN : 65 ≤ L.NN) (hNA : 34 ≤ L.NA) {s S SP Sf : ℕ} {nH dH ng dg nP dP nf df : ℕ → ℤ}
    {DH0 DP0 Df0 nl dl : ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (h33 : σ.nat 33 = d * d)
    (hH : ∀ k < d * d, σ.arr aEH k = nH k ∧ σ.arr 12 k = dH k)
    (hg : ∀ k < d, σ.arr aEg k = ng k ∧ σ.arr 13 k = dg k)
    (hP : ∀ k < d * d, σ.arr aEP k = nP k ∧ σ.arr 14 k = dP k)
    (hf : ∀ k < d, σ.arr aEf k = nf k ∧ σ.arr 15 k = df k)
    (bH : ∀ k < d * d, |nH k| ≤ 2 ^ s ∧ 1 ≤ dH k ∧ dH k ≤ 2 ^ s)
    (bg : ∀ k < d, |ng k| ≤ 2 ^ s ∧ 1 ≤ dg k ∧ dg k ≤ 2 ^ s)
    (bP : ∀ k < d * d, |nP k| ≤ 2 ^ s ∧ 1 ≤ dP k ∧ dP k ≤ 2 ^ s)
    (bf : ∀ k < d, |nf k| ≤ 2 ^ s ∧ 1 ≤ df k ∧ df k ≤ 2 ^ s)
    (h105 : σ.sc 105 = DH0) (h106 : σ.sc 106 = DP0) (h107 : σ.sc 107 = Df0) (h108 : σ.sc 108 = ((1 : ℤ) : ℝ))
    (h109 : σ.sc 109 = nl) (h110 : σ.sc 110 = dl)
    (bDH : 0 ≤ DH0 ∧ DH0 ≤ 2 ^ S) (bDP : 0 ≤ DP0 ∧ DP0 ≤ 2 ^ SP) (bDf : 0 ≤ Df0 ∧ Df0 ≤ 2 ^ Sf)
    (bl : |nl| ≤ 2 ^ s ∧ 1 ≤ dl ∧ dl ≤ 2 ^ s)
    (hℓ1 : s + S < ℓ) (hℓ2 : s + SP < ℓ) (hℓ3 : s + Sf + SP < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xprepB L) σ (prepBUnits d) (fun σ' =>
      (∀ k < d * d, σ'.arr aEH k = ((nH k * (DH0 / dH k) * 1 : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEg k = ((ng k * (DH0 / dg k) * 1 : ℤ) : ℝ)) ∧
      σ'.sc 80 = ((nl * (DH0 / dl) : ℤ) : ℝ) ∧
      (∀ k < d * d, σ'.arr aEP k = ((nP k * (DP0 / dP k) * 1 : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEf k = ((nf k * (Df0 / df k) * DP0 : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 80 ∨ y = 103 ∨ y = 104 ∨ y = 111) (fun j => j = 34)
        (fun a _ => a = aEH ∨ a = aEg ∨ a = aEP ∨ a = aEf) σ σ') := by
  have hdd : d * d < 2 ^ ℓa := by omega
  have hd0 : d < 2 ^ ℓa := by omega
  have hKd : d * d ≤ asz d := by unfold asz; omega
  have hKd' : d ≤ asz d := by unfold asz; omega
  have b1 : |(1 : ℤ)| ≤ 2 ^ 0 := by simp
  -- `H`
  refine XV.seq (XV.scaleArr hL (by omega) (by omega) (on := aEH) (dn := 12) (rk := 34) (rn := 33) (sD := 105) (sM := 108)
    (K := d * d) (s := s) (S := S) (T := 0) (nu := nH) (de := dH) (D := DH0) (Mu := 1) (by pwgo) (by omega)
    (by pwgo) (by omega) (by omega) (by omega) (by pwgo) (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ h33 h1 h105 h108 (fun k hk => (hH k hk).1) (fun k hk => (hH k hk).2)
    (fun k hk => (bH k hk).1) (fun k hk => (bH k hk).2) bDH b1 hKd (by omega) hdd) fun σ1 ⟨a1, d1, F1⟩ => ?_
  -- `g`
  refine XV.seq (XV.scaleArr hL (by omega) (by omega) (on := aEg) (dn := 13) (rk := 34) (rn := rD) (sD := 105) (sM := 108)
    (K := d) (s := s) (S := S) (T := 0) (nu := ng) (de := dg) (D := DH0) (Mu := 1) (by pwgo) (by omega)
    (by pwgo) (by omega) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by rw [F1.1 rD (by pwgo), hD]) (by rw [F1.1 rOne (by pwgo), h1])
    (by rw [F1.2.1 105 (by omega), h105]) (by rw [F1.2.1 108 (by omega), h108])
    (fun k hk => by rw [F1.2.2.1 aEg k (by pwgo), (hg k hk).1])
    (fun k hk => by rw [F1.2.2.1 13 k (by pwgo), (hg k hk).2])
    (fun k hk => (bg k hk).1) (fun k hk => (bg k hk).2) bDH b1 hKd' (by omega) hd0) fun σ2 ⟨a2, d2, F2⟩ => ?_
  have G2 : FrameA (fun y => y = 80 ∨ y = 103 ∨ y = 104 ∨ y = 111) (fun j => j = 34)
      (fun a _ => a = aEH ∨ a = aEg) σ σ2 :=
    (F1.mono (fun y h => by omega) (fun j h => h) (fun a k h => Or.inl h.1)).trans
      (F2.mono (fun y h => by omega) (fun j h => h) (fun a k h => Or.inr h.1))
  -- `ℓ`
  have q110 : σ2.sc 110 = dl := by rw [G2.2.1 110 (by omega), h110]
  have q105 : σ2.sc 105 = DH0 := by rw [G2.2.1 105 (by omega), h105]
  have sl : s < ℓ := by omega
  have Sl : S < ℓ := by omega
  refine XV.seq (XV.divI hL (x := 111) (a := 105) (b := 110) (by omega) (by omega) (by omega) (u := DH0) (v := dl)
    q105 q110 (absI_le_pow (by rw [abs_of_nonneg bDH.1]; exact bDH.2) Sl)
    (absI_le_pow (by rw [abs_of_pos (by omega)]; exact bl.2.2) sl)) fun σ3 e3 => ?_
  subst e3
  obtain ⟨lb1, lb2, lb3⟩ := scale_bound nl dl DH0 s S bl.1 bl.2.1 bDH.1 bDH.2
  refine XV.seq (XV.mulI hL (x := 80) (a := 109) (b := 111) (by omega) (by omega) (by omega) (u := nl)
    (v := DH0 / dl) (by rwenv; rw [G2.2.1 109 (by omega), h109]) (by rwenv)
    (absI_le_pow bl.1 sl) (absI_le_pow (by rw [abs_of_nonneg lb2]; exact lb3.trans bDH.2) Sl)
    (absI_le_pow lb1 (by omega))) fun σ4 e4 => ?_
  subst e4
  set σ4 := (σ2.setSc 111 ((DH0 / dl : ℤ) : ℝ)).setSc 80 ((nl * (DH0 / dl) : ℤ) : ℝ) with hσ4
  have G4 : FrameA (fun y => y = 80 ∨ y = 103 ∨ y = 104 ∨ y = 111) (fun j => j = 34)
      (fun a _ => a = aEH ∨ a = aEg) σ σ4 := (G2.setSc (Or.inr (Or.inr (Or.inr rfl))) _).setSc (Or.inl rfl) _
  -- `P`
  refine XV.seq (XV.scaleArr hL (by omega) (by omega) (on := aEP) (dn := 14) (rk := 34) (rn := 33) (sD := 106) (sM := 108)
    (K := d * d) (s := s) (S := SP) (T := 0) (nu := nP) (de := dP) (D := DP0) (Mu := 1) (by pwgo) (by omega)
    (by pwgo) (by omega) (by omega) (by omega) (by pwgo) (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by rw [G4.1 33 (by omega), h33]) (by rw [G4.1 rOne (by pwgo), h1])
    (by rw [G4.2.1 106 (by omega), h106]) (by rw [G4.2.1 108 (by omega), h108])
    (fun k hk => by rw [G4.2.2.1 aEP k (by pwgo), (hP k hk).1])
    (fun k hk => by rw [G4.2.2.1 14 k (by pwgo), (hP k hk).2])
    (fun k hk => (bP k hk).1) (fun k hk => (bP k hk).2) bDP b1 hKd (by omega) hdd) fun σ5 ⟨a5, d5, F5⟩ => ?_
  have G5 : FrameA (fun y => y = 80 ∨ y = 103 ∨ y = 104 ∨ y = 111) (fun j => j = 34)
      (fun a _ => a = aEH ∨ a = aEg ∨ a = aEP) σ σ5 :=
    (G4.mono (fun y h => h) (fun j h => h) (fun a k h => h.imp_right Or.inl)).trans
      (F5.mono (fun y h => by omega) (fun j h => h) (fun a k h => Or.inr (Or.inr h.1)))
  -- `f`
  refine XV.mono (XV.scaleArr hL (by omega) (by omega) (on := aEf) (dn := 15) (rk := 34) (rn := rD) (sD := 107) (sM := 106)
    (K := d) (s := s) (S := Sf) (T := SP) (nu := nf) (de := df) (D := Df0) (Mu := DP0) (by pwgo) (by omega)
    (by pwgo) (by omega) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by rw [G5.1 rD (by pwgo), hD]) (by rw [G5.1 rOne (by pwgo), h1])
    (by rw [G5.2.1 107 (by omega), h107]) (by rw [G5.2.1 106 (by omega), h106])
    (fun k hk => by rw [G5.2.2.1 aEf k (by pwgo), (hf k hk).1])
    (fun k hk => by rw [G5.2.2.1 15 k (by pwgo), (hf k hk).2])
    (fun k hk => (bf k hk).1) (fun k hk => (bf k hk).2) bDf (by rw [abs_of_nonneg bDP.1]; exact bDP.2) hKd'
    (by omega) hd0) le_rfl fun σ6 ⟨a6, d6, F6⟩ => ?_
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk => ?_, a6, ?_, ?_⟩
  · rw [F6.2.2.1 aEH k (by pwgo), F5.2.2.1 aEH k (by pwgo), hσ4]; rwenv
    rw [F2.2.2.1 aEH k (by pwgo)]; exact a1 k hk
  · rw [F6.2.2.1 aEg k (by pwgo), F5.2.2.1 aEg k (by pwgo), hσ4]; rwenv; exact a2 k hk
  · rw [F6.2.1 80 (by omega), F5.2.1 80 (by omega), hσ4]; rwenv
  · rw [F6.2.2.1 aEP k (by pwgo)]; exact a5 k hk
  · rw [d6, d5, hσ4]; rwenv; rw [d2, d1]
  · exact (G5.mono (fun y h => h) (fun j h => h) (fun a k h => h.imp_right (Or.imp_right Or.inl))).trans
      (F6.mono (fun y h => by omega) (fun j h => h) (fun a k h => Or.inr (Or.inr (Or.inr h.1))))

set_option maxHeartbeats 32000000 in
/-- **Block C on the machine**: `81 := D_f`, `82 := R_int`, `83 := 1`, the reduced pairs of `r` and of `D_P e`. -/
theorem XV.prepC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    {s Sf : ℕ} {DP0 Df0 ur vr ue ve : ℤ} {Ri : ℕ}
    (hz : σ.sc sZ = 0) (h106 : σ.sc 106 = DP0) (h107 : σ.sc 107 = Df0) (hR : σ.sc sRint = Ri)
    (hr : PairS' σ (sPl + 2) (sPl + 3) s ur vr) (he : PairS' σ (sPl + 4) (sPl + 5) s ue ve)
    (bDP : 0 ≤ DP0 ∧ DP0 ≤ 2 ^ (s * (d * d))) (bDf : 0 ≤ Df0 ∧ Df0 ≤ 2 ^ Sf) (bR : (Ri : ℤ) ≤ 2 ^ s)
    (hℓ1 : Sf < ℓ) (hℓ2 : s * (d * d) + s + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xprepC L) σ (prepCUnits d s) (fun σ' =>
      σ'.sc 81 = ((Df0 : ℤ) : ℝ) ∧ σ'.sc 82 = ((Ri : ℤ) : ℝ) ∧ σ'.sc 83 = ((1 : ℤ) : ℝ) ∧
      σ'.sc 84 = ((redN ur vr : ℤ) : ℝ) ∧ σ'.sc 85 = ((redD ur vr : ℤ) : ℝ) ∧
      σ'.sc 86 = ((redN (DP0 * ue) ve : ℤ) : ℝ) ∧ σ'.sc 87 = ((redD (DP0 * ue) ve : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (81 ≤ y ∧ y ≤ 87) ∨ (98 ≤ y ∧ y ≤ 100) ∨ y = 112) (fun _ => False) (fun _ _ => False)
        σ σ') := by
  obtain ⟨ru, rv, rbu, rv0, rbv⟩ := hr
  obtain ⟨eu, ev, ebu, ev0, ebv⟩ := he
  have sl : s < ℓ := by nlinarith
  have hs1 : s + 1 < ℓ := by nlinarith
  have h0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bDf' : |Df0| < 2 ^ ℓ := absI_le_pow (by rw [abs_of_nonneg bDf.1]; exact bDf.2) hℓ1
  have bR' : |(Ri : ℤ)| < 2 ^ ℓ := absI_le_pow (by rw [abs_of_nonneg (by positivity)]; exact bR) sl
  -- `81 := D_f + 0`, `82 := R_int + 0`, `83 := 1`
  refine XV.seq (XV.addI hL (x := 81) (a := 107) (b := sZ) (by omega) (by omega) (by pwgo) (u := Df0) (v := 0)
    h107 (by rw [hz, Int.cast_zero]) bDf' h0 (by rw [add_zero]; exact bDf')) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := 82) (a := sRint) (b := sZ) (by omega) (by pwgo) (by pwgo) (u := Ri) (v := 0)
    (by rwenv; rw [hR]; exact (Int.cast_natCast Ri).symm) (by rwenv; rw [hz, Int.cast_zero]) bR' h0
    (by rw [add_zero]; exact bR')) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.constI hL (x := 83) (by omega) 1 (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))
    fun σ3 e3 => ?_
  subst e3
  set σ3 := ((σ.setSc 81 ((Df0 + 0 : ℤ) : ℝ)).setSc 82 (((Ri : ℤ) + 0 : ℤ) : ℝ)).setSc 83 ((1 : ℤ) : ℝ) with hσ3
  -- `r`
  refine XV.seq (XV.red hL (z := sZ) (sN := sPl + 2) (sD := sPl + 3) (sa := 98) (sb := 99) (st := 100)
    (snum := 84) (sden := 85) (by pwgo) (by pwgo) (by pwgo) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by decide) (N := ur) (D := vr) (s := s) (by rw [hσ3]; rwenv; exact hz)
    (by rw [hσ3]; rwenv; exact ru) (by rw [hσ3]; rwenv; exact rv) rv0 rbu rbv hs1)
    fun σ4 ⟨r4n, r4d, r4dr, r4F⟩ => ?_
  -- `112 := D_P u_e`
  have bDP' : |DP0| ≤ 2 ^ (s * (d * d)) := by rw [abs_of_nonneg bDP.1]; exact bDP.2
  have bDu : |DP0 * ue| ≤ 2 ^ (s * (d * d) + s) := absI_mul_le bDP' ebu
  refine XV.seq (XV.mulI hL (x := 112) (a := 106) (b := sPl + 4) (by omega) (by omega) (by pwgo) (u := DP0)
    (v := ue) (by rw [r4F.2.1 106 (by omega), hσ3]; rwenv; exact h106)
    (by rw [r4F.2.1 (sPl + 4) (by pwgo), hσ3]; rwenv; exact eu)
    (absI_le_pow bDP' (by omega)) (absI_le_pow ebu sl) (absI_le_pow bDu (by omega))) fun σ5 e5 => ?_
  subst e5
  -- `e`
  refine XV.mono (XV.red hL (z := sZ) (sN := 112) (sD := sPl + 5) (sa := 98) (sb := 99) (st := 100) (snum := 86)
    (sden := 87) (by pwgo) (by omega) (by pwgo) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by decide) (N := DP0 * ue) (D := ve) (s := s * (d * d) + s)
    (by rwenv; rw [r4F.2.1 sZ (by pwgo), hσ3]; rwenv; exact hz) (by rwenv)
    (by rwenv; rw [r4F.2.1 (sPl + 5) (by pwgo), hσ3]; rwenv; exact ev) ev0 bDu
    (ebv.trans (pow_le_pow_right₀ (by norm_num) (by omega))) hℓ2) le_rfl fun σ6 ⟨r6n, r6d, r6dr, r6F⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, r6n, r6d, ?_, ?_⟩
  · (rw [r6F.2.1 81 (by omega)]; rwenv; rw [r4F.2.1 81 (by omega), hσ3]; rwenv) <;> simp
  · (rw [r6F.2.1 82 (by omega)]; rwenv; rw [r4F.2.1 82 (by omega), hσ3]; rwenv) <;> simp
  · rw [r6F.2.1 83 (by omega)]; rwenv; rw [r4F.2.1 83 (by omega), hσ3]; rwenv
  · rw [r6F.2.1 84 (by omega)]; rwenv; exact r4n
  · rw [r6F.2.1 85 (by omega)]; rwenv; exact r4d
  · rw [r6dr]; rwenv; rw [r4dr, hσ3]; rwenv
  · exact ((((((FrameA.refl _ _ _ σ).setSc (by omega) _).setSc (by omega) _).setSc (by omega) _).trans
      (r4F.mono (fun y h => by omega) (fun j h => h) (fun a k h => h))).setSc (by omega) _).trans
      (r6F.mono (fun y h => by omega) (fun j h => h) (fun a k h => h))

set_option maxHeartbeats 32000000 in
/-- **The preparation on the machine**, on the integers of the input pairs. -/
theorem XV.prep {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    (hNN : 65 ≤ L.NN) (hNA : 34 ≤ L.NA) {s : ℕ} {uH vH ug vg uP vP uf vf : ℕ → ℤ} {ul vl ur vr ue ve : ℤ}
    {Ri : ℕ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hR : σ.sc sRint = Ri)
    (bR : (Ri : ℤ) ≤ 2 ^ s)
    (hH : PairsA σ aPHn aPHd (d * d) s uH vH) (hg : PairsA σ aPgn aPgd d s ug vg)
    (hP : PairsA σ aPPn aPPd (d * d) s uP vP) (hf : PairsA σ aPfn aPfd d s uf vf)
    (hl : PairS' σ sPl (sPl + 1) s ul vl) (hr : PairS' σ (sPl + 2) (sPl + 3) s ur vr)
    (he : PairS' σ (sPl + 4) (sPl + 5) s ue ve) (hℓ : s * (d * d + d + 2) + 1 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xprep L) σ (prepUnits d s) (fun σ' =>
      (∀ k < d * d, σ'.arr aEH k =
        ((redN (uH k) (vH k) * (DH d uH vH ug vg ul vl / redD (uH k) (vH k)) * 1 : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEg k =
        ((redN (ug k) (vg k) * (DH d uH vH ug vg ul vl / redD (ug k) (vg k)) * 1 : ℤ) : ℝ)) ∧
      σ'.sc 80 = ((redN ul vl * (DH d uH vH ug vg ul vl / redD ul vl) : ℤ) : ℝ) ∧
      (∀ k < d * d, σ'.arr aEP k =
        ((redN (uP k) (vP k) * (DPr (d * d) uP vP / redD (uP k) (vP k)) * 1 : ℤ) : ℝ)) ∧
      (∀ k < d, σ'.arr aEf k =
        ((redN (uf k) (vf k) * (DPr d uf vf / redD (uf k) (vf k)) * DPr (d * d) uP vP : ℤ) : ℝ)) ∧
      σ'.sc 81 = ((DPr d uf vf : ℤ) : ℝ) ∧ σ'.sc 82 = ((Ri : ℤ) : ℝ) ∧ σ'.sc 83 = ((1 : ℤ) : ℝ) ∧
      σ'.sc 84 = ((redN ur vr : ℤ) : ℝ) ∧ σ'.sc 85 = ((redD ur vr : ℤ) : ℝ) ∧
      σ'.sc 86 = ((redN (DPr (d * d) uP vP * ue) ve : ℤ) : ℝ) ∧
      σ'.sc 87 = ((redD (DPr (d * d) uP vP * ue) ve : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA SPrep NPrep (fun a _ => APrep a) σ σ') := by
  obtain ⟨lu, lv, lbu, lv0, lbv⟩ := hl
  obtain ⟨DH1, DH2⟩ := DH_bounds (uH := uH) (ug := ug) (fun k hk => ⟨(hH k hk).2.2.2.1, (hH k hk).2.2.2.2⟩)
    (fun k hk => ⟨(hg k hk).2.2.2.1, (hg k hk).2.2.2.2⟩) lv0 lbu lbv
  obtain ⟨DP1, DP2⟩ := DPr_bounds (u := uP) fun k hk => ⟨(hP k hk).2.2.2.1, (hP k hk).2.2.2.2⟩
  obtain ⟨Df1, Df2⟩ := DPr_bounds (u := uf) fun k hk => ⟨(hf k hk).2.2.2.1, (hf k hk).2.2.2.2⟩
  refine XV.seq (XV.prepA hL hNS hNN hNA hD h1 hz hH hg hP hf ⟨lu, lv, lbu, lv0, lbv⟩ hℓ hda)
    fun σA ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, Ad, AF⟩ => ?_
  refine XV.seq (XV.prepB hL hNS hNN hNA (s := s) (S := s * (d * d) + s * d + s) (SP := s * (d * d)) (Sf := s * d)
    (nH := fun k => redN (uH k) (vH k)) (dH := fun k => redD (uH k) (vH k))
    (ng := fun k => redN (ug k) (vg k)) (dg := fun k => redD (ug k) (vg k))
    (nP := fun k => redN (uP k) (vP k)) (dP := fun k => redD (uP k) (vP k))
    (nf := fun k => redN (uf k) (vf k)) (df := fun k => redD (uf k) (vf k))
    (by rw [AF.1 rD (by pwgo), hD]) (by rw [AF.1 rOne (by pwgo), h1]) A11 A1 A2 A3 A4
    (fun k hk => rD_bounds (hH k hk).2.2.2.1 (hH k hk).2.2.1 (hH k hk).2.2.2.2)
    (fun k hk => rD_bounds (hg k hk).2.2.2.1 (hg k hk).2.2.1 (hg k hk).2.2.2.2)
    (fun k hk => rD_bounds (hP k hk).2.2.2.1 (hP k hk).2.2.1 (hP k hk).2.2.2.2)
    (fun k hk => rD_bounds (hf k hk).2.2.2.1 (hf k hk).2.2.1 (hf k hk).2.2.2.2)
    A5 A6 A7 A8 A9 A10 ⟨DH1.le, DH2⟩ ⟨DP1.le, DP2⟩ ⟨Df1.le, Df2⟩ (rD_bounds lv0 lbu lbv)
    (by nlinarith) (by nlinarith) (by nlinarith) hda)
    fun σB ⟨B1, B2, B3, B4, B5, Bd, BF⟩ => ?_
  have GB := AF.trans (G_mono (fun y h => by omega) (fun j h => by omega) (fun a k h => by pwgo) BF)
  obtain ⟨ru, rv, rbu, rv0, rbv⟩ := hr
  obtain ⟨eu, ev, ebu, ev0, ebv⟩ := he
  refine XV.mono (XV.prepC hL hNS (s := s) (Sf := s * d) (DP0 := DPr (d * d) uP vP) (Df0 := DPr d uf vf)
    (by rw [GB.2.1 sZ (by pwgo), hz]) (by rw [BF.2.1 106 (by omega), A6])
    (by rw [BF.2.1 107 (by omega), A7]) (by rw [GB.2.1 sRint (by pwgo), hR])
    ⟨by rw [GB.2.1 (sPl + 2) (by pwgo), ru], by rw [GB.2.1 (sPl + 3) (by pwgo), rv], rbu, rv0, rbv⟩
    ⟨by rw [GB.2.1 (sPl + 4) (by pwgo), eu], by rw [GB.2.1 (sPl + 5) (by pwgo), ev], ebu, ev0, ebv⟩
    ⟨DP1.le, DP2⟩ ⟨Df1.le, Df2⟩ bR (by nlinarith) (by nlinarith)) le_rfl
    fun σC ⟨C1, C2, C3, C4, C5, C6, C7, Cd, CF⟩ => ?_
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk => ?_, fun k hk => ?_, C1, C2, C3, C4, C5, C6, C7,
    by rw [Cd, Bd, Ad], GB.trans (G_mono (fun y h => by omega) (fun j h => by exact h.elim) (fun a k h => by exact h.elim) CF)⟩
  · rw [CF.2.2.1 aEH k not_false]; exact B1 k hk
  · rw [CF.2.2.1 aEg k not_false]; exact B2 k hk
  · rw [CF.2.1 80 (by omega)]; exact B3
  · rw [CF.2.2.1 aEP k not_false]; exact B4 k hk
  · rw [CF.2.2.1 aEf k not_false]; exact B5 k hk

/-- The units of the preparation within `1024 (d + s + 1)^3`. -/
theorem prepUnits_le (d s : ℕ) : prepUnits d s ≤ 1024 * (d + s + 1) ^ 3 := by
  simp only [prepUnits, prepAUnits, prepBUnits, prepCUnits, redArrUnits, redCellUnits, scaleArrUnits, redUnits,
    gcdUnits]
  nlinarith [Nat.zero_le (d * d * d), Nat.zero_le (s * s * s), Nat.zero_le (d * d * s), Nat.zero_le (d * s * s),
    Nat.zero_le (d * d), Nat.zero_le (s * s), Nat.zero_le (d * s)]

end AdversarialBco.Bit.Transfer.BLM.PrepM
