/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.Transfer.XBLR2g

@[expose] public section

/-!
# BL's setup on the machine: P3's count and P5's row test

One pass over the input rows `r < m` (R2's cells): row `r` is read from its cells and cleared (`XV.inRow`:
`â_r = a_r Π_r`, `b̂_r D_S = b_r Π_r D_S`), then `s = â_r·â_r`; when `s > 0` (the row is kept), `rMk += 1`,
`u = b̂_r D_S - â_r·μ̂_S`, and the flag `sBadS` is set when `u ≤ 0`. `XV.s3`: `rMk` ends at the count of the rows with
`s > 0`, the flag at `1` iff some such row has `u ≤ 0`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The slot of P5's flag: some kept row has `β̃ ≤ 0`. -/
abbrev sBadS : ℕ := 29

/-- `s = â_r·â_r` of row `r`. -/
def s3S (Nm Dn : ℕ → ℕ → ℤ) (d r : ℕ) : ℤ :=
  (fun j : Fin d => rowA Nm Dn d r j) ⬝ᵥ (fun j : Fin d => rowA Nm Dn d r j)

/-- `u = b̂_r D_S - â_r·μ̂_S` of row `r`. -/
def s3U (Nm Dn : ℕ → ℕ → ℤ) (muS : Fin d → ℤ) (DS : ℤ) (r : ℕ) : ℤ :=
  rowA Nm Dn d r d * DS - (fun j : Fin d => rowA Nm Dn d r j) ⬝ᵥ muS

/-- A kept row: `rMk += 1`, `t = â·μ̂_S`, `u = b̂ D_S - t`, the flag set when `u ≤ 0`. -/
def xS3upd (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rMk rMk rOne))) (.seq (xdot L sZ sTa tR aRw aMuS rr rk rD rOne)
  (.seq (toX (VL.sop2 L .sub sGD sRB sTa)) (xifS L sZ sGD .skip (toX (VL.sconst L sBadS 1)))))

/-- One input row. -/
def xS3row (L : Layout) : XCmd :=
  .seq (xinRow L sRD sRT sRN sRQ sRB sDS aRw rI rTT rjj rD rD1 rK rOne)
  (.seq (xdot L sZ sGN tR aRw aRw rr rk rD rOne) (xifS L sZ sGN (xS3upd L) .skip))

/-- P3 and P5's test: `rD1 := d + 1`, then the rows. -/
def xS3 (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rD1 rD rOne))) (xforN rK rM rOne (xS3row L))

/-- The units of one row and of `xS3`. -/
def s3rowUnits (d : ℕ) : ℕ := (18 * d + 28) + ((d * 10 + 5) + ((1 + ((d * 10 + 5) + (1 + 3))) + 2))
def s3Units (d m : ℕ) : ℕ := 1 + (m * (s3rowUnits d + 3) + 3)

/-- The cells the rows change. -/
def S3 (y : ℕ) : Prop := y = sBadS ∨ (sGN ≤ y ∧ y ≤ sRQ) ∨ tR ≤ y
def N3 (j : ℕ) : Prop := j = rMk ∨ (rD1 ≤ j ∧ j ≤ rk)
def N3r (j : ℕ) : Prop := j = rMk ∨ (rI ≤ j ∧ j ≤ rk)
def A3 (a _k : ℕ) : Prop := a = aRw

/-- `omega` after unfolding the cell names (BL's, R2's, the rows'). -/
macro "somega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, sZ, sDS, aMuS, aRw, rD1, rK, rI, rTT, rjj,
  rr, rk, sGN, sGD, sTa, sRB, sRD, sRT, sRN, sRQ, tR, sBadS, oE, rEE, aWE, S3, N3, N3r, A3, ne_eq, not_or, not_and,
  not_not]) <;> omega))

theorem s3_inc_a : ∀ y, (y = sRD ∨ y = sRT ∨ y = sRN ∨ y = sRQ ∨ y = sRB) → S3 y := by
  intro y h; simp only [S3, sRD, sRT, sRN, sRQ, sRB, sBadS, sGN, tR] at *; omega
theorem s3_inc_an : ∀ j, (j = rI ∨ j = rTT ∨ j = rjj) → N3r j := by
  intro j h; simp only [N3r, rI, rTT, rjj, rMk, rk] at *; omega
theorem s3_inc_d : ∀ y, (y = sGN ∨ tR ≤ y) → S3 y := by
  intro y h; simp only [S3, sRQ, sBadS, sGN, tR] at *; omega
theorem s3_inc_t : ∀ y, (y = sTa ∨ tR ≤ y) → S3 y := by
  intro y h; simp only [S3, sRQ, sBadS, sGN, sTa, tR] at *; omega
theorem s3_inc_dn : ∀ j, (j = rk ∨ j = rr) → N3r j := by
  intro j h; simp only [N3r, rI, rr, rMk, rk] at *; omega
theorem s3_inc_rn : ∀ j, N3r j → N3 j := by
  intro j h; simp only [N3r, N3, rI, rD1, rMk, rk] at *; omega

set_option maxHeartbeats 4000000 in
/-- **One input row of P3 and P5.** -/
theorem XV.s3row {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E m r : ℕ} {Nm Dn : ℕ → ℕ → ℤ} {Mh DS : ℤ} {muS : Fin d → ℤ} (hr : r < m)
    (hD : σ.nat rD = d) (hD1 : σ.nat rD1 = d + 1) (hK : σ.nat rK = r) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hDS : σ.sc sDS = DS) (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k) (hmk : σ.nat rMk ≤ r)
    (hoff : 3 + 2 * ((d + 1) * m) ≤ X.off) (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa)
    (hinpN : ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * r + j)) = Nm r j)
    (hinpD : ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * r + j)) = Dn r j)
    (hM1 : 1 ≤ Mh) (hNm : ∀ j ≤ d, |Nm r j| ≤ Mh) (hDn : ∀ j ≤ d, 1 ≤ Dn r j ∧ Dn r j ≤ Mh)
    (hME : Mh ≤ 2 ^ E) (hDS1 : 1 ≤ DS) (bDS : DS ≤ 2 ^ E) (bmu : ∀ k, |muS k| ≤ 2 ^ E)
    (hdE : d ≤ 2 ^ E) (hℓ : 3 * (E * d) + 10 * E + 5 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xS3row L) σ (s3rowUnits d) (fun σ' =>
      σ'.nat rMk = σ.nat rMk + (if 0 < s3S Nm Dn d r then 1 else 0) ∧
      σ'.sc sBadS = (if 0 < s3S Nm Dn d r ∧ s3U Nm Dn muS DS r ≤ 0 then 1 else σ.sc sBadS) ∧
      σ'.draws = σ.draws ∧ FrameA S3 N3r A3 σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by somega)
  have hmA : m < 2 ^ ℓa := by
    have : m ≤ 4 + 2 * ((d + 1) * m) := by nlinarith
    omega
  have hdℓ : (d : ℤ) ≤ 2 ^ E := by exact_mod_cast hdE
  have hdm : ∀ a : ℕ, (d : ℤ) * 2 ^ a ≤ 2 ^ (E + a) := fun a => by
    rw [pow_add]; exact mul_le_mul_of_nonneg_right hdℓ (by positivity)
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  have hMp : Mh ^ (d + 2) ≤ 2 ^ (E * d + 2 * E) := by
    rw [show E * d + 2 * E = E * (d + 2) by ring, pow_mul]; exact pow_le_pow_left₀ (by omega) hME _
  have bA : ∀ j ≤ d, |rowA Nm Dn d r j| ≤ 2 ^ (E * d + 2 * E) := fun j hj => (rowA_abs hM1 hNm hDn hj).trans hMp
  set av : Fin d → ℤ := fun j => rowA Nm Dn d r j with hav
  have bav : ∀ k, |av k| ≤ 2 ^ (E * d + 2 * E) := fun k => bA k k.2.le
  have bmu' : ∀ k, |muS k| ≤ 2 ^ (E * d + 2 * E) := fun k => (bmu k).trans (pow_mono_z (by omega))
  set gS := s3S Nm Dn d r with hgS
  set ta := av ⬝ᵥ muS with hta
  set gU := s3U Nm Dn muS DS r with hgU
  have bgS : |gS| ≤ 2 ^ (2 * (E * d) + 5 * E) :=
    (dot_abs_le bav bav hdE).trans (pow_mono_z (by omega))
  have bta : |ta| ≤ 2 ^ (E * d + 4 * E) := (dot_abs_le bav bmu hdE).trans (pow_mono_z (by omega))
  have bsB : |rowA Nm Dn d r d * DS| ≤ 2 ^ (E * d + 3 * E) := by
    rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < DS)]
    calc |rowA Nm Dn d r d| * DS ≤ 2 ^ (E * d + 2 * E) * 2 ^ E :=
          mul_le_mul (bA d le_rfl) bDS (by omega) (by positivity)
      _ = 2 ^ (E * d + 3 * E) := by ring
  have bgU : |gU| ≤ 2 ^ (E * d + 4 * E + 1) := by
    rw [hgU, s3U]
    refine (abs_sub _ _).trans ?_
    have := bsB.trans (pow_mono_z (show E * d + 3 * E ≤ E * d + 4 * E by omega))
    rw [pow_succ]; linarith
  have hdot : d * 2 ^ (2 * (E * d + 2 * E)) < 2 ^ ℓ := by
    have h := lt_of_le_of_lt (hdm (2 * (E * d + 2 * E))) (hℓ2 (a := E + 2 * (E * d + 2 * E)) (by omega))
    exact_mod_cast h
  -- step 1: row `r`
  refine XV.seq (XV.inRow hL (sD := sRD) (sT := sRT) (sN := sRN) (sQ := sRQ) (sB := sRB) (sDn := sDS)
    (aRow := aRw) (nI := rI) (nT := rTT) (nj := rjj) (nd := rD) (nd1 := rD1) (nk := rK) (none := rOne) (k := r)
    (Mh := Mh) (D := DS) (Nm := Nm r) (Dn := Dn r) (by somega) (by somega) (by somega) (by somega) (by somega)
    (by somega) (by decide) (by somega) (by somega) (by somega) (by somega) (by somega) (by somega) (by somega)
    (by somega) (by decide) hD hD1 hK h1 hDS (by nlinarith) (by nlinarith) (by unfold asz at hda; omega) hinpN
    hinpD hDS1 hM1 hNm hDn ?_) fun σa ⟨ra, rb, da, Fa⟩ => ?_
  · calc Mh ^ (d + 2) * DS ≤ 2 ^ (E * d + 2 * E) * 2 ^ E := mul_le_mul hMp bDS (by omega) (by positivity)
      _ = 2 ^ (E * d + 3 * E) := by ring
      _ < 2 ^ ℓ := hℓ2 (by omega)
  have ra' : ∀ k : Fin d, σa.arr aRw k = av k := fun k => by rw [ra k k.2]; rfl
  have rb' : σa.sc sRB = ((rowA Nm Dn d r d * DS : ℤ) : ℝ) := by rw [rb]; rfl
  have sa : ∀ y, y ≠ sRD → y ≠ sRT → y ≠ sRN → y ≠ sRQ → y ≠ sRB → σa.sc y = σ.sc y := fun y h1 h2 h3 h4 h5 =>
    Fa.2.1 y (by tauto)
  have na : ∀ j, j ≠ rI → j ≠ rTT → j ≠ rjj → σa.nat j = σ.nat j := fun j h1 h2 h3 => Fa.1 j (by tauto)
  have aa : ∀ b k, b ≠ aRw → σa.arr b k = σ.arr b k := fun b k h => Fa.2.2.1 b k fun h' => h h'.1
  -- step 2: `s = â·â`
  refine XV.seq (XV.dot (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σa) (E := E * d + 2 * E) (x := av) (y := av) hL
    (z := sZ) (r := sGN) (t := tR) (ax := aRw) (ay := aRw) (nr := rr) (nk := rk) (nd := rD) (none := rOne)
    (by somega) (by somega) (by somega) (by somega) (by rw [sa _ (by somega) (by somega) (by somega) (by somega)
    (by somega), hz]) (by somega) (by somega) (by somega) (by somega) (by somega) (by somega) (by decide)
    (by rw [na _ (by somega) (by somega) (by somega), hD]) (by rw [na _ (by somega) (by somega) (by somega), h1])
    ra' ra' bav bav (by omega) hdot) fun σb ⟨sb, db, Fb⟩ => ?_
  have sb' : ∀ y, y ≠ sGN → y < tR → σb.sc y = σa.sc y := fun y h h' => Fb.2.1 y (by omega)
  have nb : ∀ j, j ≠ rk → j ≠ rr → σb.nat j = σa.nat j := fun j h h' => Fb.1 j (by tauto)
  have ab' : ∀ b k, σb.arr b k = σa.arr b k := fun b k => Fb.2.2.1 b k id
  have zb : σb.sc sZ = 0 := by
    rw [sb' _ (by somega) (by somega), sa _ (by somega) (by somega) (by somega) (by somega) (by somega), hz]
  have gSb : σb.sc sGN = (gS : ℝ) := sb
  have hgSl : |(gS : ℝ)| < 2 ^ ℓ := by
    have := bgS.trans_lt (hℓ2 (a := 2 * (E * d) + 5 * E) (by omega)); exact_mod_cast this
  have mkb : σb.nat rMk = σ.nat rMk := by
    rw [nb _ (by somega) (by somega), na _ (by somega) (by somega) (by somega)]
  have bdb : σb.sc sBadS = σ.sc sBadS := by
    rw [sb' _ (by somega) (by somega), sa _ (by somega) (by somega) (by somega) (by somega) (by somega)]
  have Gb : FrameA S3 N3r A3 σ σb :=
    (Fa.mono s3_inc_a s3_inc_an (fun b c h => h.1)).trans
      (Fb.mono s3_inc_d s3_inc_dn (fun b c h => h.elim))
  -- step 3: the test `s > 0`
  refine XV.mono (XV.ifS_skip (X := X) (K := 1 + ((d * 10 + 5) + (1 + 3))) hL (x := sZ) (y := sGN) (c := xS3upd L)
    (by somega) (by somega) (by rw [zb]; simp) (by rw [gSb]; exact hgSl) (fun hlt => ?_) (fun hlt => ?_))
    le_rfl fun _ h => h
  · -- a kept row
    rw [zb, gSb] at hlt
    have hpos : 0 < gS := by exact_mod_cast hlt
    have h1b : σb.nat rOne = 1 := by
      rw [nb _ (by somega) (by somega), na _ (by somega) (by somega) (by somega), h1]
    have hmkb : σb.nat rMk < 2 ^ ℓa := by rw [mkb]; omega
    have h1b' : σb.nat rOne < 2 ^ ℓa := by rw [h1b]; have := hL.1; omega
    refine XV.seq (XV.nadd hL (i := rMk) (a := rMk) (b := rOne) (by somega) (by somega) (by somega) hmkb h1b')
      fun σc ec => ?_
    subst ec
    refine XV.seq (XV.dot (X := X) (ℓa := ℓa) (ℓ := ℓ) (E := E * d + 2 * E) (x := av) (y := muS) hL
      (z := sZ) (r := sTa) (t := tR) (ax := aRw) (ay := aMuS) (nr := rr) (nk := rk) (nd := rD) (none := rOne)
      (by somega) (by somega) (by somega) (by somega) (by rw [Env.setNat_sc, zb]) (by somega) (by somega)
      (by somega) (by somega) (by somega) (by somega) (by decide)
      (by rw [Env.setNat_nat, if_neg (by somega), nb _ (by somega) (by somega),
        na _ (by somega) (by somega) (by somega), hD])
      (by rw [Env.setNat_nat, if_neg (by somega), nb _ (by somega) (by somega),
        na _ (by somega) (by somega) (by somega), h1])
      (fun k => by rw [Env.setNat_arr, ab', ra' k])
      (fun k => by rw [Env.setNat_arr, ab', aa _ _ (by somega), hmu k]) bav bmu' (by omega) hdot)
      fun σd ⟨sd, dd, Fd⟩ => ?_
    have sd' : ∀ y, y ≠ sTa → y < tR → σd.sc y = σb.sc y := fun y h h' => by
      rw [Fd.2.1 y (by omega), Env.setNat_sc]
    have rbd : σd.sc sRB = ((rowA Nm Dn d r d * DS : ℤ) : ℝ) := by
      rw [sd' _ (by somega) (by somega), sb' _ (by somega) (by somega), rb']
    have hUl : |((rowA Nm Dn d r d * DS : ℤ) : ℝ) - ((ta : ℤ) : ℝ)| < 2 ^ ℓ := by
      have := bgU.trans_lt (hℓ2 (a := E * d + 4 * E + 1) (by omega))
      rw [hgU, s3U] at this
      exact_mod_cast this
    have hBl : |((rowA Nm Dn d r d * DS : ℤ) : ℝ)| < 2 ^ ℓ := by
      have := bsB.trans_lt (hℓ2 (a := E * d + 3 * E) (by omega)); exact_mod_cast this
    have hTl : |((ta : ℤ) : ℝ)| < 2 ^ ℓ := by
      have := bta.trans_lt (hℓ2 (a := E * d + 4 * E) (by omega)); exact_mod_cast this
    refine XV.seq (XV.sop2 hL (x := sGD) (a := sRB) (b := sTa) (by somega) (by somega) (by somega) .sub
      (by intro h; cases h) (by rw [rbd]; exact hBl) (by rw [sd]; exact hTl)
      (by simp only [RealRAM.Op2.eval, rbd, sd]; exact hUl)) fun σe ee => ?_
    subst ee
    have ue : (σd.setSc sGD (RealRAM.Op2.eval .sub (σd.sc sRB) (σd.sc sTa))).sc sGD = (gU : ℝ) := by
      rw [Env.setSc_sc, if_pos rfl]
      simp only [RealRAM.Op2.eval, rbd, sd, hgU, s3U]; push_cast; rfl
    have ze : (σd.setSc sGD (RealRAM.Op2.eval .sub (σd.sc sRB) (σd.sc sTa))).sc sZ = 0 := by
      rw [Env.setSc_sc, if_neg (by somega), sd' _ (by somega) (by somega), zb]
    have hUl' : |(gU : ℝ)| < 2 ^ ℓ := by
      have := bgU.trans_lt (hℓ2 (a := E * d + 4 * E + 1) (by omega)); exact_mod_cast this
    have Gd : FrameA S3 N3r A3 σ σd :=
      (Gb.setNat (i := rMk) (Or.inl rfl) _).trans
        (Fd.mono s3_inc_t s3_inc_dn (fun b c h => h.elim))
    have mkd : σd.nat rMk = σ.nat rMk + 1 := by
      rw [Fd.1 _ (by somega), Env.setNat_nat, if_pos rfl, mkb, h1b]
    have bdd : σd.sc sBadS = σ.sc sBadS := by rw [sd' _ (by somega) (by somega), bdb]
    by_cases hu : σd.sc sZ < (gU : ℝ)
    · refine XV.mono (XV.ifS_t hL (by somega) (by somega) (by rw [ze]; simp) (by rw [ue]; exact hUl')
        (by rw [ze, ue]; rw [sd' _ (by somega) (by somega), zb] at hu; exact hu) (XV.skip _)) (by omega)
        fun σ' e => ?_
      subst e
      have hu' : 0 < gU := by rw [sd' _ (by somega) (by somega), zb] at hu; exact_mod_cast hu
      refine ⟨by rw [Env.setSc_nat, mkd, if_pos hpos], ?_, by rw [Env.setSc_draws, dd, Env.setNat_draws, db, da],
        Gd.setSc (Or.inr (Or.inl ⟨by somega, by somega⟩)) _⟩
      rw [Env.setSc_sc, if_neg (by somega), bdd, if_neg (by omega)]
    · have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
        rw [Rat.cast_one, abs_one]; exact_mod_cast Nat.one_lt_two_pow (by omega : ℓ ≠ 0)
      refine XV.mono (XV.ifS_f hL (by somega) (by somega) (by rw [ze]; simp) (by rw [ue]; exact hUl')
        (by rw [ze, ue]; rw [sd' _ (by somega) (by somega), zb] at hu; exact hu)
        (XV.sconst hL (x := sBadS) (by somega) 1 rfl h1l)) (by omega) fun σ' e => ?_
      subst e
      have hu' : gU ≤ 0 := by
        rw [sd' _ (by somega) (by somega), zb] at hu; push_neg at hu; exact_mod_cast hu
      refine ⟨by rw [Env.setSc_nat, Env.setSc_nat, mkd, if_pos hpos], ?_,
        by rw [Env.setSc_draws, Env.setSc_draws, dd, Env.setNat_draws, db, da],
        (Gd.setSc (Or.inr (Or.inl ⟨by somega, by somega⟩)) _).setSc (Or.inl rfl) _⟩
      rw [Env.setSc_sc, if_pos rfl, if_pos ⟨hpos, hu'⟩]; simp
  · -- a dropped row
    rw [zb, gSb] at hlt
    have hpos : ¬ 0 < gS := by exact_mod_cast hlt
    refine ⟨by rw [mkb, if_neg hpos, add_zero], by rw [bdb, if_neg (fun h => hpos h.1)], by rw [db, da], Gb⟩

/-! ## The rows -/

/-- The count of the rows `k < r` with `s > 0`. -/
def s3cnt (Nm Dn : ℕ → ℕ → ℤ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => s3cnt Nm Dn d r + if 0 < s3S Nm Dn d r then 1 else 0

theorem s3cnt_le (Nm Dn : ℕ → ℕ → ℤ) (d : ℕ) : ∀ r, s3cnt Nm Dn d r ≤ r
  | 0 => le_rfl
  | r + 1 => by
    have := s3cnt_le Nm Dn d r
    simp only [s3cnt]; split_ifs <;> omega

/-- Some row `k < r` has `s > 0` and `u ≤ 0`. -/
def s3bad (Nm Dn : ℕ → ℕ → ℤ) (muS : Fin d → ℤ) (DS : ℤ) (r : ℕ) : Prop :=
  ∃ k < r, 0 < s3S Nm Dn d k ∧ s3U Nm Dn muS DS k ≤ 0

theorem s3bad_succ (Nm Dn : ℕ → ℕ → ℤ) (muS : Fin d → ℤ) (DS : ℤ) (r : ℕ) :
    s3bad Nm Dn muS DS (r + 1) ↔ s3bad Nm Dn muS DS r ∨ (0 < s3S Nm Dn d r ∧ s3U Nm Dn muS DS r ≤ 0) := by
  constructor
  · rintro ⟨k, hk, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr h
  · rintro (⟨k, hk, h⟩ | h)
    · exact ⟨k, by omega, h⟩
    · exact ⟨r, by omega, h⟩

set_option maxHeartbeats 4000000 in
/-- **P3's count and P5's row test on the machine.** -/
theorem XV.s3 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E m : ℕ} {Nm Dn : ℕ → ℕ → ℤ} {Mh DS : ℤ} {muS : Fin d → ℤ}
    (hD : σ.nat rD = d) (hM : σ.nat rM = m) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hDS : σ.sc sDS = DS) (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k) (hk0 : σ.nat rMk = 0)
    (hb0 : σ.sc sBadS = 0)
    (hoff : 3 + 2 * ((d + 1) * m) ≤ X.off) (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa)
    (hinpN : ∀ r < m, ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * r + j)) = Nm r j)
    (hinpD : ∀ r < m, ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * r + j)) = Dn r j)
    (hM1 : 1 ≤ Mh) (hNm : ∀ r < m, ∀ j ≤ d, |Nm r j| ≤ Mh) (hDn : ∀ r < m, ∀ j ≤ d, 1 ≤ Dn r j ∧ Dn r j ≤ Mh)
    (hME : Mh ≤ 2 ^ E) (hDS1 : 1 ≤ DS) (bDS : DS ≤ 2 ^ E) (bmu : ∀ k, |muS k| ≤ 2 ^ E)
    (hdE : d ≤ 2 ^ E) (hℓ : 3 * (E * d) + 10 * E + 5 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xS3 L) σ (s3Units d m) (fun σ' =>
      σ'.nat rMk = s3cnt Nm Dn d m ∧
      (σ'.sc sBadS = 1 ∧ s3bad Nm Dn muS DS m ∨ σ'.sc sBadS = 0 ∧ ¬ s3bad Nm Dn muS DS m) ∧
      σ'.draws = σ.draws ∧ FrameA S3 N3 A3 σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by somega)
  have hmA : m < 2 ^ ℓa := by
    have : m ≤ 4 + 2 * ((d + 1) * m) := by nlinarith
    omega
  refine XV.seq (XV.nadd hL (i := rD1) (a := rD) (b := rOne) (by somega) (by somega) (by somega)
    (by rw [hD]; unfold asz at hda; nlinarith) (by rw [h1]; omega)) fun σ0 e0 => ?_
  subst e0
  let J : ℕ → Env d → Prop := fun r σ' =>
    σ'.nat rMk = s3cnt Nm Dn d r ∧
    (σ'.sc sBadS = 1 ∧ s3bad Nm Dn muS DS r ∨ σ'.sc sBadS = 0 ∧ ¬ s3bad Nm Dn muS DS r) ∧
    σ'.nat rD1 = d + 1 ∧ σ'.draws = σ.draws ∧ FrameA S3 N3 A3 σ σ'
  refine XV.mono (XV.forN hL (i := rK) (n := rM) (one := rOne) (body := xS3row L) (by somega) (by somega)
    (by somega) (by somega) (by somega) m _ hmA J (σ.setNat rD1 (σ.nat rD + σ.nat rOne))
    (by simp [hM]) (by simp [h1])
    ⟨by simp [hk0, s3cnt], Or.inr ⟨by simp [hb0], fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k)⟩,
      by simp [hD, h1], by simp,
      ((FrameA.refl _ _ _ σ).setNat (i := rD1) (Or.inr ⟨le_rfl, by somega⟩) _).setNat (i := rK)
        (Or.inr ⟨by somega, by somega⟩) 0⟩ ?_) le_rfl fun σ' ⟨⟨h1', h2', _, h4', h5'⟩, _⟩ => ⟨h1', h2', h4', h5'⟩
  intro r hr σ' ⟨hk, hb, hd1, hdr, F'⟩ hrk hrm hr1
  have nn : ∀ j, ¬ N3 j → σ'.nat j = σ.nat j := F'.1
  have ss : ∀ y, ¬ S3 y → σ'.sc y = σ.sc y := F'.2.1
  have aa : ∀ b k, b ≠ aRw → σ'.arr b k = σ.arr b k := fun b k h => F'.2.2.1 b k h
  refine XV.mono (XV.s3row hL hlay (σ := σ') (E := E) (m := m) (r := r) (Nm := Nm) (Dn := Dn) (Mh := Mh)
    (DS := DS) (muS := muS) hr (by rw [nn _ (by somega), hD]) hd1 hrk hr1 (by rw [ss _ (by somega), hz])
    (by rw [ss _ (by somega), hDS]) (fun k => by rw [aa _ _ (by somega), hmu k])
    (by rw [hk]; exact s3cnt_le Nm Dn d r) hoff hma (hinpN r hr) (hinpD r hr) hM1 (hNm r hr) (hDn r hr) hME hDS1
    bDS bmu hdE hℓ) le_rfl fun σ'' ⟨p1, p2, p3, F''⟩ => ?_
  have F3 := F'.trans (F''.mono (fun y h => h) s3_inc_rn (fun _ _ h => h))
  refine ⟨by rw [F''.1 rK (by somega), hrk], by rw [F''.1 rM (by somega), hrm], by rw [F''.1 rOne (by somega), hr1],
    ?_, ?_, ?_, ?_, F3.setNat (i := rK) (Or.inr ⟨by somega, by somega⟩) _⟩
  · rw [Env.setNat_nat, if_neg (by somega), p1, hk]; rfl
  · rw [Env.setNat_sc, p2, s3bad_succ]
    by_cases hc : 0 < s3S Nm Dn d r ∧ s3U Nm Dn muS DS r ≤ 0
    · exact Or.inl ⟨if_pos hc, Or.inr hc⟩
    · rw [if_neg hc]
      rcases hb with ⟨e, hb'⟩ | ⟨e, hb'⟩
      · exact Or.inl ⟨e, Or.inl hb'⟩
      · exact Or.inr ⟨e, fun h => h.elim hb' hc⟩
  · rw [Env.setNat_nat, if_neg (by somega), F''.1 rD1 (by somega), hd1]
  · rw [Env.setNat_draws, p3, hdr]

end AdversarialBco.Bit.Transfer.BLM
