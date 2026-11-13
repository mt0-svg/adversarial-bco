/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2g

@[expose] public section

/-!
# BL's round on the machine, R2 PLAYPT in mode `run`, the scale and the play

From the gauge pair `(b_N, b_D)` (`b_D > 0`), `ε̂ = ε' 2^pF` and `F = 2^pF`: `pt' = max(1, π/(1 - ε'))` is
`pt_N/pt_D` with `(pt_N, pt_D) = (b_N F, b_D (F - ε̂))` when `b_D (F - ε̂) < b_N F`, else `(1, 1)` (slots `sPtN`,
`sPtD`); then the play buffer `aPl` in the form of the play leaf: `D_S D_X pt_N` in cell `0` and
`μ̂_{S,k} D_X pt_N + y_k pt_D` in cell `1 + k` (`y = Â_S X̂`), so that the play is `μ_S + A_S (X'/pt')`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The integers -/

/-- The scale `(pt_N, pt_D)`. -/
def ptPair (bN bD F eh : ℤ) : ℤ × ℤ := if bD * (F - eh) < bN * F then (bN * F, bD * (F - eh)) else (1, 1)

/-! ## The code -/

/-- `b_D (F - ε̂)`. -/
def ieC1 : IE := .op .mul (.sc sBD) (.op .sub (.sc s2pF) (.sc sEps))

/-- `b_N F`. -/
def ieC2 : IE := .op .mul (.sc sBN) (.sc s2pF)

/-- `D_S D_X pt_N`. -/
def ieP0 : IE := .op .mul (.op .mul (.sc sDS) (.sc sDX)) (.sc sPtN)

/-- `μ̂_{S,k} D_X pt_N + y_k pt_D`, `k` in the register `rk`. -/
def iePj : IE := .op .add (.op .mul (.op .mul (.arr aMuS rk) (.sc sDX)) (.sc sPtN)) (.op .mul (.arr aYv rk) (.sc sPtD))

theorem ieC1_facts : ieC1.units = 5 ∧ ieC1.scr = 4 ∧ topL ieC1 = (2, 1) := ⟨rfl, rfl, by simp [ieC1, topL, magL]⟩
theorem ieC2_facts : ieC2.units = 3 ∧ ieC2.scr = 2 ∧ topL ieC2 = (2, 0) := ⟨rfl, rfl, by simp [ieC2, topL, magL]⟩
theorem ieP0_facts : ieP0.units = 5 ∧ ieP0.scr = 4 ∧ topL ieP0 = (3, 0) := ⟨rfl, rfl, by simp [ieP0, topL, magL]⟩
theorem iePj_facts : iePj.units = 11 ∧ iePj.scr = 8 ∧ topL iePj = (3, 1) := ⟨rfl, rfl, by simp [iePj, topL, magL]⟩

/-- R2, the scale and the play buffer. -/
def xR2p (L : Layout) : XCmd :=
  .seq (ieC1.code L sZ sC1 tR)
  (.seq (ieC2.code L sZ sC2 tR)
  (.seq (xifS L sC1 sC2 (.seq (toX (VL.sop2 L .add sPtN sC2 sZ)) (toX (VL.sop2 L .add sPtD sC1 sZ)))
    (.seq (toX (VL.sconst L sPtN 1)) (toX (VL.sconst L sPtD 1))))
  (.seq (ieP0.code L sZ sC1 tR)
  (.seq (.prim (.frag (.nconst rr 0)))
  (.seq (toX (VL.aset L aPl rr sC1))
  (.seq (.prim (.frag (.nconst rr 1)))
    (xmapE L sZ tR iePj aPl rr rOne rk rD rOne)))))))

/-- The units of `xR2p`. -/
def r2pUnits (d : ℕ) : ℕ := 5 + (3 + (4 + (5 + (1 + (2 + (1 + (d * (11 + 6) + 3)))))))

/-- The cells of the scale and the play. -/
def SP (y : ℕ) : Prop := y = sPtN ∨ y = sPtD ∨ y = sC1 ∨ y = sC2 ∨ tR ≤ y
def NP (j : ℕ) : Prop := j = rr ∨ j = rk
def AP (a _k : ℕ) : Prop := a = aPl

/-- `qomega` with the cell sets of the scale and the play. -/
macro "pomega" : tactic => `(tactic| ((try simp only [SP, NP, AP]) <;> qomega))

theorem incSP_c1 : ∀ y, (y = sC1 ∨ tR ≤ y) → SP y := by intro y h; simp only [SP] at *; omega
theorem incSP_c2 : ∀ y, (y = sC2 ∨ tR ≤ y) → SP y := by intro y h; simp only [SP] at *; omega
theorem incSP_t : ∀ y, tR ≤ y → SP y := by intro y h; simp only [SP] at *; omega
theorem incNP_k : ∀ j, (j = rk ∨ j = rr) → NP j := by intro j h; simp only [NP] at *; omega

theorem ptPair_pos {bN bD F eh : ℤ} (hbD : 0 < bD) (he : eh < F) :
    0 < (ptPair bN bD F eh).1 ∧ 0 < (ptPair bN bD F eh).2 := by
  unfold ptPair
  split_ifs with h
  · have : 0 < bD * (F - eh) := mul_pos hbD (by omega)
    exact ⟨by linarith, this⟩
  · exact ⟨one_pos, one_pos⟩

theorem ptPair_abs {bN bD F eh : ℤ} {T E : ℕ} (hbN : |bN| ≤ 2 ^ T) (hbD : |bD| ≤ 2 ^ T) (hF : |F| ≤ 2 ^ E)
    (he : |eh| ≤ 2 ^ E) : |(ptPair bN bD F eh).1| ≤ 2 ^ (T + E + 1) ∧ |(ptPair bN bD F eh).2| ≤ 2 ^ (T + E + 1) := by
  have h1 : (1 : ℤ) ≤ 2 ^ (T + E + 1) := one_le_pow₀ (by norm_num)
  have hs : |F - eh| ≤ 2 ^ (E + 1) := (abs_sub _ _).trans (by rw [pow_succ]; linarith)
  unfold ptPair
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [abs_mul]
      calc |bN| * |F| ≤ 2 ^ T * 2 ^ E := mul_le_mul hbN hF (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ (T + E + 1) := by rw [← pow_add]; exact pow_mono_z (by omega)
    · rw [abs_mul]
      calc |bD| * |F - eh| ≤ 2 ^ T * 2 ^ (E + 1) := mul_le_mul hbD hs (abs_nonneg _) (by positivity)
        _ = 2 ^ (T + E + 1) := by ring
  · exact ⟨by simpa using h1, by simpa using h1⟩

set_option maxHeartbeats 4000000 in
/-- **R2, the scale and the play buffer.** -/
theorem XV.r2p {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E : ℕ} {bN bD F eh DS DX : ℤ} {yv muS : Fin d → ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hbN : σ.sc sBN = bN) (hbD : σ.sc sBD = bD)
    (hF : σ.sc s2pF = F) (he : σ.sc sEps = eh) (hDS : σ.sc sDS = DS) (hDX : σ.sc sDX = DX)
    (hy : ∀ k : Fin d, σ.arr aYv k = yv k) (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k)
    (bbN : |bN| ≤ 2 ^ tG d E) (bbD : |bD| ≤ 2 ^ tG d E) (bF : |F| ≤ 2 ^ E) (beh : |eh| ≤ 2 ^ E)
    (bDS : |DS| ≤ 2 ^ E) (bDX : |DX| ≤ 2 ^ (4 * E)) (byv : ∀ k, |yv k| ≤ 2 ^ (7 * E + 2))
    (bmu : ∀ k, |muS k| ≤ 2 ^ E) (hd1 : 1 ≤ d) (hℓ : 3 * (E * d) + 33 * E + 11 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xR2p L) σ (r2pUnits d) (fun σ' =>
      σ'.sc sPtN = ((ptPair bN bD F eh).1 : ℝ) ∧ σ'.sc sPtD = ((ptPair bN bD F eh).2 : ℝ) ∧
      σ'.arr aPl 0 = ((DS * DX * (ptPair bN bD F eh).1 : ℤ) : ℝ) ∧
      (∀ k : Fin d, σ'.arr aPl (1 + k) =
        ((muS k * DX * (ptPair bN bD F eh).1 + yv k * (ptPair bN bD F eh).2 : ℤ) : ℝ)) ∧
      σ'.draws = σ.draws ∧ FrameA SP NP AP σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by omega)
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  set T := tG d E with hT
  have hTE : E ≤ T := by rw [hT]; unfold tG; omega
  have eT : ∀ {x : ℤ}, |x| ≤ 2 ^ E → |x| ≤ 2 ^ T := fun h => h.trans (pow_mono_z hTE)
  -- step 1: `c_1 = b_D (F - ε̂)`
  refine XV.seq (XV.ieRun (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σ) (E := T) (v := bD * (F - eh)) hL (z := sZ)
    (x := sC1) (t := tR) (e := ieC1) (by simp [ieC1, IE.WF]; pomega) (by pomega) (by pomega)
    (by rw [ieC1_facts.2.1]; pomega) hz
    ⟨⟨bD, hbD, bbD⟩, ⟨F, hF, eT bF⟩, ⟨eh, he, eT beh⟩⟩ (top_lt ieC1_facts.2.2 (by rw [hT]; unfold tG; omega))
    (by simp only [ieC1, IE.eval, RealRAM.Op2.eval, hbD, hF, he]; push_cast; ring))
    fun σ1 ⟨s1, b1, d1, P1⟩ => ?_
  have q1 : ∀ y, y ≠ sC1 → y < tR → σ1.sc y = σ.sc y := fun y h h' => P1.2.1 y (by omega)
  -- step 2: `c_2 = b_N F`
  refine XV.seq (XV.ieRun (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σ1) (E := T) (v := bN * F) hL (z := sZ)
    (x := sC2) (t := tR) (e := ieC2) (by simp [ieC2, IE.WF]; pomega) (by pomega) (by pomega)
    (by rw [ieC2_facts.2.1]; pomega) (by rw [q1 _ (by pomega) (by pomega), hz])
    ⟨⟨bN, by rw [q1 _ (by pomega) (by pomega), hbN], bbN⟩, ⟨F, by rw [q1 _ (by pomega) (by pomega), hF], eT bF⟩⟩
    (top_lt ieC2_facts.2.2 (by rw [hT]; unfold tG; omega))
    (by simp only [ieC2, IE.eval, RealRAM.Op2.eval, q1 _ (by pomega : sBN ≠ sC1) (by pomega),
      q1 _ (by pomega : s2pF ≠ sC1) (by pomega), hbN, hF]; push_cast; ring))
    fun σ2 ⟨s2, b2, d2, P2⟩ => ?_
  have q2 : ∀ y, y ≠ sC2 → y < tR → σ2.sc y = σ1.sc y := fun y h h' => P2.2.1 y (by omega)
  -- step 3: the scale
  set pN := (ptPair bN bD F eh).1 with hpN
  set pD := (ptPair bN bD F eh).2 with hpD
  obtain ⟨bpN, bpD⟩ := ptPair_abs (T := T) bbN bbD bF beh
  have hT2 : 2 * T + 1 < ℓ := by rw [hT]; unfold tG; omega
  have c1v : σ2.sc sC1 = ((bD * (F - eh) : ℤ) : ℝ) := by rw [q2 _ (by pomega) (by pomega), s1]
  have z2 : σ2.sc sZ = 0 := by rw [q2 _ (by pomega) (by pomega), q1 _ (by pomega) (by pomega), hz]
  have F2 : FrameA SP NP AP σ σ2 := ((FrameA.ofP P1).mono incSP_c1 (fun j h => h.elim)
    (fun b k h => h)).trans ((FrameA.ofP P2).mono incSP_c2 (fun j h => h.elim) (fun b k h => h))
  have d2' : σ2.draws = σ.draws := by rw [d2, d1]
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp
  have hb1 : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact_mod_cast (Nat.one_lt_two_pow (by omega : ℓ ≠ 0))
  refine XV.seq (K₁ := 4) (Q₁ := fun σ3 => σ3.sc sPtN = (pN : ℝ) ∧ σ3.sc sPtD = (pD : ℝ) ∧ σ3.draws = σ.draws ∧
      FrameA SP NP AP σ σ3) ?_ fun σ3 ⟨p3, p3', d3, F3⟩ => ?_
  · by_cases hc : σ2.sc sC1 < σ2.sc sC2
    · have hc' : bD * (F - eh) < bN * F := by rw [c1v, s2] at hc; exact_mod_cast hc
      refine XV.mono (XV.ifS_t hL (by pomega) (by pomega) (by rw [c1v]; exact XV.abs_int_lt b1) (by rw [s2]; exact XV.abs_int_lt b2) hc
        (XV.seq (K₁ := 1) (K₂ := 1) (XV.sop2 hL (x := sPtN) (a := sC2) (b := sZ) (by pomega) (by pomega) (by pomega) .add (by intro h; cases h)
          (by rw [s2]; exact XV.abs_int_lt b2) (by rw [z2]; exact h0) (by rw [s2, z2]; simpa [RealRAM.Op2.eval] using XV.abs_int_lt b2))
          fun σa ea => ?_)) (by norm_num) fun _ h => h
      subst ea
      refine XV.mono (XV.sop2 hL (x := sPtD) (a := sC1) (b := sZ) (by pomega) (by pomega) (by pomega) .add
        (by intro h; cases h) (by simp only [Env.setSc_sc]; rw [ite_eq_right (by pomega), c1v]; exact XV.abs_int_lt b1)
        (by simp only [Env.setSc_sc]; rw [ite_eq_right (by pomega), z2]; exact h0)
        (by simp only [Env.setSc_sc]; rw [ite_eq_right (by pomega), ite_eq_right (by pomega), c1v, z2];
            simpa [RealRAM.Op2.eval] using XV.abs_int_lt b1)) le_rfl fun σb eb => ?_
      subst eb
      refine ⟨?_, ?_, by simp [d2'], (F2.setSc (x := sPtN) (by simp [SP]) _).setSc (x := sPtD) (by simp [SP]) _⟩
      · rw [scO _ (by pomega : sPtN ≠ sPtD), scS, s2, z2, hpN, ptPair, ite_eq_left hc']; simp [RealRAM.Op2.eval]
      · rw [scS, scO _ (by pomega : sC1 ≠ sPtN), scO _ (by pomega : sZ ≠ sPtN), c1v, z2, hpD, ptPair, ite_eq_left hc']
        simp [RealRAM.Op2.eval]
    · have hc' : ¬ bD * (F - eh) < bN * F := by rw [c1v, s2] at hc; exact_mod_cast hc
      refine XV.ifS_f hL (by pomega) (by pomega) (by rw [c1v]; exact XV.abs_int_lt b1) (by rw [s2]; exact XV.abs_int_lt b2) hc
        (XV.seq (K₁ := 1) (K₂ := 1) (XV.sconst hL (x := sPtN) (by pomega) 1 rfl hb1) fun σa ea => ?_)
      subst ea
      refine XV.mono (XV.sconst hL (x := sPtD) (by pomega) 1 rfl hb1) le_rfl fun σb eb => ?_
      subst eb
      refine ⟨?_, ?_, by simp [d2'], (F2.setSc (x := sPtN) (by simp [SP]) _).setSc (x := sPtD) (by simp [SP]) _⟩
      · rw [scO _ (by pomega : sPtN ≠ sPtD), scS, hpN, ptPair, ite_eq_right hc']; simp
      · rw [scS, hpD, ptPair, ite_eq_right hc']; simp
  -- step 4: cell `0` of the play buffer
  have s3 : ∀ y, ¬ SP y → σ3.sc y = σ.sc y := F3.2.1
  have n3 : ∀ j, ¬ NP j → σ3.nat j = σ.nat j := F3.1
  have a3 : ∀ b k, b ≠ aPl → σ3.arr b k = σ.arr b k := fun b k h => F3.2.2.1 b k h
  set T1 := T + E + 1 with hT1
  have eT1 : ∀ {x : ℤ}, |x| ≤ 2 ^ E → |x| ≤ 2 ^ T1 := fun h => h.trans (pow_mono_z (by omega))
  have bDX1 : |DX| ≤ 2 ^ T1 := bDX.trans (pow_mono_z (by rw [hT1, hT]; unfold tG; omega))
  have hT3 : 3 * T1 + 1 < ℓ := by rw [hT1, hT]; unfold tG; omega
  refine XV.seq (XV.ieRun (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σ3) (E := T1) (v := DS * DX * pN) hL (z := sZ)
    (x := sC1) (t := tR) (e := ieP0) (by simp [ieP0, IE.WF]; pomega) (by pomega) (by pomega)
    (by rw [ieP0_facts.2.1]; pomega) (by rw [s3 _ (by pomega), hz])
    ⟨⟨⟨DS, by rw [s3 _ (by pomega), hDS], eT1 bDS⟩, ⟨DX, by rw [s3 _ (by pomega), hDX], bDX1⟩⟩, ⟨pN, p3, bpN⟩⟩
    (top_lt ieP0_facts.2.2 (by omega))
    (by simp only [ieP0, IE.eval, RealRAM.Op2.eval, s3 _ (by pomega : ¬ SP sDS), s3 _ (by pomega : ¬ SP sDX),
      hDS, hDX, p3]; push_cast; ring))
    fun σ4 ⟨s4, b4, d4, P4⟩ => ?_
  have q4 : ∀ y, y ≠ sC1 → y < tR → σ4.sc y = σ3.sc y := fun y h h' => P4.2.1 y (by omega)
  -- step 5, 6: `aPl[0] := D_S D_X pt_N`
  refine XV.seq (XV.nconst hL (σ := σ4) (i := rr) (by pomega) 0 (by positivity)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.aset hL (a := aPl) (i := rr) (x := sC1) (by pomega) (by pomega) (by pomega)
    (by simp only [Env.setNat_nat, ↓reduceIte]; unfold asz; nlinarith) (by simp only [Env.setNat_sc, s4]; exact XV.abs_int_lt b4))
    fun σ6 e6 => ?_
  subst e6
  -- step 7, 8: the cells `1 + k`
  refine XV.seq (XV.nconst hL (i := rr) (by pomega) 1 (by have := hL.1; omega)) fun σ7 e7 => ?_
  subst e7
  set σ7 := ((σ4.setNat rr 0).setArr aPl ((σ4.setNat rr 0).nat rr) ((σ4.setNat rr 0).sc sC1)).setNat rr 1 with hσ7
  have s7 : ∀ y, y ≠ sC1 → y < tR → σ7.sc y = σ3.sc y := fun y h h' => by
    simp only [hσ7, Env.setNat_sc, Env.setArr_sc]; exact q4 y h h'
  have n7 : ∀ j, j ≠ rr → σ7.nat j = σ3.nat j := fun j h => by
    simp only [hσ7, Env.setNat_nat, Env.setArr_nat]; rw [ite_eq_right h, ite_eq_right h, P4.1 j id]
  have a7 : ∀ b k, b ≠ aPl → σ7.arr b k = σ3.arr b k := fun b k h => by
    simp only [hσ7, Env.setNat_arr, Env.setArr_arr]; rw [ite_eq_right (fun h' => h h'.1), P4.2.2.1]
  have c70 : σ7.arr aPl 0 = ((DS * DX * pN : ℤ) : ℝ) := by
    simp only [hσ7, Env.setNat_arr, Env.setArr_arr, Env.setNat_nat, Env.setNat_sc, ↓reduceIte]; simp [s4]
  have F7 : FrameA SP NP AP σ σ7 := by
    have : FrameA SP NP AP σ3 σ4 := (FrameA.ofP P4).mono incSP_c1 (fun j h => h.elim)
      (fun b k h => h)
    exact (((F3.trans this).setNat (i := rr) (by simp [NP]) _).setArr rfl _).setNat (i := rr) (by simp [NP]) _
  have d7 : σ7.draws = σ.draws := by simp only [hσ7, Env.setNat_draws, Env.setArr_draws, d4, d3]
  set pj : Fin d → ℤ := fun k => muS k * DX * pN + yv k * pD with hpj
  refine XV.mono (XV.mapE (E := T1) (N := d) (base := 1) (st := 1) (F := vext pj) hL (σ := σ7) (z := sZ) (t := tR)
    (aB := aPl) (nr := rr) (nst := rOne) (nk := rk) (nn := rD) (none := rOne) (e := iePj)
    (by simp [iePj, IE.WF]; pomega) (by pomega) (by rw [iePj_facts.2.1]; pomega)
    (by rw [s7 _ (by pomega) (by pomega), s3 _ (by pomega), hz]) (by pomega) (by pomega) (by pomega) (by pomega)
    (by pomega) (by pomega) (by decide) (by decide) (by decide)
    (by rw [n7 _ (by pomega), n3 _ (by pomega), hD]) (by rw [n7 _ (by pomega), n3 _ (by pomega), h1])
    (by simp [hσ7]) (by rw [n7 _ (by pomega), n3 _ (by pomega), h1]) one_pos
    (fun k hk => by unfold asz; nlinarith) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by have := hL.1; omega) (top_lt iePj_facts.2.2 (by omega)) ?_) le_rfl fun σ8 ⟨x8, _, d8, F8⟩ => ?_
  · intro k hk σ' F' d' hk' hr'
    have sc' : ∀ y, y ≠ sC1 → y < tR → ¬ SP y → σ'.sc y = σ.sc y := fun y h h' h'' => by
      rw [F'.2.1 y (by omega), s7 y h h', s3 y h'']
    have ar' : ∀ b, b ≠ aPl → σ'.arr b k = σ.arr b k := fun b h => by
      rw [F'.2.2.1 b k (fun h' => h h'.1), a7 b k h, a3 b k h]
    have mu' : σ'.arr aMuS k = muS ⟨k, hk⟩ := by rw [ar' _ (by pomega)]; exact hmu ⟨k, hk⟩
    have yv' : σ'.arr aYv k = yv ⟨k, hk⟩ := by rw [ar' _ (by pomega)]; exact hy ⟨k, hk⟩
    have pN' : σ'.sc sPtN = (pN : ℝ) := by rw [F'.2.1 _ (by pomega), s7 _ (by pomega) (by pomega), p3]
    have pD' : σ'.sc sPtD = (pD : ℝ) := by rw [F'.2.1 _ (by pomega), s7 _ (by pomega) (by pomega), p3']
    have hkd : k < asz d := by unfold asz; nlinarith
    refine ⟨⟨⟨⟨⟨by rw [hk']; exact hkd, muS ⟨k, hk⟩, by rw [hk', mu'], eT1 (bmu _)⟩,
      DX, by rw [sc' _ (by pomega) (by pomega) (by pomega), hDX], bDX1⟩, pN, pN', bpN⟩,
      ⟨⟨by rw [hk']; exact hkd, yv ⟨k, hk⟩, by rw [hk', yv'],
        (byv _).trans (pow_mono_z (by rw [hT1, hT]; unfold tG; omega))⟩, pD, pD', bpD⟩⟩, ?_⟩
    simp only [iePj, IE.eval, RealRAM.Op2.eval, hk', mu', yv', pN', pD',
      sc' _ (by pomega : sDX ≠ sC1) (by pomega) (by pomega), hDX]
    rw [vext_lt _ hk, hpj]; push_cast; ring
  refine ⟨?_, ?_, ?_, fun k => ?_, ?_, ?_⟩
  · rw [F8.2.1 _ (by pomega), s7 _ (by pomega) (by pomega), p3]
  · rw [F8.2.1 _ (by pomega), s7 _ (by pomega) (by pomega), p3']
  · rw [F8.2.2.1 _ _ (fun h => by omega), c70]
  · have := x8 k k.2
    rw [one_mul, vext_lt _ k.2] at this
    exact this
  · rw [d8, d7]
  · exact F7.trans (F8.mono incSP_t incNP_k (fun b k h => h.1))

end AdversarialBco.Bit.Transfer.BLM
