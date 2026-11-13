/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLPrep
public import AdversarialBco.Bit.Transfer.XBLPrepP

@[expose] public section

/-!
# The preparation of BL's calls, part 3: `CallPrepBL`

The frozen contract `CallPrepBL` (Bit/Transfer/XBLCall.lean) holds with the command `xprep` of `XV.prep`, `C = 1024`,
`k = 3`. The integers of the input pairs are the floors of their cells (`pairA_cells`, `pairS_cells`); the reduced
pairs are the numerators and denominators of BL's rationals (`num_den_of_div`, `e_numden`), the products of the
reduced denominators are `quadDen`, `objDen`, `linDen` (`quadDen_range`, `objDen_range`), and the cleared cells are
`clr` (`clr_out`): `ellIn_of`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.PrepM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- The cells of a pair of arrays as integers. -/
def CellA (σ : Env d) (an ad s k : ℕ) : Prop :=
  σ.arr an k = (⌊σ.arr an k⌋ : ℝ) ∧ σ.arr ad k = (⌊σ.arr ad k⌋ : ℝ) ∧ |⌊σ.arr an k⌋| ≤ 2 ^ s ∧
    0 < ⌊σ.arr ad k⌋ ∧ ⌊σ.arr ad k⌋ ≤ 2 ^ s

theorem pairA_cells {σ : Env d} {an ad k s : ℕ} {x : ℚ} (h : PairA σ an ad k s x) :
    CellA σ an ad s k ∧ (⌊σ.arr an k⌋ : ℚ) / (⌊σ.arr ad k⌋ : ℚ) = x := by
  obtain ⟨u, v, v0, bu, bv, eu, ev, ex⟩ := h
  unfold CellA
  rw [eu, ev, Int.floor_intCast, Int.floor_intCast]
  exact ⟨⟨rfl, rfl, bu, v0, bv⟩, ex⟩

theorem pairS_cells {σ : Env d} {yn yd s : ℕ} {x : ℚ} (h : PairS σ yn yd s x) :
    PairS' σ yn yd s ⌊σ.sc yn⌋ ⌊σ.sc yd⌋ ∧ (⌊σ.sc yn⌋ : ℚ) / (⌊σ.sc yd⌋ : ℚ) = x := by
  obtain ⟨u, v, v0, bu, bv, eu, ev, ex⟩ := h
  unfold PairS'
  rw [eu, ev, Int.floor_intCast, Int.floor_intCast]
  exact ⟨⟨rfl, rfl, bu, v0, bv⟩, ex⟩

/-- `D_f` from integers equal to the denominators of `f`. -/
theorem linDen_range (f : Fin d → ℚ) (y : ℕ → ℤ) (hf : ∀ j : Fin d, ((f j).den : ℤ) = y j) :
    ((∏ j, (f j).den : ℕ) : ℤ) = ∏ j ∈ Finset.range d, y j := by
  rw [Nat.cast_prod, ← Fin.prod_univ_eq_prod_range y d]
  exact Finset.prod_congr rfl fun j _ => hf j

/-- **The cells after the preparation are the inputs of the block.** -/
theorem ellIn_of {D : CallQ d} {σ' : Env d} {uH vH ug vg uP vP uf vf : ℕ → ℤ} {ul vl ur vr ue ve : ℤ} {Ri : ℕ}
    (qH : ∀ i j : Fin d, 0 < vH (d * i + j) ∧ (uH (d * i + j) : ℚ) / (vH (d * i + j) : ℚ) = D.H i j)
    (qg : ∀ j : Fin d, 0 < vg j ∧ (ug j : ℚ) / (vg j : ℚ) = D.g j)
    (qP : ∀ i j : Fin d, 0 < vP (d * i + j) ∧ (uP (d * i + j) : ℚ) / (vP (d * i + j) : ℚ) = D.P i j)
    (qf : ∀ j : Fin d, 0 < vf j ∧ (uf j : ℚ) / (vf j : ℚ) = D.f j)
    (ql : 0 < vl ∧ (ul : ℚ) / (vl : ℚ) = D.ℓ) (qr : 0 < vr ∧ (ur : ℚ) / (vr : ℚ) = D.r)
    (qe : 0 < ve ∧ (ue : ℚ) / (ve : ℚ) = D.e) (hR : D.R = (Ri : ℚ)) (hDP : 0 < DPr (d * d) uP vP)
    (nd : σ'.nat rD = d) (nm : σ'.nat rMk = D.m)
    (pH : ∀ k < d * d, σ'.arr aEH k =
      ((redN (uH k) (vH k) * (DH d uH vH ug vg ul vl / redD (uH k) (vH k)) * 1 : ℤ) : ℝ))
    (pg : ∀ k < d, σ'.arr aEg k =
      ((redN (ug k) (vg k) * (DH d uH vH ug vg ul vl / redD (ug k) (vg k)) * 1 : ℤ) : ℝ))
    (pl : σ'.sc 80 = ((redN ul vl * (DH d uH vH ug vg ul vl / redD ul vl) : ℤ) : ℝ))
    (pP : ∀ k < d * d, σ'.arr aEP k =
      ((redN (uP k) (vP k) * (DPr (d * d) uP vP / redD (uP k) (vP k)) * 1 : ℤ) : ℝ))
    (pf : ∀ k < d, σ'.arr aEf k =
      ((redN (uf k) (vf k) * (DPr d uf vf / redD (uf k) (vf k)) * DPr (d * d) uP vP : ℤ) : ℝ))
    (p81 : σ'.sc 81 = ((DPr d uf vf : ℤ) : ℝ)) (p82 : σ'.sc 82 = ((Ri : ℤ) : ℝ)) (p83 : σ'.sc 83 = ((1 : ℤ) : ℝ))
    (p84 : σ'.sc 84 = ((redN ur vr : ℤ) : ℝ)) (p85 : σ'.sc 85 = ((redD ur vr : ℤ) : ℝ))
    (p86 : σ'.sc 86 = ((redN (DPr (d * d) uP vP * ue) ve : ℤ) : ℝ))
    (p87 : σ'.sc 87 = ((redD (DPr (d * d) uP vP * ue) ve : ℤ) : ℝ)) :
    EllIn blkBL (clearQ D) σ' := by
  have dH : ∀ i j : Fin d, (D.H i j).num = redN (uH (d * i + j)) (vH (d * i + j)) ∧
      ((D.H i j).den : ℤ) = redD (uH (d * i + j)) (vH (d * i + j)) :=
    fun i j => num_den_of_div _ _ (qH i j).1 _ (qH i j).2.symm
  have dg : ∀ j : Fin d, (D.g j).num = redN (ug j) (vg j) ∧ ((D.g j).den : ℤ) = redD (ug j) (vg j) :=
    fun j => num_den_of_div _ _ (qg j).1 _ (qg j).2.symm
  have dP : ∀ i j : Fin d, (D.P i j).num = redN (uP (d * i + j)) (vP (d * i + j)) ∧
      ((D.P i j).den : ℤ) = redD (uP (d * i + j)) (vP (d * i + j)) :=
    fun i j => num_den_of_div _ _ (qP i j).1 _ (qP i j).2.symm
  have df : ∀ j : Fin d, (D.f j).num = redN (uf j) (vf j) ∧ ((D.f j).den : ℤ) = redD (uf j) (vf j) :=
    fun j => num_den_of_div _ _ (qf j).1 _ (qf j).2.symm
  have dl : D.ℓ.num = redN ul vl ∧ (D.ℓ.den : ℤ) = redD ul vl := num_den_of_div _ _ ql.1 _ ql.2.symm
  have dr : D.r.num = redN ur vr ∧ (D.r.den : ℤ) = redD ur vr := num_den_of_div _ _ qr.1 _ qr.2.symm
  have eQ : ((quadDen D : ℕ) : ℤ) = DH d uH vH ug vg ul vl := by
    unfold DH; rw [one_mul]
    exact quadDen_range D.H D.g D.ℓ (fun k => redD (uH k) (vH k)) (fun k => redD (ug k) (vg k)) (redD ul vl)
      (fun i j => (dH i j).2) (fun j => (dg j).2) dl.2
  have eO : ((objDen D : ℕ) : ℤ) = DPr (d * d) uP vP := by
    unfold DPr; rw [one_mul]; exact objDen_range D.P (fun k => redD (uP k) (vP k)) fun i j => (dP i j).2
  have eL : ((linDen D : ℕ) : ℤ) = DPr d uf vf := by
    unfold DPr; rw [one_mul]; exact linDen_range D.f (fun k => redD (uf k) (vf k)) fun j => (df j).2
  have hO : 0 < objDen D := by have h := hDP; rw [← eO] at h; exact_mod_cast h
  have de := e_numden (objDen D) hO D.e ue ve qe.1 qe.2
  have hk : ∀ i j : Fin d, d * (i : ℕ) + j < d * d := fun i j => by
    have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt i.2)
    rw [Nat.mul_succ] at this; omega
  refine ⟨nd, nm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i j => ?_, fun j => ?_, fun i j => ?_, fun j => ?_⟩
  · show σ'.sc 80 = ((D.ℓ.num * ((quadDen D / D.ℓ.den : ℕ) : ℤ) : ℤ) : ℝ)
    rw [clr_out _ _ _ _ dl.1 dl.2, eQ, pl]
  · show σ'.sc 81 = ((linDen D : ℕ) : ℝ)
    rw [p81, ← eL, Int.cast_natCast (R := ℝ)]
  · show σ'.sc 82 = ((D.R.num : ℤ) : ℝ)
    rw [p82, hR, Rat.num_natCast]
  · show σ'.sc 83 = ((D.R.den : ℕ) : ℝ)
    rw [p83, hR, Rat.den_natCast]; simp
  · show σ'.sc 84 = ((D.r.num : ℤ) : ℝ)
    rw [p84, dr.1]
  · show σ'.sc 85 = ((D.r.den : ℕ) : ℝ)
    rw [p85, ← dr.2, Int.cast_natCast (R := ℝ)]
  · show σ'.sc 86 = ((((objDen D : ℚ) * D.e).num : ℤ) : ℝ)
    rw [p86, ← eO, de.1]; rfl
  · show σ'.sc 87 = (((((objDen D : ℚ) * D.e).den : ℕ)) : ℝ)
    rw [p87, ← eO, ← Int.cast_natCast (R := ℝ), de.2]; rfl
  · show σ'.arr aEH (d * i + j) = (((D.H i j).num * ((quadDen D / (D.H i j).den : ℕ) : ℤ) : ℤ) : ℝ)
    rw [clr_out _ _ _ _ (dH i j).1 (dH i j).2, eQ, pH _ (hk i j), mul_one]
  · show σ'.arr aEg j = (((D.g j).num * ((quadDen D / (D.g j).den : ℕ) : ℤ) : ℤ) : ℝ)
    rw [clr_out _ _ _ _ (dg j).1 (dg j).2, eQ, pg _ j.2, mul_one]
  · show σ'.arr aEP (d * i + j) = (((D.P i j).num * ((objDen D / (D.P i j).den : ℕ) : ℤ) : ℤ) : ℝ)
    rw [clr_out _ _ _ _ (dP i j).1 (dP i j).2, eO, pP _ (hk i j), mul_one]
  · show σ'.arr aEf j =
      (((D.f j).num * ((linDen D / (D.f j).den : ℕ) : ℤ) * ((objDen D : ℕ) : ℤ) : ℤ) : ℝ)
    rw [clr_out _ _ _ _ (df j).1 (df j).2, eL, eO, pf _ j.2]

set_option maxHeartbeats 16000000 in
/-- **`CallPrepBL` holds.** -/
theorem callPrepBL : CallPrepBL := by
  refine ⟨xprep, 1024, 3, ?_⟩
  intro d L X ℓa ℓ s cfg H g ℓq r P f e σ hd hL hlay hin hCl hCa
  obtain ⟨hNS, hNN, hNA⟩ := hlay
  simp only [oE, rEE, aWE] at hNS hNN hNA
  obtain ⟨hD, hMk, h1, hz, hR, bR, pH, pg, pP, pf, pl, pr, pe⟩ := hin
  have hx3 : s * (d * d + d + 2) + 1 ≤ (d + s + 1) ^ 3 := by
    nlinarith [Nat.zero_le (d * d * d), Nat.zero_le (s * s * s), Nat.zero_le (d * d * s), Nat.zero_le (d * s * s),
      Nat.zero_le (d * d), Nat.zero_le (s * s), Nat.zero_le (d * s)]
  have hx2 : d * d + d ≤ (d + s + 1) ^ 3 := by
    nlinarith [Nat.zero_le (d * d * d), Nat.zero_le (s * s * s), Nat.zero_le (d * d * s), Nat.zero_le (d * s * s),
      Nat.zero_le (d * d), Nat.zero_le (s * s), Nat.zero_le (d * s)]
  have hℓ : s * (d * d + d + 2) + 1 < ℓ := by omega
  have hda : d * d + d < 2 ^ ℓa := by omega
  have hH : PairsA σ aPHn aPHd (d * d) s (fun k => ⌊σ.arr aPHn k⌋) (fun k => ⌊σ.arr aPHd k⌋) :=
    (cells_mat (d := d) (CellA σ aPHn aPHd s)).mp fun i j => (pairA_cells (pH i j)).1
  have hP : PairsA σ aPPn aPPd (d * d) s (fun k => ⌊σ.arr aPPn k⌋) (fun k => ⌊σ.arr aPPd k⌋) :=
    (cells_mat (d := d) (CellA σ aPPn aPPd s)).mp fun i j => (pairA_cells (pP i j)).1
  have hg : PairsA σ aPgn aPgd d s (fun k => ⌊σ.arr aPgn k⌋) (fun k => ⌊σ.arr aPgd k⌋) :=
    fun k hk => (pairA_cells (pg ⟨k, hk⟩)).1
  have hf : PairsA σ aPfn aPfd d s (fun k => ⌊σ.arr aPfn k⌋) (fun k => ⌊σ.arr aPfd k⌋) :=
    fun k hk => (pairA_cells (pf ⟨k, hk⟩)).1
  have hDP := (DPr_bounds (u := fun k => ⌊σ.arr aPPn k⌋) fun k hk => ⟨(hP k hk).2.2.2.1, (hP k hk).2.2.2.2⟩).1
  refine XV.mono (XV.prep hL (by omega) (by omega) (by omega) (Ri := cfg.par.Rint) hD h1 hz hR bR hH hg hP hf
    (pairS_cells pl).1 (pairS_cells pr).1 (pairS_cells pe).1 hℓ hda) (prepUnits_le d s)
    fun σ' ⟨q1, q2, q3, q4, q5, q81, q82, q83, q84, q85, q86, q87, qd, qF⟩ => ⟨?_, qd, qF⟩
  exact ellIn_of (D := callOf cfg H g ℓq r P f e) (σ' := σ') (Ri := cfg.par.Rint)
    (uH := fun k => ⌊σ.arr aPHn k⌋) (vH := fun k => ⌊σ.arr aPHd k⌋) (ug := fun k => ⌊σ.arr aPgn k⌋)
    (vg := fun k => ⌊σ.arr aPgd k⌋) (uP := fun k => ⌊σ.arr aPPn k⌋) (vP := fun k => ⌊σ.arr aPPd k⌋)
    (uf := fun k => ⌊σ.arr aPfn k⌋) (vf := fun k => ⌊σ.arr aPfd k⌋) (ul := ⌊σ.sc sPl⌋) (vl := ⌊σ.sc (sPl + 1)⌋)
    (ur := ⌊σ.sc (sPl + 2)⌋) (vr := ⌊σ.sc (sPl + 3)⌋) (ue := ⌊σ.sc (sPl + 4)⌋) (ve := ⌊σ.sc (sPl + 5)⌋)
    (fun i j => ⟨(pairA_cells (pH i j)).1.2.2.2.1, (pairA_cells (pH i j)).2⟩)
    (fun j => ⟨(pairA_cells (pg j)).1.2.2.2.1, (pairA_cells (pg j)).2⟩)
    (fun i j => ⟨(pairA_cells (pP i j)).1.2.2.2.1, (pairA_cells (pP i j)).2⟩)
    (fun j => ⟨(pairA_cells (pf j)).1.2.2.2.1, (pairA_cells (pf j)).2⟩)
    ⟨(pairS_cells pl).1.2.2.2.1, (pairS_cells pl).2⟩ ⟨(pairS_cells pr).1.2.2.2.1, (pairS_cells pr).2⟩
    ⟨(pairS_cells pe).1.2.2.2.1, (pairS_cells pe).2⟩ rfl hDP
    (by rw [qF.1 rD (by pwgo)]; exact hD) (by rw [qF.1 rMk (by pwgo)]; exact hMk)
    q1 q2 q3 q4 q5 q81 q82 q83 q84 q85 q86 q87

end AdversarialBco.Bit.Transfer.BLM.PrepM
