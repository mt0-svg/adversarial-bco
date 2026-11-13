/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRow
public import AdversarialBco.Bit.Transfer.XBLRowK

@[expose] public section

/-!
# The row provider of BL, part 7: `RowBL`

The frozen contract `RowBL` (Bit/Transfer/XBLCall.lean) holds with the command `xrow` of `XV.row`, `C = 1024`,
`k = 3`: the integers of the cells are BL's rationals (`colDot_range`, `beta_range`, the input cells `NmI`, `DnI`,
the position `PosRep`), the row found by the scan is the `i`-th kept row (`scanK_get`, `keep_link`), and the units
and magnitudes are below `1024 W^3`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.BLP Matrix

/-- The units of the row command below `1024 x^3`. -/
theorem rowUnits_le {d m s x : ℕ} (hd : d ≤ x) (hm : m ≤ x) (hx : 1 ≤ x) (hs : s ≤ 14 * x ^ 2) :
    rowUnits d m s ≤ 1024 * x ^ 3 := by
  have hdm : d * m ≤ x * x := Nat.mul_le_mul hd hm
  have hdd : d * d ≤ x * x := Nat.mul_le_mul hd hd
  have hds : d * s ≤ x * (14 * x ^ 2) := Nat.mul_le_mul hd hs
  have h2 : x * x = x ^ 2 := by ring
  have h3 : x * (14 * x ^ 2) = 14 * x ^ 3 := by ring
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hx3 : x ^ 2 ≤ x ^ 3 := by nlinarith
  simp only [rowUnits, scanUnits, scanKb, sqUnits, colUnits, colKb, sdotUnits, redUnits, gcdUnits, betaUnits,
    outUnits]
  nlinarith

/-- The magnitude `s = 3 (E + size(M) (d + 2)) + d + 1` below `14 x^2`. -/
theorem s_le {d sz E x : ℕ} (hd : d + 1 ≤ x) (hsz : sz ≤ x) (hE : E ≤ x) :
    3 * (E + sz * (d + 2)) + d + 1 ≤ 14 * x ^ 2 := by
  have h1 : sz * (d + 2) ≤ x * (x + 1) := Nat.mul_le_mul hsz (by omega)
  have hx : 1 ≤ x := by omega
  nlinarith

/-- The bounds of `rowBL` from `1024 x^3 ≤ ℓ` and `1024 x^3 < 2^ℓa`. -/
theorem row_bounds {d m s i x ℓ ℓa : ℕ} (hx : 1 ≤ x) (hd : d + 2 ≤ 3 * x) (hd1 : d + 1 ≤ x) (hm1 : m + 1 ≤ x)
    (hi : i < x) (hs : s ≤ 14 * x ^ 2) (hC : 1024 * x ^ 3 ≤ ℓ) (hCa : 1024 * x ^ 3 < 2 ^ ℓa) :
    s * (d + 2) + 1 < ℓ ∧ 4 + 2 * (d + 1) * (m + 1) < 2 ^ ℓa ∧ i < 2 ^ ℓa ∧ d * d + d < 2 ^ ℓa := by
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hx3 : x ^ 2 ≤ x ^ 3 := by nlinarith
  have h1 : s * (d + 2) ≤ 14 * x ^ 2 * (3 * x) := Nat.mul_le_mul hs hd
  have h2 : (d + 1) * (m + 1) ≤ x * x := Nat.mul_le_mul hd1 hm1
  have h3 : d * d ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
  have e1 : 14 * x ^ 2 * (3 * x) = 42 * x ^ 3 := by ring
  have e2 : x * x = x ^ 2 := by ring
  have e3 : 2 * (d + 1) * (m + 1) = 2 * ((d + 1) * (m + 1)) := by ring
  omega

set_option maxHeartbeats 16000000 in
/-- **`RowBL` holds.** -/
theorem rowBL : RowBL := by
  refine ⟨xrow, 1024, 3, ?_⟩
  intro d L w n m M E ℓa ℓ A b c S H g ℓq r P f e hd hL hH hOn he0 he1 hCl hCa
  refine ⟨fun y h => ?_, fun j h => ?_, fun a h => ?_, ?_⟩
  · simp only [SRow, blkBL, oE] at h ⊢; omega
  · simp only [NRow, blkBL, rEE] at h ⊢; omega
  · simp only [ARow, blkBL, aWE] at h ⊢; omega
  intro σ ctx hi
  obtain ⟨hNS, hNN, hNA⟩ := ctx.lay
  simp only [oE, rEE, aWE] at hNS hNN hNA
  obtain ⟨rD', rM', rMk', rOne', rPF'⟩ := ctx.regs
  obtain ⟨cZ, c2p, cEps⟩ := ctx.consts
  obtain ⟨DS, hDS0, hDS, hmuS, hAS⟩ := ctx.pos
  obtain ⟨bsc, barr⟩ := ctx.bnd
  set i := σ.nat blkBL.rE with hidef
  have hi' : i < (keptIdx A).length := hi
  have hkl : (keptIdx A).length ≤ m := by
    unfold keptIdx; exact (List.length_filter_le _ _).trans (by simp)
  have hm1 : 1 ≤ m := by omega
  -- the cells of the context as integers
  have hint : ∀ a ∈ [aMuS, aAS], ∀ k < asz d, σ.arr a k = (⌊σ.arr a k⌋ : ℝ) ∧ |⌊σ.arr a k⌋| ≤ 2 ^ E :=
    fun a ha k hk => by
      obtain ⟨z, hz, hzb⟩ := barr a ha k hk
      rw [hz, Int.floor_intCast]; exact ⟨rfl, hzb⟩
  set xa : ℕ → ℤ := fun k => ⌊σ.arr aAS k⌋ with hxadef
  set xmu : ℕ → ℤ := fun k => ⌊σ.arr aMuS k⌋ with hxmudef
  have hxa : ∀ k < d * d, σ.arr aAS k = xa k := fun k hk =>
    (hint aAS (by simp) k (by unfold asz; omega)).1
  have hmu : ∀ l < d, σ.arr aMuS l = xmu l := fun l hl =>
    (hint aMuS (by simp) l (by unfold asz; omega)).1
  have bxa : ∀ k < d * d, |xa k| ≤ 2 ^ E := fun k hk => (hint aAS (by simp) k (by unfold asz; omega)).2
  have bmu : ∀ l < d, |xmu l| ≤ 2 ^ E := fun l hl => (hint aMuS (by simp) l (by unfold asz; omega)).2
  obtain ⟨zD, hzD, bzD⟩ := bsc sDS (by simp)
  have ezD : zD = DS := by rw [hDS] at hzD; exact_mod_cast hzD.symm
  subst ezD
  have bDS : zD ≤ 2 ^ E := le_trans (le_abs_self _) bzD
  obtain ⟨z2, hz2, bz2⟩ := bsc s2pF (by simp)
  have ez2 : z2 = 2 ^ (par d n).pF := by
    rw [c2p] at hz2; exact_mod_cast hz2.symm
  subst ez2
  have bp2 : (2 : ℤ) ^ (par d n).pF ≤ 2 ^ E := le_trans (le_abs_self _) bz2
  have h2p : σ.sc s2pF = (((2 : ℤ) ^ (par d n).pF : ℤ) : ℝ) := by rw [c2p]; push_cast; rfl
  set eh := qn (par d n).pF (par d n).eps with hehdef
  have hehq : (eh : ℚ) = (par d n).eps * 2 ^ (par d n).pF := hOn
  have heh : 0 ≤ eh ∧ eh ≤ 2 ^ (par d n).pF := by
    constructor
    · have : (0 : ℚ) ≤ eh := by rw [hehq]; positivity
      exact_mod_cast this
    · have : (eh : ℚ) ≤ 2 ^ (par d n).pF := by
        rw [hehq]; exact mul_le_of_le_one_left (by positivity) he1
      exact_mod_cast this
  -- the input rows
  have hM1 : (1 : ℤ) ≤ M := by
    have := (hH.2 ⟨0, by omega⟩).2
    have h0 := (b ⟨0, by omega⟩).den_pos
    have h1 : 0 < M := h0.trans_le this
    exact_mod_cast h1
  have bNm : ∀ k < m, ∀ j ≤ d, |NmI d n m A b k j| ≤ (M : ℤ) := fun k hk j hj => by
    have e := NmI_eq (n := n) A b ⟨k, hk⟩ hj
    change NmI d n m A b k j = _ at e
    rw [e, Int.abs_eq_natAbs]
    unfold BitRAM.entry
    split_ifs with hjd
    · exact_mod_cast (hH.1 ⟨k, hk⟩ ⟨j, hjd⟩).1
    · exact_mod_cast (hH.2 ⟨k, hk⟩).1
  have bDn : ∀ k < m, ∀ j ≤ d, 1 ≤ DnI d n m A b k j ∧ DnI d n m A b k j ≤ (M : ℤ) := fun k hk j hj => by
    have e := DnI_eq (n := n) A b ⟨k, hk⟩ hj
    change DnI d n m A b k j = _ at e
    rw [e]
    refine ⟨by exact_mod_cast (BitRAM.entry A b ⟨k, hk⟩ j).den_pos, ?_⟩
    unfold BitRAM.entry
    split_ifs with hjd
    · exact_mod_cast (hH.1 ⟨k, hk⟩ ⟨j, hjd⟩).2
    · exact_mod_cast (hH.2 ⟨k, hk⟩).2
  -- the row found by the scan
  set K := (keptIdx A).get ⟨i, hi'⟩ with hKdef
  have hK : rowK d (NmI d n m A b) i m = (K : ℕ) := by
    unfold rowK
    exact @scanK_get m (fun k : Fin m => A k ≠ 0) (fun k => inferInstance) (keepOf d (NmI d n m A b)) (fun k => by
      unfold keepOf
      exact keep_link A (NmI d n m A b) (fun k' j => by
        rw [NmI_eq (n := n) A b k' j.2.le]; unfold BitRAM.entry; simp [j.2]) k) i hi'
  -- magnitudes
  obtain ⟨hMt, hDt⟩ := mag_t M d E (by exact_mod_cast hM1)
  set t := E + M.size * (d + 2) with htdef
  set x := d + m + M.size + E + 1 with hxdef
  have hsx := s_le (d := d) (sz := M.size) (E := E) (x := x) (by omega) (by omega) (by omega)
  have hU := rowUnits_le (d := d) (m := m) (s := 3 * t + d + 1) (x := x) (by omega) (by omega) (by omega) hsx
  obtain ⟨hℓ, hma, hia, hda⟩ := row_bounds (d := d) (m := m) (s := 3 * t + d + 1) (i := i) (x := x) (ℓ := ℓ)
    (ℓa := ℓa) (by omega) (by omega) (by omega) (by omega) (by omega) hsx hCl hCa
  refine XV.mono (XV.row (d := d) (L := L) (X := ctxOf w n m A b) (ℓa := ℓa) (ℓ := ℓ) (σ := σ) hL (by omega)
    (by omega) (by omega) (m := m) (i := i) (E := E) (t := t) (Nm := NmI d n m A b) (Dn := DnI d n m A b)
    (Mh := M) (DS := zD) (p2 := 2 ^ (par d n).pF) (eh := eh) (xa := xa) (xmu := xmu) rD' rM' rOne' rfl cZ h2p
    cEps hDS hxa hmu le_rfl (fun k hk j hj => rfl) (fun k hk j hj => rfl) hM1 bNm bDn (by rw [hK]; exact K.2)
    hDS0 (by positivity) heh bp2 bxa bmu bDS hMt hDt (by omega) hℓ hma hia hda) hU ?_
  intro σ' ⟨u1, u2, u3, u4⟩
  rw [hK] at u1 u2
  -- the rationals of the row
  have hα : ∀ j : Fin d, rowAq d (NmI d n m A b) (DnI d n m A b) xa zD K j = (mkCfg d n m A b c S).α ⟨i, hi'⟩ j :=
    fun j => by
      unfold rowAq
      rw [show (mkCfg d n m A b c S).α ⟨i, hi'⟩ = S.2ᵀ *ᵥ A K from rfl]
      refine (colDot_range S.2 (A K) xa (rowH d (NmI d n m A b) (DnI d n m A b) K) zD
        (rowP d (DnI d n m A b) K) hDS0 (PiI_pos (n := n) A b K) (fun i' j' => ?_) (fun l => rowA_A (n := n) A b K l) j).symm
      obtain ⟨x', hx', hxq⟩ := hAS i' j'
      have : xa (d * i' + j') = x' := by
        simp only [hxadef]; rw [hx', Int.floor_intCast]
      rw [this]; exact hxq
  have hβ : rowBq d (NmI d n m A b) (DnI d n m A b) xmu zD (2 ^ (par d n).pF) eh K =
      (1 - (par d n).eps) * (mkCfg d n m A b c S).β ⟨i, hi'⟩ := by
    unfold rowBq
    rw [show (mkCfg d n m A b c S).β ⟨i, hi'⟩ = b K - A K ⬝ᵥ S.1 from rfl]
    refine (beta_range (par d n).pF (par d n).eps eh hehq (b K) (A K) S.1
      (rowA (NmI d n m A b) (DnI d n m A b) d K d) (rowH d (NmI d n m A b) (DnI d n m A b) K) xmu zD
      (rowP d (DnI d n m A b) K) hDS0 (PiI_pos (n := n) A b K) (rowA_b (n := n) A b K) (fun l => rowA_A (n := n) A b K l) (fun l => ?_)).symm
    obtain ⟨x', hx', hxq⟩ := hmuS l
    have : xmu l = x' := by simp only [hxmudef]; rw [hx', Int.floor_intCast]
    rw [this]; exact hxq
  have hR : rowDenR d (rowAq d (NmI d n m A b) (DnI d n m A b) xa zD K)
      (rowBq d (NmI d n m A b) (DnI d n m A b) xmu zD (2 ^ (par d n).pF) eh K) =
      rowDen (callOf (mkCfg d n m A b c S) H g ℓq r P f e) ⟨i, hi'⟩ := by
    unfold rowDenR rowDen
    rw [hβ, ← Fin.prod_univ_eq_prod_range]
    simp only [hα]
    rfl
  refine ⟨fun j => ?_, ?_, u3, u4⟩
  · have := u1 j j.2
    rw [hR, hα j] at this
    exact this
  · rw [hR, hβ] at u2
    exact u2

end AdversarialBco.Bit.Transfer.BLM.RowM
