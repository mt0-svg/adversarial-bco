/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowO
public import AdversarialBco.Bit.Transfer.XBLR2q

@[expose] public section

/-!
# The row provider of BL, part 6: the row command on the machine

`xrow L` chains the scan (the row `kk`, the `i`-th row with a positive sum of squares), the reading of the row
(`â = Nm (P / Dn)`, `b̂ D_S`, `XV.inRow`), the product `P` of its denominators, `D₀ = D_S P`, the columns,
the right-hand side and the output. `XV.row`: the array `33` and the slot `770` end as the row `kk` cleared by the
product of its reduced denominators (`clr`), in terms of the integers that the cells hold.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP AdversarialBco.Bit.RQ

variable {d : ℕ}

/-- The row command. -/
def xrow (L : Layout) : XCmd :=
  .seq (xscan L) (.seq (xinRow L 100 101 102 103 104 sDS 12 36 37 33 rD 39 35 rOne)
    (.seq (xaddr 36 39 35 37 4) (.seq (toX (VL.sconst L 105 ((1 : ℤ) : ℚ)))
      (.seq (xdenProd L 105 106 33 36 39 rOne) (.seq (toX (VL.sop2 L .mul 107 sDS 105))
        (.seq (xcols L) (.seq (xbeta L) (xout L))))))))

/-- The units of the row command. -/
def rowUnits (d m s : ℕ) : ℕ :=
  scanUnits d m + ((18 * d + 28) + ((1 + (1 + (1 + 1))) + (1 + (((d + 1) * (4 + 3) + 3) +
    (1 + (colUnits d s + (betaUnits d s + outUnits d)))))))

/-- The row `kk` that the scan finds. -/
def rowK (d : ℕ) (Nm : ℕ → ℕ → ℤ) (i m : ℕ) : ℕ := (scanK (keepOf d Nm) i m).2

/-- The cleared row `â_l = Nm (P / Dn)` of the row `k`. -/
def rowH (d : ℕ) (Nm Dn : ℕ → ℕ → ℤ) (k : ℕ) : ℕ → ℤ := fun l => rowA Nm Dn d k l

/-- The product `P` of the denominators of the row `k`. -/
def rowP (d : ℕ) (Dn : ℕ → ℕ → ℤ) (k : ℕ) : ℤ := ∏ j ∈ Finset.range (d + 1), Dn k j

/-- The entry `q` of `α̃`, `N_q / D₀`. -/
def rowAq (d : ℕ) (Nm Dn : ℕ → ℕ → ℤ) (xa : ℕ → ℤ) (DS : ℤ) (k q : ℕ) : ℚ :=
  (colN d xa (rowH d Nm Dn k) q : ℚ) / ((DS * rowP d Dn k : ℤ) : ℚ)

/-- The right-hand side `N_β / D_β`. -/
def rowBq (d : ℕ) (Nm Dn : ℕ → ℕ → ℤ) (xmu : ℕ → ℤ) (DS p2 eh : ℤ) (k : ℕ) : ℚ :=
  (((p2 - eh) * (rowA Nm Dn d k d * DS - dotS d (rowH d Nm Dn k) xmu) : ℤ) : ℚ) /
    ((p2 * (DS * rowP d Dn k) : ℤ) : ℚ)

/-- The product of the denominators of a row `a q` (`q < d`), `b`. -/
def rowDenR (d : ℕ) (a : ℕ → ℚ) (b : ℚ) : ℕ := (∏ q ∈ Finset.range d, (a q).den) * b.den

/-- `clr` of `N / D` (`D > 0`) as the machine computes it, from the reduced pair. -/
theorem clr_link {x : ℚ} {N D : ℤ} (hD : 0 < D) (hx : x = (N : ℚ) / D) {R' : ℕ} {R : ℤ} (hR : (R' : ℤ) = R) :
    clr R' x = N / (Int.gcd N D : ℤ) * (R / (D / (Int.gcd N D : ℤ))) := by
  obtain ⟨h1, h2⟩ := num_den_of_div N D hD x hx
  unfold clr
  rw [Int.natCast_div, hR, h1, h2]

theorem den_link {x : ℚ} {N D : ℤ} (hD : 0 < D) (hx : x = (N : ℚ) / D) :
    ((x.den : ℕ) : ℤ) = D / (Int.gcd N D : ℤ) := (num_den_of_div N D hD x hx).2

theorem pow_le_pow_of_le' {E t : ℕ} (h : E ≤ t) : (2 : ℤ) ^ E ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) h

set_option maxHeartbeats 16000000 in
/-- **The row command on the machine.** From the cells of the context (`d`, `m`, `1`, `i` in the register `64`, `0`,
`2^pF = p2`, `ε̂ = eh`, `D_S`, the numerators of `A_S` and `μ_S`) and the input rows (numerators `Nm`, denominators
`Dn`, all of height `Mh`), `xrow L` writes the row `kk = rowK` cleared by `rowDenR`: `clr R (N_q / D₀)` into the
cells `q < d` of the array `33`, `clr R (N_β / D_β)` into the slot `770`. -/
theorem XV.row {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    (hNN : 65 ≤ L.NN) (hNA : 34 ≤ L.NA) {m i E t : ℕ} {Nm Dn : ℕ → ℕ → ℤ} {Mh DS p2 eh : ℤ} {xa xmu : ℕ → ℤ}
    (hD : σ.nat rD = d) (hM : σ.nat rM = m) (h1 : σ.nat rOne = 1) (hi : σ.nat 64 = i)
    (hz : σ.sc sZ = 0) (h2p : σ.sc s2pF = p2) (hep : σ.sc sEps = eh) (hDS : σ.sc sDS = DS)
    (hxa : ∀ k < d * d, σ.arr aAS k = xa k) (hmu : ∀ l < d, σ.arr aMuS l = xmu l)
    (hoff : 3 + 2 * (d + 1) * m ≤ X.off)
    (hinpN : ∀ k < m, ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * k + j)) = Nm k j)
    (hinpD : ∀ k < m, ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * k + j)) = Dn k j)
    (hM1 : 1 ≤ Mh) (bNm : ∀ k < m, ∀ j ≤ d, |Nm k j| ≤ Mh) (bDn : ∀ k < m, ∀ j ≤ d, 1 ≤ Dn k j ∧ Dn k j ≤ Mh)
    (hkk : rowK d Nm i m < m) (hDS0 : 0 < DS) (hp2 : 0 < p2) (heh : 0 ≤ eh ∧ eh ≤ p2) (bp2 : p2 ≤ 2 ^ E)
    (bxa : ∀ k < d * d, |xa k| ≤ 2 ^ E) (bmu : ∀ l < d, |xmu l| ≤ 2 ^ E) (bDS : DS ≤ 2 ^ E)
    (hMt : Mh ^ (d + 2) ≤ 2 ^ t) (hDt : 2 ^ E * Mh ^ (d + 1) ≤ 2 ^ t) (hEt : E ≤ t)
    (hℓ : (3 * t + d + 1) * (d + 2) + 1 < ℓ) (hma : 4 + 2 * (d + 1) * (m + 1) < 2 ^ ℓa) (hia : i < 2 ^ ℓa)
    (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xrow L) σ (rowUnits d m (3 * t + d + 1)) (fun σ' =>
      (∀ q < d, σ'.arr 33 q = ((clr (rowDenR d (rowAq d Nm Dn xa DS (rowK d Nm i m))
          (rowBq d Nm Dn xmu DS p2 eh (rowK d Nm i m))) (rowAq d Nm Dn xa DS (rowK d Nm i m) q) : ℤ) : ℝ)) ∧
      σ'.sc 770 = ((clr (rowDenR d (rowAq d Nm Dn xa DS (rowK d Nm i m))
          (rowBq d Nm Dn xmu DS p2 eh (rowK d Nm i m))) (rowBq d Nm Dn xmu DS p2 eh (rowK d Nm i m)) : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = 770 ∨ SRow y) NRow (fun b _ => b = 33 ∨ ARow b) σ σ') := by
  have hla := hL.1
  set kk := rowK d Nm i m with hkkdef
  set s := 3 * t + d + 1 with hsdef
  have hd1 : d + 1 < 2 ^ ℓa := by nlinarith
  have hkm : (d + 1) * (kk + 1) ≤ (d + 1) * m := Nat.mul_le_mul_left _ hkk
  -- magnitudes
  have hMle : Mh ≤ 2 ^ t := le_trans (le_self_pow₀ hM1 (by omega)) hMt
  have h2E : (1 : ℤ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hEt' : (2 : ℤ) ^ E ≤ 2 ^ t := pow_le_pow_of_le' hEt
  have h2t2s : (2 : ℤ) ^ (2 * t) ≤ 2 ^ s := pow_le_pow_of_le' (by omega)
  have hts' : (2 : ℤ) ^ t ≤ 2 ^ s := pow_le_pow_of_le' (by omega)
  have hsl : s < ℓ := by nlinarith
  have h2tl : 2 * t < ℓ := by omega
  have hdpow : d < 2 ^ d := Nat.lt_two_pow_self
  have hts : d * 2 ^ (2 * t) ≤ 2 ^ s := by
    calc d * 2 ^ (2 * t) ≤ 2 ^ d * 2 ^ (2 * t) := Nat.mul_le_mul_right _ hdpow.le
      _ = 2 ^ (2 * t + d) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdl : d * 2 ^ (2 * t) < 2 ^ ℓ := lt_of_le_of_lt hts (Nat.pow_lt_pow_right (by norm_num) hsl)
  have hMl : Mh ^ (d + 2) * DS < 2 ^ ℓ := by
    have : Mh ^ (d + 2) * DS ≤ 2 ^ t * 2 ^ t := mul_le_mul hMt (bDS.trans hEt') hDS0.le (by positivity)
    have h2 : (2 : ℤ) ^ t * 2 ^ t = 2 ^ (2 * t) := by ring
    have h3 : (2 : ℤ) ^ (2 * t) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) h2tl
    linarith
  have hMd1 : Mh ^ (d + 1) < 2 ^ ℓ := by
    have : Mh ^ (d + 1) ≤ Mh ^ (d + 2) := pow_le_pow_right₀ hM1 (by omega)
    have h3 : (2 : ℤ) ^ t < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  -- the scan
  refine XV.seq (XV.scan hL (by omega) (by omega) (m := m) (i := i) (E := t) (Nm := Nm) hD hM h1 hi hz hoff
    (fun k hk j hj => hinpN k hk j hj.le) (fun k hk j hj => (bNm k hk j hj.le).trans hMle) h2tl hdl hma hia)
    fun σ1 ⟨c35, c38, c39, cdr, cF⟩ => ?_
  have k1n : ∀ j, j < 32 ∨ 64 ≤ j → σ1.nat j = σ.nat j := fun j hj => cF.1 j (by simp only [NR]; omega)
  have k1s : ∀ y, y ≠ 96 → y ≠ 97 → σ1.sc y = σ.sc y := fun y a b => cF.2.1 y (by omega)
  have k1a : ∀ a k, σ1.arr a k = σ.arr a k := fun a k => cF.2.2.1 a k not_false
  -- the row `kk`
  refine XV.seq (XV.inRow hL (sD := 100) (sT := 101) (sN := 102) (sQ := 103) (sB := 104) (sDn := sDS) (aRow := 12)
    (nI := 36) (nT := 37) (nj := 33) (nd := rD) (nd1 := 39) (nk := 35) (none := rOne) (k := kk) (Mh := Mh)
    (D := DS) (Nm := Nm kk) (Dn := Dn kk) (by omega) (by omega) (by omega) (by omega) (by omega) (by rwgo)
    (by decide) (by omega) (by omega) (by omega) (by omega) (by rwgo) (by omega) (by omega) (by rwgo) (by decide)
    (by rw [k1n rD (by rwgo), hD]) c39 c35 (by rw [k1n rOne (by rwgo), h1]) (by rw [k1s sDS (by rwgo) (by rwgo), hDS])
    (by nlinarith) (by nlinarith) hda (fun j hj => hinpN kk hkk j hj) (fun j hj => hinpD kk hkk j hj) (by omega)
    hM1 (fun j hj => bNm kk hkk j hj) (fun j hj => bDn kk hkk j hj) hMl) fun σ2 ⟨i1, i2, i3, i4⟩ => ?_
  have k2n : ∀ j, j ≠ 36 → j ≠ 37 → j ≠ 33 → σ2.nat j = σ1.nat j := fun j a b c => i4.1 j (by omega)
  have k2s : ∀ y, (y < 100 ∨ 104 < y) → σ2.sc y = σ1.sc y := fun y h => i4.2.1 y (by omega)
  have k2a : ∀ a k, a ≠ 12 → σ2.arr a k = σ.arr a k := fun a k h => by
    rw [i4.2.2.1 a k (by omega), k1a]
  -- the address of the first denominator, `P`, `D₀`
  refine XV.seq (XV.addr hL (nI := 36) (nd1 := 39) (nk := 35) (nT := 37) (c0 := 4) (D1 := d + 1) (K := kk)
    (by omega) (by omega) (by omega) (by omega) (by decide) (by rw [k2n 39 (by omega) (by omega) (by omega), c39])
    (by rw [k2n 35 (by omega) (by omega) (by omega)]; exact c35) (by nlinarith) hd1 (by nlinarith))
    fun σ3 ⟨a1, a2, a3⟩ => ?_
  have h1l : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XV.seq (XV.constI hL (x := 105) (by omega) 1 h1l) fun σ4 e4 => ?_
  subst e4
  have hinpP : ∀ j < d + 1, X.inp (4 + 2 * ((d + 1) * kk) + 2 * j) = Dn kk j := fun j hj => by
    rw [show 4 + 2 * ((d + 1) * kk) + 2 * j = 4 + 2 * ((d + 1) * kk + j) by ring]
    exact hinpD kk hkk j (by omega)
  refine XV.seq (XV.denProd hL (sD := 105) (sT := 106) (nj := 33) (nI := 36) (nn := 39) (none := rOne) (N := d + 1)
    (c := 4 + 2 * ((d + 1) * kk)) (Mh := Mh) (Dn := Dn kk) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by rwgo) (by decide) (by rwenv; exact a1)
    (by rwenv; rw [a3.1 39 (by omega), k2n 39 (by omega) (by omega) (by omega), c39])
    (by rwenv; rw [a3.1 rOne (by rwgo), k2n rOne (by rwgo) (by rwgo) (by rwgo), k1n rOne (by rwgo), h1])
    (by rwenv; simp) (by nlinarith) (by nlinarith) hinpP hM1 (fun j hj => bDn kk hkk j (by omega)) hMd1)
    fun σ5 ⟨p1, p2', p3, p4⟩ => ?_
  obtain ⟨hP1, hP2⟩ := prod_range_abs_le (Dn kk) Mh hM1 (d + 1) (fun j hj => bDn kk hkk j (by omega))
  have ePr : (∏ j ∈ Finset.range (d + 1), Dn kk j) = rowP d Dn kk := rfl
  rw [ePr] at p1 hP1 hP2
  -- what `σ5` keeps
  have k5s : ∀ y, y ≠ 105 → y ≠ 106 → σ5.sc y = σ2.sc y := fun y a b => by
    rw [p4.2.1 y (by omega)]; rwenv; exact a3.2.1 y not_false
  have k5n : ∀ j, j ≠ 33 → j ≠ 36 → j ≠ 37 → σ5.nat j = σ2.nat j := fun j a b c => by
    rw [p4.1 j (by omega)]; rwenv; exact a3.1 j (by omega)
  have k5a : ∀ a k, σ5.arr a k = σ2.arr a k := fun a k => by
    rw [p4.2.2.1 a k not_false]; rwenv; exact a3.2.2.1 a k not_false
  have bD0 : DS * rowP d Dn kk ≤ 2 ^ t :=
    le_trans (mul_le_mul bDS hP2 (by omega) (by positivity)) hDt
  have hD0 : 0 < DS * rowP d Dn kk := mul_pos hDS0 (by omega)
  have bDSt : |DS| ≤ 2 ^ t := by rw [abs_of_pos hDS0]; exact bDS.trans hEt'
  have bPt : |rowP d Dn kk| ≤ 2 ^ t := by
    rw [abs_of_pos (by omega)]
    exact le_trans (le_mul_of_one_le_left (by omega) h2E) (le_trans (mul_le_mul_of_nonneg_left hP2 (by positivity)) hDt)
  refine XV.seq (XV.mulI hL (x := 107) (a := sDS) (b := 105) (by omega) (by rwgo) (by omega) (u := DS)
    (v := rowP d Dn kk) (by rw [k5s sDS (by rwgo) (by rwgo), k2s sDS (by rwgo), k1s sDS (by rwgo) (by rwgo), hDS]) p1
    (absI_le_pow bDSt (by omega)) (absI_le_pow bPt (by omega))
    (absI_le_pow (by rw [abs_of_pos hD0]; exact bD0) (by omega))) fun σ6 e6 => ?_
  subst e6
  -- the columns
  have bah : ∀ l < d, |rowH d Nm Dn kk l| ≤ 2 ^ t := fun l hl =>
    (rowA_abs hM1 (fun j hj => bNm kk hkk j hj) (fun j hj => bDn kk hkk j hj) hl.le).trans hMt
  have bbh : |rowA Nm Dn d kk d| ≤ 2 ^ t :=
    (rowA_abs hM1 (fun j hj => bNm kk hkk j hj) (fun j hj => bDn kk hkk j hj) le_rfl).trans hMt
  refine XV.seq (XV.cols hL (by omega) (by omega) (by omega) (t := t) (s := s) (xa := xa) (ah := rowH d Nm Dn kk)
    (D0 := DS * rowP d Dn kk) (by rwenv; rw [k5n rD (by rwgo) (by rwgo) (by rwgo), k2n rD (by rwgo) (by rwgo) (by rwgo),
      k1n rD (by rwgo), hD])
    (by rwenv; rw [k5n rOne (by rwgo) (by rwgo) (by rwgo), k2n rOne (by rwgo) (by rwgo) (by rwgo), k1n rOne (by rwgo), h1])
    (by rwenv; rw [k5n 38 (by omega) (by omega) (by omega), k2n 38 (by omega) (by omega) (by omega), c38])
    (by rwenv; rw [k5s sZ (by rwgo) (by rwgo), k2s sZ (by rwgo), k1s sZ (by rwgo) (by rwgo), hz]) (by rwenv) hD0
    (bD0.trans hts') (fun k hk => by rwenv; rw [k5a, k2a aAS k (by rwgo), hxa k hk])
    (fun l hl => by rwenv; rw [k5a, i1 l hl]; rfl) (fun k hk => (bxa k hk).trans hEt') bah hts (by nlinarith) hda)
    fun σ7 ⟨o1, o2, o3, o4⟩ => ?_
  -- what `σ7` keeps
  set P := rowP d Dn kk with hPdef
  set D0 := DS * P with hD0def
  set ah := rowH d Nm Dn kk with hahdef
  have n7 : ∀ j, j < 32 ∨ 64 ≤ j → σ7.nat j = σ.nat j := fun j hj => by
    rw [o4.1 j (by omega)]; rwenv
    rw [k5n j (by omega) (by omega) (by omega), k2n j (by omega) (by omega) (by omega), k1n j hj]
  have s7 : ∀ y, y < 96 ∨ 256 ≤ y → σ7.sc y = σ.sc y := fun y hy => by
    rw [o4.2.1 y (by omega)]; rwenv
    rw [k5s y (by omega) (by omega), k2s y (by omega), k1s y (by omega) (by omega)]
  have a7 : ∀ a k, a < 12 ∨ 16 ≤ a → σ7.arr a k = σ.arr a k := fun a k ha => by
    rw [o4.2.2.1 a k (by omega)]; rwenv; rw [k5a, k2a a k (by omega)]
  have e104 : σ7.sc 104 = ((rowA Nm Dn d kk d * DS : ℤ) : ℝ) := by
    rw [o4.2.1 104 (by omega)]; rwenv; rw [k5s 104 (by omega) (by omega), i2]; rfl
  have e107 : σ7.sc 107 = ((D0 : ℤ) : ℝ) := by rw [o4.2.1 107 (by omega)]; rwenv
  have e12 : ∀ l < d, σ7.arr 12 l = ah l := fun l hl => by
    rw [o4.2.2.1 12 l (by omega)]; rwenv; rw [k5a, i1 l hl]; rfl
  -- the right-hand side
  obtain ⟨q1, q2⟩ := prod_den_le (q := d) (s := s) hD0 (bD0.trans hts') (colG d xa ah D0) fun j hj => by
    obtain ⟨_, _, h3, h4⟩ := red_bounds (colN d xa ah j) D0 hD0
    exact ⟨h3, h4⟩
  have hdot : |dotS d ah xmu| ≤ d * 2 ^ (2 * t) := abs_sum_mul_le bah fun l hl => (bmu l hl).trans hEt'
  have hdotZ : (d : ℤ) * 2 ^ (2 * t) ≤ 2 ^ s := by exact_mod_cast hts
  have bbD : |rowA Nm Dn d kk d * DS| ≤ 2 ^ (2 * t) := by
    rw [abs_mul, show 2 * t = t + t by ring, pow_add]; exact mul_le_mul bbh bDSt (abs_nonneg _) (by positivity)
  have hpe : |p2 - eh| ≤ 2 ^ t := by rw [abs_of_nonneg (by omega)]; exact le_trans (by omega) (bp2.trans hEt')
  have b118 : |rowA Nm Dn d kk d * DS - dotS d ah xmu| ≤ 2 ^ s := by
    have h2 : (2 : ℤ) ^ (2 * t) * (d + 1) ≤ 2 ^ s := by
      have hd2 : ((d : ℤ) + 1) ≤ 2 ^ (d + 1) := by
        have := (Nat.lt_two_pow_self (n := d + 1)); push_cast; exact_mod_cast this.le
      calc (2 : ℤ) ^ (2 * t) * (d + 1) ≤ 2 ^ (2 * t) * 2 ^ (d + 1) := mul_le_mul_of_nonneg_left hd2 (by positivity)
        _ ≤ 2 ^ s := by rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc _ ≤ |rowA Nm Dn d kk d * DS| + |dotS d ah xmu| := abs_sub _ _
      _ ≤ 2 ^ (2 * t) + d * 2 ^ (2 * t) := add_le_add bbD hdot
      _ ≤ 2 ^ s := by nlinarith
  have b121 : p2 * D0 ≤ 2 ^ s := by
    calc p2 * D0 ≤ 2 ^ t * 2 ^ t := mul_le_mul (bp2.trans hEt') bD0 hD0.le (by positivity)
      _ = 2 ^ (2 * t) := by ring
      _ ≤ 2 ^ s := h2t2s
  have b120 : |(p2 - eh) * (rowA Nm Dn d kk d * DS - dotS d ah xmu)| ≤ 2 ^ s := by
    have := mag_beta d t (p2 - eh) (rowA Nm Dn d kk d) DS (dotS d ah xmu) hpe bbh bDSt hdot
    rwa [show 3 * t + d + 1 = s from rfl] at this
  have hDb : 0 < p2 * D0 := mul_pos hp2 hD0
  refine XV.seq (XV.beta hL (by omega) (by omega) (by omega) (t := t) (s := s) (S := s * d) (ah := ah) (xmu := xmu)
    (bD := rowA Nm Dn d kk d * DS) (p2 := p2) (eh := eh) (D0 := D0)
    (R0 := ∏ q ∈ Finset.range d, D0 / colG d xa ah D0 q) (by rw [n7 rD (by rwgo), hD]) (by rw [n7 rOne (by rwgo), h1])
    (by rw [s7 sZ (by rwgo), hz]) e104 (by rw [s7 s2pF (by rwgo), h2p]) (by rw [s7 sEps (by rwgo), hep]) e107 o2 e12
    (fun l hl => by rw [a7 aMuS l (by rwgo), hmu l hl]) bah (fun l hl => (bmu l hl).trans hEt') hts (by omega)
    (bbD.trans h2t2s) (by rw [abs_of_pos hp2]; exact bp2.trans (hEt'.trans hts'))
    (by rw [abs_of_nonneg heh.1]; exact heh.2.trans (bp2.trans (hEt'.trans hts')))
    (by rw [abs_of_pos hD0]; exact bD0.trans hts') b118 (hpe.trans hts') b120 hDb b121
    (by rw [abs_of_pos (by omega)]; exact q2) (by nlinarith) hda) fun σ8 ⟨β1, β2, β3, β4, β5⟩ => ?_
  -- the output
  set Nb := (p2 - eh) * (rowA Nm Dn d kk d * DS - dotS d ah xmu) with hNbdef
  set gb := (Int.gcd Nb (p2 * D0) : ℤ) with hgbdef
  obtain ⟨g1, g2, g3, g4⟩ := red_bounds Nb (p2 * D0) hDb
  have n8 : ∀ j, j < 32 ∨ 64 ≤ j → σ8.nat j = σ.nat j := fun j hj => by
    rw [β5.1 j (by omega), n7 j hj]
  have bR : (∏ q ∈ Finset.range d, D0 / colG d xa ah D0 q) * (p2 * D0 / gb) ≤ 2 ^ (s * d + s) := by
    rw [pow_add]; exact mul_le_mul q2 (g4.trans b121) (zero_le_one.trans g3) (by positivity)
  refine XV.mono (XV.out hL (by omega) (by omega) (by omega) (s := s) (S := s * d + s)
    (nu := fun q => colN d xa ah q / colG d xa ah D0 q) (de := fun q => D0 / colG d xa ah D0 q) (nb := Nb / gb)
    (db := p2 * D0 / gb) (R := (∏ q ∈ Finset.range d, D0 / colG d xa ah D0 q) * (p2 * D0 / gb))
    (by rw [n8 rD (by rwgo), hD]) (by rw [n8 rOne (by rwgo), h1]) β3 β1 β2
    (fun q hq => by rw [β5.2.2.1 13 q not_false]; exact (o1 q hq).1)
    (fun q hq => by rw [β5.2.2.1 14 q not_false]; exact (o1 q hq).2)
    (fun q hq => (red_bounds (colN d xa ah q) D0 hD0).2.1.trans (by
      exact (abs_sum_mul_le (Xv := fun l => xa (q + d * l)) (Yv := ah)
        (fun l hl => (bxa _ (by nlinarith)).trans hEt') bah).trans hdotZ))
    (fun q hq => ⟨(red_bounds (colN d xa ah q) D0 hD0).2.2.1,
      (red_bounds (colN d xa ah q) D0 hD0).2.2.2.trans (bD0.trans hts')⟩)
    (g2.trans b120) ⟨g3, g4.trans b121⟩ (by positivity) bR (by nlinarith) hda) le_rfl
    fun σ9 ⟨u1, u2, u3, u4⟩ => ?_
  have hx : ∀ q, rowAq d Nm Dn xa DS kk q = (colN d xa ah q : ℚ) / ((D0 : ℤ) : ℚ) := fun q => rfl
  have hb : rowBq d Nm Dn xmu DS p2 eh kk = (Nb : ℚ) / ((p2 * D0 : ℤ) : ℚ) := rfl
  have hR : ((rowDenR d (rowAq d Nm Dn xa DS kk) (rowBq d Nm Dn xmu DS p2 eh kk) : ℕ) : ℤ) =
      (∏ q ∈ Finset.range d, D0 / colG d xa ah D0 q) * (p2 * D0 / gb) := by
    unfold rowDenR
    push_cast
    rw [den_link hDb hb]
    congr 1
    exact Finset.prod_congr rfl fun q _ => den_link hD0 (hx q)
  refine ⟨fun q hq => by rw [u1 q hq, clr_link hD0 (hx q) hR]; rfl, by rw [u2, clr_link hDb hb hR], by
    rw [u3, β4, o3]; rwenv; rw [p2']; rwenv; rw [a2, i3, cdr], ?_⟩
  -- the frame
  have F := ((((((((cF.mono (S' := fun y => y = 770 ∨ SRow y) (N' := NRow)
    (Ar' := fun b _ => b = 33 ∨ ARow b) (fun y h => by simp only [SRow]; omega) (fun j h => h)
    (fun _ _ h => h.elim)).trans (i4.mono (fun y h => by simp only [SRow]; omega)
      (fun j h => by simp only [NRow]; omega) (fun b k h => by simp only [ARow]; omega))).trans
    (a3.mono (fun y h => h.elim) (fun j h => by simp only [NRow]; omega) (fun _ _ h => h.elim))).setSc
      (Or.inr ⟨by norm_num, by norm_num⟩) _).trans (p4.mono (fun y h => by simp only [SRow]; omega)
      (fun j h => by simp only [NRow]; omega) (fun _ _ h => h.elim))).setSc
      (Or.inr ⟨by norm_num, by norm_num⟩) _).trans (o4.mono (fun y h => by simp only [SRow]; omega)
      (fun j h => by simp only [NRow]; omega) (fun b k h => by simp only [ARow]; omega))).trans
    (β5.mono (fun y h => by simp only [SRow]; omega) (fun j h => by simp only [NRow]; omega)
      (fun _ _ h => h.elim))).trans (u4.mono (fun y h => by simp only [SRow]; omega)
      (fun j h => by simp only [NRow]; omega) (fun b k h => Or.inl h))
  exact F

end AdversarialBco.Bit.Transfer.BLM.RowM
